/* ============================================================
   Confluence — Crypto Signal Terminal (v2)
   Adds: RSI, MACD, Bollinger Bands, volume confirmation,
   support/resistance key levels, a 1H timeframe panel, and an
   overall-bias summary combining all three timeframes.
   ============================================================ */

const API = 'https://api.binance.com/api/v3/klines';
const TICKER_API = 'https://api.binance.com/api/v3/ticker/24hr';

const TIMEFRAMES = [
  { key: '15m', interval: '15m', label: '15 Minute', title: 'Scalp Window', weight: 0.8 },
  { key: '1h',  interval: '1h',  label: '1 Hour',     title: 'Swing Window', weight: 1.0 },
  { key: '1d',  interval: '1d',  label: '1 Day',      title: 'Position Window', weight: 1.3 }
];

const SYMBOLS = [
  'BTCUSDT','ETHUSDT','HYPEUSDT','XRPUSDT','SOLUSDT','BNBUSDT','ADAUSDT','DOGEUSDT',
  'AVAXUSDT','LINKUSDT','DOTUSDT','LTCUSDT','TRXUSDT','TONUSDT','SUIUSDT',
  'ARBUSDT','OPUSDT'
];

let currentSymbol = 'BTCUSDT';
let lastResults = null; // cache of the most recent analysis, so the risk calculator can re-render instantly without refetching
let latestByTf = {};    // most recent analysis per timeframe key, used by the "Log This Trade" buttons
let toastTimer = null;
const JOURNAL_KEY = 'confluence_journal_v1';

/* ---------------- clock ---------------- */
function tickClock(){
  const el = document.getElementById('clock');
  if(el) el.textContent = new Date().toUTCString().slice(0,25) + ' UTC';
}
tickClock(); setInterval(tickClock, 1000);

/* ---------------- math helpers ---------------- */
function ema(values, period){
  const k = 2/(period+1);
  const out = new Array(values.length).fill(null);
  if(values.length < period) return out;
  let prev = values.slice(0, period).reduce((a,b)=>a+b,0)/period;
  out[period-1] = prev;
  for(let i=period;i<values.length;i++){
    prev = values[i]*k + prev*(1-k);
    out[i] = prev;
  }
  return out;
}

function sma(values, period){
  const out = new Array(values.length).fill(null);
  for(let i=period-1;i<values.length;i++){
    let sum=0;
    for(let j=i-period+1;j<=i;j++) sum+=values[j];
    out[i]=sum/period;
  }
  return out;
}

function atr(candles, period){
  const trs = [];
  for(let i=1;i<candles.length;i++){
    const c = candles[i], p = candles[i-1];
    const tr = Math.max(c.high-c.low, Math.abs(c.high-p.close), Math.abs(c.low-p.close));
    trs.push(tr);
  }
  const out = [];
  if(trs.length < period) return out;
  let prev = trs.slice(0,period).reduce((a,b)=>a+b,0)/period;
  out[period] = prev;
  for(let i=period+1;i<trs.length+1;i++){
    prev = (prev*(period-1) + trs[i-1])/period;
    out[i] = prev;
  }
  return out; // index-aligned to candles (out[i] = ATR ending at candles[i])
}

function rsi(closes, period=14){
  const out = new Array(closes.length).fill(null);
  if(closes.length <= period) return out;
  let gains=0, losses=0;
  for(let i=1;i<=period;i++){
    const diff = closes[i]-closes[i-1];
    if(diff>=0) gains+=diff; else losses-=diff;
  }
  let avgGain = gains/period, avgLoss = losses/period;
  out[period] = avgLoss===0 ? 100 : 100-(100/(1+avgGain/avgLoss));
  for(let i=period+1;i<closes.length;i++){
    const diff = closes[i]-closes[i-1];
    const gain = diff>0?diff:0;
    const loss = diff<0?-diff:0;
    avgGain = (avgGain*(period-1)+gain)/period;
    avgLoss = (avgLoss*(period-1)+loss)/period;
    out[i] = avgLoss===0 ? 100 : 100-(100/(1+avgGain/avgLoss));
  }
  return out;
}

function macd(closes, fast=12, slow=26, signalP=9){
  const emaFast = ema(closes, fast);
  const emaSlow = ema(closes, slow);
  const macdLine = closes.map((_,i)=> (emaFast[i]!=null && emaSlow[i]!=null) ? emaFast[i]-emaSlow[i] : null);
  const vals = [], idxMap = [];
  macdLine.forEach((v,i)=>{ if(v!=null){ vals.push(v); idxMap.push(i); } });
  const signalRaw = ema(vals, signalP);
  const signalLine = new Array(closes.length).fill(null);
  signalRaw.forEach((v,k)=>{ if(v!=null) signalLine[idxMap[k]] = v; });
  const hist = closes.map((_,i)=> (macdLine[i]!=null && signalLine[i]!=null) ? macdLine[i]-signalLine[i] : null);
  return { macdLine, signalLine, hist };
}

function bollinger(closes, period=20, mult=2){
  const out = new Array(closes.length).fill(null);
  for(let i=period-1;i<closes.length;i++){
    const slice = closes.slice(i-period+1, i+1);
    const mean = slice.reduce((a,b)=>a+b,0)/period;
    const variance = slice.reduce((a,b)=>a+(b-mean)**2,0)/period;
    const sd = Math.sqrt(variance);
    out[i] = { mid: mean, upper: mean+mult*sd, lower: mean-mult*sd };
  }
  return out;
}

function volumeStats(candles, period=20){
  const vols = candles.map(c=>c.volume);
  const last = vols[vols.length-1];
  const start = Math.max(0, vols.length-1-period);
  const slice = vols.slice(start, vols.length-1);
  const avg = slice.length ? slice.reduce((a,b)=>a+b,0)/slice.length : last;
  return { last, avg, ratio: avg ? last/avg : 1 };
}

// simple fractal swing detection: pivot high/low with `look` bars each side
function findSwings(candles, look){
  const highs = [], lows = [];
  for(let i=look; i<candles.length-look; i++){
    let isHigh = true, isLow = true;
    for(let j=i-look;j<=i+look;j++){
      if(j===i) continue;
      if(candles[j].high >= candles[i].high) isHigh = false;
      if(candles[j].low <= candles[i].low) isLow = false;
    }
    if(isHigh) highs.push({i, price: candles[i].high});
    if(isLow) lows.push({i, price: candles[i].low});
  }
  return {highs, lows};
}

function detectTrend(candles, emaFast, emaMid, emaSlow, swings){
  const last = candles.length-1;
  const price = candles[last].close;
  const f = emaFast[last], m = emaMid[last], s = emaSlow[last];
  let emaScore = 0;
  if(f!=null && m!=null && s!=null){
    if(f>m && m>s && price>f) emaScore = 1;
    else if(f<m && m<s && price<f) emaScore = -1;
  }
  let structScore = 0;
  const h = swings.highs, l = swings.lows;
  if(h.length>=2 && l.length>=2){
    const hUp = h[h.length-1].price > h[h.length-2].price;
    const lUp = l[l.length-1].price > l[l.length-2].price;
    if(hUp && lUp) structScore = 1;
    else if(!hUp && !lUp) structScore = -1;
  }
  const combined = emaScore + structScore;
  let dir = 'neutral';
  if(combined >= 1) dir = 'up';
  else if(combined <= -1) dir = 'down';
  return {dir, emaScore, structScore};
}

function nearestFibHit(price, levels, tolPct){
  let best = null;
  for(const lv of levels){
    const dist = Math.abs(price - lv.price)/price;
    if(dist <= tolPct && (best===null || dist < best.dist)){
      best = {...lv, dist};
    }
  }
  return best;
}

function fibLevels(swingHigh, swingLow, dirIsRetraceFromHigh){
  const range = swingHigh - swingLow;
  const ratios = [0, 0.236, 0.382, 0.5, 0.618, 0.786, 1];
  return ratios.map(r=>{
    const price = dirIsRetraceFromHigh ? swingHigh - range*r : swingLow + range*r;
    return {ratio:r, price};
  });
}

function candlePattern(candles){
  const n = candles.length-1;
  const c = candles[n], p = candles[n-1];
  const body = Math.abs(c.close-c.open);
  const range = c.high-c.low || 1e-9;
  const upperWick = c.high - Math.max(c.close,c.open);
  const lowerWick = Math.min(c.close,c.open) - c.low;
  const patterns = [];

  if(p.close < p.open && c.close > c.open && c.close >= p.open && c.open <= p.close){
    patterns.push({name:'Bullish Engulfing', dir:1});
  }
  if(p.close > p.open && c.close < c.open && c.open >= p.close && c.close <= p.open){
    patterns.push({name:'Bearish Engulfing', dir:-1});
  }
  if(lowerWick > body*2 && lowerWick/range > 0.5 && upperWick/range < 0.2){
    patterns.push({name:'Bullish Pin Bar', dir:1});
  }
  if(upperWick > body*2 && upperWick/range > 0.5 && lowerWick/range < 0.2){
    patterns.push({name:'Bearish Pin Bar', dir:-1});
  }
  return patterns;
}

function keyLevels(swings, price){
  const below = swings.lows.map(l=>l.price).filter(p=>p<price).sort((a,b)=>b-a);
  const above = swings.highs.map(h=>h.price).filter(p=>p>price).sort((a,b)=>a-b);
  return { support: below[0] ?? null, resistance: above[0] ?? null };
}

/* ---------------- trade setup (entry / stop / targets) ---------------- */
function tradeSetup(direction, price, stopPrice, levels){
  if(direction==='neutral' || !stopPrice) return null;
  const risk = Math.abs(price - stopPrice);
  if(risk<=0) return null;
  let tp1, tp2;
  if(direction==='long'){
    tp1 = price + risk*1.5;
    tp2 = price + risk*3;
    if(levels.resistance && levels.resistance>price && levels.resistance<tp1) tp1 = levels.resistance;
  } else {
    tp1 = price - risk*1.5;
    tp2 = price - risk*3;
    if(levels.support && levels.support<price && levels.support>tp1) tp1 = levels.support;
  }
  const rr1 = Math.abs(tp1-price)/risk;
  const rr2 = Math.abs(tp2-price)/risk;
  return { entry: price, stop: stopPrice, tp1, tp2, rr1, rr2, riskAbs: risk };
}

/* ---------------- position sizing / leverage suggestion ---------------- */
function positionSizing(accountSize, riskPct, stopDistPct, price){
  if(!stopDistPct || stopDistPct<=0 || !accountSize || accountSize<=0 || !price) return null;
  const riskAmount = accountSize * (riskPct/100);
  const stopDistAbs = price * (stopDistPct/100);
  const positionUnits = riskAmount / stopDistAbs;
  const positionNotional = positionUnits * price;
  const rawLeverage = positionNotional / accountSize;
  const cappedLeverage = Math.min(rawLeverage, 25);
  return {
    riskAmount, positionUnits, positionNotional,
    leverage: cappedLeverage,
    wasCapped: rawLeverage>25
  };
}

/* ---------------- speculative price projection ---------------- */
function linearRegression(values){
  const n = values.length;
  const xs = values.map((_,i)=>i);
  const xMean = xs.reduce((a,b)=>a+b,0)/n;
  const yMean = values.reduce((a,b)=>a+b,0)/n;
  let num=0, den=0;
  for(let i=0;i<n;i++){ num += (xs[i]-xMean)*(values[i]-yMean); den += (xs[i]-xMean)**2; }
  const slope = den===0 ? 0 : num/den;
  const intercept = yMean - slope*xMean;
  let ssTot=0, ssRes=0;
  for(let i=0;i<n;i++){
    const pred = slope*xs[i]+intercept;
    ssRes += (values[i]-pred)**2;
    ssTot += (values[i]-yMean)**2;
  }
  const r2 = ssTot===0 ? 0 : Math.max(0, 1-(ssRes/ssTot));
  return {slope, intercept, r2};
}

function projectPrice(closes, lookback=20, periodsAhead=5, currentATR){
  if(!closes || closes.length<8) return null;
  const slice = closes.slice(-Math.min(lookback, closes.length));
  const {slope, intercept, r2} = linearRegression(slice);
  const futureX = slice.length-1+periodsAhead;
  const projected = slope*futureX + intercept;
  const current = slice[slice.length-1];
  const changePct = ((projected-current)/current)*100;
  const uncertainty = (currentATR||Math.abs(current*0.01)) * Math.sqrt(periodsAhead);
  const confidence = r2>0.6 ? 'trend-consistent' : r2>0.3 ? 'moderate fit' : 'weak fit';
  return {
    projected, changePct, r2, periodsAhead, confidence,
    upper: projected+uncertainty, lower: projected-uncertainty
  };
}

/* ---------------- plain-language summary ---------------- */
function plainSummary(data){
  const bits = [];
  bits.push(`the trend on this timeframe is ${data.trend.dir}`);
  if(data.fibHitLevel) bits.push(`price is sitting right at the ${data.fibHitLevel.ratio} fib retracement`);
  if(data.patterns.length) bits.push(`a ${data.patterns[data.patterns.length-1].name.toLowerCase()} just printed on the last candle`);
  if(data.rsiVal!=null){
    const rsiWord = data.rsiVal>=70 ? 'overbought' : data.rsiVal<=30 ? 'oversold' : 'in neutral territory';
    bits.push(`RSI is ${rsiWord} at ${data.rsiVal.toFixed(0)}`);
  }
  const dirWord = data.direction==='long' ? 'a bullish' : data.direction==='short' ? 'a bearish' : 'no clear';
  return `Right now, ${bits.join(', ')}. Taken together, that's ${dirWord} read with a confluence score of ${data.score}/100.`;
}

/* ---------------- confluence scoring ---------------- */
function computeScore({trendDirVal, fibHitLevel, patternDir, rsiVal, macdHist, macdHistPrev, bbVal, price, volRatio, lastCandleUp}){
  let score = 0;
  if(trendDirVal !== 0) score += 18;

  if(fibHitLevel){
    score += (fibHitLevel.ratio===0.5 || fibHitLevel.ratio===0.618) ? 24 : 14;
  }

  if(patternDir !== 0 && patternDir === trendDirVal) score += 16;
  else if(patternDir !== 0) score += 5;

  if(rsiVal!=null && trendDirVal!==0){
    if(trendDirVal===1){
      if(rsiVal>=40 && rsiVal<=70) score += 10;
      else if(rsiVal>75) score -= 6;
    } else {
      if(rsiVal<=60 && rsiVal>=30) score += 10;
      else if(rsiVal<25) score -= 6;
    }
  }

  if(macdHist!=null && trendDirVal!==0){
    if(Math.sign(macdHist)===trendDirVal) score += 12;
    if(macdHistPrev!=null && Math.sign(macdHistPrev)!==trendDirVal && Math.sign(macdHist)===trendDirVal) score += 6;
  }

  if(bbVal && trendDirVal!==0){
    const width = (bbVal.upper - bbVal.lower) || 1;
    const posPct = (price - bbVal.lower)/width; // 0 at lower band .. 1 at upper band
    if(trendDirVal===1){
      if(posPct<0.35) score += 8;
      else if(posPct>0.9) score -= 4;
    } else {
      if(posPct>0.65) score += 8;
      else if(posPct<0.1) score -= 4;
    }
  }

  if(volRatio!=null && trendDirVal!==0){
    if(volRatio>1.5 && lastCandleUp===(trendDirVal===1)) score += 8;
    else if(volRatio<0.5) score -= 3;
  }

  score = Math.max(0, Math.min(100, score));
  let direction = 'neutral';
  if(trendDirVal===1 && score>=50) direction = 'long';
  else if(trendDirVal===-1 && score>=50) direction = 'short';
  return { score, direction };
}

/* ---------------- core analysis ---------------- */
function analyze(rawCandles){
  const candles = rawCandles.map(k=>({
    time:k[0], open:+k[1], high:+k[2], low:+k[3], close:+k[4], volume:+k[5]
  }));
  const closes = candles.map(c=>c.close);
  const e20 = ema(closes, 20);
  const e50 = ema(closes, 50);
  const e200 = closes.length>200 ? ema(closes, 200) : ema(closes, Math.min(100, Math.floor(closes.length/2)));
  const atrArr = atr(candles, 14);
  const last = candles.length-1;
  const price = candles[last].close;
  const currentATR = atrArr[atrArr.length-1] || (candles[last].high-candles[last].low);

  const swings = findSwings(candles, 4);
  const trend = detectTrend(candles, e20, e50, e200, swings);
  const trendDirVal = trend.dir==='up' ? 1 : trend.dir==='down' ? -1 : 0;

  let fibData = null, fibHitLevel = null;
  const h = swings.highs, l = swings.lows;
  if(h.length && l.length){
    const lastHigh = h[h.length-1];
    const lastLow = l[l.length-1];
    const retraceFromHigh = lastHigh.i > lastLow.i;
    const swingHighPrice = Math.max(lastHigh.price, lastLow.price);
    const swingLowPrice = Math.min(lastHigh.price, lastLow.price);
    const levels = fibLevels(swingHighPrice, swingLowPrice, retraceFromHigh);
    fibData = {levels, swingHighPrice, swingLowPrice, retraceFromHigh};
    fibHitLevel = nearestFibHit(price, levels.filter(lv=>lv.ratio>0 && lv.ratio<1), 0.006);
  }

  const patterns = candlePattern(candles);
  const patternDir = patterns.length ? patterns[patterns.length-1].dir : 0;

  const rsiArr = rsi(closes, 14);
  const rsiVal = rsiArr[rsiArr.length-1];

  const macdData = macd(closes, 12, 26, 9);
  const macdHist = macdData.hist[macdData.hist.length-1];
  const macdHistPrev = macdData.hist[macdData.hist.length-2];

  const bbArr = bollinger(closes, 20, 2);
  const bbVal = bbArr[bbArr.length-1];

  const vol = volumeStats(candles, 20);
  const lastCandleUp = candles[last].close > candles[last].open;

  const {score, direction} = computeScore({
    trendDirVal, fibHitLevel, patternDir, rsiVal, macdHist, macdHistPrev,
    bbVal, price, volRatio: vol.ratio, lastCandleUp
  });

  let stopPrice = null;
  if(direction!=='neutral' && l.length && h.length){
    if(direction==='long'){
      const structuralStop = l[l.length-1].price;
      stopPrice = Math.min(structuralStop, price - currentATR*1.5);
    } else {
      const structuralStop = h[h.length-1].price;
      stopPrice = Math.max(structuralStop, price + currentATR*1.5);
    }
  }
  const stopDistPct = stopPrice ? Math.abs(price-stopPrice)/price*100 : null;
  const levels = keyLevels(swings, price);
  const trade = tradeSetup(direction, price, stopPrice, levels);
  const projection = projectPrice(closes, 20, 5, currentATR);

  const result = {
    price, trend, trendDirVal, score, direction, fibData, fibHitLevel, patterns,
    stopPrice, stopDistPct, currentATR, swings, rsiVal, macdHist, macdHistPrev,
    bbVal, vol, levels, closes, trade, projection
  };
  result.summary = plainSummary(result);
  return result;
}

/* ---------------- rendering ---------------- */
function fmtPrice(p){
  if(p==null) return '—';
  if(p>=1000) return p.toLocaleString(undefined,{maximumFractionDigits:2});
  if(p>=1) return p.toFixed(4);
  return p.toFixed(6);
}

function gaugeSVG(score, dir){
  const angle = (score/100)*180;
  const rad = (angle-180)*Math.PI/180;
  const cx=64, cy=64, r=50;
  const x = cx + r*Math.cos(rad);
  const y = cy + r*Math.sin(rad);
  const color = dir==='long' ? 'var(--long)' : dir==='short' ? 'var(--short)' : 'var(--gold)';
  return `
  <svg width="128" height="74" viewBox="0 0 128 74">
    <path d="M 14 64 A 50 50 0 0 1 114 64" fill="none" stroke="#232830" stroke-width="9" stroke-linecap="round"/>
    <path d="M 14 64 A 50 50 0 0 1 114 64" fill="none" stroke="${color}" stroke-width="9" stroke-linecap="round"
      stroke-dasharray="${(score/100)*157} 157"/>
    <line x1="${cx}" y1="${cy}" x2="${x}" y2="${y}" stroke="${color}" stroke-width="2.5"/>
    <circle cx="${cx}" cy="${cy}" r="4" fill="${color}"/>
  </svg>`;
}

function sparklineSVG(closes){
  if(!closes || closes.length<2) return '';
  const w=140,h=36,pad=2;
  const slice = closes.slice(-40);
  const min = Math.min(...slice), max = Math.max(...slice);
  const span = (max-min) || 1;
  const stepX = (w-pad*2)/(slice.length-1);
  const pts = slice.map((v,i)=>{
    const x = pad + i*stepX;
    const y = h-pad - ((v-min)/span)*(h-pad*2);
    return `${x.toFixed(1)},${y.toFixed(1)}`;
  }).join(' ');
  const up = slice[slice.length-1] >= slice[0];
  const color = up ? 'var(--long)' : 'var(--short)';
  return `<svg width="${w}" height="${h}" viewBox="0 0 ${w} ${h}"><polyline points="${pts}" fill="none" stroke="${color}" stroke-width="1.8" stroke-linejoin="round" stroke-linecap="round"/></svg>`;
}

function fibBarHTML(fibData, price){
  if(!fibData) return '<div class="section-label">Fibonacci</div><div style="color:var(--ink-faint); font-family:var(--mono); font-size:11px;">No clean swing detected yet</div>';
  const {levels, swingHighPrice, swingLowPrice} = fibData;
  const span = swingHighPrice - swingLowPrice || 1;
  const pos = v => ((v-swingLowPrice)/span)*100;
  let html = '<div class="section-label">Fibonacci Zone (last swing)</div><div class="fibbar">';
  levels.forEach(lv=>{
    const leftPct = pos(lv.price);
    html += `<div class="fibline" style="left:${leftPct}%"><span class="lbl">${lv.ratio===0?'0':lv.ratio===1?'1':lv.ratio}</span></div>`;
  });
  const pricePct = Math.max(0,Math.min(100,pos(price)));
  html += `<div class="fibmarker" style="left:${pricePct}%"></div>`;
  html += '</div>';
  return html;
}

function bbBarHTML(bbVal, price){
  if(!bbVal) return '';
  const width = (bbVal.upper-bbVal.lower) || 1;
  const pct = Math.max(0, Math.min(100, ((price-bbVal.lower)/width)*100));
  return `
    <div class="section-label">Bollinger Bands (20, 2σ)</div>
    <div class="bbbar"><div class="bbmarker" style="left:${pct}%"></div></div>
    <div class="bblabels"><span>${fmtPrice(bbVal.lower)}</span><span>mid ${fmtPrice(bbVal.mid)}</span><span>${fmtPrice(bbVal.upper)}</span></div>
  `;
}

function indicatorGridHTML(data){
  const rsiVal = data.rsiVal;
  const rsiClass = rsiVal==null ? '' : rsiVal>=70 ? 'neg' : rsiVal<=30 ? 'pos' : '';
  const rsiZone = rsiVal==null ? '—' : rsiVal>=70 ? 'Overbought' : rsiVal<=30 ? 'Oversold' : 'Neutral';
  const rsiPct = rsiVal==null ? 0 : Math.max(0,Math.min(100,rsiVal));

  const hist = data.macdHist;
  const histClass = hist==null ? '' : hist>0 ? 'pos' : 'neg';
  const crossed = data.macdHistPrev!=null && hist!=null && Math.sign(data.macdHistPrev)!==Math.sign(hist);

  const vol = data.vol;
  const volClass = vol.ratio>1.5 ? 'warn' : vol.ratio<0.5 ? '' : '';

  return `
  <div class="ind-grid">
    <div class="ind-card">
      <div class="lbl"><span>RSI (14)</span><span>${rsiZone}</span></div>
      <div class="val ${rsiClass}">${rsiVal==null?'—':rsiVal.toFixed(1)}</div>
      <div class="rangebar"><div class="fill" style="width:${rsiPct}%"></div></div>
    </div>
    <div class="ind-card">
      <div class="lbl"><span>MACD Hist</span><span>${crossed?'fresh cross':''}</span></div>
      <div class="val ${histClass}">${hist==null?'—':hist>0?'+':''}${hist==null?'':fmtPrice(hist)}</div>
      <div class="mini">signal ${hist==null?'—':(hist>0?'bullish':'bearish')} momentum</div>
    </div>
    <div class="ind-card">
      <div class="lbl"><span>Volume</span><span>vs 20-avg</span></div>
      <div class="val ${volClass}">${vol.ratio.toFixed(2)}×</div>
      <div class="mini">${vol.ratio>1.5?'spike':vol.ratio<0.5?'thin':'normal'}</div>
    </div>
    <div class="ind-card">
      <div class="lbl"><span>ATR (14)</span><span>volatility</span></div>
      <div class="val">${fmtPrice(data.currentATR)}</div>
      <div class="mini">${((data.currentATR/data.price)*100).toFixed(2)}% of price</div>
    </div>
  </div>`;
}

function tradeSetupHTML(trade, direction, tfKey){
  if(!trade){
    return `<div class="section-label">Trade Setup</div>
    <div class="tradecard empty">No qualifying setup on this timeframe right now — wait for confluence before planning an entry.</div>`;
  }
  const dirWord = direction==='long' ? 'Long' : 'Short';
  return `
  <div class="section-label">Trade Setup — ${dirWord}</div>
  <div class="tradecard">
    <div class="trade-row"><span>Entry</span><b>${fmtPrice(trade.entry)}</b></div>
    <div class="trade-row"><span>Stop Loss</span><b class="hl-short">${fmtPrice(trade.stop)}</b></div>
    <div class="trade-row"><span>Target 1 <em>${trade.rr1.toFixed(1)}R</em></span><b class="hl-long">${fmtPrice(trade.tp1)}</b></div>
    <div class="trade-row"><span>Target 2 <em>${trade.rr2.toFixed(1)}R</em></span><b class="hl-long">${fmtPrice(trade.tp2)}</b></div>
    <button class="logtrade-btn ${direction}" data-tf="${tfKey}">+ Log This Trade</button>
  </div>`;
}

function sizingHTML(stopDistPct, price){
  if(!stopDistPct || !price) return '';
  const accEl = document.getElementById('accountSizeInput');
  const riskEl = document.getElementById('riskPctInput');
  const accountSize = accEl ? parseFloat(accEl.value)||0 : 1000;
  const riskPct = riskEl ? parseFloat(riskEl.value)||0 : 1;
  const sizing = positionSizing(accountSize, riskPct, stopDistPct, price);
  if(!sizing) return '';
  return `
  <div class="section-label">Position Sizing <span class="hint" title="Sized so a stop-out costs exactly your chosen risk % of account — based on the calculator above.">?</span></div>
  <div class="sizing-grid">
    <div class="ind-card"><div class="lbl"><span>Risk Amount</span></div><div class="val">$${sizing.riskAmount.toFixed(2)}</div></div>
    <div class="ind-card"><div class="lbl"><span>Position Size</span></div><div class="val">${sizing.positionUnits.toFixed(4)}</div></div>
    <div class="ind-card"><div class="lbl"><span>Notional Value</span></div><div class="val">$${sizing.positionNotional.toFixed(2)}</div></div>
    <div class="ind-card"><div class="lbl"><span>Suggested Leverage</span></div><div class="val warn">${sizing.leverage.toFixed(2)}×${sizing.wasCapped?'<span class="capnote">capped</span>':''}</div></div>
  </div>`;
}

function projectionHTML(proj){
  if(!proj) return '';
  const up = proj.changePct>=0;
  return `
  <div class="section-label">Speculative Projection <span class="hint" title="A straight-line extrapolation of the last 20 candles. It is not a prediction — real price action regularly breaks away from a trendline like this.">?</span></div>
  <div class="proj-grid">
    <div class="ind-card"><div class="lbl"><span>+${proj.periodsAhead} candles</span></div><div class="val ${up?'pos':'neg'}">${fmtPrice(proj.projected)}</div><div class="mini">${up?'+':''}${proj.changePct.toFixed(2)}%</div></div>
    <div class="ind-card"><div class="lbl"><span>Likely range</span></div><div class="val">${fmtPrice(proj.lower)}–${fmtPrice(proj.upper)}</div><div class="mini">${proj.confidence}</div></div>
  </div>
  <div class="proj-disclaimer">Extrapolated trend only — treat as one possible scenario, not a forecast.</div>`;
}

function levelsHTML(levels){
  return `
  <div class="section-label">Key Levels</div>
  <div class="levels-row">
    <div class="level-box sup"><div class="lbl">Support</div><div class="val">${levels.support?fmtPrice(levels.support):'—'}</div></div>
    <div class="level-box res"><div class="lbl">Resistance</div><div class="val">${levels.resistance?fmtPrice(levels.resistance):'—'}</div></div>
  </div>`;
}

function renderPanel(elId, data, tfKey){
  const el = document.getElementById(elId);
  if(!el) return;
  const dirLabel = data.direction.toUpperCase();
  const badgeClass = data.direction==='long'?'long':data.direction==='short'?'short':'neutral';

  const patternTags = data.patterns.length
    ? data.patterns.map(p=>`<span class="tag ${p.dir===1?'hit-long':'hit-short'}">${p.name}</span>`).join('')
    : '<span class="tag">No pattern at last candle</span>';

  const fibTag = data.fibHitLevel
    ? `<span class="tag hit">Price at ${data.fibHitLevel.ratio} retracement</span>`
    : `<span class="tag">Not at a key fib level</span>`;

  const trendTag = `<span class="tag ${data.trend.dir!=='neutral'?'hit':''}">Trend: ${data.trend.dir}</span>`;

  el.innerHTML = `
    <div class="signal-row">
      <span class="signal-badge ${badgeClass}">${dirLabel}</span>
      <span class="signal-score">confluence <b>${data.score}</b>/100</span>
    </div>
    <div class="gauge-wrap">
      <div class="gauge">${gaugeSVG(data.score, data.direction)}</div>
      <div class="gauge-text">
        <span class="n">${data.score}</span>
        trend + fib + pattern + RSI + MACD + BB + volume
      </div>
    </div>
    <div class="plain-summary">${data.summary}</div>
    ${indicatorGridHTML(data)}
    ${fibBarHTML(data.fibData, data.price)}
    ${bbBarHTML(data.bbVal, data.price)}
    ${levelsHTML(data.levels)}
    <div class="section-label">Signals detected</div>
    <div class="tags">${trendTag}${fibTag}${patternTags}</div>
    ${tradeSetupHTML(data.trade, data.direction, tfKey)}
    ${sizingHTML(data.stopDistPct, data.price)}
    ${projectionHTML(data.projection)}
  `;
}

function renderAllPanels(resultsByTf){
  TIMEFRAMES.forEach(tf=>{
    if(resultsByTf[tf.key]){
      latestByTf[tf.key] = resultsByTf[tf.key];
      renderPanel('panel-'+tf.key, resultsByTf[tf.key], tf.key);
    }
  });
}

function renderHero(resultsByTf){
  const el = document.getElementById('heroCard');
  if(!el) return;
  let weightedScore = 0, weightSum = 0, longVotes = 0, shortVotes = 0;
  const longTfs = [], shortTfs = [];
  TIMEFRAMES.forEach(tf=>{
    const d = resultsByTf[tf.key];
    if(!d) return;
    weightedScore += d.score * tf.weight;
    weightSum += tf.weight;
    if(d.direction==='long'){ longVotes++; longTfs.push(tf.label); }
    else if(d.direction==='short'){ shortVotes++; shortTfs.push(tf.label); }
  });
  const avgScore = weightSum ? Math.round(weightedScore/weightSum) : 0;
  let overall = 'neutral';
  if(longVotes>shortVotes && longVotes>=1 && avgScore>=45) overall = 'long';
  else if(shortVotes>longVotes && shortVotes>=1 && avgScore>=45) overall = 'short';

  const votePills = TIMEFRAMES.map(tf=>{
    const d = resultsByTf[tf.key];
    const cls = d ? d.direction : 'neutral';
    return `<span class="vote-pill ${cls}">${tf.label}: ${d?d.direction.toUpperCase():'—'} (${d?d.score:'—'})</span>`;
  }).join('');

  el.innerHTML = `
    <div class="hero-badge ${overall}">${overall.toUpperCase()}<small>weighted ${avgScore}/100</small></div>
    <div class="hero-text">
      <h3>Overall Bias — 15m / 1h / 1d combined</h3>
      <p>${longVotes} of ${TIMEFRAMES.length} timeframes lean long, ${shortVotes} lean short. Weighted toward higher timeframes (1D counts most, 15m least). Use this as context, not a standalone trigger — check each panel below before acting.</p>
    </div>
    <div class="hero-votes">${votePills}</div>
  `;

  const alertEl = document.getElementById('strongAlert');
  if(!alertEl) return;
  if(longVotes>=2 && overall==='long'){
    alertEl.hidden = false;
    alertEl.className = 'strong-alert long';
    alertEl.innerHTML = `<span class="strong-icon">⚡</span><div><div class="strong-title">Strong Long Confluence</div><div class="strong-body">${longVotes} of ${TIMEFRAMES.length} timeframes agree — ${longTfs.join(' + ')}. Weighted score ${avgScore}/100. Multi-timeframe agreement like this is where confluence setups tend to carry the most weight — worth a closer look at the panels below.</div></div>`;
  } else if(shortVotes>=2 && overall==='short'){
    alertEl.hidden = false;
    alertEl.className = 'strong-alert short';
    alertEl.innerHTML = `<span class="strong-icon">⚡</span><div><div class="strong-title">Strong Short Confluence</div><div class="strong-body">${shortVotes} of ${TIMEFRAMES.length} timeframes agree — ${shortTfs.join(' + ')}. Weighted score ${avgScore}/100. Multi-timeframe agreement like this is where confluence setups tend to carry the most weight — worth a closer look at the panels below.</div></div>`;
  } else {
    alertEl.hidden = true;
    alertEl.innerHTML = '';
  }
}

/* ---------------- toast ---------------- */
function showToast(msg){
  const el = document.getElementById('toast');
  if(!el) return;
  el.textContent = msg;
  el.classList.add('show');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(()=>el.classList.remove('show'), 2400);
}

/* ---------------- performance journal ---------------- */
function loadJournal(){
  try{
    const raw = localStorage.getItem(JOURNAL_KEY);
    return raw ? JSON.parse(raw) : [];
  } catch(e){ return []; }
}

function saveJournal(arr){
  try{
    localStorage.setItem(JOURNAL_KEY, JSON.stringify(arr));
    return true;
  } catch(e){
    showToast("Couldn't save — your browser may be blocking local storage");
    return false;
  }
}

function clearJournal(){ saveJournal([]); }

function deleteTradeEntry(id){
  saveJournal(loadJournal().filter(t=>t.id!==id));
}

function logTrade(tfKey, data, symbol){
  if(!data || !data.trade) return;
  const tf = TIMEFRAMES.find(t=>t.key===tfKey);
  const journal = loadJournal();
  journal.push({
    id: 'jr_'+Date.now()+'_'+Math.random().toString(36).slice(2,7),
    symbol, tfKey, tfLabel: tf ? tf.label : tfKey,
    direction: data.direction,
    entry: data.trade.entry, stop: data.trade.stop, tp1: data.trade.tp1, tp2: data.trade.tp2,
    score: data.score,
    status: 'open',
    loggedAt: Date.now()
  });
  saveJournal(journal);
}

function closeTradeEntry(id, act){
  const journal = loadJournal();
  const idx = journal.findIndex(t=>t.id===id);
  if(idx===-1) return;
  const t = journal[idx];
  let exitPrice, outcomeLabel;
  if(act==='tp1'){ exitPrice = t.tp1; outcomeLabel = 'Target 1 hit'; }
  else if(act==='tp2'){ exitPrice = t.tp2; outcomeLabel = 'Target 2 hit'; }
  else if(act==='stop'){ exitPrice = t.stop; outcomeLabel = 'Stopped out'; }
  else if(act==='market'){
    const canClose = lastResults && t.symbol===currentSymbol && lastResults['15m'];
    if(!canClose) return; // guarded by disabled button, but double-check
    exitPrice = lastResults['15m'].price;
    outcomeLabel = 'Closed at market';
  } else return;

  const riskAbs = Math.abs(t.entry-t.stop) || 1e-9;
  const resultR = ((exitPrice-t.entry)/riskAbs) * (t.direction==='long'?1:-1);
  const status = resultR>0.05 ? 'won' : resultR<-0.05 ? 'lost' : 'breakeven';
  journal[idx] = {...t, status, exitPrice, outcomeLabel, resultR, closedAt: Date.now()};
  saveJournal(journal);
}

function computeJournalStats(journal){
  const closed = journal.filter(t=>t.status!=='open');
  const wins = closed.filter(t=>t.status==='won').length;
  const losses = closed.filter(t=>t.status==='lost').length;
  const breakeven = closed.filter(t=>t.status==='breakeven').length;
  const totalR = closed.reduce((s,t)=>s+t.resultR, 0);
  const avgR = closed.length ? totalR/closed.length : 0;
  const winRate = closed.length ? (wins/closed.length)*100 : 0;
  return { total: journal.length, open: journal.length-closed.length, closedCount: closed.length, wins, losses, breakeven, winRate, avgR, totalR };
}

function journalRowHTML(t){
  const dirClass = t.direction==='long' ? 'long' : 'short';
  const dateStr = new Date(t.loggedAt).toLocaleString(undefined,{month:'short', day:'numeric', hour:'2-digit', minute:'2-digit'});
  let body = `
    <div class="jr-meta">
      <span class="jr-sym">${t.symbol.replace('USDT','')}</span>
      <span class="signal-badge ${dirClass}">${t.direction.toUpperCase()}</span>
      <span class="jr-tf">${t.tfLabel}</span>
      <span class="jr-date">${dateStr}</span>
    </div>
    <div class="jr-prices">
      <span>Entry<b>${fmtPrice(t.entry)}</b></span>
      <span>Stop<b class="hl-short">${fmtPrice(t.stop)}</b></span>
      <span>TP1<b class="hl-long">${fmtPrice(t.tp1)}</b></span>
      <span>TP2<b class="hl-long">${fmtPrice(t.tp2)}</b></span>
    </div>`;

  if(t.status==='open'){
    const canMarketClose = !!(lastResults && t.symbol===currentSymbol && lastResults['15m']);
    body += `
    <div class="jr-actions">
      <button class="jr-btn win" data-act="tp1" data-id="${t.id}">Hit TP1</button>
      <button class="jr-btn win" data-act="tp2" data-id="${t.id}">Hit TP2</button>
      <button class="jr-btn loss" data-act="stop" data-id="${t.id}">Stopped Out</button>
      <button class="jr-btn" data-act="market" data-id="${t.id}" ${canMarketClose?'':'disabled'} title="${canMarketClose?'':'Load '+t.symbol+' in Live Signals to enable'}">Close @ Market</button>
      <button class="jr-btn del" data-act="delete" data-id="${t.id}">Delete</button>
    </div>`;
  } else {
    const rClass = t.resultR>0 ? 'pos' : t.resultR<0 ? 'neg' : '';
    body += `
    <div class="jr-result">
      <span class="jr-outcome">${t.outcomeLabel} · exit ${fmtPrice(t.exitPrice)}</span>
      <span class="jr-r ${rClass}">${t.resultR>=0?'+':''}${t.resultR.toFixed(2)}R</span>
      <button class="jr-btn del" data-act="delete" data-id="${t.id}">Delete</button>
    </div>`;
  }
  return `<div class="journal-row ${t.status}">${body}</div>`;
}

function renderPerformance(){
  const journal = loadJournal();
  const stats = computeJournalStats(journal);
  const statsEl = document.getElementById('perfStats');
  if(statsEl){
    statsEl.innerHTML = `
      <div class="ind-card"><div class="lbl"><span>Logged</span></div><div class="val">${stats.total}</div><div class="mini">${stats.open} open</div></div>
      <div class="ind-card"><div class="lbl"><span>Win Rate</span></div><div class="val ${stats.closedCount?(stats.winRate>=50?'pos':'neg'):''}">${stats.closedCount?stats.winRate.toFixed(0)+'%':'—'}</div><div class="mini">${stats.wins}W / ${stats.losses}L${stats.breakeven?' / '+stats.breakeven+'BE':''}</div></div>
      <div class="ind-card"><div class="lbl"><span>Avg R</span></div><div class="val ${stats.closedCount?(stats.avgR>0?'pos':stats.avgR<0?'neg':''):''}">${stats.closedCount?(stats.avgR>=0?'+':'')+stats.avgR.toFixed(2)+'R':'—'}</div></div>
      <div class="ind-card"><div class="lbl"><span>Total R</span></div><div class="val ${stats.closedCount?(stats.totalR>0?'pos':stats.totalR<0?'neg':''):''}">${stats.closedCount?(stats.totalR>=0?'+':'')+stats.totalR.toFixed(2)+'R':'—'}</div></div>
    `;
  }
  const listEl = document.getElementById('journalList');
  if(!listEl) return;
  if(!journal.length){
    listEl.innerHTML = `<div class="journal-empty">No trades logged yet — head to Live Signals, find a timeframe with a Trade Setup card, and tap “+ Log This Trade” to start tracking your performance here.</div>`;
    return;
  }
  const sorted = [...journal].sort((a,b)=>b.loggedAt-a.loggedAt);
  listEl.innerHTML = sorted.map(journalRowHTML).join('');
}

function handleLogTrade(tfKey){
  const data = latestByTf[tfKey];
  if(!data || !data.trade) return;
  logTrade(tfKey, data, currentSymbol);
  const tf = TIMEFRAMES.find(t=>t.key===tfKey);
  showToast(`Logged ${data.direction.toUpperCase()} ${currentSymbol.replace('USDT','')} · ${tf?tf.label:tfKey}`);
}

/* ---------------- fetch & orchestrate ---------------- */
function buildSymbolBar(){
  const bar = document.getElementById('symbolbar');
  if(!bar) return;
  const frag = document.createDocumentFragment();
  SYMBOLS.forEach(sym=>{
    const btn = document.createElement('button');
    btn.className = 'chip';
    btn.dataset.sym = sym;
    btn.textContent = sym.replace('USDT','');
    frag.appendChild(btn);
  });
  bar.insertBefore(frag, bar.querySelector('.custom-sym'));
}

async function loadSymbol(symbol){
  currentSymbol = symbol;
  const statusEl = document.getElementById('statusLine');
  statusEl.className = 'status';
  statusEl.innerHTML = `<span class="loading-pulse"></span> loading ${symbol} across 15m / 1h / 1d…`;
  document.querySelectorAll('.chip[data-sym]').forEach(c=>{
    c.classList.toggle('active', c.dataset.sym===symbol);
  });

  try{
    const fetches = TIMEFRAMES.map(tf =>
      fetch(`${API}?symbol=${symbol}&interval=${tf.interval}&limit=300`)
        .then(r=>{ if(!r.ok) throw new Error('bad symbol or network'); return r.json(); })
    );
    const tickerFetch = fetch(`${TICKER_API}?symbol=${symbol}`).then(r=>r.json());

    const [rawResults, ticker] = await Promise.all([Promise.all(fetches), tickerFetch]);

    const resultsByTf = {};
    TIMEFRAMES.forEach((tf, idx)=>{
      resultsByTf[tf.key] = analyze(rawResults[idx]);
    });

    const priceData = resultsByTf['15m'];
    document.getElementById('pxVal').textContent = fmtPrice(priceData.price);
    document.getElementById('pxSym').textContent = symbol;
    document.getElementById('pxSpark').innerHTML = sparklineSVG(priceData.closes);
    const chgPct = parseFloat(ticker.priceChangePercent || 0);
    const chgEl = document.getElementById('pxChg');
    chgEl.textContent = (chgPct>=0?'+':'') + chgPct.toFixed(2) + '% 24h';
    chgEl.className = 'chg ' + (chgPct>=0?'up':'down');

    lastResults = resultsByTf;
    renderHero(resultsByTf);
    renderAllPanels(resultsByTf);

    statusEl.textContent = `live — updated ${new Date().toLocaleTimeString()} — refreshes every 30s`;
  } catch(err){
    statusEl.className = 'status err';
    statusEl.textContent = `couldn't load ${symbol}: ${err.message}. Check the symbol is a valid Binance pair (e.g. BTCUSDT).`;
  }
}

function init(){
  buildSymbolBar();
  document.getElementById('symbolbar').addEventListener('click', e=>{
    const btn = e.target.closest('.chip[data-sym]');
    if(btn) loadSymbol(btn.dataset.sym);
  });
  document.getElementById('customGo').addEventListener('click', ()=>{
    const v = document.getElementById('customInput').value.trim().toUpperCase();
    if(v) loadSymbol(v);
  });
  document.getElementById('customInput').addEventListener('keydown', e=>{
    if(e.key==='Enter') document.getElementById('customGo').click();
  });

  ['accountSizeInput','riskPctInput'].forEach(id=>{
    const el = document.getElementById(id);
    if(el) el.addEventListener('input', ()=>{ if(lastResults) renderAllPanels(lastResults); });
  });

  document.querySelector('.panels').addEventListener('click', e=>{
    const btn = e.target.closest('.logtrade-btn');
    if(btn) handleLogTrade(btn.dataset.tf);
  });

  const navtabs = document.querySelector('.navtabs');
  if(navtabs){
    navtabs.addEventListener('click', e=>{
      const btn = e.target.closest('.navtab');
      if(!btn) return;
      document.querySelectorAll('.navtab').forEach(b=>b.classList.toggle('active', b===btn));
      const tab = btn.dataset.tab;
      document.getElementById('liveView').hidden = tab!=='live';
      document.getElementById('perfView').hidden = tab!=='perf';
      if(tab==='perf') renderPerformance();
    });
  }

  const perfView = document.getElementById('perfView');
  if(perfView){
    perfView.addEventListener('click', e=>{
      const btn = e.target.closest('.jr-btn');
      if(!btn || btn.disabled) return;
      const id = btn.dataset.id, act = btn.dataset.act;
      if(act==='delete'){ deleteTradeEntry(id); showToast('Trade removed'); }
      else { closeTradeEntry(id, act); showToast('Trade closed'); }
      renderPerformance();
    });
  }

  const clearBtn = document.getElementById('clearJournalBtn');
  if(clearBtn){
    clearBtn.addEventListener('click', ()=>{
      if(confirm('Delete all logged trades? This cannot be undone.')){
        clearJournal();
        renderPerformance();
        showToast('History cleared');
      }
    });
  }

  loadSymbol(currentSymbol);
  setInterval(()=>loadSymbol(currentSymbol), 30000);
}

document.addEventListener('DOMContentLoaded', init);
