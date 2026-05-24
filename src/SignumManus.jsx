import { useState, useRef, useMemo, useEffect, useCallback } from "react";

/* ═══════════════════════════════════════════════════
   ALGORITHMS
═══════════════════════════════════════════════════ */

function streamline(pts, passes) {
  if (passes === 0 || pts.length < 3) return pts;
  let r = pts;
  for (let p = 0; p < passes; p++) {
    const s = [r[0]];
    for (let i = 1; i < r.length - 1; i++)
      s.push({ x:(r[i-1].x+r[i].x*2+r[i+1].x)/4, y:(r[i-1].y+r[i].y*2+r[i+1].y)/4, t:r[i].t });
    s.push(r[r.length-1]);
    r = s;
  }
  return r;
}

function rdp(pts, eps) {
  if (pts.length <= 2) return pts;
  const sqd = (p,a,b) => {
    let x=a.x,y=a.y,dx=b.x-x,dy=b.y-y;
    if(dx||dy){const t=((p.x-x)*dx+(p.y-y)*dy)/(dx*dx+dy*dy);if(t>1){x=b.x;y=b.y}else if(t>0){x+=dx*t;y+=dy*t}}
    return (p.x-x)**2+(p.y-y)**2;
  };
  const sq=eps*eps,res=[pts[0]];
  const go=(f,l)=>{let mx=sq,idx=-1;
    for(let i=f+1;i<l;i++){const d=sqd(pts[i],pts[f],pts[l]);if(d>mx){mx=d;idx=i}}
    if(idx>-1){if(idx-f>1)go(f,idx);res.push(pts[idx]);if(l-idx>1)go(idx,l)}};
  go(0,pts.length-1); res.push(pts[pts.length-1]);
  return res;
}

function toBezier(pts, sm=0.2) {
  if(!pts?.length) return '';
  if(pts.length===1) return `M${pts[0].x},${pts[0].y}`;
  const cp=(c,p,n,rev)=>{
    const px=p||c,nx=n||c;
    const a=Math.atan2(nx.y-px.y,nx.x-px.x)+(rev?Math.PI:0);
    const l=Math.hypot(nx.x-px.x,nx.y-px.y)*sm;
    return[+(c.x+Math.cos(a)*l).toFixed(2),+(c.y+Math.sin(a)*l).toFixed(2)];
  };
  return pts.reduce((d,p,i,a)=>{
    if(!i) return `M${+p.x.toFixed(2)},${+p.y.toFixed(2)}`;
    const[c1x,c1y]=cp(a[i-1],a[i-2],p),[c2x,c2y]=cp(p,a[i-1],a[i+1],true);
    return `${d}C${c1x},${c1y} ${c2x},${c2y} ${+p.x.toFixed(2)},${+p.y.toFixed(2)}`;
  },'');
}

function svgLen(d) {
  try{const p=document.createElementNS('http://www.w3.org/2000/svg','path');p.setAttribute('d',d);return p.getTotalLength()||0}
  catch{return 0}
}

const chainLen = pts => pts.reduce((s,p,i)=>i?s+Math.hypot(p.x-pts[i-1].x,p.y-pts[i-1].y):0,0);

function buildStrokeLinear(stroke, n=24, inEase=0, outEase=0) {
  const t0=stroke[0].t,t1=stroke.at(-1).t,span=t1-t0;
  if(!span) return 'linear(0,1)';
  let dist=0;
  const rLen=chainLen(stroke);
  const pairs=stroke.map((p,pi)=>{
    if(pi>0) dist+=Math.hypot(p.x-stroke[pi-1].x,p.y-stroke[pi-1].y);
    return{t:(p.t-t0)/span,v:rLen?dist/rLen:pi/(stroke.length-1)};
  });
  const raw=[];
  for(let i=0;i<=n;i++){
    const t=i/n; let v=pairs.at(-1).v;
    for(let j=0;j<pairs.length-1;j++){
      const[a,b]=[pairs[j],pairs[j+1]];
      if(t>=a.t&&t<=b.t){v=a.v+(b.t>a.t?(t-a.t)/(b.t-a.t):0)*(b.v-a.v);break}
    }
    raw.push(Math.min(1,Math.max(0,v)));
  }
  const D=0.3;
  const stops=raw.map((v,i)=>{
    const t=i/n;
    if(inEase>0&&t<=D){const lt=t/D,ev=raw[Math.round(D*n)];return ev*Math.pow(lt,1+inEase*2)}
    if(outEase>0&&t>=1-D){const lt=(t-(1-D))/D,sv=raw[Math.round((1-D)*n)];return sv+(1-sv)*Math.pow(lt,1/(1+outEase*2))}
    return v;
  });
  return `linear(${stops.map((v,i)=>i===0||i===n?v.toFixed(4):`${v.toFixed(4)} ${(i/n*100).toFixed(1)}%`).join(',')})`;
}

/* ═══════════════════════════════════════════════════
   THEME
═══════════════════════════════════════════════════ */
const C = {
  canvas:      '#ffffff',
  panelBg:     '#f2f0ec',
  headerBg:    '#eceae5',
  border:      '#c8c4bc',
  text:        '#1c1a17',
  sub:         '#4a4640',
  dim:         '#7a746c',
  btnDark:     '#1c1a17',
  btnDarkText: '#f5f3ef',
  btnLight:    '#ffffff',
  code:        '#e6e3dc',
  tabActive:   '#ffffff',
  // Solid mid-grey — clearly visible on white canvas without being harsh
  defaultGuide:'#a8a29a',
};
const MONO = "'JetBrains Mono','Fira Code','Courier New',monospace";

/* ═══════════════════════════════════════════════════
   CANVAS BACKGROUND
   All three guide types use a unified density scale:
     1 = sparse (fewest guides / largest spacing)
    10 = dense  (most guides / smallest spacing)
   Sliding RIGHT always means MORE. Never exported.
═══════════════════════════════════════════════════ */

// density 1–10 → pixel spacing (right = denser = smaller spacing)
const densityToLineSpacing = d => Math.round(82 - d * 6.8);  // 1→75px  10→14px
const densityToGridSize    = d => Math.round(86 - d * 7.4);  // 1→79px  10→12px
const densityToDotSpacing  = d => Math.round(66 - d * 5.4);  // 1→61px  10→12px

function BgPattern({ type, lineDensity, gridDensity, dotDensity, color }) {
  if (type === 'lines') {
    const sp = densityToLineSpacing(lineDensity);
    return (
      <pattern id="bg-guide" x="0" y="0" width="9999" height={sp} patternUnits="userSpaceOnUse">
        <line x1="0" y1={sp} x2="9999" y2={sp} stroke={color} strokeWidth="0.7"/>
      </pattern>
    );
  }
  if (type === 'grid') {
    const sz = densityToGridSize(gridDensity);
    return (
      <pattern id="bg-guide" width={sz} height={sz} patternUnits="userSpaceOnUse">
        <path d={`M${sz} 0L0 0 0 ${sz}`} fill="none" stroke={color} strokeWidth="0.6"/>
      </pattern>
    );
  }
  if (type === 'dots') {
    const sp = densityToDotSpacing(dotDensity);
    return (
      <pattern id="bg-guide" width={sp} height={sp} patternUnits="userSpaceOnUse">
        <circle cx="0" cy="0" r="1.4" fill={color}/>
      </pattern>
    );
  }
  return null;
}

/* ═══════════════════════════════════════════════════
   UI ATOMS
═══════════════════════════════════════════════════ */

const SH = ({label}) => (
  <div style={{fontSize:9,letterSpacing:'0.14em',color:C.dim,textTransform:'uppercase',fontFamily:MONO,marginBottom:10}}>
    {label}
  </div>
);

const HR = () => <div style={{borderTop:`1px solid ${C.border}`,margin:'14px 0'}}/>;

function SliderRow({label,value,min,max,step,fmt,onChange}) {
  return (
    <div style={{marginBottom:12}}>
      <div style={{display:'flex',justifyContent:'space-between',marginBottom:5}}>
        <span style={{fontSize:10,color:C.sub,fontFamily:MONO}}>{label}</span>
        <span style={{fontSize:10,color:C.text,fontFamily:MONO,fontWeight:700}}>{fmt(value)}</span>
      </div>
      <input type="range" min={min} max={max} step={step} value={value}
        onChange={e=>onChange(parseFloat(e.target.value))} style={{width:'100%',cursor:'pointer'}}/>
    </div>
  );
}

function ColorSwatch({label, value, onChange}) {
  const ref = useRef(null);
  return (
    <div style={{display:'flex',alignItems:'center',justifyContent:'space-between',marginBottom:12}}>
      <span style={{fontSize:10,color:C.sub,fontFamily:MONO}}>{label}</span>
      <div style={{display:'flex',alignItems:'center',gap:8}}>
        <span style={{fontSize:10,color:C.dim,fontFamily:MONO}}>{value}</span>
        <button onClick={()=>ref.current?.click()} style={{
          width:22,height:22,borderRadius:'50%',background:value,
          border:`2px solid ${C.border}`,cursor:'pointer',padding:0,flexShrink:0,
          boxShadow:'0 1px 4px rgba(0,0,0,0.18)',
        }}/>
        <input ref={ref} type="color" value={value} onChange={e=>onChange(e.target.value)}
          style={{position:'absolute',opacity:0,width:0,height:0,pointerEvents:'none'}}/>
      </div>
    </div>
  );
}

function SegmentGroup({options, value, onChange}) {
  return (
    <div style={{display:'flex',gap:3,marginBottom:12}}>
      {options.map(([val,label])=>(
        <button key={val} onClick={()=>onChange(val)} style={{
          flex:1,padding:'6px 0',fontSize:8,borderRadius:2,fontFamily:MONO,
          background:value===val?C.btnDark:C.btnLight,
          border:`1px solid ${value===val?C.btnDark:C.border}`,
          color:value===val?C.btnDarkText:C.sub,
          cursor:'pointer',letterSpacing:'0.06em',textTransform:'uppercase',lineHeight:1.2,
        }}>{label}</button>
      ))}
    </div>
  );
}

function Btn({onClick,disabled,dark,small,children,style={}}) {
  return (
    <button onClick={onClick} disabled={disabled} style={{
      padding:small?'9px 12px':'9px 0',
      width:small?'auto':'100%',
      borderRadius:3,fontFamily:MONO,
      background:dark?(disabled?'#bbb':C.btnDark):C.btnLight,
      border:`1px solid ${disabled?'#bbb':dark?C.btnDark:C.border}`,
      color:dark?(disabled?'#888':C.btnDarkText):(disabled?'#aaa':C.text),
      cursor:disabled?'not-allowed':'pointer',
      fontSize:10,letterSpacing:'0.07em',marginBottom:small?0:6,
      transition:'opacity 0.15s',lineHeight:1,...style,
    }}>{children}</button>
  );
}

/* ═══════════════════════════════════════════════════
   MAIN COMPONENT
═══════════════════════════════════════════════════ */

export default function SignumManus() {
  const containerRef = useRef(null);
  const svgRef       = useRef(null);

  const [narrow,    setNarrow]    = useState(typeof window!=='undefined'?window.innerWidth<660:false);
  const [mobileTab, setMobileTab] = useState('stroke'); // stroke is first and most important

  // Drawing history
  const [strokes,   setStrokes]   = useState([]);
  const [undoStack, setUndoStack] = useState([]);
  const [redoStack, setRedoStack] = useState([]);
  const [live,      setLive]      = useState(null);
  const [inking,    setInking]    = useState(false);

  // Stroke settings
  const [strmln,   setStrmln]   = useState(3);
  const [simp,     setSimp]     = useState(1.5);
  const [bsm,      setBsm]      = useState(0.2);
  const [strokeW,  setStrokeW]  = useState(2);
  const [inkColor, setInkColor] = useState('#111111');

  // Animation settings
  const [spd,     setSpd]     = useState(1.0);
  const [dly,     setDly]     = useState(0.5);
  const [inEase,  setInEase]  = useState(0);
  const [outEase, setOutEase] = useState(0);

  // Canvas guide settings
  // All density sliders: 1 (sparse) → 10 (dense). Right = more. Always.
  const [bgType,       setBgType]       = useState('blank');
  const [lineDensity,  setLineDensity]  = useState(5);
  const [gridDensity,  setGridDensity]  = useState(5);
  const [dotDensity,   setDotDensity]   = useState(5);
  const [guideColor,   setGuideColor]   = useState(C.defaultGuide);

  // UI state
  const [animKey,       setAnimKey]       = useState(0);
  const [previewing,    setPreviewing]    = useState(false);
  const [copied,        setCopied]        = useState(false);
  const [showCodeModal, setShowCodeModal] = useState(false);

  /* Responsive */
  useEffect(()=>{
    const ro=new ResizeObserver(e=>setNarrow(e[0].contentRect.width<660));
    if(containerRef.current) ro.observe(containerRef.current);
    return()=>ro.disconnect();
  },[]);

  /* Undo / Redo */
  const undo=useCallback(()=>{
    if(!undoStack.length) return;
    setRedoStack(r=>[strokes,...r]); setStrokes(undoStack.at(-1)); setUndoStack(u=>u.slice(0,-1)); setPreviewing(false);
  },[undoStack,strokes]);

  const redo=useCallback(()=>{
    if(!redoStack.length) return;
    setUndoStack(u=>[...u,strokes]); setStrokes(redoStack[0]); setRedoStack(r=>r.slice(1)); setPreviewing(false);
  },[redoStack,strokes]);

  useEffect(()=>{
    const h=e=>{
      if((e.ctrlKey||e.metaKey)&&e.key==='z'&&!e.shiftKey){e.preventDefault();undo()}
      if((e.ctrlKey||e.metaKey)&&(e.key==='y'||(e.key==='z'&&e.shiftKey))){e.preventDefault();redo()}
    };
    window.addEventListener('keydown',h); return()=>window.removeEventListener('keydown',h);
  },[undo,redo]);

  const pushStroke=useCallback((stroke)=>{
    setUndoStack(u=>[...u,strokes]); setRedoStack([]); setStrokes(s=>[...s,stroke]);
  },[strokes]);

  const doErase=useCallback(()=>{
    if(!strokes.length) return;
    setUndoStack(u=>[...u,strokes]); setRedoStack([]); setStrokes([]); setLive(null); setPreviewing(false);
  },[strokes]);

  /* Per-stroke geometry + sequential animation timing */
  const computed=useMemo(()=>{
    if(!strokes.length) return null;
    const g0=strokes[0][0].t;
    const strokeData=strokes.map((stroke,si)=>{
      const path=toBezier(rdp(streamline(stroke,strmln),simp),bsm);
      const len=svgLen(path);
      const animDelay=dly+(stroke[0].t-g0)/1000/spd;
      const duration=Math.max(0.06,(stroke.at(-1).t-stroke[0].t)/1000)/spd;
      const timing=buildStrokeLinear(stroke,24,si===0?inEase:0,si===strokes.length-1?outEase:0);
      return{path,len,animDelay,duration,timing};
    });
    const last=strokeData.at(-1);
    return{strokeData,totalDur:(last.animDelay+last.duration).toFixed(2)};
  },[strokes,strmln,simp,bsm,spd,dly,inEase,outEase]);

  const livePath=live?.length>1?toBezier(live,bsm):null;

  /* Pointer events */
  const xy=e=>{const r=svgRef.current.getBoundingClientRect(),s=e.touches?.[0]??e;return{x:s.clientX-r.left,y:s.clientY-r.top,t:Date.now()}};
  const onDown=e=>{e.preventDefault();setPreviewing(false);setLive([xy(e)]);setInking(true)};
  const onMove=e=>{e.preventDefault();if(!inking)return;setLive(p=>[...p,xy(e)])};
  const onUp=e=>{
    e.preventDefault();if(!inking)return;
    setLive(p=>{if(p?.length>1)pushStroke(p);return null});
    setInking(false);
  };

  const doPreview=()=>{setAnimKey(k=>k+1);setPreviewing(true)};

  /* SVG+CSS export — guides never included */
  const svgCode=computed?(()=>{
    const el=svgRef.current;
    const w=el?.clientWidth||480,h=el?.clientHeight||320;
    const{strokeData}=computed;
    const css=[
      '@keyframes draw { to { stroke-dashoffset: 0; } }',
      ...strokeData.map((s,i)=>{const d=(s.len+strokeW+2).toFixed(2);return`.s${i}{stroke-dasharray:${d};stroke-dashoffset:${d};animation:draw ${s.duration.toFixed(3)}s ${s.animDelay.toFixed(3)}s ${s.timing} forwards}`;})
    ].join('\n    ');
    const paths=strokeData.map((s,i)=>
      `  <path class="s${i}" d="${s.path}" stroke="${inkColor}" fill="none"\n    stroke-width="${strokeW}" stroke-linecap="round" stroke-linejoin="round"/>`
    ).join('\n');
    return `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${w} ${h}" width="${w}" height="${h}">\n  <style>\n    ${css}\n  </style>\n${paths}\n</svg>`;
  })():'';

  const doCopy=()=>{
    if(!svgCode) return;

    const succeed=()=>{setCopied(true);setTimeout(()=>setCopied(false),2500)};

    // Level 1: modern clipboard API (blocked in some sandboxed iframes)
    if(navigator.clipboard?.writeText){
      navigator.clipboard.writeText(svgCode).then(succeed).catch(()=>fallback());
    } else {
      fallback();
    }

    // Level 2: execCommand via hidden textarea
    function fallback(){
      try{
        const ta=document.createElement('textarea');
        ta.value=svgCode;
        ta.setAttribute('readonly','');
        ta.style.cssText='position:fixed;top:0;left:0;width:2px;height:2px;opacity:0;pointer-events:none';
        document.body.appendChild(ta);
        ta.focus(); ta.select();
        const ok=document.execCommand('copy');
        document.body.removeChild(ta);
        if(ok) succeed(); else setShowCodeModal(true);
      }catch{
        setShowCodeModal(true);
      }
    }
  };

  /* ── Control blocks (shared between desktop + mobile) ── */

  // Section order: Stroke → Animate → Canvas → Export

  const strokeControls = (
    <>
      <SliderRow label="streamline" value={strmln} min={0} max={10} step={1}
        fmt={v=>v===0?'off':`${v}×`} onChange={setStrmln}/>
      <SliderRow label="simplify" value={simp} min={0} max={5} step={0.1}
        fmt={v=>v.toFixed(1)} onChange={setSimp}/>
      <SliderRow label="smooth" value={bsm} min={0} max={0.5} step={0.01}
        fmt={v=>v.toFixed(2)} onChange={setBsm}/>
      <SliderRow label="width" value={strokeW} min={0.5} max={6} step={0.5}
        fmt={v=>`${v}px`} onChange={setStrokeW}/>
      <ColorSwatch label="ink colour" value={inkColor} onChange={setInkColor}/>
    </>
  );

  const animControls = (
    <>
      <SliderRow label="speed" value={spd} min={0.2} max={3} step={0.1}
        fmt={v=>`${v.toFixed(1)}×`} onChange={setSpd}/>
      <SliderRow label="delay" value={dly} min={0} max={3} step={0.1}
        fmt={v=>`${v.toFixed(1)}s`} onChange={setDly}/>
      <SliderRow label="ease in" value={inEase} min={0} max={3} step={0.1}
        fmt={v=>v===0?'off':v.toFixed(1)} onChange={setInEase}/>
      <SliderRow label="ease out" value={outEase} min={0} max={3} step={0.1}
        fmt={v=>v===0?'off':v.toFixed(1)} onChange={setOutEase}/>
    </>
  );

  // All three guide types use a unified density scale.
  // 1 = sparse (fewest/largest), 10 = dense (most/smallest). Right = always more.
  const canvasControls = (
    <>
      <SegmentGroup
        value={bgType} onChange={setBgType}
        options={[['blank','blank'],['lines','lines'],['grid','grid'],['dots','dots']]}
      />
      {bgType==='lines' && (
        <SliderRow label="density" value={lineDensity} min={1} max={10} step={1}
          fmt={v=>`${v}`} onChange={setLineDensity}/>
      )}
      {bgType==='grid' && (
        <SliderRow label="density" value={gridDensity} min={1} max={10} step={1}
          fmt={v=>`${v}`} onChange={setGridDensity}/>
      )}
      {bgType==='dots' && (
        <SliderRow label="density" value={dotDensity} min={1} max={10} step={1}
          fmt={v=>`${v}`} onChange={setDotDensity}/>
      )}
      {bgType!=='blank' && (
        <ColorSwatch label="guide colour" value={guideColor} onChange={setGuideColor}/>
      )}
    </>
  );

  /* ── SVG drawing area ── */

  const drawArea = (
    <div style={{flex:1,position:'relative',overflow:'hidden',minHeight:0}}>
      <svg ref={svgRef} width="100%" height="100%"
        style={{display:'block',cursor:'crosshair',touchAction:'none'}}
        onMouseDown={onDown} onMouseMove={onMove} onMouseUp={onUp} onMouseLeave={onUp}
        onTouchStart={onDown} onTouchMove={onMove} onTouchEnd={onUp}
      >
        <defs>
          {/* Guide pattern lives only here — never written to svgCode */}
          <BgPattern
            type={bgType}
            lineDensity={lineDensity}
            gridDensity={gridDensity}
            dotDensity={dotDensity}
            color={guideColor}
          />
        </defs>

        {/* 1. White paper */}
        <rect width="100%" height="100%" fill={C.canvas}/>
        {/* 2. Guide overlay */}
        {bgType!=='blank' && <rect width="100%" height="100%" fill="url(#bg-guide)"/>}
        {/* 3. Completed strokes (static) */}
        {!previewing && computed?.strokeData.map((s,i)=>(
          <path key={i} d={s.path} fill="none" stroke={inkColor}
            strokeWidth={strokeW} strokeLinecap="round" strokeLinejoin="round"/>
        ))}
        {/* 4. Live stroke */}
        {livePath && (
          <path d={livePath} fill="none" stroke={inkColor}
            strokeWidth={strokeW} strokeLinecap="round" strokeLinejoin="round" opacity={0.4}/>
        )}
        {/* 5. Sequential animated preview */}
        {previewing && computed && computed.strokeData.map((s,i)=>(
          <path
            key={`a${animKey}-${i}`}
            d={s.path} fill="none" stroke={inkColor}
            strokeWidth={strokeW} strokeLinecap="round" strokeLinejoin="round"
            style={{
              strokeDasharray:  s.len + strokeW + 2,
              strokeDashoffset: s.len + strokeW + 2,
              animation:`sig_draw ${s.duration.toFixed(3)}s ${s.animDelay.toFixed(3)}s ${s.timing} forwards`,
            }}
          />
        ))}
      </svg>

      <div style={{
        position:'absolute',bottom:0,left:0,right:0,
        padding:'5px 14px',borderTop:`1px solid ${C.border}`,
        background:'rgba(242,240,236,0.93)',backdropFilter:'blur(4px)',
        display:'flex',justifyContent:'space-between',
        fontSize:9,color:C.dim,letterSpacing:'0.08em',fontFamily:MONO,
      }}>
        <span>SIGNUM MANUS</span>
        {computed
          ?<span>{strokes.length} stroke{strokes.length!==1?'s':''} · {computed.totalDur}s</span>
          :<span>draw to begin</span>
        }
      </div>
    </div>
  );

  /* ── Desktop panel — order: Stroke → Animate → Canvas → Export ── */

  const desktopPanel = (
    <div style={{
      width:230,background:C.panelBg,borderLeft:`1px solid ${C.border}`,
      padding:'16px 16px',overflowY:'auto',flexShrink:0,display:'flex',flexDirection:'column',
    }}>

      <SH label="stroke"/>
      {strokeControls}
      <div style={{display:'flex',gap:6,marginBottom:6}}>
        <Btn onClick={undo} disabled={!undoStack.length} small style={{flex:1}}>↩ undo</Btn>
        <Btn onClick={redo} disabled={!redoStack.length} small style={{flex:1}}>redo ↪</Btn>
      </div>
      <Btn onClick={doErase} disabled={!strokes.length}>erase all</Btn>

      <HR/>

      <SH label="animation"/>
      {animControls}
      <Btn onClick={doPreview} disabled={!computed} dark>▶  preview</Btn>

      <HR/>

      <SH label="canvas"/>
      {canvasControls}

      <HR/>

      <SH label="export"/>
      <Btn onClick={doCopy} disabled={!computed} dark={copied}>
        {copied ? '✓  Code Copied!' : 'Copy Code'}
      </Btn>

      {computed && (
        <>
          <div style={{display:'flex',flexDirection:'column',gap:5,margin:'6px 0 10px'}}>
            {[['strokes',String(strokes.length)],['total dur',`${computed.totalDur}s`],['delay',`${dly}s`]]
              .map(([k,v])=>(
                <div key={k} style={{display:'flex',justifyContent:'space-between'}}>
                  <span style={{fontSize:9,color:C.dim,letterSpacing:'0.08em',textTransform:'uppercase'}}>{k}</span>
                  <span style={{fontSize:9,color:C.sub,fontFamily:MONO}}>{v}</span>
                </div>
              ))}
          </div>
          {/* Selectable textarea — click to select all, copy manually if clipboard blocked */}
          <textarea
            readOnly
            value={svgCode}
            onClick={e=>{e.target.select();doCopy()}}
            style={{
              width:'100%',padding:'8px 10px',background:C.code,border:`1px solid ${C.border}`,
              borderRadius:2,fontSize:8,color:C.sub,fontFamily:MONO,
              resize:'none',height:110,lineHeight:1.6,cursor:'pointer',outline:'none',
              boxSizing:'border-box',
            }}
          />
          <div style={{fontSize:8,color:C.dim,marginTop:3}}>click code to select · then ⌘C / Ctrl+C</div>
        </>
      )}

      {!computed && (
        <div style={{marginTop:4,fontSize:9,color:C.dim,lineHeight:2.1}}>
          <div style={{color:C.text,fontWeight:700,marginBottom:4,fontSize:10}}>how to use</div>
          <div>① draw your signature</div>
          <div>② adjust sliders</div>
          <div>③ preview animation</div>
          <div>④ copy SVG + CSS</div>
          <div style={{marginTop:8,color:C.dim,lineHeight:1.8}}>
            <b>streamline</b> — removes jitter<br/>
            <b>ease in/out</b> — pen settle &amp; lift<br/>
            <b>canvas guides</b> — not exported<br/>
            <b>⌘Z / ⌘⇧Z</b> — undo / redo
          </div>
        </div>
      )}
    </div>
  );

  /* ── Mobile panel — tabs: Stroke → Animate → Canvas → Export ── */

  const MOBILE_TABS = [
    ['stroke', '✏'],
    ['animate','▶'],
    ['canvas', '⊞'],
    ['export', '⇑'],
  ];

  const mobilePanel = (
    <div style={{background:C.panelBg,borderTop:`1px solid ${C.border}`,flexShrink:0}}>

      <div style={{display:'flex',gap:6,padding:'10px 12px',borderBottom:`1px solid ${C.border}`,alignItems:'center'}}>
        <Btn onClick={undo} disabled={!undoStack.length} small>↩</Btn>
        <Btn onClick={redo} disabled={!redoStack.length} small>↪</Btn>
        <Btn onClick={doErase} disabled={!strokes.length} small>✕</Btn>
        <div style={{flex:1}}/>
        <Btn onClick={doPreview} disabled={!computed} dark small>▶ play</Btn>
        <Btn onClick={doCopy} disabled={!computed} dark={copied} small style={{minWidth:72}}>
          {copied?'✓ Copied':'Copy Code'}
        </Btn>
      </div>

      <div style={{display:'flex',borderBottom:`1px solid ${C.border}`}}>
        {MOBILE_TABS.map(([tab,icon])=>(
          <button key={tab} onClick={()=>setMobileTab(tab)} style={{
            flex:1,padding:'8px 0',fontSize:9,
            background:mobileTab===tab?C.tabActive:'transparent',
            border:'none',borderBottom:mobileTab===tab?`2px solid ${C.text}`:'2px solid transparent',
            cursor:'pointer',letterSpacing:'0.07em',textTransform:'uppercase',
            color:mobileTab===tab?C.text:C.dim,fontFamily:MONO,
          }}>{icon} {tab}</button>
        ))}
      </div>

      <div style={{overflowY:'auto',maxHeight:230,padding:'12px 14px'}}>
        {mobileTab==='stroke' && (
          <div style={{display:'grid',gridTemplateColumns:'1fr 1fr',gap:'0 20px'}}>
            {strokeControls}
          </div>
        )}
        {mobileTab==='animate' && (
          <div style={{display:'grid',gridTemplateColumns:'1fr 1fr',gap:'0 20px'}}>
            {animControls}
            <div style={{gridColumn:'1/-1'}}>
              <Btn onClick={doPreview} disabled={!computed} dark>▶  preview</Btn>
            </div>
          </div>
        )}
        {mobileTab==='canvas' && (
          <div>{canvasControls}</div>
        )}
        {mobileTab==='export' && (
          <div>
            {computed ? (
              <>
                <div style={{display:'flex',gap:6,marginBottom:10}}>
                  {[['strokes',String(strokes.length)],['dur',`${computed.totalDur}s`]].map(([k,v])=>(
                    <div key={k} style={{flex:1,padding:'6px 8px',background:C.code,borderRadius:3,textAlign:'center'}}>
                      <div style={{fontSize:8,color:C.dim,letterSpacing:'0.1em',textTransform:'uppercase',marginBottom:2}}>{k}</div>
                      <div style={{fontSize:12,color:C.text,fontFamily:MONO,fontWeight:700}}>{v}</div>
                    </div>
                  ))}
                </div>
                <textarea
                  readOnly
                  value={svgCode}
                  onClick={e=>{e.target.select();doCopy()}}
                  style={{
                    width:'100%',padding:'8px 10px',background:C.code,border:`1px solid ${C.border}`,
                    borderRadius:2,fontSize:8,color:C.sub,fontFamily:MONO,
                    resize:'none',height:120,lineHeight:1.6,cursor:'pointer',outline:'none',
                    boxSizing:'border-box',
                  }}
                />
                <div style={{fontSize:8,color:C.dim,marginTop:3}}>tap to select · then copy</div>
              </>
            ) : (
              <div style={{fontSize:10,color:C.dim,lineHeight:2,marginTop:8}}>
                Draw something first, then your SVG + CSS code appears here.
              </div>
            )}
          </div>
        )}
      </div>
    </div>
  );

  /* ═══ RENDER ═══════════════════════════════════════════════════ */
  return (
    <div ref={containerRef} style={{
      display:'flex',flexDirection:'column',height:'100vh',
      background:C.panelBg,fontFamily:MONO,fontSize:11,color:C.text,
    }}>
      <style>{`
        *{box-sizing:border-box}body{margin:0}
        input[type=range]{-webkit-appearance:none;appearance:none;height:3px;border-radius:2px;background:${C.border};outline:none;width:100%}
        input[type=range]::-webkit-slider-thumb{-webkit-appearance:none;width:14px;height:14px;border-radius:50%;background:${C.btnDark};cursor:pointer;border:2px solid ${C.panelBg};box-shadow:0 1px 3px rgba(0,0,0,0.22)}
        input[type=range]::-moz-range-thumb{width:14px;height:14px;border-radius:50%;background:${C.btnDark};cursor:pointer;border:2px solid ${C.panelBg}}
        button:hover:not(:disabled){opacity:0.72}
        textarea{font-family:${MONO};-webkit-overflow-scrolling:touch}
        @keyframes sig_draw{to{stroke-dashoffset:0}}
      `}</style>

      {/* Code modal — last-resort fallback when clipboard is fully blocked */}
      {showCodeModal && (
        <div style={{
          position:'fixed',inset:0,background:'rgba(0,0,0,0.55)',zIndex:999,
          display:'flex',alignItems:'center',justifyContent:'center',padding:20,
        }} onClick={()=>setShowCodeModal(false)}>
          <div style={{
            background:C.panelBg,border:`1px solid ${C.border}`,borderRadius:4,
            padding:20,width:'100%',maxWidth:560,
          }} onClick={e=>e.stopPropagation()}>
            <div style={{display:'flex',justifyContent:'space-between',alignItems:'center',marginBottom:12}}>
              <span style={{fontSize:11,fontWeight:700,color:C.text,fontFamily:MONO,letterSpacing:'0.06em'}}>
                SELECT ALL &amp; COPY  (⌘A then ⌘C)
              </span>
              <button onClick={()=>setShowCodeModal(false)} style={{
                background:'none',border:'none',cursor:'pointer',fontSize:16,color:C.dim,lineHeight:1,
              }}>✕</button>
            </div>
            <textarea
              readOnly
              value={svgCode}
              onFocus={e=>e.target.select()}
              onClick={e=>e.target.select()}
              style={{
                width:'100%',height:260,padding:'10px 12px',
                background:C.code,border:`1px solid ${C.border}`,borderRadius:2,
                fontSize:9,color:C.sub,fontFamily:MONO,lineHeight:1.6,
                resize:'none',outline:'none',
              }}
            />
          </div>
        </div>
      )}

      <div style={{
        display:'flex',alignItems:'center',justifyContent:'space-between',
        padding:`${narrow?9:11}px 16px`,
        borderBottom:`1px solid ${C.border}`,background:C.headerBg,flexShrink:0,
      }}>
        <div>
          <span style={{fontSize:narrow?12:14,fontWeight:700,letterSpacing:'0.04em',color:C.text}}>
            Signum Manus
          </span>
          {!narrow && <span style={{fontSize:10,color:C.dim,marginLeft:10}}>signature → SVG + CSS animation</span>}
        </div>
        {computed && (
          <span style={{fontSize:9,color:C.dim,letterSpacing:'0.08em'}}>
            {strokes.length} stroke{strokes.length!==1?'s':''} · {computed.totalDur}s
          </span>
        )}
      </div>

      <div style={{display:'flex',flex:1,flexDirection:narrow?'column':'row',overflow:'hidden',minHeight:0}}>
        {drawArea}
        {narrow ? mobilePanel : desktopPanel}
      </div>
    </div>
  );
}
