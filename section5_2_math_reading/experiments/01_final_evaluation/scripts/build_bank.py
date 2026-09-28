# -*- coding: utf-8 -*-
"""E24 bank + evidence.

Bank: every pool6 item with a CORRECT verdict from one of the two Codex audits.

Evidence, per Test 1 item:
  PAPER          - the paper excerpt already frozen in pool5/6 for the older items,
                   and a relevance-ranked excerpt built here for the batch-4 items.
  LEAN_OLD       - E22's per-paper block: the paper's Lean declarations in sorted FILE
                   order, truncated at 6,000 chars. Reproduced exactly so that the E22
                   condition is one of this run's arms.
  LEAN_NEW       - the fix. Declarations ranked by relevance to the item, with the
                   declaration named in the item's `basis` forced to the front when the
                   basis is a Lean name. Same 6,000-char budget.
  SHAM           - Lean from the other 15 papers, length-matched per item to LEAN_NEW.

The LEAN_OLD vs LEAN_NEW contrast is the point: it measures directly whether E22's
Test 1 null was an artifact of the answer-bearing theorem being absent from the block.
"""
import json, re, glob, os, collections, hashlib, random, gzip

ROOT = '/ANONYMIZED/Documents/ANONYMIZED_PROJECT'
E22  = ROOT + '/outputs/E22_scale_2026-09-17'
E23  = ROOT + '/outputs/E23_revised_2026-09-18'
E24  = ROOT + '/outputs/E24_final_2026-09-19'
SNAP = ROOT + '/outputs/E01S_paper_understanding_2026-09-13/inputs/source/lean_sources/GenLimit'
PUB  = ROOT + '/public-repo/GenLimitLean/GenLimit'
MOD = {'P01':(SNAP,'Paper01_LanguageGeneration'),'P02':(SNAP,'Paper02_LearningTheory'),
 'P03':(PUB,'Paper03_HallucinationAndModeCollapse'),'P04':(SNAP,'Paper04_ExploringFacetsOfLanguageGeneration'),
 'P05':(PUB,'Paper05_HallucinationsBreadthAndStability'),'P06':(SNAP,'Paper06_NoisyExamples'),
 'P08':(SNAP,'Paper08_HallucinationDetection'),'P09':(SNAP,'Paper09_RepresentativeLanguageGeneration'),
 'P10':(SNAP,'Paper10_UnionClosednessOfLanguageGeneration'),'P12':(SNAP,'Paper12_NoiseLossAndFeedback'),
 'P17':(SNAP,'Paper17_InfiniteContamination'),'P19':(SNAP,'Paper19_EffectOfNoise'),
 'P23':(SNAP,'Paper23_BanachDensityTopologyAndGeometry'),'P28':(SNAP,'Paper28_ContrastiveGeneration'),
 'P31':(PUB,'Paper31_BoundedMemory'),'P39':(PUB,'Paper39_DenseGeneration')}
CLUSTER = ['P02','P06','P12','P17','P19']
CAP = 6000
HEAD = "-- Lean formalization of this paper (statements only; proofs are in the library)\n"

# ---------------------------------------------------------------- Lean extraction
def strip_comments(src):
    out=[];i=0;depth=0
    while i<len(src):
        if src.startswith('/-',i): depth+=1;i+=2;continue
        if src.startswith('-/',i) and depth: depth-=1;i+=2;continue
        if depth: i+=1;continue
        if src.startswith('--',i):
            j=src.find('\n',i); i=len(src) if j<0 else j; continue
        out.append(src[i]); i+=1
    return ''.join(out)
DECL=re.compile(r'^(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([A-Za-z_][\w\']*)',re.M)
TERM=re.compile(r':=|\bby\b|\n\n')
def statements(root,moddir):
    out=[]
    files=sorted(glob.glob(os.path.join(root,moddir,'**','*.lean'),recursive=True))
    f1=os.path.join(root,moddir+'.lean')
    if os.path.exists(f1): files.append(f1)
    for f in files:
        src=strip_comments(open(f,encoding='utf8',errors='ignore').read())
        for m in DECL.finditer(src):
            kind,name=m.group(1),m.group(2)
            w=src[m.end():m.end()+900]; t=TERM.search(w)
            sig=re.sub(r'\s+',' ',(name+(w[:t.start()] if t else w)).strip())
            if 25<len(sig)<240: out.append(("%s %s"%(kind,sig),name))
    seen=set();uniq=[]
    for s,n in out:
        if n not in seen: seen.add(n); uniq.append((s,n))
    return uniq

BLOCKS={p:statements(r,m) for p,(r,m) in MOD.items()}
CORE=statements(SNAP,'Core')
# A global declaration index over every Lean source in the project, including the E12
# machine-checked key file. Needed because an item's `basis` often names a declaration
# that lives outside its own paper's module -- E12.Keys.* in the key file, or a bridge
# theorem declared in a neighbouring paper. LEAN_OLD could never contain those; LEAN_NEW
# can, and a real retriever would surface them too.
GLOBAL={}
for _root in (SNAP, PUB):
    for _f in glob.glob(os.path.join(_root,'**','*.lean'),recursive=True):
        for _s,_n in statements(os.path.dirname(_f), os.path.basename(_f)[:-5]) or []:
            GLOBAL.setdefault(_n,(_s,_n))
for _f in glob.glob(os.path.join(SNAP,'**','*.lean'),recursive=True)+ \
          glob.glob(os.path.join(PUB,'**','*.lean'),recursive=True)+ \
          [ROOT+'/outputs/E12_round2_2026-09-16/corpus/E12Keys.lean']:
    _src=strip_comments(open(_f,encoding='utf8',errors='ignore').read())
    for _m in DECL.finditer(_src):
        _kind,_name=_m.group(1),_m.group(2)
        _w=_src[_m.end():_m.end()+900]; _t=TERM.search(_w)
        _sig=re.sub(r'\s+',' ',(_name+(_w[:_t.start()] if _t else _w)).strip())
        if 25<len(_sig)<240: GLOBAL.setdefault(_name,("%s %s"%(_kind,_sig),_name))

def pack(sigs,cap=CAP):
    out=HEAD; kept=[]
    for s,_ in sigs:
        if len(out)+len(s)>cap: break
        out+=s+"\n"; kept.append(s)
    return out,kept

LEAN_OLD={p:pack(BLOCKS[p]+CORE)[0] for p in MOD}

# ---------------------------------------------------------------- relevance
STOP=set('''the a an of in to is are and or not for with that which this it its by at on be as if
then when we our their there any all each such from also thus hence so than paper theorem lemma
definition proposition corollary equation remark claim let suppose case every some no exists exist
given following holds hold true false where does do statement result set sets one two both same
other only over under above below must may can cannot always never'''.split())
WORD=re.compile(r"[A-Za-z][A-Za-z0-9_']{2,}")
def toks(s):
    s=re.sub(r"([a-z0-9])([A-Z])",r"\1 \2",s or '')
    return {w.lower() for w in WORD.findall(s) if w.lower() not in STOP and len(w)>2}
def is_leanname(b):
    b=(b or '').strip()
    return bool(b) and ' ' not in b and len(b)>6 and re.fullmatch(r"[A-Za-z0-9_.']+",b) is not None

def lean_new(it):
    """Per-question block: basis declaration first when known, then relevance order."""
    p=it['papers'][0]
    if p not in MOD: p='P02'
    pool=BLOCKS[p]+CORE
    q=toks(it['stem'])|toks(it.get('basis',''))|toks(it.get('label',''))
    forced=[]
    b=(it.get('basis') or '').strip()
    if is_leanname(b):
        leaf=b.split('.')[-1]
        forced=[(s,n) for s,n in pool if n==leaf]
        if not forced and leaf in GLOBAL: forced=[GLOBAL[leaf]]
    rest=[(s,n) for s,n in pool if (s,n) not in forced]
    scored=sorted(rest,key=lambda sn: -(len(q & toks(sn[0]))/ (len(toks(sn[0]))**0.5+1)))
    return pack(forced+scored)

rng=random.Random(20260919)
def sham_for(p,target_len):
    others=[s for q in MOD if q!=p for s in BLOCKS[q]]
    rng.shuffle(others)
    return pack(others,cap=target_len)[0]

# ---------------------------------------------------------------- paper excerpts
PK=json.load(open(E22+'/inputs/packets16.json'))
def relevance(text,stem):
    w=toks(stem)
    if not w: return 0
    t=text.lower()
    return sum(1 for x in w if x in t)
def paper_excerpt(it):
    if it.get('paper_text'): return it['paper_text']
    if it['cat']=='cross':
        named=list(it['papers']); blocks=[]
        for q in CLUSTER:
            keys=[k for k in PK if k.startswith(q+'|')]
            if not keys: continue
            ranked=sorted(keys,key=lambda k:-relevance(PK[k],it['stem']))
            for k in ranked[:2 if q in named else 1]:
                blocks.append(PK[k])
        return "\n\n".join(b[:2600] for b in blocks)[:13000]
    p=it['papers'][0]
    keys=[k for k in PK if k.startswith(p+'|')]
    if not keys: return ''
    ranked=sorted(keys,key=lambda k:-relevance(PK[k],it['stem']))
    return "\n\n".join(PK[k][:4400] for k in ranked[:3])[:13000]

# ---------------------------------------------------------------- build
def main():
    pool=json.load(open(E23+'/inputs/pool6.json'))
    bank=[x for x in pool if x.get('codex_verdict')=='CORRECT']
    cov_old=cov_new=n_leanname=0
    out=[]
    for it in bank:
        rec=dict(it)
        rec['test']=1 if it['cat'] in ('within','within_from_cross') else 2
        rec['paper_text']=paper_excerpt(it)
        if rec['test']==1:
            p=it['papers'][0] if it['papers'][0] in MOD else 'P02'
            rec['lean_old']=LEAN_OLD[p]
            nb,_=lean_new(it)
            rec['lean_new']=nb
            rec['lean_sham']=sham_for(p,len(nb))
            b=(it.get('basis') or '').strip()
            if is_leanname(b) and b.split('.')[-1] in GLOBAL:
                n_leanname+=1
                leaf=re.escape(b.split('.')[-1])
                cov_old += bool(re.search(r'\b%s\b'%leaf, rec['lean_old']))
                cov_new += bool(re.search(r'\b%s\b'%leaf, rec['lean_new']))
        out.append(rec)
    payload=json.dumps(out,ensure_ascii=False).encode('utf8')
    with open(E24+'/inputs/bank24.json.gz','wb') as raw:
        with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as f:
            f.write(payload)
    t1=[x for x in out if x['test']==1]; t2=[x for x in out if x['test']==2]
    print("bank: %d items | Test 1 %d | Test 2 %d"%(len(out),len(t1),len(t2)))
    print("paper excerpt chars: med %d max %d"%(
        sorted(len(x['paper_text']) for x in out)[len(out)//2], max(len(x['paper_text']) for x in out)))
    print()
    print("LEAN COVERAGE on the %d Test-1 items whose basis names a declaration that EXISTS"%n_leanname)
    print("(79 further items name author shorthand such as NoisyExamples.DefinitionD1, which is")
    print(" not a declaration anywhere in the tree; they are excluded from this denominator.)")
    print("  LEAN_OLD (E22, file order) : %3d/%3d = %.1f%%"%(cov_old,n_leanname,100*cov_old/max(1,n_leanname)))
    print("  LEAN_NEW (per question)    : %3d/%3d = %.1f%%"%(cov_new,n_leanname,100*cov_new/max(1,n_leanname)))
    ml=[(len(x['lean_new']),len(x['lean_sham'])) for x in t1]
    print("  length match new vs sham: worst |1 - sham/new| = %.4f"%max(abs(1-b/a) for a,b in ml))
    print("  t2_flag:",dict(collections.Counter(x.get('t2_flag') for x in t2)))
if __name__=='__main__': main()
