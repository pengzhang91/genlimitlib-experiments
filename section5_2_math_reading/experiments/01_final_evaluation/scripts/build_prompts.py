# -*- coding: utf-8 -*-
"""Freeze E24 prompts.

Stage 1 -- closed-book screen: CLOSED arm, rotations 0-1, every item.
Stage 2 -- confirmatory:       all arms, rotations 2-4, items that survived the screen.

Rotations 2-4 are held out from the screen, so the reported contrasts are not computed
on the same observations that selected the items.

  python3 scripts/build_prompts.py 1
  python3 scripts/build_prompts.py 2 analysis/screen.json
"""
import json,sys,hashlib,collections,os,gzip
H=lambda s: hashlib.sha256(s.encode()).hexdigest()
E22='/ANONYMIZED/Documents/ANONYMIZED_PROJECT/outputs/E22_scale_2026-09-17'

def load_bank():
    if os.path.exists('inputs/bank24.json'):
        with open('inputs/bank24.json', encoding='utf8') as f: return json.load(f)
    with gzip.open('inputs/bank24.json.gz', mode='rt', encoding='utf8') as f: return json.load(f)

BANK=load_bank()
MAP=open(E22+'/inputs/MAP5.txt',encoding='utf8').read()
SHAMMAP=open(E22+'/inputs/SHAMMAP5.txt',encoding='utf8').read()

SYSTEM=("Answer the multiple-choice mathematical question. Choose exactly one option. "
        "When reference material is supplied, use it to interpret the mathematical "
        "definitions and assumptions. When it is absent, answer using your mathematical "
        "knowledge. Do not use external tools. Respond with exactly one character: "
        "A, B, C, D, or E. Do not write anything else.")
L=['A','B','C','D','E']
SUP="\n\nSupplementary reference material:\n"
ARMS={1:['CLOSED','PAPER','PAPER_LEAN_OLD','PAPER_LEAN_NEW','PAPER_SHAM'],
      2:['CLOSED','PAPERS','PAPERS_MAP','PAPERS_SHAMMAP']}
BUDGET=34000   # local guard; the real token count is checked on the host

def ev(it,arm):
    # Lazy: a Test 2 item carries no lean_* fields, so the branches must not all be
    # evaluated. An eager dict literal here raised KeyError on the first cross item.
    if arm=='CLOSED': return None
    P=it['paper_text']
    if arm in ('PAPER','PAPERS'):    return P
    if arm=='PAPER_LEAN_OLD':        return P+SUP+it['lean_old']
    if arm=='PAPER_LEAN_NEW':        return P+SUP+it['lean_new']
    if arm=='PAPER_SHAM':            return P+SUP+it['lean_sham']
    if arm=='PAPERS_MAP':            return P+SUP+MAP
    if arm=='PAPERS_SHAMMAP':        return P+SUP+SHAMMAP
    raise KeyError(arm)

def main():
    stage=int(sys.argv[1]); keep=None
    if stage==2:
        keep=set(json.load(open(sys.argv[2]))['retained'])
        print("screen retained %d items"%len(keep))
    rots=[0,1] if stage==1 else [2,3,4]
    for test in (1,2):
        items=[i for i in BANK if i['test']==test]
        if keep is not None: items=[i for i in items if i['id'] in keep]
        arms=['CLOSED'] if stage==1 else ARMS[test]
        rows=[];keys=[]
        for it in items:
            opts=[it['correct']]+list(it['distractors'])
            # rotation anchored to the item's stable id, so stage 1 and stage 2 agree
            base=int(H(it['id'])[:8],16)%5
            for k in rots:
                shift=(base+k)%5
                perm=[None]*5; perm[shift]=0
                rest=[1,2,3,4] if k%2==0 else [4,3,2,1]
                for j,slot in enumerate([s for s in range(5) if s!=shift]): perm[slot]=rest[j]
                blk="\n".join("%s. %s"%(L[j],opts[p]) for j,p in enumerate(perm))
                for arm in arms:
                    e=ev(it,arm)
                    user=(("Reference material:\n"+e+"\n\n") if e else "")+"Question:\n"+it['stem']+"\n\n"+blk
                    rid="T%d_%s_%s_r%d"%(test,it['id'],arm,k)
                    rows.append(dict(request_id=rid,item_id=it['id'],test=test,
                        papers=it['papers'],cat=it['cat'],arm=arm,rot=k,stage=stage,
                        t2_flag=it.get('t2_flag'),construct=it.get('construct'),src=it.get('src'),
                        messages=[{"role":"system","content":SYSTEM},{"role":"user","content":user}],
                        prompt_sha256=H(SYSTEM+"\x00"+user),chars=len(SYSTEM)+len(user)))
                    keys.append(dict(request_id=rid,gold=L[shift]))
        over=[r for r in rows if r['chars']>BUDGET]
        if over:
            raise SystemExit("REFUSING TO FREEZE: %d prompts over %d chars (longest %d)"%(
                len(over),BUDGET,max(r['chars'] for r in over)))
        tag="screen" if stage==1 else "confirm"
        prompt_path='prompts/t%d_%s.jsonl'%(test,tag)
        if stage==2:
            with open(prompt_path+'.gz','wb') as raw:
                with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as f:
                    for r in rows: f.write((json.dumps(r,ensure_ascii=False)+"\n").encode('utf8'))
        else:
            with open(prompt_path,'w') as f:
                for r in rows: f.write(json.dumps(r,ensure_ascii=False)+"\n")
        with open('inputs/t%d_%s_key.jsonl'%(test,tag),'w') as f:
            for r in keys: f.write(json.dumps(r,ensure_ascii=False)+"\n")
        print("Test %d %-7s: %5d prompts | %d items | arms %s"%(test,tag,len(rows),len(items),arms))
        print("   gold balance %s | max %d chars | FREEZE %s"%(
            dict(collections.Counter(k['gold'] for k in keys)),
            max(r['chars'] for r in rows) if rows else 0,
            H("".join(sorted(r['prompt_sha256'] for r in rows)))[:16]))
if __name__=='__main__': main()
