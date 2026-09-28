# -*- coding: utf-8 -*-
"""E24 analysis.

Stage 1 screen : CLOSED arm, rotations 0-1. Retain items scoring <= 0.50.
Stage 2 report : all arms, rotations 2-4 (held out from the screen).

Test 1 is reported twice: on the closed-book-screened set, and on the doubly
screened subset that additionally leaves the PAPER arm below ceiling -- the only
subset with room for a formalization effect, following E22.

Uncertainty: paired percentile bootstrap resampling CLUSTERS of paraphrased items,
not items. Some questions restate the same underlying relation, and treating them as
independent overstates precision.
"""
import json, sys, collections, random, math, os, gzip

def open_text(p):
    if os.path.exists(p):
        return open(p, encoding='utf8', errors='ignore')
    gz = p + '.gz'
    if os.path.exists(gz):
        return gzip.open(gz, mode='rt', encoding='utf8', errors='ignore')
    raise FileNotFoundError(p)

def load_jsonl(p):
    with open_text(p) as f:
        return [json.loads(l) for l in f]

def load_json(p):
    with open_text(p) as f:
        return json.load(f)

def cluster_of(it):
    lab = (it.get('label') or '').strip()
    if lab: return "%s|%s" % ('+'.join(it['papers']), lab)
    return it['id']

def acc_by(recs, keys):
    """item -> arm -> list of 0/1"""
    d = collections.defaultdict(lambda: collections.defaultdict(list))
    for r in recs:
        k = keys.get(r['request_id'])
        if k is None or r.get('status') != 'completed': continue
        d[r['_item']][r['_arm']].append(1 if r.get('argmax') == k else 0)
    return d

def boot(pairs, clusters, B=10000, seed=20260919):
    """pairs: list of (cluster, delta). Percentile CI over cluster resamples."""
    by = collections.defaultdict(list)
    for c, d in pairs: by[c].append(d)
    cl = list(by)
    if not cl: return (float('nan'),)*3
    rng = random.Random(seed)
    point = sum(sum(by[c])/len(by[c]) for c in cl)/len(cl)
    out = []
    for _ in range(B):
        s = [by[cl[rng.randrange(len(cl))]] for _ in range(len(cl))]
        out.append(sum(sum(x)/len(x) for x in s)/len(s))
    out.sort()
    return point, out[int(.025*B)], out[int(.975*B)]

def main():
    bank = {x['id']: x for x in load_json('inputs/bank24.json')}
    # ---------- stage 1 ----------
    if sys.argv[1] == 'screen':
        retained = []; rows = []
        for test in (1, 2):
            keys = {r['request_id']: r['gold'] for r in load_jsonl('inputs/t%d_screen_key.jsonl' % test)}
            meta = {r['request_id']: r for r in load_jsonl('prompts/t%d_screen.jsonl' % test)}
            recs = load_jsonl('runs/t%d_screen_raw.jsonl' % test)
            per = collections.defaultdict(list)
            for r in recs:
                m = meta.get(r['request_id'])
                if not m or r.get('status') != 'completed': continue
                per[m['item_id']].append(1 if r.get('argmax') == keys[r['request_id']] else 0)
            keep = [i for i, v in per.items() if sum(v)/len(v) <= 0.50]
            retained += keep
            rows.append((test, len(per), len(keep), sum(sum(v)/len(v) for v in per.values())/max(1,len(per))))
        json.dump(dict(retained=retained), open('analysis/screen.json','w'))
        print("stage 1 -- closed-book screen (rotations 0-1)")
        for test, n, k, a in rows:
            print("  Test %d: %4d items, mean closed-book accuracy %.3f, retained %d (%.0f%%)"%(test,n,a,k,100*k/max(1,n)))
        print("  total retained: %d -> analysis/screen.json" % len(retained))
        return

    # ---------- stage 2 ----------
    out = {}
    for test in (1, 2):
        f = 'runs/t%d_confirm_raw.jsonl' % test
        if not os.path.exists(f): continue
        keys = {r['request_id']: r['gold'] for r in load_jsonl('inputs/t%d_confirm_key.jsonl' % test)}
        meta = {r['request_id']: r for r in load_jsonl('prompts/t%d_confirm.jsonl' % test)}
        recs = []
        for r in load_jsonl(f):
            m = meta.get(r['request_id'])
            if not m: continue
            r['_item'] = m['item_id']; r['_arm'] = m['arm']; recs.append(r)
        d = acc_by(recs, keys)
        arms = sorted({r['_arm'] for r in recs})
        base = 'PAPER' if test == 1 else 'PAPERS'

        def report(items, tag):
            items = [i for i in items if i in d]
            print("\n=== Test %d | %s | n=%d items, %d clusters ==="%(
                test, tag, len(items), len({cluster_of(bank[i]) for i in items})))
            means = {}
            for a in arms:
                v = [sum(d[i][a])/len(d[i][a]) for i in items if d[i].get(a)]
                means[a] = sum(v)/len(v) if v else float('nan')
                print("  %-16s %.3f   (n=%d)" % (a, means[a], len(v)))
            print("  --- contrasts (paired within item, bootstrap over clusters) ---")
            res = {}
            for a in arms:
                if a in (base, 'CLOSED'): continue
                pr = [(cluster_of(bank[i]), sum(d[i][a])/len(d[i][a]) - sum(d[i][base])/len(d[i][base]))
                      for i in items if d[i].get(a) and d[i].get(base)]
                p, lo, hi = boot(pr, None)
                res["%s - %s"%(a,base)] = (p,lo,hi)
                print("  %-34s %+.3f  [%+.3f, %+.3f]" % ("%s - %s"%(a,base), p, lo, hi))
            if test == 1 and 'PAPER_LEAN_NEW' in arms and 'PAPER_SHAM' in arms:
                for a in ('PAPER_LEAN_NEW','PAPER_LEAN_OLD'):
                    pr=[(cluster_of(bank[i]), sum(d[i][a])/len(d[i][a]) - sum(d[i]['PAPER_SHAM'])/len(d[i]['PAPER_SHAM']))
                        for i in items if d[i].get(a) and d[i].get('PAPER_SHAM')]
                    p,lo,hi=boot(pr,None); res["%s - PAPER_SHAM"%a]=(p,lo,hi)
                    print("  %-34s %+.3f  [%+.3f, %+.3f]"%("%s - PAPER_SHAM"%a,p,lo,hi))
                pr=[(cluster_of(bank[i]), sum(d[i]['PAPER_LEAN_NEW'])/len(d[i]['PAPER_LEAN_NEW'])
                                        - sum(d[i]['PAPER_LEAN_OLD'])/len(d[i]['PAPER_LEAN_OLD']))
                    for i in items if d[i].get('PAPER_LEAN_NEW') and d[i].get('PAPER_LEAN_OLD')]
                p,lo,hi=boot(pr,None); res["LEAN_NEW - LEAN_OLD"]=(p,lo,hi)
                print("  %-34s %+.3f  [%+.3f, %+.3f]"%("LEAN_NEW - LEAN_OLD",p,lo,hi))
            if test == 2 and 'PAPERS_MAP' in arms and 'PAPERS_SHAMMAP' in arms:
                pr=[(cluster_of(bank[i]), sum(d[i]['PAPERS_MAP'])/len(d[i]['PAPERS_MAP'])
                                        - sum(d[i]['PAPERS_SHAMMAP'])/len(d[i]['PAPERS_SHAMMAP']))
                    for i in items if d[i].get('PAPERS_MAP') and d[i].get('PAPERS_SHAMMAP')]
                p,lo,hi=boot(pr,None); res["PAPERS_MAP - PAPERS_SHAMMAP"]=(p,lo,hi)
                print("  %-34s %+.3f  [%+.3f, %+.3f]"%("PAPERS_MAP - PAPERS_SHAMMAP",p,lo,hi))
            return dict(n=len(items), clusters=len({cluster_of(bank[i]) for i in items}),
                        means=means, contrasts=res)

        allit = list(d)
        out["test%d_screened"%test] = report(allit, "closed-book screened")
        if test == 1:
            dbl = [i for i in allit if d[i].get('PAPER') and sum(d[i]['PAPER'])/len(d[i]['PAPER']) < 1.0]
            out["test1_double"] = report(dbl, "doubly screened (PAPER arm off ceiling)")
            # The subset where the manipulation actually bites: the answer-bearing
            # declaration is ABSENT from LEAN_OLD and PRESENT in LEAN_NEW. If E22's null
            # was caused by the theorem being missing, the effect should appear here.
            import re as _re
            def _leaf(x):
                b=(x.get('basis') or '').strip()
                if not b or ' ' in b or len(b)<=6 or not _re.fullmatch(r"[A-Za-z0-9_.']+",b): return None
                return b.split('.')[-1]
            manip=[]; manip_thm=[]
            for i in allit:
                x=bank[i]; lf=_leaf(x)
                if not lf: continue
                inold=bool(_re.search(r'\b%s\b'%_re.escape(lf), x.get('lean_old','')))
                m=_re.search(r'^(theorem|lemma|def|abbrev) %s\b'%_re.escape(lf), x.get('lean_new',''), _re.M)
                if m and not inold:
                    manip.append(i)
                    if m.group(1) in ('theorem','lemma'): manip_thm.append(i)
            if len(manip)>=10:
                out["test1_manipulated"]=report(manip,"LEAN_OLD misses the declaration, LEAN_NEW supplies it")
            if len(manip_thm)>=10:
                out["test1_manipulated_thm"]=report(manip_thm,"same, restricted to theorem/lemma bases (signature = statement)")
        if test == 2:
            for flag in ('multiple_source_candidate','single_paper','stem_only','repository_only'):
                sub=[i for i in allit if bank[i].get('t2_flag')==flag]
                if len(sub)>=15: out["test2_%s"%flag]=report(sub, "t2_flag = %s"%flag)
            b4=[i for i in allit if bank[i].get('batch')==4]
            if len(b4)>=15: out["test2_batch4"]=report(b4, "batch 4 only")
    json.dump(out, open('analysis/results.json','w'), indent=1)
    print("\nwrote analysis/results.json")
if __name__ == '__main__': main()
