"""Independent small-instance diagnostics for the archived gamma chapter.

Numerical LP solves are diagnostic only; they are not proof certificates.
Run with Python 3 + numpy + scipy. No manuscript files are changed.
"""
import itertools as it
import json
import math
import random
import numpy as np
from scipy.optimize import linprog

TOL = 1e-7
solves = 0


def solve(c, **kwargs):
    global solves
    solves += 1
    ans = linprog(c, method="highs", **kwargs)
    if not ans.success:
        raise AssertionError((ans.status, ans.message, kwargs))
    return ans


def coefficient(infinite, finite, outside, f):
    m, nf = len(infinite[0]), len(f)
    best = -math.inf
    for u in infinite:
        rows, rhs = [], []
        for v in infinite:
            rows.append(list(np.subtract(v, u)) + [0] * nf)
            rhs.append(0)
        for v in finite:
            rows.append(list(np.subtract(v, u)) + [0] * nf)
            rhs.append(1)
        for w, j in outside:
            rows.append(list(np.subtract(w, u)) + [int(i in j) for i in f])
            rhs.append(1)
        for chosen in it.product([0, 1], repeat=len(finite)):
            c = np.zeros(m + nf)
            for (v, count), use in zip(finite.items(), chosen):
                if use:
                    c[:m] -= count * np.subtract(v, u)
            ans = solve(c, A_ub=rows, b_ub=rhs,
                        A_eq=[[0] * m + [1] * nf], b_eq=[1],
                        bounds=[(None, None)] * m + [(0, None)] * nf)
            best = max(best, -ans.fun)
    return best


def tangent(infinite, finite, outside, f, counts, u):
    m, nf = len(u), len(f)
    types = [(w, [0] * nf) for w in infinite]
    types += [(v, [int(s == finite[v])] * nf) for v, s in counts.items()]
    types += [(w, [int(i not in j) for i in f]) for w, j in outside]
    types = [(w, d) for w, d in types if w != u]
    h = sum((s * np.subtract(v, u) for v, s in counts.items()), np.zeros(m))
    nq = len(types)
    aeq = np.zeros((m, nq + 1))
    aub = np.zeros((nf, nq + 1))
    for j, (w, d) in enumerate(types):
        aeq[:, j] = np.subtract(w, u)
        aub[:, j] = d
    aub[:, -1] = -1
    ans = solve([0] * nq + [1], A_eq=aeq, b_eq=h,
                A_ub=aub, b_ub=np.zeros(nf), bounds=[(0, None)] * (nq + 1))
    assert sum(ans.x[:-1]) <= sum(abs(h)) + TOL
    assert sum(abs(h)) <= m * sum(counts.values()) + TOL
    return ans.fun


def signature_for_f(rows, f):
    core = {}
    outside = set()
    fs = set(f)
    for v, members, count in rows:
        if fs <= members:
            core[v] = core.get(v, 0) + count
        else:
            outside.add((v, tuple(sorted(fs & members))))
    infinite = [v for v, c in core.items() if math.isinf(c)]
    finite = {v: int(c) for v, c in core.items() if not math.isinf(c)}
    return infinite, finite, sorted(outside)


def generic_checks():
    rng = random.Random(20260925)
    signatures, subfamilies, tangent_cases = 0, 0, 0
    max_gap = 0.0
    while signatures < 30:
        rows = []
        for v in it.product([0, 1], repeat=2):
            for mem in [set(), {0}, {1}, {0, 1}]:
                state = rng.choices([0, 1, 2, math.inf], [6, 2, 1, 1])[0]
                if state:
                    rows.append((v, mem, state))
        if any(not any(i in mem and math.isinf(c) for _, mem, c in rows)
               for i in [0, 1]):
            continue
        signatures += 1
        for f in [(0,), (1,), (0, 1)]:
            infinite, finite, outside = signature_for_f(rows, f)
            if not infinite:
                continue
            subfamilies += 1
            gamma = coefficient(infinite, finite, outside, f)
            values = []
            for ss in it.product(*(range(c + 1) for c in finite.values())):
                counts = dict(zip(finite, ss))
                for u in infinite:
                    values.append(tangent(infinite, finite, outside, f, counts, u))
                    tangent_cases += 1
            gap = abs(max(values) - gamma)
            max_gap = max(max_gap, gap)
            assert gap < TOL, (rows, f, gamma, max(values))
            if finite:
                assert gamma + TOL >= max(finite.values()) / len(f)
            else:
                assert abs(gamma) < TOL
            assert gamma <= sum(finite.values()) + TOL
    return dict(signatures=signatures, infinite_subfamilies=subfamilies,
                count_anchor_cases=tangent_cases, max_equality_residual=max_gap)


def exact_examples():
    private = []
    for n in range(2, 6):
        for b in [1, 2, 5]:
            f = tuple(range(n))
            got = coefficient([(0,)], {(1,): b}, [((1,), (i,)) for i in f], f)
            expected = b * (1 - 1/n)
            assert abs(got - expected) < TOL
            private.append([n, b, got])
    parity = []
    for m in range(1, 4):
        profiles = list(it.product([0, 1], repeat=m))
        infinite = [v for v in profiles if sum(v) % 2 == 0]
        finite = {v: 1 for v in profiles if sum(v) % 2 == 1}
        got = coefficient(infinite, finite, [], (0,))
        assert abs(got - 1) < TOL
        parity.append([m, got])
    return dict(private_tail=private, parity=parity)


def maxcut_reduction(n, edges):
    m = 2*n + 3
    d, f, c = 2*n, 2*n+1, 2*n+2
    weight = 2*len(edges) + 1
    finite = {}
    def add(indices, count):
        v = tuple(int(i in indices) for i in range(m))
        assert v not in finite
        finite[v] = count
    for indices in [[d], [f], [c, d, f]]:
        add(indices, weight)
    for i in range(n):
        add([i, n+i], weight)
        add([i], 1)
        add([n+i], 1)
    for i, j in edges:
        add([i, n+j, c], 1)
        add([j, n+i, c], 1)
    got = coefficient([(0,) * m], finite, [], (0,))
    cut = max(sum(bits[i] != bits[j] for i, j in edges)
              for bits in it.product([0, 1], repeat=n))
    expected = weight*(n+3) + n + cut
    assert abs(got - expected) < TOL, (n, edges, got, expected)
    return dict(vertices=n, edges=edges, profiles=len(finite),
                computed_gamma=got, expected_gamma=expected)


if __name__ == "__main__":
    result = {"generic": generic_checks(), "examples": exact_examples(),
              "maxcut": [maxcut_reduction(0, []), maxcut_reduction(1, []),
                         maxcut_reduction(2, []), maxcut_reduction(2, [(0, 1)])]}
    result["lp_solves"] = solves
    print(json.dumps(result, indent=2))
