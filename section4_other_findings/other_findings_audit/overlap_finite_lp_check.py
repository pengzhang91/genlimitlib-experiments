"""Finite numerical stress tests of the overlap formulas, not a proof certificate.

A point type is a pair of residual-atom vertices of two laminar trees.
At least one fresh type may be realized infinitely often; other types may
have only forbidden representatives. A type can have both observed mass
and a fresh representative. Some forbidden types receive zero mass.
"""

import itertools
import json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog


def incidence(parents):
    n = len(parents)
    out = np.zeros((n, n - 1))
    for node in range(n):
        cur = node
        while cur:
            out[node, cur - 1] = 1
            cur = parents[cur]
    return out


def boolean_costs(parents, realized):
    """Enumerate integer tree costs; independently compare to the l1 LP."""
    n = len(parents)
    profiles = incidence(parents)[realized]
    costs = {}
    for labels in itertools.product([0, 1], repeat=n):
        trace = tuple(labels[i] for i in realized)
        cut = sum(labels[j] != labels[parents[j]] for j in range(1, n))
        costs[trace] = min(costs.get(trace, n), cut)
    for trace, cut in costs.items():
        # c0 is free, c_1,...,c_{n-1} are signed, and z bounds abs(c).
        obj = np.r_[np.zeros(n), np.ones(n - 1)]
        aeq = np.c_[np.ones(len(realized)), profiles, np.zeros_like(profiles)]
        aub = np.zeros((2 * (n - 1), 2 * n - 1))
        for j in range(n - 1):
            aub[2 * j, 1 + j] = 1
            aub[2 * j + 1, 1 + j] = -1
            aub[2 * j : 2 * j + 2, n + j] = -1
        result = linprog(obj, A_ub=aub, b_ub=np.zeros(len(aub)),
                         A_eq=aeq, b_eq=trace,
                         bounds=[(None, None)] * n + [(0, None)] * (n - 1),
                         method="highs")
        assert result.success, result.message
        assert abs(result.fun - cut) < 1e-8, (parents, realized, trace, cut, result.fun)
    return costs


def run_case(rng, serial):
    sizes = [int(rng.integers(2, 6)), int(rng.integers(2, 6))]
    parents = [[-1] + [int(rng.integers(j)) for j in range(1, n)] for n in sizes]
    pairs = list(itertools.product(range(sizes[0]), range(sizes[1])))
    rng.shuffle(pairs)
    pairs = pairs[:int(rng.integers(2, len(pairs) + 1))]
    fresh = rng.random(len(pairs)) < 0.5
    fresh[int(rng.integers(len(pairs)))] = True
    weights = rng.integers(0, 8, len(pairs)).astype(float)
    weights[int(rng.integers(len(pairs)))] += 1
    weights /= weights.sum()
    profiles = [incidence(p) for p in parents]
    test_matrix = np.array([np.r_[profiles[0][a], profiles[1][b]] for a, b in pairs])
    means = weights @ test_matrix
    fresh_matrix = test_matrix[fresh].T
    num_q = int(fresh.sum())
    result = linprog(np.r_[np.zeros(num_q), 1.],
                     A_ub=np.r_[np.c_[fresh_matrix, -np.ones(len(means))],
                                np.c_[-fresh_matrix, -np.ones(len(means))]],
                     b_ub=np.r_[means, -means],
                     A_eq=np.array([np.r_[np.ones(num_q), 0.]]), b_eq=[1.],
                     bounds=[(0, None)] * (num_q + 1), method="highs")
    assert result.success, result.message
    realized = [sorted({p[block] for p in pairs}) for block in range(2)]
    costs = [boolean_costs(parents[i], realized[i]) for i in range(2)]
    maps = [{node: j for j, node in enumerate(nodes)} for nodes in realized]
    best = 0.
    for u, p in costs[0].items():
        um = np.array([u[maps[0][a]] for a, _ in pairs])
        for v, q in costs[1].items():
            if p + q == 0:
                continue
            vm = np.array([v[maps[1][b]] for _, b in pairs])
            if np.any((um * vm)[fresh]):
                continue
            best = max(best, max(float(weights @ (um + vm)) - 1., 0.) / (p + q))
    err = abs(result.fun - best)
    assert err < 1e-8, (serial, pairs, fresh.tolist(), weights.tolist(), result.fun, best)
    return {"case": serial, "primal": float(result.fun), "bottleneck": best,
            "absolute_error": err,
            "empty_tree_vertices": sum(sizes[i] - len(realized[i]) for i in range(2)),
            "zero_mass_forbidden_types": int(np.sum((weights == 0) & ~fresh))}


if __name__ == "__main__":
    rng = np.random.default_rng(20260926)
    results = [run_case(rng, i) for i in range(160)]
    summary = {"seed": 20260926, "cases": len(results), "status": "PASS",
               "max_absolute_error": max(r["absolute_error"] for r in results),
               "cases_with_empty_tree_vertices": sum(r["empty_tree_vertices"] > 0 for r in results),
               "cases_with_zero_mass_forbidden_types": sum(r["zero_mass_forbidden_types"] > 0 for r in results),
               "note": "Floating-point LP checks supplement the independent written proof review; not formal verification.",
               "results": results}
    Path(__file__).with_suffix(".json").write_text(json.dumps(summary, indent=2) + "\n")
    print({k: v for k, v in summary.items() if k != "results"})
