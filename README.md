# WOWII Conjecture 198a — a proof, formalized in Lean 4

**Theorem** (Graffiti.pc conjecture 198a, E. DeLaViña, *Written on the Wall II*, 2006).
If `G` is a connected graph on at least two vertices with `b(G) ≤ 2 + ecc_avg(G)`, where `b(G)` is the order
of a largest induced bipartite subgraph and `ecc_avg(G)` is the average eccentricity, then `G` has a
Hamiltonian path.

The informal proof is in [`PROOF.md`](PROOF.md). The Lean proof (Lean 4.33.1, Mathlib `v4.33.1`) is
`WOW198a.conjecture198a` in [`WOW198a/Main.lean`](WOW198a/Main.lean). It proves exactly the statement
`WrittenOnTheWallII.GraphConjecture198a.conjecture198a` of
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures); this is checked by
[`WOW198a/Check.lean`](WOW198a/Check.lean).

| File | Content |
|---|---|
| `Basic.lean` | bipartite certificates, geodesics, Hamiltonian walks from lists |
| `L1.lean` | `b(G) = diam(G) + 1` ⟹ Hamiltonian path |
| `L2.lean` | self-centred and `diam ≥ 3` ⟹ `b(G) ≥ diam + 3` |
| `L3.lean` | diameter 2, no dominating vertex, `b(G) ≤ 4` ⟹ Hamiltonian path |
| `Main.lean` | the theorem |

```
lake exe cache get   # Mathlib cache
lake build
lake env lean WOW198a/Check.lean
# 'WOW198a.conjecture198a' depends on axioms: [propext, Classical.choice, Quot.sound]
```
