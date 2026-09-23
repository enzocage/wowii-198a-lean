# A proof of Graffiti.pc conjecture WOWII 198a

**Conjecture 198a** (DeLaVina, Graffiti.pc, *Written on the Wall II*, 12 Jan 2006, status "O").
Let G be a simple connected graph with n > 1 vertices. If b(G) ≤ 2 + ecc_avg(G), then G has a
Hamiltonian path.

Here b(G) is the order of a largest induced bipartite subgraph and ecc_avg(G) = (1/n) Σ_v ecc(v) is the
average eccentricity. (The companion conjecture 198, with ecc_avg taken over the vertices of maximum degree,
was proved by R. Stong in 2010; 198a is still listed as open on the WOWII page and in
`google-deepmind/formal-conjectures`.)

Notation: D = diam(G), and d(·,·) is the graph distance. A set S ⊆ V is *bipartite* if G[S] is bipartite.
To show that S is bipartite it is enough to give f : S → ℕ such that f(x) ≢ f(y) (mod 2) whenever xy ∈ E.

## Two easy bounds

Let P = v₀v₁…v_D be a shortest path between two vertices at distance D. Then d(v_i, v_j) = |i − j|.
In particular v_i v_j ∈ E ⇔ |i − j| = 1, and a common neighbour of v_i and v_j forces |i − j| ≤ 2.

* V(P) is bipartite (take f(v_i) = i), so **b(G) ≥ D + 1**.
* ecc(v) ≤ D for all v, so ecc_avg ≤ D, and the hypothesis gives **b(G) ≤ D + 2**.

Hence b(G) ∈ {D+1, D+2}. If b(G) = D + 2, the hypothesis gives ecc_avg ≥ D, so **every vertex has
eccentricity exactly D** (G is self-centred).

## Lemma L1: b(G) = D + 1 ⇒ G has a Hamiltonian path

(No eccentricity assumption is needed.)

*(a) Every x ∉ P is adjacent to two consecutive vertices v_i, v_{i+1}.* Otherwise the P-neighbours of x
(which lie in a window of three consecutive indices) all have the same parity. Put f(v_i) = i and
f(x) = j+1, where j is any P-neighbour index (or 0). This makes V(P) ∪ {x} bipartite with D + 2 vertices,
a contradiction.

*(b) Slots.* For x ∉ P let slot(x) be the least i with x ~ v_i and x ~ v_{i+1}. If slot(x) = k, the
P-neighbours of x lie in {v_k, v_{k+1}, v_{k+2}}. Indeed, v_{k−1} is excluded by the minimality of k,
and v_{k−2} is excluded because d(v_{k−2}, v_{k+1}) = 3.

*(c) Each slot is a clique.* Let x ≠ y be non-adjacent with slot(x) = slot(y) = k. Take
S = (V(P) ∖ {v_{k+1}}) ∪ {x, y}, with f(v_i) = i and f(x) = f(y) = k + 1. In S, the neighbours of x and y
are only v_k and v_{k+2}, both of parity different from k+1. So S is bipartite with D + 2 vertices, a
contradiction.

*(d) The path.* Let C_k be the set of vertices in slot k. Every vertex of C_k is adjacent to v_k and
v_{k+1}, and C_k is a clique. So

  v₀, C₀, v₁, C₁, v₂, …, v_{D−1}, C_{D−1}, v_D

(each C_k listed in any order) is a Hamiltonian path. ∎

## Lemma L2: G self-centred with D ≥ 3 ⇒ b(G) ≥ D + 3

*D ≥ 4.* Let m = ⌊D/2⌋, c = v_m, and let w be a vertex with d(c, w) = D. Take a shortest path
c = q₀, q₁, …, q_D = w, so d(c, q_j) = j. Put S = V(P) ∪ {q_j : ⌈D/2⌉ < j ≤ D} and f(x) = d(c, x).
Adjacent vertices have f-values differing by at most 1. Equal values on an edge are impossible:

* for v_i, v_{i±1} the values |i − m| and |i ± 1 − m| have different parities;
* every vertex of P has f ≤ ⌈D/2⌉ < f(q_j);
* the q_j have pairwise distinct f.

So S is bipartite, and |S| = D + 1 + ⌊D/2⌋ ≥ D + 3.

*D = 3.* Let d(v₁, w₁) = 3 and d(v₂, w₂) = 3. Then w₁ is not adjacent to v₀, v₁, v₂, and w₂ is not
adjacent to v₁, v₂, v₃.

* If w₁ ≠ w₂: G[V(P) ∪ {w₁, w₂}] is a subgraph of the 6-cycle v₀v₁v₂v₃w₁w₂. It is bipartite with 6 vertices.
* If w₁ = w₂ =: w: then w has no neighbour on P. Let β be the vertex before w on a shortest v₁–w path, so
  d(v₁, β) = 2. Then β ∉ P, β ≁ v₁, and β ≁ v₂ (since d(v₂, w) = 3). Also β cannot see both v₀ and v₃,
  because d(v₀, v₃) = 3. So G[V(P) ∪ {β, w}] is a tree with 6 vertices. ∎

## Lemma L3: D = 2, no dominating vertex, b(G) ≤ 4 ⇒ G has a Hamiltonian path

Let l = p₀p₁…p_{k−1} be a longest path, and suppose some h ∉ l. Let H be the set of vertices reachable from
h in G − V(l). Let S be the set of vertices of l with a neighbour in H. Maximality of l gives:

1. p₀, p_{k−1} ∉ S (otherwise prepend or append a vertex of H);
2. p_i ∈ S ⇒ p_{i+1} has no neighbour in H (otherwise insert an H-path between p_i and p_{i+1});
3. p_i ∈ S ⇒ p₀ ≁ p_{i+1} (otherwise use z p_i p_{i−1} … p₀ p_{i+1} … p_{k−1} with z ∈ H);
4. p_i, p_j ∈ S with i < j ⇒ p_{i+1} ≁ p_{j+1} (otherwise use p₀…p_i, an H-path,
   p_j p_{j−1} … p_{i+1}, then p_{j+1} … p_{k−1}).

*|S| ≥ 2.* Every z ∈ H has d(z, p₀) = 2 by (1). A common neighbour of z and p₀ cannot lie outside l, again
by (1), so it lies in S. Suppose S = {s}. Then every vertex of H is adjacent to s. A vertex w ∉ H ∪ {s} is
not adjacent to h, and every common neighbour of h and w must be s. So s is adjacent to all other
vertices, which contradicts the assumption that no vertex dominates.

Take p_i, p_j ∈ S with i < j. By (1), 1 ≤ i and j + 1 < k. By (1)–(4), {h, p₀, p_{i+1}, p_{j+1}} is
independent. Adding p_i gives a bipartite set of 5 vertices, which contradicts b(G) ≤ 4. Hence l is
Hamiltonian. ∎

## Proof of the theorem

By the two easy bounds, b(G) ∈ {D+1, D+2}.

* If b(G) = D + 1, apply L1.
* If b(G) = D + 2, then G is self-centred:
  * D = 1: G is complete, so it has a Hamiltonian path.
  * D = 2: no vertex is dominating (its eccentricity is 2) and b(G) = 4, so L3 applies.
  * D ≥ 3: L2 gives b(G) ≥ D + 3, a contradiction. ∎

**Remarks.**

1. The argument proves two stronger statements, which may be of independent interest:
   * *every connected graph with b(G) = diam(G) + 1 is traceable*;
   * *every self-centred graph of diameter D ≥ 3 has b(G) ≥ D + 3*.
2. The whole proof is formalized in Lean 4 / Mathlib against the exact statement of
   `WrittenOnTheWallII.GraphConjecture198a.conjecture198a` from google-deepmind/formal-conjectures.
   It uses the same definitions of `b` and `averageEccentricity` from `FormalConjecturesForMathlib`.
