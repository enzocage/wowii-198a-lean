import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Induced
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Eccentricity
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# Basic tools for the proof of WOWII Conjecture 198a

* bipartite certificates (a parity function on a vertex set),
* geodesic sequences,
* Hamiltonian walks from lists.
-/

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace WOW198a

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α}

/-! ### Bipartite certificates -/

/-- A finite set together with a function whose parity separates adjacent vertices of the set
gives a lower bound on the size of a largest induced bipartite subgraph. -/
theorem card_le_bip (s : Finset α) (f : α → ℕ)
    (hf : ∀ x ∈ s, ∀ y ∈ s, G.Adj x y → f x % 2 ≠ f y % 2) :
    s.card ≤ G.largestInducedBipartiteSubgraphSize := by
  unfold largestInducedBipartiteSubgraphSize
  apply le_csSup
  · exact ⟨Fintype.card α, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · refine ⟨s, (induce_isBipartite_iff_exists_coloring G s).mpr
      ⟨fun v => ⟨f v % 2, Nat.mod_lt _ (by norm_num)⟩, ?_⟩, rfl⟩
    intro u hu v hv huv h
    exact hf u hu v hv huv (by simpa using congrArg Fin.val h)

/-- The statement "every bipartite certificate has at most `k` vertices". -/
def BipBound (G : SimpleGraph α) (k : ℕ) : Prop :=
  ∀ (s : Finset α) (f : α → ℕ), (∀ x ∈ s, ∀ y ∈ s, G.Adj x y → f x % 2 ≠ f y % 2) → s.card ≤ k

theorem bipBound_of_le {k : ℕ} (h : G.largestInducedBipartiteSubgraphSize ≤ k) : BipBound G k :=
  fun s f hf => (card_le_bip s f hf).trans h

/-! ### Hamiltonian walks from lists -/

theorem ham_of_list (l : List α) (hne : l ≠ []) (hc : l.IsChain G.Adj) (hnd : l.Nodup)
    (hall : ∀ x, x ∈ l) : ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  refine ⟨_, _, Walk.ofSupport l hne hc, fun x => ?_⟩
  rw [Walk.support_ofSupport]
  exact List.count_eq_one_of_mem hnd (hall x)

/-- A list whose distinct entries are pairwise adjacent is a chain. -/
theorem isChain_of_pairwise_adj (l : List α) (hnd : l.Nodup)
    (h : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → G.Adj x y) : l.IsChain G.Adj := by
  apply List.Pairwise.isChain
  exact List.Pairwise.imp_of_mem (fun hx hy hxy => h _ hx _ hy hxy) hnd

/-! ### Distances -/

theorem dist_le_two_of_common (hconn : G.Connected) {u v x : α} (hu : G.Adj x u)
    (hv : G.Adj x v) : G.dist u v ≤ 2 := by
  have h1 : G.dist u x = 1 := dist_eq_one_iff_adj.mpr hu.symm
  have h2 : G.dist x v = 1 := dist_eq_one_iff_adj.mpr hv
  have := hconn.dist_triangle (u := u) (v := x) (w := v)
  omega

theorem dist_le_one_of_adj {u v : α} (h : G.Adj u v) : G.dist u v ≤ 1 :=
  (dist_eq_one_iff_adj.mpr h).le

/-- Adjacent vertices have distances to a fixed vertex that differ by at most one. -/
theorem dist_adj_le (hconn : G.Connected) (c : α) {x y : α} (h : G.Adj x y) :
    G.dist c x ≤ G.dist c y + 1 := by
  have := hconn.dist_triangle (u := c) (v := y) (w := x)
  have h1 : G.dist y x = 1 := dist_eq_one_iff_adj.mpr h.symm
  omega

theorem exists_common_of_dist_two (hconn : G.Connected) {u v : α} (h : G.dist u v = 2) :
    ∃ y, G.Adj u y ∧ G.Adj y v := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
  refine ⟨p.getVert 1, ?_, ?_⟩
  · have := p.adj_getVert_succ (i := 0) (by omega)
    simpa [Walk.getVert_zero] using this
  · have := p.adj_getVert_succ (i := 1) (by omega)
    have e : p.getVert 2 = v := by rw [show 2 = p.length by omega]; exact p.getVert_length
    simpa [e] using this

/-! ### Geodesics -/

/-- `P 0, P 1, …, P D` is a shortest path. -/
structure Geod (G : SimpleGraph α) (D : ℕ) (P : ℕ → α) : Prop where
  adj : ∀ i < D, G.Adj (P i) (P (i + 1))
  dist : ∀ i j, i ≤ j → j ≤ D → G.dist (P i) (P j) = j - i

theorem Geod.of_walk (hconn : G.Connected) {u v : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v) : Geod G p.length p.getVert := by
  have hadj : ∀ i < p.length, G.Adj (p.getVert i) (p.getVert (i + 1)) :=
    fun i hi => p.adj_getVert_succ hi
  -- upper bound
  have hup : ∀ i j, i ≤ j → j ≤ p.length → G.dist (p.getVert i) (p.getVert j) ≤ j - i := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; simp
    | succ j hij ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := dist_le_one_of_adj (hadj j (by omega))
      have := hconn.dist_triangle (u := p.getVert i) (v := p.getVert j) (w := p.getVert (j + 1))
      omega
  refine ⟨hadj, fun i j hij hj => le_antisymm (hup i j hij hj) ?_⟩
  have h0 := hup 0 i (by omega) (by omega)
  have h1 := hup j p.length hj le_rfl
  rw [Walk.getVert_zero] at h0
  rw [Walk.getVert_length] at h1
  have t1 := hconn.dist_triangle (u := u) (v := p.getVert i) (w := v)
  have t2 := hconn.dist_triangle (u := p.getVert i) (v := p.getVert j) (w := v)
  omega

namespace Geod

variable {D : ℕ} {P : ℕ → α}

theorem dist' (hP : Geod G D P) {i j : ℕ} (hi : i ≤ D) (hj : j ≤ D) :
    G.dist (P i) (P j) = max i j - min i j := by
  rcases le_total i j with h | h
  · rw [hP.dist i j h hj]; omega
  · rw [dist_comm, hP.dist j i h hi]; omega

theorem inj (hP : Geod G D P) {i j : ℕ} (hi : i ≤ D) (hj : j ≤ D) (h : P i = P j) : i = j := by
  have := hP.dist' hi hj
  rw [h, dist_self] at this
  omega

theorem adj_iff (hP : Geod G D P) {i j : ℕ} (hi : i ≤ D) (hj : j ≤ D) :
    G.Adj (P i) (P j) ↔ i + 1 = j ∨ j + 1 = i := by
  constructor
  · intro h
    have := hP.dist' hi hj
    rw [dist_eq_one_iff_adj.mpr h] at this
    omega
  · rintro (h | h)
    · subst h; exact hP.adj i (by omega)
    · subst h; exact (hP.adj j (by omega)).symm

theorem common (hP : Geod G D P) (hconn : G.Connected) {i j : ℕ} (hi : i ≤ D) (hj : j ≤ D)
    {x : α} (h1 : G.Adj x (P i)) (h2 : G.Adj x (P j)) : i ≤ j + 2 ∧ j ≤ i + 2 := by
  have := dist_le_two_of_common hconn h1 h2
  rw [hP.dist' hi hj] at this
  omega

end Geod

/-! ### Index function along a geodesic -/

open Classical in
/-- The position of a vertex on the geodesic `P` (or `0` if it is not on it). -/
noncomputable def idx (D : ℕ) (P : ℕ → α) (x : α) : ℕ :=
  if h : ∃ i, i ≤ D ∧ P i = x then Nat.find h else 0

theorem idx_P {D : ℕ} {P : ℕ → α} (hP : Geod G D P) {i : ℕ} (hi : i ≤ D) :
    idx D P (P i) = i := by
  classical
  have h : ∃ k, k ≤ D ∧ P k = P i := ⟨i, hi, rfl⟩
  simp only [idx, dif_pos h]
  have hs := Nat.find_spec h
  exact hP.inj hs.1 hi hs.2

/-- The vertex set of the geodesic. -/
def pset (D : ℕ) (P : ℕ → α) : Finset α := (Finset.range (D + 1)).image P

theorem mem_pset {D : ℕ} {P : ℕ → α} {x : α} : x ∈ pset D P ↔ ∃ i, i ≤ D ∧ P i = x := by
  simp [pset]

theorem card_pset {D : ℕ} {P : ℕ → α} (hP : Geod G D P) : (pset D P).card = D + 1 := by
  rw [pset, Finset.card_image_of_injOn]
  · simp
  · intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    exact hP.inj (by omega) (by omega) h

end WOW198a
