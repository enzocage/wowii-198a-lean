import WOW198a.L1
import WOW198a.L2
import WOW198a.L3

/-!
# WOWII Conjecture 198a

**Theorem.** Let `G` be a connected graph on at least two vertices.  If
`b(G) ≤ 2 + ecc_avg(G)`, where `b(G)` is the order of a largest induced bipartite subgraph and
`ecc_avg(G)` the average eccentricity, then `G` has a Hamiltonian path.

**Proof.** Let `D = diam G` and let `P` be a diametral shortest path.  `P` is an induced bipartite
subgraph, so `b(G) ≥ D + 1`; every eccentricity is at most `D`, so `b(G) ≤ D + 2`.

* If `b(G) = D + 1`, Lemma L1 (`ham_of_bipBound`) gives a Hamiltonian path.
* If `b(G) = D + 2`, the hypothesis forces every vertex to have eccentricity `D`.
  - `D = 1`: `G` is complete.
  - `D = 2`: Lemma L3 (`ham_of_diam_two`).
  - `D ≥ 3`: Lemma L2 (`big_bip_3`, `big_bip_ge4`) gives an induced bipartite subgraph on
    `D + 3` vertices, a contradiction.
-/

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace WOW198a

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

theorem conjecture198a (G : SimpleGraph α) (h : G.Connected)
    (hb : b G ≤ 2 + averageEccentricity G) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  set D := G.diam with hD
  set B := G.largestInducedBipartiteSubgraphSize with hBdef
  have hne : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp h
  have hecc_le : ∀ v, (G.eccent v).toNat ≤ D := by
    intro v
    exact ENat.toNat_le_toNat eccent_le_ediam hne
  -- a diametral path
  obtain ⟨u, w, huw⟩ := G.exists_dist_eq_diam
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist u w
  have hP' := Geod.of_walk h q hq
  have hlen : q.length = D := hq.trans huw
  rw [hlen] at hP'
  set P := q.getVert with hPdef
  have hP : Geod G D P := hP'
  -- `B ≥ D + 1`
  have hB1 : D + 1 ≤ B := by
    have := card_le_bip (G := G) (pset D P) (idx D P) ?_
    · rwa [card_pset hP] at this
    · intro x hx y hy hxy
      obtain ⟨i, hi, rfl⟩ := mem_pset.mp hx
      obtain ⟨j, hj, rfl⟩ := mem_pset.mp hy
      rw [idx_P hP hi, idx_P hP hj]
      have := (hP.adj_iff hi hj).mp hxy
      omega
  -- the numerical hypothesis
  set N := Fintype.card α with hNdef
  have hN : 0 < N := Fintype.card_pos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : N * B ≤ 2 * N + ∑ v, (G.eccent v).toNat := by
    have h1 : (B : ℝ) ≤ 2 + (∑ v, ((G.eccent v).toNat : ℝ)) / N := by
      have := hb
      simp only [SimpleGraph.b, averageEccentricity] at this
      push_cast at this
      exact this
    have h2 := mul_le_mul_of_nonneg_left h1 hNr.le
    rw [mul_add, mul_div_cancel₀ _ hNr.ne'] at h2
    have : ((N * B : ℕ) : ℝ) ≤ ((2 * N + ∑ v, (G.eccent v).toNat : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  have hsum_le : ∑ v, (G.eccent v).toNat ≤ N * D := by
    calc ∑ v, (G.eccent v).toNat ≤ ∑ _v : α, D := Finset.sum_le_sum (fun v _ => hecc_le v)
      _ = N * D := by simp [N]
  have hB2 : B ≤ D + 2 := by
    have : N * B ≤ N * (D + 2) := by nlinarith
    exact Nat.le_of_mul_le_mul_left this hN
  by_cases hBD : B ≤ D + 1
  · exact ham_of_bipBound h hP (bipBound_of_le hBD)
  have hBeq : B = D + 2 := by omega
  -- every eccentricity equals `D`
  have hall : ∀ v, (G.eccent v).toNat = D := by
    by_contra hc
    push Not at hc
    obtain ⟨v0, hv0⟩ := hc
    have hlt : (G.eccent v0).toNat < D := lt_of_le_of_ne (hecc_le v0) hv0
    have : ∑ v, (G.eccent v).toNat < N * D := by
      calc ∑ v, (G.eccent v).toNat < ∑ _v : α, D :=
            Finset.sum_lt_sum (fun v _ => hecc_le v) ⟨v0, Finset.mem_univ _, hlt⟩
        _ = N * D := by simp [N]
    rw [hBeq] at hsum
    nlinarith
  have hpart : ∀ v, ∃ w, G.dist v w = D := by
    intro v
    obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite v
    exact ⟨w, by rw [← hall v, ← hw]; rfl⟩
  have hD1 : 1 ≤ D := Nat.pos_of_ne_zero (G.diam_ne_zero_of_ediam_ne_top hne)
  have hdist : ∀ x y, G.dist x y ≤ D := fun x y => dist_le_diam hne
  rcases (by omega : D = 1 ∨ D = 2 ∨ D = 3 ∨ 4 ≤ D) with h1 | h2 | h3 | h4
  · -- `G` is complete
    have hadj : ∀ x y, x ≠ y → G.Adj x y := by
      intro x y hxy
      have h0 : G.dist x y ≠ 0 := by rw [Ne, h.dist_eq_zero_iff]; exact hxy
      have := hdist x y
      exact dist_eq_one_iff_adj.mp (by omega)
    refine ham_of_list (Finset.univ.toList) ?_
      (isChain_of_pairwise_adj _ (Finset.nodup_toList _) (fun x _ y _ hxy => hadj x y hxy))
      (Finset.nodup_toList _) (by simp)
    intro he
    have := congrArg List.length he
    simp [Finset.length_toList] at this
  · -- diameter two
    refine ham_of_diam_two h (fun x y => h2 ▸ hdist x y) (fun v => ?_)
      (bipBound_of_le (by omega))
    obtain ⟨w, hw⟩ := hpart v
    refine ⟨w, fun he => ?_, fun hadj => ?_⟩
    · subst he; simp at hw; omega
    · rw [dist_eq_one_iff_adj.mpr hadj] at hw; omega
  · -- `D = 3`: impossible
    obtain ⟨w₁, hw₁⟩ := hpart (P 1)
    obtain ⟨w₂, hw₂⟩ := hpart (P 2)
    rw [h3] at hP hw₁ hw₂
    obtain ⟨s, f, hf, hs⟩ := big_bip_3 h hP hw₁ hw₂
    have := card_le_bip s f hf
    omega
  · -- `D ≥ 4`: impossible
    obtain ⟨w, hw⟩ := hpart (P (D / 2))
    obtain ⟨s, f, hf, hs⟩ := big_bip_ge4 h hP h4 hw
    have := card_le_bip s f hf
    omega

end WOW198a
