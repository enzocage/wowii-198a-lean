import WOW198a.Basic

/-!
# Lemma L2: self-centered graphs of diameter `D ≥ 3` have `b(G) ≥ D + 3`

Let `P 0, …, P D` be a diametral shortest path.

* `D ≥ 4`: let `c = P (D/2)` and let `w` be at distance `D` from `c`.  The geodesic from `c` to `w`
  leaves the ball of radius `⌈D/2⌉` around `c` (which contains the whole of `P`) after
  `⌈D/2⌉` steps.  `P` together with the last `⌊D/2⌋ ≥ 2` vertices of this geodesic has no edge
  inside a BFS layer around `c`, hence is bipartite.
* `D = 3`: a short case analysis with the eccentric vertices of `P 1` and `P 2`.
-/

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace WOW198a

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α}
variable {D : ℕ} {P : ℕ → α}

/-- A geodesic starting at `c` and ending at a vertex at distance `D` from `c`. -/
theorem exists_geod_from (hconn : G.Connected) {c w : α} (hw : G.dist c w = D) :
    ∃ Q : ℕ → α, Geod G D Q ∧ Q 0 = c ∧ Q D = w := by
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist c w
  have hQ := Geod.of_walk hconn q hq
  have hl : q.length = D := hq.trans hw
  rw [hl] at hQ
  refine ⟨q.getVert, hQ, Walk.getVert_zero q, ?_⟩
  rw [← hl]; exact Walk.getVert_length q

theorem dist_mid (hP : Geod G D P) {m i : ℕ} (hm : m ≤ D) (hi : i ≤ D) :
    (i ≤ m ∧ G.dist (P m) (P i) = m - i) ∨ (m ≤ i ∧ G.dist (P m) (P i) = i - m) := by
  rcases le_total i m with h | h
  · left; refine ⟨h, ?_⟩; rw [dist_comm, hP.dist i m h hm]
  · right; exact ⟨h, hP.dist m i h hi⟩

theorem big_bip_ge4 (hconn : G.Connected) (hP : Geod G D P) (hD : 4 ≤ D) {w : α}
    (hw : G.dist (P (D / 2)) w = D) :
    ∃ s : Finset α, ∃ f : α → ℕ,
      (∀ x ∈ s, ∀ y ∈ s, G.Adj x y → f x % 2 ≠ f y % 2) ∧ D + 3 ≤ s.card := by
  have hm2 : 2 * (D / 2) ≤ D ∧ D ≤ 2 * (D / 2) + 1 := by omega
  generalize hm : D / 2 = m at hw hm2
  generalize hc : P m = c at hw
  obtain ⟨Q, hQ, hQ0, -⟩ := exists_geod_from hconn hw
  have hdQ : ∀ j, j ≤ D → G.dist c (Q j) = j := by
    intro j hj; rw [← hQ0, hQ.dist 0 j (Nat.zero_le _) hj]; omega
  have hmD : m ≤ D := by omega
  have hdP : ∀ i, i ≤ D → G.dist c (P i) ≤ D - m := by
    intro i hi
    rcases dist_mid hP hmD hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hc] at h2 <;> omega
  let A := pset D P
  let B := (Finset.Icc (D - m + 1) D).image Q
  have hmemB : ∀ y ∈ B, ∃ j, D - m + 1 ≤ j ∧ j ≤ D ∧ Q j = y := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_Icc] at hj
    exact ⟨j, hj.1, hj.2, rfl⟩
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro y hyA hyB
    obtain ⟨i, hi, rfl⟩ := mem_pset.mp hyA
    obtain ⟨j, hj1, hj2, hj⟩ := hmemB _ hyB
    have := hdP i hi
    rw [← hj, hdQ j hj2] at this
    omega
  have hcardB : B.card = m := by
    rw [Finset.card_image_of_injOn]
    · simp; omega
    · intro j hj j' hj' h
      simp only [coe_Icc, Set.mem_Icc] at hj hj'
      have := congrArg (G.dist c) h
      rwa [hdQ j hj.2, hdQ j' hj'.2] at this
  refine ⟨A ∪ B, fun y => G.dist c y, ?_, ?_⟩
  · intro x hx y hy hxy
    show G.dist c x % 2 ≠ G.dist c y % 2
    have h1 := dist_adj_le hconn c hxy
    have h2 := dist_adj_le hconn c hxy.symm
    suffices hne : G.dist c x ≠ G.dist c y by omega
    rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨i, hi, rfl⟩ := mem_pset.mp hx
      obtain ⟨j, hj, rfl⟩ := mem_pset.mp hy
      have hij := (hP.adj_iff hi hj).mp hxy
      rcases dist_mid hP hmD hi with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
        rcases dist_mid hP hmD hj with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> rw [hc] at a2 b2 <;> omega
    · obtain ⟨i, hi, rfl⟩ := mem_pset.mp hx
      obtain ⟨j, hj1, hj2, rfl⟩ := hmemB _ hy
      have := hdP i hi; rw [hdQ j hj2]; omega
    · obtain ⟨i, hi1, hi2, rfl⟩ := hmemB _ hx
      obtain ⟨j, hj, rfl⟩ := mem_pset.mp hy
      have := hdP j hj; rw [hdQ i hi2]; omega
    · obtain ⟨i, hi1, hi2, rfl⟩ := hmemB _ hx
      obtain ⟨j, hj1, hj2, rfl⟩ := hmemB _ hy
      rw [hdQ i hi2, hdQ j hj2]
      intro hij; subst hij
      exact G.irrefl hxy
  · rw [Finset.card_union_of_disjoint hdisj, card_pset hP, hcardB]
    omega

theorem not_adj_of_dist_three (hconn : G.Connected) {u v x : α} (h : G.dist u x = 3)
    (hv : G.dist u v ≤ 1) : ¬ G.Adj v x := by
  intro hvx
  have := hconn.dist_triangle (u := u) (v := v) (w := x)
  have := dist_le_one_of_adj hvx
  omega

theorem big_bip_3 (hconn : G.Connected) (hP : Geod G 3 P) {w₁ w₂ : α}
    (h1 : G.dist (P 1) w₁ = 3) (h2 : G.dist (P 2) w₂ = 3) :
    ∃ s : Finset α, ∃ f : α → ℕ,
      (∀ x ∈ s, ∀ y ∈ s, G.Adj x y → f x % 2 ≠ f y % 2) ∧ 6 ≤ s.card := by
  classical
  have d1 : ∀ i, i ≤ 3 → G.dist (P 1) (P i) ≤ 2 := by
    intro i hi; rw [hP.dist' (by omega) hi]; omega
  have d2 : ∀ i, i ≤ 3 → G.dist (P 2) (P i) ≤ 2 := by
    intro i hi; rw [hP.dist' (by omega) hi]; omega
  have w1P : w₁ ∉ pset 3 P := by
    intro h; obtain ⟨i, hi, rfl⟩ := mem_pset.mp h; have := d1 i hi; omega
  have w2P : w₂ ∉ pset 3 P := by
    intro h; obtain ⟨i, hi, rfl⟩ := mem_pset.mp h; have := d2 i hi; omega
  have nw1 : ∀ i, i ≤ 2 → ¬ G.Adj (P i) w₁ := by
    intro i hi
    apply not_adj_of_dist_three hconn h1
    rw [hP.dist' (by omega) (by omega)]; omega
  have nw2 : ∀ i, 1 ≤ i → i ≤ 3 → ¬ G.Adj (P i) w₂ := by
    intro i hi hi'
    apply not_adj_of_dist_three hconn h2
    rw [hP.dist' (by omega) (by omega)]; omega
  have hmem : ∀ a b z, z ∈ insert a (insert b (pset 3 P)) → z = a ∨ z = b ∨ ∃ i, i ≤ 3 ∧ P i = z := by
    intro a b z hz
    simp only [Finset.mem_insert] at hz
    rcases hz with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (mem_pset.mp h))
  have hcard : ∀ a b, a ∉ pset 3 P → b ∉ pset 3 P → a ≠ b →
      (insert a (insert b (pset 3 P))).card = 6 := by
    intro a b ha hb hab
    have h' : a ∉ insert b (pset 3 P) := by
      rw [Finset.mem_insert]; rintro (h | h)
      · exact hab h
      · exact ha h
    rw [Finset.card_insert_of_notMem h', Finset.card_insert_of_notMem hb, card_pset hP]
  by_cases hw : w₁ = w₂
  · -- `w := w₁ = w₂` is adjacent to no vertex of `P`
    subst hw
    have nw : ∀ i, i ≤ 3 → ¬ G.Adj (P i) w₁ := by
      intro i hi
      rcases Nat.lt_or_ge i 3 with h | h
      · exact nw1 i (by omega)
      · exact nw2 i (by omega) hi
    obtain ⟨R, hR, hR0, hR3⟩ := exists_geod_from hconn h1
    have hβd : G.dist (P 1) (R 2) = 2 := by rw [← hR0, hR.dist 0 2 (by omega) (by omega)]
    have hβw : G.Adj (R 2) w₁ := by
      have := hR.adj 2 (by omega); rwa [hR3] at this
    have hβne : R 2 ≠ w₁ := G.ne_of_adj hβw
    have hβP : R 2 ∉ pset 3 P := by
      intro h
      obtain ⟨i, hi, hPi⟩ := mem_pset.mp h
      have := hP.dist' (i := 1) (j := i) (by omega) hi
      rw [hPi, hβd] at this
      have hi3 : i = 3 := by omega
      subst hi3
      exact nw 3 le_rfl (hPi ▸ hβw)
    have nβ1 : ¬ G.Adj (R 2) (P 1) := by
      intro h
      have := dist_eq_one_iff_adj.mpr h.symm
      omega
    have nβ2 : ¬ G.Adj (R 2) (P 2) := by
      intro h
      exact not_adj_of_dist_three hconn h2 (dist_le_one_of_adj h.symm) hβw
    have nβ03 : ¬ (G.Adj (R 2) (P 0) ∧ G.Adj (R 2) (P 3)) := by
      rintro ⟨h0, h3⟩
      have := hP.common hconn (i := 0) (j := 3) (by omega) le_rfl h0 h3
      omega
    let fβ : ℕ := if G.Adj (R 2) (P 0) then 1 else 0
    let f : α → ℕ := fun y => if y = w₁ then fβ + 1 else if y = R 2 then fβ else idx 3 P y
    have hfP : ∀ i, i ≤ 3 → f (P i) = i := by
      intro i hi
      have e1 : P i ≠ w₁ := fun h => w1P (mem_pset.mpr ⟨i, hi, h⟩)
      have e2 : P i ≠ R 2 := fun h => hβP (mem_pset.mpr ⟨i, hi, h⟩)
      simp [f, e1, e2, idx_P hP hi]
    have hfw : f w₁ = fβ + 1 := by simp [f]
    have hfβ : f (R 2) = fβ := by simp [f, hβne]
    have hβnb : ∀ i, i ≤ 3 → G.Adj (R 2) (P i) → fβ % 2 ≠ i % 2 := by
      intro i hi h
      have : i = 0 ∨ i = 3 := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h' | h' | h' | h'
        · exact Or.inl h'
        · subst h'; exact absurd h nβ1
        · subst h'; exact absurd h nβ2
        · exact Or.inr h'
      rcases this with rfl | rfl
      · simp [fβ, h]
      · have : ¬ G.Adj (R 2) (P 0) := fun h0 => nβ03 ⟨h0, h⟩
        simp [fβ, this]
    refine ⟨insert w₁ (insert (R 2) (pset 3 P)), f, ?_, (hcard _ _ w1P hβP hβne.symm).ge⟩
    intro x hx y hy hxy
    rcases hmem _ _ _ hx with hx' | hx' | ⟨i, hi, rfl⟩ <;>
      rcases hmem _ _ _ hy with hy' | hy' | ⟨j, hj, rfl⟩
    · rw [hx', hy'] at hxy; exact absurd hxy G.irrefl
    · rw [hx', hy']; rw [hfw, hfβ]; omega
    · rw [hx'] at hxy; exact absurd hxy.symm (nw j hj)
    · rw [hx', hy']; rw [hfw, hfβ]; omega
    · rw [hx', hy'] at hxy; exact absurd hxy G.irrefl
    · rw [hx'] at hxy ⊢; rw [hfβ, hfP j hj]; exact hβnb j hj hxy
    · rw [hy'] at hxy; exact absurd hxy (nw i hi)
    · rw [hy'] at hxy ⊢; rw [hfβ, hfP i hi]; exact (hβnb i hi hxy.symm).symm
    · rw [hfP i hi, hfP j hj]; have := (hP.adj_iff hi hj).mp hxy; omega
  · let f : α → ℕ := fun y => if y = w₁ then 0 else if y = w₂ then 1 else idx 3 P y
    have hfP : ∀ i, i ≤ 3 → f (P i) = i := by
      intro i hi
      have e1 : P i ≠ w₁ := fun h => w1P (mem_pset.mpr ⟨i, hi, h⟩)
      have e2 : P i ≠ w₂ := fun h => w2P (mem_pset.mpr ⟨i, hi, h⟩)
      simp [f, e1, e2, idx_P hP hi]
    have hf1 : f w₁ = 0 := by simp [f]
    have hf2 : f w₂ = 1 := by simp [f, Ne.symm hw]
    have a1 : ∀ i, i ≤ 3 → G.Adj (P i) w₁ → i = 3 := by
      intro i hi h
      by_contra hne; exact nw1 i (by omega) h
    have a2 : ∀ i, i ≤ 3 → G.Adj (P i) w₂ → i = 0 := by
      intro i hi h
      by_contra hne; exact nw2 i (by omega) hi h
    refine ⟨insert w₁ (insert w₂ (pset 3 P)), f, ?_, (hcard _ _ w1P w2P hw).ge⟩
    intro x hx y hy hxy
    rcases hmem _ _ _ hx with hx' | hx' | ⟨i, hi, rfl⟩ <;>
      rcases hmem _ _ _ hy with hy' | hy' | ⟨j, hj, rfl⟩
    · rw [hx', hy'] at hxy; exact absurd hxy G.irrefl
    · rw [hx', hy']; rw [hf1, hf2]; omega
    · rw [hx'] at hxy ⊢; rw [hf1, hfP j hj, a1 j hj hxy.symm]; omega
    · rw [hx', hy']; rw [hf1, hf2]; omega
    · rw [hx', hy'] at hxy; exact absurd hxy G.irrefl
    · rw [hx'] at hxy ⊢; rw [hf2, hfP j hj, a2 j hj hxy.symm]; omega
    · rw [hy'] at hxy ⊢; rw [hf1, hfP i hi, a1 i hi hxy]; omega
    · rw [hy'] at hxy ⊢; rw [hf2, hfP i hi, a2 i hi hxy]; omega
    · rw [hfP i hi, hfP j hj]; have := (hP.adj_iff hi hj).mp hxy; omega

end WOW198a
