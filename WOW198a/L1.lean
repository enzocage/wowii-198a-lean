import WOW198a.Basic

/-!
# Lemma L1: if `b(G) = diam(G) + 1` then `G` has a Hamiltonian path

Let `P 0, …, P D` be a diametral shortest path.  If no induced bipartite subgraph has more than
`D + 1` vertices, then every vertex off the path is adjacent to two consecutive path vertices.
Assigning each such vertex to the least such pair ("slot"), the vertices of a slot form a clique,
so they can be threaded into the path between the two path vertices of their slot.
-/

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace WOW198a

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α}
variable {D : ℕ} {P : ℕ → α}

theorem mem_insert_pset {x y : α} (hy : y ∈ insert x (pset D P)) :
    y = x ∨ ∃ i, i ≤ D ∧ P i = y := by
  rcases Finset.mem_insert.mp hy with h | h
  · exact Or.inl h
  · exact Or.inr (mem_pset.mp h)

/-- Every vertex off the geodesic is adjacent to two consecutive geodesic vertices. -/
theorem exists_slot (hconn : G.Connected) (hP : Geod G D P) (hB : BipBound G (D + 1))
    {x : α} (hx : x ∉ pset D P) : ∃ i, i < D ∧ G.Adj x (P i) ∧ G.Adj x (P (i + 1)) := by
  classical
  by_contra hno
  push Not at hno
  let f : α → ℕ := fun y => if y = x then
      (if h : ∃ i, i ≤ D ∧ G.Adj x (P i) then Nat.find h + 1 else 0) else idx D P y
  have hcard : (insert x (pset D P)).card = D + 2 := by
    rw [Finset.card_insert_of_notMem hx, card_pset hP]
  have key : ∀ j, j ≤ D → G.Adj x (P j) → f x % 2 ≠ j % 2 := by
    intro j hj hxj
    have h : ∃ i, i ≤ D ∧ G.Adj x (P i) := ⟨j, hj, hxj⟩
    have hfx : f x = Nat.find h + 1 := by simp [f, dif_pos h]
    obtain ⟨hj0, hxj0⟩ := Nat.find_spec h
    have hmin : Nat.find h ≤ j := Nat.find_min' h ⟨hj, hxj⟩
    have hc := hP.common hconn hj0 hj hxj0 hxj
    have hne : j ≠ Nat.find h + 1 := by
      intro hj1
      exact hno (Nat.find h) (by omega) hxj0 (hj1 ▸ hxj)
    rw [hfx]; omega
  have hfP : ∀ i, i ≤ D → f (P i) = i := by
    intro i hi
    have : P i ≠ x := fun h => hx (mem_pset.mpr ⟨i, hi, h⟩)
    simp [f, this, idx_P hP hi]
  have := hB (insert x (pset D P)) f ?_
  · omega
  intro y hy z hz hyz
  rcases mem_insert_pset hy with hyx | ⟨i, hi, rfl⟩ <;>
    rcases mem_insert_pset hz with hzx | ⟨j, hj, rfl⟩
  · rw [hyx, hzx] at hyz; exact absurd hyz G.irrefl
  · rw [hyx] at hyz ⊢; rw [hfP j hj]; exact key j hj hyz
  · rw [hzx] at hyz ⊢; rw [hfP i hi]; exact (key i hi hyz.symm).symm
  · rw [hfP i hi, hfP j hj]
    have := (hP.adj_iff hi hj).mp hyz
    omega

open Classical in
/-- The least index `i` such that `x` is adjacent to `P i` and `P (i+1)`. -/
noncomputable def slot (G : SimpleGraph α) (D : ℕ) (P : ℕ → α) (x : α) : ℕ :=
  if h : ∃ i, i < D ∧ G.Adj x (P i) ∧ G.Adj x (P (i + 1)) then Nat.find h else D

theorem slot_spec {x : α} (h : ∃ i, i < D ∧ G.Adj x (P i) ∧ G.Adj x (P (i + 1))) :
    slot G D P x < D ∧ G.Adj x (P (slot G D P x)) ∧ G.Adj x (P (slot G D P x + 1)) := by
  classical
  simp only [slot, dif_pos h]
  exact Nat.find_spec h

theorem slot_min {x : α} {i : ℕ} (hi : i < D) (h1 : G.Adj x (P i)) (h2 : G.Adj x (P (i + 1))) :
    slot G D P x ≤ i := by
  classical
  have h : ∃ i, i < D ∧ G.Adj x (P i) ∧ G.Adj x (P (i + 1)) := ⟨i, hi, h1, h2⟩
  simp only [slot, dif_pos h]
  exact Nat.find_min' h ⟨hi, h1, h2⟩

/-- The path neighbours of a vertex in slot `k` are among `P k`, `P (k+1)`, `P (k+2)`. -/
theorem slot_nbrs (hconn : G.Connected) (hP : Geod G D P) {x : α}
    (h : ∃ i, i < D ∧ G.Adj x (P i) ∧ G.Adj x (P (i + 1))) {j : ℕ} (hj : j ≤ D)
    (hxj : G.Adj x (P j)) : j = slot G D P x ∨ j = slot G D P x + 1 ∨ j = slot G D P x + 2 := by
  obtain ⟨hk, h1, h2⟩ := slot_spec h
  have c1 := hP.common hconn hj (by omega) hxj h1
  have c2 := hP.common hconn hj (by omega) hxj h2
  have hne : j + 1 ≠ slot G D P x := by
    intro he
    have := slot_min (G := G) (D := D) (P := P) (x := x) (i := j) (by omega) hxj (he ▸ h1)
    omega
  omega

/-- Vertices in the same slot are adjacent. -/
theorem slot_clique (hconn : G.Connected) (hP : Geod G D P) (hB : BipBound G (D + 1))
    {x y : α} (hx : x ∉ pset D P) (hy : y ∉ pset D P) (hxy : x ≠ y)
    (hs : slot G D P x = slot G D P y) : G.Adj x y := by
  classical
  by_contra hn
  have ex := exists_slot hconn hP hB hx
  have ey := exists_slot hconn hP hB hy
  set k := slot G D P x with hk
  obtain ⟨hkD, hx1, hx2⟩ := slot_spec ex
  let f : α → ℕ := fun z => if z = x ∨ z = y then k + 1 else idx D P z
  let s : Finset α := insert x (insert y ((pset D P).erase (P (k + 1))))
  have hPk1 : P (k + 1) ∈ pset D P := mem_pset.mpr ⟨k + 1, by omega, rfl⟩
  have hcard : s.card = D + 2 := by
    have h1 : y ∉ (pset D P).erase (P (k + 1)) := fun h => hy (Finset.mem_of_mem_erase h)
    have h2 : x ∉ insert y ((pset D P).erase (P (k + 1))) := by
      rw [Finset.mem_insert]; rintro (h | h)
      · exact hxy h
      · exact hx (Finset.mem_of_mem_erase h)
    rw [Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1,
      Finset.card_erase_of_mem hPk1, card_pset hP]
    omega
  have hfP : ∀ i, i ≤ D → f (P i) = i := by
    intro i hi
    have h1 : P i ≠ x := fun h => hx (mem_pset.mpr ⟨i, hi, h⟩)
    have h2 : P i ≠ y := fun h => hy (mem_pset.mpr ⟨i, hi, h⟩)
    simp [f, h1, h2, idx_P hP hi]
  have hfx : f x = k + 1 := by simp [f]
  have hfy : f y = k + 1 := by simp [f]
  -- membership in `s`
  have hmem : ∀ z ∈ s, z = x ∨ z = y ∨ ∃ i, i ≤ D ∧ i ≠ k + 1 ∧ P i = z := by
    intro z hz
    simp only [s, Finset.mem_insert, Finset.mem_erase] at hz
    rcases hz with h | h | ⟨hne, hz⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨i, hi, rfl⟩ := mem_pset.mp hz
      refine Or.inr (Or.inr ⟨i, hi, fun h => hne (h ▸ rfl), rfl⟩)
  -- neighbours of `x` and `y` in `s`
  have nbx : ∀ j, j ≤ D → j ≠ k + 1 → G.Adj x (P j) → j = k ∨ j = k + 2 := by
    intro j hj hj1 hxj
    have := slot_nbrs hconn hP ex hj hxj
    omega
  have nby : ∀ j, j ≤ D → j ≠ k + 1 → G.Adj y (P j) → j = k ∨ j = k + 2 := by
    intro j hj hj1 hyj
    have := slot_nbrs hconn hP ey hj hyj
    rw [← hs] at this
    omega
  have := hB s f ?_
  · omega
  intro z hz w hw hzw
  rcases hmem z hz with hz' | hz' | ⟨i, hi, hi1, rfl⟩ <;>
    rcases hmem w hw with hw' | hw' | ⟨j, hj, hj1, rfl⟩
  · rw [hz', hw'] at hzw; exact absurd hzw G.irrefl
  · rw [hz', hw'] at hzw; exact absurd hzw hn
  · rw [hz'] at hzw ⊢; rw [hfx, hfP j hj]; have := nbx j hj hj1 hzw; omega
  · rw [hz', hw'] at hzw; exact absurd hzw.symm hn
  · rw [hz', hw'] at hzw; exact absurd hzw G.irrefl
  · rw [hz'] at hzw ⊢; rw [hfy, hfP j hj]; have := nby j hj hj1 hzw; omega
  · rw [hw'] at hzw ⊢; rw [hfx, hfP i hi]; have := nbx i hi hi1 hzw.symm; omega
  · rw [hw'] at hzw ⊢; rw [hfy, hfP i hi]; have := nby i hi hi1 hzw.symm; omega
  · rw [hfP i hi, hfP j hj]
    have := (hP.adj_iff hi hj).mp hzw
    omega

/-- The vertices of slot `k`, as a list. -/
noncomputable def blk (G : SimpleGraph α) (D : ℕ) (P : ℕ → α) (k : ℕ) : List α :=
  (Finset.univ.filter (fun x => x ∉ pset D P ∧ slot G D P x = k)).toList

theorem mem_blk {k : ℕ} {x : α} : x ∈ blk G D P k ↔ x ∉ pset D P ∧ slot G D P x = k := by
  simp [blk]

/-- The Hamiltonian path, built up to position `k`. -/
noncomputable def hamList (G : SimpleGraph α) (D : ℕ) (P : ℕ → α) : ℕ → List α
  | 0 => [P 0]
  | k + 1 => hamList G D P k ++ blk G D P k ++ [P (k + 1)]

theorem hamList_props (hconn : G.Connected) (hP : Geod G D P) (hB : BipBound G (D + 1)) :
    ∀ k, k ≤ D →
      (hamList G D P k).getLast? = some (P k) ∧
      (hamList G D P k).IsChain G.Adj ∧
      (hamList G D P k).Nodup ∧
      (∀ x, x ∈ hamList G D P k ↔ (∃ i, i ≤ k ∧ P i = x) ∨ (x ∉ pset D P ∧ slot G D P x < k)) := by
  intro k hk
  induction k with
  | zero =>
    refine ⟨rfl, List.isChain_singleton _, List.nodup_singleton _, fun x => ?_⟩
    simp only [hamList, List.mem_singleton]
    constructor
    · rintro rfl; exact Or.inl ⟨0, le_rfl, rfl⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨_, h⟩)
      · rw [Nat.le_zero.mp hi]
      · omega
  | succ k ih =>
    obtain ⟨hlast, hchain, hnd, hmem⟩ := ih (by omega)
    have hkD : k < D := by omega
    -- facts about the block
    have hblk_adj : ∀ x ∈ blk G D P k, G.Adj x (P k) ∧ G.Adj x (P (k + 1)) := by
      intro x hx
      obtain ⟨hxp, hsl⟩ := mem_blk.mp hx
      obtain ⟨_, h1, h2⟩ := slot_spec (exists_slot hconn hP hB hxp)
      rw [hsl] at h1 h2
      exact ⟨h1, h2⟩
    have hblk_nd : (blk G D P k).Nodup := Finset.nodup_toList _
    have hblk_chain : (blk G D P k).IsChain G.Adj := by
      apply isChain_of_pairwise_adj _ hblk_nd
      intro x hx y hy hxy
      obtain ⟨hxp, hsx⟩ := mem_blk.mp hx
      obtain ⟨hyp, hsy⟩ := mem_blk.mp hy
      exact slot_clique hconn hP hB hxp hyp hxy (hsx.trans hsy.symm)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [hamList]
    · simp only [hamList]
      refine List.IsChain.append (List.IsChain.append hchain hblk_chain ?_)
        (List.isChain_singleton _) ?_
      · intro a ha b hb
        rw [hlast, Option.mem_def, Option.some_inj] at ha
        subst ha
        exact (hblk_adj b (List.mem_of_mem_head? hb)).1.symm
      · intro a ha b hb
        simp only [List.head?_cons, Option.mem_def, Option.some_inj] at hb
        subst hb
        rw [List.getLast?_append, Option.mem_def] at ha
        cases h : (blk G D P k).getLast? with
        | none =>
          rw [h, hlast] at ha
          simp only [Option.none_or, Option.some_inj] at ha
          subst ha
          exact hP.adj k hkD
        | some c =>
          rw [h] at ha
          simp only [Option.some_or, Option.some_inj] at ha
          subst ha
          exact (hblk_adj c (List.mem_of_getLast? h)).2
    · simp only [hamList]
      rw [List.nodup_append, List.nodup_append]
      refine ⟨⟨hnd, hblk_nd, ?_⟩, List.nodup_singleton _, ?_⟩
      · intro a ha b hb hab
        subst hab
        obtain ⟨hbp, hbs⟩ := mem_blk.mp hb
        rcases (hmem a).mp ha with ⟨i, hi, rfl⟩ | ⟨_, hs⟩
        · exact hbp (mem_pset.mpr ⟨i, by omega, rfl⟩)
        · omega
      · intro a ha b hb hab
        rw [List.mem_singleton] at hb
        subst hb; subst hab
        rcases List.mem_append.mp ha with ha | ha
        · rcases (hmem _).mp ha with ⟨i, hi, hPi⟩ | ⟨hp, _⟩
          · have := hP.inj (by omega) (by omega) hPi
            omega
          · exact hp (mem_pset.mpr ⟨k + 1, by omega, rfl⟩)
        · exact (mem_blk.mp ha).1 (mem_pset.mpr ⟨k + 1, by omega, rfl⟩)
    · intro x
      simp only [hamList]
      rw [List.mem_append, List.mem_append, List.mem_singleton, mem_blk, hmem]
      constructor
      · rintro (((⟨i, hi, rfl⟩ | ⟨hp, hs⟩) | ⟨hp, hs⟩) | hx)
        · exact Or.inl ⟨i, by omega, rfl⟩
        · exact Or.inr ⟨hp, by omega⟩
        · exact Or.inr ⟨hp, by omega⟩
        · exact Or.inl ⟨k + 1, le_rfl, hx.symm⟩
      · rintro (⟨i, hi, rfl⟩ | ⟨hp, hs⟩)
        · rcases Nat.lt_or_ge i (k + 1) with h | h
          · exact Or.inl (Or.inl (Or.inl ⟨i, by omega, rfl⟩))
          · exact Or.inr (by rw [show i = k + 1 by omega])
        · rcases Nat.lt_or_ge (slot G D P x) k with h | h
          · exact Or.inl (Or.inl (Or.inr ⟨hp, h⟩))
          · exact Or.inl (Or.inr ⟨hp, by omega⟩)

/-- **Lemma L1.** If a connected graph has a geodesic of length `D` and no induced bipartite
subgraph on more than `D + 1` vertices, then it has a Hamiltonian path. -/
theorem ham_of_bipBound (hconn : G.Connected) (hP : Geod G D P) (hB : BipBound G (D + 1)) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨hlast, hchain, hnd, hmem⟩ := hamList_props hconn hP hB D le_rfl
  refine ham_of_list (hamList G D P D) ?_ hchain hnd ?_
  · intro h; rw [h] at hlast; simp at hlast
  · intro x
    rw [hmem]
    by_cases hx : x ∈ pset D P
    · exact Or.inl (mem_pset.mp hx)
    · exact Or.inr ⟨hx, (slot_spec (exists_slot hconn hP hB hx)).1⟩

end WOW198a
