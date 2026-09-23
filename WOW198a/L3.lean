import WOW198a.Basic

/-!
# Lemma L3: diameter two, no dominating vertex, `b(G) ≤ 4` ⟹ Hamiltonian path

This is a Chvátal–Erdős type longest-path argument.  Let `l` be a longest path and suppose a vertex
`h` is not on it.  Let `H` be the set of vertices reachable from `h` avoiding `l`, and `S` the set of
path vertices with a neighbour in `H`.  Using diameter two and the absence of a dominating vertex
one shows `|S| ≥ 2`.  For two vertices `l[i], l[j] ∈ S` (`i < j`) the vertices
`h, l[0], l[i+1], l[j+1]` are pairwise non-adjacent (otherwise there is a longer path), and together
with `l[i]` they span an induced star-plus-isolated-vertices, i.e. an induced bipartite subgraph on
five vertices.
-/

set_option linter.unusedSectionVars false

open SimpleGraph Finset

namespace WOW198a

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α}

/-! ### List lemmas -/

theorem getLast?_take_of {l : List α} {i : ℕ} {x : α} (hx : l[i]? = some x) :
    (l.take (i + 1)).getLast? = some x := by
  rw [List.getLast?_take]; simp [hx]

theorem head?_take_of {l : List α} {i : ℕ} {x : α} (hx : l[0]? = some x) :
    (l.take (i + 1)).head? = some x := by
  rw [List.head?_take, if_neg (by omega), List.head?_eq_getElem?, hx]

theorem mem_some {a b : α} (h : a ∈ some b) : a = b := by
  simpa [Option.mem_def, eq_comm] using h

/-- Inserting a chain between positions `i` and `i+1` of a chain. -/
theorem isChain_insert {l π : List α} {i : ℕ} {x y a b : α} (hl : l.IsChain G.Adj)
    (hπ : π.IsChain G.Adj) (ha : π.head? = some a) (hb : π.getLast? = some b)
    (hx : l[i]? = some x) (hy : l[i + 1]? = some y) (h1 : G.Adj x a) (h2 : G.Adj b y) :
    (l.take (i + 1) ++ π ++ l.drop (i + 1)).IsChain G.Adj := by
  refine List.IsChain.append (List.IsChain.append (hl.take _) hπ ?_) (hl.drop _) ?_
  · intro p hp q hq
    rw [getLast?_take_of hx] at hp
    rw [ha] at hq
    rw [mem_some hp, mem_some hq]; exact h1
  · intro p hp q hq
    rw [List.getLast?_append, hb] at hp
    rw [List.head?_drop, hy] at hq
    simp only [Option.some_or] at hp
    rw [mem_some hp, mem_some hq]; exact h2

theorem isChain_symm_reverse {l : List α} (hl : l.IsChain G.Adj) : l.reverse.IsChain G.Adj := by
  rw [List.isChain_reverse]
  exact hl.imp (fun _ _ h => h.symm)

/-- Rotation: `z, l[i], l[i-1], …, l[0], l[i+1], …`. -/
theorem isChain_rotate {l : List α} {i : ℕ} {z x₀ x y : α} (hl : l.IsChain G.Adj)
    (h0 : l[0]? = some x₀) (hx : l[i]? = some x) (hy : l[i + 1]? = some y)
    (hz : G.Adj z x) (h0y : G.Adj x₀ y) :
    (z :: ((l.take (i + 1)).reverse ++ l.drop (i + 1))).IsChain G.Adj := by
  rw [List.isChain_cons]
  refine ⟨?_, List.IsChain.append (isChain_symm_reverse (hl.take _)) (hl.drop _) ?_⟩
  · intro q hq
    rw [List.head?_append, List.head?_reverse, getLast?_take_of hx] at hq
    simp only [Option.some_or] at hq
    rw [mem_some hq]; exact hz
  · intro p hp q hq
    rw [List.getLast?_reverse, head?_take_of h0] at hp
    rw [List.head?_drop, hy] at hq
    rw [mem_some hp, mem_some hq]; exact h0y

/-- Reversing the segment between two insertion points. -/
theorem isChain_cross {l π : List α} {i j : ℕ} {x y x' y' a b : α} (hl : l.IsChain G.Adj)
    (hij : i < j) (hπ : π.IsChain G.Adj) (ha : π.head? = some a) (hb : π.getLast? = some b)
    (hx : l[i]? = some x) (hx' : l[i + 1]? = some x') (hy : l[j]? = some y)
    (hy' : l[j + 1]? = some y') (h1 : G.Adj x a) (h2 : G.Adj b y) (h3 : G.Adj x' y') :
    (l.take (i + 1) ++ π ++ (((l.drop (i + 1)).take (j - i)).reverse ++ l.drop (j + 1))).IsChain
      G.Adj := by
  set M := (l.drop (i + 1)).take (j - i) with hM
  have hMhead : M.head? = some x' := by
    rw [hM, List.head?_take, if_neg (by omega), List.head?_drop, hx']
  have hMlast : M.getLast? = some y := by
    rw [hM, List.getLast?_take, if_neg (by omega), List.getElem?_drop,
      show i + 1 + (j - i - 1) = j by omega, hy]
    rfl
  refine List.IsChain.append (List.IsChain.append (hl.take _) hπ ?_)
    (List.IsChain.append (isChain_symm_reverse ((hl.drop _).take _)) (hl.drop _) ?_) ?_
  · intro p hp q hq
    rw [getLast?_take_of hx] at hp
    rw [ha] at hq
    rw [mem_some hp, mem_some hq]; exact h1
  · intro p hp q hq
    rw [List.getLast?_reverse, hMhead] at hp
    rw [List.head?_drop, hy'] at hq
    rw [mem_some hp, mem_some hq]; exact h3
  · intro p hp q hq
    rw [List.getLast?_append, hb] at hp
    simp only [Option.some_or] at hp
    rw [List.head?_append, List.head?_reverse, hMlast] at hq
    simp only [Option.some_or] at hq
    rw [mem_some hp, mem_some hq]; exact h2

theorem nodup_of_perm {l l' π : List α} (hl : l.Nodup) (hπ : π.Nodup) (hd : ∀ y ∈ π, y ∉ l)
    (hp : l'.Perm (π ++ l)) : l'.Nodup :=
  hp.nodup_iff.mpr (List.nodup_append.mpr ⟨hπ, hl, fun a ha _ hb hab => hd a ha (hab ▸ hb)⟩)

/-! ### Longest paths -/

/-- A path, given as the list of its vertices. -/
def IsPathList (G : SimpleGraph α) (l : List α) : Prop := l.Nodup ∧ l.IsChain G.Adj

theorem exists_longest [Nonempty α] (G : SimpleGraph α) :
    ∃ l, IsPathList G l ∧ l ≠ [] ∧ ∀ l', IsPathList G l' → l'.length ≤ l.length := by
  classical
  let Q : ℕ → Prop := fun k => ∃ l, IsPathList G l ∧ l.length = k
  have hQ1 : Q 1 :=
    ⟨[Classical.arbitrary α], ⟨List.nodup_singleton _, List.isChain_singleton _⟩, rfl⟩
  have hle : 1 ≤ Fintype.card α := Fintype.card_pos
  obtain ⟨l, hl, hlen⟩ := Nat.findGreatest_spec (P := Q) hle hQ1
  have h1 := Nat.le_findGreatest hle hQ1
  refine ⟨l, hl, ?_, fun l' hl' => ?_⟩
  · intro h; subst h; simp at hlen; omega
  · rw [hlen]
    exact Nat.le_findGreatest hl'.1.length_le_card ⟨l', hl', rfl⟩

/-! ### Lemma L3 -/

theorem dist_eq_two (hconn : G.Connected) (hd : ∀ u v, G.dist u v ≤ 2) {u v : α} (huv : u ≠ v)
    (hn : ¬ G.Adj u v) : ∃ y, G.Adj u y ∧ G.Adj y v := by
  apply exists_common_of_dist_two hconn
  have h1 := hd u v
  have h2 : G.dist u v ≠ 0 := by
    rw [Ne, hconn.dist_eq_zero_iff]; exact huv
  have h3 : G.dist u v ≠ 1 := fun h => hn (dist_eq_one_iff_adj.mp h)
  omega

theorem ham_of_diam_two (hconn : G.Connected) (hd : ∀ u v, G.dist u v ≤ 2)
    (hdom : ∀ v, ∃ w, w ≠ v ∧ ¬ G.Adj v w) (hB : BipBound G 4) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have : Nonempty α := hconn.nonempty
  obtain ⟨l, ⟨hlnd, hlc⟩, hlne, hmax⟩ := exists_longest G
  by_cases hall : ∀ x, x ∈ l
  · exact ham_of_list l hlne hlc hlnd hall
  exfalso
  push Not at hall
  obtain ⟨h, hh⟩ := hall
  have noLonger : ∀ l' : List α, l'.Nodup → l'.IsChain G.Adj → l.length < l'.length → False :=
    fun l' h1 h2 h3 => absurd (hmax l' ⟨h1, h2⟩) (by omega)
  -- the vertices reachable from `h` outside `l`
  let R : α → Prop := fun z => ∃ q : G.Walk h z, ∀ y ∈ q.support, y ∉ l
  have R_h : R h := ⟨Walk.nil, by simpa using hh⟩
  have R_not : ∀ z, R z → z ∉ l := fun z ⟨q, hq⟩ => hq z q.end_mem_support
  have R_step : ∀ z y, R z → G.Adj z y → y ∉ l → R y := by
    rintro z y ⟨q, hq⟩ hzy hy
    refine ⟨q.concat hzy, fun u hu => ?_⟩
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact hq u hu
    · exact hy
  have R_path : ∀ a b, R a → R b → ∃ π : List α, π.head? = some a ∧ π.getLast? = some b ∧
      π.Nodup ∧ π.IsChain G.Adj ∧ ∀ y ∈ π, y ∉ l := by
    rintro a b ⟨qa, hqa⟩ ⟨qb, hqb⟩
    let w := (qa.reverse.append qb).bypass
    refine ⟨w.support, ?_, ?_, (Walk.bypass_isPath _).support_nodup, w.isChain_adj_support, ?_⟩
    · rw [← Walk.cons_tail_support]; rfl
    · rw [List.getLast?_eq_some_getLast w.support_ne_nil, Walk.getLast_support]
    · intro y hy
      have hy' := Walk.support_bypass_subset_support _ hy
      rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hy'
      rcases hy' with hy' | hy'
      · exact hqa y hy'
      · exact hqb y hy'
  -- positions on the path
  set k := l.length with hk
  have hkpos : 0 < k := List.length_pos_of_ne_nil hlne
  let v : ℕ → α := fun i => l.getD i h
  have hv : ∀ i, i < k → l[i]? = some (v i) := by
    intro i hi
    simp [v, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hv_mem : ∀ i, i < k → v i ∈ l := fun i hi => List.mem_of_getElem? (hv i hi)
  have hv_inj : ∀ i j, i < k → j < k → v i = v j → i = j := by
    intro i j hi hj hij
    have h1 := hv i hi
    have h2 := hv j hj
    rw [hij] at h1
    exact (List.getElem?_inj hi hlnd).mp (h1.trans h2.symm)
  have hv_adj : ∀ i, i + 1 < k → G.Adj (v i) (v (i + 1)) := by
    intro i hi
    have := List.isChain_iff_getElem.mp hlc i hi
    have e1 : v i = l[i] := by
      simp only [v, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    have e2 : v (i + 1) = l[i + 1] := by
      simp only [v, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    rw [e1, e2]; exact this
  have hv_of_mem : ∀ x, x ∈ l → ∃ i, i < k ∧ v i = x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact ⟨i, hi, by simp [v, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]⟩
  have hl0 : l[0]? = some (v 0) := hv 0 hkpos
  -- (c1) `H` has no neighbour at the start of `l`
  have c1 : ∀ z, R z → ¬ G.Adj z (v 0) := by
    intro z hz hadj
    apply noLonger (z :: l)
    · exact List.nodup_cons.mpr ⟨R_not z hz, hlnd⟩
    · rw [List.isChain_cons]
      refine ⟨fun q hq => ?_, hlc⟩
      rw [List.head?_eq_getElem?, hl0] at hq
      rw [mem_some hq]; exact hadj
    · simp; omega
  -- (c2) nor at the end
  have c2 : ∀ z, R z → ¬ G.Adj (v (k - 1)) z := by
    intro z hz hadj
    apply noLonger (l ++ [z])
    · rw [List.nodup_append]
      refine ⟨hlnd, List.nodup_singleton _, fun a ha b hb hab => ?_⟩
      rw [List.mem_singleton] at hb
      exact R_not z hz (hb ▸ hab ▸ ha)
    · refine List.IsChain.append hlc (List.isChain_singleton _) (fun p hp q hq => ?_)
      rw [List.getLast?_eq_getElem?, ← hk, hv (k - 1) (by omega)] at hp
      rw [List.head?_cons] at hq
      rw [mem_some hp, mem_some hq]; exact hadj
    · simp; omega
  -- (c3) successors of attachment points are not attachment points
  have c3 : ∀ i z b, i + 1 < k → R z → G.Adj (v i) z → R b → ¬ G.Adj b (v (i + 1)) := by
    intro i z b hi hz hvz hb hbv
    obtain ⟨π, ha, hπb, hπnd, hπc, hπl⟩ := R_path z b hz hb
    have hπne : π ≠ [] := by rintro rfl; simp at ha
    have hperm : (l.take (i + 1) ++ π ++ l.drop (i + 1)).Perm (π ++ l) := by
      have p2 : (l.take (i + 1) ++ π ++ l.drop (i + 1)).Perm
          (π ++ l.take (i + 1) ++ l.drop (i + 1)) := List.perm_append_comm.append_right _
      rwa [List.append_assoc π, List.take_append_drop] at p2
    apply noLonger _ (nodup_of_perm hlnd hπnd hπl hperm)
      (isChain_insert hlc hπc ha hπb (hv i (by omega)) (hv (i + 1) hi) hvz hbv)
    rw [hperm.length_eq, List.length_append]
    have := List.length_pos_of_ne_nil hπne
    omega
  -- (c4) the start is not adjacent to successors of attachment points
  have c4 : ∀ i z, i + 1 < k → R z → G.Adj (v i) z → ¬ G.Adj (v 0) (v (i + 1)) := by
    intro i z hi hz hvz h0
    have hperm : (z :: ((l.take (i + 1)).reverse ++ l.drop (i + 1))).Perm ([z] ++ l) := by
      refine List.Perm.cons _ ?_
      have p := (List.reverse_perm (l.take (i + 1))).append_right (l.drop (i + 1))
      rwa [List.take_append_drop] at p
    apply noLonger _ (nodup_of_perm hlnd (List.nodup_singleton _)
      (by simpa using R_not z hz) hperm)
      (isChain_rotate hlc hl0 (hv i (by omega)) (hv (i + 1) hi) hvz.symm h0)
    rw [hperm.length_eq]; simp; omega
  -- (c5) successors of two attachment points are not adjacent
  have c5 : ∀ i j z b, i < j → j + 1 < k → R z → G.Adj (v i) z → R b → G.Adj (v j) b →
      ¬ G.Adj (v (i + 1)) (v (j + 1)) := by
    intro i j z b hij hj hz hvz hb hvb hadj
    obtain ⟨π, ha, hπb, hπnd, hπc, hπl⟩ := R_path z b hz hb
    have hπne : π ≠ [] := by rintro rfl; simp at ha
    set M := (l.drop (i + 1)).take (j - i) with hM
    have hsplit : l = l.take (i + 1) ++ (M ++ l.drop (j + 1)) := by
      have : l.drop (j + 1) = (l.drop (i + 1)).drop (j - i) := by
        rw [List.drop_drop]; congr 1; omega
      rw [this, hM, List.take_append_drop, List.take_append_drop]
    have hperm : (l.take (i + 1) ++ π ++ (M.reverse ++ l.drop (j + 1))).Perm (π ++ l) := by
      have p1 : (l.take (i + 1) ++ π ++ (M.reverse ++ l.drop (j + 1))).Perm
          (l.take (i + 1) ++ π ++ (M ++ l.drop (j + 1))) :=
        List.Perm.append_left _ ((List.reverse_perm _).append_right _)
      have p2 : (l.take (i + 1) ++ π ++ (M ++ l.drop (j + 1))).Perm
          (π ++ l.take (i + 1) ++ (M ++ l.drop (j + 1))) :=
        List.perm_append_comm.append_right _
      have e : π ++ l.take (i + 1) ++ (M ++ l.drop (j + 1)) = π ++ l := by
        rw [List.append_assoc, ← hsplit]
      exact p1.trans (e ▸ p2)
    apply noLonger _ (nodup_of_perm hlnd hπnd hπl hperm)
      (isChain_cross hlc hij hπc ha hπb (hv i (by omega)) (hv (i + 1) (by omega))
        (hv j (by omega)) (hv (j + 1) hj) hvz hvb.symm hadj)
    rw [hperm.length_eq, List.length_append]
    have := List.length_pos_of_ne_nil hπne
    omega
  -- attachment points
  let N : α → Prop := fun x => x ∈ l ∧ ∃ z, R z ∧ G.Adj x z
  -- there are two distinct attachment points
  have two : ∃ x y, N x ∧ N y ∧ x ≠ y := by
    by_contra hc
    push Not at hc
    -- every vertex of `H` sees a common attachment point `s`
    have att : ∀ z, R z → ∃ y, N y ∧ G.Adj z y ∧ G.Adj y (v 0) := by
      intro z hz
      have hz0 : z ≠ v 0 := fun he => R_not z hz (he ▸ hv_mem 0 hkpos)
      obtain ⟨y, hzy, hy0⟩ := dist_eq_two hconn hd hz0 (c1 z hz)
      by_cases hyl : y ∈ l
      · exact ⟨y, ⟨hyl, z, hz, hzy.symm⟩, hzy, hy0⟩
      · exact absurd hy0 (c1 y (R_step z y hz hzy hyl))
    obtain ⟨s, hsN, -, -⟩ := att h R_h
    have hRs : ∀ z, R z → G.Adj z s := by
      intro z hz
      obtain ⟨y, hyN, hzy, -⟩ := att z hz
      rwa [hc y s hyN hsN] at hzy
    obtain ⟨w, hws, hsw⟩ := hdom s
    apply hsw
    by_cases hRw : R w
    · exact (hRs w hRw).symm
    · have hNw : ∀ z, R z → G.Adj z w → False := by
        intro z hz hzw
        by_cases hwl : w ∈ l
        · exact hws (hc w s ⟨hwl, z, hz, hzw.symm⟩ hsN)
        · exact hRw (R_step z w hz hzw hwl)
      have hhw : h ≠ w := fun he => hRw (he ▸ R_h)
      obtain ⟨y, hhy, hyw⟩ := dist_eq_two hconn hd hhw (fun hh' => hNw h R_h hh')
      by_cases hyl : y ∈ l
      · rwa [hc y s ⟨hyl, h, R_h, hhy.symm⟩ hsN] at hyw
      · exact absurd hyw (hNw y (R_step h y R_h hhy hyl))
  obtain ⟨x, y, ⟨hxl, zx, hzx, hxz⟩, ⟨hyl, zy, hzy, hyz⟩, hxy⟩ := two
  obtain ⟨i₀, hi₀, rfl⟩ := hv_of_mem x hxl
  obtain ⟨j₀, hj₀, rfl⟩ := hv_of_mem y hyl
  have hij₀ : i₀ ≠ j₀ := fun he => hxy (he ▸ rfl)
  -- order the two attachment points
  obtain ⟨i, j, hij, hi, hj, zi, hzi, hvi, zj, hzj, hvj⟩ : ∃ i j, i < j ∧ i < k ∧ j < k ∧
      ∃ zi, R zi ∧ G.Adj (v i) zi ∧ ∃ zj, R zj ∧ G.Adj (v j) zj := by
    rcases Nat.lt_or_gt_of_ne hij₀ with h' | h'
    · exact ⟨i₀, j₀, h', hi₀, hj₀, zx, hzx, hxz, zy, hzy, hyz⟩
    · exact ⟨j₀, i₀, h', hj₀, hi₀, zy, hzy, hyz, zx, hzx, hxz⟩
  have hi1 : 1 ≤ i := by
    by_contra h'
    have : i = 0 := by omega
    subst this
    exact c1 zi hzi hvi.symm
  have hj1 : j + 1 < k := by
    by_contra h'
    have : j = k - 1 := by omega
    subst this
    exact c2 zj hzj hvj
  -- the five vertices
  let I : List α := [h, v 0, v (i + 1), v (j + 1)]
  have hI : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b := by
    have n1 : ¬ G.Adj h (v 0) := c1 h R_h
    have n2 : ¬ G.Adj h (v (i + 1)) := c3 i zi h (by omega) hzi hvi R_h
    have n3 : ¬ G.Adj h (v (j + 1)) := c3 j zj h hj1 hzj hvj R_h
    have n4 : ¬ G.Adj (v 0) (v (i + 1)) := c4 i zi (by omega) hzi hvi
    have n5 : ¬ G.Adj (v 0) (v (j + 1)) := c4 j zj hj1 hzj hvj
    have n6 : ¬ G.Adj (v (i + 1)) (v (j + 1)) := c5 i j zi zj hij hj1 hzi hvi hzj hvj
    intro a ha b hb hab
    simp only [I, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;>
      rw [ha, hb] at hab <;>
      first
      | exact G.irrefl hab
      | exact n1 hab | exact n1 hab.symm | exact n2 hab | exact n2 hab.symm
      | exact n3 hab | exact n3 hab.symm | exact n4 hab | exact n4 hab.symm
      | exact n5 hab | exact n5 hab.symm | exact n6 hab | exact n6 hab.symm
  let s : Finset α := insert (v i) I.toFinset
  let f : α → ℕ := fun u => if u = v i then 1 else 0
  have hvi_notI : v i ∉ I := by
    simp only [I, List.mem_cons, List.not_mem_nil, or_false]
    rintro (he | he | he | he)
    · exact R_not h R_h (he ▸ hv_mem i hi)
    · have := hv_inj _ _ hi hkpos he; omega
    · have := hv_inj _ _ hi (by omega) he; omega
    · have := hv_inj _ _ hi (by omega) he; omega
  have hInd : I.Nodup := by
    have hh0 : h ≠ v 0 := fun he => R_not h R_h (he ▸ hv_mem 0 hkpos)
    have hh1 : h ≠ v (i + 1) := fun he => R_not h R_h (he ▸ hv_mem (i + 1) (by omega))
    have hh2 : h ≠ v (j + 1) := fun he => R_not h R_h (he ▸ hv_mem (j + 1) hj1)
    have e1 : v 0 ≠ v (i + 1) := fun he => by have := hv_inj _ _ hkpos (by omega) he; omega
    have e2 : v 0 ≠ v (j + 1) := fun he => by have := hv_inj _ _ hkpos hj1 he; omega
    have e3 : v (i + 1) ≠ v (j + 1) := fun he => by
      have := hv_inj _ _ (by omega) hj1 he; omega
    simp [I, hh0, hh1, hh2, e1, e2, e3]
  have hcard : s.card = 5 := by
    rw [Finset.card_insert_of_notMem (by simpa using hvi_notI), List.card_toFinset,
      hInd.dedup]
    rfl
  have := hB s f (by
    intro a ha b hb hab
    simp only [s, Finset.mem_insert, List.mem_toFinset] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd hab G.irrefl
    · have : b ≠ v i := fun he => hvi_notI (he ▸ hb)
      simp [f, this]
    · have : a ≠ v i := fun he => hvi_notI (he ▸ ha)
      simp [f, this]
    · exact absurd hab (hI a ha b hb))
  omega

end WOW198a
