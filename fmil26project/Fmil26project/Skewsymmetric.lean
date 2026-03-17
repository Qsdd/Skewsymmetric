import Mathlib
open Matrix
open BigOperators
open Equiv Equiv.Perm Finset Function
open Finset

--variable {α β n m R : Type*}
namespace Matrix

/-- A matrix `A : Matrix n n α` is "skewsymmetric" if `-Aᵀ = A`. -/
def IsSkewSymm [Neg α] (A : Matrix n n α) : Prop :=
  -Aᵀ = A

instance [Neg α] (A : Matrix n n α) [Decidable (-Aᵀ = A)] : Decidable (IsSkewSymm A) :=
  inferInstanceAs <| Decidable (_ = _)

theorem IsSkewSymm.eq [Neg α] {A : Matrix n n α} (h : A.IsSkewSymm) : -Aᵀ = A :=
  h
/-- A version of `Matrix.ext_iff` that unfolds the `Matrix.transpose`. -/
theorem IsSkewSymm.ext_iff [Neg α] {A : Matrix n n α} : A.IsSkewSymm ↔ ∀ i j, -A j i = A i j :=
  Matrix.ext_iff.symm

/-- A version of `Matrix.ext` that unfolds the `Matrix.transpose`. -/
theorem IsSkewSymm.ext [Neg α] {A : Matrix n n α} : (∀ i j, -A j i = A i j) → A.IsSkewSymm :=
  Matrix.ext

theorem IsSkewSymm.apply [Neg α] {A : Matrix n n α} (h : A.IsSkewSymm) (i j : n) : -A j i = A i j :=
  IsSkewSymm.ext_iff.1 h i j


theorem isSkewSymm_sub_transpose_self [AddCommGroup α] (A : Matrix n n α) : (A - Aᵀ).IsSkewSymm :=
by
apply IsSkewSymm.ext
simp only [sub_apply, transpose_apply, neg_sub, implies_true]

theorem isSkewSymm_transpose_sub_self [AddCommGroup α] (A : Matrix n n α) : (Aᵀ-A).IsSkewSymm :=
by
apply IsSkewSymm.ext
simp only [sub_apply, transpose_apply, neg_sub, implies_true]

lemma transpose_eq_minus_of_Skewsymm [CommRing α] (A : Matrix n n α) (h : A.IsSkewSymm) :
(Aᵀ =-A ) := by
apply IsSkewSymm.eq at h
exact neg_eq_iff_eq_neg.mp h




variable {n : ℕ}
/-- The determinant of an odd-dimensional skew-symmetric matrix is 0. -/
theorem det_eq_zero_of_IsSkewSymm_odd_dim [CommRing α] [NoZeroDivisors α]
    (A : Matrix (Fin n) (Fin n) α) (h0 : ¬(1:α) + (1:α) = 0) (h1 : A.IsSkewSymm)
    (h2 : Odd n) : A.det =0
:= by
  have h3: det A = det (-A) := by
    rw[← det_transpose]
    rw[transpose_eq_minus_of_Skewsymm]
    exact h1
  rw[det_neg] at h3
  have h4: det A = -det (A) := by
    nth_rewrite 1[h3]
    rw[Fintype.card_fin n]
    rw[ Odd.neg_one_pow h2]
    exact neg_one_mul A.det
  apply eq_neg_iff_add_eq_zero.mp at h4
  rw[← one_mul A.det] at h4
  rw[← RightDistribClass.right_distrib] at h4
  rw[mul_eq_zero] at h4
  apply Or.resolve_left at h4
  exact h4 h0

---The following are due to LEAN club :
-- George H. Seelinger, Chenchen Zhao, Darij Grinberg modified to my purposes

structure PerfectMatching (α : Type u) [Fintype α] [DecidableEq α] [LinearOrder α] where
  edges : Finset (α ×ₗ α)
  ordered : ∀ b ∈ edges, b.1 < b.2
  disjoint : ∀ a ∈ edges, ∀ b ∈ edges,
  (a ≠ b)→ (a.1 ≠ b.1  ∧ a.2 ≠ b.2 ∧ a.1 ≠ b.2 ∧ a.2 ≠ b.1)
  union : ∀ (i : α), ∃ b ∈ edges, (i = b.1 ∨ i = b.2)



variable {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α]
--sum_sigma\in PerfectMatching signpm(sigma)\prod_i\in sigma.edges a i.1 i.2
def set {α} [Fintype α] [DecidableEq α] (b : α × α) : Finset α :=
  {b.1, b.2}


-- In a perfect matching, each element of α lies in EXACTLY
-- one block.
theorem PerfectMatching.unique_block (M : PerfectMatching α) :
  ∀ (i : α), ∃! b ∈ M.edges, i ∈ set b := by
    intro i
    obtain ⟨b, hbedge, hbi⟩ := M.union i
    use b
    constructor
    constructor
    · exact hbedge
    · rw[set]
      refine mem_insert.mpr ?_
      by_cases h: i=b.1
      · exact Or.symm (Or.inr h)
      have halt : i=b.2 := by exact Or.resolve_left hbi h
      refine Or.symm (Or.intro_left (i = b.1) ?_)
      exact mem_singleton.mpr halt
    intro y ⟨hyedge, hyi⟩
    have hyinew : i=y.1∨ i=y.2 :=
      by
      rw[set] at hyi
      simp only [mem_insert, mem_singleton] at hyi
      exact hyi
    by_contra hneq
    change (y ≠ b) at hneq
    symm at hneq
    have hdj : (b.1 ≠ y.1 ∧ b.2 ≠ y.2 ∧ b.1 ≠ y.2 ∧ b.2 ≠ y.1) := M.disjoint b hbedge y hyedge hneq
    by_cases hy1: i=y.1
    · by_cases hb1:i=b.1
      · rw[← hy1, hb1] at hdj
        have hcontra := hdj.left
        contradiction
      have hb2 : i=b.2 := by exact Or.resolve_left hbi hb1
      rw[← hy1,hb2] at hdj
      have hcontra:=hdj.right.right.right
      contradiction
    have hy2 : i=y.2 :=by exact Or.resolve_left hyinew hy1
    by_cases hb1:i=b.1
    · rw[← hy2,hb1] at hdj
      have hcontra := hdj.right.right.left
      contradiction
    have hb2 : i=b.2 := by exact Or.resolve_left hbi hb1
    rw[← hy2, hb2] at hdj
    have hcontra := hdj.right.left
    contradiction



lemma block_card_two
    (M : PerfectMatching α) {b : α × α} (hb : b ∈ M.edges) :
    (set b).card = 2 := by
    have hne : b.1 ≠ b.2 := ne_of_lt (M.ordered b hb)
    rw[set]
    simp only [mem_singleton, hne, not_false_eq_true, card_insert_of_notMem, card_singleton,
      Nat.reduceAdd]

lemma blocks_cover (M : PerfectMatching α) :
    (M.edges.biUnion set : Finset α) = Finset.univ := by
  ext i; constructor
  · intro _; exact Finset.mem_univ _
  · intro _
    rcases M.union i with ⟨b, hb, hi⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨b, hb, ?_⟩
    rw[set]
    rcases hi with rfl | rfl <;> simp
lemma disjoint_edges (M : PerfectMatching α) :
  ∀ a ∈ M.edges, ∀ b ∈ M.edges, a ≠ b → Disjoint ({a.1, a.2} : Finset α) ({b.1, b.2} : Finset α)
:=by
intro a ha b hb hab
have hm:= M.disjoint a ha b hb hab
have hma1 : (a.1 ≠ b.1) ∧ (a.1≠ b.2) := ⟨hm.left,hm.right.right.left⟩
refine disjoint_insert_left.mpr ?_
constructor
· by_contra hcontra
  simp only [mem_insert, mem_singleton] at hcontra
  by_cases ha1 : a.1 = b.1
  · have hcontra1 := hma1.left
    contradiction
  have ha2 : a.1=b.2 := by exact Or.resolve_left hcontra ha1
  have hcontra2 := hma1.right
  contradiction
refine disjoint_singleton_left.mpr ?_
· have hma2 : a.2 ≠ b.1 ∧ a.2≠ b.2 :=
    by exact ⟨hm.right.right.right,hm.right.left⟩
  by_contra hcontra
  simp only [mem_insert, mem_singleton] at hcontra
  by_cases ha2 : a.2 = b.1
  · have hcontra1 := hma2.left
    contradiction
  have ha2 : a.2=b.2 := by exact Or.resolve_left hcontra ha2
  have hcontra2 := hma2.right
  contradiction
lemma card_eq_sum_block_card (M : PerfectMatching α) :
    Fintype.card α = ∑ b ∈ M.edges, (set b).card := by
  -- cardinality of the union of blocks as a sum
  calc
    Fintype.card α
        = (Finset.univ : Finset α).card := (Finset.card_univ (α := α)).symm
    _ = (M.edges.biUnion set : Finset α).card := by
          simp [blocks_cover M]
    _ = ∑ b ∈ M.edges, (set b).card := Finset.card_biUnion (disjoint_edges M)

theorem PerfectMatching.card_eq_twice_card_edges (M : PerfectMatching α) :
  Fintype.card α = 2 * M.edges.card :=
  calc Fintype.card α
    _ = ∑ b ∈ M.edges, (set b).card := card_eq_sum_block_card M
    _ = ∑ b ∈ M.edges, (2 : ℕ) := by
        refine Finset.sum_congr rfl ?_
        intro b hb
        apply block_card_two M hb
        -- sum of a constant over a finite set
    _ = 2 * M.edges.card := by simp [mul_comm]

theorem PerfectMatching.card_even (M : PerfectMatching α) :
  Even (Fintype.card α) := by
    refine ⟨M.edges.card, ?_⟩
    rw [PerfectMatching.card_eq_twice_card_edges M]
    simp [two_mul]

theorem even_card_of_exists_PerfectMatching
    (h : Nonempty (PerfectMatching α)) :
    Even (Fintype.card α) := by
  obtain ⟨M⟩ := h
  exact PerfectMatching.card_even M



def PerfectMatching.block (M : PerfectMatching α) : α → α × α :=
  fun i => Finset.choose (fun (b : α × α) => (i ∈ set b))
                         (M.edges : Finset (α × α)) (PerfectMatching.unique_block M i)


theorem PerfectMatching.block_spec (M : PerfectMatching α) (i : α) :
  (PerfectMatching.block M i ∈ M.edges) ∧ (i ∈ set (PerfectMatching.block M i)) := by
    apply choose_spec

theorem PerfectMatching.block_uni (M : PerfectMatching α) (i : α) (b : α × α)
  (hbe : b ∈ M.edges)
  (hib : i ∈ set b) : b = PerfectMatching.block M i := by
    have h2 : (b ∈ M.edges) ∧ (i ∈ set b) := ⟨hbe, hib⟩
    apply (PerfectMatching.unique_block M i).unique
    · exact h2
    · exact (PerfectMatching.block_spec M i)

def first_or_second_if_not (pair : α × α) (i : α) := if pair.1 = i then pair.2 else pair.1

-- The partner of a given element of α in M:
def PerfectMatching.partner (M : PerfectMatching α) : α → α :=
  fun i => first_or_second_if_not (M.block i) i


theorem PerfectMatching.partner_block (M : PerfectMatching α) (i : α) :
    set (M.block i) = {i, M.partner i} := by
  -- Proof generated by Aristotle:
  ext i
  -- By definition of the block, if i is in the block, then the block must be {i, partner i}.
  have h_block : ∀ i : α, set (M.block i) = {i, M.partner i} := by
    -- By definition of `PerfectMatching.block`, the block is a pair `(a, b)` where `a < b` and `i` is in `{a, b}`.
    intro i
    obtain ⟨a, b, hab, hi⟩ : ∃ a b : α, a < b ∧ i ∈ ({a, b} : Finset α) ∧ M.block i = (a, b) := by
      have := M.block_spec i;
      exact ⟨ _, _, M.ordered _ this.1, this.2, rfl ⟩;
    unfold PerfectMatching.partner;
    unfold first_or_second_if_not; aesop;
    exact Finset.pair_comm _ _;
  aesop

-- From here on out solely my own work.
lemma partner_not_eq
  {n : ℕ} (M : (PerfectMatching (Fin (2 * n)))) (x : Fin (2 * n)) :
  PerfectMatching.partner M x ≠ x :=
by
intro h
have help := M.block_spec x
obtain⟨help1,help2⟩:=help
rw[PerfectMatching.partner] at h
rw[first_or_second_if_not] at h
by_cases h2: (M.block x).1 =x
· simp only [h2, ↓reduceIte] at h
  nth_rewrite 2 [← h2] at h
  have h3:=M.ordered (M.block x) help1
  symm at h
  rw[h] at h3
  exact (lt_self_iff_false (M.block x).2).mp h3
· simp only [h2, ↓reduceIte] at h

-- We define a list which are all the edges of a PerfectMatching on Fin(2*n)in order.
-- This will be useful in defining a permutation
def sortedEdges
  (M : PerfectMatching (Fin (2 * n))) :
  List (Fin (2*n)×ₗFin (2*n)) :=
  M.edges.sort
--We establish that the length is the expected value
theorem sortedEdges_length (n : ℕ) (M : PerfectMatching (Fin (2 * n))) :
((M.edges).sort).length= n:=
by
rw[Finset.length_sort]
have h: 2 * n = 2 * M.edges.card :=
  by
  rw [← PerfectMatching.card_eq_twice_card_edges M]
  rw[Fintype.card_fin (2*n)]
apply Nat.mul_left_cancel at h
· exact h.symm
exact Nat.zero_lt_two

--We establish that the list contains no duplicates
theorem sortedEdges_nodup (n : ℕ) (M : PerfectMatching (Fin (2 * n))) : List.Nodup (M.edges.sort) :=
by exact sort_nodup M.edges fun a b ↦ a ≤ b

theorem sortedEdges_injone (l m n : ℕ) (M : PerfectMatching (Fin (2 * n)))
(hl : l < (sortedEdges M).length) (hm : m < (sortedEdges M).length)
(h : (sortedEdges M)[l] = (sortedEdges M)[m]) : l=m:=by
have h4 := sortedEdges_nodup n M
exact (List.Nodup.getElem_inj_iff h4).mp h

variable {R : Type v} [CommRing R]
end Matrix
--We define a number of helper functions to define the associated permutation to the matching
--These first two define an equivalence between the finset containing 2n elements
--and the product of finsets containing 2 and n elements. This eases defining a permuation on 2n
def evenfiniso (n : ℕ) [NeZero n] (u : Fin (2 * n)) :
(Fin 2 × Fin n):= (Fin.ofNat 2 ((Fin.val u) %2) ,(Fin.ofNat n ((Fin.val u)/2) : Fin n))
def fineveniso {n : ℕ} [NeZero n] (u : (Fin 2 × Fin n)) : Fin (2*n)
:= Fin.ofNat (2*n) (2* (Fin.val (u.2)) + Fin.val (u.1))
-- The following is the heart of our permutation but defined on a product.
def crossedges (n : ℕ) (M : PerfectMatching (Fin (2 * n)))
(u : Fin 2 × Fin n) : Fin (2 * n) :=
by
have h: ((M.edges).sort).length= n:=
  by exact sortedEdges_length n M
by_cases h2: u.1=0
· exact ((M.edges.sort)[u.2]).1
exact ((M.edges.sort)[u.2]).2
--Here we define the actual permutation
def perm_of_matching (n : ℕ) [NeZero n] (M : PerfectMatching (Fin (2 * n)))
(u : Fin (2 * n)) : Fin (2 * n) :=crossedges  n M (evenfiniso n u)
--We show that our two helper functions indeed are an equivalence by showing they are inverses
theorem fineveniso_inverse {n : ℕ} [NeZero n] (u : Fin (2 * n)) :
fineveniso (evenfiniso n u) = u:= by
rw[fineveniso, evenfiniso]
simp only [Fin.ofNat_eq_cast, Fin.val_natCast, dvd_refl, Nat.mod_mod_of_dvd]
have h1 : ↑u / 2 % n = ↑u / 2 := by
  have h1_1 :  ↑u / 2< n :=
    by
    refine Nat.div_lt_of_lt_mul ?_
    exact u.isLt
  exact Nat.mod_eq_of_lt h1_1
rw[h1]
rw[add_comm]
rw[Nat.mod_add_div]
exact Fin.cast_val_eq_self u

theorem evenfiniso_inverse {n : ℕ} [NeZero n]
  (u : (Fin 2 × Fin n)) : evenfiniso (n) (fineveniso u) = u:= by
rw[fineveniso, evenfiniso]
simp only [Fin.ofNat_eq_cast, Fin.val_natCast, dvd_mul_right, Nat.mod_mod_of_dvd,
  Nat.mul_add_mod_self_left]
have h: Fin.val u.1 ≤ 1:= by exact Fin.is_le u.1
have h1 : Fin.val u.1 < 2 :=by exact u.1.isLt
have h2 : Fin.val u.2 < n:= by exact u.2.isLt
have h3 : Fin.val u.2 ≤ n-1:= by exact Nat.le_sub_one_of_lt h2
have h4 : 2* Fin.val u.2 ≤ 2*(n-1) := by exact Nat.mul_le_mul_left 2 h3
have h5 : 2 * Fin.val u.2 + Fin.val u.1≤ 2*(n-1)+1:= by exact Nat.add_le_add h4 h
have h6 : 2*(n-1) +1 = 2*n -1 :=
  have h6help: n = (n-1)+1 := by
    refine Eq.symm (Nat.sub_add_cancel ?_)
    exact NeZero.one_le
  by
  nth_rewrite 2[h6help]
  rw[Nat.mul_add]
  simp
rw[h6] at h5
have h7 : 0<2*n  :=by exact Nat.pos_of_neZero (2 * n)
have h8 :2 * Fin.val u.2 + Fin.val u.1 < 2* n := by exact Nat.lt_of_le_sub_one h7 h5
have h9 : (2 * ↑u.2 + ↑u.1) % (2 * n) = 2 * ↑u.2 + ↑u.1 :=by exact Nat.mod_eq_of_lt h8
have h10 :   (Fin.val u.1 % 2) = Fin.val u.1 :=by exact Nat.mod_eq_of_lt h1
rw[h9,h10]
rw[Nat.add_div Nat.zero_lt_two]
have h11 : 2 * Fin.val u.2 % 2 = 0 :=by exact Nat.mul_mod_right 2 ↑u.2
rw[h11,zero_add]
have h12 : 2 > Fin.val u.1 % 2:= by exact Nat.mod_lt_of_lt h1
have h13 : ¬(2 ≤ Fin.val u.1 % 2):= by exact Nat.not_le_of_lt h12
rw [Nat.mul_div_cancel_left (↑u.2) (Nat.le.step Nat.le.refl)]
rw [Nat.div_eq_of_lt h1]
rw[Nat.add_zero]
rw[ite_cond_eq_false]
· rw[Nat.add_zero]
  simp
exact eq_false h13
--With this in hand it is enough to show that crossedges is injective to show that
--we indeed have a permutation
theorem crossedges_injective {n : ℕ} [NeZero n]
(M : PerfectMatching (Fin (2 * n))) : Function.Injective (crossedges n M) := by
intro a b h
have hbasea : a.2 < n :=by exact a.2.isLt
have hbaseb : b.2 < n := by exact b.2.isLt
have hbasehelp := sortedEdges_length n M
have conca : ↑a.2 < M.edges.sort.length :=by
  exact Nat.lt_of_lt_of_eq hbasea (id (Eq.symm hbasehelp))
have concb : ↑b.2 < M.edges.sort.length :=by
  exact Nat.lt_of_lt_of_eq hbaseb (id (Eq.symm hbasehelp))
have helperae: (M.edges.sort)[↑a.2] ∈ M.edges := by
  have helperae2 : (M.edges.sort)[↑a.2]∈ (M.edges.sort) :=by exact List.mem_of_getElem rfl
  exact (mem_sort fun a b ↦ a ≤ b).mp helperae2
have helperaedup:=helperae
have helperbe: (M.edges.sort)[↑b.2] ∈ M.edges := by
  have helperbe2 : (M.edges.sort)[↑b.2]∈ (M.edges.sort) :=by exact List.mem_of_getElem rfl
  exact (mem_sort fun a b ↦ a ≤ b).mp helperbe2
have helper2:= M.disjoint (M.edges.sort)[↑a.2]
apply helper2 at helperae
apply helperae at helperbe
rw[crossedges] at h
rw[crossedges] at h
by_cases h1 :a.1 =0
· by_cases h11 :b.1 =0
  · have h111 : a.1 = b.1 :=by rw[h1, h11]
    rw[h1,h11] at h
    simp only [Fin.isValue, ↓reduceDIte, Fin.getElem_fin] at h
    have helper : (M.edges.sort)[↑a.2] = (M.edges.sort)[↑b.2] :=by
      by_contra helper4
      apply helperbe at helper4
      have h5:=helper4.left
      contradiction
    refine Eq.symm (Prod.ext (id (Eq.symm h111)) ?_)
    have almostthere:= sortedEdges_injone ↑a.2 ↑b.2 n M conca concb helper
    exact Fin.eq_of_val_eq (id (Eq.symm almostthere))
  · have h12 : b.1 =1 :=by exact Fin.eq_one_of_ne_zero b.1 h11
    have h112 : a.1≠ b.1 := by exact ne_of_eq_of_ne h1 fun a ↦ h11 (id (Eq.symm a))
    rw[h1,h12] at h
    simp only [Fin.isValue, ↓reduceDIte, Fin.getElem_fin, one_ne_zero] at h
    have helper : (M.edges.sort)[↑a.2] = (M.edges.sort)[↑b.2] :=by
      by_contra helper4
      apply helperbe at helper4
      have h5:=helper4.right.right.left
      contradiction
    have almostthere:= sortedEdges_injone ↑a.2 ↑b.2 n M conca concb helper
    simp[← almostthere] at h
    have contrahelp := M.ordered (M.edges.sort)[↑a.2]
    apply contrahelp at helperaedup
    have contrahelptwo : (M.edges.sort fun a b ↦ a ≤ b)[a.2].1 ≠
    (M.edges.sort fun a b ↦ a ≤ b)[a.2].2:= by exact Fin.ne_of_lt helperaedup
    contradiction
· have h2 : a.1 = 1 := by exact Fin.eq_one_of_ne_zero a.1 h1
  by_cases h21 : b.1 =0
  · have h212 : a.1≠ b.1 := by exact Ne.symm (ne_of_eq_of_ne h21 fun a_1 ↦ h1 (id (Eq.symm a_1)))
    rw[h2,h21] at h
    simp only [Fin.isValue, ↓reduceDIte, Fin.getElem_fin, one_ne_zero] at h
    have helper : (M.edges.sort)[↑a.2] = (M.edges.sort)[↑b.2] :=by
      by_contra helper4
      apply helperbe at helper4
      have h5:=helper4.right.right.right
      contradiction
    have almostthere:= sortedEdges_injone ↑a.2 ↑b.2 n M conca concb helper
    simp[← almostthere] at h
    have contrahelp := M.ordered (M.edges.sort)[↑a.2]
    apply contrahelp at helperaedup
    have contrahelptwo : (M.edges.sort fun a b ↦ a ≤ b)[a.2].2 ≠
    (M.edges.sort fun a b ↦ a ≤ b)[a.2].1:= by exact Ne.symm (Fin.ne_of_lt helperaedup)
    contradiction
  · have h22 :b.1 =1 := Fin.eq_one_of_ne_zero b.1 h21
    rw[h2,h22] at h
    have h222 : a.1 = b.1 :=by rw[h2, h22]
    simp only [Fin.isValue, ↓reduceDIte, Fin.getElem_fin, one_ne_zero] at h
    have helper : (M.edges.sort)[↑a.2] = (M.edges.sort)[↑b.2] :=by
      by_contra helper4
      apply helperbe at helper4
      have h5:=helper4.right.left
      contradiction
    refine Eq.symm (Prod.ext (id (Eq.symm h222)) ?_)
    have almostthere:= sortedEdges_injone ↑a.2 ↑b.2 n M conca concb helper
    exact Fin.eq_of_val_eq (id (Eq.symm almostthere))



theorem perm_of_matching_injective (n : ℕ) [NeZero n] (M : PerfectMatching (Fin (2 * n))) :
Function.Injective (perm_of_matching n M) :=
by
intro a b h
rw[perm_of_matching] at h
rw[perm_of_matching] at h
apply crossedges_injective at h
have h2: fineveniso (evenfiniso n a) = fineveniso (evenfiniso n b) :=by
  exact Fin.eq_of_val_eq (congrArg Fin.val (congrArg fineveniso h))
rw[fineveniso_inverse] at h2
rw[fineveniso_inverse] at h2
exact h2

theorem perm_of_matching_bijective {n : ℕ} [NeZero n] (M : PerfectMatching (Fin (2 * n))) :
Function.Bijective (perm_of_matching n M) := by
refine Finite.injective_iff_bijective.mp ?_
exact perm_of_matching_injective n M

theorem perm_of_matching_surjective {n : ℕ} [NeZero n] (M : PerfectMatching (Fin (2 * n))) :
Function.Surjective (perm_of_matching n M) := by
exact Bijective.surjective (perm_of_matching_bijective M)

--We can now finally construct our permutation
noncomputable def toPerm {n : ℕ} [NeZero n]
  (M : PerfectMatching (Fin (2 * n))) :
  Equiv.Perm (Fin (2*n)) :=
by
  classical
  refine
  { toFun := ?f
    invFun := ?g
    left_inv := ?linv
    right_inv := ?rinv }
  ------------------------------------------------------------
  -- forward map
  ------------------------------------------------------------
  · exact perm_of_matching n M
  ------------------------------------------------------------
  --inverse map
  ------------------------------------------------------------
  · exact Function.invFun (perm_of_matching n M)

  · exact leftInverse_invFun (perm_of_matching_injective n M)
  · exact rightInverse_invFun (Bijective.surjective (perm_of_matching_bijective M))
--we define the sign of our matching to be the sign of the associated permutation
noncomputable def signMatching {n : ℕ} [NeZero n]
  (M : PerfectMatching (Fin (2 * n))) : ℤˣ := Equiv.Perm.sign (toPerm M)

--We can now almost define the Pfaffian, but we need to convince ourselves our sums are finite
def toedges (n : ℕ) [NeZero n] (M : PerfectMatching (Fin (2 * n))) :
  Finset (Lex (Fin (2 * n) × Fin (2 * n))) := M.edges

lemma toedges_injective (n : ℕ) [NeZero n] : Injective (toedges n) := by
intro M N h
rw[toedges] at h
rw[toedges] at h
cases M
cases N
cases h
rfl

noncomputable def fintypematching
(n : ℕ) [NeZero n] : Fintype ((PerfectMatching (Fin (2 * n)))) :=by
have h := toedges_injective n
exact Fintype.ofInjective (toedges n) h

--Here finally is our definition of the pfaffian.
noncomputable def Pf
{R : Type v} {n : ℕ} [NeZero n] [CommRing R] (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R):R := by
have h := fintypematching n
exact ∑ M: (PerfectMatching (Fin (2 * n))), signMatching M * ∏ i ∈ M.edges, A (i.1) (i.2)

--We show a couple of simple properties.
lemma matching_card (n : ℕ) [NeZero n] (M : PerfectMatching (Fin (2 * n))) :
   M.edges.card = n := by
have h1 : 2*M.edges.card =2*n := by
  have h2 : 2*M.edges.card = Fintype.card (Fin (2*n)) := by
    exact Eq.symm (PerfectMatching.card_eq_twice_card_edges M)
  rw[h2]
  exact Fintype.card_fin (2 * n)
apply Nat.mul_left_cancel at h1
· exact h1
exact Nat.zero_lt_two

theorem Pf_mul {R : Type v} {n : ℕ} [NeZero n] [CommRing R] (a : R)
(A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) : Pf (a • A) = a^n * Pf A := by
rw[Pf]
simp only [smul_apply, smul_eq_mul, ← pow_card_mul_prod,matching_card]
rw[Pf]
simp only [mul_sum,← mul_assoc, mul_comm]

theorem Pf_trans {R : Type v} {n : ℕ} [NeZero n] [CommRing R]
(A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) (h : IsSkewSymm A) : Pf Aᵀ = (-1)^n * Pf A :=
by
rw[IsSkewSymm] at h
rw[← neg_inj] at h
rw[neg_neg] at h
rw[h]
have h2:= Pf_mul (-1) A
rw[neg_one_smul] at h2
exact h2
--We now begin our long journey to proving (Pf A)^2 =det A.
--We begin by partitioning permutations into two kinds.
theorem sign_two_values {α : Type u_2} [Fintype α] [LinearOrder α]
(f : Perm α) (h : sign f ≠ -1) : sign f =1 := by
have h2 : sign f = 1 ∨ sign f= -1 := by exact Int.units_eq_one_or (sign f)
exact Or.resolve_right h2 h

def even_perm {α : Type u_2} [Fintype α] [LinearOrder α] (f : Perm α) : Prop :=
∀σ ∈ f.cycleFactorsFinset, sign σ = -1

noncomputable instance even_perm_decidable {α : Type u_2} [Fintype α] [LinearOrder α]
 (f : Perm α) :Decidable (even_perm f):= by
exact Classical.propDecidable (even_perm f)

def odd_perm {α : Type u_2} [Fintype α] [LinearOrder α] (f : Perm α) : Prop :=
∃σ ∈ f.cycleFactorsFinset, sign σ = 1

noncomputable instance odd_perm_decidable {α : Type u_2} [Fintype α] [LinearOrder α]
 (f : Perm α) :Decidable (odd_perm f):= by
exact Classical.propDecidable (odd_perm f)

theorem odd_or_even {α : Type u_2} [Fintype α] [LinearOrder α] (f : Perm α) :
even_perm f ∨ odd_perm f :=
by
by_cases! h : even_perm f
· exact Or.symm (Or.inr h)
rw[even_perm] at h
push_neg at h
have h2 : ∃ σ ∈ f.cycleFactorsFinset, sign σ = 1 := by
  obtain ⟨x, (h3)⟩ := h
  obtain ⟨h4, h5⟩ := h3
  apply sign_two_values x at h5
  exact Filter.frequently_principal.mp fun a ↦ a h4 h5
exact Or.inr h2

theorem odd_of_not_even {α : Type u_2} [Fintype α] [LinearOrder α] (f : Perm α) : ¬(even_perm f) ↔ odd_perm f := by
rw[even_perm]
rw[odd_perm]
push_neg
by_cases h : ¬even_perm f
sorry
sorry
--The determinant may be split into two sums over the odds and the evens
theorem det_eq_sum_odd_even
{R : Type v} {n : ℕ} [NeZero n] [CommRing R] (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) :
det A = ∑ σ : Perm (Fin (2 * n)) with even_perm σ, Equiv.Perm.sign σ • ∏ i, A (σ i) i +
∑ σ : Perm (Fin (2 * n)) with odd_perm σ, Equiv.Perm.sign σ • ∏ i, A (σ i) i  := by
have h :det A = ∑ σ : Perm (Fin (2 * n)) with even_perm σ, Equiv.Perm.sign σ • ∏ i, A (σ i) i
 + ∑ σ : Perm (Fin (2 * n)) with ¬ even_perm σ, Equiv.Perm.sign σ • ∏ i, A (σ i) i :=
  by
  rw[det_apply]
  exact Eq.symm (sum_filter_add_sum_filter_not univ even_perm fun x ↦ sign x • ∏ i, A (x i) i)
rw[h]
rw [add_right_inj]
sorry
--We now aim to show that the odd permutations sum to zero by explicitly showing which terms cancel
--To any odd permuation we associate another with which it will cancel.
theorem nat_of_odd_perm {n : ℕ} [NeZero n](f : Perm (Fin (2 * n))) (h : odd_perm f) :
∃m : ℕ,  sign (f.cycleOf (Fin.ofNat (2*n) m)) =1 := by
rw[odd_perm] at h
obtain ⟨x, (h1)⟩ := h
obtain ⟨h2, (h3)⟩ := h1
have ha : ∃a:Fin (2 * n), a∈ x.support := by
  refine nonempty_def.mp ?_
  refine IsCycle.nonempty_support ?_
  have help := mem_cycleFactorsFinset_iff.mp h2
  obtain ⟨help1, help2⟩ := help
  exact help1
obtain ⟨a, (h4)⟩ := ha
have h4 := cycle_is_cycleOf h4 h2
use a
simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
rw[← h4]
rw[h3]
def small_nat_of_odd_perm {n : ℕ} [NeZero n]
(f : Perm (Fin (2 * n))) (h : odd_perm f) :ℕ :=by
have h2:=nat_of_odd_perm f h
exact Nat.find (h2)
def perm_of_odd_perm {n : ℕ} [NeZero n]
(f : Perm (Fin (2 * n))) (h : odd_perm f) : Perm (Fin (2 * n)):=
by
have m:= small_nat_of_odd_perm f h
exact (f.cycleOf (Fin.ofNat (2*n) (m)))⁻¹*(f.cycleOf (Fin.ofNat (2*n) (m)))⁻¹*f
theorem hardtoname {n : ℕ} [NeZero n] (f : Perm (Fin (2 * n))) (h : odd_perm f) :
 (perm_of_odd_perm f h).cycleOf  (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)) =
  (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)))⁻¹ :=by
rw[perm_of_odd_perm]
simp
sorry

theorem perm_of_odd_perm_odd {n : ℕ} [NeZero n] (f : Perm (Fin (2 * n))) (h : odd_perm f):
odd_perm (perm_of_odd_perm f h) := by
rw[odd_perm]
rw[perm_of_odd_perm]
use f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h))
simp
constructor
sorry
sorry


theorem inv_perm_of_odd_perm {n : ℕ}  [NeZero n](f : Perm (Fin (2 * n))) (h : odd_perm f)
: perm_of_odd_perm (perm_of_odd_perm f h) (perm_of_odd_perm_odd f h) = f := by
rw[perm_of_odd_perm]
sorry
--The preceeding work culminates here in showing that the odd permutations
--do not contribute to the determinant
theorem odd_sum_eq_zero {R : Type v} {n : ℕ} [NeZero n] [CommRing R]
 (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) (h:A.IsSkewSymm) :
∑ σ : Perm (Fin (2 * n)) with odd_perm σ, Equiv.Perm.sign σ • ∏ i, A (σ i) i = 0 :=by sorry



--We now aim to associate an even permutation to every pair of matchings
--We construct this permutation by constructing disjoint cycles that multiply to it.
--We construct these cycles from a list which we construct iteratively.
def list_of_pair_matching_it
{n : ℕ} (M N : (PerfectMatching (Fin (2 * n)))) (Lx : List (Fin (2 * n)) × Fin (2 * n))
: List (Fin (2 * n))×Fin (2*n):=
by
have u:= PerfectMatching.partner N Lx.2
have v:= PerfectMatching.partner M u
exact if (u ∉ Lx.1 ∧ v ∉ Lx.1) then (Lx.1 ++ [u,v],v)  else (Lx.1, v)

def list_of_pair_matching_it_many
 {n : ℕ} (m : ℕ) [NeZero n] (M N : (PerfectMatching (Fin (2 * n)))) (x : Fin (2 * n))
 : List (Fin (2 * n)) := by
have lstart:= [x,PerfectMatching.partner M x]
exact ((list_of_pair_matching_it M N) ^[m] (lstart,x)).1


def list_of_pair_matching
  {n : ℕ} [NeZero n] (M N : (PerfectMatching (Fin (2 * n)))) (x : Fin (2 * n)) :
  List (Fin (2 * n)) :=
list_of_pair_matching_it_many n M N x
--We show this list has no duplicates iteratively
lemma list_of_pair_matching_it_nodup_of_nodup
  {n : ℕ} (M N : (PerfectMatching (Fin (2 * n))))
  (Lx : List (Fin (2 * n)) × Fin (2 * n)) (hl : List.Nodup Lx.1) :
  List.Nodup (list_of_pair_matching_it M N Lx).1 :=
by
rw[list_of_pair_matching_it]
by_cases h : (PerfectMatching.partner N Lx.2∉ Lx.1 ∧
 PerfectMatching.partner M (PerfectMatching.partner N Lx.2) ∉ Lx.1)
· simp only [h, not_false_eq_true, and_self, ↓reduceIte]
  obtain ⟨hleft,hright⟩ :=h
  have h2: PerfectMatching.partner M (PerfectMatching.partner N Lx.2)
    ≠ PerfectMatching.partner N Lx.2 :=
    by exact partner_not_eq M (N.partner Lx.2)
  have h2 : List.Nodup [N.partner Lx.2, M.partner (N.partner Lx.2)] :=
    by
    refine List.nodup_iff_pairwise_ne.mpr ?_
    exact List.pairwise_pair.mpr (id (Ne.symm h2))
  refine List.nodup_append'.mpr ?_
  constructor
  · exact hl
  constructor
  · exact h2
  refine List.disjoint_cons_right.mpr ?_
  constructor
  · exact Not.imp hleft fun a ↦ a
  refine List.disjoint_singleton.mpr ?_
  exact hright
· simp only [h, ↓reduceIte]
  exact hl

lemma list_of_pair_matching_it_many_nodup
 {n : ℕ} (m : ℕ) [NeZero n] (M N : (PerfectMatching (Fin (2 * n)))) (x : Fin (2 * n))
 : List.Nodup (list_of_pair_matching_it_many m M N x) :=by
rw[list_of_pair_matching_it_many]
induction' m with d hd
· simp only [iterate_zero, id_eq, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
  not_false_eq_true, List.nodup_nil, and_self, and_true]
  refine Ne.symm ?_
  exact partner_not_eq M x
have h:= list_of_pair_matching_it_nodup_of_nodup M N
  ((list_of_pair_matching_it M N)^[d] ([x, M.partner x], x)) hd
nth_rewrite 1[← iterate_one (list_of_pair_matching_it M N)] at h
rw[add_comm]
rw[iterate_add]
exact h

theorem list_of_pair_matching_nodup
  {n : ℕ} [NeZero n] (M N : (PerfectMatching (Fin (2 * n)))) (x : Fin (2 * n)) :
  List.Nodup (list_of_pair_matching M N x) :=by
exact list_of_pair_matching_it_many_nodup n M N x
--We show that the list is not trivial iteratively
lemma length_le_list_of_pair_matching_it
{n : ℕ} (M N : (PerfectMatching (Fin (2 * n)))) (Lx : List (Fin (2 * n)) × Fin (2 * n)) :
(Lx.1).length≤ ((list_of_pair_matching_it M N Lx).1).length := by
rw[list_of_pair_matching_it]
by_cases h : (PerfectMatching.partner N Lx.2∉ Lx.1 ∧
   PerfectMatching.partner M (PerfectMatching.partner N Lx.2) ∉ Lx.1)
· simp only [h, not_false_eq_true, and_self, ↓reduceIte]
  obtain ⟨hleft,hright⟩ :=h
  refine List.Sublist.length_le ?_
  exact List.sublist_append_left Lx.1 [N.partner Lx.2, M.partner (N.partner Lx.2)]
· simp only [h, ↓reduceIte, le_refl]

lemma two_le_list_of_pair_matching_it_many_length
  {n : ℕ} (m : ℕ) [NeZero n] (M N : (PerfectMatching (Fin (2 * n)))) (x : Fin (2 * n)) :
  2≤ (list_of_pair_matching_it_many m M N x ).length := by
rw[list_of_pair_matching_it_many]
induction' m with d hd
· simp only [iterate_zero, id_eq, List.length_cons,
  List.length_nil, zero_add, Nat.reduceAdd, le_refl]
have h:= length_le_list_of_pair_matching_it M N
      ((list_of_pair_matching_it M N)^[d] ([x, M.partner x], x))
nth_rewrite 1[← iterate_one (list_of_pair_matching_it M N)] at h
rw[add_comm]
rw[iterate_add]
exact Nat.le_trans hd h

theorem two_le_list_of_pair_matching
  {n : ℕ} [NeZero n] (M N : (PerfectMatching (Fin (2 * n)))) (x : Fin (2 * n)) :
  2≤ (list_of_pair_matching M N x).length :=by
exact two_le_list_of_pair_matching_it_many_length n M N x
--We also show it has an even number of elements iteratively
lemma even_list_of_pair_matching_it_of_even
  {n : ℕ} (M N : (PerfectMatching (Fin (2 * n)))) (Lx : List (Fin (2 * n)) × Fin (2 * n))
  (hl : 2 ∣ ((Lx.1).length)) :
  2∣  ((list_of_pair_matching_it M N Lx).1).length := by
rw[list_of_pair_matching_it]
by_cases h : (PerfectMatching.partner N Lx.2∉ Lx.1 ∧
 PerfectMatching.partner M (PerfectMatching.partner N Lx.2) ∉ Lx.1)
· simp only [h, not_false_eq_true, and_self, ↓reduceIte]
  obtain ⟨hleft,hright⟩ :=h
  have h2: (Lx.1 ++ [N.partner Lx.2, M.partner (N.partner Lx.2)]).length =
    Lx.1.length +([N.partner Lx.2, M.partner (N.partner Lx.2)]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
  rw[h2]
  exact Nat.dvd_add_self_right.mpr hl
· simp only [h, ↓reduceIte]
  exact hl
lemma even_list_of_pair_matching_it_many
  {n : ℕ} (m : ℕ) [NeZero n] (M N : (PerfectMatching (Fin (2 * n)))) (x : Fin (2 * n)) :
  2∣  (list_of_pair_matching_it_many m M N x ).length :=
by
rw[list_of_pair_matching_it_many]
induction' m with d hd
· simp only [iterate_zero, id_eq, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
  dvd_refl]
have h:= even_list_of_pair_matching_it_of_even M N
  ((list_of_pair_matching_it M N)^[d] ([x, M.partner x], x))
rw[add_comm]
rw[iterate_add]
exact
  (Nat.ModEq.dvd_iff
        (congrFun rfl ((list_of_pair_matching_it M N)^[d] ([x, M.partner x], x)).1.length) hd).mp
    (h hd)
theorem even_list_of_pair_matching {n : ℕ} [NeZero n] (M N : PerfectMatching (Fin (2 * n)))
 (x : Fin (2 * n)) : 2∣  (list_of_pair_matching M N x ).length :=
by exact even_list_of_pair_matching_it_many n M N x

--We define the cycle from our list
def cycle_of_pair_matching {n : ℕ} [NeZero n] (M N : PerfectMatching (Fin (2 * n)))
 (x : Fin (2 * n)):Perm (Fin (2 * n)):=by
have l := list_of_pair_matching M N x
exact List.formPerm l
--We show it is indeed a cycle from the preceeding work
theorem cycle_of_pair_matching_cycle {n : ℕ} [NeZero n] (M N : (PerfectMatching (Fin (2 * n))))
  (x : Fin (2 * n)) : IsCycle (cycle_of_pair_matching M N x) :=
by
have h:= list_of_pair_matching_nodup M N x
have h2 : 2 ≤ (list_of_pair_matching M N x).length:=
  by exact two_le_list_of_pair_matching M N x
rw[cycle_of_pair_matching]
exact List.isCycle_formPerm h h2


--We show that it has negative sign from our evenness theorems
theorem cycle_of_pair_matching_even {n : ℕ} [NeZero n] (M N : PerfectMatching (Fin (2 * n)))
  (x : Fin (2 * n)) : sign (cycle_of_pair_matching M N x) = -1 := by
have h := cycle_of_pair_matching_cycle M N x
have h2 :=even_list_of_pair_matching M N x
sorry
--We now build the full permutation iteratively
def perm_of_pair_matching_it {n : ℕ} [NeZero n] (M N : PerfectMatching (Fin (2 * n)))
 (fm : Perm (Fin (2 * n)) × ℕ) : Perm (Fin (2 * n)) × ℕ :=
by exact (if Fin.ofNat (2*n) (fm.2)∉fm.1.support
 then (fm.1*(cycle_of_pair_matching M N (Fin.ofNat (2*n) (fm.2))),n+1) else (fm.1,n+1))

def perm_of_pair_matching_it_many {n : ℕ} (m : ℕ) [NeZero n] (M N : PerfectMatching (Fin (2 * n)))
 :  Perm (Fin (2 * n)) := by
exact ((perm_of_pair_matching_it M N) ^[m] (1,1)).1

def perm_of_pair_matching
  {n : ℕ} [NeZero n] (M N : (PerfectMatching (Fin (2 * n)))) : Perm (Fin (2*n)) := by
exact perm_of_pair_matching_it_many n M N
--We show that this permutation is even iteratively.
theorem even_perm_perm_of_pair_matching_it_of_even {n : ℕ} [NeZero n]
 (M N : (PerfectMatching (Fin (2 * n)))) (fm : Perm (Fin (2 * n)) × ℕ) (hfm : even_perm fm.1) :
  even_perm ((perm_of_pair_matching_it M N fm).1) :=
by
rw[perm_of_pair_matching_it]
by_cases h: Fin.ofNat (2 * n) fm.2 ∉ fm.1.support
· have h2: (if Fin.ofNat (2 * n) fm.2 ∉ fm.1.support
  then (fm.1 * cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2), n + 1)
  else (fm.1, n + 1)) = (fm.1 * cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2), n + 1):=
    by exact if_pos h
  rw[h2]
  simp only [Fin.ofNat_eq_cast]
  rw[even_perm]
  intro σ hσ
  rw[even_perm] at hfm
  have h3 :σ ∈ (fm.1).cycleFactorsFinset
  ∨ σ ∈ (cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2)).cycleFactorsFinset :=
    by sorry
  by_cases h4: σ ∈ (fm.1).cycleFactorsFinset
  · exact Units.val_inj.mp (congrArg Units.val (hfm σ h4))
  have h5 :σ ∈ (cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2)).cycleFactorsFinset :=by
    exact Or.resolve_left h3 h4
  have h6 : σ = (cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2)) :=by
    have h6help : (cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2)).cycleFactorsFinset
    = { cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2)} := by
      refine cycleFactorsFinset_eq_singleton_self_iff.mpr ?_
      exact cycle_of_pair_matching_cycle M N (Fin.ofNat (2 * n) fm.2)
    exact (eq_singleton_iff_unique_mem.mp (h6help)).right σ h5
  rw[h6]
  exact cycle_of_pair_matching_even M N (Fin.ofNat (2 * n) fm.2)
· have h7: (if Fin.ofNat (2 * n) fm.2 ∉ fm.1.support
  then (fm.1 * cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2), n + 1)
  else (fm.1, n + 1)) = (fm.1, n + 1) :=
    by exact if_neg h
  rw[h7]
  exact hfm
theorem even_perm_of_pair_matching {n : ℕ} [NeZero n] (M N : PerfectMatching (Fin (2 * n)))
: even_perm (perm_of_pair_matching M N) :=
by sorry
--We now start build a pair of matchings from a given even permutation.
theorem pair_matching_of_even_perm {n : ℕ} [NeZero n] (σ : Perm (Fin (2 * n))) (hσ : even_perm σ) :
∃M :PerfectMatching (Fin (2 * n)),∃N :PerfectMatching (Fin (2 * n)), σ = perm_of_pair_matching M N := by sorry
--After this we show that signs and products are preserved under our bijection.
theorem det_eq_Pf_square {R : Type v} {n : ℕ} [NeZero n] [CommRing R]
(A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) (h : IsSkewSymm A) : (Pf A)*(Pf A) = det A := by
rw[Pf]
rw[det_eq_sum_odd_even]
rw[odd_sum_eq_zero,add_zero]
sorry
sorry
def equivtest {n : ℕ} [NeZero n] :Equiv (Fin (2*n)) (Fin 2 × Fin n) :=
by
  classical
  refine
  { toFun := ?f
    invFun := ?g
    left_inv := ?linv
    right_inv := ?rinv }
  · exact evenfiniso n
  · exact fineveniso
  · exact fineveniso_inverse
  · exact evenfiniso_inverse
