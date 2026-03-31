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

theorem IsSkewSymm.eq [Neg α] {A : Matrix n n α} (h : A.IsSkewSymm) : -Aᵀ = A := h
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
/-- The diagonal of a skew-symmetric matrix is all 0 -/
lemma diag_eq_zero_of_SkewSymm [CommRing α] [NoZeroDivisors α]
  (A : Matrix n n α) (h0 : ¬(1:α) + (1:α) = 0) (h : A.IsSkewSymm) :
    A i i = 0 := by
    apply IsSkewSymm.apply at h
    have hA : A i i = - (A i i) := by exact neg_eq_iff_eq_neg.mp (h i i)
    apply eq_neg_iff_add_eq_zero.mp at hA
    rw[← one_mul (A i i)] at hA
    rw[← RightDistribClass.right_distrib] at hA
    rw[mul_eq_zero] at hA
    apply Or.resolve_left at hA
    exact hA h0
variable {n : ℕ}
/-- The determinant of an odd-dimensional skew-symmetric matrix is 0. -/
theorem det_eq_zero_of_IsSkewSymm_odd_dim [CommRing α] [NoZeroDivisors α]
  (A : Matrix (Fin n) (Fin n) α) (h0 : ¬(1:α) + (1:α) = 0) (h1 : A.IsSkewSymm)
  (h2 : Odd n) : A.det =0:=
    by
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


def det_prod {R : Type v} [CommRing R] {n : ℕ} [NeZero n]
  (σ : Perm (Fin (2 * n))) (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) :R :=
    ∏ i, A (σ i) i

def full_support (σ : Perm (Fin (2 * n))) :Prop := ∀x, x∈σ.support
noncomputable instance (σ : Perm (Fin (2 * n))) : Decidable (full_support σ ) :=
  by exact Classical.propDecidable (full_support σ)

theorem det_prod_eq_zero_of_not_full_support {R : Type v} (n : ℕ)
  [NeZero n] [CommRing R] [NoZeroDivisors R] [Nontrivial R] (h0 : ¬(1:R) + (1:R) = 0)
  (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) (hA : IsSkewSymm A)
  (σ : Perm (Fin (2 * n))) (hσ : ∃ x, x ∉ σ.support) :
  det_prod σ A = 0 := by
    obtain ⟨x,hx⟩ := hσ
    simp only [Perm.mem_support, ne_eq, Decidable.not_not] at hx
    rw[det_prod]
    have hax : A (σ x) x = 0 :=by
      rw[hx]
      exact diag_eq_zero_of_SkewSymm A h0 hA
    have hprod: ∃ i∈ univ, A (σ i) i =0 :=by
      use x
      constructor
      · exact mem_univ x
      exact hax
    exact prod_eq_zero_iff.mpr hprod


theorem det_eq_full_support_det {R : Type v} {n : ℕ} [NeZero n]
  [CommRing R] [NoZeroDivisors R] [Nontrivial R]
  (h0 : ¬(1:R) + (1:R) = 0) (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) (hA : IsSkewSymm A)
    : det A =  ∑ σ : Perm (Fin (2*n)) with full_support σ , Equiv.Perm.sign σ • ∏ i, A (σ i) i:=
    by
  have h :det A = ∑ σ : Perm (Fin (2 * n)) with full_support σ, Equiv.Perm.sign σ • ∏ i, A (σ i) i
  + ∑ σ : Perm (Fin (2 * n)) with ¬ full_support σ, Equiv.Perm.sign σ • ∏ i, A (σ i) i :=
    by
    rw[det_apply]
    exact Eq.symm (sum_filter_add_sum_filter_not univ full_support fun x ↦ sign x • ∏ i, A (x i) i)
  rw[h]
  simp only [add_eq_left]
  have hpush_neg : ∑ σ with ¬full_support σ, sign σ • ∏ i, A (σ i) i
    = ∑ σ with ∃ x, x ∉ σ.support, sign σ • ∏ i, A (σ i) i :=
  by simp only [full_support, Perm.mem_support, ne_eq, not_forall, Decidable.not_not]
  rw[hpush_neg]
  have hdetprod :=det_prod_eq_zero_of_not_full_support n h0 A hA
  have hdetprod2 : ∀ (σ : Perm (Fin (2 * n))), (∃ x, x ∉ σ.support) → ∏ i, A (σ i) i  = 0 :=
    by
    intro σ hσ
    exact hdetprod σ hσ
  refine Finset.sum_eq_zero ?_
  intro σ hσ
  simp only [Perm.mem_support, ne_eq, Decidable.not_not, mem_filter, mem_univ, true_and] at hσ
  rw [hdetprod2]
  · rw[smul_zero]
  simp only [Perm.mem_support, ne_eq, Decidable.not_not]
  exact hσ
  ---The following theorems are are due to a LEAN club consisting of
-- George H. Seelinger, Chenchen Zhao, Darij Grinberg. They are fully proven in their work.
-- I have taken their statements as axioms to not turn over the same stones,
--but have not copied their proofs.
structure PerfectMatching (α : Type u) [Fintype α] [DecidableEq α] [LinearOrder α] where
  edges : Finset (α ×ₗ α)
  ordered : ∀ b ∈ edges, b.1 < b.2
  disjoint : ∀ a ∈ edges, ∀ b ∈ edges,
  (a ≠ b)→ (a.1 ≠ b.1  ∧ a.2 ≠ b.2 ∧ a.1 ≠ b.2 ∧ a.2 ≠ b.1)
  union : ∀ (i : α), ∃ b ∈ edges, (i = b.1 ∨ i = b.2)



variable {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α]
def set {α} [Fintype α] [DecidableEq α] (b : α × α) : Finset α :=
  {b.1, b.2}
def pair {α} [Fintype α] [DecidableEq α] [LinearOrder α] (c d : α) : α × α :=
  (min c d, max c d)

-- In a perfect matching, each element of α lies in EXACTLY
-- one block.
axiom PerfectMatching.unique_block (M : PerfectMatching α) :
  ∀ (i : α), ∃! b ∈ M.edges, i ∈ set b


axiom block_card_two
    (M : PerfectMatching α) {b : α × α} (hb : b ∈ M.edges) :
    (set b).card = 2
axiom blocks_cover (M : PerfectMatching α) :
    (M.edges.biUnion set : Finset α) = Finset.univ
--This I have written myself for compatibility between my slightly modified definition
lemma disjoint_edges (M : PerfectMatching α) :
  ∀ a ∈ M.edges, ∀ b ∈ M.edges, a ≠ b →
   Disjoint ({a.1, a.2} : Finset α) ({b.1, b.2} : Finset α):= by
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

axiom card_eq_sum_block_card (M : PerfectMatching α) :
    Fintype.card α = ∑ b ∈ M.edges, (set b).card

axiom PerfectMatching.card_eq_twice_card_edges (M : PerfectMatching α) :
  Fintype.card α = 2 * M.edges.card

axiom PerfectMatching.card_even (M : PerfectMatching α) :
  Even (Fintype.card α)

axiom even_card_of_exists_PerfectMatching
    (h : Nonempty (PerfectMatching α)) :
    Even (Fintype.card α)


def PerfectMatching.block (M : PerfectMatching α) : α → α × α :=
  fun i => Finset.choose (fun (b : α × α) => (i ∈ set b))
                         (M.edges : Finset (α × α)) (PerfectMatching.unique_block M i)


axiom PerfectMatching.block_spec (M : PerfectMatching α) (i : α) :
  (PerfectMatching.block M i ∈ M.edges) ∧ (i ∈ set (PerfectMatching.block M i))

axiom PerfectMatching.block_uni (M : PerfectMatching α) (i : α) (b : α × α)
  (hbe : b ∈ M.edges)
  (hib : i ∈ set b) : b = PerfectMatching.block M i

def first_or_second_if_not (pair : α × α) (i : α) := if pair.1 = i then pair.2 else pair.1

-- The partner of a given element of α in M:
def PerfectMatching.partner (M : PerfectMatching α) : α → α :=
  fun i => first_or_second_if_not (M.block i) i


axiom PerfectMatching.partner_block (M : PerfectMatching α) (i : α) :
    set (M.block i) = {i, M.partner i}

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
  (Fin 2 × Fin n)
    := (Fin.ofNat 2 ((Fin.val u) %2) ,(Fin.ofNat n ((Fin.val u)/2) : Fin n))
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
  (u : Fin (2 * n)) : Fin (2 * n) :=
    crossedges  n M (evenfiniso n u)
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
          by
          have h6help: n = (n-1)+1 := by
                      refine Eq.symm (Nat.sub_add_cancel ?_)
                      exact NeZero.one_le
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

theorem crossedges_injective {n : ℕ} [NeZero n] (M : PerfectMatching (Fin (2 * n))) :
  Function.Injective (crossedges n M) := by
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
      refine
      { toFun := ?f
        invFun := ?g
        left_inv := ?linv
        right_inv := ?rinv }
      · exact perm_of_matching n M
      · exact Function.invFun (perm_of_matching n M)
      · exact leftInverse_invFun (perm_of_matching_injective n M)
      · exact rightInverse_invFun (Bijective.surjective (perm_of_matching_bijective M))
--we define the sign of our matching to be the sign of the associated permutation
noncomputable def signMatching {n : ℕ} [NeZero n]
  (M : PerfectMatching (Fin (2 * n))) : ℤˣ := Equiv.Perm.sign (toPerm M)

--We can now almost define the Pfaffian,
--but we need to convince ourselves the set of Perfect Matchings is finite
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

noncomputable instance fintypematching
(n : ℕ) [NeZero n] : Fintype ((PerfectMatching (Fin (2 * n)))) :=by
  have h := toedges_injective n
  exact Fintype.ofInjective (toedges n) h

--Here finally is our definition of the Pfaffian.
noncomputable def Pf
  {R : Type v} {n : ℕ} [NeZero n] [CommRing R] (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R):R := by
  exact ∑ M: (PerfectMatching (Fin (2 * n))), signMatching M * ∏ i ∈ M.edges, A (i.1) (i.2)

def Pf_prod {R : Type v} {n : ℕ} [NeZero n] [CommRing R]
  (M : PerfectMatching (Fin (2 * n))) (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) :R:=
     ∏ i ∈ M.edges, A (i.1) (i.2)


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
  (f : Perm α) :Decidable (odd_perm f):=
  by
    exact Classical.propDecidable (odd_perm f)

abbrev Odd_Perm (α : Type u_2) [Fintype α] [LinearOrder α] := { x : Perm (α) | odd_perm x }


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
theorem odd_of_not_even {α : Type u_2} [Fintype α] [LinearOrder α] (f : Perm α) :
  ¬(even_perm f) ↔ odd_perm f := by
    constructor
    · intro h
      rcases odd_or_even f with h_even | h_odd
      · exact False.elim (h h_even)
      · exact h_odd
    · intro h_odd h_even
      rcases h_odd with ⟨σ, hσ, hs⟩
      have hs' : sign σ = -1 := h_even σ hσ
      have : (1 : ℤˣ) = -1 := hs.symm.trans hs'
      norm_num at this

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
  simp only [odd_of_not_even]

theorem odd_sum_eq_Odd_sum {R : Type v} {n : ℕ} [NeZero n] [CommRing R]
  (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) :
  ∑ σ : Perm (Fin (2 * n)) with odd_perm σ, Equiv.Perm.sign σ • ∏ i, A (σ i) i
  = ∑ τ : (Odd_Perm (Fin (2 * n))), Equiv.Perm.sign τ.val • ∏ i, A (τ.val i) i :=
  by
    refine sum_subtype {σ | odd_perm σ} ?_ fun a ↦ sign a • ∏ i, A (a i) i
    intro σ
    exact mem_filter_univ σ
--We now aim to show that the odd permutations sum to zero by explicitly showing which terms cancel
--To any odd permuation we associate another with which it will cancel.
theorem nat_of_odd_perm {n : ℕ} [NeZero n] (f : Perm (Fin (2 * n))) (h : odd_perm f) :
  ∃m : ℕ, (f.cycleOf (Fin.ofNat (2*n) m))∈f.cycleFactorsFinset
  ∧ sign (f.cycleOf (Fin.ofNat (2*n) m)) =1 :=
  by
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
    have h5 := cycle_is_cycleOf h4 h2
    use a
    constructor
    · refine cycleOf_mem_cycleFactorsFinset_iff.mpr ?_
      refine mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mpr ?_
      use x
      constructor
      · exact mem_def.mpr h2
      · simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self, h4]
    simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
    rw[← h5]
    rw[h3]

def small_nat_of_odd_perm {n : ℕ} [NeZero n]
  (f : Perm (Fin (2 * n))) (h : odd_perm f) :ℕ :=
  by
    have h2:=nat_of_odd_perm f h
    exact Nat.find (h2)

def perm_of_odd_perm {n : ℕ} [NeZero n]
  (f : Perm (Fin (2 * n))) (h : odd_perm f) : Perm (Fin (2 * n)):=
  by
    have m:= small_nat_of_odd_perm f h
    exact f*(f.cycleOf (Fin.ofNat (2*n) (m)))⁻¹*(f.cycleOf (Fin.ofNat (2*n) (m)))⁻¹

theorem commutecycles {n : ℕ} [NeZero n] (f : Perm (Fin (2 * n))) (h : odd_perm f) :
  Commute (f * (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h)))⁻¹)
  (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h)))⁻¹ :=
  by
    have h2 : (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))) ∈ f.cycleFactorsFinset :=
      by
      refine cycleOf_mem_cycleFactorsFinset_iff.mpr ?_
      rw[small_nat_of_odd_perm]
      have hspec:= (Nat.find_spec (nat_of_odd_perm f h)).left
      exact cycleOf_mem_cycleFactorsFinset_iff.mp hspec
    have h1 : (f*(f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)))⁻¹).cycleFactorsFinset
    = f.cycleFactorsFinset\{f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h))}:=
      by exact cycleFactorsFinset_mul_inv_mem_eq_sdiff h2
    have hdis :=disjoint_mul_inv_of_mem_cycleFactorsFinset h2
    have hdisinv : Disjoint (f * (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)))⁻¹)
      (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)))⁻¹ :=
      by exact disjoint_inv_right_iff.mpr hdis
    exact Disjoint.commute hdisinv

theorem perm_of_odd_perm_nonsupport {n : ℕ} [NeZero n] (f : Perm (Fin (2 * n))) (h : odd_perm f)
(m : Fin (2 * n)) (hm : m ∉ (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support) :
  f m= (perm_of_odd_perm f h) (m) :=
  by
    rw[perm_of_odd_perm]
    rw[mul_apply,mul_apply]
    have hm2: m∉ (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)))⁻¹.support :=by
      refine Perm.notMem_support.mpr ?_
      refine inv_eq_iff_eq.mpr ?_
      have hm' := notMem_support.mp hm
      exact hm'.symm
    have hm2' := notMem_support.mp hm2
    rw[hm2']
    rw[hm2']

axiom perm_of_odd_perm_support {n : ℕ} [NeZero n] (f : Perm (Fin (2 * n))) (h : odd_perm f)
  (m : Fin (2 * n)) (hm : m ∈ (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support) :
  f⁻¹ m= (perm_of_odd_perm f h) (m)

--An almost complete proof of this fact is in the following comment.
--I kept getting timeouts at hfhelp2

/-theorem perm_of_odd_perm_support {n : ℕ} [NeZero n] (f : Perm (Fin (2 * n))) (h : odd_perm f)
  (m : Fin (2 * n)) (hm: m ∈ (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h))).support) :
  f⁻¹ m= (perm_of_odd_perm f h) (m) :=
  by
    rw[perm_of_odd_perm]
    have hf : f m = f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)) m := by
      have hfhelp := (mem_support_cycleOf_iff.mp hm).left
      exact Eq.symm (SameCycle.cycleOf_apply hfhelp)
    have hm2: m∈  (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)))⁻¹.support :=by
      rw[Perm.support_inv]
      exact hm
    rw[cycleOf_inv] at hm2
    let g:Perm (Fin (2*n)):=f⁻¹
    have hm3 : m ∈ (g.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support:= hm2
    have hfinv : g m = (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)))⁻¹ m :=by
      rw[cycleOf_inv]
      have hfhelp2 := (mem_support_cycleOf_iff.mp hm3).left
      exact Eq.symm (SameCycle.cycleOf_apply hfhelp)
    rw[mul_apply]
    rw[mul_apply]
    rw[← hf]
    rw[commutecycles]
    simp only [Perm.coe_mul, Function.comp_apply,
      EmbeddingLike.apply_eq_iff_eq]
    rw[← hfinv]
    simp only [Perm.coe_inv, apply_symm_apply]
-/
theorem cycle_factors_of_perm_of_odd_perm {n : ℕ} [NeZero n]
  (f : Perm (Fin (2 * n))) (h : odd_perm f) :
  (perm_of_odd_perm f h).cycleFactorsFinset =
  f.cycleFactorsFinset\{f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h))}
  ∪{(f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)))⁻¹}:=
  by
    have h1 : (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))) ∈ f.cycleFactorsFinset :=
      by
        refine cycleOf_mem_cycleFactorsFinset_iff.mpr ?_
        rw[small_nat_of_odd_perm]
        have hspec:= (Nat.find_spec (nat_of_odd_perm f h)).left
        exact cycleOf_mem_cycleFactorsFinset_iff.mp hspec
    have h2 : (f*(f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)))⁻¹).cycleFactorsFinset
            = f.cycleFactorsFinset\{f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h))}:=
            by exact cycleFactorsFinset_mul_inv_mem_eq_sdiff h1
    have hdis :=disjoint_mul_inv_of_mem_cycleFactorsFinset h1
    have hdisinv : Disjoint (f * (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)))⁻¹)
                  (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)))⁻¹ :=
                  by exact disjoint_inv_right_iff.mpr hdis
    have hunion:=Disjoint.cycleFactorsFinset_mul_eq_union hdisinv
    rw[perm_of_odd_perm]
    nth_rewrite 3 [IsCycle.cycleFactorsFinset_eq_singleton] at hunion
    · nth_rewrite 2 [cycleFactorsFinset_mul_inv_mem_eq_sdiff] at hunion
      · exact hunion
      exact mem_def.mpr h1
    refine isCycle_inv.mpr ?_
    have hconc : (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h)))
                ∈ f.cycleFactorsFinset := mem_def.mpr h1
    exact (mem_cycleFactorsFinset_iff.mp hconc).left



theorem perm_of_odd_perm_odd {n : ℕ} [NeZero n] (f : Perm (Fin (2 * n))) (h : odd_perm f) :
  odd_perm (perm_of_odd_perm f h) :=
  by
  rw[odd_perm]
  use (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)))⁻¹
  constructor
  · rw[cycle_factors_of_perm_of_odd_perm]
    refine
      mem_union_right
        (f.cycleFactorsFinset \ {f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))}) ?_
    exact mem_singleton.mpr rfl
  rw[small_nat_of_odd_perm]
  rw[sign_inv]
  exact (Nat.find_spec (nat_of_odd_perm f h)).right

def Odd_Perm_of_Odd_Perm {n : ℕ} [NeZero n] (f : Odd_Perm (Fin (2 * n))) :
  Odd_Perm (Fin (2 * n)) :=  by
  use perm_of_odd_perm f.val f.property
  exact perm_of_odd_perm_odd f.val f.property

lemma nat_eq_perm_of_odd_perm {n : ℕ} [NeZero n] (f : Perm (Fin (2 * n))) (h : odd_perm f) :
  small_nat_of_odd_perm (perm_of_odd_perm f h) (perm_of_odd_perm_odd f h)
  = small_nat_of_odd_perm f h :=
   by
    rw[small_nat_of_odd_perm,small_nat_of_odd_perm]
    refine Nat.find_congr' ?_
    intro m
    constructor
    · intro hcon
      constructor
      · refine cycleOf_mem_cycleFactorsFinset_iff.mpr ?_
        have hcon2 := cycleOf_mem_cycleFactorsFinset_iff.mp hcon.left
        refine Perm.mem_support.mpr ?_
        apply Perm.mem_support.mp at hcon2
        by_cases hm: (Fin.ofNat (2*n) m)∈
        (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h))).support
        · rw[← perm_of_odd_perm_support f h (Fin.ofNat (2*n) m) hm] at hcon2
          by_contra
          have help:=inv_eq_iff_eq.mpr (this.symm)
          contradiction
        rw[← perm_of_odd_perm_nonsupport f h (Fin.ofNat (2*n) m) hm] at hcon2
        exact hcon2
      have hconright:= hcon.right
      have hconleft :=hcon.left
      by_cases hm: (Fin.ofNat (2*n) m)∈
        (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h))).support
      · have hetwas : f.cycleOf (Fin.ofNat (2 * n) m) =
          f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)) := by
            refine Eq.symm (cycle_is_cycleOf hm ?_)
            have hspec := (Nat.find_spec (nat_of_odd_perm f h)).left
            rw[small_nat_of_odd_perm]
            exact hspec
        rw[hetwas]
        rw[small_nat_of_odd_perm]
        have hspec := (Nat.find_spec (nat_of_odd_perm f h)).right
        exact hspec
      rw[perm_of_odd_perm] at hconright
      rw[cycleOf_mul_of_apply_right_eq_self] at hconright
      · rw[cycleOf_mul_of_apply_right_eq_self] at hconright
        · exact hconright
        · refine Commute.inv_right ?_
          refine Commute.symm ?_
          refine self_mem_cycle_factors_commute ?_
          rw[small_nat_of_odd_perm]
          have hspec := (Nat.find_spec (nat_of_odd_perm f h)).left
          exact hspec
        simp only [Perm.mem_support, ne_eq, Decidable.not_not] at hm
        rw[inv_eq_iff_eq]
        exact hm.symm
      · exact commutecycles f h
      simp only [Perm.mem_support, ne_eq, Decidable.not_not] at hm
      rw[inv_eq_iff_eq]
      exact hm.symm
    intro hcon
    constructor
    · refine cycleOf_mem_cycleFactorsFinset_iff.mpr ?_
      have hcon2 := cycleOf_mem_cycleFactorsFinset_iff.mp hcon.left
      refine Perm.mem_support.mpr ?_
      apply Perm.mem_support.mp at hcon2
      by_cases hm: (Fin.ofNat (2*n) m)∈
        (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h))).support
      · rw[← perm_of_odd_perm_support f h (Fin.ofNat (2*n) m) hm]
        by_contra
        have help:=(inv_eq_iff_eq.mp (this)).symm
        contradiction
      rw[← perm_of_odd_perm_nonsupport f h (Fin.ofNat (2*n) m) hm]
      exact hcon2
    have hconright:= hcon.right
    have hconleft :=hcon.left
    by_cases hm: (Fin.ofNat (2*n) m)∈
      (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h))).support
    · have hetwas : (perm_of_odd_perm f h).cycleOf (Fin.ofNat (2 * n) m)  =
        (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)))⁻¹ :=
        by
          refine Eq.symm (cycle_is_cycleOf ?_ ?_)
          · rw [Perm.support_inv]
            exact hm
          · rw [cycle_factors_of_perm_of_odd_perm]
            refine mem_union_right
              (f.cycleFactorsFinset \
                        {f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))}) ?_
            exact mem_singleton.mpr rfl
      · rw[hetwas]
        have hspec := (Nat.find_spec (nat_of_odd_perm f h)).right
        rw[small_nat_of_odd_perm]
        rw[sign_inv]
        rw[hspec]
    rw[perm_of_odd_perm]
    rw[cycleOf_mul_of_apply_right_eq_self]
    · rw[cycleOf_mul_of_apply_right_eq_self]
      · exact hconright
      · refine Commute.inv_right ?_
        refine Commute.symm ?_
        refine self_mem_cycle_factors_commute ?_
        rw[small_nat_of_odd_perm]
        have hspec := (Nat.find_spec (nat_of_odd_perm f h)).left
        exact hspec
      simp only [Perm.mem_support, ne_eq, Decidable.not_not] at hm
      rw[inv_eq_iff_eq]
      exact hm.symm
    · exact commutecycles f h
    simp only [Perm.mem_support, ne_eq, Decidable.not_not] at hm
    rw[inv_eq_iff_eq]
    exact hm.symm

lemma inv_perm_of_odd_perm_aux {n : ℕ} [NeZero n] (f : Perm (Fin (2 * n))) (h : odd_perm f) :
 (perm_of_odd_perm f h).cycleOf  (Fin.ofNat (2*n)
 (small_nat_of_odd_perm (perm_of_odd_perm f h) (perm_of_odd_perm_odd f h) )) =
  (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h)))⁻¹ :=by
  rw[nat_eq_perm_of_odd_perm]
  refine Eq.symm (cycle_is_cycleOf ?_ ?_)
  · have hspec := (Nat.find_spec (nat_of_odd_perm f h)).left
    rw[Perm.support_inv]
    exact
      (eq_cycleOf_of_mem_cycleFactorsFinset_iff f
            (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))) hspec
            (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).mp
        rfl
  rw[cycle_factors_of_perm_of_odd_perm]
  refine mem_union_right
      (f.cycleFactorsFinset \ {f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))}) ?_
  exact mem_singleton.mpr rfl

theorem inv_perm_of_odd_perm {n : ℕ} [NeZero n] (f : Perm (Fin (2 * n))) (h : odd_perm f)
: perm_of_odd_perm (perm_of_odd_perm f h) (perm_of_odd_perm_odd f h) = f := by
rw[perm_of_odd_perm]
rw[inv_perm_of_odd_perm_aux]
rw[inv_inv]
rw[perm_of_odd_perm]
rw[inv_mul_cancel_right,inv_mul_cancel_right]

theorem inv_Perm_of_Odd_Perm {n : ℕ} [NeZero n] (f : Odd_Perm (Fin (2 * n))) :
Odd_Perm_of_Odd_Perm (Odd_Perm_of_Odd_Perm f) =f :=
by
rw[Odd_Perm_of_Odd_Perm]
rw[Odd_Perm_of_Odd_Perm]
refine Subtype.ext ?_
exact inv_perm_of_odd_perm f.val f.prop

theorem sign_perm_of_odd_perm_eq_sign_self {n : ℕ} [NeZero n] (f : Perm (Fin (2 * n)))
 (h : odd_perm f) : Equiv.Perm.sign f = Equiv.Perm.sign (perm_of_odd_perm f h) := by
rw[perm_of_odd_perm]
rw[small_nat_of_odd_perm]
rw [Perm.sign_mul,Perm.sign_mul, sign_inv]
have hspec := (Nat.find_spec (nat_of_odd_perm f h)).right
rw[hspec]
rw[mul_one, mul_one]

theorem shift_sign_perm_of_odd_perm {R : Type v} {n : ℕ} [NeZero n] [CommRing R]
  (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) (hA : IsSkewSymm A)
  (f : Perm (Fin (2 * n))) (h : odd_perm f) :
  ∏ i : (Fin (2 * n)), A (f i) i =  -∏ i: Fin (2 * n), A ((perm_of_odd_perm f h) i) i :=
  by
    have h2:= Eq.symm (prod_filter_mul_prod_filter_not univ
          (fun x↦ x ∈ (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h))).support)
          fun x ↦  A (f x) x)
    rw[h2]
    have h3 := Eq.symm (prod_filter_mul_prod_filter_not univ
          (fun x↦ x ∈ (f.cycleOf (Fin.ofNat (2*n) (small_nat_of_odd_perm f h))).support)
          fun x ↦  A ((perm_of_odd_perm f h) x) x)
    rw[h3]
    have help : ∀x∉ (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support,
            (perm_of_odd_perm f h) x = f x :=
            by
              rw[perm_of_odd_perm]
              intro x hx
              simp only [Perm.mem_support, ne_eq, Decidable.not_not] at hx
              rw[mul_apply]
              symm at hx
              apply inv_eq_iff_eq.mpr at hx
              rw[hx,mul_apply,hx]
    have help2 : ∀ i ∉ (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support,
              A ((perm_of_odd_perm f h) i) i = A (f i) i:=
              by
                intro i hi
                rw[help i hi]
    have h4 :
            ∏ x with x ∉ (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support,
              A ((perm_of_odd_perm f h) x) x
            =∏ x with x ∉ (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support,
              A (f x) x :=
            by
              refine prod_bijective id bijective_id ?_ ?_
              · simp only [Fin.ofNat_eq_cast, Perm.mem_support, ne_eq, Decidable.not_not,
                mem_filter, mem_univ, true_and, id_eq, implies_true]
              simp only [mem_filter, mem_univ, true_and, id_eq]
              exact help2
    have help3 :
              ∀x∈  (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support,
              (perm_of_odd_perm f h) x = f⁻¹ x := by
              intro m hm
              exact (perm_of_odd_perm_support f h m hm).symm
    have help4 :
              ∀ i ∈  (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support,
                A ((perm_of_odd_perm f h) i) i = A (f⁻¹ i) i:=
              by
              intro i hi
              rw[help3 i hi]
    have h5 :
            ∏ x with x ∈  (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support,
            A ((perm_of_odd_perm f h) x) x
            =∏ x with x ∈  (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support,
            A (f⁻¹ x) x :=
            by
              refine prod_bijective id bijective_id ?_ ?_
              · simp only [Fin.ofNat_eq_cast, Perm.mem_support, ne_eq, mem_filter, mem_univ,
                true_and, id_eq, implies_true]
              simp only [ mem_filter, mem_univ,
                true_and, id_eq]
              exact help4
    rw[h4]
    rw[h5]
    have h6 : (∏ x with x ∈ (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support,
             A x (f x))
             =
            (∏ x with x ∈ (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support,
             A (f⁻¹ x) x):=
            by
              refine prod_bijective f (Equiv.bijective f) ?_ ?_
              · intro i
                constructor
                · intro hi
                  simp only [mem_filter, mem_univ, true_and] at hi
                  simp only [mem_filter, mem_univ, true_and]
                  refine (mem_cycleFactorsFinset_support ?_ i).mpr hi
                  rw[small_nat_of_odd_perm]
                  exact (Nat.find_spec (nat_of_odd_perm f h)).left
                intro fi
                simp only [mem_filter, mem_univ, true_and] at fi
                simp only [mem_filter, mem_univ, true_and]
                refine (mem_cycleFactorsFinset_support ?_ i).mp fi
                exact (Nat.find_spec (nat_of_odd_perm f h)).left
              simp only [Fin.ofNat_eq_cast, Perm.mem_support, ne_eq, mem_filter, mem_univ, true_and,
                Perm.coe_inv, symm_apply_apply, implies_true]
    rw[← h6]
    have h7 : (∏ x with x ∈ (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support,
               A x (f x))
               =
              (∏ x with x ∈ (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support,
              -A (f x)  x) :=
              by
                refine prod_bijective id bijective_id ?_ ?_
                · simp only [Fin.ofNat_eq_cast, Perm.mem_support, ne_eq,
                mem_filter, mem_univ, true_and, id_eq, implies_true]
                simp only [Fin.ofNat_eq_cast, Perm.mem_support, ne_eq,
                mem_filter, mem_univ, true_and, id_eq]
                intro i
                rw[← IsSkewSymm.apply hA]
                simp only [implies_true]
    rw[h7]
    have h8 : (∏ x with x ∈ (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support,
              -A (f x)  x) =
              (-1: R)^(#(f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support)*
              (∏ x with x ∈ (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support,
               A (f x) x):=
              by
              have h81 : ∏ x with x ∈ ((f.cycleOf (Fin.ofNat (2 * n)
                        (small_nat_of_odd_perm f h))).support), -A (f x) x
                        = ∏ x with x∈ (f.cycleOf (Fin.ofNat (2 * n)
                         (small_nat_of_odd_perm f h))).support, ((-1 : R) * A (f x) x) := by
                        refine prod_congr rfl ?_
                        intro x hx
                        simp
              rw[h81]
              rw[← pow_card_mul_prod]
              rw[Perm.support]
              simp
    rw[h8]
    have hodd : Odd ((f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support).card := by
        rcases Nat.even_or_odd ((f.cycleOf (Fin.ofNat (2 * n)
                   (small_nat_of_odd_perm f h))).support).card
        with hEven | hOdd
        · have hmem : (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h)))
          ∈ f.cycleFactorsFinset :=
          by
            rw[small_nat_of_odd_perm]
            exact (Nat.find_spec (nat_of_odd_perm f h)).left
          have hsgn := Perm.IsCycle.sign ((mem_cycleFactorsFinset_iff.mp hmem).left)
          have hsignone : sign (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h)))= 1 := by
            rw [small_nat_of_odd_perm]
            exact (Nat.find_spec (nat_of_odd_perm f h)).right
          rw [hsignone] at hsgn
          rw [hEven.neg_one_pow] at hsgn
          norm_num at hsgn
        · exact hOdd
    have hfinal : (-1 : R) ^ (((f.cycleOf (Fin.ofNat (2 * n)
                  (small_nat_of_odd_perm f h))).support).card)
                = -1 := by
                  rw [Odd.neg_one_pow hodd]
    rw[hfinal]
    simp



theorem perm_of_odd_perm_opposite_sign {R : Type v} {n : ℕ} [NeZero n] [CommRing R]
 (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) (hA : IsSkewSymm A)
 (f : Perm (Fin (2 * n))) (h : odd_perm f) :
  Equiv.Perm.sign f • ∏ i, A (f i) i +
  Equiv.Perm.sign (perm_of_odd_perm f h) • ∏ i, A ((perm_of_odd_perm f h) i) i = 0 :=
  by
    rw[← sign_perm_of_odd_perm_eq_sign_self]
    rw[← smul_add]
    rw[shift_sign_perm_of_odd_perm]
    · simp only [neg_add_cancel, smul_zero]
    · exact hA
    exact h

theorem perm_of_odd_perm_no_fixed_points {n : ℕ} [NeZero n]
(f : Perm (Fin (2 * n))) (h : odd_perm f) : perm_of_odd_perm f h ≠ f :=
by
  by_contra h1
  rw[perm_of_odd_perm] at h1
  have h2 : (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h)))⁻¹ *
      (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h)))⁻¹ = 1 :=
      by exact mul_left_cancel h1
  have h3 : (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h)))⁻¹
           = f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h)):=
            by
            have h31 :=
            (mul_left_inj (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h)))).mpr h2
            simp only [inv_mul_cancel_right, one_mul] at h31
            exact h31
  have h4 : (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h)))^2 =1 :=
            by
            have h41 := (mul_left_inj (f.cycleOf (Fin.ofNat (2 * n)
            (small_nat_of_odd_perm f h)))).mpr h3
            rw[inv_mul_cancel] at h41
            exact h41.symm
  have hspec := (Nat.find_spec (nat_of_odd_perm f h))
  have fcyclefinset : f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))
                    ∈ f.cycleFactorsFinset := mem_def.mpr (hspec.left)
  have fcycle : IsCycle (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h)))
              := (mem_cycleFactorsFinset_iff.mp fcyclefinset).left
  have forder : orderOf (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))) =2:= by
    refine orderOf_eq_prime_iff.mpr ?_
    constructor
    · exact h4
    exact cycleOf_ne_one_iff_mem_cycleFactorsFinset.mpr fcyclefinset
  have support2 : #((f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))).support) =2 :=
                  by
                    rw[← IsCycle.orderOf fcycle]
                    exact forder
  have fsignneg : sign (f.cycleOf (Fin.ofNat (2 * n) (small_nat_of_odd_perm f h))) =-1 := by
                  rw [IsCycle.sign fcycle]
                  rw[support2]
                  simp only [even_two, Even.neg_pow, one_pow]
  have hspecright:=hspec.right
  rw[small_nat_of_odd_perm] at fsignneg
  rw[hspecright] at fsignneg
  contradiction

theorem Odd_Perm_of_Odd_Perm_no_fixed_points {n : ℕ} [NeZero n] (f : Odd_Perm (Fin (2 * n))) :
 Odd_Perm_of_Odd_Perm f  ≠ f :=
  by
    rw[Odd_Perm_of_Odd_Perm]
    refine Subtype.coe_ne_coe.mp ?_
    exact perm_of_odd_perm_no_fixed_points f.val f.property
theorem Odd_Perm_of_Odd_Perm_opposite_sign {R : Type v} {n : ℕ} [NeZero n] [CommRing R]
  (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) (hA : IsSkewSymm A) (f : Odd_Perm (Fin (2 * n))) :
  Equiv.Perm.sign f.val • ∏ i, A (f.val i) i +
  Equiv.Perm.sign ((Odd_Perm_of_Odd_Perm f).val) •
   ∏ i, A ((Odd_Perm_of_Odd_Perm f).val i) i = 0 :=by
    rw[Odd_Perm_of_Odd_Perm]
    exact perm_of_odd_perm_opposite_sign A hA f.val f.property



--The preceeding work culminates here in showing that the odd permutations
--do not contribute to the determinant

theorem odd_sum_eq_zero {R : Type v} {n : ℕ} [NeZero n] [CommRing R]
  (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) (h : A.IsSkewSymm) :
  ∑ σ :  Odd_Perm (Fin (2*n)) , Equiv.Perm.sign σ.val • ∏ i, A (σ.val i) i = 0 :=
  by
    refine Finset.sum_ninvolution ?_ ?_ ?_ ?_ ?_
    · exact Odd_Perm_of_Odd_Perm
    · intro f
      exact Odd_Perm_of_Odd_Perm_opposite_sign A h f
    · intro f hf
      exact Odd_Perm_of_Odd_Perm_no_fixed_points f
    · simp only [Set.coe_setOf, mem_univ, implies_true]
    · exact inv_Perm_of_Odd_Perm





--We now aim to associate an even permutation to every pair of matchings
--We construct this permutation by constructing disjoint cycles that multiply to it.
--We construct these cycles from a list which we construct iteratively.
def list_of_pair_matching_it
  {n : ℕ} (M N : (PerfectMatching (Fin (2 * n)))) (Lx : List (Fin (2 * n)) × Fin (2 * n)) :
  List (Fin (2 * n))×Fin (2*n):=
  by
    have u:= PerfectMatching.partner N Lx.2
    have v:= PerfectMatching.partner M u
    exact if (u ∉ Lx.1 ∧ v ∉ Lx.1) then (Lx.1 ++ [u,v],v)  else (Lx.1, v)

def list_of_pair_matching_it_many
  {n : ℕ} (m : ℕ) [NeZero n] (M N : (PerfectMatching (Fin (2 * n)))) (x : Fin (2 * n))
  : List (Fin (2 * n)) :=
  by
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
 : List.Nodup (list_of_pair_matching_it_many m M N x) :=
  by
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
  List.Nodup (list_of_pair_matching M N x) :=
    by
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
  2≤ (list_of_pair_matching_it_many m M N x ).length :=
  by
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
  2≤ (list_of_pair_matching M N x).length :=
  by
    exact two_le_list_of_pair_matching_it_many_length n M N x

--We also show it has an even number of elements iteratively
lemma even_list_of_pair_matching_it_of_even
  {n : ℕ} (M N : (PerfectMatching (Fin (2 * n)))) (Lx : List (Fin (2 * n)) × Fin (2 * n))
  (hl : 2 ∣ ((Lx.1).length)) :
  2∣  ((list_of_pair_matching_it M N Lx).1).length :=
 by
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
            (congrFun rfl ((list_of_pair_matching_it M N)^[d]
            ([x, M.partner x], x)).1.length) hd).mp
        (h hd)
theorem even_list_of_pair_matching {n : ℕ} [NeZero n] (M N : PerfectMatching (Fin (2 * n)))
  (x : Fin (2 * n)) : 2∣  (list_of_pair_matching M N x ).length :=
  by
    exact even_list_of_pair_matching_it_many n M N x

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
  (x : Fin (2 * n)) : sign (cycle_of_pair_matching M N x) = -1 :=
  by
  have h := cycle_of_pair_matching_cycle M N x
  have h2 :=even_list_of_pair_matching M N x
  have h3 := IsCycle.sign h
  rw[h3]
  simp only [neg_inj]
  have h4 : #(cycle_of_pair_matching M N x).support = (list_of_pair_matching M N x).length :=
    by
    rw[cycle_of_pair_matching]
    rw[List.support_formPerm_of_nodup]
    · refine List.toFinset_card_of_nodup ?_
      · exact list_of_pair_matching_nodup M N x
    · exact list_of_pair_matching_nodup M N x
    intro i
    have htwo : 2 ≤ (list_of_pair_matching M N x).length:=
      by exact two_le_list_of_pair_matching M N x
    have hneq : (list_of_pair_matching M N x).length > 1 :=
      by exact Nat.lt_of_succ_le htwo
    have hneq1 : (list_of_pair_matching M N x).length ≠  1 :=
      by exact Ne.symm (Nat.ne_of_lt htwo)
    exact Ne.symm (ne_of_apply_ne List.length fun a ↦ hneq1 (id (Eq.symm a)))
  rw[h4]
  have heven : ∃k, (list_of_pair_matching M N x).length = 2*k:= h2
  obtain ⟨k,hk⟩ :=heven
  rw[hk]
  simp only [even_two, Even.mul_right, Even.neg_pow, one_pow]
--We now build the full permutation iteratively
--might be better to phrase this in terms of disjointness.
noncomputable instance {n : ℕ} (f g : Perm (Fin (2 * n))) :
  Decidable (f.Disjoint g) :=by exact Classical.propDecidable (f.Disjoint g)

noncomputable def perm_of_pair_matching_it {n : ℕ} [NeZero n] (M N : PerfectMatching (Fin (2 * n)))
 (fm : Perm (Fin (2 * n)) × ℕ) : Perm (Fin (2 * n)) × ℕ :=
by
  exact (if fm.1.Disjoint (cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2))
  then (fm.1*(cycle_of_pair_matching M N (Fin.ofNat (2*n) (fm.2))),n+1) else (fm.1,n+1))

noncomputable def perm_of_pair_matching_it_many {n : ℕ} (m : ℕ) [NeZero n]
  (M N : PerfectMatching (Fin (2 * n))) :  Perm (Fin (2 * n)) := by
  exact ((perm_of_pair_matching_it M N) ^[m] (1,1)).1

noncomputable def perm_of_pair_matching
  {n : ℕ} [NeZero n] (M N : (PerfectMatching (Fin (2 * n)))) : Perm (Fin (2*n)) := by
  exact perm_of_pair_matching_it_many (2*n) M N
--We show that this permutation is even iteratively.
theorem even_perm_perm_of_pair_matching_it_of_even {n : ℕ} [NeZero n]
 (M N : (PerfectMatching (Fin (2 * n)))) (fm : Perm (Fin (2 * n)) × ℕ) (hfm : even_perm fm.1) :
  even_perm ((perm_of_pair_matching_it M N fm).1) :=
  by
    rw[perm_of_pair_matching_it]
    by_cases h: fm.1.Disjoint (cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2))
    · have h2: (if fm.1.Disjoint (cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2))
      then (fm.1 * cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2), n + 1)
      else (fm.1, n + 1)) = (fm.1 * cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2), n + 1):=
        by exact if_pos h
      rw[h2]
      simp only [Fin.ofNat_eq_cast]
      rw[even_perm]
      intro σ hσ
      rw[even_perm] at hfm
      have h3 :σ ∈ (fm.1).cycleFactorsFinset ∨
      σ ∈ (cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2)).cycleFactorsFinset :=
        by
        have h3help : (fm.1 *
         cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2)).cycleFactorsFinset
        = (cycleFactorsFinset fm.1)
        ∪ (cycleFactorsFinset (cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2))):=
          by
          refine Disjoint.cycleFactorsFinset_mul_eq_union ?_
          exact h
        refine mem_union.mp ?_
        rw[← h3help]
        exact hσ
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
    · have h7: (if fm.1.Disjoint (cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2))
      then (fm.1 * cycle_of_pair_matching M N (Fin.ofNat (2 * n) fm.2), n + 1)
      else (fm.1, n + 1)) = (fm.1, n + 1) :=
        by exact if_neg h
      rw[h7]
      exact hfm

theorem even_perm_perm_of_pair_matching_it_many {n : ℕ} [NeZero n] (m : ℕ)
  (M N : (PerfectMatching (Fin (2 * n)))) :  even_perm (perm_of_pair_matching_it_many m M N) :=
  by
    rw[perm_of_pair_matching_it_many]
    induction' m with d hd
    · simp only [iterate_zero, id_eq]
      rw[even_perm]
      intro σ hσ
      rw[cycleFactorsFinset_one] at hσ
      contradiction

    rw[add_comm,iterate_add, iterate_one]
    exact even_perm_perm_of_pair_matching_it_of_even M N
      (((perm_of_pair_matching_it M N)^[d]) (1, 1)) hd
theorem even_perm_of_pair_matching {n : ℕ} [NeZero n] (M N : PerfectMatching (Fin (2 * n)))
: even_perm (perm_of_pair_matching M N) := even_perm_perm_of_pair_matching_it_many (2*n) M N

axiom perm_of_pair_matching_full_support {n : ℕ} [NeZero n] (M N : (PerfectMatching (Fin (2 * n))))
 : full_support (perm_of_pair_matching M N)
--We now start build a pair of matchings from a given even permutation.

def cyclematchingM_of_even_perm_it {n : ℕ} [NeZero n] (σ : Perm (Fin (2 * n)))
  (Sm : Finset (Fin (2 * n) ×ₗ Fin (2 * n)) × ℕ) : Finset (Fin (2 * n) ×ₗ Fin (2 * n))× ℕ :=
  by
    exact if (∃l∈ Sm.1, l.1=Fin.ofNat (2*n) Sm.2 ∨ l.2=Fin.ofNat (2*n)  Sm.2
             ∨ l.1 = σ ((Fin.ofNat (2*n) Sm.2)) ∨ l.2 =σ ((Fin.ofNat (2*n) Sm.2)))
             then (Sm.1, (σ (σ (Fin.ofNat (2*n) Sm.2))))
            else ((Sm.1 ∪ {pair (Fin.ofNat (2*n) Sm.2) (σ (Fin.ofNat (2*n) Sm.2))}),
            (σ (σ (Fin.ofNat (2*n) Sm.2))))


def cyclematchingN_of_even_perm_it {n : ℕ} [NeZero n] (σ : Perm (Fin (2 * n)))
(Sm : Finset (Fin (2 * n) ×ₗ Fin (2 * n)) × ℕ) : Finset (Fin (2 * n) ×ₗ Fin (2 * n))× ℕ :=
cyclematchingM_of_even_perm_it σ⁻¹ Sm

def cyclematchingM_of_even_perm_it_many {n : ℕ} [NeZero n] (m : ℕ)
(σ : Perm (Fin (2 * n))) (b : ℕ) : Finset (Fin (2 * n) ×ₗ Fin (2 * n)) × ℕ :=
(cyclematchingM_of_even_perm_it σ) ^[m] (∅, b)

def cyclematchingN_of_even_perm_it_many {n : ℕ} [NeZero n] (m : ℕ)
 (σ : Perm (Fin (2 * n))) (b : ℕ) : Finset (Fin (2 * n) ×ₗ Fin (2 * n)) × ℕ  :=
cyclematchingM_of_even_perm_it_many m σ⁻¹ b
def edges_cyclematchingM_of_even_perm {n : ℕ} [NeZero n] (σ : Perm (Fin (2 * n)))
 (b : ℕ) : Finset (Fin (2 * n) ×ₗ Fin (2 * n)) :=
 (cyclematchingM_of_even_perm_it_many (2*n) σ b).1
def edges_cyclematchingN_of_even_perm {n : ℕ} [NeZero n] (σ : Perm (Fin (2 * n)))
(b : ℕ) : Finset (Fin (2 * n) ×ₗ Fin (2 * n)) :=
edges_cyclematchingM_of_even_perm σ⁻¹ b

theorem ordered_cyclematchingM_of_even_perm_it_of_ordered {n : ℕ} [NeZero n]
(σ : Perm (Fin (2 * n))) (hσ : full_support σ) (Sm : Finset (Fin (2 * n) ×ₗ Fin (2 * n)) × ℕ)
  (hSm : ∀ a ∈ Sm.1, a.1 < a.2) : ∀ a ∈ (cyclematchingM_of_even_perm_it σ Sm).1, a.1 < a.2 :=
  by
    rw[cyclematchingM_of_even_perm_it]
    by_cases case: ∃ l ∈ Sm.1, l.1 = Fin.ofNat (2*n) Sm.2 ∨
                    l.2 =Fin.ofNat (2*n) Sm.2 ∨ l.1 = σ (Fin.ofNat (2 * n) Sm.2)
                    ∨ l.2 = σ (Fin.ofNat (2 * n) Sm.2)
    · simp_rw[case]
      simp only [↓reduceIte]
      exact hSm
    simp_rw[case]
    simp only [↓reduceIte, union_singleton, mem_insert, forall_eq_or_imp]
    constructor
    · rw[pair]
      simp only [lt_sup_iff, inf_lt_left, not_le, inf_lt_right, lt_or_lt_iff_ne, ne_eq]
      rw[full_support] at hσ
      have hsm2:= hσ (Fin.ofNat (2 * n) Sm.2)
      exact Perm.mem_support.mp (hσ (Fin.ofNat (2 * n) Sm.2))
    exact hSm

theorem ordered_cyclematchingM_of_even_perm_it_many {n : ℕ} [NeZero n] (m : ℕ)
  (σ : Perm (Fin (2 * n))) (hσ : full_support σ) (b : ℕ) :
  ∀a ∈ (cyclematchingM_of_even_perm_it_many m σ b).1, a.1<a.2 :=
by
rw[cyclematchingM_of_even_perm_it_many]
induction' m with d hd
· simp only [iterate_zero, id_eq, notMem_empty, IsEmpty.forall_iff, implies_true]
rw[add_comm, iterate_add,iterate_one, Function.comp_apply]
exact ordered_cyclematchingM_of_even_perm_it_of_ordered
     σ hσ (((cyclematchingM_of_even_perm_it σ)^[d] (∅, b))) hd

theorem ordered_cyclematchingM_of_even_perm {n : ℕ} [NeZero n]
 (σ : Perm (Fin (2 * n))) (hσ : full_support σ) (b : ℕ) :
  ∀a∈ edges_cyclematchingM_of_even_perm σ b, a.1<a.2 :=
by exact ordered_cyclematchingM_of_even_perm_it_many (2*n) σ hσ b
--The following theorem is a long proof by many, many cases. It is not very human-readable.
--Sorry about this.
theorem disjoint_cyclematchingM_of_even_perm_it_of_disjoint
  {n : ℕ} [NeZero n] (σ : Perm (Fin (2 * n)))
  (Sm : Finset (Fin (2 * n) ×ₗ Fin (2 * n)) × ℕ) (hSm : ∀ a ∈ Sm.1, ∀ b ∈ Sm.1,
  (a ≠ b) → (a.1 ≠ b.1 ∧ a.2 ≠ b.2 ∧ a.1 ≠ b.2 ∧ a.2 ≠ b.1)) :
  ∀ a ∈ (cyclematchingM_of_even_perm_it σ Sm).1, ∀ b ∈ (cyclematchingM_of_even_perm_it σ Sm).1,
  (a ≠ b) → (a.1 ≠ b.1 ∧ a.2 ≠ b.2 ∧ a.1 ≠ b.2 ∧ a.2 ≠ b.1) :=
  by
    rw[cyclematchingM_of_even_perm_it]
    by_cases case: ∃ l ∈ Sm.1, l.1 =Fin.ofNat (2*n) Sm.2 ∨
      l.2 =Fin.ofNat (2*n) Sm.2 ∨ l.1 = σ (Fin.ofNat (2 * n) Sm.2)
      ∨ l.2 = σ (Fin.ofNat (2 * n) Sm.2)
    · simp_rw[case]
      simp only [↓reduceIte]
      exact hSm
    simp_rw[case]
    simp only [↓reduceIte, union_singleton, mem_insert, ne_eq, forall_eq_or_imp,
      not_true_eq_false, false_and, and_self, imp_self, true_and]
    constructor
    · intro a ha hp
      constructor
      · push_neg at case
        have casea := case a ha
        rw[pair]
        simp only [ne_eq]
        by_cases! caselt : Fin.ofNat (2 * n) Sm.2 < σ (Fin.ofNat (2 * n) Sm.2)
        · have help : min (Fin.ofNat (2 * n) Sm.2) (σ (Fin.ofNat (2 * n) Sm.2))
          =Fin.ofNat (2 * n) Sm.2:=
            by exact min_eq_left_of_lt caselt
          rw[help]
          exact Ne.intro (id (Ne.symm casea.left))
        have help : min (Fin.ofNat (2 * n) Sm.2) (σ (Fin.ofNat (2 * n) Sm.2)) =
        σ (Fin.ofNat (2 * n) Sm.2):=
          by exact min_eq_right caselt
        rw[help]
        exact Ne.intro (id (Ne.symm casea.right.right.left))
      constructor
      · push_neg at case
        have casea := case a ha
        rw[pair]
        simp only [ne_eq]
        by_cases! casegt : Fin.ofNat (2 * n) Sm.2 > σ (Fin.ofNat (2 * n) Sm.2)
        · have help : max (Fin.ofNat (2 * n) Sm.2) (σ (Fin.ofNat (2 * n) Sm.2))
          =Fin.ofNat (2 * n) Sm.2:=
            by exact max_eq_left_of_lt casegt
          rw[help]
          exact Ne.intro (id (Ne.symm casea.right.left))
        have help : max (Fin.ofNat (2 * n) Sm.2) (σ (Fin.ofNat (2 * n) Sm.2))
          =σ (Fin.ofNat (2 * n) Sm.2):=
          by exact max_eq_right casegt
        rw[help]
        exact Ne.intro (id (Ne.symm casea.right.right.right))
      constructor
      · push_neg at case
        have casea := case a ha
        rw[pair]
        simp only [ne_eq]
        by_cases! caselt : Fin.ofNat (2 * n) Sm.2 <σ (Fin.ofNat (2 * n) Sm.2)
        · have help : min (Fin.ofNat (2 * n) Sm.2) (σ (Fin.ofNat (2 * n) Sm.2)) =
          Fin.ofNat (2 * n) Sm.2:=
            by exact min_eq_left_of_lt caselt
          rw[help]
          exact Ne.intro (id (Ne.symm casea.right.left))
        have help : min (Fin.ofNat (2 * n) Sm.2) (σ (Fin.ofNat (2 * n) Sm.2)) =
        σ (Fin.ofNat (2 * n) Sm.2):=
          by exact min_eq_right caselt
        rw[help]
        exact Ne.intro (id (Ne.symm casea.right.right.right))
      push_neg at case
      have casea := case a ha
      rw[pair]
      simp only [ne_eq]
      by_cases! casegt : Fin.ofNat (2 * n) Sm.2 >σ (Fin.ofNat (2 * n) Sm.2)
      · have help : max (Fin.ofNat (2 * n) Sm.2) (σ (Fin.ofNat (2 * n) Sm.2))
        =Fin.ofNat (2 * n) Sm.2:=
          by exact max_eq_left_of_lt casegt
        rw[help]
        exact Ne.intro (id (Ne.symm casea.left))
      have help : max (Fin.ofNat (2 * n) Sm.2) (σ (Fin.ofNat (2 * n) Sm.2)) =
      σ (Fin.ofNat (2 * n) Sm.2):=
        by exact max_eq_right casegt
      rw[help]
      exact Ne.intro (id (Ne.symm casea.right.right.left))
    intro a ha
    constructor
    · intro hp
      constructor
      · push_neg at case
        have casea := case a ha
        rw[pair]
        simp only [ne_eq]
        by_cases! caselt : Fin.ofNat (2 * n) Sm.2 < σ (Fin.ofNat (2 * n) Sm.2)
        · have help : min (Fin.ofNat (2 * n) Sm.2) (σ (Fin.ofNat (2 * n) Sm.2)) =
          Fin.ofNat (2 * n) Sm.2:=
            by exact min_eq_left_of_lt caselt
          rw[help]
          exact Ne.intro casea.left
        have help : min (Fin.ofNat (2 * n) Sm.2) (σ (Fin.ofNat (2 * n) Sm.2)) =
        σ (Fin.ofNat (2 * n) Sm.2):=
          by exact min_eq_right caselt
        rw[help]
        exact Ne.intro casea.right.right.left
      constructor
      · push_neg at case
        have casea := case a ha
        rw[pair]
        simp only [ne_eq]
        by_cases! casegt : Fin.ofNat (2 * n) Sm.2 > σ (Fin.ofNat (2 * n) Sm.2)
        · have help : max (Fin.ofNat (2 * n) Sm.2) (σ (Fin.ofNat (2 * n) Sm.2))
          =Fin.ofNat (2 * n) Sm.2:=
            by exact max_eq_left_of_lt casegt
          rw[help]
          exact Ne.intro casea.right.left
        have help : max (Fin.ofNat (2 * n) Sm.2) (σ (Fin.ofNat (2 * n) Sm.2))
        =σ (Fin.ofNat (2 * n) Sm.2):=
          by exact max_eq_right casegt
        rw[help]
        exact Ne.intro casea.right.right.right
      constructor
      · push_neg at case
        have casea := case a ha
        rw[pair]
        simp only [ne_eq]
        by_cases! casegt : Fin.ofNat (2 * n) Sm.2 >σ (Fin.ofNat (2 * n) Sm.2)
        · have help : max (Fin.ofNat (2 * n) Sm.2) (σ (Fin.ofNat (2 * n) Sm.2)) =
          Fin.ofNat (2 * n) Sm.2:=
            by exact max_eq_left_of_lt casegt
          rw[help]
          exact Ne.intro (casea.left)
        have help : max (Fin.ofNat (2 * n) Sm.2) (σ (Fin.ofNat (2 * n) Sm.2))
        =σ (Fin.ofNat (2 * n) Sm.2):=
          by exact max_eq_right casegt
        rw[help]
        exact Ne.intro casea.right.right.left
      · push_neg at case
        have casea := case a ha
        rw[pair]
        simp only [ne_eq]
        by_cases! caselt : Fin.ofNat (2 * n) Sm.2 <σ (Fin.ofNat (2 * n) Sm.2)
        · have help : min (Fin.ofNat (2 * n) Sm.2) (σ (Fin.ofNat (2 * n) Sm.2))
          =Fin.ofNat (2 * n) Sm.2:=
            by exact min_eq_left_of_lt caselt
          rw[help]
          exact Ne.intro (casea.right.left)
        have help : min (Fin.ofNat (2 * n) Sm.2) (σ (Fin.ofNat (2 * n) Sm.2))
        =σ (Fin.ofNat (2 * n) Sm.2):=
          by exact min_eq_right caselt
        rw[help]
        exact Ne.intro (casea.right.right.right)
    intro c hc hp
    exact hSm a ha c hc hp

theorem disjoint_cyclematchingM_of_even_perm_it_many {n : ℕ} [NeZero n] (m : ℕ)
 (σ : Perm (Fin (2 * n))) (b : ℕ) : ∀ a ∈ (cyclematchingM_of_even_perm_it_many m σ b).1,
  ∀ c ∈ (cyclematchingM_of_even_perm_it_many m σ b).1,
  (a ≠ c)→ (a.1 ≠ c.1  ∧ a.2 ≠ c.2 ∧ a.1 ≠ c.2 ∧ a.2 ≠ c.1):=
  by
    rw[cyclematchingM_of_even_perm_it_many]
    induction' m with d hd
    · simp only [iterate_zero, id_eq, notMem_empty, ne_eq, IsEmpty.forall_iff, implies_true]
    rw[add_comm, iterate_add,iterate_one, Function.comp_apply]
    exact disjoint_cyclematchingM_of_even_perm_it_of_disjoint σ
     (((cyclematchingM_of_even_perm_it σ)^[d] (∅, b))) hd

theorem disjoint_cyclematchingM_of_even_perm {n : ℕ} [NeZero n]
 (σ : Perm (Fin (2 * n))) (b : ℕ) :
  ∀ a ∈ (edges_cyclematchingM_of_even_perm σ b), ∀ c ∈ (edges_cyclematchingM_of_even_perm σ b),
  (a ≠ c)→ (a.1 ≠ c.1  ∧ a.2 ≠ c.2 ∧ a.1 ≠ c.2 ∧ a.2 ≠ c.1) :=
   disjoint_cyclematchingM_of_even_perm_it_many (2*n) σ b

lemma evenpermhelp {n : ℕ} [NeZero n] (σ : Perm (Fin (2 * n))) (hσ : even_perm σ)
 (hsupp : full_support σ) (b : Fin (2 * n)) (l k : ℤ) :
 (σ^(2*k)) (b) ≠ (σ^(2*l+1)) (b) := by
by_contra h
rw[full_support] at hsupp
rw[even_perm] at hσ
have cycleatb := hσ (σ.cycleOf b)
have hsuppb := hsupp b
rw[Perm.support] at hsuppb
simp only [mem_filter, mem_univ, true_and] at hsuppb
have etwas:= (zpow_eq_zpow_on_iff σ hsuppb).mp h
apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mp at etwas
apply Int.dvd_of_emod_eq_zero at etwas
have cycleofbiscycle : σ.cycleOf b ∈ σ.cycleFactorsFinset := by
 exact cycleOf_mem_cycleFactorsFinset_iff.mpr (hsupp b)
have signcycle := cycleatb cycleofbiscycle
have divtwo : (2:ℤ) ∣ #(σ.cycleOf b).support := by
  have hpow : ((-1 : ℤˣ) ^ #(σ.cycleOf b).support) = 1 := by
    have help : (1 : ℤˣ) = (-1) ^ #(σ.cycleOf b).support := by
      have iscycle : (σ.cycleOf b).IsCycle := by
        exact (isCycle_cycleOf_iff σ).mpr hsuppb
      have help2 := Perm.IsCycle.sign iscycle
      rw [signcycle] at help2
      rw [neg_inj] at help2
      exact help2
    exact help.symm
  have hmod : #(σ.cycleOf b).support % 2 = 0 := by
    have hpowmod : ((-1 : ℤˣ) ^ (#(σ.cycleOf b).support % 2)) = 1 := by
      simpa [Int.units_pow_eq_pow_mod_two] using hpow
    rcases Nat.mod_two_eq_zero_or_one #(σ.cycleOf b).support with h0 | h1
    · exact h0
    · rw [h1] at hpowmod
      norm_num at hpowmod
  have hEven : Even #(σ.cycleOf b).support := (Nat.even_iff.mpr hmod)
  rcases hEven with ⟨t, ht⟩
  have help : t+t=2*t := by exact Eq.symm (Nat.two_mul t)
  rw[help] at ht
  refine ⟨t, ?_⟩
  exact_mod_cast ht
have contra: 2 * k % 2 = (2 * l + 1) % 2 :=
  by
  refine Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr ?_
  refine Int.emod_eq_zero_of_dvd ?_
  exact Int.dvd_trans divtwo etwas
simp only [Int.mul_emod_right, Int.mul_add_emod_self_left, Int.one_emod_two, zero_ne_one] at contra

lemma powtwo_cycle_cyclematchingM_of_even_perm_it_many {n : ℕ} [NeZero n] (m : ℕ)
(σ : Perm (Fin (2 * n))) (b : ℕ) :
  Fin.ofNat (2*n) ((cyclematchingM_of_even_perm_it_many m σ b).2) =(σ^(2*m)) (Fin.ofNat (2*n) b) :=
  by
    rw[cyclematchingM_of_even_perm_it_many]
    induction' m with d hd
    · simp only [iterate_zero, id_eq, Fin.ofNat_eq_cast, mul_zero, pow_zero, Perm.coe_one]
    rw[add_comm, iterate_add,iterate_one, Function.comp_apply]
    rw[cyclematchingM_of_even_perm_it]
    by_cases case:
              ∃ l ∈ ((cyclematchingM_of_even_perm_it σ)^[d] (∅, b)).1,
                l.1 = Fin.ofNat (2 * n) ((cyclematchingM_of_even_perm_it σ)^[d] (∅, b)).2 ∨
                  l.2 = Fin.ofNat (2 * n) ((cyclematchingM_of_even_perm_it σ)^[d] (∅, b)).2 ∨
                    l.1 = σ (Fin.ofNat (2 * n) ((cyclematchingM_of_even_perm_it σ)^[d] (∅, b)).2) ∨
                      l.2 = σ (Fin.ofNat (2 * n) ((cyclematchingM_of_even_perm_it σ)^[d] (∅, b)).2)
    · simp_rw[case]
      simp only [↓reduceIte]
      rw[hd]
      simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
      rw[mul_add]
      rw[mul_one]
      rw[pow_add]
      simp only [Perm.coe_mul, Function.comp_apply]
      rw[pow_two]
      simp only [Perm.coe_mul, Function.comp_apply]
    simp_rw[case]
    simp only [↓reduceIte]
    rw[hd]
    rw[mul_add]
    rw[pow_add]
    simp only [Perm.coe_mul, Function.comp_apply]
    rw[pow_two]
    simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self, Perm.coe_mul, Function.comp_apply]


lemma powin_cycle_cyclematchingM_of_even_perm_it_many {n : ℕ} [NeZero n] (m : ℕ)
  (σ : Perm (Fin (2 * n))) (b : ℕ) :
   ∀a ∈ (cyclematchingM_of_even_perm_it_many m σ b).1, ∃k:ℕ, a.1 =(σ^(k)) (Fin.ofNat (2*n) b) :=
   by
    rw[cyclematchingM_of_even_perm_it_many]
    induction' m with d hd
    · simp only [iterate_zero, id_eq, notMem_empty,
       Fin.ofNat_eq_cast, IsEmpty.forall_iff, implies_true]
    rw[add_comm, iterate_add,iterate_one, Function.comp_apply]
    rw[cyclematchingM_of_even_perm_it]
    by_cases case:
              ∃ l ∈ ((cyclematchingM_of_even_perm_it σ)^[d] (∅, b)).1,
                l.1 = Fin.ofNat (2 * n) ((cyclematchingM_of_even_perm_it σ)^[d] (∅, b)).2 ∨
                  l.2 = Fin.ofNat (2 * n) ((cyclematchingM_of_even_perm_it σ)^[d] (∅, b)).2 ∨
                    l.1 = σ (Fin.ofNat (2 * n) ((cyclematchingM_of_even_perm_it σ)^[d] (∅, b)).2) ∨
                      l.2 = σ (Fin.ofNat (2 * n) ((cyclematchingM_of_even_perm_it σ)^[d] (∅, b)).2)
    · simp_rw[case]
      simp only [↓reduceIte]
      exact hd
    simp_rw[case]
    simp only [↓reduceIte]
    simp only [ union_singleton, mem_insert, forall_eq_or_imp]
    constructor
    · rw[← cyclematchingM_of_even_perm_it_many]
      rw[pair]
      by_cases! casetwo : Fin.ofNat (2*n) ((cyclematchingM_of_even_perm_it_many d σ b).2)
                        < σ (Fin.ofNat (2*n) (cyclematchingM_of_even_perm_it_many d σ b).2)
      · simp only[]
        rw[min_eq_left_of_lt casetwo]
        use 2*d
        exact powtwo_cycle_cyclematchingM_of_even_perm_it_many d σ b
      simp only []
      rw[min_eq_right casetwo]
      use 2*d +1
      rw[powtwo_cycle_cyclematchingM_of_even_perm_it_many d σ b]
      rw[add_comm, pow_add]
      simp only [Fin.ofNat_eq_cast, pow_one, Perm.coe_mul, Function.comp_apply]
    exact hd

theorem subset_cyclematchingM_of_even_perm_it {n : ℕ} [NeZero n] (σ : Perm (Fin (2 * n)))
 (Sm : Finset (Fin (2 * n) ×ₗ Fin (2 * n)) × ℕ)
 : Sm.1⊆  (cyclematchingM_of_even_perm_it σ Sm).1 := by
  rw[cyclematchingM_of_even_perm_it]
  by_cases case :∃ l ∈ Sm.1,
          l.1 = Fin.ofNat (2 * n) Sm.2 ∨
            l.2 = Fin.ofNat (2 * n) Sm.2 ∨ l.1 = σ (Fin.ofNat (2 * n) Sm.2)
            ∨ l.2 = σ (Fin.ofNat (2 * n) Sm.2)
  · simp_rw[case]
    simp only [↓reduceIte]
    exact coe_subset.mp fun ⦃a⦄ a_1 ↦ a_1
  simp_rw[case]
  simp only [↓reduceIte, Fin.ofNat_eq_cast, union_singleton, subset_insert]

theorem subset_cyclematchingM_of_even_perm_it_several {n : ℕ} [NeZero n] (m : ℕ)
(σ : Perm (Fin (2 * n))) (Sm : Finset (Fin (2 * n) ×ₗ Fin (2 * n)) × ℕ)
 : Sm.1⊆  ((cyclematchingM_of_even_perm_it σ )^[m] Sm).1 := by
  induction' m with d hd
  · simp only [iterate_zero, id_eq, subset_refl]
  rw[add_comm, iterate_add,iterate_one, Function.comp_apply]
  rw[cyclematchingM_of_even_perm_it]
  by_cases case :∃ l ∈ ((cyclematchingM_of_even_perm_it σ)^[d] Sm).1,
          l.1 = Fin.ofNat (2 * n) ((cyclematchingM_of_even_perm_it σ)^[d] Sm).2 ∨
            l.2 = Fin.ofNat (2 * n) ((cyclematchingM_of_even_perm_it σ)^[d] Sm).2 ∨
              l.1 = σ (Fin.ofNat (2 * n) ((cyclematchingM_of_even_perm_it σ)^[d] Sm).2) ∨
                l.2 = σ (Fin.ofNat (2 * n) ((cyclematchingM_of_even_perm_it σ)^[d] Sm).2)
  · simp_rw[case]
    simp only [↓reduceIte]
    exact hd
  simp_rw[case]
  simp only [↓reduceIte]
  have hsub : ((cyclematchingM_of_even_perm_it σ)^[d] Sm).1 ⊆
              ((cyclematchingM_of_even_perm_it σ)^[d] Sm).1 ∪
              {pair (Fin.ofNat (2 * n) ((cyclematchingM_of_even_perm_it σ)^[d] Sm).2)
              (σ (Fin.ofNat (2 * n) ((cyclematchingM_of_even_perm_it σ)^[d] Sm).2))} :=
              subset_union_left
  exact coe_subset.mp fun ⦃a⦄ a_1 ↦ hsub (hd a_1)

--After this we show that signs and products are preserved under our bijection.

axiom whatremains {R : Type v} {n : ℕ} [NeZero n] [CommRing R]
(A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) (h : IsSkewSymm A) :
∑ i :PerfectMatching (Fin (2* n)), ∑  j :PerfectMatching (Fin (2* n)),
(↑↑(signMatching i) * ∏ i ∈ i.edges, A i.1 i.2) * (↑↑(signMatching j) * ∏ i ∈ j.edges, A i.1 i.2) =
  ∑ σ with even_perm σ, sign σ • ∏ i, A (σ i) i

theorem det_eq_Pf_square {R : Type v} {n : ℕ} [NeZero n] [CommRing R]
(A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) (h : IsSkewSymm A) : (Pf A)*(Pf A) = det A := by
rw[Pf]
rw[sum_mul_sum]
rw[det_eq_sum_odd_even]
rw[odd_sum_eq_Odd_sum]
rw[odd_sum_eq_zero]
· rw[add_zero]
  rw[whatremains]
  · exact h
exact h
