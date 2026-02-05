import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Defs

variable {α β n m R : Type*}

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

--theorem isSkewSymm_mul_transpose_self [Fintype n] [Ring α] (A : Matrix n n α) :
 --   (-(A * Aᵀ)).IsSkewSymm :=
  --transpose_mul _ _

--theorem isSymm_transpose_mul_self [Fintype n] [NonUnitalCommSemiring α] (A : Matrix n n α) :
  --  (Aᵀ * A).IsSymm :=
 -- transpose_mul _ _

--theorem isSkewSymm_subtract_transpose_self [AddCommGroup α] (A : Matrix n n α) : (A - Aᵀ).IsSkewSymm := by


--theorem isSymm_transpose_add_self [AddCommSemigroup α] (A : Matrix n n α) : (Aᵀ + A).IsSymm :=
 -- add_comm _ _
