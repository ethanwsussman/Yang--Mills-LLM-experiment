import YangMills.Construction.Matrices.NormAndTraceOfAComplexMatrix
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices.RectangularMatrix.NormOfProductAndAdjoint
def ProductAndScalarBounds {m n p : ℕ} [NeZero m] [NeZero n] [NeZero p]
    (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p) ℂ) (c : ℂ) : Prop :=
  (∀ x : Fin n → ℂ,
    ‖(WithLp.toLp 2 (A.mulVec x) : EuclideanSpace ℂ (Fin m))‖ ≤
      opNormValue A * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖) ∧
  opNormValue (A * B) ≤ opNormValue A * opNormValue B ∧
  opNormValue (c • A) = ‖c‖ * opNormValue A
def AdjointNormEq {m n : ℕ} [NeZero m] [NeZero n] (A : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  opNormValue A.conjTranspose = opNormValue A
def Properties : Prop :=
  ∀ (m n p : ℕ) [NeZero m] [NeZero n] [NeZero p]
    (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p) ℂ) (c : ℂ),
    ProductAndScalarBounds A B c ∧ AdjointNormEq A
end YangMills.Construction.Matrices.RectangularMatrix.NormOfProductAndAdjoint
