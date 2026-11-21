import YangMills.Construction.SpectralTheory.JointSpectralMeasureOfCommutingOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace JointSpectral
open BorelSpectral
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def jointMeasureOnBox (hn : 1 ≤ n) (A : Fin n → H →L[ℂ] H) (a b : Fin n → ℝ)
    (hab : ∀ i, a i < b i) : SpectralMeasure (closedBox a b) H :=
  jointMeasure hn A a b hab
def normBoundLower (A : Fin n → H →L[ℂ] H) (i : Fin n) : ℝ := -(‖A i‖ + 1)
def normBoundUpper (A : Fin n → H →L[ℂ] H) (i : Fin n) : ℝ := ‖A i‖ + 1
omit [CompleteSpace H] in
theorem normBoundLower_lt_normBoundUpper (A : Fin n → H →L[ℂ] H) (i : Fin n) :
    normBoundLower A i < normBoundUpper A i := by
  have := norm_nonneg (A i)
  simp only [normBoundLower, normBoundUpper]
  linarith
def jointMeasureOnSpace (hn : 1 ≤ n) (A : Fin n → H →L[ℂ] H) :
    SpectralMeasure (univ : Set (Fin n → ℝ)) H :=
  (jointMeasureOnBox hn A (normBoundLower A) (normBoundUpper A)
    (normBoundLower_lt_normBoundUpper A)).extendCarrier (subset_univ _) MeasurableSet.univ
end JointSpectral
end YangMills.Construction
