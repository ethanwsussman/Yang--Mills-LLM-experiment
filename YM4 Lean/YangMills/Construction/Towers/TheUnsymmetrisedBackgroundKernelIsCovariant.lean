import YangMills.Construction.Towers.TheTwoOperatorFunctionsAsFunctionsOfValues
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.RawHessianCovariance
open PeriodicOperators FieldValueFunctions Conventions
def CovarianceClaim : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ → ∀ (v : Fin 4 → ℤ)
      (ι' ι : (colourEdges L k 0).Carrier),
      rawHessianFn L k hL (shiftField (fieldPeriodicData L k hL) v f)
          ((colourEdges L k 0).translate v ι') ((colourEdges L k 0).translate v ι) =
        rawHessianFn L k hL f ι' ι
end YangMills.Construction.Tower.FullSpace.RawHessianCovariance
end
