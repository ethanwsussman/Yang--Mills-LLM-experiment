import YangMills.Construction.Towers.TheTwoOperatorFunctionsAsFunctionsOfValues
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.RawHessianLocality
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.FieldValueFunctions
def Claim : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ρ : ℝ, IsLocalWith (fieldPeriodicData L k hL) (colourEdges L k 0) (colourEdges L k 0)
      (rawHessianFn L k hL) ρ 19
end YangMills.Construction.Tower.FullSpace.RawHessianLocality
end
