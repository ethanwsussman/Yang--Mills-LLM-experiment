import YangMills.Construction.Towers.TheJetsOfTheTwoOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def OperatorFunctionsRealOnCompactFields : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ζ : Tower.FullSpace.FullField L k,
      PeriodicOperators.IsSupBelow (Tower.FullSpace.fieldPeriodicData L k hL) (ζ.pauliCoeffs hL) ρ →
      ζ.IsCompactValued →
      (∀ i' i, (Tower.FullSpace.vectorOp ζ i' i).im = 0) ∧
        ∀ i' i, (Tower.FullSpace.ghostOp ζ i' i).im = 0
end YangMills.Construction.Tower.FullSpace
end
