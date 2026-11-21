import YangMills.Construction.InfiniteLattice.WilsonWindows
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace HullsInEveryVolume
def torusMeasuresSatisfyWindowEquilibrium : Prop :=
  ∀ (L K : ℕ) (β : ℝ) (ha : 0 < PeriodicLattice.meshSize L (K : ℤ))
    (W : InfiniteLattice.LinkWindow (PeriodicLattice.meshSize L (K : ℤ))), 1 < L → 0 < β →
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      IsProbabilityMeasure (InfiniteLattice.liftedWilsonMeasure L m K β) ∧
        ∀ f : W.Assignments → ℝ, Measurable f → (∃ C : ℝ, ∀ V, |f V| ≤ C) →
          ∫ U, f (W.restrictInside U) ∂InfiniteLattice.liftedWilsonMeasure L m K β =
            ∫ U, (∫ V, f V * W.densityKernel ha β V U ∂W.haarProd)
              ∂InfiniteLattice.liftedWilsonMeasure L m K β
end HullsInEveryVolume
end YangMills.Construction
end
