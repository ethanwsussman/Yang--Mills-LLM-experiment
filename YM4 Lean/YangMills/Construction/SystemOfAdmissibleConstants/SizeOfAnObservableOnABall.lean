import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace AdmissibleConstants
open YangMills.Construction.TestFunctions
open YangMills.Construction.InfiniteLattice (GaugeField AmbientSpace smearedEnergy)
def SmearedObservableBound : Prop :=
  (∀ (a R : ℝ), 0 < a → 0 < R → ∀ f : AmbientSpace → ℝ, IsBoundedFun f →
    (∃ x, tsupport f ⊆ closedBallR4 x R) → ∀ U : GaugeField a,
      |smearedEnergy f U| ≤ 12 * (2 * R / a + 1) ^ 4 * uniformNorm f) ∧
  (∀ (L m K : ℕ) (β R : ℝ), 13 ≤ L → 0 < β → 0 < R →
    ∀ f : YangMills.Construction.PeriodicLattice.FourTorus L m → ℝ, IsBoundedFun f →
    (∃ x, tsupport f ⊆ closedBallTorus x R) →
    ∀ᵐ U ∂YangMills.Construction.PeriodicLattice.wilsonGibbsMeasure L m K β,
      |YangMills.Construction.PeriodicLattice.smearedObservable f U| ≤
        12 * min ((2 * R / YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ) + 1) ^ 4)
          ((YangMills.Construction.PeriodicLattice.torusSide L m /
            YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)) ^ 4) * uniformNorm f)
end AdmissibleConstants
end YangMills.Construction
end
