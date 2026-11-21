import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicExtension
def LiftedMeanEqTorusMean : Prop :=
  ∀ (L m K : ℕ) (β : ℝ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < β →
    ∀ f : InfiniteLattice.AmbientSpace → ℝ, InfiniteLattice.IsBoundedBorelCompactlySupported f →
      ∫ U, InfiniteLattice.smearedEnergy f U ∂InfiniteLattice.liftedWilsonMeasure L m K β =
        ∫ U, PeriodicLattice.smearedObservable (j := (K : ℤ))
          (TestFunctions.periodize (PeriodicLattice.torusSide L m) f) U
          ∂PeriodicLattice.wilsonGibbsMeasure L m K β
end PeriodicExtension
end YangMills.Construction
