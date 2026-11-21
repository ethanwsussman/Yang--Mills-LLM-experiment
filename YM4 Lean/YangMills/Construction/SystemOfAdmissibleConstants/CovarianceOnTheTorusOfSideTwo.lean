import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.GeneratingFunctionsAndConnectedFunctionsOfAMeasureAndOfATorus
import YangMills.Construction.LawInAState.DataOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open ProbabilityTheory
namespace YangMills.Construction.AdmissibleConstants
open YangMills.Construction.StateLaws
open YangMills.Construction.InfiniteLattice (AmbientSpace IsBoundedBorelCompactlySupported)
def SideTwoTorusCovariance : Prop :=
  ∀ L K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < K → ∀ β : ℝ, 0 < β → ∀ f h : AmbientSpace → ℝ,
    IsBoundedBorelCompactlySupported f → IsBoundedBorelCompactlySupported h →
      PeriodicLattice.torusUrsellFunction L 0 K β
          ![TestFunctions.periodize (PeriodicLattice.torusSide L 0) f,
            TestFunctions.periodize (PeriodicLattice.torusSide L 0) h] =
        ((cov[smearedObservable L K f, smearedObservable L K h; unitTorusMeasure L K β] : ℝ) : ℂ)
end YangMills.Construction.AdmissibleConstants
end
