import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import YangMills.Construction.Towers.InjectiveCovariantDifference
import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def LogNormaliserSubBackgroundConst : Prop :=
  ∀ L m k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 1 ≤ k →
    ∃ C : ℝ, EventuallyNearIdentity (fieldSpace L m k k) fun W =>
      CovDiffInjective W →
        ∀ (J : edgeFormSpace L m k 0) (μ : edgeFormSpace L m k k),
          (J : Edge L m k 0 → Matrices.ComplexMatrix2) =
              leftGradient (fieldSpace L m k 0) (fun U => (plaquetteAction L m k U : ℂ))
                (chosenProlongComp L m k k W) →
            (μ : Edge L m k k → Matrices.ComplexMatrix2) =
              (chosenCriticalBranch L m k).energyGradient k W →
            Real.log (totalGaussianNormaliser L m k W) -
              backgroundFunctional (chosenProlongComp L m k k W) J μ = C
end YangMills.Construction.Tower
end
