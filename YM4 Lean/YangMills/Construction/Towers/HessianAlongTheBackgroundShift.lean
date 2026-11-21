import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def HessianAlongBackgroundShift : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L n k k) fun W =>
      ∀ (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k),
        (J : Edge L n k 0 → Matrices.ComplexMatrix2) =
            leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ))
              (chosenProlongComp L n k k W) →
          (μ : Edge L n k k → Matrices.ComplexMatrix2) =
            (chosenCriticalBranch L n k).energyGradient k W →
          ∀ B : edgeFormSpace L n k 0,
            iterCovariantDerivLinear L n k (chosenProlongComp L n k k W) B = 0 →
            ∃ hB : backgroundShift L n k (chosenProlongComp L n k k W) B ∈
                LinearMap.ker (topConstraintMap L n k W),
              fibreRestrictedHessian L n k W ⟨_, hB⟩ =
                leftSecondDeriv (plaquetteAction L n k) (chosenProlongComp L n k k W) B B +
                  sourceQuadraticForm (chosenProlongComp L n k k W) J μ B
end YangMills.Construction.Tower
end
