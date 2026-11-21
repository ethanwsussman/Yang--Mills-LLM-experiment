import YangMills.Construction.Towers.DataOfAChangeOfTheGaugeFixing
import YangMills.Construction.Towers.InjectiveCovariantDifference
import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def GaugeFixingTransferDataAlongChain : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L n k k) fun W =>
      CovDiffInjective W →
        ∀ (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k),
          (J : Edge L n k 0 → Matrices.ComplexMatrix2) =
              leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ))
                (chosenProlongComp L n k k W) →
            (μ : Edge L n k k → Matrices.ComplexMatrix2) =
              (chosenCriticalBranch L n k).energyGradient k W →
            Nonempty (GaugeFixingTransferData L n k (topConstraintMap L n k W)
              (iterCovariantDerivLinear L n k (chosenProlongComp L n k k W))
              (augmentedHessian L n k W)
              (backgroundHessian (chosenProlongComp L n k k W) J μ)
              (iterAverageLinear L n k (chosenProlongComp L n k k W))
              (covDiffRealTranspose L n k (chosenProlongComp L n k k W) ∘ₗ
                covDiffLinear L n k (chosenProlongComp L n k k W)))
end YangMills.Construction.Tower
end
