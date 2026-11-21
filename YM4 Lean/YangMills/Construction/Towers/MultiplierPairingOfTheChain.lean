import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ChainMultiplierPairing.Statement : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L n k k) fun W => ∀ ξ : edgeFormSpace L n k 0,
      edgeFormPairing
          (leftGradient (fieldSpace L n k 0) (fun V => (plaquetteAction L n k V : ℂ)) (chainBottom W))
          ξ =
        traceFinsumPairing (restrictToPositiveEdges ((chosenCriticalBranch L n k).energyGradient k W))
          (restrictToPositiveEdges (topConstraintMap L n k W ξ : Edge L n k k → Matrices.ComplexMatrix2))
end YangMills.Construction.Tower
end
