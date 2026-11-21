import YangMills.Construction.Towers.ExpansionOfAStepInTheLeftChart
import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def FibreHessianViaQuadraticExpansion : Prop :=
  ∀ L m k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ a : ℕ, a + 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L m k (a + 1)) fun W =>
      (∃ q : EdgeFormBilinear L m k a, IsQuadraticExpansion (chosenProlong L m k a W) q) ∧
      ∀ q : EdgeFormBilinear L m k a, IsQuadraticExpansion (chosenProlong L m k a W) q →
        ∀ B : LinearMap.ker (constraintDifferential L m k a W),
          fibreHessianForm L m k a W B =
            leftSecondDeriv (chosenGaugeFixedEnergy L m k a) (chosenProlong L m k a W) B.1.1 B.1.1 -
              (traceFinsumPairing
                (restrictToPositiveEdges ((chosenCriticalBranch L m k).energyGradient (a + 1) W))
                (q B.1 B.1)).re
end YangMills.Construction.Tower
end
