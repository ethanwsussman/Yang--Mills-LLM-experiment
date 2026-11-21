import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower
def BackgroundFunctionalAlongBranchAnalytic : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    ∃ (𝒰 : Set (Edge L n k k → ComplexMatrix2)) (f : (Edge L n k k → ComplexMatrix2) → ℝ),
      IsOpenNhdOfOne 𝒰 ∧ IsAnalyticFieldFunction 𝒰 f ∧
        (∀ W ∈ 𝒰, ∃ (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k),
          (J : Edge L n k 0 → ComplexMatrix2) =
              leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ))
                (chosenProlongComp L n k k W) ∧
            (μ : Edge L n k k → ComplexMatrix2) = (chosenCriticalBranch L n k).energyGradient k W ∧
            BackgroundFunctionalWellDefined (chosenProlongComp L n k k W) J μ ∧
            f W = backgroundFunctional (chosenProlongComp L n k k W) J μ) ∧
        f (trivialField L n k k) =
          backgroundFunctional (trivialField L n k 0) 0 0
end Tower
end YangMills.Construction
end
