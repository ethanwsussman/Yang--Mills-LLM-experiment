import YangMills.Construction.RunningCouplingSlope.CoordinatesOfTheStepsOfAChainForm
import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def TreeCoordsTransversalSlice : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
        ∀ W : Tower.Edge L n (k + 1) (k + 1) → Matrices.ComplexMatrix2, RepresentsTorusField W V →
        ∀ P : ChainPoint L n (k + 1), IsMinimizerOver a W P → RepresentsMinimizerChain a ρ V P →
          ∀ l : LevelForms L n (k + 1) →ₗ[ℝ] EuclideanSpace ℝ (TreeChainCoord L n (k + 1)),
            (∀ ξ e, l ξ e = transportCoords P ξ ⟨e.1, .inr e.2⟩) →
            IsTransversalSlice P l ∧ sliceOrbitVolume P l = c
end YangMills.Construction.RunningCouplingSlope
end
