import YangMills.Construction.RunningCouplingSlope.CoordinatesOfTheStepsOfAChainForm
import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Classical in
def ExistsLevelFormMap : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
        ∀ W : Tower.Edge L n (k + 1) (k + 1) → Matrices.ComplexMatrix2, RepresentsTorusField W V →
        ∀ P : ChainPoint L n (k + 1), IsMinimizerOver a W P → RepresentsMinimizerChain a ρ V P →
          ∃ A : Matrix (ChainCoord L n (k + 1)) (ChainCoord L n (k + 1)) ℝ,
            A.det = Real.exp (∑ m : Fin (k + 1), ∑ e,
              ColdStepAtMirrorFrames.haarLogRatio (minimizerCoordAtStep a ρ L n (k + 1) m V e)) ∧
            ∀ u : ChainCoord L n (k + 1) → ℝ,
              IsChartPlusGauge a ρ V P (fun m i => u ⟨m, .inl i⟩) (Matrix.mulVec A u) ∧
              ∀ (m : Fin (k + 1)) (i : TreeCoord (frameAtStep L n (k + 1) m)),
                Matrix.mulVec A u ⟨m, .inr i⟩ = u ⟨m, .inr i⟩
end YangMills.Construction.RunningCouplingSlope
end
