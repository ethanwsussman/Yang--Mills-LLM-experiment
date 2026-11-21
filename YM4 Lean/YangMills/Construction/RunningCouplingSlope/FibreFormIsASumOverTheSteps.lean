import YangMills.Construction.RunningCouplingSlope.CoordinatesOfTheStepsOfAChainForm
import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
def FibreHessianSumOverSteps : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
        ∀ W : Tower.Edge L n (k + 1) (k + 1) → Matrices.ComplexMatrix2, RepresentsTorusField W V →
        ∀ P : ChainPoint L n (k + 1), IsMinimizerOver a W P → RepresentsMinimizerChain a ρ V P →
          ∃ N : Matrix (ChainCoord L n (k + 1)) (ChainCoord L n (k + 1)) ℝ,
            (∀ e e', coordLevel e' ≤ coordLevel e → N e e' = 0) ∧
            (∀ (m : Fin (k + 1)) (i : TreeCoord (frameAtStep L n (k + 1) m)) e',
              N ⟨m, .inr i⟩ e' = 0) ∧
            ∀ (ξ : LinearMap.ker (topDeriv P))
              (x : (m : Fin (k + 1)) → ReferenceDensity.ChartCoord (frameAtStep L n (k + 1) m) → ℝ),
              IsChartPlusGauge a ρ V P x (transportCoords P (ξ : LevelForms L n (k + 1)) -
                Matrix.mulVec N (transportCoords P (ξ : LevelForms L n (k + 1)))) →
              fibreHessian a P ξ = ∑ m : Fin (k + 1), dotProduct (x m)
                (Matrix.mulVec (chartHessianAtStep a ρ L n (k + 1) m V) (x m))
end RunningCouplingSlope
end YangMills.Construction
end
