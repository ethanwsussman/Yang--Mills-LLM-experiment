import YangMills.Construction.RunningCouplingSlope.ColdnessTheChainReaches
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames Interpolation ReferenceDensity ColdChain
def energyAtMinimizerDerivBoundStatement : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ D : ℕ → ℕ → ℝ, (∀ l j, 0 < D l j) ∧
      ∀ (F : BlockFrame) (s : ℝ) (V : F.GaugeField F.top), IsBlockTorus L F → IsReachableColdness c L s →
        IsSmallCurvature s V → ∀ (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
          (u : Fin l → EuclideanSpace ℝ (Fin 3)) (e : Fin j → F.Site F.top × Fin 4)
          (X : Fin j → imaginaryQuaternions),
          2 ≤ l → (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
          ContDiffAt ℝ (l + j : ℕ)
            (jointDisplacement (fun ζ V' => chartedEnergyAtMinimizer a c.ρA V' ζ) 0 V b u e X) 0 ∧
          |jointMixedDeriv (fun ζ V' => chartedEnergyAtMinimizer a c.ρA V' ζ) 0 V b u e X| ≤
            D l j * Real.exp (-(c.δ₁ / 4 * cellSetDiameter (chordBondCells b ∪ topBondCells e)))
end YangMills.Construction.RunningCouplingSlope
end
