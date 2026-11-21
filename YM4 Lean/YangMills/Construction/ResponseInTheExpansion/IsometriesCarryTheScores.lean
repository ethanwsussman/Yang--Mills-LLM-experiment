import YangMills.Construction.ClusterExpansionOfAStep.IsometriesCarryTheKernel
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.StepCosts YangMills.Construction.StepSettings YangMills.Construction.BlockAverages
def isometriesPreserveScoresStatement : Prop :=
  ∀ (R : StepSetup), R.params.Admissible → ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ g : TorusIsometry,
    (∀ z : TorusSite (n * R.params.side),
      parentBlock R.params.side ((g.scaledLift R.params.side).mapSite z) = g.mapSite (parentBlock R.params.side z)) ∧
    ∃ e : BaseChoice R.params.side n ≃ BaseChoice R.params.side n,
      ∀ (W W' : TorusField (n * R.params.side)) (V V' : TorusField n),
      (g.scaledLift R.params.side).Transports W W' → g.Transports V V' → ∀ b : BaseChoice R.params.side n,
      baseLaw (R := R) W' (e b) * (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
          bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W')
            (readAtLevel (stepBlockFrame R.params.side n) 1 V') (e b) c) =
        baseLaw (R := R) W b * (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
          bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
            (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) ∧
      (baseLaw (R := R) W b ≠ 0 → ∀ Y : TorusSite n,
        blockBondScores (R := R) W' V' (e b) (g.mapSite Y) = blockBondScores (R := R) W V b Y)
end YangMills.Construction.WeightedResponses
end
