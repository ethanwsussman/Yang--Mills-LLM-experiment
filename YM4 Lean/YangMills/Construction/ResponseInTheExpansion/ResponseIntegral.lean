import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.TorusFields YangMills.Construction.StepSettings YangMills.Construction.StepCosts
variable {R : StepSetup} {n : ℕ} [NeZero n]
def fieldBlockResponse (A : ResponseSetup R) (V : TorusField n) (Y : TorusSite n)
    (W : TorusField (n * R.params.side)) : ℝ :=
  ∑ b : BaseChoice R.params.side n, baseLaw (R := R) W b *
    (∏ c : (TorusLumps.stepBlockFrame R.params.side n).Cell × Fin 4,
      TorusLumps.bondKernel R.params R.coupling
        (readAtLevel (TorusLumps.stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (TorusLumps.stepBlockFrame R.params.side n) 1 V) b c) *
    (∑ y ∈ TorusLumps.sitesInBlocks R.params.side {Y},
        responseMass R.params R.depth R.coupling R.labels R.labelWeight A.hull (n * R.params.side) y W +
      R.params.coupling / 2 * A.coeff * blockBondScores W V b Y * R.functional (n * R.params.side) W)
def blockResponseIntegral (A : ResponseSetup R) (V : TorusField n) (Y : TorusSite n) : ℝ :=
  ∫ W : TorusField (n * R.params.side), fieldBlockResponse A V Y W ∂(fieldHaar (n * R.params.side))
end YangMills.Construction.WeightedResponses
end
