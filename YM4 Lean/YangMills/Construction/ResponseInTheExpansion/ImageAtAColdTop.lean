import YangMills.Construction.ResponseInTheExpansion.GasOfAResponseAtColdFields
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open StepGas StepSettings TorusFields TorusLumps WeightedResponses
variable {R : StepSetup} {n : ℕ} [NeZero n]
def coldImagePart (A : ResponseSetup R) (G : GasGround R n) (Y : TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) : ℝ :=
  ∑ y ∈ sitesInBlocks R.params.side {Y}, chartResponse A G.groundSetting y h +
    R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h *
      ∑ i : Fin 4, (chartBondScore G.groundSetting (Y, i) + chartBondScore G.groundSetting (Y - unitStep n i, i))
def coldImageDecompositionStatement : Prop :=
  HoldsAtEveryStep fun _ R A => ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (Y : TorusSite n) (V : TorusField n),
    IsCold R.params.threshold V → ∀ h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n),
      A.coldStep n Y V h = coldImagePart A (coldCaseGround R V) Y h + gasTermAtBlock A (coldCaseGround R V) Y h +
        ∑ y ∈ sitesInBlocks R.params.side {Y}, A.cold (n * R.params.side) y (trivialField (n * R.params.side)) h
end YangMills.Construction.ResponseInTheExpansion
end
