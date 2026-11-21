import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace WeightedResponses
open TorusFields TorusLumps StepSettings StepGas BlockAverages
variable {R : StepSetup} {n : ℕ} [NeZero n]
def gasBlockMean (A : ResponseSetup R) (G : GasGround R n) (Y : TorusSite n)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) : ℝ :=
  ∑ y ∈ sitesInBlocks R.params.side {Y},
      G.expectation ∅ (fun ξ => chartResponse A (configSetting G ξ) y f) +
    R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y f *
      ∑ i : Fin 4, (G.expectation ∅ (fun ξ => chartBondScore (configSetting G ξ) (Y, i)) +
        G.expectation ∅ (fun ξ => chartBondScore (configSetting G ξ) (Y - TorusFields.unitStep n i, i)))
def coldStepIntegralEqGasMean : Prop :=
  HoldsAtEveryStep fun _ R A => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ (Y : TorusSite n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)),
    CaseIntegrable R G.cut G.coarse G.state (caseResponse A G.coarse Y f) ∧
    caseMean R G.cut G.coarse G.state (caseResponse A G.coarse Y f) =
      gasBlockMean A G Y f +
        ∑ y ∈ sitesInBlocks R.params.side {Y}, A.cold (n * R.params.side) y (trivialField (n * R.params.side)) f
end WeightedResponses
end YangMills.Construction
end
