import YangMills.Construction.ResponseInTheExpansion.GasOfAResponseAtColdFields
import YangMills.Construction.ResponseInTheExpansion.LawOfTheColdHalf
import YangMills.Construction.ResponseInTheExpansion.MeanInTheColdSetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps StepSettings StepGas RenormalizationStepParameters WeightedResponses BlockAverages ColdStepAtMirrorFrames
variable {R : StepSetup} {n : ℕ} [NeZero n]
def coldHalfLawOf (R : StepSetup) : ColdHalfLaw :=
  ⟨R.params.coupling, R.anchorRadius, R.ballRadius, R.coupling, R.params.rt, R.frameReach, R.barrierFn,
    localFamilyOfDensity R.density⟩
abbrev coldTopField (R : StepSetup) (V : TorusField n) :
    (torusFrame R.params.side R.depth n).GaugeField (torusFrame R.params.side R.depth n).top :=
  readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V
def coldExpectationAbove (R : StepSetup) (V : TorusField n) (G : TorusField (n * R.params.side) → ℝ) : ℝ :=
  (coldHalfLawOf R).expectation (coldTopField R V) fun k => G (coldFieldAboveFrames R V k)
def coldTermAbove (A : ResponseSetup R) (V : TorusField n) (Y : TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) : ℝ :=
  ∑ y ∈ sitesInBlocks R.params.side {Y},
      coldExpectationAbove R V (fun W => centeredResponse A.cold (n * R.params.side) y W h) +
    R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h *
      ∑ i : Fin 4, (coldExpectationAbove R V
          (fun W => bondScore R.params R.coupling W V (coldChartSetting R V).bases (Y, i)) +
        coldExpectationAbove R V
          (fun W => bondScore R.params R.coupling W V (coldChartSetting R V).bases (Y - TorusFields.unitStep n i, i)))
def coldStepAboveFramesStatement : Prop :=
  HoldsAtEveryStep fun T R A => T.ColdStepHolds → ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n →
    ∀ (Y : TorusSite n) (V : TorusField n),
    IsCold R.params.threshold V → ∀ h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n),
      A.coldStep n Y V h = coldTermAbove A V Y h + gasTermAtBlock A (coldCaseGround R V) Y h +
        ∑ y ∈ sitesInBlocks R.params.side {Y}, A.cold (n * R.params.side) y (trivialField (n * R.params.side)) h
end YangMills.Construction.ResponseInTheExpansion
end
