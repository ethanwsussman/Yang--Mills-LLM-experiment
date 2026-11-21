import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrame
import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExponentsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ComparisonOnABlock
import YangMills.Construction.ColdStepAtMirrorFrames.ExponentsCompareOnTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheMeansOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.FreezingOnOneTorus
import YangMills.Construction.ColdStepAtMirrorFrames.TermsInFixedVariables
import YangMills.Construction.ColdStepAtMirrorFrames.TransportOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
def freezingThreshold (lam S c : ℝ) : ℝ :=
  c ^ 2 * (2 * freezingConstant lam S + 2 * blockComparisonConstant lam S)
def exponentConstantThreshold (T : StepParameters) (S : ℝ) : ℝ :=
  freezingThreshold T.chainParams.lam S (T.Ct + T.chainParams.lam + 1) +
    2 * (T.Ct + T.chainParams.lam + 1) * (32 * S ^ 2 / T.chainParams.lam + 1) *
      Real.exp (T.κ * T.blockIndex / 2 ^ 7)
def expansionConstantThreshold (T : StepParameters) (S : ℝ) : ℝ :=
  freezingThreshold T.chainParams.lam S ((T.Ct + 1) * (1 + T.energyRatio * (T.L : ℝ) ^ 4)) +
    2 * T.E * Real.exp (T.κ * T.blockIndex / 2 ^ 7)
def BoundsExpWeights (T : StepParameters) (S : ℝ) : Prop :=
  ∀ (F : BlockFrame) (n : ℕ), F.blockSide = T.L → 2 ≤ n → (∀ i, F.extent i = n) → ∀ z : F.Cell,
    ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(T.κ / 4 * blockDist F (bondBlock F b) z)) ≤ S ∧
      ∑ z' ∈ finiteCells F, Real.exp (-(T.κ / 4 * blockDist F z' z)) ≤ S
def stepFreezingStatement : Prop :=
  ∀ (T : StepParameters) (S : ℝ), T.IsOrdered → 1 ≤ T.blockIndex → 2 ≤ T.n₀ → 0 ≤ T.Ct → 1 ≤ T.coupling →
    0 < T.chainParams.lam →
    BoundsExpWeights T S → exponentConstantThreshold T S ≤ T.Cs → expansionConstantThreshold T S ≤ T.CE →
    CellExponentsBoundedAt T → CentredExpansionsBoundedAt T → ExponentsConvexAt T →
    CellExponentsCloseForParameters T → expansionTransportAt T →
    ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
      (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) (star : Bool), T.coupling ≤ x →
      IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → IsCubicTopTorus T.L t T.n₀ F →
      IsCubicTopTorus T.L t T.n₀ F' →
      IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
      AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
      MeansLocalize star T.a T.chainParams.ρA T.ballRadius T.chainParams.lam x T.κ T.Cs T.CE (frameRadius x) T.p
        f V V' Y Y' r
end YangMills.Construction.ColdStepAtMirrorFrames
end
