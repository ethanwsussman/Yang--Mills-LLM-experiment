import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsOfAStep
import YangMills.Construction.ResponseInTheExpansion.LocalChainAboveALevel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages LumpContours ColdStepAtMirrorFrames WeightedResponses TorusFields TorusLumps StepSettings StepMarks
  MarkedIntegrals RenormalizationStepParameters
open Classical
variable {ℓ : TorusLumps.StepParameters}
def localChainDepth (ℓ : TorusLumps.StepParameters) (β : ℝ) (k : ℕ) : ℕ := chainDepth (flowCouplings ℓ β k)
def localBlockSide (ℓ : TorusLumps.StepParameters) (β : ℝ) (k : ℕ) : ℕ :=
  ⌊flowCouplings ℓ β k ^ ((1 : ℝ) / 20)⌋₊
def localLogScale (ℓ : TorusLumps.StepParameters) (β : ℝ) (k : ℕ) : ℝ := logCubeScale (flowCouplings ℓ β k)
def finsetSupNonneg {α : Type} (S : Finset α) (f : α → ℝ) : ℝ := S.fold max 0 f
def maxCurvatureOnBall {n : ℕ} [NeZero n] (W : TorusField n) (o : TorusSite n) (r : ℝ) : ℝ :=
  finsetSupNonneg (plaquettesIn (supBall o r)) fun p => curvature W p.1 p.2.1 p.2.2
def IsColdOnBall {n : ℕ} [NeZero n] (s : ℝ) (V : TorusField n) (o : TorusSite n) (r : ℝ) : Prop :=
  ∀ p ∈ plaquettesIn (supBall o r), curvature V p.1 p.2.1 p.2.2 < s
def stepDeviation (T : StageTower ℓ) (t : ℕ) {n : ℕ} (V : TorusField n) (W : TorusField (n * ℓ.side))
    (b : TorusBond (n * ℓ.side)) : imaginaryQuaternions :=
  frameDeviation ℓ (T.stage t).anchorRadius t (T.stage t).toStepSetup.frameReach V W b
def maxDeviationOnBall (T : StageTower ℓ) (t : ℕ) {n : ℕ} [NeZero n] (V : TorusField n)
    (W : TorusField (n * ℓ.side)) (o : TorusSite n) (r : ℝ) : ℝ :=
  finsetSupNonneg (chartBondsInBlocks ℓ.side (supBall o r)) fun b =>
    ‖(stepDeviation T t V W b : Quaternion ℝ)‖
def levelSumOnBall (T : StageTower ℓ) (t : ℕ) (nn ρ₀ : ℝ) :
    (d n : ℕ) → [NeZero n] → MarkedSample ℓ (t + d) n → TorusSite (fineSide ℓ.side d n) → ℝ
  | 0, _, _, _, _ => 0
  | d + 1, n, _, u, o =>
    maxCurvatureOnBall u.2.2.1 (siteAbove ℓ.side (d + 1) n o) (ballRadius ℓ.side nn ρ₀ (d + 1)) +
      maxDeviationOnBall T (t + d) u.2.2.1 (topField ℓ (t + d) (n * ℓ.side) u.1) (siteAbove ℓ.side (d + 1) n o)
        (ballRadius ℓ.side nn ρ₀ d / (ℓ.side : ℝ) + 2) +
      levelSumOnBall T t nn ρ₀ d (n * ℓ.side) u.1 o
def IsLocalEventFrom (T : StageTower ℓ) (t d d' : ℕ) (m : ℝ) (n : ℕ) [NeZero n]
    (u : MarkedSample ℓ (t + d + d') n) (o : TorusSite (fineSide ℓ.side d (fineSide ℓ.side d' n))) : Prop :=
  Disjoint (stageState T (t + d + d') n u).2.1
      (supBall (siteAbove ℓ.side d' n (siteAbove ℓ.side d (fineSide ℓ.side d' n) o)) m) ∧
    StepsAvoidOrigin T (t + d) m d' n u (siteAbove ℓ.side d (fineSide ℓ.side d' n) o) ∧
    StepsAvoidOrigin T t m d (fineSide ℓ.side d' n) (sampleBelow ℓ (t + d) d' n u) o
def ballLog {n : ℕ} [NeZero n] (g : TorusSite n → UnitQuaternion) (W : TorusField n) (o : TorusSite n) (r : ℝ)
    (b : TorusBond n) : imaginaryQuaternions :=
  if b.1 ∈ supBall o r then minimalLog (gaugeTransform g W b) else 0
def restrictGauge {n : ℕ} (g : TorusSite n → UnitQuaternion) (Z : Finset (TorusSite n)) (x : TorusSite n) :
    UnitQuaternion :=
  if x ∈ Z then g x else 1
def gaugeDescent (k : ℕ) : (d n : ℕ) → [NeZero n] → MarkedSample ℓ (k + d) n →
    (TorusSite n → UnitQuaternion) → TorusSite (fineSide ℓ.side d n) → UnitQuaternion
  | 0, _, _, _, g => g
  | d + 1, n, _, u, g =>
    gaugeDescent k d (n * ℓ.side) u.1
      (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ (topField ℓ (k + d) (n * ℓ.side) u.1) x)
structure IsNearIdentity {n : ℕ} [NeZero n] (g : TorusSite n → UnitQuaternion) (V : TorusField n)
    (o : TorusSite n) (r s : ℝ) : Prop where
  log_le : ∀ b : TorusBond n, b.1 ∈ supBall o r → ‖(minimalLog (gaugeTransform g V b) : Quaternion ℝ)‖ ≤ s
  curvature_le : ∀ p ∈ plaquettesIn (supBall o r), curvature V p.1 p.2.1 p.2.2 ≤ s
def upperSigma (T : StageTower ℓ) (t : ℕ) : (d n : ℕ) → [NeZero n] → MeasurableSpace (MarkedSample ℓ (t + d) n)
  | 0, n, _ => stageSigma T t n
  | d + 1, n, _ =>
    (upperSigma T t d (n * ℓ.side)).comap (fun u : MarkedSample ℓ (t + d + 1) n => u.1) ⊔
      (inferInstance : MeasurableSpace (StepOutcome ℓ n)).comap (fun u : MarkedSample ℓ (t + d + 1) n => u.2)
def StepAvoids (T : StageTower ℓ) (t : ℕ) {n : ℕ} [NeZero n] (m : ℝ) (o : TorusSite n)
    (u : MarkedSample ℓ (t + 1) n) : Prop :=
  FreeCoresAvoid (T.stage t).toStepSetup (stageState T t (n * ℓ.side) u.1).2.1 u.2.2.2
    (hotCoreSites (T.stage t).toStepSetup u.2.2.1) (supBall o m)
end YangMills.Construction.ResponseInTheExpansion
end
