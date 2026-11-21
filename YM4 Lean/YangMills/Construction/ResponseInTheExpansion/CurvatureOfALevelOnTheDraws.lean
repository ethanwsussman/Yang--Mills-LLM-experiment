import YangMills.Construction.ClusterExpansionOfAStep.MarksOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.AxialRotationsOfATop
import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ResponseInTheExpansion
open Classical
variable {ℓ : TorusLumps.StepParameters}
def sampleBelow (ℓ : TorusLumps.StepParameters) (s : ℕ) :
    (d n : ℕ) → WeightedResponses.MarkedSample ℓ (s + d) n →
      WeightedResponses.MarkedSample ℓ s (WeightedResponses.fineSide ℓ.side d n)
  | 0, _, u => u
  | d + 1, n, u => sampleBelow ℓ s d (n * ℓ.side) u.1
def siteAbove (L : ℕ) : (d n : ℕ) → TorusFields.TorusSite (WeightedResponses.fineSide L d n) → TorusFields.TorusSite n
  | 0, _, o => o
  | d + 1, n, o => TorusLumps.parentBlock L (siteAbove L d (n * L) o)
def supBall {n : ℕ} [NeZero n] (o : TorusFields.TorusSite n) (r : ℝ) : Finset (TorusFields.TorusSite n) :=
  Finset.univ.filter fun z => (TorusFields.supDist z o : ℝ) ≤ r
def ballRadius (L : ℕ) (nn ρ₀ : ℝ) (j : ℕ) : ℝ := 20 * nn / (L : ℝ) ^ j + 4 * ρ₀
def responseOfLieForm (a ρA : ℝ) (L u : ℕ) [NeZero L] {n : ℕ} [NeZero n]
    (B : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) :
    TorusFields.TorusBond (n * L) → BlockAverages.imaginaryQuaternions :=
  fun b => ∑ c : TorusFields.TorusBond n, WeightedResponses.responseKernel a ρA L u b c • B c
def lieFormCurl {m : ℕ} (B : TorusFields.TorusBond m → BlockAverages.imaginaryQuaternions)
    (p : TorusFields.TorusPlaquette m) : BlockAverages.imaginaryQuaternions :=
  B (p.1, p.2.1) + B (p.1 + TorusFields.unitStep m p.2.1, p.2.2) -
    B (p.1 + TorusFields.unitStep m p.2.2, p.2.1) - B (p.1, p.2.2)
def blockTreeGauge (ℓ : TorusLumps.StepParameters) {n : ℕ} (W : TorusFields.TorusField (n * ℓ.side))
    (x : TorusFields.TorusSite (n * ℓ.side)) : BlockAverages.UnitQuaternion :=
  LumpContours.axialGauge 1 (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0 W)
    (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 0 x)
def deviationInGauge (T : WeightedResponses.StageTower ℓ) (t : ℕ) {n : ℕ} [NeZero n]
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (Z : Finset (TorusFields.TorusSite n))
    (V : TorusFields.TorusField n) (W : TorusFields.TorusField (n * ℓ.side))
    (b : TorusFields.TorusBond (n * ℓ.side)) : BlockAverages.imaginaryQuaternions :=
  if TorusLumps.parentBlock ℓ.side b.1 ∈ Z ∧ b ∈ StepCosts.chartBonds ℓ.side n then
    ColdStepAtMirrorFrames.adjointAction (g (TorusLumps.parentBlock ℓ.side b.1))
      (StepMarks.frameDeviation ℓ (T.stage t).anchorRadius t (T.stage t).toStepSetup.frameReach V W b)
  else 0
def descendedForm (T : WeightedResponses.StageTower ℓ) (k : ℕ) (nn ρ₀ : ℝ) :
    (d n : ℕ) → [NeZero n] → WeightedResponses.MarkedSample ℓ (k + d) n →
      TorusFields.TorusSite (WeightedResponses.fineSide ℓ.side d n) →
      (TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) →
      (TorusFields.TorusSite n → BlockAverages.UnitQuaternion) →
      TorusFields.TorusBond (WeightedResponses.fineSide ℓ.side d n) → BlockAverages.imaginaryQuaternions
  | 0, _, _, _, _, B, _ => B
  | d + 1, n, _, u, o, B, g =>
    descendedForm T k nn ρ₀ d (n * ℓ.side) u.1 o
      (fun b => responseOfLieForm ℓ.coupling (T.stage (k + d)).anchorRadius ℓ.side (k + d) B b +
        deviationInGauge T (k + d) g
          (supBall (siteAbove ℓ.side (d + 1) n o) (ballRadius ℓ.side nn ρ₀ (d + 1) - 3 * ρ₀)) u.2.2.1
          (WeightedResponses.topField ℓ (k + d) (n * ℓ.side) u.1) b)
      (fun x => g (TorusLumps.parentBlock ℓ.side x) *
        blockTreeGauge ℓ (WeightedResponses.topField ℓ (k + d) (n * ℓ.side) u.1) x)
def axialGaugeAt (ℓ : TorusLumps.StepParameters) {n : ℕ} (V : TorusFields.TorusField n)
    (o z : TorusFields.TorusSite n) : BlockAverages.UnitQuaternion :=
  ColdStepAtMirrorFrames.axialGaugeHolonomy (F := TorusLumps.stepBlockFrame ℓ.side n)
    (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 V)
    (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o)
    (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 z)
def gaugeTransform {n : ℕ} (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion)
    (V : TorusFields.TorusField n) (b : TorusFields.TorusBond n) : BlockAverages.UnitQuaternion :=
  g b.1 * V b.1 b.2 * (g (b.1 + TorusFields.unitStep n b.2))⁻¹
def topLogForm (ℓ : TorusLumps.StepParameters) {n : ℕ} [NeZero n] (V : TorusFields.TorusField n)
    (o : TorusFields.TorusSite n) (r s : ℝ) (b : TorusFields.TorusBond n) : BlockAverages.imaginaryQuaternions :=
  if b.1 ∈ supBall o r ∧ ∀ z ∈ supBall o r, ∀ μ ν : Fin 4, TorusFields.curvature V z μ ν ≤ s then
    LumpContours.minimalLog (gaugeTransform (axialGaugeAt ℓ V o) V b)
  else 0
def descendedCurvature (T : WeightedResponses.StageTower ℓ) (k M : ℕ) (nn ρ₀ s : ℝ) (n : ℕ) [NeZero n]
    (u : WeightedResponses.MarkedSample ℓ (k + M) n)
    (o : TorusFields.TorusSite (WeightedResponses.fineSide ℓ.side M n))
    (p : TorusFields.TorusPlaquette (WeightedResponses.fineSide ℓ.side M n)) : BlockAverages.imaginaryQuaternions :=
  lieFormCurl (descendedForm T k nn ρ₀ M n u o
    (topLogForm ℓ (WeightedResponses.topField ℓ (k + M) n u) (siteAbove ℓ.side M n o)
      (ballRadius ℓ.side nn ρ₀ M) s)
    (axialGaugeAt ℓ (WeightedResponses.topField ℓ (k + M) n u) (siteAbove ℓ.side M n o))) p
def FreeCoresAvoid (R : StepSettings.StepSetup) {n : ℕ} [NeZero n]
    (Yt : Finset (TorusFields.TorusSite (n * R.params.side)))
    (bad : Finset (TorusFields.TorusBond (n * R.params.side))) (C Z : Finset (TorusFields.TorusSite n)) : Prop :=
  ∀ X ∈ TorusLumps.clusterComponents R.params.side R.range bad Yt C,
    ¬ (X ∩ TorusLumps.sitesInBlocks R.params.side C).Nonempty →
    Disjoint (TorusLumps.coreBlocks R.params.side R.range X) Z
def StepsAvoidOrigin (T : WeightedResponses.StageTower ℓ) (k : ℕ) (m : ℝ) :
    (d n : ℕ) → [NeZero n] → WeightedResponses.MarkedSample ℓ (k + d) n →
      TorusFields.TorusSite (WeightedResponses.fineSide ℓ.side d n) → Prop
  | 0, _, _, _, _ => True
  | d + 1, n, _, u, o =>
    StepsAvoidOrigin T k m d (n * ℓ.side) u.1 o ∧
      FreeCoresAvoid (T.stage (k + d)).toStepSetup
        (WeightedResponses.stageState T (k + d) (n * ℓ.side) u.1).2.1 u.2.2.2
        (StepSettings.hotCoreSites (T.stage (k + d)).toStepSetup u.2.2.1)
        (supBall (siteAbove ℓ.side (d + 1) n o) m)
def IsLocalEvent (T : WeightedResponses.StageTower ℓ) (k M : ℕ) (m : ℝ) (n : ℕ) [NeZero n]
    (u : WeightedResponses.MarkedSample ℓ (k + M + M) n)
    (o : TorusFields.TorusSite (WeightedResponses.fineSide ℓ.side M (WeightedResponses.fineSide ℓ.side M n))) : Prop :=
  Disjoint (WeightedResponses.stageState T (k + M + M) n u).2.1
      (supBall (siteAbove ℓ.side M n (siteAbove ℓ.side M (WeightedResponses.fineSide ℓ.side M n) o)) m) ∧
    StepsAvoidOrigin T (k + M) m M n u (siteAbove ℓ.side M (WeightedResponses.fineSide ℓ.side M n) o) ∧
    StepsAvoidOrigin T k m M (WeightedResponses.fineSide ℓ.side M n)
      (sampleBelow ℓ (k + M) M n u) o
end ResponseInTheExpansion
end YangMills.Construction
end
