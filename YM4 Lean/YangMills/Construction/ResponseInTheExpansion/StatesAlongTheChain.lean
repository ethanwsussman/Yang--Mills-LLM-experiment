import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.LabelDataOfAStep
import YangMills.Construction.ResponseInTheExpansion.CurvatureOnTheBareTorus
import YangMills.Construction.ResponseInTheExpansion.JointLawOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction
namespace WeightedResponses
open TorusFields TorusLumps StepSettings StepCosts
variable {ℓ : TorusLumps.StepParameters}
structure ChainStage (ℓ : TorusLumps.StepParameters) where
  depth : ℕ
  coupling : ℝ
  nextCoupling : ℝ
  functional : TorusFunctional
  density : LocalDensity
  labels : LabelSpace
  labelWeight : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → labels.Ω) → ℝ
  clusterFactor : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → labels.Ω) → Finset (TorusSite n) → ℝ
  siteDensity : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → labels.Ω) → ℝ
  anchorRadius : ℝ
  barrierFn : ℝ → ℝ
@[reducible] def ChainStage.toStepSetup (c : ChainStage ℓ) : StepSetup :=
  ⟨ℓ, c.depth, c.coupling, c.nextCoupling, c.functional, c.density, c.labels, c.labelWeight, c.clusterFactor,
    c.siteDensity, c.anchorRadius, c.barrierFn⟩
def ChainStage.next (c : ChainStage ℓ) (h : ClusterExpansionOfAStep.CoarseLabelFacts c.toStepSetup) (x'' : ℝ) (f' : LocalDensity)
    (φ' : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → CoarseLabel c.labels.Ω ℓ.side) → ℝ) :
    ChainStage ℓ where
  depth := c.depth + 1
  coupling := c.nextCoupling
  nextCoupling := x''
  functional := kernelImage ℓ c.coupling c.functional
  density := f'
  labels := ClusterExpansionOfAStep.coarseLabelSpace c.toStepSetup h
  labelWeight := coarseWeightExpansion c.toStepSetup
  clusterFactor := coarseFactorExpansion c.toStepSetup
  siteDensity := φ'
  anchorRadius := c.anchorRadius
  barrierFn := c.barrierFn
structure StageTower (ℓ : TorusLumps.StepParameters) where
  base : ChainStage ℓ
  basePoint : base.labels.Ω
  couplings : ℕ → ℝ
  densities : ℕ → LocalDensity
  siteDensities : (R : StepSetup) → (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) →
    (Y → CoarseLabel R.labels.Ω R.params.side) → ℝ
  labelFacts : ClusterExpansionOfAStep.CoarseLabelsStandard
  two_le_side : 2 ≤ ℓ.side
def StageTower.stage (T : StageTower ℓ) : ℕ → ChainStage ℓ
  | 0 => T.base
  | t + 1 => (T.stage t).next (T.labelFacts _ T.two_le_side) (T.couplings t) (T.densities t)
      (T.siteDensities (T.stage t).toStepSetup)
def BondSet (m : ℕ) : Type := Finset (TorusBond m)
instance bondSetMeasurableSpace (m : ℕ) : MeasurableSpace (BondSet m) := ⊤
def markLaw (R : StepSetup) {n : ℕ} [NeZero n] (W : TorusField (n * R.params.side)) (V : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side))) : ℝ :=
  open Classical in
  if R.params.side ∣ n ∧ 64 ≤ n then
    if bad ⊆ markedBonds R (hotCoreSites R V) then markProduct R (hotCoreSites R V) V W bad else 0
  else if bad = ∅ then 1 else 0
def StageTower.MarksMeasurable (T : StageTower ℓ) : Prop :=
  ∀ (s n : ℕ) [NeZero n] (bad : Finset (TorusBond (n * ℓ.side))),
    Measurable fun p : TorusField (n * ℓ.side) × TorusField n => markLaw (T.stage s).toStepSetup p.1 p.2 bad
abbrev StepOutcome (ℓ : TorusLumps.StepParameters) (n : ℕ) : Type :=
  BaseChoice ℓ.side n × TorusField n × BondSet (n * ℓ.side)
def stepReferenceMeasure (ℓ : TorusLumps.StepParameters) (n : ℕ) [NeZero n] : Measure (StepOutcome ℓ n) :=
  (Measure.count : Measure (BaseChoice ℓ.side n)).prod
    ((fieldHaar n).prod (Measure.count : Measure (BondSet (n * ℓ.side))))
def stepOutcomeDensity (R : StepSetup) {n : ℕ} [NeZero n] (W : TorusField (n * R.params.side))
    (d : StepOutcome R.params n) : ℝ :=
  stepTransitionDensity R.params R.coupling W d.1 d.2.1 * markLaw R W d.2.1 d.2.2
def MarkedSample (ℓ : TorusLumps.StepParameters) : ℕ → ℕ → Type
  | 0, n => TorusField n
  | s + 1, n => MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n
instance markedSampleMeasurableSpace (ℓ : TorusLumps.StepParameters) : (s n : ℕ) → MeasurableSpace (MarkedSample ℓ s n)
  | 0, n => inferInstanceAs (MeasurableSpace (TorusField n))
  | s + 1, n =>
    letI := markedSampleMeasurableSpace ℓ s (n * ℓ.side)
    inferInstanceAs (MeasurableSpace (MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n))
def topField (ℓ : TorusLumps.StepParameters) : (s n : ℕ) → MarkedSample ℓ s n → TorusField n
  | 0, _, W => W
  | _ + 1, _, u => u.2.2.1
def bottomField (ℓ : TorusLumps.StepParameters) : (s n : ℕ) → MarkedSample ℓ s n → TorusField (fineSide ℓ.side s n)
  | 0, _, W => W
  | s + 1, n, u => bottomField ℓ s (n * ℓ.side) u.1
def forgetMarks (ℓ : TorusLumps.StepParameters) : (s n : ℕ) → MarkedSample ℓ s n → ChainSample ℓ s n
  | 0, _, W => W
  | s + 1, n, u => (forgetMarks ℓ s (n * ℓ.side) u.1, u.2.1, u.2.2.1)
def markedSampleLaw (T : StageTower ℓ) (β : ℝ) : (s n : ℕ) → [NeZero n] → Measure (MarkedSample ℓ s n)
  | 0, n, _ => wilsonLaw β n
  | s + 1, n, _ =>
    letI := markedSampleMeasurableSpace ℓ s (n * ℓ.side)
    ((markedSampleLaw T β s (n * ℓ.side)).prod (stepReferenceMeasure ℓ n)).withDensity fun u =>
      ENNReal.ofReal (stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2)
abbrev StageState (T : StageTower ℓ) (s n : ℕ) : Type :=
  TorusField n × (Σ Y : Finset (TorusSite n), (Y → (T.stage s).labels.Ω))
def stageState (T : StageTower ℓ) : (s n : ℕ) → [NeZero n] → MarkedSample ℓ s n → StageState T s n
  | 0, _, _, W => (W, ⟨thickening (2 * clusterRange T.base.coupling) (torusHotSites ℓ W), fun _ => T.basePoint⟩)
  | s + 1, n, _, u =>
    (u.2.2.1, coarseStateOf (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1)
      (stageState T s (n * ℓ.side) u.1).1 (stageState T s (n * ℓ.side) u.1).2.1
      (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1)
@[reducible] def stageSigma (T : StageTower ℓ) (s n : ℕ) [NeZero n] : MeasurableSpace (MarkedSample ℓ s n) :=
  MeasurableSpace.comap (stageState T s n) inferInstance
def stepSourceTerm (ℓ : TorusLumps.StepParameters) (x al : ℝ) (s : ℕ) {n : ℕ} [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n))
    (W : TorusField (n * ℓ.side)) (d : StepOutcome ℓ n) : ℝ :=
  ℓ.coupling / 2 * al * ∑ Y : TorusSite n, blockMean ℓ.side (s + 1) n Y h *
    ∑ i : Fin 4, (bondScore ℓ x W d.2.1 d.1 (Y, i) + bondScore ℓ x W d.2.1 d.1 (Y - TorusFields.unitStep n i, i))
def sourceTerm (T : StageTower ℓ) (al : ℕ → ℝ) (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n))
    (u : MarkedSample ℓ (s + 1) n) : ℝ :=
  stepSourceTerm ℓ (T.stage s).coupling (al s) s h (topField ℓ s (n * ℓ.side) u.1) u.2
def response (T : StageTower ℓ) (β : ℝ) (al : ℕ → ℝ) :
    (s n : ℕ) → [NeZero n] → PlaquetteWeight (fineSide ℓ.side s n) → MarkedSample ℓ s n → ℝ
  | 0, _, _, h, W => curvatureObservable h W
  | s + 1, n, _, h, u =>
    ((markedSampleLaw T β (s + 1) n)[fun u : MarkedSample ℓ (s + 1) n =>
      response T β al s (n * ℓ.side) h u.1 + sourceTerm T al s n h u | stageSigma T (s + 1) n]) u
def stepSum (T : StageTower ℓ) (β : ℝ) (al : ℕ → ℝ) (s n : ℕ) [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) (u : MarkedSample ℓ (s + 1) n) : ℝ :=
  response T β al s (n * ℓ.side) h u.1 + sourceTerm T al s n h u
def stepCovarianceTerm (T : StageTower ℓ) (β : ℝ) (al : ℕ → ℝ) (s n : ℕ) [NeZero n]
    (h₁ h₂ : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) : ℝ :=
  ∫ u, (((markedSampleLaw T β (s + 1) n)[fun u => stepSum T β al s n h₁ u * stepSum T β al s n h₂ u |
        stageSigma T (s + 1) n]) u -
      ((markedSampleLaw T β (s + 1) n)[stepSum T β al s n h₁ | stageSigma T (s + 1) n]) u *
        ((markedSampleLaw T β (s + 1) n)[stepSum T β al s n h₂ | stageSigma T (s + 1) n]) u)
      ∂(markedSampleLaw T β (s + 1) n) -
    ∫ u, sourceTerm T al s n h₁ u * sourceTerm T al s n h₂ u ∂(markedSampleLaw T β (s + 1) n)
def covarianceSum (T : StageTower ℓ) (β : ℝ) (al : ℕ → ℝ) :
    (s n : ℕ) → [NeZero n] → PlaquetteWeight (fineSide ℓ.side s n) → PlaquetteWeight (fineSide ℓ.side s n) → ℝ
  | 0, _, _, _, _ => 0
  | s + 1, n, _, h₁, h₂ => covarianceSum T β al s (n * ℓ.side) h₁ h₂ + stepCovarianceTerm T β al s n h₁ h₂
end WeightedResponses
end YangMills.Construction
end
