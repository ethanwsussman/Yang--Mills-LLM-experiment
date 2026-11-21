import YangMills.Construction.ClusterExpansionOfAStep.BasesAtABlock
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps StepSettings
namespace StepSettings
variable {R : StepSetup} {n : ℕ}
section Labels
variable [NeZero n]
open Classical in
def CoarseState.labelSet (q : CoarseState R n) : Finset (TorusSite (n * R.params.side)) :=
  Finset.univ.filter fun z => q.labelAt z ≠ Sum.inl ()
open Classical in
def CoarseState.labeling (q : CoarseState R n) : q.labelSet → R.labels.Ω := fun z =>
  match hz : q.labelAt (z : TorusSite (n * R.params.side)) with
  | Sum.inr a => a
  | Sum.inl _ => absurd hz (Finset.mem_filter.mp z.2).2
end Labels
end StepSettings
namespace ClusterExpansionOfAStep
variable {R : StepSetup} {n : ℕ}
section Labels
variable [NeZero n]
def gaugeOnCoarseState (q : CoarseState R n) (g : TorusSite n → UnitQuaternion) (y : TorusSite n)
    (s : BlockLabels R.labels.Ω R.params.side) : BlockLabels R.labels.Ω R.params.side :=
  open Classical in
  { s with
    siteLabel := fun o =>
      if h : blockSite y o ∈ q.labelSet then
        Sum.inr (R.labels.act q.labelSet (blockConstantGauge R.params.side g) q.labeling ⟨_, h⟩)
      else s.siteLabel o
    linkValue := fun c => match s.linkValue c with
      | Sum.inr w => Sum.inr (blockConstantGauge R.params.side g (blockSite y c.1) * w *
          (blockConstantGauge R.params.side g (blockSite y c.1 + TorusFields.unitStep (n * R.params.side) c.2))⁻¹)
      | Sum.inl u => Sum.inl u }
def coarseGaugeAct (Y : Finset (TorusSite n)) (g : TorusSite n → UnitQuaternion)
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) : Y → CoarseLabel R.labels.Ω R.params.side := fun y =>
  match ω y with
  | Sum.inr s => Sum.inr (gaugeOnCoarseState (R := R) ⟨Y, ω⟩ g y s)
  | Sum.inl u => Sum.inl u
end Labels
variable (R)
structure CoarseLabelFacts : Prop where
  standardBorel : StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side)
  sigmaFinite : SigmaFinite (coarseLabelMeasure R.labels.μ R.params.side)
  measurable_act : ∀ {n : ℕ} [NeZero n] (Y : Finset (TorusSite n)),
    Measurable fun p : (TorusSite n → UnitQuaternion) × (Y → CoarseLabel R.labels.Ω R.params.side) =>
      coarseGaugeAct (R := R) Y p.1 p.2
  act_one : ∀ {n : ℕ} [NeZero n] (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel R.labels.Ω R.params.side),
    coarseGaugeAct (R := R) Y (fun _ => 1) ω = ω
  act_mul : ∀ {n : ℕ} [NeZero n] (Y : Finset (TorusSite n)) (g g' : TorusSite n → UnitQuaternion)
    (ω : Y → CoarseLabel R.labels.Ω R.params.side),
    coarseGaugeAct (R := R) Y (g * g') ω = coarseGaugeAct (R := R) Y g (coarseGaugeAct (R := R) Y g' ω)
  measurePreserving_act : ∀ {n : ℕ} [NeZero n] (Y : Finset (TorusSite n)) (g : TorusSite n → UnitQuaternion),
    MeasurePreserving (coarseGaugeAct (R := R) Y g)
      (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)
      (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)
  act_local : ∀ {n : ℕ} [NeZero n] (Y Y' : Finset (TorusSite n)) (g g' : TorusSite n → UnitQuaternion)
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) (ω' : Y' → CoarseLabel R.labels.Ω R.params.side)
    (y : TorusSite n) (hy : y ∈ Y) (hy' : y ∈ Y'),
    (∀ z, supDist z y ≤ 1 → g z = g' z) → (∀ z, supDist z y ≤ 1 → (z ∈ Y ↔ z ∈ Y')) →
    (∀ z (hz : z ∈ Y) (hz' : z ∈ Y'), supDist z y ≤ 1 → ω ⟨z, hz⟩ = ω' ⟨z, hz'⟩) →
    coarseGaugeAct (R := R) Y g ω ⟨y, hy⟩ = coarseGaugeAct (R := R) Y' g' ω' ⟨y, hy'⟩
  act_free : ∀ {n : ℕ} [NeZero n] (Y : Finset (TorusSite n)) (g : TorusSite n → UnitQuaternion)
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) (y : Y),
    (∀ z, supDist z (y : TorusSite n) ≤ 1 → g z = 1) → coarseGaugeAct (R := R) Y g ω y = ω y
def coarseLabelSpace (h : CoarseLabelFacts R) : LabelSpace where
  Ω := CoarseLabel R.labels.Ω R.params.side
  sbΩ := h.standardBorel
  μ := coarseLabelMeasure R.labels.μ R.params.side
  sfμ := h.sigmaFinite
  act := fun Y g ω => coarseGaugeAct (R := R) Y g ω
  act_borel := h.measurable_act
  act_one := h.act_one
  act_mul := h.act_mul
  act_keeps := h.measurePreserving_act
  act_local := h.act_local
  act_free := h.act_free
end ClusterExpansionOfAStep
end YangMills.Construction
end
