import YangMills.Construction.ClusterExpansionOfAStep.ClusterDefs
import YangMills.Construction.ClusterExpansionOfAStep.LabelsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.StepSettings
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps StepCosts
variable (R : StepSetup) {n : ℕ}
def hotCoreSites [NeZero n] (V : TorusField n) : Finset (TorusSite n) :=
  thickening (2 * R.nextRange) (torusHotSites R.params V)
def bondMark (V : TorusField n) (W : TorusField (n * R.params.side)) (b : TorusBond (n * R.params.side)) : ℝ :=
  cutoffFactor R.ballRadius R.barrierFn
    ‖((chartCoord R.params V W b : imaginaryQuaternions) : ℍ[ℝ]) -
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ])‖
section Offsets
variable {L : ℕ}
def blockSite (y : TorusSite n) (o : BlockOffset L) : TorusSite (n * L) :=
  siteOfInt fun i => (L : ℤ) * ((y i).cast : ℤ) + (((o i : ℕ) : ℤ) - ((L : ℤ) - 1) / 2)
def siteOffset [NeZero L] (x : TorusSite (n * L)) : BlockOffset L :=
  fun i => Fin.ofNat L (((((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) % (L : ℤ)).toNat)
end Offsets
variable [NeZero n]
def markedBonds (C : Finset (TorusSite n)) : Finset (TorusBond (n * R.params.side)) :=
  open Classical in (chartBonds R.params.side n).filter fun b => parentBlock R.params.side b.1 ∉ C
def markProduct (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (bad : Finset (TorusBond (n * R.params.side))) : ℝ :=
  open Classical in
  ∏ b ∈ markedBonds R C, if b ∈ bad then 1 - bondMark R V W b else bondMark R V W b
def baseOffset (b : BaseChoice R.params.side n) (y : TorusSite n) : BlockOffset R.params.side :=
  siteOffset (toTorusSite (n * R.params.side)
    (b (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)))
def blockConfigAt (C Z : Finset (TorusSite n)) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) (y : TorusSite n) :
    BlockLabels R.labels.Ω R.params.side :=
  open Classical in
  { isCore := decide (y ∈ C)
    badBond := fun q => decide ((blockSite y q.1, q.2) ∈ bad)
    siteLabel := fun o => if h : blockSite y o ∈ Yt then Sum.inr (ωt ⟨_, h⟩) else Sum.inl ()
    basePoint := baseOffset R b y
    linkValue := fun q =>
      if parentBlock R.params.side (blockSite (L := R.params.side) y q.1 + TorusFields.unitStep (n * R.params.side) q.2) ∈ Z
      then Sum.inr (W (blockSite y q.1) q.2) else Sum.inl () }
abbrev CoarseState (n : ℕ) : Type := Σ Y : Finset (TorusSite n), (Y → CoarseLabel R.labels.Ω R.params.side)
def coarseStateOf (C : Finset (TorusSite n)) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) : CoarseState R n :=
  open Classical in
  ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, fun y =>
    if (y : TorusSite n) ∈ storedBlocks R.params.side R.range bad Yt C then
      Sum.inr (blockConfigAt R C (storedBlocks R.params.side R.range bad Yt C) W Yt ωt bad b y)
    else Sum.inl ()⟩
variable {R}
def CoarseState.markAt (q : CoarseState R n) (y : TorusSite n) :
    Option (BlockLabels R.labels.Ω R.params.side) :=
  open Classical in
  if h : y ∈ q.1 then (match q.2 ⟨y, h⟩ with
    | Sum.inr s => some s
    | Sum.inl _ => none) else none
def CoarseState.fieldWithStoredLinks (q : CoarseState R n) (W : TorusField (n * R.params.side)) :
    TorusField (n * R.params.side) := fun x i =>
  match q.markAt (parentBlock R.params.side x) with
  | some s => (match s.linkValue (siteOffset x, i) with
    | Sum.inr g => g
    | Sum.inl _ => W x i)
  | none => W x i
def CoarseState.labelAt (q : CoarseState R n) (z : TorusSite (n * R.params.side)) : WithNone R.labels.Ω :=
  match q.markAt (parentBlock R.params.side z) with
  | some s => s.siteLabel (siteOffset z)
  | none => Sum.inl ()
open Classical in
def CoarseState.unlabelled (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side))) :
    Finset (TorusSite (n * R.params.side)) :=
  Yt.filter fun z => q.labelAt z = Sum.inl ()
def CoarseState.fillLabels (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side)))
    (ν : q.unlabelled Yt → R.labels.Ω) : Yt → R.labels.Ω :=
  open Classical in fun z =>
    match hz : q.labelAt (z : TorusSite (n * R.params.side)) with
    | Sum.inr a => a
    | Sum.inl _ => ν ⟨z, Finset.mem_filter.mpr ⟨z.2, by rw [hz]⟩⟩
def baseLaw (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) : ℝ :=
  open Classical in
  if b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)
  then 1 / ((baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)).card : ℝ) else 0
variable (R)
def stepWeight (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) : ℝ :=
  R.labelWeight (n * R.params.side) W Yt ωt * baseLaw W b *
    (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
      bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) *
    markProduct R C V W bad
open Classical in
def coarseStateMass (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) : ENNReal :=
  ∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
    ∑ b : BaseChoice R.params.side n,
    ∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
      (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
          coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
        ENNReal.ofReal (stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) else 0)
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
def coarseStateWeight (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) : ℝ :=
  (coarseStateMass R C V q).toReal
end YangMills.Construction.StepSettings
end
