import YangMills.Construction.ClusterExpansionOfAStep.ActionOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StepSettings
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.StepCosts
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
def CoarseState.restrict (q : CoarseState R n) (X : Finset (TorusSite n)) : CoarseState R n :=
  ⟨q.1 ∩ X, fun y => q.2 ⟨y, (Finset.mem_inter.mp y.2).1⟩⟩
open Classical in
def CoarseState.markedZone (q : CoarseState R n) : Finset (TorusSite n) :=
  q.1.filter fun y => (q.markAt y).isSome
open Classical in
def CoarseState.storedBadBonds (q : CoarseState R n) : Finset (TorusBond (n * R.params.side)) :=
  Finset.univ.filter fun b => ∃ s, q.markAt (parentBlock R.params.side b.1) = some s ∧
    s.badBond (siteOffset b.1, b.2) = true
open Classical in
def CoarseState.storedFieldBonds (q : CoarseState R n) : Finset (TorusBond (n * R.params.side)) :=
  Finset.univ.filter fun b => ∃ s, q.markAt (parentBlock R.params.side b.1) = some s ∧
    s.linkValue (siteOffset b.1, b.2) ≠ Sum.inl ()
open Classical in
def bondsOverBlocks (L : ℕ) [NeZero L] (Z : Finset (TorusSite n)) : Finset (TorusBond (n * L)) :=
  Finset.univ.filter fun b => parentBlock L b.1 ∈ Z ∧ parentBlock L (b.1 + TorusFields.unitStep (n * L) b.2) ∈ Z
def CoarseState.storedField (q : CoarseState R n) : TorusField (n * R.params.side) :=
  q.fieldWithStoredLinks (trivialField _)
def hotLumpsOn (ℓ : StepParameters) {m : ℕ} (S : Finset (TorusSite m)) (W : TorusField m) :
    Finset (Finset (TorusSite m)) :=
  open Classical in
  (hotLumps ℓ.grid ℓ.threshold (S.image (torusSiteInFrame (stepBlockFrame ℓ.side (m / ℓ.side)) 0))
    (readAtLevel (stepBlockFrame ℓ.side (m / ℓ.side)) 0 W)).image fun l => l.image (toTorusSite m)
def hotNeighbourhoodOn (R : StepSetup) (X : Finset (TorusSite n)) (V : TorusField n) : Finset (TorusSite n) :=
  thickening (2 * R.nextRange) ((hotLumpsOn R.params X V).biUnion id)
def frameHotLumps (ℓ : StepParameters) (S : Finset (TorusSite (n * ℓ.side))) (W : TorusField (n * ℓ.side)) :
    Finset (Finset ((stepBlockFrame ℓ.side n).Site 0)) :=
  open Classical in
  hotLumps ℓ.grid ℓ.threshold (S.image (torusSiteInFrame (stepBlockFrame ℓ.side n) 0))
    (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
def frameHotLumpSites (ℓ : StepParameters) (S : Finset (TorusSite (n * ℓ.side)))
    (W : TorusField (n * ℓ.side)) : Finset (Finset (TorusSite (n * ℓ.side))) :=
  open Classical in (frameHotLumps ℓ S W).image fun l => l.image (toTorusSite (n * ℓ.side))
open Classical in
def blockBaseWeight (ℓ : StepParameters) (h : Finset (Finset ((stepBlockFrame ℓ.side n).Site 0)))
    (y : (stepBlockFrame ℓ.side n).Cell) (z : (stepBlockFrame ℓ.side n).Site 0) : ℝ :=
  if z ∈ baseSitesAt ℓ.baseDepth h y then 1 / ((baseSitesAt ℓ.baseDepth h y).card : ℝ) else 0
structure CoarseState.IsAdmissibleCoarseState (C X : Finset (TorusSite n)) (p : CoarseState R n) : Prop where
  eq_thickening : X = thickening (R.nextRange / 2) p.markedZone
  isCore_eq : ∀ y s, p.markAt y = some s → s.isCore = (open Classical in decide (y ∈ C))
  subset_dataZone : C ⊆ p.markedZone
  badBonds_subset : p.storedBadBonds ⊆ markedBonds R C
  fieldBonds_eq : p.storedFieldBonds = bondsOverBlocks R.params.side p.markedZone
  attached_eq : (open Classical in attachedSites R.params.side R.range p.storedBadBonds p.labelSet C =
    p.storedBadBonds.image Prod.fst ∪ p.labelSet ∪ sitesInBlocks R.params.side C)
  storedBlocks_eq : storedBlocks R.params.side R.range p.storedBadBonds p.labelSet C = p.markedZone
  hotHull_subset : thickening (2 * R.range)
      ((frameHotLumpSites R.params (sitesInBlocks R.params.side p.markedZone) p.storedField).biUnion id) ⊆
    p.labelSet
  component_meets : ∀ Xc ∈ chainComponents R.range p.labelSet,
    ∃ l ∈ frameHotLumpSites R.params (sitesInBlocks R.params.side p.markedZone) p.storedField,
      (open Classical in (l ∩ Xc).Nonempty)
open Classical in
def admissibilityIndicator (V : TorusField n) (q : CoarseState R n) (X : Finset (TorusSite n)) : ℝ :=
  if (q.restrict X).IsAdmissibleCoarseState (hotNeighbourhoodOn R X V) X then 1 else 0
def clusterFactorProduct (q : CoarseState R n) (X : Finset (TorusSite n)) : ℝ :=
  ∏ Xc ∈ chainComponents R.range (q.restrict X).labelSet,
    R.clusterFactor (n * R.params.side) (q.restrict X).storedField (q.restrict X).labelSet
      (q.restrict X).labeling Xc
open Classical in
def markFactorProduct (V : TorusField n) (q : CoarseState R n) (X : Finset (TorusSite n)) : ℝ :=
  ∏ b ∈ markedBonds R (hotNeighbourhoodOn R X V) ∩ bondsOverBlocks R.params.side (q.restrict X).markedZone,
    if b ∈ (q.restrict X).storedBadBonds then 1 - bondMark R V (q.restrict X).storedField b
    else bondMark R V (q.restrict X).storedField b
def baseFactorProduct (q : CoarseState R n) (X : Finset (TorusSite n)) : ℝ :=
  ∏ y ∈ (q.restrict X).markedZone, match (q.restrict X).markAt y with
    | some s => blockBaseWeight R.params
        (frameHotLumps R.params (sitesInBlocks R.params.side (q.restrict X).markedZone) (q.restrict X).storedField)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 0 (blockSite y s.basePoint))
    | none => 1
def coarseFactor (V : TorusField n) (q : CoarseState R n) (X : Finset (TorusSite n)) : ℝ :=
  admissibilityIndicator V q X * clusterFactorProduct q X * markFactorProduct V q X * baseFactorProduct q X
variable (R)
def coarseFactorExpansion (m : ℕ) (V : TorusField m) (Y : Finset (TorusSite m))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) (X : Finset (TorusSite m)) : ℝ :=
  if h : m = 0 then 0 else
    haveI : NeZero m := ⟨h⟩
    coarseFactor V (⟨Y, ω⟩ : CoarseState R m) X
def coarseWeightExpansion (m : ℕ) (V : TorusField m) (Y : Finset (TorusSite m))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) : ℝ :=
  if h : m = 0 then 0 else
    haveI : NeZero m := ⟨h⟩
    coarseStateWeight R (hotCoreSites R V) V ⟨Y, ω⟩
variable {R} in
def CoarseState.baseChoice (q : CoarseState R n) : BaseChoice R.params.side n := fun y =>
  match q.markAt (toTorusSite n y) with
  | some s => torusSiteInFrame (stepBlockFrame R.params.side n) 0 (blockSite (toTorusSite n y) s.basePoint)
  | none => cellCentre (stepBlockFrame R.params.side n).depth y
variable {R} in
structure CoarseState.IsExtension (q : CoarseState R n) (C : Finset (TorusSite n))
    (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) : Prop where
  field_eq : ∀ c ∈ q.storedFieldBonds, W c.1 c.2 = q.storedField c.1 c.2
  mem_support_iff : ∀ z, z ∈ q.labelSet ↔ z ∈ Yt ∧ parentBlock R.params.side z ∈ q.markedZone
  labeling_eq : ∀ z (hz : z ∈ Yt) (hz' : z ∈ q.labelSet), ωt ⟨z, hz⟩ = q.labeling ⟨z, hz'⟩
  mem_badBonds_iff : ∀ c, c ∈ q.storedBadBonds ↔ c ∈ bad ∧ parentBlock R.params.side c.1 ∈ q.markedZone
  baseOffset_eq : ∀ y s, q.markAt y = some s → baseOffset R b y = s.basePoint
  far_badBonds : ∀ c ∈ bad, parentBlock R.params.side c.1 ∉ q.markedZone →
    ∀ u ∈ q.storedBadBonds.image Prod.fst ∪ q.labelSet ∪ sitesInBlocks R.params.side C,
      10 * R.range < supDist c.1 u
  far_support : ∀ z ∈ Yt, parentBlock R.params.side z ∉ q.markedZone →
    ∀ u ∈ q.storedBadBonds.image Prod.fst ∪ q.labelSet ∪ sitesInBlocks R.params.side C,
      10 * R.range < supDist z u
structure StepSetup.IsWellPosed : Prop where
  hasExpansions : R.HasExpansions
  admissible : R.params.Admissible
  isCutoff : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn
  range_le : R.range ≤ R.nextRange + 1
  nextRange_le : R.nextRange ≤ R.range + 1
  nextRange_ge : 2 ^ 16 ≤ R.nextRange
  range_ge_side : 2 ^ 40 * R.params.side ≤ R.range
  range_ge_base : 4 * R.params.n₀ + 2 ^ 16 ≤ R.range
  coupling_pos : 0 < R.coupling
  functional_spec : ∀ n [NeZero n], R.params.n₀ ≤ n → Measurable (R.functional n) ∧
    (∀ W, 0 ≤ R.functional n W) ∧
    (∀ (g : TorusSite n → UnitQuaternion) (W : TorusField n),
      R.functional n (gaugeTransform g W) = R.functional n W) ∧
    ∀ (g : TorusIsometry) (W W' : TorusField n), g.Transports W W' → R.functional n W' = R.functional n W
end YangMills.Construction.StepSettings
end
