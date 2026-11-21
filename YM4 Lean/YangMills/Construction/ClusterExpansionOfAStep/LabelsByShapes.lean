import YangMills.Construction.ClusterExpansionOfAStep.LabelsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
abbrev BlockShape (L : ℕ) : Type :=
  Bool × (BlockBond L → Bool) × Finset (BlockOffset L) × BlockOffset L × Finset (BlockBond L)
variable {Ω : Type} {L : ℕ}
open Classical in
def BlockLabels.shape (s : BlockLabels Ω L) : BlockShape L :=
  (s.isCore, s.badBond, Finset.univ.filter (fun o => s.siteLabel o ≠ Sum.inl ()), s.basePoint,
    Finset.univ.filter fun c => s.linkValue c ≠ Sum.inl ())
def labelShape (l : CoarseLabel Ω L) : Option (BlockShape L) :=
  match l with
  | Sum.inl _ => none
  | Sum.inr s => some s.shape
def storedOffsets : Option (BlockShape L) → Finset (BlockOffset L)
  | none => ∅
  | some sh => sh.2.2.1
def storedBonds : Option (BlockShape L) → Finset (BlockBond L)
  | none => ∅
  | some sh => sh.2.2.2.2
open Classical in
def markOfShape (sh : BlockShape L) (a : sh.2.2.1 → Ω) (g : sh.2.2.2.2 → UnitQuaternion) : BlockLabels Ω L where
  isCore := sh.1
  badBond := sh.2.1
  siteLabel := fun o => if h : o ∈ sh.2.2.1 then Sum.inr (a ⟨o, h⟩) else Sum.inl ()
  basePoint := sh.2.2.2.1
  linkValue := fun c => if h : c ∈ sh.2.2.2.2 then Sum.inr (g ⟨c, h⟩) else Sum.inl ()
def labelOfShape : (sh : Option (BlockShape L)) →
    (storedOffsets sh → Ω) × (storedBonds sh → UnitQuaternion) → CoarseLabel Ω L
  | none, _ => Sum.inl ()
  | some sh, q => Sum.inr (markOfShape sh q.1 q.2)
abbrev ShapeLabelData (Ω : Type) {L : ℕ} {Y : Type} (σ : Y → Option (BlockShape L)) : Type :=
  (Σ y, storedOffsets (σ y)) → Ω
abbrev ShapeLinkData {L : ℕ} {Y : Type} (σ : Y → Option (BlockShape L)) : Type :=
  (Σ y, storedBonds (σ y)) → UnitQuaternion
def labelsOfShapes {Y : Type} (σ : Y → Option (BlockShape L)) (q : ShapeLabelData Ω σ × ShapeLinkData σ) :
    Y → CoarseLabel Ω L :=
  fun y => labelOfShape (σ y) (fun o => q.1 ⟨y, o⟩, fun c => q.2 ⟨y, c⟩)
def CoarseLabelMeasureByShapes : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ] (L : ℕ),
    SigmaFinite (coarseLabelMeasure μ L) ∧
    (StandardBorelSpace Ω → StandardBorelSpace (CoarseLabel Ω L)) ∧
    (∀ sh : Option (BlockShape L), MeasurableSet (labelShape (Ω := Ω) ⁻¹' {sh})) ∧
    ∀ (Y : Type) [Fintype Y] (σ : Y → Option (BlockShape L)),
      Measurable (labelsOfShapes (Ω := Ω) σ) ∧ Function.Injective (labelsOfShapes (Ω := Ω) σ) ∧
      Set.range (labelsOfShapes (Ω := Ω) σ) = {ω | ∀ y, labelShape (ω y) = σ y} ∧
      (Measure.pi fun _ : Y => coarseLabelMeasure μ L).restrict {ω | ∀ y, labelShape (ω y) = σ y} =
        ((Measure.pi fun _ : Σ y, storedOffsets (σ y) => μ).prod
          (Measure.pi fun _ : Σ y, storedBonds (σ y) => haarUnit)).map (labelsOfShapes σ)
end YangMills.Construction.TorusLumps
end
