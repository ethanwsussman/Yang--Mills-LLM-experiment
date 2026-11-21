import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
abbrev WithNone (α : Type) : Type := Unit ⊕ α
def withNoneMeasure {α : Type} [MeasurableSpace α] (μ : Measure α) : Measure (WithNone α) :=
  Measure.map Sum.inl (Measure.dirac ()) + Measure.map Sum.inr μ
abbrev BlockOffset (L : ℕ) : Type := Fin 4 → Fin L
abbrev BlockBond (L : ℕ) : Type := BlockOffset L × Fin 4
structure BlockLabels (Ω : Type) (L : ℕ) where
  isCore : Bool
  badBond : BlockBond L → Bool
  siteLabel : BlockOffset L → WithNone Ω
  basePoint : BlockOffset L
  linkValue : BlockBond L → WithNone UnitQuaternion
abbrev CoarseLabel (Ω : Type) (L : ℕ) : Type := WithNone (BlockLabels Ω L)
def BlockLabels.toProd {Ω : Type} {L : ℕ} (s : BlockLabels Ω L) :
    Bool × (BlockBond L → Bool) × (BlockOffset L → WithNone Ω) × BlockOffset L ×
      (BlockBond L → WithNone UnitQuaternion) :=
  (s.isCore, s.badBond, s.siteLabel, s.basePoint, s.linkValue)
def BlockLabels.ofProd {Ω : Type} {L : ℕ}
    (p : Bool × (BlockBond L → Bool) × (BlockOffset L → WithNone Ω) × BlockOffset L ×
      (BlockBond L → WithNone UnitQuaternion)) :
    BlockLabels Ω L :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
instance instMeasurableSpaceBlockData {Ω : Type} [MeasurableSpace Ω] {L : ℕ} :
    MeasurableSpace (BlockLabels Ω L) :=
  MeasurableSpace.comap BlockLabels.toProd inferInstance
def blockConfigMeasure {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (L : ℕ) :
    Measure (BlockLabels Ω L) :=
  Measure.map BlockLabels.ofProd
    ((Measure.count : Measure Bool).prod ((Measure.count : Measure (BlockBond L → Bool)).prod
      ((Measure.pi fun _ : BlockOffset L => withNoneMeasure μ).prod
        ((Measure.count : Measure (BlockOffset L)).prod
          (Measure.pi fun _ : BlockBond L => withNoneMeasure haarUnit)))))
def coarseLabelMeasure {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (L : ℕ) :
    Measure (CoarseLabel Ω L) :=
  withNoneMeasure (blockConfigMeasure μ L)
end YangMills.Construction.TorusLumps
end
