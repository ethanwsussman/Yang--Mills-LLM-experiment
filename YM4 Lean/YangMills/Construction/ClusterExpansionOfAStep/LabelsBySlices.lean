import YangMills.Construction.ClusterExpansionOfAStep.LabelsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SlicedLabels
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages
open scoped Classical in
def fillOn {ι α : Type} (A : Finset ι) (v : A → α) : ι → WithNone α := fun i =>
  if h : i ∈ A then Sum.inr (v ⟨i, h⟩) else Sum.inl ()
def sliceLabel {ι Ω : Type} {L : ℕ} (Z : Finset ι) (core : Z → Bool) (badBits : Z → BlockBond L → Bool)
    (o : Z → BlockOffset L) (A : Finset (Z × BlockOffset L)) (B : Finset (Z × BlockBond L))
    (g : B → UnitQuaternion) (ω : A → Ω) : ι → CoarseLabel Ω L :=
  fillOn Z fun y =>
    { isCore := core y
      badBond := badBits y
      siteLabel := fun k => fillOn A ω (y, k)
      basePoint := o y
      linkValue := fun q => fillOn B g (y, q) }
def blockDataCount (L : ℕ) : ℕ :=
  2 * (2 * (2 ^ Fintype.card (BlockBond L) * (Fintype.card (BlockOffset L) *
    (2 ^ Fintype.card (BlockBond L) * 2 ^ Fintype.card (BlockOffset L)))))
def SliceBoundStatement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ] (L : ℕ) [NeZero L] (ι : Type) [Fintype ι]
    (F : (ι → CoarseLabel Ω L) → ENNReal) (c : ENNReal),
    (∀ (Z : Finset ι) (core : Z → Bool) (badBits : Z → BlockBond L → Bool) (o : Z → BlockOffset L)
      (A : Finset (Z × BlockOffset L)) (B : Finset (Z × BlockBond L)) (g : B → UnitQuaternion),
      ∫⁻ ω : A → Ω, F (sliceLabel Z core badBits o A B g ω) ∂(Measure.pi fun _ => μ) ≤ c) →
    ∫⁻ ν, F ν ∂(Measure.pi fun _ : ι => coarseLabelMeasure μ L) ≤
      ((blockDataCount L ^ Fintype.card ι : ℕ) : ENNReal) * c
end YangMills.Construction.SlicedLabels
end
