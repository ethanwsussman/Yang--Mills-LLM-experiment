import YangMills.Construction.ClusterExpansionOfAStep.LabelDataOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfGivenShapes
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps StepSettings
namespace ClusterExpansionOfAStep
variable {R : StepSetup} {n : ℕ} [NeZero n]
section Facts
variable (hS : CoarseLabelMeasureByShapes)
include hS
theorem measurableSet_labelShape_eq (Y : Finset (TorusSite n)) (σ : Y → Option (BlockShape R.params.side)) :
    MeasurableSet {ω : Y → CoarseLabel R.labels.Ω R.params.side | ∀ y, labelShape (ω y) = σ y} := by
  have h := (hS R.labels.Ω R.labels.μ R.params.side).2.2.1
  have : {ω : Y → CoarseLabel R.labels.Ω R.params.side | ∀ y, labelShape (ω y) = σ y} =
      Set.pi univ fun y => labelShape ⁻¹' {σ y} := by
    ext ω
    simp
  rw [this]
  exact MeasurableSet.univ_pi fun y => h (σ y)
theorem measurable_coarseGaugeAct (Y : Finset (TorusSite n)) :
    Measurable fun p : (TorusSite n → UnitQuaternion) × (Y → CoarseLabel R.labels.Ω R.params.side) =>
      coarseGaugeAct (R := R) Y p.1 p.2 := by
  classical
  have hh := hS R.labels.Ω R.labels.μ R.params.side
  have hsb : StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side) := hh.2.1 inferInstance
  intro E hE
  have hcover : (fun p : (TorusSite n → UnitQuaternion) × (Y → CoarseLabel R.labels.Ω R.params.side) =>
      coarseGaugeAct (R := R) Y p.1 p.2) ⁻¹' E =
      ⋃ σ : Y → Option (BlockShape R.params.side),
        (Prod.map id (labelsOfShapes (Ω := R.labels.Ω) σ)) ''
          ((fun r : (TorusSite n → UnitQuaternion) × (ShapeLabelData R.labels.Ω σ × ShapeLinkData σ) =>
            labelsOfShapes σ (shapeGaugeAct Y σ r.1 r.2)) ⁻¹' E) := by
    ext ⟨g, ω⟩
    simp only [mem_preimage, mem_iUnion, mem_image, Prod.exists, Prod.map_apply, id_eq, Prod.mk.injEq]
    constructor
    · intro h
      let σ : Y → Option (BlockShape R.params.side) := fun y => labelShape (ω y)
      have hr : ω ∈ range (labelsOfShapes (Ω := R.labels.Ω) σ) := by
        rw [(hh.2.2.2 Y σ).2.2.1]
        exact fun y => rfl
      obtain ⟨p, hp⟩ := hr
      refine ⟨σ, g, p.1, p.2, ?_, rfl, hp⟩
      simp only [Prod.mk.eta]
      rw [← coarseGaugeAct_labelsOfShapes, hp]
      exact h
    · rintro ⟨σ, g', a, b, h, rfl, rfl⟩
      rw [coarseGaugeAct_labelsOfShapes]
      exact h
  rw [hcover]
  refine MeasurableSet.iUnion fun σ => ?_
  have hfill := (hh.2.2.2 Y σ).1
  have hinj := (hh.2.2.2 Y σ).2.1
  have hemb : MeasurableEmbedding
      (Prod.map (id : (TorusSite n → UnitQuaternion) → _) (labelsOfShapes (Ω := R.labels.Ω) σ)) :=
    Measurable.measurableEmbedding (measurable_id.prodMap hfill)
      (Function.injective_id.prodMap hinj)
  refine hemb.measurableSet_image.mpr ?_
  exact (hfill.comp (measurable_shapeGaugeAct Y σ)) hE
theorem measurePreserving_coarseGaugeAct (Y : Finset (TorusSite n)) (g : TorusSite n → UnitQuaternion) :
    MeasurePreserving (coarseGaugeAct (R := R) Y g)
      (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)
      (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) := by
  classical
  have hh := hS R.labels.Ω R.labels.μ R.params.side
  have hm : Measurable (coarseGaugeAct (R := R) Y g) :=
    (measurable_coarseGaugeAct hS Y).comp (measurable_const.prodMk measurable_id)
  refine ⟨hm, Measure.ext fun E hE => ?_⟩
  rw [Measure.map_apply hm hE]
  set P := Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side with hP
  let sh : (Y → CoarseLabel R.labels.Ω R.params.side) → (Y → Option (BlockShape R.params.side)) :=
    fun ω y => labelShape (ω y)
  have hfib : ∀ σ, sh ⁻¹' {σ} = {ω | ∀ y, labelShape (ω y) = σ y} := by
    intro σ
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    exact funext_iff
  have hsplit : ∀ A : Set (Y → CoarseLabel R.labels.Ω R.params.side), MeasurableSet A →
      P A = ∑ σ : Y → Option (BlockShape R.params.side),
        (P.restrict {ω | ∀ y, labelShape (ω y) = σ y}) A := by
    intro A hA
    have h := sum_measure_preimage_singleton (μ := P.restrict A)
      (Finset.univ : Finset (Y → Option (BlockShape R.params.side)))
      (f := sh) (fun σ _ => by rw [hfib]; exact measurableSet_labelShape_eq hS Y σ)
    have hu : sh ⁻¹' ((Finset.univ : Finset (Y → Option (BlockShape R.params.side))) : Set _) = univ := by simp
    rw [hu, Measure.restrict_apply_univ] at h
    rw [← h]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hfib, Measure.restrict_apply (measurableSet_labelShape_eq hS Y σ), Measure.restrict_apply hA, inter_comm]
  rw [hsplit _ (hm hE), hsplit _ hE]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hlaw := (hh.2.2.2 Y σ).2.2.2
  have hfill := (hh.2.2.2 Y σ).1
  rw [hlaw, Measure.map_apply hfill (hm hE), Measure.map_apply hfill hE]
  have hc : labelsOfShapes (Ω := R.labels.Ω) σ ⁻¹' (coarseGaugeAct (R := R) Y g ⁻¹' E) =
      shapeGaugeAct Y σ g ⁻¹' (labelsOfShapes (Ω := R.labels.Ω) σ ⁻¹' E) := by
    ext p
    simp only [mem_preimage]
    rw [coarseGaugeAct_labelsOfShapes]
  rw [hc]
  exact (measurePreserving_shapeGaugeAct Y σ g).measure_preimage (hfill hE).nullMeasurableSet
end Facts
theorem coarseLabelsStandard_holds (hS : CoarseLabelMeasureByShapes) : CoarseLabelsStandard := by
  intro R hL
  have hh := hS R.labels.Ω R.labels.μ R.params.side
  exact
    { standardBorel := hh.2.1 inferInstance
      sigmaFinite := hh.1
      measurable_act := fun Y => measurable_coarseGaugeAct hS Y
      act_one := coarseGaugeAct_one
      act_mul := coarseGaugeAct_mul
      measurePreserving_act := fun Y g => measurePreserving_coarseGaugeAct hS Y g
      act_local := fun Y Y' g g' ω ω' y hy hy' => coarseGaugeAct_local hL Y Y' g g' ω ω' y hy hy'
      act_free := fun Y g ω y => coarseGaugeAct_of_trivial_near hL Y g ω y }
end ClusterExpansionOfAStep
end YangMills.Construction
end
