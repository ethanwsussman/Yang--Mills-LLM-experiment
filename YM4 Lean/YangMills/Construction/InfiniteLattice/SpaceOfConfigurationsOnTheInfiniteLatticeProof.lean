import YangMills.Construction.InfiniteLattice.FactsFromTopologyMeasureAndFunctionTheoryProof
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsOnTheInfiniteLattice
import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsAtACutoffProof
import YangMills.Construction.Matrices.UnitaryLogarithmClosedForm
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
noncomputable section
namespace YangMills.Construction.InfiniteLattice.GaugeFieldSpace
open YangMills.Construction.InfiniteLattice YangMills.Construction.CutoffLattice YangMills.Construction.Matrices
variable {a : ℝ}
theorem continuous_eval_link (b : Link a) : Continuous fun U : GaugeField a => U b := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.continuous_eval_link <;> assumption
theorem continuous_of_forall_link {X : Type*} [TopologicalSpace X] {f : X → GaugeField a}
    (h : ∀ b, Continuous fun x => f x b) : Continuous f := by apply _root_.YangMills.Construction.InfiniteLattice.FieldSpace.continuous_of_forall_link <;> assumption
theorem continuous_of_forall_positiveLink {X : Type*} [TopologicalSpace X]
    {f : X → GaugeField a}
    (h : ∀ b ∈ positiveLinks a, Continuous fun x => f x b) : Continuous f := by
  refine continuous_of_forall_link fun b => ?_
  rcases mem_positiveLinks_or_opposite_mem b with hb | hb
  · exact h b hb
  · have hU : ∀ x, (f x b.opposite)⁻¹ = f x b := fun x => by
      have h' := (f x).2 b.opposite
      rw [Link.opposite_opposite] at h'
      exact h'.symm
    exact Continuous.congr (h _ hb).inv hU
theorem countable_link (a : ℝ) : Countable (Link a) := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.countable_link <;> assumption
theorem secondCountableTopology_specialUnitary :
    SecondCountableTopology ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
theorem compactSpace_gaugeField (a : ℝ) : CompactSpace (GaugeField a) := by apply _root_.YangMills.SharedProofs.p823 <;> assumption
theorem t2Space_gaugeField (a : ℝ) : T2Space (GaugeField a) :=
  inferInstanceAs
    (T2Space {U : Link a → ComplexMatrix2.specialUnitary // ∀ b, U b.opposite = (U b)⁻¹})
theorem secondCountableTopology_gaugeField (a : ℝ) :
    SecondCountableTopology (GaugeField a) := by
  have := countable_link a
  have := secondCountableTopology_specialUnitary
  exact TopologicalSpace.Subtype.secondCountableTopology
    {U : Link a → ComplexMatrix2.specialUnitary | ∀ b, U b.opposite = (U b)⁻¹}
theorem metrizableSpace_gaugeField (a : ℝ) :
    TopologicalSpace.MetrizableSpace (GaugeField a) := by apply _root_.YangMills.Construction.InfiniteLattice.AmbientFacts.Proofs.metrizableSpace_gaugeField <;> assumption
theorem positiveLinks_countable (a : ℝ) : (positiveLinks a).Countable := by
  have := countable_link a
  exact Set.to_countable _
theorem positiveLinks_infinite (ha : 0 < a) : (positiveLinks a).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℤ => Link.forwardFrom (n • axisStep a 0) 0) ?_ fun n => ⟨_, _, rfl⟩
  intro n n' h
  have h1 : n • axisStep a 0 = n' • axisStep a 0 := congrArg Link.initial h
  have h2 : (n : ℝ) * a = (n' : ℝ) * a := by
    have := congrFun (congrArg Subtype.val h1) 0
    simpa [axisStep] using this
  exact_mod_cast mul_right_cancel₀ ha.ne' h2
theorem continuous_valuesOnPositive :
    Continuous (valuesOnPositive : GaugeField a → positiveLinks a → ComplexMatrix2.specialUnitary) :=
  continuous_pi fun b => continuous_eval_link (b : Link a)
theorem productStructure_holds (ha : 0 < a) : ProductStructure a := by
  have := compactSpace_gaugeField a
  have := t2Space_gaugeField a
  refine ⟨positiveLinks_countable a, positiveLinks_infinite ha,
    xor_mem_positiveLinks ha, ?_, compactSpace_gaugeField a,
    metrizableSpace_gaugeField a⟩
  have hcont : Continuous (fieldEquivValues ha) := continuous_valuesOnPositive
  exact (hcont.homeoOfEquivCompactToT2).isHomeomorph
theorem measurable_borel_comp_continuous {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {g : X → Y}
    (hg : Continuous g) {h : Y → ℝ} (hh : Measurable[borel Y] h) :
    Measurable[borel X] (h ∘ g) := by
  let _ : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  let _ : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  exact hh.comp hg.measurable
theorem agreesOnAndOff_gluedField (ha : 0 < a) {S : Set (Link a)}
    (hS : S ⊆ positiveLinks a) (V : LinkVariables S) (U : GaugeField a) :
    AgreesOnAndOff S V U (gluedField ha hS V U) :=
  ⟨gluedField_apply_of_mem ha hS V U, fun _ hb => gluedField_apply_of_notMem ha hS V U hb⟩
theorem continuous_of_agreesOnAndOff {S : Set (Link a)}
    (c : LinkVariables S × GaugeField a → GaugeField a)
    (hc : ∀ V U, AgreesOnAndOff S V U (c (V, U))) : Continuous c := by
  refine continuous_of_forall_positiveLink fun b hb => ?_
  by_cases hbS : b ∈ S
  · have h : (fun x : LinkVariables S × GaugeField a => x.1 ⟨b, hbS⟩) = fun x => c x b :=
      funext fun x => ((hc x.1 x.2).1 ⟨b, hbS⟩).symm
    rw [← h]
    exact (continuous_apply _).comp continuous_fst
  · have h : (fun x : LinkVariables S × GaugeField a => x.2 b) = fun x => c x b :=
      funext fun x => ((hc x.1 x.2).2 b ⟨hb, hbS⟩).symm
    rw [← h]
    exact (continuous_eval_link b).comp continuous_snd
theorem finiteLinkSplicing_holds (ha : 0 < a) : FiniteLinkSplicing a := by
  intro S _ hS
  set e : LinkVariables S → GaugeField a :=
    fun V => gluedField ha hS V (trivialField a) with he
  have hecont : Continuous e :=
    (continuous_of_agreesOnAndOff (fun x => gluedField ha hS x.1 x.2)
      fun V U => agreesOnAndOff_gluedField ha hS V U).comp
      (continuous_id.prodMk continuous_const)
  have hre : ∀ V, restrictField (e V) S = V := fun V =>
    funext fun b => gluedField_apply_of_mem ha hS V _ b
  have hrcont : Continuous fun U : GaugeField a => restrictField U S :=
    continuous_pi fun b => continuous_eval_link (b : Link a)
  refine ⟨fun V U => ⟨gluedField ha hS V U, agreesOnAndOff_gluedField ha hS V U,
      fun W hW => eq_gluedField ha hS V U W hW.1 hW.2⟩,
    continuous_of_agreesOnAndOff,
    fun F => ⟨⟨fun hF => ⟨F ∘ e, fun U => ?_⟩, ?_⟩, fun hF => ⟨?_, ?_⟩⟩⟩
  · refine hF.2 U _ ?_
    exact (hre (restrictField U S)).symm
  · rintro ⟨f, hf⟩
    exact ⟨hS, fun U U' h => (hf U).trans ((congrArg f h).trans (hf U').symm)⟩
  · refine ⟨F ∘ e, fun U => hF.2 U _ (hre (restrictField U S)).symm, fun f' hf' => ?_⟩
    funext V
    have := hf' (e V)
    rw [hre] at this
    exact this.symm
  · intro f hf
    have hFe : f = F ∘ e := by
      funext V
      have := hf (e V)
      rw [hre] at this
      exact this.symm
    have hFr : F = f ∘ fun U : GaugeField a => restrictField U S := funext hf
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
    · rw [hFe]
      exact h.comp hecont
    · rw [hFr]
      exact h.comp hrcont
    · rw [hFe]
      exact measurable_borel_comp_continuous hecont h
    · rw [hFr]
      exact measurable_borel_comp_continuous hrcont h
theorem continuous_faceHolonomy (p : ElementaryPlaquette a) :
    Continuous fun U : GaugeField a => faceHolonomy U p := by
  unfold faceHolonomy
  exact (((continuous_eval_link _).mul (continuous_eval_link _)).mul
    (continuous_eval_link _).inv).mul (continuous_eval_link _).inv
theorem faceEnergyProperties_holds (hT : ComplexMatrix2.UnitaryLogarithmProperties) (a : ℝ) :
    FaceEnergyProperties a := by
  intro p
  refine ⟨?_, fun U => ?_, ?_, fun U U' h => ?_⟩
  · unfold faceEnergy
    have h : Continuous fun U : GaugeField a => (faceHolonomy U p : ComplexMatrix2) :=
      continuous_subtype_val.comp (continuous_faceHolonomy p)
    have htr : Continuous fun U : GaugeField a =>
        ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2) :=
      h.matrix_trace
    exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp htr))
  · obtain ⟨t, ⟨h₁, h₂⟩, ht⟩ := (hT.2.1 _ (faceHolonomy U p).2).1
    have h : (1 / 2) * (ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2)).re = t := by
      have := congrArg Complex.re ht
      simpa [ComplexMatrix2.halfTrace, Complex.mul_re] using this
    unfold faceEnergy
    rw [h]
    constructor <;> linarith
  · rintro b (rfl | rfl | rfl | rfl)
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  · have hb : ∀ b ∈ ({PeriodicExtensions.firstEdge p, PeriodicExtensions.secondEdge p,
        PeriodicExtensions.thirdEdge p, PeriodicExtensions.fourthEdge p} : Set (Link a)),
        U b = U' b := fun b hb => congrFun h ⟨b, hb⟩
    have hv : faceHolonomy U p = faceHolonomy U' p := by
      rw [PeriodicExtensions.faceHolonomy_eq_edges,
        PeriodicExtensions.faceHolonomy_eq_edges, hb _ (by simp), hb _ (by simp),
        hb _ (by simp), hb _ (by simp)]
    exact congrArg
      (fun g : ComplexMatrix2.specialUnitary =>
        1 - (1 / 2) * (ComplexMatrix2.fullTrace (g : ComplexMatrix2)).re) hv
theorem dependsOnlyOn_mono {E : Type*} {F : GaugeField a → E} {S T : Set (Link a)}
    (h : DependsOnlyOn F S) (hST : S ⊆ T) (hT : T ⊆ positiveLinks a) : DependsOnlyOn F T :=
  ⟨hT, fun U U' hUU => h.2 U U' (funext fun b => congrFun hUU ⟨b, hST b.2⟩)⟩
def finitelySupportedSubalgebra (a : ℝ) : Subalgebra ℝ C(GaugeField a, ℝ) where
  carrier := {F | ∃ S : Set (Link a), S.Finite ∧ DependsOnlyOn (F : GaugeField a → ℝ) S}
  mul_mem' := by
    rintro F G ⟨S, hS, hF⟩ ⟨T, hT, hG⟩
    have hST : S ∪ T ⊆ positiveLinks a := union_subset hF.1 hG.1
    have hF' := dependsOnlyOn_mono hF subset_union_left hST
    have hG' := dependsOnlyOn_mono hG subset_union_right hST
    refine ⟨S ∪ T, hS.union hT, hST, fun U U' h => ?_⟩
    simp only [ContinuousMap.coe_mul, Pi.mul_apply]
    rw [hF'.2 U U' h, hG'.2 U U' h]
  add_mem' := by
    rintro F G ⟨S, hS, hF⟩ ⟨T, hT, hG⟩
    have hST : S ∪ T ⊆ positiveLinks a := union_subset hF.1 hG.1
    have hF' := dependsOnlyOn_mono hF subset_union_left hST
    have hG' := dependsOnlyOn_mono hG subset_union_right hST
    refine ⟨S ∪ T, hS.union hT, hST, fun U U' h => ?_⟩
    simp only [ContinuousMap.coe_add, Pi.add_apply]
    rw [hF'.2 U U' h, hG'.2 U U' h]
  algebraMap_mem' r := ⟨∅, finite_empty, empty_subset _, fun _ _ _ => rfl⟩
def matrixEntryFunction (φ : ℂ → ℝ) (hφ : Continuous φ) (b : Link a) (i j : Fin 2) :
    C(GaugeField a, ℝ) :=
  ⟨fun U => φ ((U b : ComplexMatrix2) i j),
    hφ.comp ((continuous_subtype_val.comp (continuous_eval_link b)).matrix_elem i j)⟩
theorem matrixEntryFunction_mem (φ : ℂ → ℝ) (hφ : Continuous φ) {b : Link a}
    (hb : b ∈ positiveLinks a) (i j : Fin 2) :
    matrixEntryFunction φ hφ b i j ∈ finitelySupportedSubalgebra a := by
  refine ⟨{b}, finite_singleton b, singleton_subset_iff.mpr hb, fun U U' h => ?_⟩
  have h' : U b = U' b := congrFun h ⟨b, rfl⟩
  change φ ((U b : ComplexMatrix2) i j) = φ ((U' b : ComplexMatrix2) i j)
  rw [h']
theorem finitelySupportedSubalgebra_separatesPoints (ha : 0 < a) :
    (finitelySupportedSubalgebra a).SeparatesPoints := by
  intro U U' hUU
  obtain ⟨b, hb⟩ : ∃ b : positiveLinks a, U b ≠ U' b := by
    by_contra hne
    push Not at hne
    exact hUU ((fieldEquivValues ha).injective (funext hne))
  have hm : (U b : ComplexMatrix2) ≠ (U' b : ComplexMatrix2) := fun h => hb (Subtype.ext h)
  obtain ⟨i, j, hij⟩ : ∃ i j, (U b : ComplexMatrix2) i j ≠ (U' b : ComplexMatrix2) i j := by
    by_contra hne
    push Not at hne
    exact hm (Matrix.ext hne)
  by_cases hre : ((U b : ComplexMatrix2) i j).re = ((U' b : ComplexMatrix2) i j).re
  · have him : ((U b : ComplexMatrix2) i j).im ≠ ((U' b : ComplexMatrix2) i j).im := fun h =>
      hij (Complex.ext hre h)
    exact ⟨_, ⟨_, matrixEntryFunction_mem Complex.im Complex.continuous_im b.2 i j, rfl⟩, him⟩
  · exact ⟨_, ⟨_, matrixEntryFunction_mem Complex.re Complex.continuous_re b.2 i j, rfl⟩, hre⟩
theorem existsDenseLocalSequence_holds (ha : 0 < a) : ExistsDenseLocalSequence a := by
  have := compactSpace_gaugeField a
  have := t2Space_gaugeField a
  have := secondCountableTopology_gaugeField a
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    (finitelySupportedSubalgebra a) (finitelySupportedSubalgebra_separatesPoints ha)
  have : SecondCountableTopology C(GaugeField a, ℝ) := inferInstance
  have : Nonempty (finitelySupportedSubalgebra a) := ⟨0⟩
  let s : ℕ → finitelySupportedSubalgebra a :=
    TopologicalSpace.denseSeq (finitelySupportedSubalgebra a)
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  refine ⟨fun k => (s (Equiv.pnatEquivNat k) : C(GaugeField a, ℝ)), fun H ε hε => ?_,
    fun k => (s _).2⟩
  have hH : H ∈ (finitelySupportedSubalgebra a).topologicalClosure := by
    rw [htop]
    exact Algebra.mem_top
  obtain ⟨G, hG, hHG⟩ := Metric.mem_closure_iff.mp hH (ε / 2) (half_pos hε)
  obtain ⟨n, hn⟩ :=
    hs.exists_dist_lt (⟨G, hG⟩ : finitelySupportedSubalgebra a) (half_pos hε)
  refine ⟨Equiv.pnatEquivNat.symm n, ?_⟩
  rw [supNorm_eq_norm]
  simp only [Equiv.apply_symm_apply]
  rw [← dist_eq_norm]
  have hn' : dist G (s n : C(GaugeField a, ℝ)) < ε / 2 := hn
  linarith [dist_triangle H G (s n : C(GaugeField a, ℝ))]
theorem isBoundedBorel_of_measurable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] {f : X → ℝ} (hm : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    IsBoundedBorel f := by
  refine ⟨?_, C, hC⟩
  rw [← BorelSpace.measurable_eq (α := X)]
  exact hm
theorem abs_integral_le_of_forall_abs_le {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] {f : Y → ℝ} {C : ℝ} (h : ∀ y, |f y| ≤ C) :
    |∫ y, f y ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := C)
    (Eventually.of_forall h)
  simpa using this
theorem finiteLinkFubini_holds (a : ℝ) : FiniteLinkFubini a := by
  intro S _ _ Φ hΦ
  obtain ⟨hΦm, C, hC⟩ := hΦ
  have := secondCountableTopology_specialUnitary
  have := secondCountableTopology_gaugeField a
  have := metrizableSpace_gaugeField a
  have hprob : IsProbabilityMeasure (LinkVariables.haarMeasure S) := by
    unfold LinkVariables.haarMeasure ComplexMatrix2.haarPi
    infer_instance
  have hb : BorelSpace (LinkVariables S × GaugeField a) := inferInstance
  have hm : Measurable Φ := by
    rw [hb.measurable_eq]
    exact hΦm
  have hsup : ∀ x, |Φ x| ≤ YangMills.Construction.TestFunctions.uniformNorm Φ := fun x =>
    le_ciSup (f := fun x => ‖Φ x‖) ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩ x
  have hsm : StronglyMeasurable Φ := hm.stronglyMeasurable
  have hmU : ∀ U, Measurable fun V => Φ (V, U) := fun U => hm.comp measurable_prodMk_right
  have hmV : ∀ V, Measurable fun U => Φ (V, U) := fun V => hm.comp measurable_prodMk_left
  refine ⟨fun U => isBoundedBorel_of_measurable (hmU U) fun V => hC _,
    fun V => isBoundedBorel_of_measurable (hmV V) fun U => hC _,
    isBoundedBorel_of_measurable hsm.integral_prod_left'.measurable
      fun U => abs_integral_le_of_forall_abs_le _ fun V => hC _,
    fun U => abs_integral_le_of_forall_abs_le _ fun V => hsup _, fun hc => ?_,
    fun ν hν => ⟨?_, ?_⟩⟩
  · refine continuous_of_dominated (bound := fun _ => C)
      (fun U => (hmU U).aestronglyMeasurable)
      (fun U => Eventually.of_forall fun V => hC _) (integrable_const _)
      (Eventually.of_forall fun V => hc.comp (continuous_const.prodMk continuous_id))
  · exact isBoundedBorel_of_measurable hsm.integral_prod_right'.measurable
      fun V => abs_integral_le_of_forall_abs_le _ fun U => hC _
  · refine integral_integral_swap (f := fun U V => Φ (V, U)) ?_
    refine Integrable.of_bound (C := C)
      (hm.comp measurable_swap).aestronglyMeasurable (Eventually.of_forall fun x => hC _)
theorem statement_holds (hT : ComplexMatrix2.UnitaryLogarithmProperties) : Statement := fun d =>
  ⟨productStructure_holds d.spacing_pos, finiteLinkSplicing_holds d.spacing_pos,
    faceEnergyProperties_holds hT d.spacing, existsDenseLocalSequence_holds d.spacing_pos,
    finiteLinkFubini_holds d.spacing⟩
end YangMills.Construction.InfiniteLattice.GaugeFieldSpace
