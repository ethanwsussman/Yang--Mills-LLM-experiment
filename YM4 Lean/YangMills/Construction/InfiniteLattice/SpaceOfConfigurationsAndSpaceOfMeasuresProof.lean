import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndSpaceOfMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter YangMills.Construction.InfiniteLattice YangMills.Construction.GibbsAtFixedSpacing YangMills.Construction.Matrices
open scoped ComplexConjugate BoundedContinuousFunction
noncomputable section
namespace YangMills.Construction.FieldsAtSpacing.CompactnessOfFields
variable {a : ℝ}
theorem continuous_eval_link (b : Link a) : Continuous fun U : GaugeField a => U b :=
  (continuous_apply b).comp continuous_subtype_val
theorem isClosed_gaugeFieldSet :
    IsClosed {U : Link a → ComplexMatrix2.specialUnitary | ∀ b, U b.opposite = (U b)⁻¹} := by
  have h : {U : Link a → ComplexMatrix2.specialUnitary | ∀ b, U b.opposite = (U b)⁻¹} =
      ⋂ b, {U : Link a → ComplexMatrix2.specialUnitary | U b.opposite = (U b)⁻¹} := by
    ext U
    simp
  rw [h]
  exact isClosed_iInter fun b =>
    isClosed_eq (continuous_apply _) (continuous_apply b).inv
theorem compactSpace_gaugeField : CompactSpace (GaugeField a) :=
  isCompact_iff_compactSpace.mp (isClosed_gaugeFieldSet (a := a)).isCompact
attribute [local instance] compactSpace_gaugeField
theorem secondCountable_specialUnitary : SecondCountableTopology ComplexMatrix2.specialUnitary := by
  have : SecondCountableTopology ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
attribute [local instance] secondCountable_specialUnitary
theorem t2Space_gaugeField : T2Space (GaugeField a) :=
  inferInstanceAs
    (T2Space {U : Link a → ComplexMatrix2.specialUnitary // ∀ b, U b.opposite = (U b)⁻¹})
attribute [local instance] t2Space_gaugeField
theorem secondCountable_gaugeField : SecondCountableTopology (GaugeField a) := by
  have : SecondCountableTopology
      {U : Link a → ComplexMatrix2.specialUnitary // ∀ b, U b.opposite = (U b)⁻¹} :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  exact this
attribute [local instance] secondCountable_gaugeField
theorem metrizableSpace_gaugeField : TopologicalSpace.MetrizableSpace (GaugeField a) :=
  inferInstance
attribute [local instance] metrizableSpace_gaugeField
theorem continuous_linkRestriction (S : Set (Link a)) :
    Continuous (linkRestriction (a := a) S) :=
  continuous_pi fun b => continuous_eval_link b.1
theorem bijective_linkRestriction_positive (ha : 0 < a) :
    Function.Bijective (linkRestriction (a := a) (positiveLinkSet a)) := by
  constructor
  · intro U V h
    have key : ∀ b ∈ positiveLinkSet a, U b = V b := fun b hb =>
      congrFun h ⟨b, hb⟩
    refine Subtype.ext (funext fun b => ?_)
    rcases mem_positiveLinks_or_opposite_mem b with hb | hb
    · exact key b hb
    · have h₁ := U.2 b.opposite
      have h₂ := V.2 b.opposite
      rw [Link.opposite_opposite] at h₁ h₂
      change U b = V b
      rw [h₁, h₂, key _ hb]
  · intro g
    refine ⟨gluedField ha subset_rfl g (trivialField a), funext fun b => ?_⟩
    exact gluedField_apply_of_mem ha subset_rfl g _ b
theorem gaugeFieldsCompactProduct (ha : 0 < a) : GaugeFieldsCompactProduct a := by
  have hbij := bijective_linkRestriction_positive ha
  have hhom : IsHomeomorph (linkRestriction (a := a) (positiveLinkSet a)) :=
    isHomeomorph_iff_continuous_bijective.mpr ⟨continuous_linkRestriction _, hbij⟩
  exact ⟨xor_mem_positiveLinks ha, Set.to_countable _, hbij, hhom, inferInstance,
    inferInstance, inferInstance, inferInstance⟩
theorem exists_extend_linkFunction {S T : Set (Link a)} (h : S ⊆ T)
    {f : LinkVariables S → ℂ} (hf : Continuous f) :
    ∃ f' : LinkVariables T → ℂ, Continuous f' ∧
      ∀ U, f (linkRestriction S U) = f' (linkRestriction T U) :=
  ⟨fun g => f fun b => g ⟨b.1, h b.2⟩,
    hf.comp (continuous_pi fun _ => continuous_apply _), fun _ => rfl⟩
theorem exists_common_links {F G : GaugeField a → ℂ}
    (hF : F ∈ continuousFiniteLinkFunctions a)
    (hG : G ∈ continuousFiniteLinkFunctions a) :
    ∃ T : Set (Link a), T.Finite ∧ T ⊆ positiveLinkSet a ∧
      ∃ f g : LinkVariables T → ℂ, Continuous f ∧ Continuous g ∧
        (∀ U, F U = f (linkRestriction T U)) ∧ ∀ U, G U = g (linkRestriction T U) := by
  obtain ⟨-, S, hS, hs, f, hf, hFf⟩ := hF
  obtain ⟨-, S', hS', hs', g, hg, hGg⟩ := hG
  obtain ⟨f₁, hf₁, hff₁⟩ := exists_extend_linkFunction (subset_union_left (t := S')) hf
  obtain ⟨g₁, hg₁, hgg₁⟩ := exists_extend_linkFunction (subset_union_right (s := S)) hg
  exact ⟨S ∪ S', hS.union hS', union_subset hs hs', f₁, g₁, hf₁, hg₁,
    fun U => (hFf U).trans (hff₁ U), fun U => (hGg U).trans (hgg₁ U)⟩
theorem mem_continuousFiniteLinkFunctions {S : Set (Link a)} (hS : S.Finite)
    (hs : S ⊆ positiveLinkSet a)
    {f : LinkVariables S → ℂ} (hf : Continuous f) {F : GaugeField a → ℂ}
    (hF : ∀ U, F U = f (linkRestriction S U)) :
    F ∈ continuousFiniteLinkFunctions a := by
  refine ⟨?_, S, hS, hs, f, hf, hF⟩
  have : F = f ∘ linkRestriction S := funext hF
  rw [this]
  exact hf.comp (continuous_linkRestriction S)
theorem add_mem_local {F G : GaugeField a → ℂ}
    (hF : F ∈ continuousFiniteLinkFunctions a)
    (hG : G ∈ continuousFiniteLinkFunctions a) :
    F + G ∈ continuousFiniteLinkFunctions a := by
  obtain ⟨T, hT, hs, f, g, hf, hg, h, h'⟩ := exists_common_links hF hG
  exact mem_continuousFiniteLinkFunctions hT hs (hf.add hg) fun U => by simp [h U, h' U]
theorem mul_mem_local {F G : GaugeField a → ℂ}
    (hF : F ∈ continuousFiniteLinkFunctions a)
    (hG : G ∈ continuousFiniteLinkFunctions a) :
    F * G ∈ continuousFiniteLinkFunctions a := by
  obtain ⟨T, hT, hs, f, g, hf, hg, h, h'⟩ := exists_common_links hF hG
  exact mem_continuousFiniteLinkFunctions hT hs (hf.mul hg) fun U => by simp [h U, h' U]
theorem const_mem_local (z : ℂ) :
    (fun _ : GaugeField a => z) ∈ continuousFiniteLinkFunctions a :=
  mem_continuousFiniteLinkFunctions (S := ∅) finite_empty (empty_subset _) (f := fun _ => z)
    continuous_const fun _ => rfl
theorem conj_mem_local {F : GaugeField a → ℂ}
    (hF : F ∈ continuousFiniteLinkFunctions a) :
    (fun U => (starRingEnd ℂ) (F U)) ∈ continuousFiniteLinkFunctions a := by
  obtain ⟨-, S, hS, hs, f, hf, hFf⟩ := hF
  exact mem_continuousFiniteLinkFunctions hS hs (Complex.continuous_conj.comp hf) fun U => by
    simp [hFf U]
def localAlgebra (a : ℝ) : Subalgebra ℂ (GaugeField a → ℂ) where
  carrier := continuousFiniteLinkFunctions a
  mul_mem' := mul_mem_local
  add_mem' := add_mem_local
  algebraMap_mem' z := const_mem_local z
theorem entry_mem_local {b : Link a} (hb : b ∈ positiveLinkSet a) (i j : Fin 2) :
    (fun U : GaugeField a => (U b : ComplexMatrix2) i j) ∈ continuousFiniteLinkFunctions a := by
  refine mem_continuousFiniteLinkFunctions (S := {b}) (finite_singleton b)
    (singleton_subset_iff.mpr hb)
    (f := fun g => (g ⟨b, rfl⟩ : ComplexMatrix2) i j) ?_ fun _ => rfl
  exact Continuous.matrix_elem (continuous_subtype_val.comp (continuous_apply _)) i j
theorem exists_local_separating (ha : 0 < a) {U V : GaugeField a} (h : U ≠ V) :
    ∃ F ∈ continuousFiniteLinkFunctions a, F U ≠ F V := by
  have h₁ : linkRestriction (positiveLinkSet a) U ≠ linkRestriction (positiveLinkSet a) V :=
    fun e => h ((bijective_linkRestriction_positive ha).1 e)
  obtain ⟨b, hb⟩ := Function.ne_iff.mp h₁
  have h₂ : (U b.1 : ComplexMatrix2) ≠ (V b.1 : ComplexMatrix2) := fun e => hb (Subtype.ext e)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h₂
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  exact ⟨_, entry_mem_local b.2 i j, hj⟩
def localStarAlgebra (a : ℝ) : StarSubalgebra ℂ C(GaugeField a, ℂ) where
  carrier := {F | (F : GaugeField a → ℂ) ∈ continuousFiniteLinkFunctions a}
  mul_mem' hF hG := mul_mem_local hF hG
  add_mem' hF hG := add_mem_local hF hG
  algebraMap_mem' z := const_mem_local z
  star_mem' hF := conj_mem_local hF
theorem topologicalClosure_localStarAlgebra (ha : 0 < a) :
    (localStarAlgebra a).topologicalClosure = ⊤ := by
  refine ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_
  intro U V h
  obtain ⟨F, hF, hne⟩ := exists_local_separating ha h
  exact ⟨F, ⟨⟨F, hF.1⟩, hF, rfl⟩, hne⟩
theorem exists_local_approx (ha : 0 < a) (F : C(GaugeField a, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : C(GaugeField a, ℂ),
      (G : GaugeField a → ℂ) ∈ continuousFiniteLinkFunctions a ∧ ‖F - G‖ < ε := by
  have hF : F ∈ closure ((localStarAlgebra a : Set C(GaugeField a, ℂ))) := by
    have : F ∈ (localStarAlgebra a).topologicalClosure := by
      rw [topologicalClosure_localStarAlgebra ha]
      trivial
    exact this
  obtain ⟨G, hG, hd⟩ := Metric.mem_closure_iff.mp hF ε hε
  exact ⟨G, hG, by rwa [← dist_eq_norm]⟩
theorem supNorm_le_norm (F : C(GaugeField a, ℂ)) :
    observableSupNorm (F : GaugeField a → ℂ) ≤ ‖F‖ := by
  have : Nonempty (GaugeField a) := ⟨trivialField a⟩
  exact ciSup_le fun U => F.norm_coe_le_norm U
theorem continuousFiniteLinkFunctionsDense (ha : 0 < a) : ContinuousFiniteLinkFunctionsDense a := by
  refine ⟨⟨localAlgebra a, rfl, ?_⟩, const_mem_local, ?_, ?_, ?_⟩
  · intro F hF
    exact hF.1
  · intro F hF
    exact conj_mem_local hF
  · intro U V h
    exact exists_local_separating ha h
  · intro F hF ε hε
    let F₀ : C(GaugeField a, ℂ) := ⟨F, hF⟩
    obtain ⟨G, hG, hn⟩ := exists_local_approx ha F₀ hε
    exact ⟨G, hG, (supNorm_le_norm (F₀ - G)).trans_lt hn⟩
instance isProbabilityMeasure_borelProb (ν : BorelProb a) : IsProbabilityMeasure ν.1 := ν.2
theorem integrable_continuousMap (ν : BorelProb a) (F : C(GaugeField a, ℂ)) :
    Integrable (F : GaugeField a → ℂ) ν.1 := by
  refine Integrable.of_bound F.continuous.aestronglyMeasurable ‖F‖ ?_
  exact Eventually.of_forall fun U => F.norm_coe_le_norm U
theorem norm_integral_sub_integral_le (ν : BorelProb a) (F G : C(GaugeField a, ℂ)) :
    ‖ν.integral F - ν.integral G‖ ≤ ‖F - G‖ := by
  have h : ν.integral F - ν.integral G = ∫ U, (F - G) U ∂ν.1 :=
    (integral_sub (integrable_continuousMap ν F) (integrable_continuousMap ν G)).symm
  rw [h]
  have := norm_integral_le_of_norm_le_const (μ := ν.1) (f := fun U => (F - G) U) (C := ‖F - G‖)
    (Eventually.of_forall fun U => (F - G).norm_coe_le_norm U)
  simpa using this
theorem ext_of_integral_continuous {ν ν' : BorelProb a}
    (h : ∀ F : C(GaugeField a, ℂ), ν.integral F = ν'.integral F) : ν = ν' := by
  let : MetricSpace (GaugeField a) := TopologicalSpace.metrizableSpaceMetric _
  refine Subtype.ext (ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_)
  have := h ⟨fun U => ((f U : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  simp only [BorelProb.integral, GaugeFieldProbability.expect, ContinuousMap.coe_mk] at this
  rw [integral_complex_ofReal, integral_complex_ofReal] at this
  exact_mod_cast this
theorem ext_of_integral_local (ha : 0 < a) {ν ν' : BorelProb a}
    (h : ∀ F ∈ continuousFiniteLinkFunctions a, ν.integral F = ν'.integral F) :
    ν = ν' := by
  refine ext_of_integral_continuous fun F => ?_
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨G, hG, hn⟩ := exists_local_approx ha F (half_pos hε)
  have h₁ := norm_integral_sub_integral_le ν F G
  have h₂ := norm_integral_sub_integral_le ν' F G
  have e : ν.integral F - ν'.integral F =
      (ν.integral F - ν.integral G) - (ν'.integral F - ν'.integral G) := by
    rw [h _ hG]
    ring
  rw [dist_eq_norm, e]
  calc _ ≤ ‖ν.integral F - ν.integral G‖ + ‖ν'.integral F - ν'.integral G‖ := norm_sub_le _ _
    _ ≤ ε := by linarith
def ofProbabilityMeasure (μ : ProbabilityMeasure (GaugeField a)) : BorelProb a := ⟨μ.1, μ.2⟩
theorem bijective_ofProbabilityMeasure : Function.Bijective (ofProbabilityMeasure (a := a)) :=
  ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h), fun ν => ⟨⟨ν.1, ν.2⟩, rfl⟩⟩
theorem continuous_integral_ofProbabilityMeasure (F : C(GaugeField a, ℂ)) :
    Continuous fun μ : ProbabilityMeasure (GaugeField a) => (ofProbabilityMeasure μ).integral F := by
  let fr : GaugeField a →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun U => (F U).re, Complex.continuous_re.comp F.continuous⟩
  let fi : GaugeField a →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun U => (F U).im, Complex.continuous_im.comp F.continuous⟩
  have hr : Continuous fun μ : ProbabilityMeasure (GaugeField a) =>
      ∫ U, fr U ∂(μ : Measure (GaugeField a)) :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction fr
  have hi : Continuous fun μ : ProbabilityMeasure (GaugeField a) =>
      ∫ U, fi U ∂(μ : Measure (GaugeField a)) :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction fi
  have e : (fun μ : ProbabilityMeasure (GaugeField a) => (ofProbabilityMeasure μ).integral F) =
      fun μ : ProbabilityMeasure (GaugeField a) =>
        ((∫ U, fr U ∂(μ : Measure (GaugeField a)) : ℝ) : ℂ) +
        ((∫ U, fi U ∂(μ : Measure (GaugeField a)) : ℝ) : ℂ) * Complex.I := by
    funext μ
    exact (integral_re_add_im (integrable_continuousMap (ofProbabilityMeasure μ) F)).symm
  rw [e]
  exact (Complex.continuous_ofReal.comp hr).add
    ((Complex.continuous_ofReal.comp hi).mul continuous_const)
theorem continuous_ofProbabilityMeasure : Continuous (ofProbabilityMeasure (a := a)) := by
  refine continuous_iInf_rng.mpr fun F => continuous_induced_rng.mpr ?_
  exact continuous_integral_ofProbabilityMeasure ⟨F.1, F.2⟩
theorem continuous_integral_apply (F : C(GaugeField a, ℂ)) :
    Continuous fun ν : BorelProb a => ν.integral F :=
  continuous_iInf_dom (i := (⟨F, F.continuous⟩ : continuousFns a)) continuous_induced_dom
theorem t2Space_borelProb : T2Space (BorelProb a) :=
  T2Space.of_injective_continuous
    (f := fun (ν : BorelProb a) (F : C(GaugeField a, ℂ)) => ν.integral F)
    (fun _ _ h => ext_of_integral_continuous fun F => congrFun h F)
    (continuous_pi continuous_integral_apply)
theorem compactSpace_and_metrizableSpace :
    CompactSpace (BorelProb a) ∧ TopologicalSpace.MetrizableSpace (BorelProb a) := by
  have := t2Space_borelProb (a := a)
  have hhom : IsHomeomorph (ofProbabilityMeasure (a := a)) :=
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨continuous_ofProbabilityMeasure, bijective_ofProbabilityMeasure⟩
  let e := hhom.homeomorph
  exact ⟨e.compactSpace, e.symm.isEmbedding.metrizableSpace⟩
theorem compactFieldsAndMeasures : CompactFieldsAndMeasures := fun _ ha =>
  ⟨gaugeFieldsCompactProduct ha, continuousFiniteLinkFunctionsDense ha,
    compactSpace_and_metrizableSpace, fun _ _ h => ext_of_integral_local ha h⟩
end YangMills.Construction.FieldsAtSpacing.CompactnessOfFields
