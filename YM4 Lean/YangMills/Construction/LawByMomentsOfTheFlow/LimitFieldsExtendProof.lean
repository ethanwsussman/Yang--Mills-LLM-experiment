import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldsExist
import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldsExtend
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace YangMills.Construction.MomentMethod
section
variable {J J' : Type}
private theorem measure_eq_of_integral_finite_eq {P₁ P₂ : Measure (TranslateValues J)} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (h : ∀ (l : ℕ) (a : Fin l → J × ℕ) (G : (Fin l → ℝ) → ℝ), Continuous G → (∃ C : ℝ, ∀ w, |G w| ≤ C) →
      ∫ v, G (fun c => v (a c)) ∂P₁ = ∫ v, G (fun c => v (a c)) ∂P₂) : P₁ = P₂ := by
  refine IsProjectiveLimit.unique (P := fun I : Finset (J × ℕ) => P₂.map I.restrict) (fun I => ?_) (fun I => rfl)
  have hr : Measurable (I.restrict : TranslateValues J → (I → ℝ)) := Finset.measurable_restrict I
  haveI : IsProbabilityMeasure (P₁.map (I.restrict : TranslateValues J → (I → ℝ))) := Measure.isProbabilityMeasure_map hr.aemeasurable
  haveI : IsProbabilityMeasure (P₂.map (I.restrict : TranslateValues J → (I → ℝ))) := Measure.isProbabilityMeasure_map hr.aemeasurable
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map hr.aemeasurable f.continuous.aestronglyMeasurable, integral_map hr.aemeasurable f.continuous.aestronglyMeasurable]
  obtain ⟨e⟩ : Nonempty (I ≃ Fin I.card) := ⟨I.equivFin⟩
  obtain ⟨a, ha⟩ : ∃ a : Fin I.card → J × ℕ, ∀ c, a c = ((e.symm c : I) : J × ℕ) := ⟨_, fun _ => rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G : (Fin I.card → ℝ) → ℝ, G = fun w => f fun j => w (e j) := ⟨_, rfl⟩
  have hG : Continuous G := by
    rw [hGd]
    exact f.continuous.comp (continuous_pi fun j => continuous_apply _)
  have hGb : ∃ C : ℝ, ∀ w, |G w| ≤ C := ⟨‖f‖, fun w => by
    rw [hGd]
    exact f.norm_coe_le_norm _⟩
  have e2 : ∀ v : TranslateValues J, f (I.restrict v) = G fun c => v (a c) := by
    intro v
    rw [hGd]
    congr 1
    funext j
    simp [ha, Finset.restrict]
  simp_rw [e2]
  exact h _ a G hG hGb
private theorem measurable_leftValues : Measurable (leftValues (J := J) (J' := J')) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _
private theorem measurableSet_preimage_leftValues {A : Set (TranslateValues J)} (hA : MeasurableSet[shiftInvariantSigma J] A) :
    MeasurableSet[shiftInvariantSigma (J ⊕ J')] (leftValues ⁻¹' A) := by
  obtain ⟨h1, h2⟩ := hA
  refine ⟨?_, measurable_leftValues h2⟩
  have h3 := ((MeasurableSpace.measurableSet_invariants).mp h1).2
  show MeasurableSet[MeasurableSpace.invariants (translateShift (J := J ⊕ J'))] _
  rw [MeasurableSpace.measurableSet_invariants]
  refine ⟨measurable_leftValues h2, ?_⟩
  have h4 : ∀ v : TranslateValues (J ⊕ J'), leftValues (translateShift v) = translateShift (leftValues v) := fun v => rfl
  ext v
  show leftValues (translateShift v) ∈ A ↔ leftValues v ∈ A
  rw [h4]
  conv_rhs => rw [← h3]
  rfl
private theorem shiftInvariantSigma_le_pi (J : Type) : shiftInvariantSigma J ≤ MeasurableSpace.pi := inf_le_right
private theorem ae_bounds_of_setIntegral_bounds {Ω : Type} {m m0 : MeasurableSpace Ω} (hm : m ≤ m0) {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[m] Z) (hI : Integrable Z μ) {b₁ b₂ : ℝ}
    (h : ∀ A, MeasurableSet[m] A → b₁ * μ.real A ≤ ∫ ω in A, Z ω ∂μ ∧ ∫ ω in A, Z ω ∂μ ≤ b₂ * μ.real A) :
    ∀ᵐ ω ∂μ, b₁ ≤ Z ω ∧ Z ω ≤ b₂ := by
  have hIt : Integrable Z (μ.trim hm) := hI.trim hm hZ
  haveI : IsProbabilityMeasure (μ.trim hm) := ⟨by rw [trim_measurableSet_eq hm MeasurableSet.univ]; exact measure_univ⟩
  have hc : ∀ b : ℝ, Integrable (fun _ : Ω => b) (μ.trim hm) := fun b => integrable_const b
  have hreal : ∀ A, MeasurableSet[m] A → ∫ ω in A, Z ω ∂(μ.trim hm) = ∫ ω in A, Z ω ∂μ := fun A hA => (setIntegral_trim hm hZ hA).symm
  have hconst : ∀ (b : ℝ) A, MeasurableSet[m] A → ∫ _ω in A, b ∂(μ.trim hm) = b * μ.real A := by
    intro b A hA
    rw [setIntegral_const, smul_eq_mul, mul_comm]
    congr 1
    unfold Measure.real
    rw [trim_measurableSet_eq hm hA]
  have h1 : (fun _ => b₁) ≤ᵐ[μ.trim hm] Z := by
    refine ae_le_of_forall_setIntegral_le (hc b₁) hIt fun A hA _ => ?_
    rw [hconst _ _ hA, hreal _ hA]
    exact (h A hA).1
  have h2 : Z ≤ᵐ[μ.trim hm] fun _ => b₂ := by
    refine ae_le_of_forall_setIntegral_le hIt (hc b₂) fun A hA _ => ?_
    rw [hconst _ _ hA, hreal _ hA]
    exact (h A hA).2
  have h3 := ae_le_of_ae_le_trim h1
  have h4 := ae_le_of_ae_le_trim h2
  filter_upwards [h3, h4] with ω a1 a2
  exact ⟨a1, a2⟩
end
theorem jointLimitExtend_of_exists (hE : exists_jointLimitLaw_statement) : jointLimitExtendStatement := by
  intro T J J' _ _ X X' P hT hX hX' hP
  haveI := hP.isProbability
  have hXs : ∀ j, TranslatedLaws.HasBoundedMoments (Sum.elim X X' j) := by
    rintro (j | j)
    · exact hX j
    · exact hX' j
  obtain ⟨sub, P', hsub, hP'⟩ := hE T (J ⊕ J') (Sum.elim X X') hT hXs
  haveI := hP'.isProbability
  have hπ : Measurable (leftValues (J := J) (J' := J')) := measurable_leftValues
  haveI : IsProbabilityMeasure (P'.map (leftValues (J := J) (J' := J'))) := Measure.isProbabilityMeasure_map hπ.aemeasurable
  have hmap : P'.map leftValues = P := by
    refine measure_eq_of_integral_finite_eq fun l a G hG hGb => ?_
    have hcont : Continuous fun v : TranslateValues J => G fun c => v (a c) :=
      hG.comp (continuous_pi fun c => continuous_apply (a c))
    rw [integral_map hπ.aemeasurable hcont.aestronglyMeasurable]
    have l1 := hP'.tendsto l (fun c => (Sum.inl (a c).1, (a c).2)) G hG hGb
    have l2 := (hP.tendsto l a G hG hGb).comp hsub.tendsto_atTop
    exact tendsto_nhds_unique l1 l2
  refine ⟨sub, P', hsub, hP', hmap, ?_⟩
  intro Y b₁ b₂ hY hb
  have hMP : MeasurePreserving (leftValues (J := J) (J' := J')) P' P := ⟨hπ, hmap⟩
  have hY' : Integrable (Y ∘ leftValues (J := J) (J' := J')) P' := (hMP.integrable_comp hY.aestronglyMeasurable).mpr hY
  refine ae_bounds_of_setIntegral_bounds (shiftInvariantSigma_le_pi J) stronglyMeasurable_condExp integrable_condExp fun A hA => ?_
  have hA0 : MeasurableSet A := shiftInvariantSigma_le_pi J A hA
  have hpre := measurableSet_preimage_leftValues (J' := J') hA
  have e1 : ∫ v in A, (P[Y | shiftInvariantSigma J]) v ∂P = ∫ v in leftValues ⁻¹' A, (invariantCondExp P' (Y ∘ leftValues)) v ∂P' := by
    rw [setIntegral_condExp (shiftInvariantSigma_le_pi J) hY hA]
    unfold invariantCondExp
    rw [setIntegral_condExp (shiftInvariantSigma_le_pi _) hY' hpre]
    conv_lhs => rw [← hmap]
    rw [setIntegral_map hA0 (by rw [hmap]; exact hY.aestronglyMeasurable) hπ.aemeasurable]
    rfl
  have e2 : P.real A = P'.real (leftValues ⁻¹' A) := by
    unfold Measure.real
    rw [← hmap, Measure.map_apply hπ hA0]
  have hIs : IntegrableOn (invariantCondExp P' (Y ∘ leftValues)) (leftValues ⁻¹' A) P' := integrable_condExp.integrableOn
  rw [e1, e2]
  constructor
  · have := setIntegral_mono_ae_restrict (μ := P') (s := leftValues ⁻¹' A) (f := fun _ => b₁)
      (g := invariantCondExp P' (Y ∘ leftValues)) (integrable_const _).integrableOn hIs
      (ae_restrict_of_ae (hb.mono fun v hv => hv.1))
    rw [setIntegral_const, smul_eq_mul, mul_comm] at this
    exact this
  · have := setIntegral_mono_ae_restrict (μ := P') (s := leftValues ⁻¹' A) (g := fun _ => b₂)
      (f := invariantCondExp P' (Y ∘ leftValues)) hIs (integrable_const _).integrableOn
      (ae_restrict_of_ae (hb.mono fun v hv => hv.2))
    rw [setIntegral_const, smul_eq_mul, mul_comm] at this
    exact this
end YangMills.Construction.MomentMethod
end
