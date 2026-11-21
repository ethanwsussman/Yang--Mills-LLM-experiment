import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndSpaceOfMeasures
import YangMills.Construction.InfiniteLattice.TheSpaceOfConfigurationsAndTheSpaceOfMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace GibbsAtFixedSpacing.SpacesOfFieldsAndMeasures
variable {a : ℝ}
theorem isClosed_setOf_opposite_eq_inv :
    IsClosed {U : Link a → Matrices.ComplexMatrix2.specialUnitary | ∀ b, U b.opposite = (U b)⁻¹} := by
  have hset : {U : Link a → Matrices.ComplexMatrix2.specialUnitary | ∀ b, U b.opposite = (U b)⁻¹} =
      ⋂ b, {U : Link a → Matrices.ComplexMatrix2.specialUnitary | U b.opposite = (U b)⁻¹} := by
    ext U
    simp
  rw [hset]
  exact isClosed_iInter fun b => isClosed_eq (continuous_apply _) (continuous_apply b).inv
theorem secondCountableTopology_specialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
attribute [local instance] secondCountableTopology_specialUnitary
theorem secondCountableTopology_gaugeField : SecondCountableTopology (GaugeField a) := by
  have : SecondCountableTopology
      {U : Link a → Matrices.ComplexMatrix2.specialUnitary // ∀ b, U b.opposite = (U b)⁻¹} :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  exact this
attribute [local instance] secondCountableTopology_gaugeField
theorem regionSigma_mono {S T : Set AmbientSpace} (hST : S ⊆ T) :
    (regionSigma S : MeasurableSpace (GaugeField a)) ≤ regionSigma T :=
  iSup₂_le fun b hb => le_iSup₂_of_le (f := fun (b : Link a) (_ : b ∈ linksWithin T) =>
    MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) b
      ⟨hST hb.1, hST hb.2⟩ le_rfl
theorem continuousLocal_add_mem {F G : GaugeField a → ℂ} (hF : F ∈ continuousLocal a)
    (hG : G ∈ continuousLocal a) : F + G ∈ continuousLocal a := by
  obtain ⟨hFc, ⟨hFm, C, hC⟩, S, hS, hSm⟩ := hF
  obtain ⟨hGc, ⟨hGm, D, hD⟩, T, hT, hTm⟩ := hG
  have h₁ : Measurable[regionSigma (S ∪ T)] F :=
    Measurable.mono hSm (regionSigma_mono subset_union_left) le_rfl
  have h₂ : Measurable[regionSigma (S ∪ T)] G :=
    Measurable.mono hTm (regionSigma_mono subset_union_right) le_rfl
  exact ⟨hFc.add hGc, ⟨hFm.add hGm, C + D, fun U =>
    (norm_add_le _ _).trans (add_le_add (hC U) (hD U))⟩, S ∪ T, hS.union hT, h₁.add h₂⟩
theorem continuousLocal_mul_mem {F G : GaugeField a → ℂ} (hF : F ∈ continuousLocal a)
    (hG : G ∈ continuousLocal a) : F * G ∈ continuousLocal a := by
  obtain ⟨hFc, ⟨hFm, C, hC⟩, S, hS, hSm⟩ := hF
  obtain ⟨hGc, ⟨hGm, D, hD⟩, T, hT, hTm⟩ := hG
  have h₁ : Measurable[regionSigma (S ∪ T)] F :=
    Measurable.mono hSm (regionSigma_mono subset_union_left) le_rfl
  have h₂ : Measurable[regionSigma (S ∪ T)] G :=
    Measurable.mono hTm (regionSigma_mono subset_union_right) le_rfl
  refine ⟨hFc.mul hGc, ⟨hFm.mul hGm, C * D, fun U => ?_⟩, S ∪ T, hS.union hT, h₁.mul h₂⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hC U) (hD U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
theorem continuousLocal_const_mem (z : ℂ) : (fun _ : GaugeField a => z) ∈ continuousLocal a :=
  ⟨continuous_const, ⟨measurable_const, ‖z‖, fun _ => le_rfl⟩, ∅, Bornology.isBounded_empty,
    measurable_const⟩
theorem continuousLocal_conj_mem {F : GaugeField a → ℂ} (hF : F ∈ continuousLocal a) :
    (fun U => starRingEnd ℂ (F U)) ∈ continuousLocal a := by
  obtain ⟨hFc, ⟨hFm, C, hC⟩, S, hS, hSm⟩ := hF
  have hSm' : Measurable[regionSigma S] F := hSm
  exact ⟨Complex.continuous_conj.comp hFc, ⟨Complex.continuous_conj.measurable.comp hFm, C,
    fun U => by simpa using hC U⟩, S, hS, Complex.continuous_conj.measurable.comp hSm'⟩
theorem continuousLocal_of_mem_continuousFiniteLinkFunctions [CompactSpace (GaugeField a)]
    {F : GaugeField a → ℂ}
    (hF : F ∈ FieldsAtSpacing.continuousFiniteLinkFunctions a) :
    F ∈ continuousLocal a := by
  obtain ⟨hFc, B, hB, -, f, hf, hFf⟩ := hF
  have hcont : Continuous F := hFc
  refine ⟨hcont, ⟨hcont.measurable, ?_⟩, ?_⟩
  · obtain ⟨C, hC⟩ := (isCompact_range hcont).isBounded.exists_norm_le
    exact ⟨C, fun U => hC _ (mem_range_self U)⟩
  · let S : Set AmbientSpace := (fun b : Link a => (b.initial : AmbientSpace)) '' B ∪
      (fun b : Link a => (b.terminal : AmbientSpace)) '' B
    refine ⟨S, ((hB.image _).union (hB.image _)).isBounded, ?_⟩
    have hres : Measurable[regionSigma S]
        (FieldsAtSpacing.linkRestriction B : GaugeField a → LinkVariables B) := by
      refine (@measurable_pi_iff _ _ _ (regionSigma S) _ _).mpr fun b => Measurable.of_comap_le ?_
      exact le_iSup₂_of_le (f := fun (b : Link a) (_ : b ∈ linksWithin S) =>
        MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) b.1
          ⟨Or.inl ⟨b.1, b.2, rfl⟩, Or.inr ⟨b.1, b.2, rfl⟩⟩ le_rfl
    have hcomp : F = f ∘ FieldsAtSpacing.linkRestriction B := funext hFf
    rw [hcomp]
    exact hf.measurable.comp hres
theorem exists_countable_isSupNormDense_subset [CompactSpace (GaugeField a)]
    [TopologicalSpace.MetrizableSpace (GaugeField a)] {A : Set (GaugeField a → ℂ)}
    (hc : ∀ F ∈ A, Continuous F) (hd : IsSupNormDense A) :
    ∃ D : Set (GaugeField a → ℂ), D ⊆ A ∧ D.Countable ∧ IsSupNormDense D := by
  let T : Set C(GaugeField a, ℂ) := {G | (G : GaugeField a → ℂ) ∈ A}
  obtain ⟨t, htT, htc, hcl⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace T).exists_countable_dense_subset
  refine ⟨(fun G : C(GaugeField a, ℂ) => (G : GaugeField a → ℂ)) '' t, ?_, htc.image _, ?_⟩
  · rintro _ ⟨G, hG, rfl⟩
    exact htT hG
  · intro F hF ε hε
    obtain ⟨H, hH, hn⟩ := hd F hF (ε / 2) (half_pos hε)
    let F₀ : C(GaugeField a, ℂ) := ⟨F, hF⟩
    let H₀ : C(GaugeField a, ℂ) := ⟨H, hc H hH⟩
    have hH₀ : H₀ ∈ closure t := hcl hH
    obtain ⟨G, hG, hdist⟩ := Metric.mem_closure_iff.mp hH₀ (ε / 2) (half_pos hε)
    refine ⟨G, ⟨G, hG, rfl⟩, ?_⟩
    have e₁ : observableSupNorm (F - H) = ‖F₀ - H₀‖ :=
      (ContinuousMap.norm_eq_iSup_norm (F₀ - H₀)).symm
    have e₂ : observableSupNorm (F - (G : GaugeField a → ℂ)) = ‖F₀ - G‖ :=
      (ContinuousMap.norm_eq_iSup_norm (F₀ - G)).symm
    rw [dist_eq_norm] at hdist
    rw [e₂]
    rw [e₁] at hn
    calc ‖F₀ - G‖ = ‖(F₀ - H₀) + (H₀ - G)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖F₀ - H₀‖ + ‖H₀ - G‖ := norm_add_le _ _
      _ < ε := by linarith
def continuousLocalSubalgebra (a : ℝ) : Subalgebra ℂ (GaugeField a → ℂ) where
  carrier := continuousLocal a
  mul_mem' := continuousLocal_mul_mem
  add_mem' := continuousLocal_add_mem
  algebraMap_mem' := continuousLocal_const_mem
theorem fieldAndMeasureSpaceProperties_of_compactFieldsAndMeasures
    (h : FieldsAtSpacing.CompactFieldsAndMeasures) :
    FieldAndMeasureSpaceProperties := by
  intro a ha
  obtain ⟨hA, hB, hC, hD⟩ := h a ha
  obtain ⟨-, -, -, -, hcomp, hmet, -, -⟩ := hA
  obtain ⟨-, -, -, hsep, hdense⟩ := hB
  have hsub : FieldsAtSpacing.continuousFiniteLinkFunctions a ⊆ continuousLocal a :=
    fun F hF => continuousLocal_of_mem_continuousFiniteLinkFunctions hF
  have hdenseFin : IsSupNormDense (FieldsAtSpacing.continuousFiniteLinkFunctions a) :=
    fun F hF ε hε => hdense F hF ε hε
  have hdenseLoc : IsSupNormDense (continuousLocal a) := fun F hF ε hε => by
    obtain ⟨H, hH, hn⟩ := hdenseFin F hF ε hε
    exact ⟨H, hsub hH, hn⟩
  refine ⟨⟨isClosed_setOf_opposite_eq_inv, hcomp, hmet⟩, ⟨fun F hF => hF.1,
    ⟨continuousLocalSubalgebra a, rfl⟩, continuousLocal_const_mem,
    fun F hF => continuousLocal_conj_mem hF, fun U U' hne => ?_, hdenseLoc⟩, hC,
    fun ν ν' hνν' => hD ν ν' fun F hF => hνν' F (hsub hF), ?_⟩
  · obtain ⟨F, hF, hne'⟩ := hsep U U' hne
    exact ⟨F, hsub hF, hne'⟩
  · obtain ⟨D, hDsub, hcount, hd⟩ :=
      exists_countable_isSupNormDense_subset (fun F hF => (hsub hF).1) hdenseFin
    exact ⟨D, hDsub.trans hsub, hcount, hd⟩
end GibbsAtFixedSpacing.SpacesOfFieldsAndMeasures
end YangMills.Construction
