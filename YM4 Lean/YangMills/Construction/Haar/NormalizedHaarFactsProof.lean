import YangMills.Construction.Haar.NormalizedHaarMeasure
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Haar.HaarFacts
section General
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [TopologicalSpace.MetrizableSpace H] [MeasurableSpace H] [BorelSpace H]
theorem secondCountableTopology_of_compactMetrizable : SecondCountableTopology H := by
  let := TopologicalSpace.metrizableSpaceMetric H
  infer_instance
theorem isNormalizedHaar_haarMeasure :
    IsNormalizedHaar (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts H)) :=
  ⟨⟨Measure.haarMeasure_self⟩, fun g => map_mul_left_eq_self _ g⟩
theorem eq_haarMeasure_top {μ : Measure H} (hμ : IsNormalizedHaar μ) :
    μ = Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts H) := by
  have := secondCountableTopology_of_compactMetrizable (H := H)
  have := hμ.1
  have : μ.IsMulLeftInvariant := ⟨hμ.2⟩
  have hprob : IsProbabilityMeasure
      (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts H)) :=
    (isNormalizedHaar_haarMeasure (H := H)).1
  have key := Measure.isMulLeftInvariant_eq_smul μ
    (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts H))
  have hc : Measure.haarScalarFactor μ
      (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts H)) = 1 := by
    have h1 := congrArg (fun ν : Measure H => ν Set.univ) key
    simp only [Measure.smul_apply, measure_univ] at h1
    simpa using h1.symm
  rw [hc, one_smul] at key
  exact key
theorem isNormalizedHaar_unique {μ ν : Measure H} (hμ : IsNormalizedHaar μ)
    (hν : IsNormalizedHaar ν) : μ = ν :=
  (eq_haarMeasure_top hμ).trans (eq_haarMeasure_top hν).symm
theorem isNormalizedHaar_normalizedHaar : IsNormalizedHaar (normalizedHaar H) :=
  Classical.epsilon_spec (p := IsNormalizedHaar) ⟨_, isNormalizedHaar_haarMeasure⟩
theorem normalizedHaar_eq {μ : Measure H} (hμ : IsNormalizedHaar μ) :
    normalizedHaar H = μ :=
  isNormalizedHaar_unique isNormalizedHaar_normalizedHaar hμ
theorem isNormalizedHaar_map_mul_right {μ : Measure H} (hμ : IsNormalizedHaar μ) (g : H) :
    IsNormalizedHaar (μ.map fun h => h * g) := by
  have := hμ.1
  have hr : Measurable fun h : H => h * g := (continuous_mul_const g).measurable
  refine ⟨Measure.isProbabilityMeasure_map hr.aemeasurable, fun a => ?_⟩
  have hl : Measurable fun h : H => a * h := (continuous_const_mul a).measurable
  rw [Measure.map_map hl hr]
  have : ((fun h : H => a * h) ∘ fun h : H => h * g) =
      (fun h : H => h * g) ∘ fun h : H => a * h := by
    funext h
    simp [mul_assoc]
  rw [this, ← Measure.map_map hr hl, hμ.2 a]
theorem isNormalizedHaar_map_mul_right_eq {μ : Measure H} (hμ : IsNormalizedHaar μ) (g : H) :
    (μ.map fun h => h * g) = μ :=
  isNormalizedHaar_unique (isNormalizedHaar_map_mul_right hμ g) hμ
theorem isNormalizedHaar_map_inv {μ : Measure H} (hμ : IsNormalizedHaar μ) :
    IsNormalizedHaar (μ.map fun h => h⁻¹) := by
  have := hμ.1
  have hi : Measurable fun h : H => h⁻¹ := continuous_inv.measurable
  refine ⟨Measure.isProbabilityMeasure_map hi.aemeasurable, fun a => ?_⟩
  have hl : Measurable fun h : H => a * h := (continuous_const_mul a).measurable
  have hr : Measurable fun h : H => h * a⁻¹ := (continuous_mul_const a⁻¹).measurable
  rw [Measure.map_map hl hi]
  have : ((fun h : H => a * h) ∘ fun h : H => h⁻¹) =
      (fun h : H => h⁻¹) ∘ fun h : H => h * a⁻¹ := by
    funext h
    simp
  rw [this, ← Measure.map_map hi hr, isNormalizedHaar_map_mul_right_eq hμ a⁻¹]
theorem normalizedHaar_pos_of_isOpen {U : Set H} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < normalizedHaar H U := by
  rw [eq_haarMeasure_top isNormalizedHaar_normalizedHaar]
  exact hU.measure_pos _ hne
end General
theorem normalizedHaarUniqueInvariant_holds : NormalizedHaarUniqueInvariant := by
  intro H _ _ _ _ _ _ _
  exact ⟨⟨_, isNormalizedHaar_normalizedHaar, fun _ hν => (normalizedHaar_eq hν).symm⟩,
    isNormalizedHaar_normalizedHaar, isNormalizedHaar_map_mul_right_eq isNormalizedHaar_normalizedHaar,
    isNormalizedHaar_unique (isNormalizedHaar_map_inv isNormalizedHaar_normalizedHaar)
      isNormalizedHaar_normalizedHaar⟩
theorem normalizedHaarFinitePower_holds : NormalizedHaarFinitePower := by
  intro H _ _ _ _ _ _ _ S _
  have := secondCountableTopology_of_compactMetrizable (H := H)
  have hborel : BorelSpace (S → H) := Pi.borelSpace
  have hH := isNormalizedHaar_normalizedHaar (H := H)
  have := hH.1
  have : (normalizedHaar H).IsMulLeftInvariant := ⟨hH.2⟩
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, hborel.measurable_eq.symm, ?_⟩
  refine normalizedHaar_eq ⟨inferInstance, fun g => ?_⟩
  exact map_mul_left_eq_self _ g
theorem normalizedHaarSpecialUnitary_holds : NormalizedHaarSpecialUnitary := by
  have : TopologicalSpace.MetrizableSpace Matrices.ComplexMatrix2 :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (Fin 2 → Fin 2 → ℂ))
  have : TopologicalSpace.MetrizableSpace Matrices.ComplexMatrix2.specialUnitary :=
    Topology.IsEmbedding.subtypeVal.metrizableSpace
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩,
    normalizedHaar_eq isNormalizedHaar_haarMeasure⟩
theorem normalizedHaarFacts_holds : NormalizedHaarFacts :=
  ⟨normalizedHaarUniqueInvariant_holds,
    fun _ _ _ _ _ _ _ _ _ hU hne => normalizedHaar_pos_of_isOpen hU hne,
    normalizedHaarFinitePower_holds, normalizedHaarSpecialUnitary_holds⟩
end YangMills.Construction.Haar.HaarFacts
