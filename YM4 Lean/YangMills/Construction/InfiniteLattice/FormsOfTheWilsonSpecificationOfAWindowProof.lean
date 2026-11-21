import YangMills.Construction.InfiniteLattice.FormsOfTheWilsonSpecificationOfAWindow
import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import YangMills.Construction.Matrices.FunctionsAndOperatorsOfSeveralVariablesOnG
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace WindowSpecificationForms
variable {a : ℝ}
theorem isPositivelyOriented_of_mem_edgeList {p : ElementaryPlaquette a} {b : Link a}
    (hb : b ∈ WilsonOperator.edgeList p) : b.IsPositivelyOriented := by
  simp only [WilsonOperator.edgeList, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> exact ⟨_, add_sub_cancel_left _ _⟩
theorem glue_eq_patch (ha : 0 < a) (W : LinkWindow a) (V : W.Assignments) (ξ : GaugeField a)
    {b : Link a} (hb : b.IsPositivelyOriented) : W.glue ha V ξ b = patch W.links V ξ b := by
  by_cases h : b ∈ W.links
  · have h₁ : W.glue ha V ξ b = V ⟨b, h⟩ := dif_pos h
    rw [h₁]
    simp only [patch, dif_pos h]
  · have hr : b.opposite ∉ W.links := fun hr =>
      Link.opposite_not_isPositivelyOriented ha hb (W.isPositive _ hr)
    have h₁ : W.glue ha V ξ b = ξ b := (dif_neg h).trans (dif_neg hr)
    rw [h₁]
    simp only [patch, dif_neg h]
theorem exp_windowAction_eq (ha : 0 < a) (W : LinkWindow a) (β : ℝ) (V : W.Assignments)
    (ξ : GaugeField a) :
    Real.exp (-β * W.windowAction (W.glue ha V ξ)) = boltzmannWeight β W.links ξ V := by
  have h : ∀ p : ElementaryPlaquette a, faceEnergy (W.glue ha V ξ) p =
      faceEnergy (patch W.links V ξ) p := fun p =>
    WilsonOperator.faceEnergy_congr p fun b hb =>
      glue_eq_patch ha W V ξ (isPositivelyOriented_of_mem_edgeList hb)
  simp only [LinkWindow.windowAction, boltzmannWeight, LinkWindow.faces, h]
theorem integral_exp_windowAction_eq (ha : 0 < a) (W : LinkWindow a) (β : ℝ) (ξ : GaugeField a) :
    (∫ V, Real.exp (-β * W.windowAction (W.glue ha V ξ)) ∂W.haarProd) =
      partitionFunction β W.links ξ := by
  unfold partitionFunction LinkWindow.haarProd
  exact integral_congr_ae (Filter.Eventually.of_forall fun V => exp_windowAction_eq ha W β V ξ)
theorem integrable_boltzmannWeight (W : LinkWindow a) (β : ℝ) (ξ : GaugeField a) :
    Integrable (boltzmannWeight β W.links ξ) (Matrices.ComplexMatrix2.haarPi W.links) := by
  have := WilsonOperator.secondCountable_specialUnitary
  exact (WilsonOperator.continuous_boltzmannWeight β ξ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
theorem partitionFunction_pos (W : LinkWindow a) (β : ℝ) (ξ : GaugeField a) :
    0 < partitionFunction β W.links ξ :=
  integral_exp_pos (integrable_boltzmannWeight W β ξ)
theorem isProbabilityMeasure_wilsonSpecification (W : LinkWindow a) (β : ℝ) (ξ : GaugeField a) :
    IsProbabilityMeasure (wilsonSpecification β W.links ξ) := by
  have hZ := partitionFunction_pos W β ξ
  have hl : ∫⁻ v, ENNReal.ofReal (boltzmannWeight β W.links ξ v)
      ∂Matrices.ComplexMatrix2.haarPi W.links =
        ENNReal.ofReal (partitionFunction β W.links ξ) :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_boltzmannWeight W β ξ)
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).symm
  constructor
  simp only [wilsonSpecification, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hl]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hZ).ne' ENNReal.ofReal_ne_top
theorem conditionalAverage_eq_wilsonKernel (ha : 0 < a) (W : LinkWindow a) (β : ℝ)
    (F : GaugeField a → ℂ) (ξ : GaugeField a) :
    W.conditionalAverage ha β F ξ = W.wilsonKernel ha β F ξ := by
  have hk : ∀ V : W.Assignments, (W.densityKernel ha β V ξ : ℂ) =
      (Real.exp (-β * W.windowAction (W.glue ha V ξ)) : ℂ) /
        ((∫ V', Real.exp (-β * W.windowAction (W.glue ha V' ξ)) ∂W.haarProd : ℝ) : ℂ) :=
    fun V => Complex.ofReal_div _ _
  unfold LinkWindow.wilsonKernel LinkWindow.conditionalAverage
  simp only [hk, ← mul_div_assoc]
  rw [integral_div]
theorem conditionalAverage_eq_integral (ha : 0 < a) (W : LinkWindow a) (β : ℝ)
    (F : GaugeField a → ℂ) (ξ : GaugeField a) :
    W.conditionalAverage ha β F ξ = ∫ V, F (W.glue ha V ξ) ∂wilsonSpecification β W.links ξ := by
  have := WilsonOperator.secondCountable_specialUnitary
  have hm : Measurable fun V : W.Assignments => ENNReal.ofReal (boltzmannWeight β W.links ξ V) :=
    ENNReal.measurable_ofReal.comp (WilsonOperator.continuous_boltzmannWeight β ξ).measurable
  have hZ := (partitionFunction_pos W β ξ).le
  have hn : ∀ V : W.Assignments,
      F (W.glue ha V ξ) * (Real.exp (-β * W.windowAction (W.glue ha V ξ)) : ℂ) =
        (ENNReal.ofReal (boltzmannWeight β W.links ξ V)).toReal • F (W.glue ha V ξ) := by
    intro V
    have hw : 0 ≤ boltzmannWeight β W.links ξ V := (Real.exp_pos _).le
    rw [ENNReal.toReal_ofReal hw, exp_windowAction_eq ha W β V ξ, Complex.real_smul, mul_comm]
  unfold LinkWindow.conditionalAverage
  rw [integral_exp_windowAction_eq ha W β ξ]
  simp only [hn]
  unfold wilsonSpecification
  rw [integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ, Complex.real_smul, Complex.ofReal_inv,
    div_eq_inv_mul]
  rfl
end WindowSpecificationForms
open WindowSpecificationForms in
theorem WindowSpecificationForms.holds : WindowSpecificationForms.Statement := by
  intro a ha β _ W ξ
  exact ⟨integral_exp_windowAction_eq ha W β ξ, isProbabilityMeasure_wilsonSpecification W β ξ,
    fun F _ => ⟨conditionalAverage_eq_wilsonKernel ha W β F ξ,
      conditionalAverage_eq_integral ha W β F ξ⟩⟩
end YangMills.Construction.InfiniteLattice
