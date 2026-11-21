import YangMills.Construction.HullsInEveryVolume.KernelOfAWindowIsContinuousAndBounded
import YangMills.Construction.InfiniteLattice.WilsonKernelOfBondsWithOneOrientation
import YangMills.Construction.Matrices.UnitaryLogarithmClosedForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory InfiniteLattice Matrices
namespace HullsInEveryVolume
namespace WindowKernel
attribute [local instance] WilsonOperator.secondCountable_specialUnitary
variable {a : ℝ} (W : LinkWindow a) (ha : 0 < a)
private theorem continuous_apply_pair {A X Y Z : Type*} [TopologicalSpace A] [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y → Z}
    (hf : Continuous fun p : X × Y => f p.1 p.2) {g : A → X} {h : A → Y} (hg : Continuous g)
    (hh : Continuous h) : Continuous fun t => f (g t) (h t) :=
  hf.comp (hg.prodMk hh)
private theorem secondCountable_gaugeField : SecondCountableTopology (GaugeField a) := by
  have := WilsonOperator.countable_link (a := a)
  have : SecondCountableTopology (Link a → ComplexMatrix2.specialUnitary) := inferInstance
  exact TopologicalSpace.Subtype.secondCountableTopology
    {U : Link a → ComplexMatrix2.specialUnitary | ∀ b, U b.opposite = (U b)⁻¹}
private theorem isProbability_haarProd : IsProbabilityMeasure W.haarProd := by
  unfold LinkWindow.haarProd ComplexMatrix2.haarPi
  infer_instance
private theorem continuous_glue :
    Continuous fun p : W.Assignments × GaugeField a => W.glue ha p.1 p.2 := by
  classical
  have key : Continuous fun p : W.Assignments × GaugeField a =>
      ((W.glue ha p.1 p.2 : GaugeField a) : Link a → ComplexMatrix2.specialUnitary) := by
    refine continuous_pi fun b => ?_
    by_cases h : b ∈ W.links
    · have e : ∀ p : W.Assignments × GaugeField a, W.glue ha p.1 p.2 b = p.1 ⟨b, h⟩ :=
        fun p => dif_pos h
      simp only [e]
      exact (continuous_apply _).comp continuous_fst
    · by_cases h' : b.opposite ∈ W.links
      · have e : ∀ p : W.Assignments × GaugeField a,
            W.glue ha p.1 p.2 b = (p.1 ⟨b.opposite, h'⟩)⁻¹ := fun p => by
          simp [LinkWindow.glue, h, h']
        simp only [e]
        exact ((continuous_apply _).comp continuous_fst).inv
      · have e : ∀ p : W.Assignments × GaugeField a, W.glue ha p.1 p.2 b = p.2 b := fun p => by
          simp [LinkWindow.glue, h, h']
        simp only [e]
        exact (continuous_gaugeField_eval b).comp continuous_snd
  exact Continuous.subtype_mk key _
private theorem faceEnergy_mem_Icc (hT : ComplexMatrix2.UnitaryLogarithmProperties) (U : GaugeField a)
    (p : ElementaryPlaquette a) : faceEnergy U p ∈ Set.Icc (0 : ℝ) 2 := by
  obtain ⟨t, ⟨h₁, h₂⟩, ht⟩ := (hT.2.1 _ (faceHolonomy U p).2).1
  have h : (1 / 2) * (ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2)).re = t := by
    have := congrArg Complex.re ht
    simpa [ComplexMatrix2.halfTrace, Complex.mul_re] using this
  unfold faceEnergy
  rw [h]
  constructor <;> linarith
private theorem window_faces_finite : W.faces.Finite := WilsonOperator.facesTouching_finite W.links
private theorem faceEnergy_sum_bounds (hT : ComplexMatrix2.UnitaryLogarithmProperties) (U : GaugeField a) :
    0 ≤ ∑ᶠ p ∈ W.faces, faceEnergy U p ∧
      ∑ᶠ p ∈ W.faces, faceEnergy U p ≤ 2 * W.faceCount := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (window_faces_finite W)]
  have hcard : (W.faceCount : ℝ) = ((window_faces_finite W).toFinset.card : ℝ) := by
    rw [LinkWindow.faceCount, Set.ncard_eq_toFinset_card _ (window_faces_finite W)]
  refine ⟨Finset.sum_nonneg fun p _ => (faceEnergy_mem_Icc hT U p).1, ?_⟩
  rw [hcard]
  calc ∑ p ∈ (window_faces_finite W).toFinset, faceEnergy U p
      ≤ ∑ _p ∈ (window_faces_finite W).toFinset, (2 : ℝ) :=
        Finset.sum_le_sum fun p _ => (faceEnergy_mem_Icc hT U p).2
    _ = 2 * ((window_faces_finite W).toFinset.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
private theorem boltzmannWeight_bounds (hT : ComplexMatrix2.UnitaryLogarithmProperties) {β : ℝ} (hβ : 0 < β)
    (V : W.Assignments) (U : GaugeField a) :
    Real.exp (-(2 * β * W.faceCount)) ≤ W.boltzmannWeight ha β V U ∧ W.boltzmannWeight ha β V U ≤ 1 := by
  obtain ⟨h0, h2⟩ := faceEnergy_sum_bounds W hT (W.glue ha V U)
  unfold LinkWindow.boltzmannWeight
  constructor
  · apply Real.exp_le_exp.mpr
    nlinarith
  · apply Real.exp_le_one_iff.mpr
    nlinarith
private theorem continuous_boltzmannWeight (β : ℝ) :
    Continuous fun p : W.Assignments × GaugeField a => W.boltzmannWeight ha β p.1 p.2 := by
  unfold LinkWindow.boltzmannWeight
  have hs : (fun p : W.Assignments × GaugeField a =>
      ∑ᶠ q ∈ W.faces, faceEnergy (W.glue ha p.1 p.2) q) =
      fun p => ∑ q ∈ (window_faces_finite W).toFinset, faceEnergy (W.glue ha p.1 p.2) q := by
    funext p
    exact finsum_mem_eq_finite_toFinset_sum _ _
  refine Real.continuous_exp.comp (continuous_const.mul ?_)
  rw [hs]
  exact continuous_finsetSum _ fun q _ => (continuous_faceEnergy q).comp (continuous_glue W ha)
private theorem integrable_boltzmannWeight (β : ℝ) (U : GaugeField a) :
    Integrable (fun V => W.boltzmannWeight ha β V U) W.haarProd := by
  have := isProbability_haarProd W
  have hcont : Continuous fun V : W.Assignments => W.boltzmannWeight ha β V U :=
    continuous_apply_pair (f := W.boltzmannWeight ha β) (continuous_boltzmannWeight W ha β)
      continuous_id continuous_const
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
private theorem partitionFunction_bounds (hT : ComplexMatrix2.UnitaryLogarithmProperties) {β : ℝ} (hβ : 0 < β)
    (U : GaugeField a) :
    Real.exp (-(2 * β * W.faceCount)) ≤ ∫ V, W.boltzmannWeight ha β V U ∂W.haarProd ∧
      ∫ V, W.boltzmannWeight ha β V U ∂W.haarProd ≤ 1 := by
  have := isProbability_haarProd W
  have hi := integrable_boltzmannWeight W ha β U
  constructor
  · have := integral_mono (integrable_const _) hi fun V => (boltzmannWeight_bounds W ha hT hβ V U).1
    simpa using this
  · have := integral_mono hi (integrable_const _) fun V => (boltzmannWeight_bounds W ha hT hβ V U).2
    simpa using this
private theorem continuous_partitionFunction (hT : ComplexMatrix2.UnitaryLogarithmProperties) {β : ℝ}
    (hβ : 0 < β) :
    Continuous fun U : GaugeField a => ∫ V, W.boltzmannWeight ha β V U ∂W.haarProd := by
  have := isProbability_haarProd W
  have := secondCountable_gaugeField (a := a)
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ))
    (fun U => (integrable_boltzmannWeight W ha β U).aestronglyMeasurable)
    (fun U => ae_of_all _ fun V => ?_) (integrable_const _) (ae_of_all _ fun V => ?_)
  · have h := boltzmannWeight_bounds W ha hT hβ V U
    rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le (Real.exp_pos _) h.1)]
    exact h.2
  · exact continuous_apply_pair (f := W.boltzmannWeight ha β) (continuous_boltzmannWeight W ha β)
      continuous_const continuous_id
end WindowKernel
open WindowKernel in
theorem windowKernelContinuousBounded_of_unitaryLogarithm (hT : ComplexMatrix2.UnitaryLogarithmProperties) :
    windowKernelContinuousBounded := by
  intro a ha β hβ W
  have hz : ∀ U : GaugeField a, 0 < ∫ V, W.boltzmannWeight ha β V U ∂W.haarProd := fun U =>
    lt_of_lt_of_le (Real.exp_pos _) (partitionFunction_bounds W ha hT hβ U).1
  refine ⟨?_, fun V U => ?_, fun U => ?_⟩
  · unfold LinkWindow.densityKernel
    exact (continuous_boltzmannWeight W ha β).div ((continuous_partitionFunction W ha hT hβ).comp continuous_snd)
      fun p => (hz p.2).ne'
  · obtain ⟨hw0, hw1⟩ := boltzmannWeight_bounds W ha hT hβ V U
    obtain ⟨hz0, hz1⟩ := partitionFunction_bounds W ha hT hβ U
    have hE : Real.exp (2 * β * W.faceCount) * Real.exp (-(2 * β * W.faceCount)) = 1 := by
      rw [← Real.exp_add]
      simp
    unfold LinkWindow.densityKernel
    constructor
    · rw [le_div_iff₀ (hz U)]
      calc Real.exp (-(2 * β * W.faceCount)) * ∫ V, W.boltzmannWeight ha β V U ∂W.haarProd
          ≤ Real.exp (-(2 * β * W.faceCount)) * 1 :=
            mul_le_mul_of_nonneg_left hz1 (Real.exp_pos _).le
        _ ≤ W.boltzmannWeight ha β V U := by simpa using hw0
    · rw [div_le_iff₀ (hz U)]
      calc W.boltzmannWeight ha β V U ≤ 1 := hw1
        _ = Real.exp (2 * β * W.faceCount) * Real.exp (-(2 * β * W.faceCount)) := hE.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hz0 (Real.exp_pos _).le
  · simp only [LinkWindow.densityKernel]
    rw [integral_div, div_self (hz U).ne']
end HullsInEveryVolume
end YangMills.Construction
end
