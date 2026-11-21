import YangMills.Construction.InfiniteLattice.TorusOfAPeriodLatticeIsFinite
import YangMills.Construction.Matrices.GluingFamiliesPreservesProductsOfHaarMeasuresForm
import YangMills.Construction.ReflectionPositivity.IntegralOverVariablesOfATorus
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2 YangMills.Construction.SpinHarmonics
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace IntegrateOut
section Gluing
variable {J : Type}
private lemma measurable_glue_pair (B : Set J) :
    Measurable fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2 := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases hj : j ∈ B
  · have hfun : (fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2 j) =
        fun p => p.1 ⟨j, hj⟩ := by
      funext p
      exact glue_of_mem B p.1 p.2 ⟨j, hj⟩
    rw [hfun]
    exact (measurable_pi_apply _).comp measurable_fst
  · have hfun : (fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2 j) =
        fun p => p.2 ⟨j, hj⟩ := by
      funext p
      exact glue_of_notMem B p.1 p.2 ⟨j, hj⟩
    rw [hfun]
    exact (measurable_pi_apply _).comp measurable_snd
abbrev _root_.YangMills.SharedProofs.p39109 := @measurable_glue_pair
private lemma restrictTo_compl_glue (B : Set J) (v : ↥B → specialUnitary) (z : ↥Bᶜ → specialUnitary) :
    SpinHarmonics.restrictTo Bᶜ (glue B v z) = z :=
  funext fun b => glue_of_notMem B v z b
private lemma measurable_restrictTo (B : Set J) :
    Measurable (SpinHarmonics.restrictTo (X := specialUnitary) B) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _
variable [Countable J]
private def fiberIntegral (B : Set J) (f : (J → specialUnitary) → ℂ) (z : ↥Bᶜ → specialUnitary) : ℂ :=
  ∫ v, f (glue B v z) ∂haarPi ↥B
private lemma measurable_fiberIntegral (B : Set J) {f : (J → specialUnitary) → ℂ} (hf : Measurable f) :
    Measurable (fiberIntegral B f) :=
  (StronglyMeasurable.integral_prod_left'
    (f := fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => f (glue B p.1 p.2))
    (μ := haarPi ↥B) (hf.comp (measurable_glue_pair B)).stronglyMeasurable).measurable
private lemma integrable_fiber (B : Set J) {f : (J → specialUnitary) → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ u, ‖f u‖ ≤ C) (z : ↥Bᶜ → specialUnitary) :
    Integrable (fun v => f (glue B v z)) (haarPi ↥B) := by
  have hmeas : Measurable fun v : ↥B → specialUnitary => f (glue B v z) :=
    hf.comp ((measurable_glue_pair B).comp (measurable_id.prodMk measurable_const))
  exact Integrable.of_bound hmeas.aestronglyMeasurable C (Filter.Eventually.of_forall fun v => hC _)
private lemma norm_fiberIntegral_le (B : Set J) {f : (J → specialUnitary) → ℂ} {C : ℝ}
    (hC : ∀ u, ‖f u‖ ≤ C) (z : ↥Bᶜ → specialUnitary) : ‖fiberIntegral B f z‖ ≤ C := by
  have hle := norm_integral_le_of_norm_le_const (μ := haarPi ↥B)
    (f := fun v => f (glue B v z)) (C := C) (Filter.Eventually.of_forall fun v => hC _)
  simpa [fiberIntegral] using hle
private lemma integral_eq_iterated [Finite J] (B : Set J)
    (hmp : MeasurePreserving (fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2)
      ((haarPi ↥B).prod (haarPi ↥Bᶜ)) (haarPi J))
    {h : (J → specialUnitary) → ℂ} (hh : Measurable h) {C : ℝ} (hC : ∀ u, ‖h u‖ ≤ C) :
    ∫ u, h u ∂haarPi J = ∫ z, ∫ v, h (glue B v z) ∂haarPi ↥B ∂haarPi ↥Bᶜ := by
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hh.aestronglyMeasurable,
    integral_prod_symm]
  exact Integrable.of_bound (hh.comp hmp.measurable).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun p => hC _)
private lemma integral_mul_eq_integral_mul_fiber [Finite J] (B : Set J)
    (hmp : MeasurePreserving (fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2)
      ((haarPi ↥B).prod (haarPi ↥Bᶜ)) (haarPi J))
    {f g : (J → specialUnitary) → ℂ} (hf : Measurable f) (hg : Measurable g) {C : ℝ}
    (hfC : ∀ u, ‖f u‖ ≤ C) (hgC : ∀ u, ‖g u‖ ≤ C)
    (hdep : ∀ u u' : J → specialUnitary, (∀ b ∈ Bᶜ, u b = u' b) → g u = g u') :
    ∫ u, g u * f u ∂haarPi J =
      ∫ u, g u * fiberIntegral B f (SpinHarmonics.restrictTo Bᶜ u) ∂haarPi J := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hfC (fun _ => 1))
  have hgz : ∀ (v : ↥B → specialUnitary) (z : ↥Bᶜ → specialUnitary),
      g (glue B v z) = g (glue B (fun _ => 1) z) := by
    intro v z
    refine hdep _ _ fun b hb => ?_
    rw [glue_of_notMem B v z ⟨b, hb⟩, glue_of_notMem B _ z ⟨b, hb⟩]
  have hleft : ∀ u, ‖g u * f u‖ ≤ C * C := fun u => by
    rw [norm_mul]
    exact mul_le_mul (hgC u) (hfC u) (norm_nonneg _) hC0
  have hright : ∀ u, ‖g u * fiberIntegral B f (SpinHarmonics.restrictTo Bᶜ u)‖ ≤
      C * C := fun u => by
    rw [norm_mul]
    exact mul_le_mul (hgC u) (norm_fiberIntegral_le B hfC _) (norm_nonneg _) hC0
  rw [integral_eq_iterated B hmp (h := fun u => g u * f u) (hg.mul hf) hleft,
    integral_eq_iterated B hmp
      (h := fun u => g u * fiberIntegral B f (SpinHarmonics.restrictTo Bᶜ u))
      (hg.mul ((measurable_fiberIntegral B hf).comp (measurable_restrictTo Bᶜ))) hright]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [restrictTo_compl_glue, hgz _ z]
  rw [integral_const_mul, integral_const]
  simp [fiberIntegral]
end Gluing
end IntegrateOut
open IntegrateOut in
theorem integrateOutProperties_holds (hglue : GlueMeasurePreserving)
    (hfin : PeriodQuotientFinite) : IntegrateOutProperties := by
  intro Γ M
  obtain ⟨-, hJ, -⟩ := hfin 1 one_pos Γ
  have hmp := hglue Γ.QuotientLink M
  have hI : ∀ (f : Γ.QuotientField → ℂ) (U : Γ.QuotientField),
      Γ.integrateOut M f U =
        fiberIntegral M f (SpinHarmonics.restrictTo Mᶜ U) := fun _ _ => rfl
  refine ⟨fun f C hf hC => ⟨?_, fun U => ?_, fun U U' hU => ?_⟩,
    fun f f' C w hf hf' hC hC' => ?_, fun f g C hf hg hfC hgC hdep => ?_⟩
  · exact (measurable_fiberIntegral M hf).comp (measurable_restrictTo Mᶜ)
  · rw [hI]
    exact norm_fiberIntegral_le M hC _
  · rw [hI, hI]
    congr 1
    funext b
    exact hU b b.2
  · funext U
    simp only [hI, Pi.add_apply, Pi.smul_apply, fiberIntegral, smul_eq_mul]
    rw [integral_add ((integrable_fiber M hf hC _).const_mul w)
      (integrable_fiber M hf' hC' _), integral_const_mul]
  · exact integral_mul_eq_integral_mul_fiber M hmp hf hg hfC hgC hdep
end YangMills.Construction.InfiniteLattice
end
