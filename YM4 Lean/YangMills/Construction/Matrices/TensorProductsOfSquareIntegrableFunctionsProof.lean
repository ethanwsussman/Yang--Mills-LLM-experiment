import YangMills.Construction.Matrices.GluingFamiliesPreservesProductsOfHaarMeasuresForm
import YangMills.Construction.Matrices.TensorProductsOfSquareIntegrableFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.SpinHarmonics.TensorL2
def glueMeasurableEquiv {J : Type} (B : Set J)
    (hm : Measurable fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2) :
    ((↥B → specialUnitary) × (↥Bᶜ → specialUnitary)) ≃ᵐ (J → specialUnitary) where
  toEquiv := (splitEquiv B).symm
  measurable_toFun := hm
  measurable_invFun :=
    (measurable_pi_lambda _ fun _ => measurable_pi_apply _).prodMk
      (measurable_pi_lambda _ fun _ => measurable_pi_apply _)
theorem inner_toHaarL2 {K : Type} [Countable K] {F G : (K → specialUnitary) → ℂ}
    (hF : MemLp F 2 (haarPi K)) (hG : MemLp G 2 (haarPi K)) :
    (inner ℂ (toHaarL2 F) (toHaarL2 G) : ℂ) = ∫ u, inner ℂ (F u) (G u) ∂haarPi K := by
  unfold toHaarL2
  rw [dif_pos hF, dif_pos hG, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with u h₁ h₂
  rw [h₁, h₂]
theorem memLp_mul_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {f : α → ℂ} {h : β → ℂ}
    (hf : MemLp f 2 μ) (hh : MemLp h 2 ν) :
    MemLp (fun p : α × β => f p.1 * h p.2) 2 (μ.prod ν) := by
  have meas : AEStronglyMeasurable (fun p : α × β => f p.1 * h p.2) (μ.prod ν) :=
    hf.1.comp_fst.mul hh.1.comp_snd
  rw [memLp_two_iff_integrable_sq_norm meas]
  have h₁ := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have h₂ := (memLp_two_iff_integrable_sq_norm hh.1).1 hh
  refine (h₁.mul_prod h₂).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [norm_mul, mul_pow]
theorem memLp_tensorFn {J : Type} [Finite J] (B : Set J)
    (hj : MeasurePreserving (fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2)
      ((haarPi ↥B).prod (haarPi ↥Bᶜ)) (haarPi J))
    {f : (↥B → specialUnitary) → ℂ} {h : (↥Bᶜ → specialUnitary) → ℂ}
    (hf : MemLp f 2 (haarPi ↥B)) (hh : MemLp h 2 (haarPi ↥Bᶜ)) :
    MemLp (tensorFn B f h) 2 (haarPi J) := by
  have hmap : Measure.map (glueMeasurableEquiv B hj.measurable)
      ((haarPi ↥B).prod (haarPi ↥Bᶜ)) = haarPi J := hj.map_eq
  have hcomp : tensorFn B f h ∘ glueMeasurableEquiv B hj.measurable =
      fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => f p.1 * h p.2 :=
    funext fun p => tensorFn_glue B f h p.1 p.2
  rw [← hmap, MeasurableEquiv.memLp_map_measure_iff, hcomp]
  exact memLp_mul_prod hf hh
theorem tensorFnMemL2Inner_of_glue (hglue : GlueMeasurePreserving) : TensorFnMemL2Inner := by
  intro J _ B f f' h h' hf hf' hh hh'
  have hj := hglue J B
  have ht := memLp_tensorFn B hj hf hh
  have ht' := memLp_tensorFn B hj hf' hh'
  refine ⟨ht, ?_⟩
  rw [inner_toHaarL2 ht ht', inner_toHaarL2 hf hf', inner_toHaarL2 hh hh']
  have he : MeasurePreserving (glueMeasurableEquiv B hj.measurable)
      ((haarPi ↥B).prod (haarPi ↥Bᶜ)) (haarPi J) := hj
  rw [← he.integral_comp' fun u => (inner ℂ (tensorFn B f h u)
      (tensorFn B f' h' u) : ℂ),
    ← integral_prod_mul (fun v => (inner ℂ (f v) (f' v) : ℂ))
      (fun z => (inner ℂ (h z) (h' z) : ℂ))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  change (inner ℂ (tensorFn B f h (glue B p.1 p.2))
      (tensorFn B f' h' (glue B p.1 p.2)) : ℂ) =
    inner ℂ (f p.1) (f' p.1) * inner ℂ (h p.2) (h' p.2)
  rw [tensorFn_glue, tensorFn_glue]
  simp only [RCLike.inner_apply, map_mul]
  ring
end YangMills.Construction.SpinHarmonics.TensorL2
end
