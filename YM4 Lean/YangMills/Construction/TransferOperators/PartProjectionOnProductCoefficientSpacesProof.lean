import YangMills.Construction.TransferOperators.ComponentFunctionsOfTheProjections
import YangMills.Construction.TransferOperators.HatIsLinearAndKeepsRealFunctionsProof
import YangMills.Construction.TransferOperators.PartProjectionOnProductCoefficientSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.SpinHarmonics.PartialIsotypicProjection
variable {ι : Type} [Finite ι]
omit [Finite ι] in
theorem glue_restrictTo (S : Set ι) (g : ι → specialUnitary) :
    glue S (restrictTo S g) (restrictTo Sᶜ g) = g :=
  (splitEquiv S).left_inv g
theorem partIsotypicProjC_apply (S : Set ι) (k : ↥S → HalfNatural) (f : C(ι → specialUnitary, ℂ))
    (g : ι → specialUnitary) :
    partIsotypicProjC S k f g = ∫ h, isotypicKernel k (restrictTo S g) h *
      f (glue S h (restrictTo Sᶜ g)) ∂haarPi ↥S :=
  rfl
theorem integrable_partKernelIntegrand (S : Set ι) (k : ↥S → HalfNatural)
    (f : C(ι → specialUnitary, ℂ)) (g : ι → specialUnitary) :
    Integrable (fun h => isotypicKernel k (restrictTo S g) h *
      f (glue S h (restrictTo Sᶜ g))) (haarPi ↥S) := by apply _root_.YangMills.Construction.SpinHarmonics.HatLinearReal.integrable_isotypicIntegrand <;> assumption
theorem partIsotypicProjC_zero (S : Set ι) (k : ↥S → HalfNatural) :
    partIsotypicProjC S k 0 = 0 := by
  ext g
  rw [partIsotypicProjC_apply]
  simp
theorem partIsotypicProjC_add (S : Set ι) (k : ↥S → HalfNatural) (f₁ f₂ : C(ι → specialUnitary, ℂ)) :
    partIsotypicProjC S k (f₁ + f₂) =
      partIsotypicProjC S k f₁ + partIsotypicProjC S k f₂ := by
  ext g
  rw [ContinuousMap.add_apply, partIsotypicProjC_apply, partIsotypicProjC_apply,
    partIsotypicProjC_apply,
    ← integral_add (integrable_partKernelIntegrand S k f₁ g) (integrable_partKernelIntegrand S k f₂ g)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [ContinuousMap.add_apply, mul_add]
theorem partIsotypicProjC_smul (S : Set ι) (k : ↥S → HalfNatural) (c : ℂ)
    (f : C(ι → specialUnitary, ℂ)) :
    partIsotypicProjC S k (c • f) = c • partIsotypicProjC S k f := by
  ext g
  rw [ContinuousMap.smul_apply, partIsotypicProjC_apply, partIsotypicProjC_apply, smul_eq_mul,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  ring
theorem coordProduct_glue (S : Set ι) (χ : ι → C(specialUnitary, ℂ)) (x : ↥S → specialUnitary)
    (y : ↥Sᶜ → specialUnitary) :
    coordProduct χ (glue S x y) =
      coordProduct (fun i : ↥S => χ i) x * coordProduct (fun i : ↥Sᶜ => χ i) y := by
  change (∏ᶠ i, χ i (glue S x y i)) =
    (∏ᶠ i : ↥S, χ i (x i)) * ∏ᶠ i : ↥Sᶜ, χ i (y i)
  rw [finprod_eq_mul_finprod_subtype_compl S]
  congr 1
  · exact finprod_congr fun i => by rw [glue_of_mem]
  · exact finprod_congr fun i => by rw [glue_of_notMem]
theorem partIsotypicProjC_tensor (hsum : IsotypicPartSums.Statement) (S : Set ι)
    [Nonempty ↥S] (k : ↥S → HalfNatural) (f : C(ι → specialUnitary, ℂ))
    (α : C(↥S → specialUnitary, ℂ)) (β : C(↥Sᶜ → specialUnitary, ℂ))
    (hf : ∀ x y, f (glue S x y) = α x * β y) (g : ι → specialUnitary) :
    partIsotypicProjC S k f g =
      isotypicPartSum k (toHaarL2 (α : (↥S → specialUnitary) → ℂ)) (restrictTo S g) *
        β (restrictTo Sᶜ g) := by
  rw [(hsum ↥S).2.1 k α (restrictTo S g), ← integral_mul_const, partIsotypicProjC_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [hf, mul_assoc]
theorem partIsotypicProjC_coordProduct (hsum : IsotypicPartSums.Statement) (S : Set ι)
    [Nonempty ↥S] (w : ι → HalfNatural) (k : ↥S → HalfNatural) (χ : ι → C(specialUnitary, ℂ))
    (hχ : ∀ i, χ i ∈ coeffSpan (w i)) :
    (k = restrictTo S w →
      partIsotypicProjC S k (coordProduct χ) = coordProduct χ) ∧
    (k ≠ restrictTo S w → partIsotypicProjC S k (coordProduct χ) = 0) := by
  have hα : coordProduct (fun i : ↥S => χ i) ∈ prodCoeffSpan (restrictTo S w) :=
    Submodule.subset_span ⟨_, fun i => hχ i, rfl⟩
  have hsel := (hsum ↥S).2.2 (restrictTo S w) k _ hα
  have hglue := coordProduct_glue S χ
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · subst hk
    ext g
    rw [partIsotypicProjC_tensor hsum S _ _ _ _ hglue, hsel.1, ← hglue,
      glue_restrictTo]
  · ext g
    rw [partIsotypicProjC_tensor hsum S _ _ _ _ hglue, hsel.2 hk]
    simp
theorem partProjOnProdCoeffSpan (hsum : IsotypicPartSums.Statement) :
    PartProjOnProdCoeffSpanStatement := by
  intro ι _ _ S w χ k hS hχ
  have : Nonempty ↥S := hS.to_subtype
  induction hχ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, hφ, rfl⟩ := hx
    exact partIsotypicProjC_coordProduct hsum S w k φ hφ
  | zero => exact ⟨fun _ => partIsotypicProjC_zero S k, fun _ => partIsotypicProjC_zero S k⟩
  | add x y _ _ hx hy =>
    exact ⟨fun hk => by rw [partIsotypicProjC_add, hx.1 hk, hy.1 hk],
      fun hk => by rw [partIsotypicProjC_add, hx.2 hk, hy.2 hk, add_zero]⟩
  | smul c x _ hx =>
    exact ⟨fun hk => by rw [partIsotypicProjC_smul, hx.1 hk],
      fun hk => by rw [partIsotypicProjC_smul, hx.2 hk, smul_zero]⟩
end YangMills.Construction.SpinHarmonics.PartialIsotypicProjection
end
