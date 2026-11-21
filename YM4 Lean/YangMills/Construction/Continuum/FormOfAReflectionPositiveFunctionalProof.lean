import YangMills.Construction.Continuum.FormOfAReflectionPositiveFunctional
import YangMills.Construction.ReflectionPositivity.PropertiesOfTheFormOfAFunctionalProof
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositiveForm
open SeparatedTuples ReflectionPositivity.TupleForm HilbertSpaceBasics
section Generic
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {b : V → V → ℂ}
theorem posSemidef_self_eq_ofReal_re (h : IsPosSemidef b) (F : V) :
    b F F = ((b F F).re : ℂ) := by
  have him := (Complex.le_def.mp (h.nonneg F)).2
  apply Complex.ext
  · simp
  · simpa using him.symm
theorem posSemidef_norm_sq_le (h : IsPosSemidef b) (F G : V) :
    ‖b F G‖ ^ 2 ≤ (b F F).re * (b G G).re := by
  let _ := toPreInnerCore h
  have hcs := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) F G
  change ‖b F G‖ * ‖b G F‖ ≤ (b F F).re * (b G G).re at hcs
  rw [h.isHermitianForm F G, RCLike.norm_conj] at hcs
  rw [sq]
  exact hcs
theorem posSemidef_cauchy_schwarz (h : IsPosSemidef b) (F G : V) :
    ((‖b F G‖ ^ 2 : ℝ) : ℂ) ≤ b F F * b G G := by
  rw [posSemidef_self_eq_ofReal_re h F, posSemidef_self_eq_ofReal_re h G, ← Complex.ofReal_mul]
  exact_mod_cast posSemidef_norm_sq_le h F G
theorem posSemidef_apply_null_right (h : IsPosSemidef b) {N : V} (hN : b N N = 0) (G : V) :
    b G N = 0 := by
  have h0 : ‖b G N‖ ^ 2 ≤ 0 := by simpa [hN] using posSemidef_norm_sq_le h G N
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (le_antisymm h0 (sq_nonneg _)))
theorem posSemidef_apply_null_left (h : IsPosSemidef b) {N : V} (hN : b N N = 0) (G : V) :
    b N G = 0 := by
  rw [h.isHermitianForm G N, posSemidef_apply_null_right h hN G, map_zero]
theorem posSemidef_add_null (h : IsPosSemidef b) (F G : V) {N N' : V} (hN : b N N = 0)
    (hN' : b N' N' = 0) : b (F + N) (G + N') = b F G := by
  rw [h.add_left, h.add_right, h.add_right, posSemidef_apply_null_right h hN' F,
    posSemidef_apply_null_left h hN G, posSemidef_apply_null_left h hN N']
  simp
theorem coe_selfNullSpan (h : IsPosSemidef b) :
    (selfNullSpan b : Set V) = selfNullSet b := by
  let S : Submodule ℂ V :=
    { carrier := selfNullSet b
      add_mem' := fun {F G} hF hG => by
        change b (F + G) (F + G) = 0
        rw [h.add_left, h.add_right, h.add_right, posSemidef_apply_null_right h hF F,
          posSemidef_apply_null_right h hG F, posSemidef_apply_null_left h hG F,
          posSemidef_apply_null_left h hG G]
        simp
      zero_mem' := by
        have h0 := h.smul_left 0 0 0
        change b 0 0 = 0
        simpa using h0
      smul_mem' := fun z F hF => by
        change b (z • F) (z • F) = 0
        rw [h.smul_left, h.smul_right, show b F F = 0 from hF]
        simp }
  have hS : selfNullSpan b = S := Submodule.span_eq S
  rw [hS]
  rfl
theorem descendedForm_nullClass (h : IsPosSemidef b) (F G : V) :
    descendedForm b (nullClass b F) (nullClass b G) = b F G := by
  have hrep : ∀ K : V, ∃ N : V, b N N = 0 ∧
      Function.surjInv (Submodule.Quotient.mk_surjective (selfNullSpan b)) (nullClass b K) =
        K + N := by
    intro K
    set K' := Function.surjInv (Submodule.Quotient.mk_surjective (selfNullSpan b))
      (nullClass b K) with hK'
    have hmk : (Submodule.Quotient.mk K' : V ⧸ selfNullSpan b) = Submodule.Quotient.mk K :=
      Function.surjInv_eq (Submodule.Quotient.mk_surjective (selfNullSpan b)) (nullClass b K)
    have hmem : K' - K ∈ selfNullSpan b := (Submodule.Quotient.eq _).1 hmk
    have hset : K' - K ∈ (selfNullSpan b : Set V) := hmem
    rw [coe_selfNullSpan h] at hset
    exact ⟨K' - K, hset, by abel⟩
  obtain ⟨N, hN, hF⟩ := hrep F
  obtain ⟨N', hN', hG⟩ := hrep G
  unfold descendedForm
  rw [hF, hG]
  exact posSemidef_add_null h F G hN hN'
theorem isInnerProductForm_descendedForm (h : IsPosSemidef b) :
    IsInnerProductForm (descendedForm b) := by
  have hs : ∀ u : NullQuotient b, ∃ F, nullClass b F = u :=
    Submodule.Quotient.mk_surjective _
  have hadd : ∀ F G, nullClass b F + nullClass b G = nullClass b (F + G) :=
    fun _ _ => rfl
  have hsmul : ∀ (z : ℂ) F, z • nullClass b F = nullClass b (z • F) := fun _ _ => rfl
  refine { add_left := ?_, smul_left := ?_, add_right := ?_, smul_right := ?_, nonneg := ?_,
           definite := ?_ }
  · intro u v w
    obtain ⟨F, rfl⟩ := hs u
    obtain ⟨G, rfl⟩ := hs v
    obtain ⟨K, rfl⟩ := hs w
    rw [hadd]
    simp only [descendedForm_nullClass h]
    exact h.add_left F G K
  · intro z u v
    obtain ⟨F, rfl⟩ := hs u
    obtain ⟨G, rfl⟩ := hs v
    rw [hsmul]
    simp only [descendedForm_nullClass h]
    exact h.smul_left z F G
  · intro u v w
    obtain ⟨F, rfl⟩ := hs u
    obtain ⟨G, rfl⟩ := hs v
    obtain ⟨K, rfl⟩ := hs w
    rw [hadd]
    simp only [descendedForm_nullClass h]
    exact h.add_right F G K
  · intro z u v
    obtain ⟨F, rfl⟩ := hs u
    obtain ⟨G, rfl⟩ := hs v
    rw [hsmul]
    simp only [descendedForm_nullClass h]
    exact h.smul_right z F G
  · intro u
    obtain ⟨F, rfl⟩ := hs u
    rw [descendedForm_nullClass h]
    exact h.nonneg F
  · intro u hu
    obtain ⟨F, rfl⟩ := hs u
    rw [descendedForm_nullClass h] at hu
    have hset : F ∈ (selfNullSpan b : Set V) := by
      rw [coe_selfNullSpan h]
      exact hu
    exact (Submodule.Quotient.mk_eq_zero _).2 hset
end Generic
theorem reflectionForm_self_nonneg (σ : TupleFunctional)
    (h : σ.IsReflectionPositive (Mirrors.axialHyperplane TimeAxis.timeIdx 0))
    (F : PositiveSpan) : 0 ≤ reflectionForm σ F F := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.reflectionForm_self_nonneg <;> assumption
theorem formPropertiesStatement_holds : FormPropertiesStatement := by
  intro σ h
  have hp : IsPosSemidef (reflectionForm σ) :=
    { toIsSesquilinear := isSesquilinear_reflectionForm σ, nonneg := reflectionForm_self_nonneg σ h }
  refine ⟨⟨isSesquilinear_reflectionForm σ, hp.nonneg⟩, ⟨hp.isHermitianForm, posSemidef_cauchy_schwarz hp⟩,
    coe_selfNullSpan hp, ?_, descendedForm_nullClass hp, isInnerProductForm_descendedForm hp⟩
  intro F F' N N' hN hN'
  exact posSemidef_add_null hp F F' hN hN'
end YangMills.Construction.ReflectionPositiveForm
end
