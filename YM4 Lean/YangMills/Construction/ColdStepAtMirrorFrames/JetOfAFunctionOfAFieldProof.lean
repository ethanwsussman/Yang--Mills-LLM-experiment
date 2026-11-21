import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeAlongAFlowProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
theorem singleBondForm_apply {j : ℕ} {B : Finset (F.Site j × Fin 4)} (b b' : ↥B) (X : imaginaryQuaternions) :
    singleBondForm b X b' = if b' = b then X else 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlowDerivative.singleBondForm_apply <;> assumption
theorem sum_singleBondForm {j : ℕ} {B : Finset (F.Site j × Fin 4)} (Z : ↥B → imaginaryQuaternions) :
    ∑ b, singleBondForm b (Z b) = Z := by
  classical
  funext b'
  simp [Finset.sum_apply, singleBondForm_apply]
theorem singleBondForm_smul {j : ℕ} {B : Finset (F.Site j × Fin 4)} (b : ↥B) (r : ℝ) (X : imaginaryQuaternions) :
    singleBondForm b (r • X) = r • singleBondForm b X := by
  classical
  funext b'
  simp only [singleBondForm_apply, Pi.smul_apply]
  split_ifs <;> simp
theorem singleBondForm_zero {j : ℕ} {B : Finset (F.Site j × Fin 4)} (b : ↥B) :
    singleBondForm b (0 : imaginaryQuaternions) = 0 := by
  classical
  funext b'
  simp only [singleBondForm_apply, Pi.zero_apply]
  split_ifs <;> rfl
def coefficientsToForms {j k : ℕ} {B : Finset (F.Site j × Fin 4)} (c : Fin k → ↥B) (X : Fin k → imaginaryQuaternions) :
    (Fin k → ℝ) →L[ℝ] (↥B → imaginaryQuaternions) :=
  ∑ l, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l).smulRight (singleBondForm (c l) (X l))
theorem coefficientsToForms_apply {j k : ℕ} {B : Finset (F.Site j × Fin 4)} (c : Fin k → ↥B)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) :
    coefficientsToForms c X τ = ∑ l, τ l • singleBondForm (c l) (X l) := by
  simp [coefficientsToForms]
theorem extendByZero_coefficientsToForms {j k : ℕ} {B : Finset (F.Site j × Fin 4)} (c : Fin k → ↥B)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) :
    extendByZero (coefficientsToForms c X τ) = bondSpread (fun l => (c l).1) X τ := by
  classical
  funext y i
  unfold extendByZero bondSpread
  rw [coefficientsToForms_apply]
  by_cases h : (y, i) ∈ B
  · rw [dif_pos h]
    simp only [Finset.sum_apply, Pi.smul_apply, singleBondForm_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases e : c l = ⟨(y, i), h⟩
    · simp [e]
    · have e' : ¬ (c l).1 = (y, i) := fun q => e (Subtype.ext q)
      simp [e, e', eq_comm]
  · rw [dif_neg h]
    symm
    refine Finset.sum_eq_zero fun l _ => ?_
    have e' : ¬ (c l).1 = (y, i) := fun q => h (q ▸ (c l).2)
    simp [e']
theorem formCompositionJet_holds : FormCompositionJet := by
  intro E _ _ F j B G W hG
  classical
  have hC : ContDiffAt ℝ 3 (formComposition B G W) 0 := by
    let bas := Module.finBasis ℝ imaginaryQuaternions
    let r := Module.finrank ℝ imaginaryQuaternions
    let e : Fin (Fintype.card (↥B × Fin r)) ≃ ↥B × Fin r := (Fintype.equivFin _).symm
    let c : Fin (Fintype.card (↥B × Fin r)) → ↥B := fun l => (e l).1
    let X : Fin (Fintype.card (↥B × Fin r)) → imaginaryQuaternions := fun l => bas (e l).2
    have h0 := hG _ (fun l => (c l).1) X
    let s₀ : (↥B → imaginaryQuaternions) →ₗ[ℝ] (Fin (Fintype.card (↥B × Fin r)) → ℝ) :=
      { toFun := fun A l => bas.repr (A (e l).1) (e l).2
        map_add' := fun A A' => by funext l; simp
        map_smul' := fun t A => by funext l; simp }
    let s : (↥B → imaginaryQuaternions) →L[ℝ] (Fin (Fintype.card (↥B × Fin r)) → ℝ) :=
      LinearMap.toContinuousLinearMap s₀
    have key : ∀ A : ↥B → imaginaryQuaternions, coefficientsToForms c X (s A) = A := by
      intro A
      rw [coefficientsToForms_apply]
      funext b
      simp only [Finset.sum_apply, Pi.smul_apply, singleBondForm_apply]
      have e1 : ∑ x, s A x • (if b = c x then X x else 0) =
          ∑ q : ↥B × Fin r, (bas.repr (A q.1) q.2) • (if b = q.1 then bas q.2 else 0) :=
        Fintype.sum_equiv e _ _ (fun x => rfl)
      rw [e1, Fintype.sum_prod_type, Finset.sum_eq_single b]
      · simp only [if_true]
        exact bas.sum_repr (A b)
      · intro b' _ hb
        have : ¬ b = b' := fun q => hb q.symm
        simp [this]
      · simp
    have hjet : formComposition B G W =
        (fun τ => G (leftTranslate (bondSpread (fun l => (c l).1) X τ) W)) ∘ s := by
      funext A
      simp only [Function.comp, formComposition]
      rw [← extendByZero_coefficientsToForms, key]
    rw [hjet]
    have hs0 : s 0 = 0 := map_zero s
    exact ContDiffAt.comp (0 : ↥B → imaginaryQuaternions) (by rw [hs0]; exact h0) s.contDiff.contDiffAt
  have hE : ∀ (k : ℕ) (c : Fin k → ↥B) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
      iteratedFDeriv ℝ k (formComposition B G W) 0 (fun l => singleBondForm (c l) (X l)) =
        bondDeriv G W (fun l => (c l).1) X := by
    intro k c X hk
    obtain ⟨u, hu, hcu⟩ := hC.contDiffOn (m := 3) le_rfl (by simp)
    have hs := isOpen_interior (s := u)
    have h0s : (0 : ↥B → imaginaryQuaternions) ∈ interior u := mem_interior_iff_mem_nhds.mpr hu
    have hcs : ContDiffOn ℝ 3 (formComposition B G W) (interior u) := hcu.mono interior_subset
    let Λ := coefficientsToForms c X
    have hΛ0 : Λ 0 = 0 := map_zero Λ
    have hop : IsOpen (Λ ⁻¹' interior u) := hs.preimage Λ.continuous
    have h := ContinuousLinearMap.iteratedFDerivWithin_comp_right (f := formComposition B G W) (n := 3) Λ hcs
      hs.uniqueDiffOn hop.uniqueDiffOn (x := 0) (by rw [hΛ0]; exact h0s) (i := k) (by exact_mod_cast hk)
    rw [iteratedFDerivWithin_of_isOpen k hop (show (0 : Fin k → ℝ) ∈ Λ ⁻¹' interior u by
      show Λ 0 ∈ interior u
      rw [hΛ0]; exact h0s), hΛ0, iteratedFDerivWithin_of_isOpen k hs h0s] at h
    have hf : (formComposition B G W ∘ Λ) =
        fun τ => G (leftTranslate (bondSpread (fun l => (c l).1) X τ) W) := by
      funext τ
      simp only [Function.comp, formComposition, Λ]
      rw [extendByZero_coefficientsToForms]
    rw [hf] at h
    unfold bondDeriv
    rw [h]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext l
    show singleBondForm (c l) (X l) = Λ (Pi.single l 1)
    simp only [Λ, coefficientsToForms_apply]
    rw [Finset.sum_eq_single l]
    · simp
    · intro l' _ h'
      simp [h'.symm]
    · simp
  refine ⟨hC, hE, ?_⟩
  intro k e hk he0 he Z
  let m := iteratedFDeriv ℝ k (formComposition B G W) 0
  have hZ : Z = fun l => ∑ b, singleBondForm b (Z l b) := by
    funext l
    rw [sum_singleBondForm]
  have hsum : m Z = ∑ c : Fin k → ↥B, m (fun l => singleBondForm (c l) (Z l (c l))) := by
    conv_lhs => rw [hZ]
    exact m.toMultilinearMap.map_sum (fun l b => singleBondForm b (Z l b))
  show ‖m Z‖ ≤ _
  rw [hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  have hec : 0 ≤ e c := he0 c
  by_cases hz : ∃ l, Z l (c l) = 0
  · obtain ⟨l, hl⟩ := hz
    have h0 : m (fun l => singleBondForm (c l) (Z l (c l))) = 0 :=
      m.map_coord_zero l (by simp only [hl, singleBondForm_zero])
    rw [h0, norm_zero]
    exact mul_nonneg hec (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  · push Not at hz
    let X : Fin k → imaginaryQuaternions := fun l => ‖Z l (c l)‖⁻¹ • Z l (c l)
    have hX : AreUnitVectors X := fun l => by
      simp only [X, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hz l))
    have hform : (fun l => singleBondForm (c l) (Z l (c l))) =
        fun l => ‖Z l (c l)‖ • singleBondForm (c l) (X l) := by
      funext l
      rw [← singleBondForm_smul]
      simp only [X, smul_smul]
      rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hz l)), one_smul]
    rw [hform, m.map_smul_univ, hE k c X hk, norm_smul, mul_comm]
    have hp : ‖∏ l, ‖Z l (c l)‖‖ = ∏ l, ‖Z l (c l)‖ :=
      Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    rw [hp]
    exact mul_le_mul_of_nonneg_right (he c X hX) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
end YangMills.Construction.ColdStepAtMirrorFrames
end
