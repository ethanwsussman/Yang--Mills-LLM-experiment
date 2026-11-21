import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeAlongAFlow
import YangMills.Construction.ColdStepAtMirrorFrames.JetOfAFunctionOfAField
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfAMovedExponential
import YangMills.Construction.ColdStepAtMirrorFrames.ThreeDerivativesInASpace
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace FlowDerivative
section VectorSpaces
variable {E₁ E₂ E₃ : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
theorem iteratedFDeriv_comp_clm_zero (g : E₂ → E₃) (L : E₁ →L[ℝ] E₂) (n : ℕ) (hg : ContDiffAt ℝ n g 0)
    (v : Fin n → E₁) :
    iteratedFDeriv ℝ n (g ∘ L) 0 v = iteratedFDeriv ℝ n g 0 (fun l => L (v l)) := by
  obtain ⟨u, hu, hcu⟩ := hg.contDiffOn (m := n) le_rfl (by simp)
  have hs := isOpen_interior (s := u)
  have h0s : (0 : E₂) ∈ interior u := mem_interior_iff_mem_nhds.mpr hu
  have hcs : ContDiffOn ℝ n g (interior u) := hcu.mono interior_subset
  have hL0 : L 0 = 0 := map_zero L
  have hop : IsOpen (L ⁻¹' interior u) := hs.preimage L.continuous
  have h := ContinuousLinearMap.iteratedFDerivWithin_comp_right (f := g) (n := n) L hcs
    hs.uniqueDiffOn hop.uniqueDiffOn (x := 0) (by rw [hL0]; exact h0s) (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hop (show (0 : E₁) ∈ L ⁻¹' interior u by
    show L 0 ∈ interior u
    rw [hL0]; exact h0s), hL0, iteratedFDerivWithin_of_isOpen n hs h0s] at h
  rw [h]
  rfl
theorem hasDerivAt_iteratedFDeriv_slice (ψ : ℝ × E₁ → E₃) (n : ℕ) (v : Fin n → E₁)
    (hψ : ContDiffAt ℝ (n + 1 : ℕ) ψ 0) :
    HasDerivAt (fun h : ℝ => iteratedFDeriv ℝ n (fun τ => ψ (h, τ)) 0 v)
      (iteratedFDeriv ℝ (n + 1) ψ 0 (Fin.cons ((1 : ℝ), (0 : E₁)) fun l => ((0 : ℝ), v l))) 0 := by
  let w : Fin n → ℝ × E₁ := fun l => ((0 : ℝ), v l)
  have hinc : Continuous fun h : ℝ => ((h, (0 : E₁)) : ℝ × E₁) := by fun_prop
  have hev : ∀ᶠ h : ℝ in 𝓝 0, ContDiffAt ℝ (n + 1 : ℕ) ψ (h, (0 : E₁)) :=
    hinc.continuousAt.eventually (hψ.eventually (by simp))
  have e : (fun h : ℝ => iteratedFDeriv ℝ n (fun τ => ψ (h, τ)) 0 v) =ᶠ[𝓝 0]
      fun h : ℝ => iteratedFDeriv ℝ n ψ (h, (0 : E₁)) w := by
    refine hev.mono fun h hh => ?_
    let g : ℝ × E₁ → E₃ := fun z => ψ (z + (h, (0 : E₁)))
    have hg : ContDiffAt ℝ n g 0 := by
      have h1 : ContDiffAt ℝ n ψ ((0 : ℝ × E₁) + (h, (0 : E₁))) := by
        rw [zero_add]
        exact hh.of_le (by exact_mod_cast Nat.le_succ n)
      exact ContDiffAt.comp (0 : ℝ × E₁) h1 (by fun_prop)
    have h2 := iteratedFDeriv_comp_clm_zero g (ContinuousLinearMap.inr ℝ ℝ E₁) n hg v
    have h3 : (g ∘ (ContinuousLinearMap.inr ℝ ℝ E₁)) = fun τ => ψ (h, τ) := by
      funext τ
      simp [g]
    rw [h3] at h2
    have h4 := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := ψ) n ((h, (0 : E₁)) : ℝ × E₁) (0 : ℝ × E₁)
    rw [zero_add] at h4
    show iteratedFDeriv ℝ n (fun τ => ψ (h, τ)) 0 v = _
    rw [h2]
    show iteratedFDeriv ℝ n g 0 _ = _
    have h5 : iteratedFDeriv ℝ n g 0 = iteratedFDeriv ℝ n ψ (h, (0 : E₁)) := h4
    rw [h5]
    rfl
  have hM : DifferentiableAt ℝ (iteratedFDeriv ℝ n ψ) 0 :=
    hψ.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
  have hinc' : HasDerivAt (fun h : ℝ => ((h, (0 : E₁)) : ℝ × E₁)) ((1 : ℝ), (0 : E₁)) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const _ _)
  have h1 : HasDerivAt (fun h : ℝ => iteratedFDeriv ℝ n ψ (h, (0 : E₁)))
      (fderiv ℝ (iteratedFDeriv ℝ n ψ) 0 ((1 : ℝ), (0 : E₁))) 0 := by
    have hM' : HasFDerivAt (iteratedFDeriv ℝ n ψ) (fderiv ℝ (iteratedFDeriv ℝ n ψ) 0) ((0 : ℝ), (0 : E₁)) :=
      hM.hasFDerivAt
    exact hM'.comp_hasDerivAt (0 : ℝ) hinc'
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × E₁) E₃ w).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) h1
  have h3 : iteratedFDeriv ℝ (n + 1) ψ 0 (Fin.cons ((1 : ℝ), (0 : E₁)) fun l => ((0 : ℝ), v l)) =
      fderiv ℝ (iteratedFDeriv ℝ n ψ) 0 ((1 : ℝ), (0 : E₁)) w := by
    rw [iteratedFDeriv_succ_apply_left]
    simp [w, Fin.tail_cons]
  rw [h3]
  exact h2.congr_of_eventuallyEq e
section BondMotion
variable {ι P Q E : Type} [Fintype ι] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E]
def bondMotion (Θ : Q → imaginaryQuaternions) (ℓ : ι → P →L[ℝ] Q) (z : P) : ι → imaginaryQuaternions :=
  fun b => Θ (ℓ b z)
theorem contDiffAt_bondMotion (Θ : Q → imaginaryQuaternions) (ℓ : ι → P →L[ℝ] Q) (hΘ : ContDiffAt ℝ 3 Θ 0) :
    ContDiffAt ℝ 3 (bondMotion Θ ℓ) 0 := by
  refine contDiffAt_pi.mpr fun b => ?_
  have h0 : ContDiffAt ℝ 3 Θ (ℓ b 0) := by rw [map_zero]; exact hΘ
  exact ContDiffAt.comp (0 : P) h0 (ℓ b).contDiff.contDiffAt
theorem iteratedFDeriv_bondMotion_apply (Θ : Q → imaginaryQuaternions) (ℓ : ι → P →L[ℝ] Q)
    (hΘ : ContDiffAt ℝ 3 Θ 0) (n : ℕ) (hn : n ≤ 3) (w : Fin n → P) (b : ι) :
    iteratedFDeriv ℝ n (bondMotion Θ ℓ) 0 w b = iteratedFDeriv ℝ n Θ 0 (fun l => ℓ b (w l)) := by
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => imaginaryQuaternions) b).iteratedFDeriv_comp_left
    (contDiffAt_bondMotion Θ ℓ hΘ) (i := n) (by exact_mod_cast hn)
  have h2 : (⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => imaginaryQuaternions) b) ∘ bondMotion Θ ℓ) =
      Θ ∘ (ℓ b) := rfl
  rw [h2] at h1
  have h3 := iteratedFDeriv_comp_clm_zero Θ (ℓ b) n (hΘ.of_le (by exact_mod_cast hn)) w
  rw [h1] at h3
  exact h3
theorem norm_iteratedFDeriv_bondMotion_le (Θ : Q → imaginaryQuaternions) (ℓ : ι → P →L[ℝ] Q) (C : ℝ)
    (hΘ : ContDiffAt ℝ 3 Θ 0) (hC : ∀ j : ℕ, j ≤ 3 → ‖iteratedFDeriv ℝ j Θ 0‖ ≤ C) (n : ℕ) (hn : n ≤ 3)
    (w : Fin n → P) (b : ι) :
    ‖iteratedFDeriv ℝ n (bondMotion Θ ℓ) 0 w b‖ ≤ C * ∏ l, ‖ℓ b (w l)‖ := by
  rw [iteratedFDeriv_bondMotion_apply Θ ℓ hΘ n hn]
  exact ((iteratedFDeriv ℝ n Θ 0).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hC n hn) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
def sumNorm (Z : ι → imaginaryQuaternions) : ℝ := ∑ b, ‖Z b‖
theorem sumNorm_nonneg (Z : ι → imaginaryQuaternions) : 0 ≤ sumNorm Z :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _
theorem iteratedFDeriv_comp_bondMotion_bounds (h3d : ThirdOrderChainRuleVectorValued)
    (J : (ι → imaginaryQuaternions) → E) (Θ : Q → imaginaryQuaternions) (ℓ : ι → P →L[ℝ] Q) (C S : ℝ)
    (M : ℕ → ℝ) (hJ : ContDiffAt ℝ 3 J 0) (hΘ : ContDiffAt ℝ 3 Θ 0) (hΘ0 : Θ 0 = 0)
    (hC : ∀ j : ℕ, j ≤ 3 → ‖iteratedFDeriv ℝ j Θ 0‖ ≤ C) (hC1 : 1 ≤ C) (hM : ∀ l, 0 ≤ M l)
    (hJb : ∀ (n : ℕ) (Z : Fin n → ι → imaginaryQuaternions), 1 ≤ n → n ≤ 3 →
      ‖iteratedFDeriv ℝ n J 0 Z‖ ≤ M n * ∏ l, sumNorm (Z l))
    (u : P) (hu : ∑ b, ‖ℓ b u‖ ≤ S) :
    (‖iteratedFDeriv ℝ 1 (J ∘ bondMotion Θ ℓ) 0 ![u]‖ ≤ M 1 * C * S) ∧
    (∀ v : P, (∀ b, ‖ℓ b v‖ ≤ 1) → ∑ b, ‖ℓ b v‖ ≤ 1 →
      ‖iteratedFDeriv ℝ 2 (J ∘ bondMotion Θ ℓ) 0 ![u, v]‖ ≤ (M 2 * C ^ 2 + M 1 * C) * S) ∧
    (∀ v w : P, (∀ b, ‖ℓ b v‖ ≤ 1) → (∀ b, ‖ℓ b w‖ ≤ 1) → ∑ b, ‖ℓ b v‖ ≤ 1 → ∑ b, ‖ℓ b w‖ ≤ 1 →
      ‖iteratedFDeriv ℝ 3 (J ∘ bondMotion Θ ℓ) 0 ![u, v, w]‖ ≤
        (M 3 * C ^ 3 + 3 * (M 2 * C ^ 2) + M 1 * C) * S) := by
  have hC0 : 0 ≤ C := by linarith
  have hS : 0 ≤ S := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans hu
  have hα0 : bondMotion Θ ℓ 0 = 0 := by
    funext b
    simp [bondMotion, hΘ0]
  have hmc := contDiffAt_bondMotion Θ ℓ hΘ
  obtain ⟨_, d1, d2, d3⟩ := h3d J (bondMotion Θ ℓ) 0 (by rw [hα0]; exact hJ) hmc
  rw [hα0] at d1 d2 d3
  have n1 : ∀ x : P, sumNorm (iteratedFDeriv ℝ 1 (bondMotion Θ ℓ) 0 ![x]) ≤ C * ∑ b, ‖ℓ b x‖ := by
    intro x
    unfold sumNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have := norm_iteratedFDeriv_bondMotion_le Θ ℓ C hΘ hC 1 (by norm_num) ![x] b
    simpa using this
  have n2 : ∀ x y : P, (∀ b, ‖ℓ b y‖ ≤ 1) →
      sumNorm (iteratedFDeriv ℝ 2 (bondMotion Θ ℓ) 0 ![x, y]) ≤ C * ∑ b, ‖ℓ b x‖ := by
    intro x y hy
    unfold sumNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have h := norm_iteratedFDeriv_bondMotion_le Θ ℓ C hΘ hC 2 (by norm_num) ![x, y] b
    rw [Fin.prod_univ_two] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    calc _ ≤ ‖ℓ b x‖ * 1 := mul_le_mul_of_nonneg_left (hy b) (norm_nonneg _)
      _ = _ := mul_one _
  have n3 : ∀ x y z : P, (∀ b, ‖ℓ b y‖ ≤ 1) → (∀ b, ‖ℓ b z‖ ≤ 1) →
      sumNorm (iteratedFDeriv ℝ 3 (bondMotion Θ ℓ) 0 ![x, y, z]) ≤ C * ∑ b, ‖ℓ b x‖ := by
    intro x y z hy hz
    unfold sumNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have h := norm_iteratedFDeriv_bondMotion_le Θ ℓ C hΘ hC 3 (by norm_num) ![x, y, z] b
    rw [Fin.prod_univ_three] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    have h1 := hy b
    have h2 := hz b
    have h3 := norm_nonneg (ℓ b x)
    have h4 := norm_nonneg (ℓ b y)
    have h5 := norm_nonneg (ℓ b z)
    calc _ ≤ ‖ℓ b x‖ * 1 * 1 := by gcongr
      _ = _ := by ring
  have nu := (n1 u).trans (mul_le_mul_of_nonneg_left hu hC0)
  have j1 : ∀ Z : ι → imaginaryQuaternions, ‖iteratedFDeriv ℝ 1 J 0 ![Z]‖ ≤ M 1 * sumNorm Z := fun Z => by
    have := hJb 1 ![Z] le_rfl (by norm_num)
    simpa using this
  have j2 : ∀ Z Z' : ι → imaginaryQuaternions,
      ‖iteratedFDeriv ℝ 2 J 0 ![Z, Z']‖ ≤ M 2 * (sumNorm Z * sumNorm Z') := fun Z Z' => by
    have := hJb 2 ![Z, Z'] (by norm_num) (by norm_num)
    rw [Fin.prod_univ_two] at this
    simpa using this
  have j3 : ∀ Z Z' Z'' : ι → imaginaryQuaternions, ‖iteratedFDeriv ℝ 3 J 0 ![Z, Z', Z'']‖ ≤
      M 3 * (sumNorm Z * sumNorm Z' * sumNorm Z'') := fun Z Z' Z'' => by
    have := hJb 3 ![Z, Z', Z''] (by norm_num) le_rfl
    rw [Fin.prod_univ_three] at this
    simpa using this
  have lz := fun Z : ι → imaginaryQuaternions => sumNorm_nonneg Z
  refine ⟨?_, ?_, ?_⟩
  · rw [d1 u]
    calc _ ≤ M 1 * sumNorm (iteratedFDeriv ℝ 1 (bondMotion Θ ℓ) 0 ![u]) := j1 _
      _ ≤ M 1 * (C * S) := mul_le_mul_of_nonneg_left nu (hM 1)
      _ = _ := by ring
  · intro v hv hv1
    have nv := (n1 v).trans (mul_le_mul_of_nonneg_left hv1 hC0)
    rw [d2 u v]
    refine (norm_add_le _ _).trans ?_
    have t1 := (j2 (iteratedFDeriv ℝ 1 (bondMotion Θ ℓ) 0 ![u]) (iteratedFDeriv ℝ 1 (bondMotion Θ ℓ) 0 ![v])).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul nu nv (lz _) (by positivity)) (hM 2))
    have t2 := (j1 (iteratedFDeriv ℝ 2 (bondMotion Θ ℓ) 0 ![u, v])).trans
      (mul_le_mul_of_nonneg_left ((n2 u v hv).trans (mul_le_mul_of_nonneg_left hu hC0)) (hM 1))
    nlinarith [t1, t2]
  · intro v w hv hw hv1 hw1
    have nv := (n1 v).trans (mul_le_mul_of_nonneg_left hv1 hC0)
    have nw := (n1 w).trans (mul_le_mul_of_nonneg_left hw1 hC0)
    have nuv := (n2 u v hv).trans (mul_le_mul_of_nonneg_left hu hC0)
    have nuw := (n2 u w hw).trans (mul_le_mul_of_nonneg_left hu hC0)
    have nvw := (n2 v w hw).trans (mul_le_mul_of_nonneg_left hv1 hC0)
    have nuvw := (n3 u v w hv hw).trans (mul_le_mul_of_nonneg_left hu hC0)
    rw [d3 u v w]
    have t1 := (j3 (iteratedFDeriv ℝ 1 (bondMotion Θ ℓ) 0 ![u]) (iteratedFDeriv ℝ 1 (bondMotion Θ ℓ) 0 ![v])
      (iteratedFDeriv ℝ 1 (bondMotion Θ ℓ) 0 ![w])).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul (mul_le_mul nu nv (lz _) (by positivity)) nw (lz _) (by positivity)) (hM 3))
    have t2 := (j2 (iteratedFDeriv ℝ 2 (bondMotion Θ ℓ) 0 ![u, v]) (iteratedFDeriv ℝ 1 (bondMotion Θ ℓ) 0 ![w])).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul nuv nw (lz _) (by positivity)) (hM 2))
    have t3 := (j2 (iteratedFDeriv ℝ 2 (bondMotion Θ ℓ) 0 ![u, w]) (iteratedFDeriv ℝ 1 (bondMotion Θ ℓ) 0 ![v])).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul nuw nv (lz _) (by positivity)) (hM 2))
    have t4 := (j2 (iteratedFDeriv ℝ 2 (bondMotion Θ ℓ) 0 ![v, w]) (iteratedFDeriv ℝ 1 (bondMotion Θ ℓ) 0 ![u])).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul nvw nu (lz _) (by positivity)) (hM 2))
    have t5 := (j1 (iteratedFDeriv ℝ 3 (bondMotion Θ ℓ) 0 ![u, v, w])).trans
      (mul_le_mul_of_nonneg_left nuvw (hM 1))
    refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)) t4)) t5)).trans (le_of_eq ?_)
    ring
end BondMotion
end VectorSpaces
theorem expUnit_zero : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
variable {F : BlockFrame}
theorem expUnit_add_smul (a b : ℝ) (w : imaginaryQuaternions) :
    expUnit ((a + b) • w) = expUnit (a • w) * expUnit (b • w) := by
  apply Subtype.ext
  show NormedSpace.exp ((((a + b) • w : imaginaryQuaternions)) : Quaternion ℝ) =
    NormedSpace.exp (((a • w : imaginaryQuaternions)) : Quaternion ℝ) *
      NormedSpace.exp (((b • w : imaginaryQuaternions)) : Quaternion ℝ)
  have e : ((((a + b) • w : imaginaryQuaternions)) : Quaternion ℝ) =
      ((a • w : imaginaryQuaternions) : Quaternion ℝ) + ((b • w : imaginaryQuaternions) : Quaternion ℝ) := by
    simp [add_smul]
  rw [e]
  have hc : Commute ((a • w : imaginaryQuaternions) : Quaternion ℝ) ((b • w : imaginaryQuaternions) : Quaternion ℝ) := by
    simp only [Submodule.coe_smul]
    exact (Commute.refl _).smul_left _ |>.smul_right _
  exact NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hc
    ((NormedSpace.expSeries_radius_eq_top ℝ (Quaternion ℝ)).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℝ (Quaternion ℝ)).symm ▸ edist_lt_top _ _)
theorem expFlow_add {j : ℕ} (B : F.Site j → Fin 4 → imaginaryQuaternions) (W : F.GaugeField j) (u h : ℝ) :
    expFlow B W (u + h) = leftTranslate (fun y i => h • B y i) (expFlow B W u) := by
  funext y i
  simp only [expFlow, leftTranslate]
  rw [add_comm u h, expUnit_add_smul, mul_assoc]
theorem expFlow_zero {j : ℕ} (B : F.Site j → Fin 4 → imaginaryQuaternions) (W : F.GaugeField j) :
    expFlow B W 0 = W := by
  funext y i
  simp [expFlow, leftTranslate, expUnit_zero]
theorem singleBondForm_apply {j : ℕ} {B : Finset (F.Site j × Fin 4)} (b b' : ↥B) (X : imaginaryQuaternions) :
    singleBondForm b X b' = if b' = b then X else 0 := by
  classical
  unfold singleBondForm
  by_cases h : b' = b
  · subst h; simp
  · simp [h]
def coeffForm {j k : ℕ} {T : Finset (F.Site j × Fin 4)} (c : Fin k → ↥T) (X : Fin k → imaginaryQuaternions) :
    (Fin k → ℝ) →L[ℝ] (↥T → imaginaryQuaternions) :=
  ∑ l, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l).smulRight (singleBondForm (c l) (X l))
theorem coeffForm_apply {j k : ℕ} {T : Finset (F.Site j × Fin 4)} (c : Fin k → ↥T)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) (b : ↥T) :
    coeffForm c X τ b = ∑ l, τ l • (if b = c l then X l else 0) := by
  simp [coeffForm, Finset.sum_apply, singleBondForm_apply]
theorem coeffForm_eq_bondSpread {j k : ℕ} {T : Finset (F.Site j × Fin 4)} (c : Fin k → ↥T)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) (b : ↥T) :
    coeffForm c X τ b = bondSpread (fun l => (c l).1) X τ b.1.1 b.1.2 := by
  classical
  rw [coeffForm_apply]
  unfold bondSpread
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases e : b = c l
  · subst e; simp
  · have e' : ¬ (c l).1 = (b.1.1, b.1.2) := fun q => e (Subtype.ext q.symm)
    simp [e, e']
def bondLinearMap {j k : ℕ} {T : Finset (F.Site j × Fin 4)} (c : Fin k → ↥T) (X : Fin k → imaginaryQuaternions)
    (Bh : ↥T → imaginaryQuaternions) (b : ↥T) :
    (ℝ × (Fin k → ℝ)) →L[ℝ] (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) :=
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥T => imaginaryQuaternions) b).comp (coeffForm c X)).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin k → ℝ))).prod
    (((ContinuousLinearMap.fst ℝ ℝ (Fin k → ℝ)).smulRight (Bh b)).prod 0)
theorem cubic_constant_bounds {m1 m2 m3 C : ℝ} (h1 : 0 ≤ m1) (h2 : 0 ≤ m2) (h3 : 0 ≤ m3) (hC : 1 ≤ C) :
    (m1 * C ≤ 3 * C ^ 3 * (m1 + m2 + m3)) ∧ (m2 * C ^ 2 + m1 * C ≤ 3 * C ^ 3 * (m1 + m2 + m3)) ∧
      (m3 * C ^ 3 + 3 * (m2 * C ^ 2) + m1 * C ≤ 3 * C ^ 3 * (m1 + m2 + m3)) := by
  have a : C ≤ C ^ 3 := by nlinarith [mul_self_nonneg (C - 1), sq_nonneg C]
  have b : C ^ 2 ≤ C ^ 3 := by nlinarith [sq_nonneg C]
  have c : 0 ≤ C ^ 3 := by positivity
  have e1 := mul_le_mul_of_nonneg_left a h1
  have e2 := mul_le_mul_of_nonneg_left b h2
  have p1 := mul_nonneg h1 c
  have p2 := mul_nonneg h2 c
  have p3 := mul_nonneg h3 c
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
end FlowDerivative
open FlowDerivative
theorem derivBoundAlongFlow_holds (hlog : ConjugatedExpLogSmooth)
    (h3d : ThirdOrderChainRuleVectorValued) (hjet : FormCompositionJet) :
    DerivBoundAlongFlow := by
  obtain ⟨Θ, U, CΘ, hU, hCΘ, hdiag, hΘc, hexp, hΘ0, hb, -, -⟩ := hlog
  have hC1 : 1 ≤ 1 + CΘ := by linarith
  refine ⟨3 * (1 + CΘ) ^ 3, by positivity, ?_⟩
  intro E _ _ F j T G W B M hT hM hsm hbd k c X hk hX
  set C := 1 + CΘ with hCdef
  let Bh : ↥T → imaginaryQuaternions := fun b => B b.1.1 b.1.2
  let c' : Fin k → ↥T := fun l => ⟨c l, hT _⟩
  set S := ∑ b ∈ T, ‖B b.1 b.2‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hz0 : (0 : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) ∈ U := hdiag 0
  have hΘ0' : Θ 0 = 0 := hΘ0 0
  have hΘa : ContDiffAt ℝ 3 Θ 0 := hΘc.contDiffAt (hU.mem_nhds hz0)
  have hCb : ∀ j : ℕ, j ≤ 3 → ‖iteratedFDeriv ℝ j Θ 0‖ ≤ C := fun j hj =>
    (hb 0 j (by simp) hj).trans (by simp only [hCdef]; linarith)
  let φ : ℝ → E := fun u => bondDeriv G (expFlow B W u) c X
  have key : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∃ d, HasDerivAt φ d u ∧
      ‖d‖ ≤ 3 * C ^ 3 * (M 1 + M 2 + M 3) * S := by
    intro u h0 h1
    have hsm' := hsm u h0 h1
    obtain ⟨hJc, -, hJb0⟩ := hjet E F j T G (expFlow B W u) hsm'
    let ℓ := bondLinearMap c' X Bh
    let ψ : ℝ × (Fin k → ℝ) → E := formComposition T G (expFlow B W u) ∘ bondMotion Θ ℓ
    have hα0 : bondMotion Θ ℓ 0 = 0 := by
      funext b
      simp [bondMotion, hΘ0']
    have hψ : ContDiffAt ℝ 3 ψ 0 :=
      (h3d (formComposition T G (expFlow B W u)) (bondMotion Θ ℓ) 0 (by rw [hα0]; exact hJc)
        (contDiffAt_bondMotion Θ ℓ hΘa)).1
    have hevU : ∀ᶠ z in 𝓝 (0 : ℝ × (Fin k → ℝ)), ∀ b, ℓ b z ∈ U :=
      Filter.eventually_all.mpr fun b => ((ℓ b).continuous.tendsto 0).eventually
        (by rw [map_zero]; exact hU.mem_nhds hz0)
    have hid : ∀ᶠ z in 𝓝 (0 : ℝ × (Fin k → ℝ)), ψ z =
        G (leftTranslate (bondSpread c X z.2) (leftTranslate (fun y i => z.1 • B y i) (expFlow B W u))) := by
      refine hevU.mono fun z hz => ?_
      show G (leftTranslate (extendByZero (bondMotion Θ ℓ z)) (expFlow B W u)) = _
      congr 1
      funext y i
      have hy : (y, i) ∈ T := hT _
      simp only [leftTranslate, extendByZero, dif_pos hy]
      have h3 := hexp _ (hz ⟨(y, i), hy⟩)
      simp only [bondMotion]
      rw [h3]
      have h4 : ℓ ⟨(y, i), hy⟩ z = (bondSpread c X z.2 y i, z.1 • B y i, 0) := by
        rw [show ℓ ⟨(y, i), hy⟩ z = (coeffForm c' X z.2 ⟨(y, i), hy⟩, z.1 • Bh ⟨(y, i), hy⟩, 0) from rfl,
          coeffForm_eq_bondSpread]
      rw [h4]
      simp [expUnit_zero, mul_assoc]
    have hid' : ∀ᶠ z in 𝓝 (((0 : ℝ), (0 : Fin k → ℝ))), ψ z =
        G (leftTranslate (bondSpread c X z.2) (leftTranslate (fun y i => z.1 • B y i) (expFlow B W u))) := hid
    have hcur := hid'.curry_nhds
    have hφ : (fun h => φ (u + h)) =ᶠ[𝓝 0]
        fun h => iteratedFDeriv ℝ k (fun τ => ψ (h, τ)) 0 (fun l => Pi.single l 1) :=
      hcur.mono fun h hh => by
        show bondDeriv G (expFlow B W (u + h)) c X = _
        rw [expFlow_add]
        unfold bondDeriv
        have e : (fun τ => ψ (h, τ)) =ᶠ[𝓝 0]
            fun τ => G (leftTranslate (bondSpread c X τ) (leftTranslate (fun y i => h • B y i) (expFlow B W u))) := hh
        have e2 := (Filter.EventuallyEq.iteratedFDeriv ℝ e k).self_of_nhds
        show _ = (iteratedFDeriv ℝ k (fun τ => ψ (h, τ)) 0) (fun l => Pi.single l 1)
        rw [e2]
    have hk3 : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ 3 := by
      have : k + 1 ≤ 3 := by omega
      exact_mod_cast this
    have hd := hasDerivAt_iteratedFDeriv_slice ψ k (fun l => Pi.single l 1) (hψ.of_le hk3)
    refine ⟨iteratedFDeriv ℝ (k + 1) ψ 0 (Fin.cons ((1 : ℝ), (0 : Fin k → ℝ))
      fun l => ((0 : ℝ), (Pi.single l 1 : Fin k → ℝ))), ?_, ?_⟩
    · have g := hd.congr_of_eventuallyEq hφ
      have g2 : HasDerivAt (fun h => φ (u + (h - u))) _ u :=
        HasDerivAt.comp_sub_const (f := fun h => φ (u + h)) u u (by simpa using g)
      simpa using g2
    · have hJb : ∀ (n : ℕ) (Z : Fin n → ↥T → imaginaryQuaternions), 1 ≤ n → n ≤ 3 →
          ‖iteratedFDeriv ℝ n (formComposition T G (expFlow B W u)) 0 Z‖ ≤ M n * ∏ l, sumNorm (Z l) := by
        intro n Z hn1 hn3
        have := hJb0 n (fun _ => M n) hn3 (fun _ => hM n)
          (fun c X hX => hbd u h0 h1 n _ X hn1 hn3 hX) Z
        refine this.trans (le_of_eq ?_)
        rw [← Finset.mul_sum]
        congr 1
        unfold sumNorm
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      have hu : ∑ b, ‖ℓ b ((1 : ℝ), (0 : Fin k → ℝ))‖ ≤ S := by
        have e : ∀ b : ↥T, ‖ℓ b ((1 : ℝ), (0 : Fin k → ℝ))‖ = ‖B b.1.1 b.1.2‖ := fun b => by
          show ‖(coeffForm c' X 0 b, (1 : ℝ) • Bh b, (0 : imaginaryQuaternions))‖ = _
          simp [Prod.norm_def, Bh]
        simp only [e]
        exact le_of_eq (Finset.sum_coe_sort T (fun b => ‖B b.1 b.2‖))
      have hv : ∀ (l : Fin k) (b : ↥T), ‖ℓ b ((0 : ℝ), (Pi.single l 1 : Fin k → ℝ))‖ =
          if b = c' l then 1 else 0 := by
        intro l b
        show ‖(coeffForm c' X (Pi.single l 1) b, (0 : ℝ) • Bh b, (0 : imaginaryQuaternions))‖ = _
        rw [coeffForm_apply, Finset.sum_eq_single l]
        · by_cases e : b = c' l
          · simp [e, Prod.norm_def, hX l]
          · simp [e, Prod.norm_def]
        · intro l' _ h'
          simp [Pi.single_eq_of_ne h']
        · simp
      have hv1 : ∀ (l : Fin k) (b : ↥T), ‖ℓ b ((0 : ℝ), (Pi.single l 1 : Fin k → ℝ))‖ ≤ 1 := fun l b => by
        rw [hv]; split_ifs <;> norm_num
      have hv2 : ∀ l : Fin k, ∑ b, ‖ℓ b ((0 : ℝ), (Pi.single l 1 : Fin k → ℝ))‖ ≤ 1 := fun l => by
        simp only [hv]
        simp
      have hC1' : 1 ≤ C := hC1
      obtain ⟨m1, m2, m3⟩ := iteratedFDeriv_comp_bondMotion_bounds h3d (formComposition T G (expFlow B W u))
        Θ ℓ C S M hJc hΘa hΘ0' hCb hC1' hM hJb _ hu
      obtain ⟨k1, k2, k3⟩ := cubic_constant_bounds (hM 1) (hM 2) (hM 3) hC1'
      obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      · have e : (Fin.cons ((1 : ℝ), (0 : Fin 0 → ℝ)) fun l => ((0 : ℝ), (Pi.single l 1 : Fin 0 → ℝ)) :
            Fin 1 → ℝ × (Fin 0 → ℝ)) = ![((1 : ℝ), (0 : Fin 0 → ℝ))] := by
          funext i; fin_cases i; rfl
        rw [e]
        exact m1.trans (mul_le_mul_of_nonneg_right k1 hS0)
      · have e : (Fin.cons ((1 : ℝ), (0 : Fin 1 → ℝ)) fun l => ((0 : ℝ), (Pi.single l 1 : Fin 1 → ℝ)) :
            Fin 2 → ℝ × (Fin 1 → ℝ)) =
            ![((1 : ℝ), (0 : Fin 1 → ℝ)), ((0 : ℝ), (Pi.single 0 1 : Fin 1 → ℝ))] := by
          funext i; fin_cases i <;> rfl
        rw [e]
        exact (m2 _ (hv1 0) (hv2 0)).trans (mul_le_mul_of_nonneg_right k2 hS0)
      · have e : (Fin.cons ((1 : ℝ), (0 : Fin 2 → ℝ)) fun l => ((0 : ℝ), (Pi.single l 1 : Fin 2 → ℝ)) :
            Fin 3 → ℝ × (Fin 2 → ℝ)) =
            ![((1 : ℝ), (0 : Fin 2 → ℝ)), ((0 : ℝ), (Pi.single 0 1 : Fin 2 → ℝ)),
              ((0 : ℝ), (Pi.single 1 1 : Fin 2 → ℝ))] := by
          funext i; fin_cases i <;> rfl
        rw [e]
        exact (m3 _ _ (hv1 0) (hv1 1) (hv2 0) (hv2 1)).trans (mul_le_mul_of_nonneg_right k3 hS0)
  have hd : ∀ u ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ (deriv φ u) (Set.Icc 0 1) u := fun u hu => by
    obtain ⟨d, h, _⟩ := key u hu.1 hu.2
    exact h.differentiableAt.hasDerivAt.hasDerivWithinAt
  have hbd' : ∀ u ∈ Set.Ico (0 : ℝ) 1, ‖deriv φ u‖ ≤ 3 * C ^ 3 * (M 1 + M 2 + M 3) * S := fun u hu => by
    obtain ⟨d, h, hd⟩ := key u hu.1 hu.2.le
    rw [h.deriv]
    exact hd
  have hfin := norm_image_sub_le_of_norm_deriv_le_segment_01' hd hbd'
  have e0 : φ 0 = bondDeriv G W c X := by
    show bondDeriv G (expFlow B W 0) c X = _
    rw [expFlow_zero]
  rw [e0] at hfin
  exact hfin
end ColdStepAtMirrorFrames
end YangMills.Construction
end
