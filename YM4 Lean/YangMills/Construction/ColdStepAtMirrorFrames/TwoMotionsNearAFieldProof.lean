import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderNearOneProof
import YangMills.Construction.ColdStepAtMirrorFrames.ThreeDerivativesInASpace
import YangMills.Construction.ColdStepAtMirrorFrames.TwoMotionsNearAField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages Estimates
namespace ColdStepAtMirrorFrames
namespace SecondDerivAlongMotions
variable {F : BlockFrame}
theorem norm_apply_le_of_single_bound {ι E : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (m : ContinuousMultilinearMap ℝ (fun _ : Fin k => ι → imaginaryQuaternions) E) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (c : Fin k → ι) (X : Fin k → imaginaryQuaternions), AreUnitVectors X → ‖m fun l => Pi.single (c l) (X l)‖ ≤ C)
    (Z : Fin k → ι → imaginaryQuaternions) : ‖m Z‖ ≤ C * ∏ l, ∑ b, ‖Z l b‖ := by
  have hZ : Z = fun l => ∑ b, (Pi.single b (Z l b) : ι → imaginaryQuaternions) := by
    funext l
    exact (Finset.univ_sum_single (Z l)).symm
  have h1 : m Z = ∑ r : Fin k → ι, m fun l => Pi.single (r l) (Z l (r l)) := by
    conv_lhs => rw [hZ]
    exact m.map_sum _
  rw [h1, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  by_cases h0 : ∃ l, Z l (r l) = 0
  · obtain ⟨l, hl⟩ := h0
    have : m (fun l => Pi.single (r l) (Z l (r l))) = 0 :=
      m.map_coord_zero l (by simp [hl])
    rw [this, norm_zero]
    exact mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  · push Not at h0
    let X : Fin k → imaginaryQuaternions := fun l => ‖Z l (r l)‖⁻¹ • Z l (r l)
    have hX : AreUnitVectors X := fun l => by
      show ‖‖Z l (r l)‖⁻¹ • Z l (r l)‖ = 1
      rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (h0 l))
    have e1 : (fun l => (Pi.single (r l) (Z l (r l)) : ι → imaginaryQuaternions)) =
        fun l => ‖Z l (r l)‖ • (Pi.single (r l) (X l) : ι → imaginaryQuaternions) := by
      funext l
      rw [← Pi.single_smul]
      congr 1
      show Z l (r l) = ‖Z l (r l)‖ • ‖Z l (r l)‖⁻¹ • Z l (r l)
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (h0 l)), one_smul]
    rw [e1, m.map_smul_univ, norm_smul, Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _),
      mul_comm]
    exact mul_le_mul_of_nonneg_right (h r X hX) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
theorem sub_apply_fin_two_left {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => D) E) (a b c : D) :
    m ![a, c] - m ![b, c] = m ![a - b, c] := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderNearCriticalAux.bilinear_sub_left <;> assumption
theorem sub_apply_fin_two_right {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => D) E) (a b c : D) :
    m ![c, a] - m ![c, b] = m ![c, a - b] := by
  have := m.map_update_sub ![c, b] 1 a b
  have e1 : Function.update ![c, b] 1 (a - b) = ![c, a - b] := by
    funext i; fin_cases i <;> rfl
  have e2 : Function.update ![c, b] 1 a = ![c, a] := by
    funext i; fin_cases i <;> rfl
  have e3 : Function.update ![c, b] 1 b = ![c, b] := by
    funext i; fin_cases i <;> rfl
  rw [e1, e2, e3] at this
  exact this.symm
def restrictMotion {j p : ℕ} (T : Finset (F.Site j × Fin 4)) (α : (Fin p → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions) :
    (Fin p → ℝ) → ↥T → imaginaryQuaternions := fun τ b => α τ b.1.1 b.1.2
theorem comp_leftTranslate_eq {j p : ℕ} {T : Finset (F.Site j × Fin 4)} (hT : ∀ b, b ∈ T) (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (α : (Fin p → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions) :
    (fun τ => G (leftTranslate (α τ) W)) = formComposition T G W ∘ restrictMotion T α := by
  funext τ
  show _ = G (leftTranslate (extendByZero (restrictMotion T α τ)) W)
  congr 1
  funext y i
  have hy : (y, i) ∈ T := hT _
  simp only [leftTranslate, extendByZero, dif_pos hy, restrictMotion]
theorem restrictMotion_contDiffAt {j p : ℕ} (T : Finset (F.Site j × Fin 4)) (α : (Fin p → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions)
    (h : ∀ x b, ContDiffAt ℝ 3 (fun τ => α τ x b) 0) : ContDiffAt ℝ 3 (restrictMotion T α) 0 :=
  contDiffAt_pi.mpr fun b => h b.1.1 b.1.2
theorem iteratedFDeriv_restrictMotion_apply {j p r : ℕ} (T : Finset (F.Site j × Fin 4)) (α : (Fin p → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions)
    (h : ∀ x b, ContDiffAt ℝ 3 (fun τ => α τ x b) 0) (hr : r ≤ 3) (e : Fin r → Fin p) (b : ↥T) :
    iteratedFDeriv ℝ r (restrictMotion T α) 0 (fun l => Pi.single (e l) 1) b = motionComponent α e b.1.1 b.1.2 := by
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥T => imaginaryQuaternions) b).iteratedFDeriv_comp_left
    (restrictMotion_contDiffAt T α h) (i := r) (by exact_mod_cast hr)
  have h2 : (⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥T => imaginaryQuaternions) b) ∘ restrictMotion T α) =
      fun τ => α τ b.1.1 b.1.2 := rfl
  rw [h2] at h1
  unfold motionComponent
  rw [h1]
  rfl
theorem sum_norm_iteratedFDeriv_restrictMotion {j p r : ℕ} (T : Finset (F.Site j × Fin 4)) (α : (Fin p → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions)
    (h : ∀ x b, ContDiffAt ℝ 3 (fun τ => α τ x b) 0) (hr : r ≤ 3) (e : Fin r → Fin p) :
    ∑ b : ↥T, ‖iteratedFDeriv ℝ r (restrictMotion T α) 0 (fun l => Pi.single (e l) 1) b‖ =
      ∑ b ∈ T, ‖motionComponent α e b.1 b.2‖ := by
  simp only [iteratedFDeriv_restrictMotion_apply T α h hr e]
  exact Finset.sum_coe_sort T fun b => ‖motionComponent α e b.1 b.2‖
theorem single_comp_fin_one {p : ℕ} (l : Fin p) : (fun m : Fin 1 => (Pi.single (![l] m) 1 : Fin p → ℝ)) = ![Pi.single l 1] := by
  funext m; fin_cases m; rfl
theorem single_comp_fin_two {p : ℕ} (l l' : Fin p) :
    (fun m : Fin 2 => (Pi.single (![l, l'] m) 1 : Fin p → ℝ)) = ![Pi.single l 1, Pi.single l' 1] := by
  funext m; fin_cases m <;> rfl
end SecondDerivAlongMotions
open SecondDerivAlongMotions
theorem secondDerivAlongMotionsClose_proof (hjet : FormCompositionJet)
    (h3d : ThirdOrderChainRuleVectorValued) : SecondDerivAlongMotionsClose := by
  classical
  intro F j T G W W₀ ε E K μ hT hW hW₀ hε hE hK hμ hent hz hE2
  obtain ⟨hJc, hJe, -⟩ := hjet ℝ F j T G W hW
  obtain ⟨hIc, hIe, -⟩ := hjet ℝ F j T G W₀ hW₀
  have hfs : ∀ (b : ↥T) (X : imaginaryQuaternions), (Pi.single b X : ↥T → imaginaryQuaternions) = singleBondForm b X := by
    intro b X
    funext b'
    by_cases e : b' = b
    · subst e; simp [singleBondForm]
    · simp [singleBondForm, e, Pi.single_eq_of_ne e]
  have m1 : ∀ Z : Fin 1 → ↥T → imaginaryQuaternions,
      ‖(iteratedFDeriv ℝ 1 (formComposition T G W) 0 - iteratedFDeriv ℝ 1 (formComposition T G W₀) 0) Z‖ ≤
        ε * ∏ l, ∑ b, ‖Z l b‖ := by
    refine norm_apply_le_of_single_bound _ ε hε fun c X hX => ?_
    simp only [hfs, sub_apply]
    rw [hJe 1 c X (by norm_num), hIe 1 c X (by norm_num)]
    exact hent 1 _ X le_rfl (by norm_num) hX
  have m2 : ∀ Z : Fin 2 → ↥T → imaginaryQuaternions,
      ‖(iteratedFDeriv ℝ 2 (formComposition T G W) 0 - iteratedFDeriv ℝ 2 (formComposition T G W₀) 0) Z‖ ≤
        ε * ∏ l, ∑ b, ‖Z l b‖ := by
    refine norm_apply_le_of_single_bound _ ε hε fun c X hX => ?_
    simp only [hfs, sub_apply]
    rw [hJe 2 c X (by norm_num), hIe 2 c X (by norm_num)]
    exact hent 2 _ X (by norm_num) le_rfl hX
  have n1 : ∀ Z : Fin 1 → ↥T → imaginaryQuaternions, iteratedFDeriv ℝ 1 (formComposition T G W₀) 0 Z = 0 := by
    intro Z
    have := norm_apply_le_of_single_bound (iteratedFDeriv ℝ 1 (formComposition T G W₀) 0) 0 le_rfl (fun c X hX => by
      simp only [hfs]
      rw [hIe 1 c X (by norm_num), hz _ X hX]
      simp) Z
    simpa using this
  have n2 : ∀ Z : Fin 2 → ↥T → imaginaryQuaternions, ‖iteratedFDeriv ℝ 2 (formComposition T G W₀) 0 Z‖ ≤ E * ∏ l, ∑ b, ‖Z l b‖ := by
    refine norm_apply_le_of_single_bound _ E hE fun c X hX => ?_
    simp only [hfs]
    rw [hIe 2 c X (by norm_num)]
    exact hE2 _ X hX
  refine ⟨?_, ?_⟩
  · intro α h0 hc hK1
    have hα0 : restrictMotion T α 0 = 0 := by
      funext b
      exact h0 _ _
    have hd := h3d (formComposition T G W) (restrictMotion T α) 0 (by rw [hα0]; exact hJc) (restrictMotion_contDiffAt T α hc)
    rw [comp_leftTranslate_eq hT G W α, hd.2.1, hα0]
    set a := iteratedFDeriv ℝ 1 (restrictMotion T α) 0 ![Pi.single 0 1] with ha
    have hl : ∑ b, ‖a b‖ ≤ K := by
      have := sum_norm_iteratedFDeriv_restrictMotion T α hc (by norm_num) ![0]
      rw [single_comp_fin_one] at this
      rw [ha, this]
      exact hK1
    have h1 := m1 ![a]
    simp only [sub_apply, n1, sub_zero] at h1
    rw [Real.norm_eq_abs] at h1
    simp only [Finset.univ_unique, Finset.prod_singleton] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hε)
    simpa using hl
  · intro α α₀ h0 h00 hc hc0 hKa hKb hK01 hμ'
    have hα0 : restrictMotion T α 0 = 0 := by
      funext b
      exact h0 _ _
    have hβ0 : restrictMotion T α₀ 0 = 0 := by
      funext b
      exact h00 _ _
    have hd := h3d (formComposition T G W) (restrictMotion T α) 0 (by rw [hα0]; exact hJc) (restrictMotion_contDiffAt T α hc)
    have hd0 := h3d (formComposition T G W₀) (restrictMotion T α₀) 0 (by rw [hβ0]; exact hIc) (restrictMotion_contDiffAt T α₀ hc0)
    rw [comp_leftTranslate_eq hT G W α, comp_leftTranslate_eq hT G W₀ α₀, hd.2.2.1, hd0.2.2.1, hα0, hβ0, n1, add_zero]
    set a0 := iteratedFDeriv ℝ 1 (restrictMotion T α) 0 ![Pi.single 0 1] with ha0
    set a1 := iteratedFDeriv ℝ 1 (restrictMotion T α) 0 ![Pi.single 1 1] with ha1
    set a01 := iteratedFDeriv ℝ 2 (restrictMotion T α) 0 ![Pi.single 0 1, Pi.single 1 1] with ha01
    set b0 := iteratedFDeriv ℝ 1 (restrictMotion T α₀) 0 ![Pi.single 0 1] with hb0
    set b1 := iteratedFDeriv ℝ 1 (restrictMotion T α₀) 0 ![Pi.single 1 1] with hb1
    have la : ∀ l : Fin 2, ∑ b, ‖iteratedFDeriv ℝ 1 (restrictMotion T α) 0 ![Pi.single l 1] b‖ ≤ K := fun l => by
      have := sum_norm_iteratedFDeriv_restrictMotion T α hc (by norm_num) ![l]
      rw [single_comp_fin_one] at this
      rw [this]
      exact hKa l
    have lb : ∀ l : Fin 2, ∑ b, ‖iteratedFDeriv ℝ 1 (restrictMotion T α₀) 0 ![Pi.single l 1] b‖ ≤ K := fun l => by
      have := sum_norm_iteratedFDeriv_restrictMotion T α₀ hc0 (by norm_num) ![l]
      rw [single_comp_fin_one] at this
      rw [this]
      exact hKb l
    have l01 : ∑ b, ‖a01 b‖ ≤ K := by
      have := sum_norm_iteratedFDeriv_restrictMotion T α hc (by norm_num) ![0, 1]
      rw [single_comp_fin_two] at this
      rw [ha01, this]
      exact hK01
    have ld : ∀ l : Fin 2, ∑ b, ‖(iteratedFDeriv ℝ 1 (restrictMotion T α) 0 ![Pi.single l 1] -
        iteratedFDeriv ℝ 1 (restrictMotion T α₀) 0 ![Pi.single l 1]) b‖ ≤ μ := fun l => by
      have e1 := iteratedFDeriv_restrictMotion_apply T α hc (by norm_num) ![l]
      have e2 := iteratedFDeriv_restrictMotion_apply T α₀ hc0 (by norm_num) ![l]
      rw [single_comp_fin_one] at e1 e2
      simp only [Pi.sub_apply, e1, e2]
      have := Finset.sum_coe_sort T fun b => ‖motionComponent α ![l] b.1 b.2 - motionComponent α₀ ![l] b.1 b.2‖
      rw [this]
      exact hμ' l
    have s0 : 0 ≤ ∑ b, ‖a0 b‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have s1 : 0 ≤ ∑ b, ‖a1 b‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have s2 : 0 ≤ ∑ b, ‖b0 b‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have s3 : 0 ≤ ∑ b, ‖(a0 - b0) b‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have s4 : 0 ≤ ∑ b, ‖(a1 - b1) b‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have t1 := m2 ![a0, a1]
    have t2 := n2 ![a0 - b0, a1]
    have t3 := n2 ![b0, a1 - b1]
    have t4 := m1 ![a01]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Finset.univ_unique,
      Finset.prod_singleton, Real.norm_eq_abs] at t1 t2 t3 t4
    have t4' : |(iteratedFDeriv ℝ 1 (formComposition T G W) 0 - iteratedFDeriv ℝ 1 (formComposition T G W₀) 0) ![a01]| ≤ ε * K := by
      refine t4.trans (mul_le_mul_of_nonneg_left ?_ hε)
      simpa using l01
    have t1' : |(iteratedFDeriv ℝ 2 (formComposition T G W) 0 - iteratedFDeriv ℝ 2 (formComposition T G W₀) 0) ![a0, a1]| ≤ ε * K ^ 2 := by
      refine t1.trans (mul_le_mul_of_nonneg_left ?_ hε)
      rw [sq]
      exact mul_le_mul (la 0) (la 1) s1 hK
    have t2' : |iteratedFDeriv ℝ 2 (formComposition T G W₀) 0 ![a0 - b0, a1]| ≤ E * (μ * K) := by
      refine t2.trans (mul_le_mul_of_nonneg_left ?_ hE)
      exact mul_le_mul (ld 0) (la 1) s1 hμ
    have t3' : |iteratedFDeriv ℝ 2 (formComposition T G W₀) 0 ![b0, a1 - b1]| ≤ E * (K * μ) := by
      refine t3.trans (mul_le_mul_of_nonneg_left ?_ hE)
      exact mul_le_mul (lb 0) (ld 1) s4 hK
    have e1 := sub_apply_fin_two_left (iteratedFDeriv ℝ 2 (formComposition T G W₀) 0) a0 b0 a1
    have e2 := sub_apply_fin_two_right (iteratedFDeriv ℝ 2 (formComposition T G W₀) 0) a1 b1 b0
    have h01 : iteratedFDeriv ℝ 1 (formComposition T G W₀) 0 ![a01] = 0 := n1 _
    simp only [sub_apply] at t1' t4'
    rw [h01, sub_zero] at t4'
    have key : iteratedFDeriv ℝ 2 (formComposition T G W) 0 ![a0, a1] + iteratedFDeriv ℝ 1 (formComposition T G W) 0 ![a01] -
        iteratedFDeriv ℝ 2 (formComposition T G W₀) 0 ![b0, b1] =
        (iteratedFDeriv ℝ 2 (formComposition T G W) 0 ![a0, a1] - iteratedFDeriv ℝ 2 (formComposition T G W₀) 0 ![a0, a1]) +
        iteratedFDeriv ℝ 2 (formComposition T G W₀) 0 ![a0 - b0, a1] +
        iteratedFDeriv ℝ 2 (formComposition T G W₀) 0 ![b0, a1 - b1] + iteratedFDeriv ℝ 1 (formComposition T G W) 0 ![a01] := by
      rw [← e1, ← e2]
      ring
    rw [key]
    refine (abs_add_le _ _).trans ?_
    have u1 := abs_add_le ((iteratedFDeriv ℝ 2 (formComposition T G W) 0 ![a0, a1] - iteratedFDeriv ℝ 2 (formComposition T G W₀) 0 ![a0, a1]) +
      iteratedFDeriv ℝ 2 (formComposition T G W₀) 0 ![a0 - b0, a1]) (iteratedFDeriv ℝ 2 (formComposition T G W₀) 0 ![b0, a1 - b1])
    have u2 := abs_add_le (iteratedFDeriv ℝ 2 (formComposition T G W) 0 ![a0, a1] - iteratedFDeriv ℝ 2 (formComposition T G W₀) 0 ![a0, a1])
      (iteratedFDeriv ℝ 2 (formComposition T G W₀) 0 ![a0 - b0, a1])
    have e3 : ε * (K ^ 2 + K) + 2 * E * K * μ = ε * K ^ 2 + E * (μ * K) + E * (K * μ) + ε * K := by ring
    rw [e3]
    linarith
end ColdStepAtMirrorFrames
end YangMills.Construction
end
