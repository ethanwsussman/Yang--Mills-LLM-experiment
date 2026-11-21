import YangMills.Construction.ColdChainAtEveryLevel.ComplexDifferences
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.ComplexPlaquettes
variable {F : BlockAverages.BlockFrame}
def polarDet (a b : ComplexifiedQuaternions.ComplexQuat) : ℂ := (a * Matrix.adjugate b).trace
theorem det_add_eq_add_polarDet (a b : ComplexifiedQuaternions.ComplexQuat) :
    (a + b).det = a.det + b.det + polarDet a b := by
  simp [polarDet, Matrix.det_fin_two, Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring
theorem norm_polarDet_le (a b : ComplexifiedQuaternions.ComplexQuat) : ‖polarDet a b‖ ≤ 2 * (‖a‖ * ‖b‖) := by
  refine (ComplexifiedQuaternions.norm_trace_le _).trans ?_
  have h := norm_mul_le a (Matrix.adjugate b)
  rw [ComplexifiedQuaternions.norm_adjugate] at h
  linarith
theorem polarDet_add_right (a b c : ComplexifiedQuaternions.ComplexQuat) :
    polarDet a (b + c) = polarDet a b + polarDet a c := by
  simp [polarDet, ComplexifiedQuaternions.adjugate_map_add, mul_add, Matrix.trace_add]
theorem norm_half_det_add_sub_le (Y A : ComplexifiedQuaternions.ComplexQuat) :
    ‖(Y + A).det / 2 - Y.det / 2‖ ≤ ‖A‖ * (‖Y‖ + ‖A‖) := by
  have e : (Y + A).det / 2 - Y.det / 2 = (A.det + polarDet Y A) / 2 := by
    rw [det_add_eq_add_polarDet]
    ring
  rw [e, norm_div, Complex.norm_ofNat]
  have h1 := norm_add_le A.det (polarDet Y A)
  have h2 := ComplexifiedQuaternions.norm_det_le A
  have h3 := norm_polarDet_le Y A
  nlinarith
theorem norm_half_det_second_diff_le (Y A B D : ComplexifiedQuaternions.ComplexQuat) :
    ‖(Y + A + B + D).det / 2 - (Y + A).det / 2 - (Y + B).det / 2 + Y.det / 2‖ ≤
      ‖A‖ * ‖B‖ + ‖D‖ * (‖Y‖ + ‖A‖ + ‖B‖ + ‖D‖) := by
  have e : (Y + A + B + D).det / 2 - (Y + A).det / 2 - (Y + B).det / 2 + Y.det / 2 =
      (D.det + polarDet B D + polarDet A B + polarDet A D + polarDet Y D) / 2 := by
    have e1 : Y + A + B + D = Y + (A + (B + D)) := by abel
    rw [e1, det_add_eq_add_polarDet Y, det_add_eq_add_polarDet A, det_add_eq_add_polarDet B,
      det_add_eq_add_polarDet Y A, det_add_eq_add_polarDet Y B,
      polarDet_add_right, polarDet_add_right, polarDet_add_right]
    ring
  rw [e, norm_div, Complex.norm_ofNat]
  have h1 := ComplexifiedQuaternions.norm_det_le D
  have h2 := norm_polarDet_le B D
  have h3 := norm_polarDet_le A B
  have h4 := norm_polarDet_le A D
  have h5 := norm_polarDet_le Y D
  have h6 := norm_add_le (D.det + polarDet B D + polarDet A B + polarDet A D) (polarDet Y D)
  have h7 := norm_add_le (D.det + polarDet B D + polarDet A B) (polarDet A D)
  have h8 := norm_add_le (D.det + polarDet B D) (polarDet A B)
  have h9 := norm_add_le D.det (polarDet B D)
  nlinarith [norm_nonneg D, norm_nonneg A, norm_nonneg B, norm_nonneg Y]
theorem one_sub_half_trace_eq_half_det {G : ComplexifiedQuaternions.ComplexQuat} (h : G.det = 1) :
    1 - G.trace / 2 = (G - 1).det / 2 := by
  have h1 := ComplexifiedQuaternions.det_one_add (G - 1)
  rw [add_sub_cancel, h] at h1
  have h2 : (G - 1).trace = G.trace - 2 := by
    simp [Matrix.trace_sub, Matrix.trace_one]
  rw [h2] at h1
  linear_combination (1 / 2 : ℂ) * h1
def expField (R : F.GaugeField 0) (ξ : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) :
    F.ComplexField 0 :=
  fun x i => BlockAverages.unitExp (ξ x i) * BlockAverages.ofUnit (R x i)
theorem complexPlaquetteHolonomy_eq {j : ℕ} (X : F.ComplexField j) (p : F.Site j × Fin 4 × Fin 4) :
    BlockAverages.complexPlaquetteHolonomy X p = X p.1 p.2.1 * X (p.1 + BlockAverages.unitStep j p.2.1) p.2.2 *
      Matrix.adjugate (X (p.1 + BlockAverages.unitStep j p.2.2) p.2.1) * Matrix.adjugate (X p.1 p.2.2) := by
  simp [BlockAverages.complexPlaquetteHolonomy, BlockAverages.complexPathHolonomy, BlockAverages.complexLinkValue,
    BlockAverages.stepDisplacement, mul_assoc, sub_eq_add_neg, add_assoc]
section Plaquette
variable (R : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4)
def plaquetteSourceNorm (ξ : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) : ℝ :=
  ‖ξ p.1 p.2.1‖ + ‖ξ (p.1 + BlockAverages.unitStep 0 p.2.1) p.2.2‖ +
    ‖ξ (p.1 + BlockAverages.unitStep 0 p.2.2) p.2.1‖ + ‖ξ p.1 p.2.2‖
def basePlaquetteHolonomy : BlockAverages.UnitQuaternion :=
  R p.1 p.2.1 * R (p.1 + BlockAverages.unitStep 0 p.2.1) p.2.2 *
    (R (p.1 + BlockAverages.unitStep 0 p.2.2) p.2.1)⁻¹ * (R p.1 p.2.2)⁻¹
def covariantCurl (ξ : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) :
    ComplexifiedQuaternions.ComplexQuat :=
  ComplexifiedQuaternions.purePart (ξ p.1 p.2.1) +
      BlockAverages.conjByUnit (R p.1 p.2.1)
        (ComplexifiedQuaternions.purePart (ξ (p.1 + BlockAverages.unitStep 0 p.2.1) p.2.2)) -
    BlockAverages.conjByUnit (R p.1 p.2.1 * R (p.1 + BlockAverages.unitStep 0 p.2.1) p.2.2 *
        (R (p.1 + BlockAverages.unitStep 0 p.2.2) p.2.1)⁻¹)
      (ComplexifiedQuaternions.purePart (ξ (p.1 + BlockAverages.unitStep 0 p.2.2) p.2.1)) -
    BlockAverages.conjByUnit (basePlaquetteHolonomy R p) (ComplexifiedQuaternions.purePart (ξ p.1 p.2.2))
def plaquetteRemainder (ξ : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) :
    ComplexifiedQuaternions.ComplexQuat :=
  BlockAverages.complexPlaquetteHolonomy (expField R ξ) p -
    BlockAverages.ofUnit (basePlaquetteHolonomy R p) - covariantCurl R p ξ
theorem complexPlaquetteHolonomy_expField_eq (ξ : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) :
    BlockAverages.complexPlaquetteHolonomy (expField R ξ) p =
      BlockAverages.unitExp (ξ p.1 p.2.1) *
        BlockAverages.conjByUnit (R p.1 p.2.1)
          (BlockAverages.unitExp (ξ (p.1 + BlockAverages.unitStep 0 p.2.1) p.2.2)) *
      BlockAverages.conjByUnit (R p.1 p.2.1 * R (p.1 + BlockAverages.unitStep 0 p.2.1) p.2.2 *
          (R (p.1 + BlockAverages.unitStep 0 p.2.2) p.2.1)⁻¹)
        (Matrix.adjugate (BlockAverages.unitExp (ξ (p.1 + BlockAverages.unitStep 0 p.2.2) p.2.1))) *
      BlockAverages.conjByUnit (basePlaquetteHolonomy R p)
        (Matrix.adjugate (BlockAverages.unitExp (ξ p.1 p.2.2))) *
      BlockAverages.ofUnit (basePlaquetteHolonomy R p) := by
  rw [complexPlaquetteHolonomy_eq]
  simp only [expField, Matrix.adjugate_mul_distrib, ← BlockAverages.ofUnit_inv, BlockAverages.conjByUnit,
    basePlaquetteHolonomy, mul_inv_rev, inv_inv, BlockAverages.ofUnit_mul, mul_assoc,
    ComplexContours.ofUnit_inv_mul_cancel_left, ComplexContours.ofUnit_mul_inv_cancel_left,
    BlockAverages.ofUnit_mul_inv, mul_one]
theorem norm_unitExp_sub_one_le {y : ComplexifiedQuaternions.ComplexQuat} (hy : ‖y‖ ≤ 1 / 256) :
    ‖BlockAverages.unitExp y - 1‖ ≤ 2 * ‖y‖ := by
  have h1 := ComplexDifferences.norm_unitExp_sub_one_sub_purePart_le (y := y) (by linarith)
  have h2 := ComplexifiedQuaternions.norm_purePart_le y
  have e : BlockAverages.unitExp y - 1 =
      (BlockAverages.unitExp y - 1 - ComplexifiedQuaternions.purePart y) + ComplexifiedQuaternions.purePart y := by
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  nlinarith [norm_nonneg y]
theorem norm_plaquetteRemainder_le {ξ : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat}
    (hN : plaquetteSourceNorm p ξ ≤ 1 / 256) {σ : ℝ}
    (hσ : ‖BlockAverages.ofUnit (basePlaquetteHolonomy R p) - 1‖ ≤ σ) :
    ‖plaquetteRemainder R p ξ‖ ≤ 173 * (plaquetteSourceNorm p ξ ^ 2 + σ * plaquetteSourceNorm p ξ) := by
  set ξ₁ := ξ p.1 p.2.1 with hξ₁
  set ξ₂ := ξ (p.1 + BlockAverages.unitStep 0 p.2.1) p.2.2 with hξ₂
  set ξ₃ := ξ (p.1 + BlockAverages.unitStep 0 p.2.2) p.2.1 with hξ₃
  set ξ₄ := ξ p.1 p.2.2 with hξ₄
  set g₂ := R p.1 p.2.1 with hg₂
  set g₃ := R p.1 p.2.1 * R (p.1 + BlockAverages.unitStep 0 p.2.1) p.2.2 *
    (R (p.1 + BlockAverages.unitStep 0 p.2.2) p.2.1)⁻¹ with hg₃
  set g₄ := basePlaquetteHolonomy R p with hg₄
  have hN' : plaquetteSourceNorm p ξ = ‖ξ₁‖ + ‖ξ₂‖ + ‖ξ₃‖ + ‖ξ₄‖ := rfl
  set N := plaquetteSourceNorm p ξ with hNd
  have n₁ := norm_nonneg ξ₁
  have n₂ := norm_nonneg ξ₂
  have n₃ := norm_nonneg ξ₃
  have n₄ := norm_nonneg ξ₄
  have hN0 : 0 ≤ N := by linarith
  have hσ0 : 0 ≤ σ := (norm_nonneg _).trans hσ
  have b₁ : ‖ξ₁‖ ≤ 1 / 256 := by linarith
  have b₂ : ‖ξ₂‖ ≤ 1 / 256 := by linarith
  have b₃ : ‖ξ₃‖ ≤ 1 / 256 := by linarith
  have b₄ : ‖ξ₄‖ ≤ 1 / 256 := by linarith
  set f₁ := BlockAverages.unitExp ξ₁ - 1 - ComplexifiedQuaternions.purePart ξ₁ with hf₁
  set f₂ := BlockAverages.unitExp ξ₂ - 1 - ComplexifiedQuaternions.purePart ξ₂ with hf₂
  set f₃ := BlockAverages.unitExp ξ₃ - 1 - ComplexifiedQuaternions.purePart ξ₃ with hf₃
  set f₄ := BlockAverages.unitExp ξ₄ - 1 - ComplexifiedQuaternions.purePart ξ₄ with hf₄
  have c₁ : ‖f₁‖ ≤ 129 * ‖ξ₁‖ ^ 2 := ComplexDifferences.norm_unitExp_sub_one_sub_purePart_le (by linarith)
  have c₂ : ‖f₂‖ ≤ 129 * ‖ξ₂‖ ^ 2 := ComplexDifferences.norm_unitExp_sub_one_sub_purePart_le (by linarith)
  have c₃ : ‖f₃‖ ≤ 129 * ‖ξ₃‖ ^ 2 := ComplexDifferences.norm_unitExp_sub_one_sub_purePart_le (by linarith)
  have c₄ : ‖f₄‖ ≤ 129 * ‖ξ₄‖ ^ 2 := ComplexDifferences.norm_unitExp_sub_one_sub_purePart_le (by linarith)
  set a₁ := BlockAverages.unitExp ξ₁ - 1 with ha₁
  set a₂ := BlockAverages.conjByUnit g₂ (BlockAverages.unitExp ξ₂ - 1) with ha₂
  set a₃ := BlockAverages.conjByUnit g₃ (Matrix.adjugate (BlockAverages.unitExp ξ₃ - 1)) with ha₃
  set a₄ := BlockAverages.conjByUnit g₄ (Matrix.adjugate (BlockAverages.unitExp ξ₄ - 1)) with ha₄
  have d₁ : ‖a₁‖ ≤ 2 * ‖ξ₁‖ := norm_unitExp_sub_one_le b₁
  have d₂ : ‖a₂‖ ≤ 2 * ‖ξ₂‖ := by
    rw [ha₂, BlockAverages.norm_conjByUnit]; exact norm_unitExp_sub_one_le b₂
  have d₃ : ‖a₃‖ ≤ 2 * ‖ξ₃‖ := by
    rw [ha₃, BlockAverages.norm_conjByUnit, ComplexifiedQuaternions.norm_adjugate]
    exact norm_unitExp_sub_one_le b₃
  have d₄ : ‖a₄‖ ≤ 2 * ‖ξ₄‖ := by
    rw [ha₄, BlockAverages.norm_conjByUnit, ComplexifiedQuaternions.norm_adjugate]
    exact norm_unitExp_sub_one_le b₄
  have e₁ : BlockAverages.unitExp ξ₁ = 1 + a₁ := by rw [ha₁]; abel
  have e₂ : BlockAverages.conjByUnit g₂ (BlockAverages.unitExp ξ₂) = 1 + a₂ := by
    rw [ha₂, ComplexContours.conjByUnit_sub, ComplexContours.conjByUnit_one]
    abel
  have e₃ : BlockAverages.conjByUnit g₃ (Matrix.adjugate (BlockAverages.unitExp ξ₃)) = 1 + a₃ := by
    have : BlockAverages.unitExp ξ₃ = 1 + (BlockAverages.unitExp ξ₃ - 1) := by abel
    rw [ha₃]
    nth_rewrite 1 [this]
    rw [ComplexifiedQuaternions.adjugate_map_add, ComplexContours.adjugate_one_complexQuat,
      ComplexContours.conjByUnit_add, ComplexContours.conjByUnit_one]
  have e₄ : BlockAverages.conjByUnit g₄ (Matrix.adjugate (BlockAverages.unitExp ξ₄)) = 1 + a₄ := by
    have : BlockAverages.unitExp ξ₄ = 1 + (BlockAverages.unitExp ξ₄ - 1) := by abel
    rw [ha₄]
    nth_rewrite 1 [this]
    rw [ComplexifiedQuaternions.adjugate_map_add, ComplexContours.adjugate_one_complexQuat,
      ComplexContours.conjByUnit_add, ComplexContours.conjByUnit_one]
  have hG : BlockAverages.complexPlaquetteHolonomy (expField R ξ) p =
      (1 + a₁) * (1 + a₂) * (1 + a₃) * (1 + a₄) * BlockAverages.ofUnit g₄ := by
    rw [complexPlaquetteHolonomy_expField_eq]
    rw [← hξ₁, ← hξ₂, ← hξ₃, ← hξ₄, ← hg₂, ← hg₃, ← hg₄, e₁, e₂, e₃, e₄]
  have hτ : 2 * N ≤ 1 := by linarith
  have hA : ‖a₁‖ ≤ 2 * N := by linarith
  have hB : ‖a₂‖ ≤ 2 * N := by linarith
  have hC : ‖a₃‖ ≤ 2 * N := by linarith
  have hD : ‖a₄‖ ≤ 2 * N := by linarith
  have hfour := ComplexContours.norm_four_factor_sub_le a₁ a₂ a₃ a₄ hτ hA hB hC hD
  set Pp := (1 + a₁) * (1 + a₂) * (1 + a₃) * (1 + a₄) with hPp
  set Sg := a₁ + a₂ + a₃ + a₄ with hSg
  have hSgn : ‖Sg‖ ≤ 2 * N := by
    have u1 := norm_add_le (a₁ + a₂ + a₃) a₄
    have u2 := norm_add_le (a₁ + a₂) a₃
    have u3 := norm_add_le a₁ a₂
    linarith
  have hcurl : Sg - covariantCurl R p ξ = f₁ + BlockAverages.conjByUnit g₂ f₂ +
      BlockAverages.conjByUnit g₃ (Matrix.adjugate f₃) + BlockAverages.conjByUnit g₄ (Matrix.adjugate f₄) := by
    have a₁e : BlockAverages.unitExp ξ₁ - 1 = ComplexifiedQuaternions.purePart ξ₁ + f₁ := by rw [hf₁, ha₁]; abel
    have a₂e : BlockAverages.unitExp ξ₂ - 1 = ComplexifiedQuaternions.purePart ξ₂ + f₂ := by rw [hf₂]; abel
    have a₃e : BlockAverages.unitExp ξ₃ - 1 = ComplexifiedQuaternions.purePart ξ₃ + f₃ := by rw [hf₃]; abel
    have a₄e : BlockAverages.unitExp ξ₄ - 1 = ComplexifiedQuaternions.purePart ξ₄ + f₄ := by rw [hf₄]; abel
    rw [hSg, ha₁, ha₂, ha₃, ha₄, a₁e, a₂e, a₃e, a₄e]
    simp only [covariantCurl, ComplexifiedQuaternions.adjugate_map_add, ComplexContours.adjugate_purePart,
      ComplexContours.conjByUnit_add, ← hξ₁, ← hξ₂, ← hξ₃, ← hξ₄, ← hg₂, ← hg₃, ← hg₄]
    have u3 : BlockAverages.conjByUnit g₃ (-ComplexifiedQuaternions.purePart ξ₃) =
        -BlockAverages.conjByUnit g₃ (ComplexifiedQuaternions.purePart ξ₃) := by
      simp [BlockAverages.conjByUnit]
    have u4 : BlockAverages.conjByUnit g₄ (-ComplexifiedQuaternions.purePart ξ₄) =
        -BlockAverages.conjByUnit g₄ (ComplexifiedQuaternions.purePart ξ₄) := by
      simp [BlockAverages.conjByUnit]
    rw [u3, u4]
    abel
  have hcn : ‖Sg - covariantCurl R p ξ‖ ≤ 129 * N ^ 2 := by
    rw [hcurl]
    have u1 := norm_add_le (f₁ + BlockAverages.conjByUnit g₂ f₂ + BlockAverages.conjByUnit g₃ (Matrix.adjugate f₃))
      (BlockAverages.conjByUnit g₄ (Matrix.adjugate f₄))
    have u2 := norm_add_le (f₁ + BlockAverages.conjByUnit g₂ f₂) (BlockAverages.conjByUnit g₃ (Matrix.adjugate f₃))
    have u3 := norm_add_le f₁ (BlockAverages.conjByUnit g₂ f₂)
    rw [BlockAverages.norm_conjByUnit, ComplexifiedQuaternions.norm_adjugate] at u1 u2
    rw [BlockAverages.norm_conjByUnit] at u3
    have v : ‖ξ₁‖ ^ 2 + ‖ξ₂‖ ^ 2 + ‖ξ₃‖ ^ 2 + ‖ξ₄‖ ^ 2 ≤ N ^ 2 := by
      rw [hN']
      nlinarith [mul_nonneg n₁ n₂, mul_nonneg n₁ n₃, mul_nonneg n₁ n₄, mul_nonneg n₂ n₃, mul_nonneg n₂ n₄,
        mul_nonneg n₃ n₄]
    linarith
  have hq : plaquetteRemainder R p ξ = (Pp - (1 + a₃ + a₁ + a₂ + a₄)) * BlockAverages.ofUnit g₄ +
      Sg * (BlockAverages.ofUnit g₄ - 1) + (Sg - covariantCurl R p ξ) := by
    rw [plaquetteRemainder, hG, ← hg₄]
    rw [hSg]
    noncomm_ring
  rw [hq]
  have w1 : ‖(Pp - (1 + a₃ + a₁ + a₂ + a₄)) * BlockAverages.ofUnit g₄‖ ≤ 44 * N ^ 2 := by
    rw [BlockAverages.norm_mul_ofUnit]
    refine hfour.trans (le_of_eq ?_)
    ring
  have w2 : ‖Sg * (BlockAverages.ofUnit g₄ - 1)‖ ≤ 2 * N * σ :=
    (norm_mul_le _ _).trans (mul_le_mul hSgn hσ (norm_nonneg _) (by positivity))
  have w3 := norm_add_le ((Pp - (1 + a₃ + a₁ + a₂ + a₄)) * BlockAverages.ofUnit g₄ +
    Sg * (BlockAverages.ofUnit g₄ - 1)) (Sg - covariantCurl R p ξ)
  have w4 := norm_add_le ((Pp - (1 + a₃ + a₁ + a₂ + a₄)) * BlockAverages.ofUnit g₄)
    (Sg * (BlockAverages.ofUnit g₄ - 1))
  have w5 : 0 ≤ σ * N := by positivity
  nlinarith
end Plaquette
section PlaquetteDifferences
variable (R : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4)
theorem plaquetteSourceNorm_add_le (a b : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) :
    plaquetteSourceNorm p (a + b) ≤ plaquetteSourceNorm p a + plaquetteSourceNorm p b := by
  unfold plaquetteSourceNorm
  simp only [Pi.add_apply]
  have h1 := norm_add_le (a p.1 p.2.1) (b p.1 p.2.1)
  have h2 := norm_add_le (a (p.1 + BlockAverages.unitStep 0 p.2.1) p.2.2)
    (b (p.1 + BlockAverages.unitStep 0 p.2.1) p.2.2)
  have h3 := norm_add_le (a (p.1 + BlockAverages.unitStep 0 p.2.2) p.2.1)
    (b (p.1 + BlockAverages.unitStep 0 p.2.2) p.2.1)
  have h4 := norm_add_le (a p.1 p.2.2) (b p.1 p.2.2)
  linarith
theorem plaquetteSourceNorm_smul (z : ℂ) (a : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) :
    plaquetteSourceNorm p (z • a) = ‖z‖ * plaquetteSourceNorm p a := by
  unfold plaquetteSourceNorm
  simp only [Pi.smul_apply, norm_smul]
  ring
theorem plaquetteSourceNorm_nonneg (a : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) :
    0 ≤ plaquetteSourceNorm p a := by
  unfold plaquetteSourceNorm
  positivity
theorem covariantCurl_add (a b : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) :
    covariantCurl R p (a + b) = covariantCurl R p a + covariantCurl R p b := by
  simp only [covariantCurl, Pi.add_apply, ComplexifiedQuaternions.purePart_add, ComplexContours.conjByUnit_add]
  abel
theorem det_expField (ξ : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) (x : F.Site 0) (i : Fin 4) :
    (expField R ξ x i).det = 1 := by
  rw [expField, Matrix.det_mul, ComplexChainStep.det_unitExp, BlockAverages.det_ofUnit, one_mul]
theorem det_complexPlaquetteHolonomy_expField (ξ : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) :
    (BlockAverages.complexPlaquetteHolonomy (expField R ξ) p).det = 1 := by
  rw [complexPlaquetteHolonomy_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
    ComplexContours.det_adjugate_complexQuat, ComplexContours.det_adjugate_complexQuat, det_expField,
    det_expField, det_expField, det_expField]
  norm_num
theorem differentiableAt_expField (y e : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) {z : ℂ}
    {x : F.Site 0} {i : Fin 4} (h : ‖(y + z • e) x i‖ ≤ 1 / 16) :
    DifferentiableAt ℂ (fun w => expField R (y + w • e) x i) z := by
  simp only [expField]
  exact (ComplexDifferences.differentiableAt_unitExp_comp
    (ComplexRemainders.differentiableAt_fieldLine y e z x i) h).fun_mul (differentiableAt_const _)
theorem plaquetteRemainder_quadraticBound {σ : ℝ}
    (hσ : ‖BlockAverages.ofUnit (basePlaquetteHolonomy R p) - 1‖ ≤ σ) :
    ComplexRemainders.QuadraticBoundOnBall (plaquetteSourceNorm p) (plaquetteRemainder R p) 173 σ (1 / 256) where
  triangle := plaquetteSourceNorm_add_le p
  homogeneous := plaquetteSourceNorm_smul p
  holomorphic := by
    intro y e z hz
    have hk : ∀ {b : F.Site 0} {i : Fin 4}, ‖(y + z • e) b i‖ ≤ plaquetteSourceNorm p (y + z • e) →
        DifferentiableAt ℂ (fun w => expField R (y + w • e) b i) z := fun h =>
      differentiableAt_expField R y e (h.trans (by linarith))
    have n₁ := norm_nonneg ((y + z • e) p.1 p.2.1)
    have n₂ := norm_nonneg ((y + z • e) (p.1 + BlockAverages.unitStep 0 p.2.1) p.2.2)
    have n₃ := norm_nonneg ((y + z • e) (p.1 + BlockAverages.unitStep 0 p.2.2) p.2.1)
    have n₄ := norm_nonneg ((y + z • e) p.1 p.2.2)
    have d₁ := hk (b := p.1) (i := p.2.1) (by unfold plaquetteSourceNorm; linarith)
    have d₂ := hk (b := p.1 + BlockAverages.unitStep 0 p.2.1) (i := p.2.2) (by unfold plaquetteSourceNorm; linarith)
    have d₃ := hk (b := p.1 + BlockAverages.unitStep 0 p.2.2) (i := p.2.1) (by unfold plaquetteSourceNorm; linarith)
    have d₄ := hk (b := p.1) (i := p.2.2) (by unfold plaquetteSourceNorm; linarith)
    have hc : DifferentiableAt ℂ (fun w => covariantCurl R p (y + w • e)) z := by
      simp only [covariantCurl]
      have q₁ := ComplexRemainders.differentiableAt_purePart_comp
        (ComplexRemainders.differentiableAt_fieldLine y e z p.1 p.2.1)
      have q₂ := ComplexRemainders.differentiableAt_conjByUnit_comp (R p.1 p.2.1)
        (ComplexRemainders.differentiableAt_purePart_comp
          (ComplexRemainders.differentiableAt_fieldLine y e z (p.1 + BlockAverages.unitStep 0 p.2.1) p.2.2))
      have q₃ := ComplexRemainders.differentiableAt_conjByUnit_comp
        (R p.1 p.2.1 * R (p.1 + BlockAverages.unitStep 0 p.2.1) p.2.2 *
          (R (p.1 + BlockAverages.unitStep 0 p.2.2) p.2.1)⁻¹)
        (ComplexRemainders.differentiableAt_purePart_comp
          (ComplexRemainders.differentiableAt_fieldLine y e z (p.1 + BlockAverages.unitStep 0 p.2.2) p.2.1))
      have q₄ := ComplexRemainders.differentiableAt_conjByUnit_comp (basePlaquetteHolonomy R p)
        (ComplexRemainders.differentiableAt_purePart_comp
          (ComplexRemainders.differentiableAt_fieldLine y e z p.1 p.2.2))
      exact ((q₁.fun_add q₂).fun_sub q₃).fun_sub q₄
    simp only [plaquetteRemainder, complexPlaquetteHolonomy_eq]
    exact ((((d₁.fun_mul d₂).fun_mul (ComplexRemainders.differentiableAt_adjugate_comp d₃)).fun_mul
      (ComplexRemainders.differentiableAt_adjugate_comp d₄)).fun_sub (differentiableAt_const _)).fun_sub hc
  bound := fun y hy => norm_plaquetteRemainder_le R p hy.le hσ
def plaquetteGap (ξ : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) :
    ComplexifiedQuaternions.ComplexQuat :=
  BlockAverages.complexPlaquetteHolonomy (expField R ξ) p - 1
theorem plaquetteGap_eq (ξ : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) :
    plaquetteGap R p ξ = (BlockAverages.ofUnit (basePlaquetteHolonomy R p) - 1) + covariantCurl R p ξ +
      plaquetteRemainder R p ξ := by
  simp only [plaquetteGap, plaquetteRemainder]
  abel
theorem complexPlaquetteTerm_expField_eq (ξ : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat) :
    BlockAverages.complexPlaquetteTerm (expField R ξ) p = (plaquetteGap R p ξ).det / 2 :=
  one_sub_half_trace_eq_half_det (det_complexPlaquetteHolonomy_expField R p ξ)
set_option maxHeartbeats 1000000 in
theorem norm_complexPlaquetteTerm_second_diff_le {ξ e₁ e₂ : F.Site 0 → Fin 4 → ComplexifiedQuaternions.ComplexQuat}
    {σ t : ℝ} (hσ0 : 0 < σ) (hσ : ‖BlockAverages.ofUnit (basePlaquetteHolonomy R p) - 1‖ ≤ σ) (ht : 0 ≤ t)
    (hsm : 24 * (3 * t + σ) < 1 / 256) (h0 : plaquetteSourceNorm p ξ ≤ t) (h1 : plaquetteSourceNorm p e₁ ≤ t)
    (h2 : plaquetteSourceNorm p e₂ ≤ t) :
    ‖BlockAverages.complexPlaquetteTerm (expField R (ξ + e₁ + e₂)) p -
          BlockAverages.complexPlaquetteTerm (expField R (ξ + e₁)) p -
        BlockAverages.complexPlaquetteTerm (expField R (ξ + e₂)) p +
          BlockAverages.complexPlaquetteTerm (expField R ξ) p‖ ≤
      (‖covariantCurl R p e₁‖ + 12 * 173 * (3 * t + σ) * plaquetteSourceNorm p e₁) *
          (‖covariantCurl R p e₂‖ + 12 * 173 * (3 * t + σ) * plaquetteSourceNorm p e₂) +
        64 * 173 * plaquetteSourceNorm p e₁ * plaquetteSourceNorm p e₂ *
          (4 * (‖plaquetteGap R p ξ‖ + ‖plaquetteGap R p (ξ + e₁)‖ + ‖plaquetteGap R p (ξ + e₂)‖ +
            ‖plaquetteGap R p (ξ + e₁ + e₂)‖)) := by
  have hq := plaquetteRemainder_quadraticBound R p hσ
  have hN1 : plaquetteSourceNorm p (ξ + e₁) ≤ 3 * t := (plaquetteSourceNorm_add_le p _ _).trans (by linarith)
  have hN2 : plaquetteSourceNorm p (ξ + e₂) ≤ 3 * t := (plaquetteSourceNorm_add_le p _ _).trans (by linarith)
  have hN0 : plaquetteSourceNorm p ξ ≤ 3 * t := by linarith
  have hsm3 : 3 * (3 * t + σ) < 1 / 256 := by linarith
  have l1 := hq.norm_sub_le (by norm_num) hσ0 (t := 3 * t) (by positivity) hsm3 hN0 hN1
  have l2 := hq.norm_sub_le (by norm_num) hσ0 (t := 3 * t) (by positivity) hsm3 hN0 hN2
  have e1 : ξ + e₁ - ξ = e₁ := by abel
  have e2 : ξ + e₂ - ξ = e₂ := by abel
  rw [e1] at l1
  rw [e2] at l2
  have hd := hq.norm_second_diff_le (by norm_num) hσ0 (by linarith) (y := ξ) (e₁ := e₁) (e₂ := e₂) ht
    (by linarith) h0 h1 h2
  set Y₀ := plaquetteGap R p ξ with hY₀
  set Y₁ := plaquetteGap R p (ξ + e₁) with hY₁
  set Y₂ := plaquetteGap R p (ξ + e₂) with hY₂
  set Y₃ := plaquetteGap R p (ξ + e₁ + e₂) with hY₃
  set A := Y₁ - Y₀ with hA
  set B := Y₂ - Y₀ with hB
  set D := Y₃ - Y₁ - Y₂ + Y₀ with hD
  have hAe : A = covariantCurl R p e₁ + (plaquetteRemainder R p (ξ + e₁) - plaquetteRemainder R p ξ) := by
    rw [hA, hY₁, hY₀, plaquetteGap_eq, plaquetteGap_eq, covariantCurl_add]
    abel
  have hBe : B = covariantCurl R p e₂ + (plaquetteRemainder R p (ξ + e₂) - plaquetteRemainder R p ξ) := by
    rw [hB, hY₂, hY₀, plaquetteGap_eq, plaquetteGap_eq, covariantCurl_add]
    abel
  have hDe : D = plaquetteRemainder R p (ξ + e₁ + e₂) - plaquetteRemainder R p (ξ + e₁) -
      plaquetteRemainder R p (ξ + e₂) + plaquetteRemainder R p ξ := by
    rw [hD, hY₃, hY₁, hY₂, hY₀, plaquetteGap_eq, plaquetteGap_eq, plaquetteGap_eq, plaquetteGap_eq,
      covariantCurl_add, covariantCurl_add, covariantCurl_add]
    abel
  have hAn : ‖A‖ ≤ ‖covariantCurl R p e₁‖ + 12 * 173 * (3 * t + σ) * plaquetteSourceNorm p e₁ := by
    rw [hAe]
    exact (norm_add_le _ _).trans (by linarith)
  have hBn : ‖B‖ ≤ ‖covariantCurl R p e₂‖ + 12 * 173 * (3 * t + σ) * plaquetteSourceNorm p e₂ := by
    rw [hBe]
    exact (norm_add_le _ _).trans (by linarith)
  have hDn : ‖D‖ ≤ 64 * 173 * plaquetteSourceNorm p e₁ * plaquetteSourceNorm p e₂ := by
    rw [hDe]
    exact hd
  have hmain := norm_half_det_second_diff_le Y₀ A B D
  have s1 : Y₀ + A = Y₁ := by rw [hA]; abel
  have s2 : Y₀ + B = Y₂ := by rw [hB]; abel
  have s3 : Y₀ + A + B + D = Y₃ := by rw [hA, hB, hD]; abel
  rw [s3, s1, s2] at hmain
  simp only [complexPlaquetteTerm_expField_eq]
  rw [← hY₀, ← hY₁, ← hY₂, ← hY₃]
  refine hmain.trans ?_
  have b1 : ‖A‖ * ‖B‖ ≤ (‖covariantCurl R p e₁‖ + 12 * 173 * (3 * t + σ) * plaquetteSourceNorm p e₁) *
      (‖covariantCurl R p e₂‖ + 12 * 173 * (3 * t + σ) * plaquetteSourceNorm p e₂) :=
    mul_le_mul hAn hBn (norm_nonneg _) ((norm_nonneg _).trans hAn)
  have n₀ := norm_nonneg Y₀
  have n₁ := norm_nonneg Y₁
  have n₂ := norm_nonneg Y₂
  have n₃ := norm_nonneg Y₃
  have c1 : ‖A‖ ≤ ‖Y₁‖ + ‖Y₀‖ := norm_sub_le _ _
  have c2 : ‖B‖ ≤ ‖Y₂‖ + ‖Y₀‖ := norm_sub_le _ _
  have c3 : ‖D‖ ≤ ‖Y₃‖ + ‖Y₁‖ + ‖Y₂‖ + ‖Y₀‖ := by
    have u1 := norm_add_le (Y₃ - Y₁ - Y₂) Y₀
    have u2 := norm_sub_le (Y₃ - Y₁) Y₂
    have u3 := norm_sub_le Y₃ Y₁
    linarith
  have b2 : ‖D‖ * (‖Y₀‖ + ‖A‖ + ‖B‖ + ‖D‖) ≤ 64 * 173 * plaquetteSourceNorm p e₁ * plaquetteSourceNorm p e₂ *
      (4 * (‖Y₀‖ + ‖Y₁‖ + ‖Y₂‖ + ‖Y₃‖)) :=
    mul_le_mul hDn (by linarith)
      (add_nonneg (add_nonneg (add_nonneg n₀ (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _))
      ((norm_nonneg _).trans hDn)
  linarith
end PlaquetteDifferences
end YangMills.Construction.ComplexPlaquettes
end
