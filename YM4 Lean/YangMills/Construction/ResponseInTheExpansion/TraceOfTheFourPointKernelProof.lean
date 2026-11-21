import YangMills.Construction.ResponseInTheExpansion.TraceOfTheFourPointKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open LinearResponse
namespace ResponseInTheExpansion.FourPointKernelTrace
private theorem sum_orderedPlane (g : Fin 4 → Fin 4 → ℝ) :
    ∑ P : OrderedPlane, g P.1.1 P.1.2 = g 0 1 + g 0 2 + g 0 3 + g 1 2 + g 1 3 + g 2 3 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun e : Fin 4 × Fin 4 => e.1 < e.2) (by simp)
    (fun e => g e.1 e.2), Finset.sum_filter, Fintype.sum_prod_type]
  simp [Fin.sum_univ_four]
  ring
abbrev _root_.YangMills.DeltaSharedProofs.p501869 := @sum_orderedPlane
private def secondCompound (X : Matrix (Fin 4) (Fin 4) ℝ) : Matrix OrderedPlane OrderedPlane ℝ :=
  fun P P' => X P.1.1 P'.1.1 * X P.1.2 P'.1.2 - X P.1.1 P'.1.2 * X P.1.2 P'.1.1
private theorem secondCompound_mul (X Y : Matrix (Fin 4) (Fin 4) ℝ) :
    secondCompound X * secondCompound Y = secondCompound (X * Y) := by
  ext P P'
  rw [Matrix.mul_apply]
  refine (sum_orderedPlane (fun r t => (X P.1.1 r * X P.1.2 t - X P.1.1 t * X P.1.2 r) *
    (Y r P'.1.1 * Y t P'.1.2 - Y r P'.1.2 * Y t P'.1.1))).trans ?_
  simp only [secondCompound, Matrix.mul_apply, Fin.sum_univ_four]
  ring
private theorem secondCompound_one : secondCompound (1 : Matrix (Fin 4) (Fin 4) ℝ) = 1 := by
  ext ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩
  simp only [secondCompound, Matrix.one_apply, Subtype.mk.injEq, Prod.mk.injEq]
  simp only at hab hcd
  have hcross : (if a = d then (1 : ℝ) else 0) * (if b = c then 1 else 0) = 0 := by
    by_cases had : a = d
    · by_cases hbc : b = c
      · rw [had, hbc] at hab
        exact absurd hab hcd.not_gt
      · simp [hbc]
    · simp [had]
  rw [hcross, sub_zero]
  by_cases hac : a = c
  · by_cases hbd : b = d
    · simp [hac, hbd]
    · simp [hac, hbd]
  · simp [hac]
private theorem secondCompound_transpose (X : Matrix (Fin 4) (Fin 4) ℝ) :
    (secondCompound X).transpose = secondCompound X.transpose := by
  ext P P'
  simp only [Matrix.transpose_apply, secondCompound]
  ring
private theorem trace_secondCompound (X : Matrix (Fin 4) (Fin 4) ℝ) :
    (secondCompound X).trace = (X 0 0 * X 1 1 - X 0 1 * X 1 0) + (X 0 0 * X 2 2 - X 0 2 * X 2 0) +
      (X 0 0 * X 3 3 - X 0 3 * X 3 0) + (X 1 1 * X 2 2 - X 1 2 * X 2 1) +
      (X 1 1 * X 3 3 - X 1 3 * X 3 1) + (X 2 2 * X 3 3 - X 2 3 * X 3 2) :=
  sum_orderedPlane (fun μ ν => X μ μ * X ν ν - X μ ν * X ν μ)
private theorem trace_one_orderedPlane : (1 : Matrix OrderedPlane OrderedPlane ℝ).trace = 6 := by
  have h := sum_orderedPlane (fun _ _ => (1 : ℝ))
  simp only [Matrix.trace, Matrix.diag, Matrix.one_apply_eq]
  rw [h]
  norm_num
private def frobeniusSq (X : Matrix OrderedPlane OrderedPlane ℝ) : ℝ := (X * X.transpose).trace
private theorem frobeniusSq_eq_sum (X : Matrix OrderedPlane OrderedPlane ℝ) :
    frobeniusSq X = ∑ i, ∑ j, X i j ^ 2 := by
  simp only [frobeniusSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    pow_two]
private theorem frobeniusSq_add_four_le (a b c d : Matrix OrderedPlane OrderedPlane ℝ) :
    frobeniusSq (a + b + c + d) ≤ 4 * (frobeniusSq a + frobeniusSq b + frobeniusSq c + frobeniusSq d) := by
  simp only [frobeniusSq_eq_sum, Matrix.add_apply, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  nlinarith [sq_nonneg (a i j - b i j), sq_nonneg (a i j - c i j), sq_nonneg (a i j - d i j),
    sq_nonneg (b i j - c i j), sq_nonneg (b i j - d i j), sq_nonneg (c i j - d i j)]
private theorem frobeniusSq_nonneg (X : Matrix OrderedPlane OrderedPlane ℝ) : 0 ≤ frobeniusSq X := by
  rw [frobeniusSq_eq_sum]
  positivity
private theorem frobeniusSq_mul_orthogonal (X U : Matrix OrderedPlane OrderedPlane ℝ)
    (hU : U * U.transpose = 1) : frobeniusSq (X * U) = frobeniusSq X := by
  unfold frobeniusSq
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU, Matrix.one_mul]
private theorem frobeniusSq_orthogonal_mul (X U : Matrix OrderedPlane OrderedPlane ℝ)
    (hU : U.transpose * U = 1) : frobeniusSq (U * X) = frobeniusSq X := by
  unfold frobeniusSq
  rw [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hU, Matrix.mul_one]
private theorem orthogonal_mul (U V : Matrix OrderedPlane OrderedPlane ℝ) (hU : U * U.transpose = 1)
    (hV : V * V.transpose = 1) : (U * V) * (U * V).transpose = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc V, hV, Matrix.one_mul, hU]
private def reflectionMatrix (z : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => hyperplaneReflection z i j
private theorem sum_mul_kronecker_sub (i j : Fin 4) (p q : Fin 4 → ℝ) :
    ∑ k, (((if i = k then 1 else 0) - p k) * ((if k = j then 1 else 0) - q k) : ℝ) =
      (if i = j then 1 else 0) - q i - p j + ∑ k, p k * q k := by
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four] <;> ring
private theorem reflectionMatrix_mul_apply (z w : Fin 4 → ℝ) (i j : Fin 4) :
    (reflectionMatrix z * reflectionMatrix w) i j = (if i = j then 1 else 0) - 2 * w i * w j / sqNorm w -
      2 * z i * z j / sqNorm z +
      4 * euclideanInner z w * z i * w j / (sqNorm z * sqNorm w) := by
  rw [Matrix.mul_apply]
  refine (sum_mul_kronecker_sub i j (fun k => 2 * z i * z k / sqNorm z)
    (fun k => 2 * w k * w j / sqNorm w)).trans ?_
  simp only [euclideanInner, Fin.sum_univ_four]
  ring
private theorem reflectionMatrix_transpose (z : Fin 4 → ℝ) :
    (reflectionMatrix z).transpose = reflectionMatrix z := by
  ext i j
  show hyperplaneReflection z j i = hyperplaneReflection z i j
  unfold hyperplaneReflection
  by_cases h : i = j
  · subst h
    rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    ring
private theorem reflectionMatrix_mul_self (z : Fin 4 → ℝ) (hz : 0 < sqNorm z) :
    reflectionMatrix z * reflectionMatrix z = 1 := by
  ext i j
  have hinner : euclideanInner z z = sqNorm z := by
    simp only [euclideanInner, sqNorm, pow_two]
  rw [reflectionMatrix_mul_apply, Matrix.one_apply, hinner]
  have hz' := hz.ne'
  field_simp
  ring
private def wedgeReflection (z : Fin 4 → ℝ) : Matrix OrderedPlane OrderedPlane ℝ :=
  secondCompound (reflectionMatrix z)
private theorem wedgeReflection_transpose (z : Fin 4 → ℝ) :
    (wedgeReflection z).transpose = wedgeReflection z := by
  rw [wedgeReflection, secondCompound_transpose, reflectionMatrix_transpose]
private theorem wedgeReflection_mul_self (z : Fin 4 → ℝ) (hz : 0 < sqNorm z) :
    wedgeReflection z * wedgeReflection z = 1 := by
  rw [wedgeReflection, secondCompound_mul, reflectionMatrix_mul_self z hz, secondCompound_one]
private theorem wedgeReflection_orthogonal (z : Fin 4 → ℝ) (hz : 0 < sqNorm z) :
    wedgeReflection z * (wedgeReflection z).transpose = 1 := by
  rw [wedgeReflection_transpose, wedgeReflection_mul_self z hz]
set_option maxRecDepth 100000 in
private theorem secondInvariant_cleared (z e : Fin 4 → ℝ) (s E d : ℝ)
    (hs : s = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) (hE : E = e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2 + e 3 ^ 2)
    (hd : d = z 0 * e 0 + z 1 * e 1 + z 2 * e 2 + z 3 * e 3) (H : Fin 4 → Fin 4 → ℝ)
    (hH : ∀ i j, H i j = (if i = j then s * E else 0) - 2 * E * z i * z j - 2 * s * e i * e j +
      4 * d * z i * e j) :
    (H 0 0 * H 1 1 - H 0 1 * H 1 0) + (H 0 0 * H 2 2 - H 0 2 * H 2 0) +
      (H 0 0 * H 3 3 - H 0 3 * H 3 0) + (H 1 1 * H 2 2 - H 1 2 * H 2 1) +
      (H 1 1 * H 3 3 - H 1 3 * H 3 1) + (H 2 2 * H 3 3 - H 2 3 * H 3 2) =
      8 * d ^ 2 * s * E - 2 * s ^ 2 * E ^ 2 := by
  simp only [hH]
  simp only [if_true, Fin.isValue, Fin.reduceEq, if_false]
  subst hs hE hd
  ring
private theorem trace_wedgeReflection_mul (z e : Fin 4 → ℝ) (hz : 0 < sqNorm z)
    (he : sqNorm e = 1) :
    (wedgeReflection z * wedgeReflection e).trace = 8 * euclideanInner z e ^ 2 / sqNorm z - 2 := by
  have hz' := hz.ne'
  have hprod : ∀ i j, (reflectionMatrix z * reflectionMatrix e) i j =
      ((if i = j then sqNorm z * sqNorm e else 0) -
        2 * sqNorm e * z i * z j - 2 * sqNorm z * e i * e j +
        4 * euclideanInner z e * z i * e j) / sqNorm z := by
    intro i j
    rw [reflectionMatrix_mul_apply, he]
    by_cases h : i = j
    · simp only [h, if_true]
      field_simp
      ring
    · simp only [h, if_false]
      field_simp
      ring
  have hinv := secondInvariant_cleared z e (sqNorm z) (sqNorm e) (euclideanInner z e)
    (by simp only [sqNorm, Fin.sum_univ_four]) (by simp only [sqNorm, Fin.sum_univ_four])
    (by simp only [euclideanInner, Fin.sum_univ_four])
    (fun i j => (reflectionMatrix z * reflectionMatrix e) i j * sqNorm z) (by
    intro i j
    simp only [hprod]
    field_simp)
  rw [wedgeReflection, wedgeReflection, secondCompound_mul, trace_secondCompound]
  rw [he] at hinv
  have : 8 * euclideanInner z e ^ 2 / sqNorm z - 2 =
      (8 * euclideanInner z e ^ 2 * sqNorm z * 1 - 2 * sqNorm z ^ 2 * 1 ^ 2) /
        sqNorm z ^ 2 := by
    field_simp
  rw [this, ← hinv]
  field_simp
private theorem frobeniusSq_wedgeReflection_sub (z e : Fin 4 → ℝ) (hz : 0 < sqNorm z)
    (he₀ : 0 < sqNorm e) (he : sqNorm e = 1) :
    frobeniusSq (wedgeReflection z - wedgeReflection e) =
      16 - 16 * (euclideanInner z e ^ 2 / sqNorm z) := by
  unfold frobeniusSq
  rw [Matrix.transpose_sub, wedgeReflection_transpose, wedgeReflection_transpose]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  rw [wedgeReflection_mul_self z hz, wedgeReflection_mul_self e he₀, trace_one_orderedPlane,
    Matrix.trace_mul_comm (wedgeReflection e) (wedgeReflection z),
    trace_wedgeReflection_mul z e hz he]
  ring
private theorem prod_four_sub_one {R : Type*} [Ring R] (a₀ a₁ a₂ a₃ b : R) (h : b * b = 1) :
    a₀ * a₁ * a₂ * a₃ - 1 =
      (a₀ - b) * (a₁ * a₂ * a₃) + b * (a₁ - b) * (a₂ * a₃) + (a₂ - b) * a₃ + b * (a₃ - b) := by
  simp only [sub_mul, mul_sub, mul_assoc, h, one_mul]
  abel
private theorem planeKernelMatrix_eq_smul (z : Fin 4 → ℝ) :
    planeKernelMatrix z = (Real.pi ^ 2 * sqNorm z ^ 2)⁻¹ • wedgeReflection z := by
  ext P P'
  simp only [planeKernelMatrix, continuumCurvatureKernel, wedgeReflection, secondCompound,
    reflectionMatrix, Matrix.smul_apply, smul_eq_mul]
  rw [div_eq_inv_mul]
private theorem trace_wedge_prod_mem (z : Fin 4 → Fin 4 → ℝ) (e : Fin 4 → ℝ) (he : sqNorm e = 1)
    (hpos : ∀ i, 0 < sqNorm (z i))
    (hangle : ∀ i, (1 - (1 / 8 : ℝ) ^ 2) * sqNorm (z i) ≤ euclideanInner (z i) e ^ 2) :
    4 ≤ (wedgeReflection (z 0) * wedgeReflection (z 1) * wedgeReflection (z 2) *
        wedgeReflection (z 3)).trace ∧
      (wedgeReflection (z 0) * wedgeReflection (z 1) * wedgeReflection (z 2) *
        wedgeReflection (z 3)).trace ≤ 6 := by
  have he₀ : 0 < sqNorm e := by rw [he]; norm_num
  have hclose : ∀ i, frobeniusSq (wedgeReflection (z i) - wedgeReflection e) ≤ 1 / 4 := by
    intro i
    rw [frobeniusSq_wedgeReflection_sub (z i) e (hpos i) he₀ he]
    have h1 : (1 - (1 / 8 : ℝ) ^ 2) ≤ euclideanInner (z i) e ^ 2 / sqNorm (z i) := by
      rw [le_div_iff₀ (hpos i)]
      exact hangle i
    norm_num at h1 ⊢
    linarith
  have hB := wedgeReflection_mul_self e he₀
  have hBt : (wedgeReflection e).transpose * wedgeReflection e = 1 := by
    rw [wedgeReflection_transpose, hB]
  have ho := fun i => wedgeReflection_orthogonal (z i) (hpos i)
  have h12 := orthogonal_mul _ _ (ho 1) (ho 2)
  have h23 := orthogonal_mul _ _ (ho 2) (ho 3)
  have h123 := orthogonal_mul _ _ h12 (ho 3)
  have h01 := orthogonal_mul _ _ (ho 0) (ho 1)
  have hM := orthogonal_mul _ _ (orthogonal_mul _ _ h01 (ho 2)) (ho 3)
  have hF : frobeniusSq (wedgeReflection (z 0) * wedgeReflection (z 1) * wedgeReflection (z 2) *
      wedgeReflection (z 3) - 1) ≤ 4 := by
    rw [prod_four_sub_one _ _ _ _ (wedgeReflection e) hB]
    refine (frobeniusSq_add_four_le _ _ _ _).trans ?_
    rw [frobeniusSq_mul_orthogonal _ _ h123, frobeniusSq_mul_orthogonal _ _ h23,
      frobeniusSq_orthogonal_mul _ _ hBt, frobeniusSq_mul_orthogonal _ _ (ho 3),
      frobeniusSq_orthogonal_mul _ _ hBt]
    linarith [hclose 0, hclose 1, hclose 2, hclose 3]
  have hT : frobeniusSq (wedgeReflection (z 0) * wedgeReflection (z 1) * wedgeReflection (z 2) *
      wedgeReflection (z 3) - 1) =
      12 - 2 * (wedgeReflection (z 0) * wedgeReflection (z 1) * wedgeReflection (z 2) *
        wedgeReflection (z 3)).trace := by
    unfold frobeniusSq
    rw [Matrix.transpose_sub, Matrix.transpose_one]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, Matrix.trace_sub]
    rw [hM, trace_one_orderedPlane, Matrix.trace_transpose]
    ring
  have hN := frobeniusSq_nonneg (wedgeReflection (z 0) * wedgeReflection (z 1) *
    wedgeReflection (z 2) * wedgeReflection (z 3) - 1)
  constructor <;> linarith
theorem fourPointKernelTrace_holds : fourPointKernelTraceStatement := by
  intro z e he _ hpos hangle
  obtain ⟨h4, h6⟩ := trace_wedge_prod_mem z e he hpos hangle
  have hπ : 0 < Real.pi := Real.pi_pos
  have hP : 0 < ∏ i, (sqNorm (z i) ^ 2)⁻¹ :=
    Finset.prod_pos fun i _ => inv_pos.mpr (pow_pos (hpos i) 2)
  have hc : 0 < (∏ i, (sqNorm (z i) ^ 2)⁻¹) / Real.pi ^ 8 := div_pos hP (pow_pos hπ 8)
  have hK : Matrix.trace (planeKernelMatrix (z 0) * planeKernelMatrix (z 1) *
        planeKernelMatrix (z 2) * planeKernelMatrix (z 3)) =
      (∏ i, (sqNorm (z i) ^ 2)⁻¹) / Real.pi ^ 8 *
        (wedgeReflection (z 0) * wedgeReflection (z 1) * wedgeReflection (z 2) *
          wedgeReflection (z 3)).trace := by
    simp only [planeKernelMatrix_eq_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul, Fin.prod_univ_four]
    ring
  rw [hK]
  have e3 : 3 / Real.pi ^ 8 * ∏ i, (sqNorm (z i) ^ 2)⁻¹ =
      (∏ i, (sqNorm (z i) ^ 2)⁻¹) / Real.pi ^ 8 * 3 := by ring
  have e6 : 6 / Real.pi ^ 8 * ∏ i, (sqNorm (z i) ^ 2)⁻¹ =
      (∏ i, (sqNorm (z i) ^ 2)⁻¹) / Real.pi ^ 8 * 6 := by ring
  rw [e3, e6]
  exact ⟨mul_le_mul_of_nonneg_left (by linarith) hc.le, mul_le_mul_of_nonneg_left h6 hc.le⟩
end ResponseInTheExpansion.FourPointKernelTrace
end YangMills.Construction
end
