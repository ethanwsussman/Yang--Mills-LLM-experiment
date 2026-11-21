import YangMills.Construction.Matrices.ExpProductExpansionAndConjugation
import Mathlib
import YangMills.Construction.Matrices.RepresentationsFieldsAndSmoothFunctionsOnG

section
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2.FourExpConjugation
def bracket (X Y : ComplexMatrix2) : ComplexMatrix2 := X * Y - Y * X
def SecondOrderExpansion : Prop :=
  ∀ (Z : Fin 4 → ComplexMatrix2) (Y : ComplexMatrix2) (ϱ : ℝ) (s W P : ComplexMatrix2),
    ϱ = ∑ j, operatorNorm (Z j) → ϱ ≤ 1 →
    s = ∑ j, Z j → W = halfCommutatorSum Z → P = (List.ofFn fun j => matExp (Z j)).prod →
    operatorNorm (conjugateBy P Y - Y - bracket s Y -
        ((1 / 2 : ℂ) • bracket s (bracket s Y) + bracket W Y)) ≤
        10 * Real.exp 1 ^ 2 * ϱ ^ 3 * operatorNorm Y ∧
      operatorNorm (bracket s Y) ≤ 2 * ϱ * operatorNorm Y ∧
      operatorNorm ((1 / 2 : ℂ) • bracket s (bracket s Y) + bracket W Y) ≤
        3 * ϱ ^ 2 * operatorNorm Y
end YangMills.Construction.Matrices.ComplexMatrix2.FourExpConjugation
end
end

open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
namespace FourExpConjugation
private theorem matExp_mul_matExp_neg (A : ComplexMatrix2) : matExp A * matExp (-A) = 1 := by apply _root_.YangMills.Construction.SpinHarmonics.matExp_mul_matExp_neg <;> assumption
private theorem list_prod_ofFn_fin_four (f : Fin 4 → ComplexMatrix2) :
    (List.ofFn f).prod = f 0 * f 1 * f 2 * f 3 := by
  simp [List.ofFn_succ, mul_assoc]
private theorem halfCommutatorSum_fin_four (Z : Fin 4 → ComplexMatrix2) :
    halfCommutatorSum Z = (1 / 2 : ℂ) • ((Z 0 * Z 1 - Z 1 * Z 0) + (Z 0 * Z 2 - Z 2 * Z 0) +
      (Z 0 * Z 3 - Z 3 * Z 0) + (Z 1 * Z 2 - Z 2 * Z 1) + (Z 1 * Z 3 - Z 3 * Z 1) +
      (Z 2 * Z 3 - Z 3 * Z 2)) := by
  have h0 : Finset.Ioi (0 : Fin 4) = {1, 2, 3} := by decide
  have h1 : Finset.Ioi (1 : Fin 4) = {2, 3} := by decide
  have h2 : Finset.Ioi (2 : Fin 4) = {3} := by decide
  have h3 : Finset.Ioi (3 : Fin 4) = ∅ := by decide
  unfold halfCommutatorSum
  rw [Fin.sum_univ_four, h0, h1, h2, h3]
  congr 1
  simp
  abel
abbrev _root_.YangMills.SharedProofs.p20090 := @halfCommutatorSum_fin_four
private theorem norm_bracket_le_two_mul (X Y : ComplexMatrix2) :
    ‖bracket X Y‖ ≤ 2 * ‖X‖ * ‖Y‖ := by
  have h1 := norm_mul_le X Y
  have h2 := norm_mul_le Y X
  have h3 := norm_sub_le (X * Y) (Y * X)
  unfold bracket
  linarith
abbrev _root_.YangMills.SharedProofs.p42284 := @norm_bracket_le_two_mul
private theorem norm_sandwich_le_pow_three {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (X Y X' : ComplexMatrix2) (a b : ℕ)
    (hab : 3 ≤ a + b) (hX : ‖X‖ ≤ ρ ^ a) (hX' : ‖X'‖ ≤ ρ ^ b) :
    ‖X * Y * X'‖ ≤ ρ ^ 3 * ‖Y‖ := by
  have h := norm_mul_le_of_le (norm_mul_le_of_le hX (le_refl ‖Y‖)) hX'
  have h2 : ρ ^ (a + b) ≤ ρ ^ 3 := pow_le_pow_of_le_one h0 h1 hab
  calc ‖X * Y * X'‖ ≤ ρ ^ a * ‖Y‖ * ρ ^ b := h
    _ = ρ ^ (a + b) * ‖Y‖ := by rw [pow_add]; ring
    _ ≤ ρ ^ 3 * ‖Y‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
private theorem norm_cubic_remainder_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (s A A' R R' Y : ComplexMatrix2)
    (hs : ‖s‖ ≤ ρ) (hA : ‖A‖ ≤ ρ ^ 2) (hA' : ‖A'‖ ≤ ρ ^ 2) (hR : ‖R‖ ≤ ρ ^ 3)
    (hR' : ‖R'‖ ≤ ρ ^ 3) :
    ‖(1 + s + A + R) * Y * (1 - s + A' + R') - Y - (s * Y - Y * s) -
        (A * Y + Y * A' - s * Y * s)‖ ≤ 10 * ρ ^ 3 * ‖Y‖ := by
  have e : (1 + s + A + R) * Y * (1 - s + A' + R') - Y - (s * Y - Y * s) -
        (A * Y + Y * A' - s * Y * s) =
      1 * Y * R' + s * Y * A' + s * Y * R' + A * Y * (-s) + A * Y * A' + A * Y * R' +
        R * Y * 1 + R * Y * (-s) + R * Y * A' + R * Y * R' := by
    noncomm_ring
  rw [e]
  have n1 : ‖(1 : ComplexMatrix2)‖ ≤ ρ ^ 0 := by simp
  have ns : ‖s‖ ≤ ρ ^ 1 := by simpa using hs
  have nn : ‖-s‖ ≤ ρ ^ 1 := by simpa using hs
  have t1 := norm_sandwich_le_pow_three h0 h1 1 Y R' 0 3 (by norm_num) n1 hR'
  have t2 := norm_sandwich_le_pow_three h0 h1 s Y A' 1 2 (by norm_num) ns hA'
  have t3 := norm_sandwich_le_pow_three h0 h1 s Y R' 1 3 (by norm_num) ns hR'
  have t4 := norm_sandwich_le_pow_three h0 h1 A Y (-s) 2 1 (by norm_num) hA nn
  have t5 := norm_sandwich_le_pow_three h0 h1 A Y A' 2 2 (by norm_num) hA hA'
  have t6 := norm_sandwich_le_pow_three h0 h1 A Y R' 2 3 (by norm_num) hA hR'
  have t7 := norm_sandwich_le_pow_three h0 h1 R Y 1 3 0 (by norm_num) hR n1
  have t8 := norm_sandwich_le_pow_three h0 h1 R Y (-s) 3 1 (by norm_num) hR nn
  have t9 := norm_sandwich_le_pow_three h0 h1 R Y A' 3 2 (by norm_num) hR hA'
  have t10 := norm_sandwich_le_pow_three h0 h1 R Y R' 3 3 (by norm_num) hR hR'
  refine (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
    (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
      (norm_add_le_of_le t1 t2) t3) t4) t5) t6) t7) t8) t9) t10).trans_eq ?_
  ring
private theorem quadratic_terms_eq_brackets (s W Y : ComplexMatrix2) :
    (1 / 2 : ℂ) • bracket s (bracket s Y) + bracket W Y =
      ((1 / 2 : ℂ) • s ^ 2 + W) * Y + Y * ((1 / 2 : ℂ) • s ^ 2 - W) - s * Y * s := by
  have h : bracket s (bracket s Y) = s ^ 2 * Y + Y * s ^ 2 - (2 : ℂ) • (s * Y * s) := by
    rw [two_smul]
    unfold bracket
    noncomm_ring
  have h2 : (1 / 2 : ℂ) • (2 : ℂ) • (s * Y * s) = s * Y * s := by
    rw [smul_smul]
    norm_num
  rw [h, smul_sub, h2, smul_add]
  simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, bracket]
  abel
private theorem norm_halfCommutatorSum_le (Z : Fin 4 → ComplexMatrix2) (ρ : ℝ)
    (hρ : ρ = ∑ j, ‖Z j‖) :
    ‖halfCommutatorSum Z‖ ≤ ρ ^ 2 / 2 := by
  rw [halfCommutatorSum_fin_four, norm_smul]
  have hb : ∀ i j, ‖Z i * Z j - Z j * Z i‖ ≤ 2 * ‖Z i‖ * ‖Z j‖ := fun i j =>
    norm_bracket_le_two_mul _ _
  have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hn]
  have hsum := norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
    (norm_add_le_of_le (hb 0 1) (hb 0 2)) (hb 0 3)) (hb 1 2)) (hb 1 3)) (hb 2 3)
  rw [hρ, Fin.sum_univ_four]
  nlinarith [sq_nonneg ‖Z 0‖, sq_nonneg ‖Z 1‖, sq_nonneg ‖Z 2‖, sq_nonneg ‖Z 3‖]
end FourExpConjugation
open FourExpConjugation in
theorem FourExpConjugation.secondOrderExpansion_holds
    (h : ExpProductExpansionAndConjugation) :
    FourExpConjugation.SecondOrderExpansion := by
  intro Z Y ϱ s W P hϱ hle hs hW hP
  have hρ : ϱ = ∑ j, ‖Z j‖ := hϱ
  have h0 : 0 ≤ ϱ := by
    rw [hρ]
    exact Finset.sum_nonneg fun j _ => norm_nonneg _
  set Z' : Fin 4 → ComplexMatrix2 := ![-Z 3, -Z 2, -Z 1, -Z 0] with hZ'
  set Q : ComplexMatrix2 := (List.ofFn fun j => matExp (Z' j)).prod with hQ
  have hϱ' : ϱ = ∑ j, operatorNorm (Z' j) := by
    rw [hρ]
    simp only [hZ', operatorNorm, Fin.sum_univ_four]
    simp
    ring
  have hs' : -s = ∑ j, Z' j := by
    rw [hs]
    simp only [hZ', Fin.sum_univ_four]
    simp
    abel
  have hW' : -W = halfCommutatorSum Z' := by
    rw [hW, halfCommutatorSum_fin_four, halfCommutatorSum_fin_four, ← smul_neg]
    congr 1
    simp only [hZ']
    simp
    abel
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, list_prod_ofFn_fin_four, list_prod_ofFn_fin_four]
    simp only [hZ']
    simp only [Matrix.cons_val]
    have e0 := matExp_mul_matExp_neg (Z 0)
    have e1 := matExp_mul_matExp_neg (Z 1)
    have e2 := matExp_mul_matExp_neg (Z 2)
    have e3 := matExp_mul_matExp_neg (Z 3)
    calc matExp (Z 0) * matExp (Z 1) * matExp (Z 2) * matExp (Z 3) *
          (matExp (-Z 3) * matExp (-Z 2) * matExp (-Z 1) * matExp (-Z 0))
        = matExp (Z 0) * (matExp (Z 1) * (matExp (Z 2) * (matExp (Z 3) * matExp (-Z 3)) *
            matExp (-Z 2)) * matExp (-Z 1)) * matExp (-Z 0) := by simp only [mul_assoc]
      _ = 1 := by rw [e3, mul_one, e2, mul_one, e1, mul_one, e0]
  have hinv : P⁻¹ = Q := Matrix.inv_eq_right_inv hPQ
  obtain ⟨-, -, a, b⟩ := h.1 4 Z ϱ s W P hϱ hs hW hP
  obtain ⟨-, -, c, d⟩ := h.1 4 Z' ϱ (-s) (-W) Q hϱ' hs' hW' hQ
  have hexp : Real.exp ϱ ≤ 3 := by
    have h1 : Real.exp ϱ ≤ Real.exp 1 := Real.exp_le_exp.mpr hle
    have h2 := Real.exp_one_lt_d9
    linarith
  have htail : 1 / 6 * ϱ ^ 3 * Real.exp ϱ ≤ ϱ ^ 3 := by
    have h3 : 0 ≤ ϱ ^ 3 := by positivity
    nlinarith
  set R : ComplexMatrix2 := P - 1 - s - (1 / 2 : ℂ) • s ^ 2 - W with hR
  set R' : ComplexMatrix2 := Q - 1 - -s - (1 / 2 : ℂ) • (-s) ^ 2 - -W with hR'
  have nR : ‖R‖ ≤ ϱ ^ 3 := (a.trans b).trans htail
  have nR' : ‖R'‖ ≤ ϱ ^ 3 := (c.trans d).trans htail
  set A : ComplexMatrix2 := (1 / 2 : ℂ) • s ^ 2 + W with hA
  set A' : ComplexMatrix2 := (1 / 2 : ℂ) • s ^ 2 - W with hA'
  have eP : P = 1 + s + A + R := by
    rw [hR, hA]
    abel
  have eQ : Q = 1 - s + A' + R' := by
    rw [hR', hA', even_two.neg_pow]
    abel
  have ns : ‖s‖ ≤ ϱ := by
    rw [hs, hρ]
    exact norm_sum_le _ _
  have nW : ‖W‖ ≤ ϱ ^ 2 / 2 := by
    rw [hW]
    exact norm_halfCommutatorSum_le Z ϱ hρ
  have nsq : ‖(1 / 2 : ℂ) • s ^ 2‖ ≤ ϱ ^ 2 / 2 := by
    rw [norm_smul, sq s]
    have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [hn]
    have h1 := norm_mul_le_of_le ns ns
    nlinarith
  have nA : ‖A‖ ≤ ϱ ^ 2 := by
    have := norm_add_le_of_le nsq nW
    linarith
  have nA' : ‖A'‖ ≤ ϱ ^ 2 := by
    have := norm_sub_le_of_le nsq nW
    linarith
  have nY := norm_nonneg Y
  have hmain := norm_cubic_remainder_le h0 hle s A A' R R' Y ns nA nA' nR nR'
  have hb1 : ‖bracket s Y‖ ≤ 2 * ϱ * ‖Y‖ := by
    have := norm_bracket_le_two_mul s Y
    nlinarith
  refine ⟨?_, hb1, ?_⟩
  · have hAd : conjugateBy P Y - Y - bracket s Y -
        ((1 / 2 : ℂ) • bracket s (bracket s Y) + bracket W Y) =
        (1 + s + A + R) * Y * (1 - s + A' + R') - Y - (s * Y - Y * s) -
          (A * Y + Y * A' - s * Y * s) := by
      rw [quadratic_terms_eq_brackets, ← eP, ← eQ, ← hinv]
      rfl
    show ‖_‖ ≤ _
    rw [hAd]
    refine hmain.trans ?_
    have e1 : 1 ≤ Real.exp 1 ^ 2 := one_le_pow₀ (by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith)
    have h3 : 0 ≤ ϱ ^ 3 * ‖Y‖ := by positivity
    nlinarith
  · have hb2 : ‖bracket s (bracket s Y)‖ ≤ 4 * ϱ ^ 2 * ‖Y‖ := by
      have h1 := norm_bracket_le_two_mul s (bracket s Y)
      have h2 := norm_nonneg (bracket s Y)
      have h3 : ‖s‖ * ‖bracket s Y‖ ≤ ϱ * (2 * ϱ * ‖Y‖) :=
        mul_le_mul ns hb1 h2 h0
      nlinarith
    have hb3 : ‖bracket W Y‖ ≤ ϱ ^ 2 * ‖Y‖ := by
      have h1 := norm_bracket_le_two_mul W Y
      have h2 : ‖W‖ * ‖Y‖ ≤ ϱ ^ 2 / 2 * ‖Y‖ := mul_le_mul_of_nonneg_right nW nY
      linarith
    have hb4 : ‖(1 / 2 : ℂ) • bracket s (bracket s Y)‖ ≤ 2 * ϱ ^ 2 * ‖Y‖ := by
      rw [norm_smul]
      have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      rw [hn]
      linarith
    have := norm_add_le_of_le hb4 hb3
    show ‖_‖ ≤ _
    linarith
end YangMills.Construction.Matrices.ComplexMatrix2
