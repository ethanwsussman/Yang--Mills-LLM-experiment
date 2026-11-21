import YangMills.Construction.InfiniteLattice.TraceOnTheGroupAndOneBondWeightProof
import YangMills.Construction.Matrices.ConjugationExpProducts
import YangMills.Construction.Matrices.ElementaryMatrixBoundsProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2.ConjugationExp
theorem inv_eq_star_of_mem_unitary {h : ComplexMatrix2} (hh : h ∈ unitary ComplexMatrix2) :
    h⁻¹ = star h :=
  Matrix.inv_eq_right_inv (Unitary.mul_star_self_of_mem hh)
theorem isUnit_of_mem_unitary {h : ComplexMatrix2} (hh : h ∈ unitary ComplexMatrix2) : IsUnit h :=
  ⟨⟨h, star h, Unitary.mul_star_self_of_mem hh, Unitary.star_mul_self_of_mem hh⟩, rfl⟩
theorem inv_mem_unitary_of_mem {h : ComplexMatrix2} (hh : h ∈ unitary ComplexMatrix2) :
    h⁻¹ ∈ unitary ComplexMatrix2 := by
  rw [inv_eq_star_of_mem_unitary hh]
  exact Unitary.star_mem hh
theorem mul_inv_eq_one_of_mem_unitary {h : ComplexMatrix2} (hh : h ∈ unitary ComplexMatrix2) :
    h * h⁻¹ = 1 := by
  rw [inv_eq_star_of_mem_unitary hh]
  exact Unitary.mul_star_self_of_mem hh
theorem operatorNorm_conjugateBy {h : ComplexMatrix2} (hh : h ∈ unitary ComplexMatrix2)
    (Y : ComplexMatrix2) : operatorNorm (conjugateBy h Y) = operatorNorm Y := by
  simp only [operatorNorm, conjugateBy]
  rw [CStarRing.norm_mul_mem_unitary _ (inv_mem_unitary_of_mem hh),
    CStarRing.norm_mem_unitary_mul _ hh]
theorem fullTrace_conjugateBy_eq_zero {h : ComplexMatrix2} (hh : h ∈ unitary ComplexMatrix2)
    {Y : ComplexMatrix2} (hY : fullTrace Y = 0) : fullTrace (conjugateBy h Y) = 0 := by
  have e : h⁻¹ * h = 1 := by
    rw [inv_eq_star_of_mem_unitary hh]
    exact Unitary.star_mul_self_of_mem hh
  simp only [fullTrace, conjugateBy] at hY ⊢
  rw [Matrix.trace_mul_comm, ← mul_assoc, e, one_mul, hY]
theorem conjugateBy_mem_hermitianTraceless {h : ComplexMatrix2} (hh : h ∈ unitary ComplexMatrix2)
    {Y : ComplexMatrix2} (hY : Y ∈ hermitianTraceless) :
    conjugateBy h Y ∈ hermitianTraceless := by
  refine ⟨?_, fullTrace_conjugateBy_eq_zero hh hY.2⟩
  have hs : Y.conjTranspose = Y := hY.1.symm
  have hi : h⁻¹ = h.conjTranspose := inv_eq_star_of_mem_unitary hh
  simp only [conjugateBy, hi, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hs,
    mul_assoc]
def iPauliX : ComplexMatrix2 := !![0, Complex.I; Complex.I, 0]
def iPauliY : ComplexMatrix2 := !![0, 1; -1, 0]
def iPauliZ : ComplexMatrix2 := !![Complex.I, 0; 0, -Complex.I]
theorem star_iPauliX : star iPauliX = !![0, -Complex.I; -Complex.I, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [iPauliX, Matrix.star_apply]
theorem star_iPauliY : star iPauliY = !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [iPauliY, Matrix.star_apply]
theorem star_iPauliZ : star iPauliZ = !![-Complex.I, 0; 0, Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [iPauliZ, Matrix.star_apply]
theorem iPauliX_mem_specialUnitary : iPauliX ∈ specialUnitary := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, star_iPauliX]
  refine ⟨?_, ?_⟩
  · simp [iPauliX, Matrix.one_fin_two]
  · simp [iPauliX, Matrix.det_fin_two]
theorem iPauliY_mem_specialUnitary : iPauliY ∈ specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.SUTwoTrace.symplecticUnit_mem <;> assumption
theorem iPauliZ_mem_specialUnitary : iPauliZ ∈ specialUnitary := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, star_iPauliZ]
  refine ⟨?_, ?_⟩
  · simp [iPauliZ, Matrix.one_fin_two]
  · simp [iPauliZ, Matrix.det_fin_two]
theorem mem_unitary_of_mem_specialUnitary {h : ComplexMatrix2} (hh : h ∈ specialUnitary) :
    h ∈ unitary ComplexMatrix2 :=
  Matrix.specialUnitaryGroup_le_unitaryGroup hh
theorem sum_conjugateBy_iPauli_eq_zero {Y : ComplexMatrix2} (hY : Y ∈ traceless) :
    conjugateBy 1 Y + conjugateBy iPauliX Y + conjugateBy iPauliY Y + conjugateBy iPauliZ Y = 0 := by
  have t : Y 0 0 + Y 1 1 = 0 := by
    have : fullTrace Y = 0 := hY
    simpa [fullTrace, Matrix.trace_fin_two] using this
  have e₀ : conjugateBy 1 Y = Y := by simp [conjugateBy]
  rw [e₀]
  simp only [conjugateBy, inv_eq_star_of_mem_unitary (mem_unitary_of_mem_specialUnitary iPauliX_mem_specialUnitary),
    inv_eq_star_of_mem_unitary (mem_unitary_of_mem_specialUnitary iPauliY_mem_specialUnitary),
    inv_eq_star_of_mem_unitary (mem_unitary_of_mem_specialUnitary iPauliZ_mem_specialUnitary),
    star_iPauliX, star_iPauliY, star_iPauliZ]
  rw [Matrix.eta_fin_two Y]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iPauliX, iPauliY, iPauliZ] <;>
    ring_nf <;> simp [Complex.I_sq] <;>
    first
      | linear_combination t
      | linear_combination (2 : ℂ) * t
theorem matExp_I_smul_mem_unitary {Y : ComplexMatrix2} (hY : Y ∈ hermitianTraceless) :
    matExp (Complex.I • Y) ∈ unitary ComplexMatrix2 := by
  have hs : Y.conjTranspose = Y := hY.1.symm
  have e : star (matExp (Complex.I • Y)) = (matExp (Complex.I • Y))⁻¹ := by
    rw [← Matrix.exp_neg]
    show (matExp (Complex.I • Y)).conjTranspose = _
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hs]
    simp
  have hu : IsUnit (matExp (Complex.I • Y)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
  · rw [e]
    exact Matrix.nonsing_inv_mul _ hu
  · rw [e]
    exact Matrix.mul_nonsing_inv _ hu
theorem operatorNorm_I_smul (A : ComplexMatrix2) :
    operatorNorm (Complex.I • A) = operatorNorm A := by
  simp [operatorNorm, norm_smul]
theorem real_exp_sub_one_le_two_mul {x : ℝ} (h₀ : 0 ≤ x) (h₁ : x ≤ 1) :
    Real.exp x - 1 ≤ 2 * x := by
  have h := Real.abs_exp_sub_one_le (x := x) (by rw [abs_of_nonneg h₀]; exact h₁)
  rw [abs_of_nonneg h₀] at h
  exact (le_abs_self _).trans h
theorem add_operatorNorm_mul_matExp_le
    (hb : ∀ W Z : ComplexMatrix2,
      operatorNorm (W * matExp Z - 1) ≤ (1 + operatorNorm (W - 1)) * Real.exp (operatorNorm Z) - 1)
    {W Z : ComplexMatrix2} {s r : ℝ} (hW : 1 + operatorNorm (W - 1) ≤ Real.exp s)
    (hZ : operatorNorm Z ≤ r) :
    1 + operatorNorm (W * matExp Z - 1) ≤ Real.exp (s + r) := by
  have h := hb W Z
  have h₁ : Real.exp (operatorNorm Z) ≤ Real.exp r := Real.exp_le_exp.mpr hZ
  have h₂ : (1 + operatorNorm (W - 1)) * Real.exp (operatorNorm Z) ≤ Real.exp s * Real.exp r :=
    mul_le_mul hW h₁ (Real.exp_pos _).le (Real.exp_pos _).le
  rw [Real.exp_add]
  linarith
theorem add_operatorNorm_matExp_sub_one_le
    (hb : ∀ W Z : ComplexMatrix2,
      operatorNorm (W * matExp Z - 1) ≤ (1 + operatorNorm (W - 1)) * Real.exp (operatorNorm Z) - 1)
    {Z : ComplexMatrix2} {r : ℝ} (hZ : operatorNorm Z ≤ r) :
    1 + operatorNorm (matExp Z - 1) ≤ Real.exp r := by
  have h₀ : 1 + operatorNorm ((1 : ComplexMatrix2) - 1) ≤ Real.exp 0 := by simp
  have h := add_operatorNorm_mul_matExp_le hb h₀ hZ
  simpa using h
theorem operatorNorm_triple_product_expansion (a b c u v w : ComplexMatrix2) :
    operatorNorm ((1 + u) * (1 + v) * (1 + w) - 1 - (a + b + c)) ≤
      operatorNorm (u - a) + operatorNorm (v - b) + operatorNorm (w - c) +
        operatorNorm u * operatorNorm v + operatorNorm u * operatorNorm w +
        operatorNorm v * operatorNorm w + operatorNorm u * operatorNorm v * operatorNorm w := by
  have e : (1 + u) * (1 + v) * (1 + w) - 1 - (a + b + c) =
      (u - a) + (v - b) + (w - c) + u * v + u * w + v * w + u * v * w := by
    noncomm_ring
  rw [e]
  simp only [operatorNorm]
  have n₁ : ‖u * v‖ ≤ ‖u‖ * ‖v‖ := norm_mul_le _ _
  have n₂ : ‖u * w‖ ≤ ‖u‖ * ‖w‖ := norm_mul_le _ _
  have n₃ : ‖v * w‖ ≤ ‖v‖ * ‖w‖ := norm_mul_le _ _
  have n₄ : ‖u * v * w‖ ≤ ‖u‖ * ‖v‖ * ‖w‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right n₁ (norm_nonneg _))
  have s₁ := norm_add_le ((u - a) + (v - b) + (w - c) + u * v + u * w + v * w) (u * v * w)
  have s₂ := norm_add_le ((u - a) + (v - b) + (w - c) + u * v + u * w) (v * w)
  have s₃ := norm_add_le ((u - a) + (v - b) + (w - c) + u * v) (u * w)
  have s₄ := norm_add_le ((u - a) + (v - b) + (w - c)) (u * v)
  have s₅ := norm_add_le ((u - a) + (v - b)) (w - c)
  have s₆ := norm_add_le (u - a) (v - b)
  linarith
theorem second_order_arithmetic {q s x y z : ℝ} (hq₀ : 0 ≤ q) (hq : q ≤ 1 / 12) (hs₀ : 0 ≤ s)
    (hs : s ≤ 13 / 12 * q) (hy₀ : 0 ≤ y) (hz₀ : 0 ≤ z) (hx : x ≤ s) (hy : y ≤ s)
    (hz : z ≤ s) :
    s * q + s * q + s * q + x * y + x * z + y * z + x * y * z ≤ 9 * q ^ 2 := by
  have hsq : s * q ≤ 13 / 12 * q ^ 2 := by nlinarith
  have hss : s * s ≤ 169 / 144 * q ^ 2 := by nlinarith
  have hxy : x * y ≤ s * s := mul_le_mul hx hy hy₀ hs₀
  have hxz : x * z ≤ s * s := mul_le_mul hx hz hz₀ hs₀
  have hyz : y * z ≤ s * s := mul_le_mul hy hz hz₀ hs₀
  have hsm : s ≤ 1 := by nlinarith
  have hxyz : x * y * z ≤ s * s * 1 :=
    mul_le_mul hxy (hz.trans hsm) hz₀ (mul_nonneg hs₀ hs₀)
  nlinarith [sq_nonneg q]
theorem operatorNorm_matExp_sub_one_sub_le
    (hb : ∀ (Z Z' : ComplexMatrix2) (r : ℝ), max (operatorNorm Z) (operatorNorm Z') ≤ r →
      operatorNorm (matExp Z - matExp Z' - (Z - Z')) ≤ (Real.exp r - 1) * operatorNorm (Z - Z'))
    {Z : ComplexMatrix2} {q : ℝ} (hZ : operatorNorm Z ≤ q) :
    operatorNorm (matExp Z - 1 - Z) ≤ (Real.exp q - 1) * q := by
  have hq₀ : 0 ≤ q := (norm_nonneg _).trans hZ
  have h := hb Z 0 q (max_le hZ (by simpa [operatorNorm] using hq₀))
  have e₀ : matExp (0 : ComplexMatrix2) = 1 := NormedSpace.exp_zero
  rw [e₀, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left hZ (by
    have := Real.add_one_le_exp q
    linarith))
theorem logSeries_one : logSeries (1 : ComplexMatrix2) = 0 := by
  simp [logSeries]
theorem matExp_I_smul_mem_specialUnitary
    (hd : ∀ Z : ComplexMatrix2, (matExp Z).det = Complex.exp (fullTrace Z)) {Y : ComplexMatrix2}
    (hY : Y ∈ hermitianTraceless) : matExp (Complex.I • Y) ∈ specialUnitary := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.ElementaryBounds.matExp_I_smul_mem <;> assumption
theorem operatorNorm_conjugateBy_matExp_sub_le
    (hb : ∀ Z : ComplexMatrix2, operatorNorm (matExp Z - 1) ≤ Real.exp (operatorNorm Z) - 1)
    {A J : ComplexMatrix2} {q : ℝ} (hA : A ∈ hermitianTraceless) (hAq : operatorNorm A ≤ q)
    (hq : q ≤ 1) :
    operatorNorm (conjugateBy (matExp (Complex.I • A)) J - J) ≤ 4 * q * operatorNorm J := by
  have hq₀ : 0 ≤ q := (norm_nonneg _).trans hAq
  set V := matExp (Complex.I • A) with hV
  have hu : V ∈ unitary ComplexMatrix2 := matExp_I_smul_mem_unitary hA
  have e : conjugateBy V J - J = (V * J - J * V) * V⁻¹ := by
    have h₁ : J = J * V * V⁻¹ := by rw [mul_assoc, mul_inv_eq_one_of_mem_unitary hu, mul_one]
    calc conjugateBy V J - J = V * J * V⁻¹ - J * V * V⁻¹ := by rw [← h₁]; rfl
      _ = (V * J - J * V) * V⁻¹ := by rw [sub_mul]
  have e₂ : V * J - J * V = (V - 1) * J - J * (V - 1) := by noncomm_ring
  have hV₁ : operatorNorm (V - 1) ≤ 2 * q := by
    have h₁ := hb (Complex.I • A)
    rw [operatorNorm_I_smul] at h₁
    have h₂ : Real.exp (operatorNorm A) ≤ Real.exp q := Real.exp_le_exp.mpr hAq
    have h₃ := real_exp_sub_one_le_two_mul hq₀ hq
    linarith
  have hn : operatorNorm ((V - 1) * J - J * (V - 1)) ≤
      2 * operatorNorm (V - 1) * operatorNorm J := by
    simp only [operatorNorm]
    have n₁ : ‖(V - 1) * J‖ ≤ ‖V - 1‖ * ‖J‖ := norm_mul_le _ _
    have n₂ : ‖J * (V - 1)‖ ≤ ‖J‖ * ‖V - 1‖ := norm_mul_le _ _
    have n₃ := norm_sub_le ((V - 1) * J) (J * (V - 1))
    linarith
  have hJ : 0 ≤ operatorNorm J := norm_nonneg _
  rw [e]
  have hm : operatorNorm ((V * J - J * V) * V⁻¹) = operatorNorm (V * J - J * V) :=
    CStarRing.norm_mul_mem_unitary _ (inv_mem_unitary_of_mem hu)
  rw [hm, e₂]
  refine hn.trans ?_
  have := mul_le_mul_of_nonneg_right hV₁ hJ
  nlinarith
theorem operatorNorm_four_matExp_product_sub_one_le
    (hb : ∀ W Z : ComplexMatrix2,
      operatorNorm (W * matExp Z - 1) ≤ (1 + operatorNorm (W - 1)) * Real.exp (operatorNorm Z) - 1)
    {Z₁ Z₂ Z₃ Z₄ : ComplexMatrix2} {r : ℝ} (h₁ : operatorNorm Z₁ ≤ r) (h₂ : operatorNorm Z₂ ≤ r)
    (h₃ : operatorNorm Z₃ ≤ r) (h₄ : operatorNorm Z₄ ≤ r) (hr : 4 * r ≤ 1) :
    operatorNorm (matExp Z₁ * matExp Z₂ * matExp Z₃ * matExp Z₄ - 1) ≤ 8 * r := by
  have hr₀ : 0 ≤ r := (norm_nonneg _).trans h₁
  have p := add_operatorNorm_mul_matExp_le hb (add_operatorNorm_mul_matExp_le hb
    (add_operatorNorm_mul_matExp_le hb (add_operatorNorm_matExp_sub_one_le hb h₁) h₂) h₃) h₄
  have e : r + r + r + r = 4 * r := by ring
  rw [e] at p
  have := real_exp_sub_one_le_two_mul (by linarith : 0 ≤ 4 * r) hr
  linarith
theorem exists_log_three_matExp_product (hE : ExpLogEstimates)
    {A B C : ComplexMatrix2} {q : ℝ} (hA : A ∈ hermitianTraceless) (hB : B ∈ hermitianTraceless)
    (hC : C ∈ hermitianTraceless) (nA : operatorNorm A ≤ q) (nB : operatorNorm B ≤ q)
    (nC : operatorNorm C ≤ q) (hq : q ≤ 1 / 12) :
    ∃ Y ∈ hermitianTraceless, matExp (Complex.I • Y) =
        matExp (Complex.I • A) * matExp (Complex.I • B) * matExp (Complex.I • C) ∧
      operatorNorm (Y - (A + B + C)) ≤ 81 * q ^ 2 := by
  obtain ⟨hb₁, hb₂, hb₃, -, -, hd, -, hun, hlip, -⟩ := hE
  have hq₀ : 0 ≤ q := (norm_nonneg _).trans nA
  set a := Complex.I • A with ha
  set b := Complex.I • B with hb
  set c := Complex.I • C with hc
  have na : operatorNorm a ≤ q := by rw [ha, operatorNorm_I_smul]; exact nA
  have nb : operatorNorm b ≤ q := by rw [hb, operatorNorm_I_smul]; exact nB
  have nc : operatorNorm c ≤ q := by rw [hc, operatorNorm_I_smul]; exact nC
  set P := matExp a * matExp b * matExp c with hP
  have hPG : P ∈ specialUnitary :=
    mul_mem (mul_mem (matExp_I_smul_mem_specialUnitary hd hA)
      (matExp_I_smul_mem_specialUnitary hd hB)) (matExp_I_smul_mem_specialUnitary hd hC)
  have hPdet : P.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp hPG).2
  have hP₁ : operatorNorm (P - 1) ≤ 6 * q := by
    have p := add_operatorNorm_mul_matExp_le hb₃
      (add_operatorNorm_mul_matExp_le hb₃ (add_operatorNorm_matExp_sub_one_le hb₃ na) nb) nc
    have e : q + q + q = 3 * q := by ring
    rw [e] at p
    have := real_exp_sub_one_le_two_mul (by linarith : 0 ≤ 3 * q) (by linarith)
    linarith
  have hlt : operatorNorm (P - 1) < 1 := by linarith
  obtain ⟨H, -, hlog, -, hexp, -, hdet⟩ := hun P (mem_unitary_of_mem_specialUnitary hPG) hlt
  have hH : H ∈ hermitianTraceless := (hdet hPdet).2.1
  refine ⟨H, hH, hexp, ?_⟩
  have h1 : operatorNorm ((1 : ComplexMatrix2) - 1) ≤ 6 * q := by
    simpa [operatorNorm] using hq₀
  have hL := (hlip (6 * q) P 1 (by linarith) (by linarith) hP₁ h1).2.2.1
  rw [logSeries_one, sub_zero] at hL
  have hL' : operatorNorm (logSeries P - (P - 1)) ≤ 72 * q ^ 2 := by
    refine hL.trans ?_
    have hd₁ : 6 * q / (1 - 6 * q) ≤ 12 * q := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have h₀ : 0 ≤ operatorNorm (P - 1) := norm_nonneg _
    calc 6 * q / (1 - 6 * q) * operatorNorm (P - 1) ≤ 12 * q * (6 * q) :=
          mul_le_mul hd₁ hP₁ h₀ (by linarith)
      _ = 72 * q ^ 2 := by ring
  set s := Real.exp q - 1 with hs
  have hs₀ : 0 ≤ s := by
    have := Real.add_one_le_exp q
    rw [hs]
    linarith
  have hs₁ : s ≤ 13 / 12 * q := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := q) (by rw [abs_of_nonneg hq₀]; linarith)
    have h' := (le_abs_self _).trans h
    rw [hs]
    nlinarith
  have nu : ∀ {Z : ComplexMatrix2}, operatorNorm Z ≤ q → operatorNorm (matExp Z - 1) ≤ s := by
    intro Z hZ
    have h₁ := hb₁ Z
    have h₂ : Real.exp (operatorNorm Z) ≤ Real.exp q := Real.exp_le_exp.mpr hZ
    exact h₁.2.trans (by rw [hs]; linarith)
  have nv : ∀ {Z : ComplexMatrix2}, operatorNorm Z ≤ q →
      operatorNorm (matExp Z - 1 - Z) ≤ s * q := by
    intro Z hZ
    exact operatorNorm_matExp_sub_one_sub_le (fun Z Z' r hr => (hb₂ Z Z' r hr).2) hZ
  have hprod : operatorNorm (P - 1 - (a + b + c)) ≤ 9 * q ^ 2 := by
    have e : P = (1 + (matExp a - 1)) * (1 + (matExp b - 1)) * (1 + (matExp c - 1)) := by
      simp [hP]
    have h := operatorNorm_triple_product_expansion a b c (matExp a - 1) (matExp b - 1)
      (matExp c - 1)
    rw [← e] at h
    have hnum := second_order_arithmetic hq₀ hq hs₀ hs₁ (norm_nonneg (matExp b - 1))
      (norm_nonneg (matExp c - 1)) (nu na) (nu nb) (nu nc)
    have v₁ := nv na
    have v₂ := nv nb
    have v₃ := nv nc
    linarith
  have e₁ : Complex.I • H = logSeries P := hlog.symm
  have hfin : operatorNorm (H - (A + B + C)) = operatorNorm (logSeries P - (a + b + c)) := by
    rw [← operatorNorm_I_smul (H - (A + B + C)), smul_sub, e₁]
    simp only [smul_add, ha, hb, hc]
  rw [hfin]
  have e₂ : logSeries P - (a + b + c) = (logSeries P - (P - 1)) + (P - 1 - (a + b + c)) := by abel
  rw [e₂]
  have := norm_add_le (logSeries P - (P - 1)) (P - 1 - (a + b + c))
  simp only [operatorNorm] at hL' hprod ⊢
  linarith
theorem conjugationExpProductBounds_of_expLogEstimates (hE : ExpLogEstimates) :
    ConjugationExpProductBounds := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨![1, iPauliX, iPauliY, iPauliZ], ?_, ?_⟩
    · intro k
      fin_cases k
      · exact one_mem _
      · exact iPauliX_mem_specialUnitary
      · exact iPauliY_mem_specialUnitary
      · exact iPauliZ_mem_specialUnitary
    · intro Y hY
      have h := sum_conjugateBy_iPauli_eq_zero hY
      simpa [Fin.sum_univ_four] using h
  · intro h hh Y
    have hu := mem_unitary_of_mem_specialUnitary hh
    refine ⟨operatorNorm_conjugateBy hu Y, ?_, fun hY => fullTrace_conjugateBy_eq_zero hu hY,
      fun hY => conjugateBy_mem_hermitianTraceless hu hY⟩
    exact Matrix.exp_conj h Y (isUnit_of_mem_unitary hu)
  · intro Y hY
    exact matExp_I_smul_mem_specialUnitary hE.2.2.2.2.2.1 hY
  · intro A B C q hA hB hC nA nB nC hq
    exact exists_log_three_matExp_product hE hA hB hC nA nB nC hq
  · intro A J q hA hAq hq
    exact operatorNorm_conjugateBy_matExp_sub_le (fun Z => (hE.1 Z).2) hA hAq hq
  · intro Z₁ Z₂ Z₃ Z₄ r h₁ h₂ h₃ h₄ hr
    exact operatorNorm_four_matExp_product_sub_one_le hE.2.2.1 h₁ h₂ h₃ h₄ hr
end YangMills.Construction.Matrices.ComplexMatrix2.ConjugationExp
end
