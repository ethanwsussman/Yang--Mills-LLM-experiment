import YangMills.Construction.Analysis.PolarCoordinatesLowDim
import YangMills.Construction.Matrices.HaarExpChartDensity
import YangMills.Construction.Matrices.LieAlgebraNormAdjointIsometry
import YangMills.Construction.Matrices.WeylIntegrationOnG
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices YangMills.Construction.Matrices.ComplexMatrix2 Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace SpinHarmonics
namespace WeylIntegration
def lieCoords : LieElement →ₗ[ℝ] ℝ × ℂ where
  toFun Y := ((Y.toMatrix 0 0).re, Y.toMatrix 0 1)
  map_add' A B := by
    have : (A + B).toMatrix = A.toMatrix + B.toMatrix := rfl
    simp [this]
  map_smul' c A := by
    have : (c • A).toMatrix = c • A.toMatrix := rfl
    simp [this]
theorem entries_of_lieElement (Y : LieElement) :
    Y.toMatrix 1 1 = -Y.toMatrix 0 0 ∧ Y.toMatrix 1 0 = star (Y.toMatrix 0 1) ∧
      Y.toMatrix 0 0 = ((Y.toMatrix 0 0).re : ℂ) := by
  have ht : fullTrace Y.toMatrix = 0 := Y.2.2
  have h1 : Y.toMatrix 1 1 = -Y.toMatrix 0 0 := by
    simp only [fullTrace, Matrix.trace_fin_two] at ht
    linear_combination ht
  refine ⟨h1, LieElement.toMatrix_entry_swap Y 0 1, ?_⟩
  have h2 := LieElement.toMatrix_entry_swap Y 0 0
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h2
    simp at this ⊢
    linarith
theorem lieCoords_bijective : Function.Bijective lieCoords := by
  constructor
  · intro A B h
    have h1 : (A.toMatrix 0 0).re = (B.toMatrix 0 0).re := congrArg Prod.fst h
    have h2 : A.toMatrix 0 1 = B.toMatrix 0 1 := congrArg Prod.snd h
    obtain ⟨a1, a2, a3⟩ := entries_of_lieElement A
    obtain ⟨b1, b2, b3⟩ := entries_of_lieElement B
    have h0 : A.toMatrix 0 0 = B.toMatrix 0 0 := by rw [a3, b3, h1]
    apply Subtype.ext
    change A.toMatrix = B.toMatrix
    ext i j
    fin_cases i <;> fin_cases j
    · exact h0
    · exact h2
    · simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue]; rw [a2, b2, h2]
    · simp only [Fin.mk_one, Fin.isValue]; rw [a1, b1, h0]
  · rintro ⟨a, z⟩
    have hm : (!![(a : ℂ), z; star z, -(a : ℂ)] : ComplexMatrix2) ∈ hermitianTraceless := by
      refine ⟨?_, ?_⟩
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
      · simp [fullTrace, Matrix.trace_fin_two]
    refine ⟨⟨_, hm⟩, ?_⟩
    simp [lieCoords, LieElement.toMatrix]
theorem finrank_lieElement : Module.finrank ℝ LieElement = 3 := by
  have e := (LinearEquiv.ofBijective lieCoords lieCoords_bijective).finrank_eq
  rw [e, Module.finrank_prod, Module.finrank_self, Complex.finrank_real_complex]
def diagPair (e : ℝ) : ComplexMatrix2 := !![(e : ℂ), 0; 0, -(e : ℂ)]
theorem exists_conj_diagPair {Y : ComplexMatrix2} (hY : Y ∈ hermitianTraceless) :
    ∃ (h : specialUnitary) (e : ℝ),
      Y = (h : ComplexMatrix2) * diagPair e * star (h : ComplexMatrix2) := by
  have hH : Y.IsHermitian := hY.1.symm
  set W : ComplexMatrix2 := (hH.eigenvectorUnitary : ComplexMatrix2) with hW
  have hWs : W * star W = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hspec : Y = W * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) * star W := by
    have := hH.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, Function.comp_def] using this
  have htr : hH.eigenvalues 0 + hH.eigenvalues 1 = 0 := by
    have h1 := hH.trace_eq_sum_eigenvalues
    have h2 : Matrix.trace Y = 0 := hY.2
    rw [h2] at h1
    simp only [Fin.sum_univ_two] at h1
    have h3 := congrArg Complex.re h1
    simp at h3
    linarith
  have hdet : star W.det * W.det = 1 := by
    have := congrArg Matrix.det hWs
    rw [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose] at this
    rw [mul_comm]
    exact this
  have hd0 : W.det ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (W.det)⁻¹ (n := 2) (by norm_num)
  have hzz : star z * z = 1 := by
    have h1 : star (z ^ 2) * z ^ 2 = 1 := by
      rw [hz, star_inv₀]
      field_simp
      have : star W.det ≠ 0 := by
        intro h0
        rw [h0] at hdet
        simp at hdet
      rw [mul_comm] at hdet
      field_simp
      simpa [mul_comm] using hdet.symm
    have h2 : (star z * z) ^ 2 = 1 := by
      rw [mul_pow, ← star_pow]
      exact h1
    have h3 : 0 ≤ (star z * z).re ∧ (star z * z).im = 0 := by
      have : star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
        rw [mul_comm]
        exact Complex.mul_conj z
      rw [this]
      simp [Complex.normSq_nonneg]
    have h4 : star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
      rw [mul_comm]
      exact Complex.mul_conj z
    rw [h4] at h2 ⊢
    have h5 : (Complex.normSq z) ^ 2 = 1 := by exact_mod_cast h2
    have h6 : Complex.normSq z = 1 := by
      have := Complex.normSq_nonneg z
      nlinarith
    rw [h6]
    simp
  have hmem : z • W ∈ specialUnitary := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, star_smul, Matrix.smul_mul, Matrix.mul_smul, hWs, smul_smul]
      have hzz' : z * (starRingEnd ℂ) z = 1 := by rw [mul_comm]; exact hzz
      simp [hzz']
    · rw [Matrix.det_smul, Fintype.card_fin, hz]
      exact inv_mul_cancel₀ hd0
  refine ⟨⟨_, hmem⟩, hH.eigenvalues 0, ?_⟩
  have hD : Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) = diagPair (hH.eigenvalues 0) := by
    have h1 : hH.eigenvalues 1 = -hH.eigenvalues 0 := by linarith
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagPair, h1]
  show Y = (z • W) * diagPair (hH.eigenvalues 0) * star (z • W)
  simp only [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← hD, ← hspec, hzz, one_smul]
theorem sincAngle_mul_self (a : ℝ) : sincAngle a * a = Real.sin a := by
  by_cases h : a = 0
  · simp [sincAngle, h]
  · simp only [sincAngle, h, if_false]
    field_simp
theorem continuous_sincAngle : Continuous sincAngle := by
  have h : sincAngle = Real.sinc := by
    funext a
    by_cases h : a = 0
    · simp [sincAngle, h]
    · simp [sincAngle, h, Real.sinc_of_ne_zero h, div_eq_inv_mul]
  rw [h]
  exact Real.continuous_sinc
theorem star_mul_self_specialUnitary (h : specialUnitary) :
    star (h : ComplexMatrix2) * (h : ComplexMatrix2) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp h.2).1
theorem mul_star_self_specialUnitary (h : specialUnitary) :
    (h : ComplexMatrix2) * star (h : ComplexMatrix2) = 1 :=
  Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp h.2).1
theorem matExp_eq_conj_diagPhase (hLog : UnitaryLogConjugationProperties) {Y : ComplexMatrix2}
    (hY : Y ∈ hermitianTraceless) :
    ∃ (h : specialUnitary) (e : ℝ), (e = operatorNorm Y ∨ e = -operatorNorm Y) ∧
      matExp (Complex.I • Y) = (h : ComplexMatrix2) * diagPhaseMatrix e * star (h : ComplexMatrix2) := by
  obtain ⟨hsq, hexp, -⟩ := hLog.1 Y hY
  obtain ⟨h, e, hh⟩ := exists_conj_diagPair hY
  have hDD : diagPair e * diagPair e = ((e : ℂ) ^ 2) • (1 : ComplexMatrix2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagPair, Matrix.mul_apply, Fin.sum_univ_two, sq]
  have hYY : Y ^ 2 = ((e : ℂ) ^ 2) • (1 : ComplexMatrix2) := by
    have h₁ : Y ^ 2 = (h : ComplexMatrix2) * (diagPair e * diagPair e) * star (h : ComplexMatrix2) := by
      rw [sq]
      nth_rewrite 1 [hh]
      nth_rewrite 1 [hh]
      calc (h : ComplexMatrix2) * diagPair e * star (h : ComplexMatrix2) *
            ((h : ComplexMatrix2) * diagPair e * star (h : ComplexMatrix2))
          = (h : ComplexMatrix2) * diagPair e * (star (h : ComplexMatrix2) * (h : ComplexMatrix2)) *
              diagPair e * star (h : ComplexMatrix2) := by
            simp only [mul_assoc]
        _ = _ := by rw [star_mul_self_specialUnitary]; simp only [mul_one, mul_assoc]
    rw [h₁, hDD, Matrix.mul_smul, Matrix.smul_mul, mul_one, mul_star_self_specialUnitary]
  have hee : e ^ 2 = operatorNorm Y ^ 2 := by
    have h₁ := congrFun (congrFun (hsq.symm.trans hYY) 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h₁
    exact_mod_cast h₁.symm
  have hor : e = operatorNorm Y ∨ e = -operatorNorm Y := sq_eq_sq_iff_eq_or_eq_neg.mp hee
  refine ⟨h, e, hor, ?_⟩
  have hcos : Real.cos (operatorNorm Y) = Real.cos e := by
    rcases hor with r | r <;> rw [r]
    simp
  have hsin : sincAngle (operatorNorm Y) * e = Real.sin e := by
    rcases hor with r | r <;> rw [r]
    · exact sincAngle_mul_self _
    · rw [mul_neg, Real.sin_neg, sincAngle_mul_self]
  have hsinC : (sincAngle (operatorNorm Y) : ℂ) * (e : ℂ) = Complex.sin e := by
    rw [← Complex.ofReal_sin, ← hsin]
    push_cast
    rfl
  have hmid : (Real.cos (operatorNorm Y) : ℂ) • (1 : ComplexMatrix2) +
      (Complex.I * (sincAngle (operatorNorm Y) : ℂ)) • diagPair e = diagPhaseMatrix e := by
    rw [hcos]
    have e₁ : Complex.exp (Complex.I * e) = Complex.cos e + Complex.I * Complex.sin e := by
      rw [mul_comm, Complex.exp_mul_I]
      ring
    have e₂ : Complex.exp (-(Complex.I * e)) = Complex.cos e - Complex.I * Complex.sin e := by
      rw [← mul_neg, mul_comm, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      ring
    ext i j
    fin_cases i <;> fin_cases j
    · simp [diagPair, diagPhaseMatrix, e₁]
      rw [mul_assoc, hsinC]
    · simp [diagPair, diagPhaseMatrix]
    · simp [diagPair, diagPhaseMatrix]
    · simp [diagPair, diagPhaseMatrix, e₂]
      rw [mul_assoc, hsinC, sub_eq_add_neg]
  rw [hexp, ← hmid]
  nth_rewrite 3 [hh]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one,
    mul_star_self_specialUnitary, Matrix.mul_smul, Matrix.smul_mul]
def quarterRotation : specialUnitary :=
  ⟨!![0, 1; -1, 0], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, by simp [Matrix.det_fin_two]⟩
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]⟩
theorem diagPhase_neg (φ : ℝ) :
    diagPhase (-φ) = quarterRotation * diagPhase φ * quarterRotation⁻¹ := by
  apply Subtype.ext
  show diagPhaseMatrix (-φ) = (!![0, 1; -1, 0] : ComplexMatrix2) * diagPhaseMatrix φ *
    star (!![0, 1; -1, 0] : ComplexMatrix2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagPhaseMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]
theorem coe_expChart (hLog : UnitaryLogConjugationProperties) (Y : LieElement) :
    (expChart Y : ComplexMatrix2) = matExp (Complex.I • Y.toMatrix) := by
  have hm : matExp (Complex.I • Y.toMatrix) ∈ specialUnitary := (hLog.1 Y.toMatrix Y.2).2.2
  simp [expChart, hm]
theorem conjInvariant_expChart (hLog : UnitaryLogConjugationProperties) {F : specialUnitary → ℂ}
    (hF : IsConjInvariant F) (Y : LieElement) :
    F (expChart Y) = F (diagPhase (operatorNorm Y.toMatrix)) := by
  obtain ⟨h, e, hor, he⟩ := matExp_eq_conj_diagPhase hLog Y.2
  have h₁ : expChart Y = h * diagPhase e * h⁻¹ := by
    apply Subtype.ext
    rw [coe_expChart hLog]
    exact he
  rw [h₁, hF]
  rcases hor with r | r
  · rw [r]
    rfl
  · rw [r, diagPhase_neg, hF]
    rfl
theorem radialIntegral_complex
    (hr : Analysis.PolarCoordinates.RadialIntegralFormula LieElement 3 (4 * Real.pi))
    (Φ : ℝ → ℂ) (hI : Integrable fun Y : LieElement => Φ ‖Y‖) :
    ∫ Y : LieElement, Φ ‖Y‖ =
      ((4 * Real.pi : ℝ) : ℂ) * ∫ r in Ioi (0 : ℝ), Φ r * ((r ^ 2 : ℝ) : ℂ) := by
  obtain ⟨i₁, e₁⟩ := hr (fun r => (Φ r).re) hI.re
  obtain ⟨i₂, e₂⟩ := hr (fun r => (Φ r).im) hI.im
  have hJ : IntegrableOn (fun r : ℝ => Φ r * ((r ^ 2 : ℝ) : ℂ)) (Ioi 0) := by
    have h := (i₁.ofReal (𝕜 := ℂ)).add ((i₂.ofReal (𝕜 := ℂ)).mul_const Complex.I)
    refine h.congr (ae_of_all _ fun r => ?_)
    have hz : Φ r * ((r ^ 2 : ℝ) : ℂ) =
        (((Φ r).re * r ^ 2 : ℝ) : ℂ) + (((Φ r).im * r ^ 2 : ℝ) : ℂ) * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im (Φ r)]
      push_cast
      ring
    simp only [Pi.add_apply]
    exact hz.symm
  rw [← integral_re_add_im hI, ← integral_re_add_im hJ]
  have a₁ : ∫ Y : LieElement, RCLike.re (Φ ‖Y‖) = ∫ Y : LieElement, (Φ ‖Y‖).re := rfl
  have a₂ : ∫ Y : LieElement, RCLike.im (Φ ‖Y‖) = ∫ Y : LieElement, (Φ ‖Y‖).im := rfl
  have b₁ : ∫ r in Ioi (0 : ℝ), RCLike.re (Φ r * ((r ^ 2 : ℝ) : ℂ)) =
      ∫ r in Ioi (0 : ℝ), (Φ r).re * r ^ (3 - 1) := by
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    exact Complex.re_mul_ofReal _ _
  have b₂ : ∫ r in Ioi (0 : ℝ), RCLike.im (Φ r * ((r ^ 2 : ℝ) : ℂ)) =
      ∫ r in Ioi (0 : ℝ), (Φ r).im * r ^ (3 - 1) := by
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    exact Complex.im_mul_ofReal _ _
  rw [a₁, a₂, b₁, b₂, e₁, e₂]
  simp only [RCLike.I_to_complex, Complex.coe_algebraMap]
  push_cast
  ring
theorem continuous_diagPhase : Continuous diagPhase := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [diagPhaseMatrix] <;> fun_prop
theorem statement_holds (hChart : HaarExpChartProperties)
    (hLog : UnitaryLogConjugationProperties)
    (hNorm : LieAlgebraNormAdjointIsometry)
    (hPolar : Analysis.PolarCoordinates.PolarCoordinatesDimThreeFour) :
    statement := by
  intro F hF
  have hnorm : ∀ Y : LieElement, operatorNorm Y.toMatrix = ‖Y‖ := fun Y => (hNorm.2.2.1 Y).symm
  have hradial := (hPolar LieElement).1 finrank_lieElement
  set c : ℝ := (2 * Real.pi ^ 2)⁻¹ with hc
  set Ψ : ℝ → ℂ := fun r => F (diagPhase r) * ((c * sincAngle r ^ 2 : ℝ) : ℂ) with hΨ
  have hΨc : Continuous Ψ := by
    have h₁ : Continuous fun r : ℝ => F (diagPhase r) := F.continuous.comp continuous_diagPhase
    have h₂ : Continuous fun r : ℝ => c * sincAngle r ^ 2 :=
      continuous_const.mul (continuous_sincAngle.pow 2)
    exact h₁.mul (Complex.continuous_ofReal.comp h₂)
  set Φ : ℝ → ℂ := (Iio Real.pi).indicator Ψ with hΦ
  have hball : lieBallPi = Metric.ball (0 : LieElement) Real.pi := by
    ext Y
    simp [lieBallPi, hnorm]
  have hmeas : MeasurableSet lieBallPi := by
    rw [hball]
    exact Metric.isOpen_ball.measurableSet
  have hindicator : (fun Y : LieElement => Φ ‖Y‖) =
      lieBallPi.indicator fun Y : LieElement => Ψ ‖Y‖ := by
    funext Y
    by_cases h : ‖Y‖ < Real.pi
    · have h' : Y ∈ lieBallPi := by simpa [hball] using h
      rw [indicator_of_mem h']
      exact indicator_of_mem (mem_Iio.mpr h) _
    · have h' : Y ∉ lieBallPi := by simpa [hball] using h
      rw [indicator_of_notMem h']
      exact indicator_of_notMem (by simpa using h) _
  have hint : Integrable fun Y : LieElement => Φ ‖Y‖ := by
    rw [hindicator, integrable_indicator_iff hmeas]
    have hcont : Continuous fun Y : LieElement => Ψ ‖Y‖ := hΨc.comp continuous_norm
    have hcomp : IntegrableOn (fun Y : LieElement => Ψ ‖Y‖) (Metric.closedBall 0 Real.pi) :=
      hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
    refine hcomp.mono_set ?_
    rw [hball]
    exact Metric.ball_subset_closedBall
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ U, ‖F U‖ ≤ C := ⟨‖F‖, F.norm_coe_le_norm⟩
  have hchart := hChart.1.1 (⇑F) F.continuous.measurable ⟨C, hC⟩
  have hpoint : ∀ Y : LieElement,
      F (expChart Y) * (haarExpDensity Y.toMatrix : ℂ) = Ψ ‖Y‖ := by
    intro Y
    rw [conjInvariant_expChart hLog hF Y, hnorm Y]
    simp only [hΨ, haarExpDensity, hnorm Y, hc]
  have hIoi : ∫ r in Ioi (0 : ℝ), Φ r * ((r ^ 2 : ℝ) : ℂ) =
      ∫ r in Ioo (0 : ℝ) Real.pi, Ψ r * ((r ^ 2 : ℝ) : ℂ) := by
    have h₁ : (fun r : ℝ => Φ r * ((r ^ 2 : ℝ) : ℂ)) =
        (Iio Real.pi).indicator fun r : ℝ => Ψ r * ((r ^ 2 : ℝ) : ℂ) := by
      funext r
      by_cases h : r ∈ Iio Real.pi
      · simp only [hΦ, indicator_of_mem h]
      · simp only [hΦ, indicator_of_notMem h, zero_mul]
    rw [h₁, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]
  have hfinal : ∀ r : ℝ, Ψ r * ((r ^ 2 : ℝ) : ℂ) =
      (c : ℂ) * (F (diagPhase r) * ((Real.sin r ^ 2 : ℝ) : ℂ)) := by
    intro r
    have h₁ : c * sincAngle r ^ 2 * r ^ 2 = c * Real.sin r ^ 2 := by
      rw [← sincAngle_mul_self r]
      ring
    have h₂ : ((c * sincAngle r ^ 2 : ℝ) : ℂ) * ((r ^ 2 : ℝ) : ℂ) =
        (c : ℂ) * ((Real.sin r ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h₁
    simp only [hΨ]
    rw [mul_assoc, h₂]
    ring
  calc ∫ g, F g ∂haarProb
      = ∫ Y in lieBallPi,
          F (expChart Y) * (haarExpDensity Y.toMatrix : ℂ) ∂lieLebesgue := hchart
    _ = ∫ Y in lieBallPi, Ψ ‖Y‖ ∂lieLebesgue := by simp only [hpoint]
    _ = ∫ Y : LieElement, Φ ‖Y‖ := by rw [hindicator, integral_indicator hmeas]
    _ = ((4 * Real.pi : ℝ) : ℂ) * ∫ r in Ioi (0 : ℝ), Φ r * ((r ^ 2 : ℝ) : ℂ) :=
        radialIntegral_complex hradial.2.2.2.2 Φ hint
    _ = ((4 * Real.pi : ℝ) : ℂ) * ((c : ℂ) *
          ∫ r in Ioo (0 : ℝ) Real.pi, F (diagPhase r) * ((Real.sin r ^ 2 : ℝ) : ℂ)) := by
        rw [hIoi, ← integral_const_mul (c : ℂ)]
        simp only [hfinal]
    _ = ((2 / Real.pi : ℝ) : ℂ) *
          ∫ φ in (0 : ℝ)..Real.pi, F (diagPhase φ) * ((Real.sin φ ^ 2 : ℝ) : ℂ) := by
        rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo, ← mul_assoc]
        congr 1
        have h₁ : (4 * Real.pi) * c = 2 / Real.pi := by
          have := Real.pi_ne_zero
          rw [hc]
          field_simp
          ring
        exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h₁
end WeylIntegration
end SpinHarmonics
end YangMills.Construction
