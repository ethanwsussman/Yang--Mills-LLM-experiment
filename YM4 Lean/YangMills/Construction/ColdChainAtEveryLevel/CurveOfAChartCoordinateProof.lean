import YangMills.Construction.ColdChainAtEveryLevel.CurveOfAChartCoordinate
import YangMills.Construction.ColdChainAtEveryLevel.FactsOfTheLogarithm
import YangMills.Construction.ColdChainAtEveryLevel.LogarithmNearOne
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfAMovedExponential
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology ContDiff
open NormedSpace
namespace YangMills.Construction.ExpShiftCurves
open BlockAverages QuaternionLog ColdStepAtMirrorFrames
local instance normedAlgebraRatQuaternion : NormedAlgebra ℚ ℍ[ℝ] := NormedAlgebra.restrictScalars ℚ ℝ ℍ[ℝ]
theorem analyticAt_qlog_one : AnalyticAt ℝ qlog 1 := by
  have hω : ContDiffAt ℝ ω (exp : ℍ[ℝ] → ℍ[ℝ]) 0 := (exp_analytic (𝕂 := ℝ) (0 : ℍ[ℝ])).contDiffAt
  have := hω.to_localInverse hasFDerivAt_exp_zero_refl (by simp)
  rw [exp_zero_eq_one] at this
  exact this.analyticAt
def imPartCLM : ℍ[ℝ] →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => ⟨pureComponent q, re_pureComponent q⟩
      map_add' := fun a b => Subtype.ext (pureComponent_add a b)
      map_smul' := fun r a => Subtype.ext (pureComponent_smul r a) }
theorem imPartCLM_coe (v : imaginaryQuaternions) : imPartCLM (v : ℍ[ℝ]) = v :=
  Subtype.ext (pureComponent_of_re_eq_zero v.2)
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := Subtype.ext (by simp [expUnit])
theorem exists_analytic_shift_curve (Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions)
    (U : Set (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)) (C : ℝ) (hU : IsOpen U) (hC : 0 ≤ C)
    (hd : ∀ r, diagonalTriple r ∈ U) (hs : ContDiffOn ℝ 3 Θ U)
    (he : ∀ z ∈ U, expUnit (Θ z) = expUnit z.1 * expUnit z.2.1 * (expUnit z.2.2)⁻¹)
    (h0 : ∀ r, Θ (diagonalTriple r) = 0)
    (hb : ∀ (r : imaginaryQuaternions) (j : ℕ), ‖r‖ ≤ 1 → j ≤ 3 → ‖iteratedFDeriv ℝ j Θ (diagonalTriple r)‖ ≤ C)
    (hf : ∀ z : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions, fderiv ℝ Θ 0 z = z.1 + z.2.1 - z.2.2)
    (hl : ∀ (r : imaginaryQuaternions) (z : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions), ‖r‖ ≤ 1 →
      ‖fderiv ℝ Θ (diagonalTriple r) z - fderiv ℝ Θ 0 z‖ ≤ C * ‖r‖ * ‖z‖)
    (w d : imaginaryQuaternions) (hw : ‖w‖ ≤ 1) :
    ∃ η : ℝ → imaginaryQuaternions, AnalyticAt ℝ η 0 ∧ η 0 = 0 ∧
      (∀ᶠ τ : ℝ in 𝓝 0, expUnit (η τ) * expUnit w = expUnit (w + τ • d)) ∧
      ‖deriv η 0 - d‖ ≤ (C + 1) * ‖w‖ * ‖d‖ ∧ ‖deriv (deriv η) 0‖ ≤ (C + 1) * ‖d‖ ^ 2 := by
  let D : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions := (d, 0, 0)
  let g : ℝ → imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions := fun τ => diagonalTriple w + τ • D
  have hg0 : g 0 = diagonalTriple w := by simp [g]
  have hgd : ∀ τ, HasDerivAt g D τ := fun τ => by
    have h := ((hasDerivAt_id τ).smul_const D).const_add (diagonalTriple w)
    simp only [id, one_smul] at h
    exact h
  have hgc : Filter.Tendsto g (𝓝 0) (𝓝 (diagonalTriple w)) := by
    have := (hgd 0).continuousAt.tendsto
    rwa [hg0] at this
  have hUn : ∀ᶠ τ in 𝓝 (0 : ℝ), g τ ∈ U := hgc.eventually (hU.mem_nhds (hd w))
  have hcd : ∀ z ∈ U, ContDiffAt ℝ 3 Θ z := fun z hz => hs.contDiffAt (hU.mem_nhds hz)
  let η₁ : ℝ → imaginaryQuaternions := fun τ => Θ (g τ)
  have hg1 : ∀ τ, (g τ).1 = w + τ • d := fun τ => by simp [g, D, diagonalTriple]
  have hg2 : ∀ τ, (g τ).2.1 = 0 := fun τ => by simp [g, D, diagonalTriple]
  have hg3 : ∀ τ, (g τ).2.2 = w := fun τ => by simp [g, D, diagonalTriple]
  have hη₁0 : η₁ 0 = 0 := by simp only [η₁, hg0, h0]
  have hη₁e : ∀ᶠ τ in 𝓝 (0 : ℝ), expUnit (η₁ τ) * expUnit w = expUnit (w + τ • d) := by
    filter_upwards [hUn] with τ hτ
    simp only [η₁]
    rw [he _ hτ, hg1, hg2, hg3, expUnit_zero]
    simp
  have hη₁d : deriv η₁ =ᶠ[𝓝 0] fun τ => fderiv ℝ Θ (g τ) D := by
    filter_upwards [hUn] with τ hτ
    have h1 : DifferentiableAt ℝ Θ (g τ) := (hcd _ hτ).differentiableAt (by norm_num)
    exact (h1.hasFDerivAt.comp_hasDerivAt τ (hgd τ)).deriv
  have hcx : ContDiffAt ℝ 3 Θ (diagonalTriple w) := hcd _ (hd w)
  have hD2 : DifferentiableAt ℝ (fderiv ℝ Θ) (diagonalTriple w) := by
    have : ContDiffAt ℝ 2 (fderiv ℝ Θ) (diagonalTriple w) := hcx.fderiv_right (by norm_num)
    exact this.differentiableAt (by norm_num)
  have hη₁1 : deriv η₁ 0 = fderiv ℝ Θ (diagonalTriple w) D := by
    rw [hη₁d.eq_of_nhds, hg0]
  have hη₁2 : deriv (deriv η₁) 0 = fderiv ℝ (fderiv ℝ Θ) (diagonalTriple w) D D := by
    rw [hη₁d.deriv_eq]
    have h1 : HasFDerivAt (fderiv ℝ Θ) (fderiv ℝ (fderiv ℝ Θ) (g 0)) (g 0) := by
      rw [hg0]
      exact hD2.hasFDerivAt
    have h2 : HasDerivAt (fun τ => fderiv ℝ Θ (g τ)) (fderiv ℝ (fderiv ℝ Θ) (g 0) D) 0 :=
      HasFDerivAt.comp_hasDerivAt (f := g) (l := fderiv ℝ Θ) 0 h1 (hgd 0)
    have h3 := (h2.clm_apply (hasDerivAt_const (0 : ℝ) D)).deriv
    rw [h3, hg0]
    simp
  have hnD : ‖D‖ = ‖d‖ := by simp [D, Prod.norm_def]
  let P : ℝ → ℍ[ℝ] := fun τ => exp (((w + τ • d : imaginaryQuaternions) : ℍ[ℝ])) * exp (-(w : ℍ[ℝ]))
  have hP0 : P 0 = 1 := by
    simp only [P, zero_smul, add_zero]
    rw [← exp_add_of_commute (by simp)]
    simp
  have hPa : AnalyticAt ℝ P 0 := by
    have h1 : AnalyticAt ℝ (fun τ : ℝ => ((w + τ • d : imaginaryQuaternions) : ℍ[ℝ])) 0 := by
      have : (fun τ : ℝ => ((w + τ • d : imaginaryQuaternions) : ℍ[ℝ])) = fun τ : ℝ => (w : ℍ[ℝ]) + τ • (d : ℍ[ℝ]) := by
        funext τ
        simp
      rw [this]
      fun_prop
    have h2 : AnalyticAt ℝ (fun τ : ℝ => exp (((w + τ • d : imaginaryQuaternions) : ℍ[ℝ]))) 0 :=
      (exp_analytic (𝕂 := ℝ) _).comp h1
    exact h2.mul analyticAt_const
  have hℓ : AnalyticAt ℝ (fun τ => qlog (P τ)) 0 := by
    have h1 : AnalyticAt ℝ qlog (P 0) := by rw [hP0]; exact analyticAt_qlog_one
    exact h1.comp hPa
  have hηa : AnalyticAt ℝ (fun τ => imPartCLM (qlog (P τ))) 0 := (imPartCLM.analyticAt _).comp hℓ
  have hto : Filter.Tendsto (fun τ => ((η₁ τ : imaginaryQuaternions) : ℍ[ℝ])) (𝓝 0) (𝓝 0) := by
    have h1 : Filter.Tendsto η₁ (𝓝 0) (𝓝 0) := by
      have := hcx.continuousAt.tendsto.comp hgc
      rwa [h0] at this
    exact (continuous_subtype_val.tendsto (0 : imaginaryQuaternions)).comp h1
  have heq : (fun τ => imPartCLM (qlog (P τ))) =ᶠ[𝓝 0] η₁ := by
    filter_upwards [hto.eventually eventually_qlog_exp, hη₁e] with τ h1 h2
    have h3 : exp ((η₁ τ : imaginaryQuaternions) : ℍ[ℝ]) * exp (w : ℍ[ℝ]) = exp (((w + τ • d : imaginaryQuaternions) : ℍ[ℝ])) :=
      congrArg Subtype.val h2
    have h4 : exp (w : ℍ[ℝ]) * exp (-(w : ℍ[ℝ])) = 1 := by
      rw [← exp_add_of_commute (by simp)]
      simp
    have h5 : P τ = exp ((η₁ τ : imaginaryQuaternions) : ℍ[ℝ]) := by
      simp only [P]
      rw [← h3, mul_assoc, h4, mul_one]
    simp only [h5, h1, imPartCLM_coe]
  refine ⟨fun τ => imPartCLM (qlog (P τ)), hηa, ?_, ?_, ?_, ?_⟩
  · rw [heq.self_of_nhds, hη₁0]
  · filter_upwards [heq, hη₁e] with τ h1 h2
    rw [h1, h2]
  · rw [heq.deriv_eq, hη₁1]
    have h1 := hl w D hw
    have h2 : fderiv ℝ Θ 0 D = d := by
      rw [hf]
      simp [D]
    rw [h2, hnD] at h1
    refine h1.trans ?_
    have : 0 ≤ ‖w‖ * ‖d‖ := by positivity
    nlinarith
  · rw [heq.deriv.deriv_eq, hη₁2]
    have h1 := (iteratedFDeriv ℝ 2 Θ (diagonalTriple w)).le_opNorm ![D, D]
    rw [iteratedFDeriv_two_apply] at h1
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hnD] at h1
    have h2 := hb w 2 hw (by norm_num)
    refine h1.trans ?_
    have h3 : 0 ≤ ‖d‖ * ‖d‖ := by positivity
    have h4 := mul_le_mul_of_nonneg_right h2 h3
    nlinarith
theorem expShiftCurve_of_conjugatedExpLogSmooth (h : ConjugatedExpLogSmooth) : ExpShiftCurve := by
  obtain ⟨Θ, U, C, hU, hC, hd, hs, he, h0, hb, hf, hl⟩ := h
  exact ⟨C + 1, 1, by positivity, one_pos, fun w d hw =>
    exists_analytic_shift_curve Θ U C hU hC hd hs he h0 hb hf hl w d hw⟩
end YangMills.Construction.ExpShiftCurves
end
