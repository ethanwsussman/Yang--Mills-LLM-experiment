import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionUnderAGaugeOfTheTopForm
import YangMills.Construction.ColdStepAtMirrorFrames.FirstOrderAtTheFlatFieldForm
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace UniformFieldFirstDeriv
open BlockOffsets
variable {F : BlockFrame}
theorem exists_adjointAction_eq_neg (X : imaginaryQuaternions) (hX : ‖X‖ = 1) :
    ∃ g : UnitQuaternion, adjointAction g X = -X := by
  set a := (X : ℍ[ℝ]).imI
  set b := (X : ℍ[ℝ]).imJ
  set c := (X : ℍ[ℝ]).imK
  have hre : (X : ℍ[ℝ]).re = 0 := X.2
  have hn : a ^ 2 + b ^ 2 + c ^ 2 = 1 := by
    have h1 : ‖(X : ℍ[ℝ])‖ ^ 2 = 1 := by
      have : ‖(X : ℍ[ℝ])‖ = 1 := hX
      rw [this]; norm_num
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def', hre] at h1
    nlinarith
  obtain ⟨p, q, r, hpn, hdot⟩ : ∃ p q r : ℝ, p ^ 2 + q ^ 2 + r ^ 2 = 1 ∧ p * a + q * b + r * c = 0 := by
    by_cases h : a ^ 2 + b ^ 2 = 0
    · refine ⟨1, 0, 0, by norm_num, ?_⟩
      have : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      rw [this]; ring
    · have hp : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
      set d := Real.sqrt (a ^ 2 + b ^ 2)
      have hd : d ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hp.le
      have hd0 : d ≠ 0 := by
        intro h0
        rw [h0] at hd
        nlinarith
      refine ⟨-b / d, a / d, 0, ?_, ?_⟩
      · field_simp
        nlinarith
      · field_simp
        ring
  obtain ⟨P, hPr, hPi, hPj, hPk⟩ : ∃ P : ℍ[ℝ], P.re = 0 ∧ P.imI = p ∧ P.imJ = q ∧ P.imK = r :=
    ⟨⟨0, p, q, r⟩, rfl, rfl, rfl, rfl⟩
  have hN : Quaternion.normSq P = 1 := by
    rw [Quaternion.normSq_def', hPr, hPi, hPj, hPk]
    linarith
  have hPs : star P * P = 1 := by
    rw [Quaternion.star_mul_self, hN]
    simp
  have hPs' : P * star P = 1 := by
    rw [Quaternion.self_mul_star, hN]
    simp
  let g : UnitQuaternion := ⟨P, Unitary.mem_iff.mpr ⟨hPs, hPs'⟩⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  show P * (X : ℍ[ℝ]) * star P = -(X : ℍ[ℝ])
  apply Quaternion.ext
  · simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
      Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, Quaternion.re_neg, hre, hPr, hPi, hPj, hPk]
    ring
  · simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
      Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, Quaternion.imI_neg, hre, hPr, hPi, hPj, hPk]
    linear_combination (2 * p) * hdot - a * hpn
  · simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
      Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, Quaternion.imJ_neg, hre, hPr, hPi, hPj, hPk]
    linear_combination (2 * q) * hdot - b * hpn
  · simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
      Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, Quaternion.imK_neg, hre, hPr, hPi, hPj, hPk]
    linear_combination (2 * r) * hdot - c * hpn
theorem plaquetteDefect_leftTranslate_le {j : ℕ} (Z : F.Site j → Fin 4 → imaginaryQuaternions)
    (p : F.Site j × Fin 4 × Fin 4) (q : ℝ)
    (hq : ∀ y i, ‖Z y i‖ ≤ q) : plaquetteDefect (leftTranslate Z (uniformField F j)) p ≤ 4 * q := by
  obtain ⟨x, μ, ν⟩ := p
  have e1 : x + unitStep j μ + unitStep j ν - unitStep j μ = x + unitStep j ν := by abel
  have e2 : x + unitStep j μ + unitStep j ν + -unitStep j μ = x + unitStep j ν := by abel
  have e5 : x + unitStep j ν - unitStep j ν = x := by abel
  have hp : plaquetteHolonomy (leftTranslate Z (uniformField F j)) (x, μ, ν) =
      expUnit (Z x μ) * (expUnit (Z (x + unitStep j μ) ν) *
        ((expUnit (Z (x + unitStep j ν) μ))⁻¹ * (expUnit (Z x ν))⁻¹)) := by
    simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
      if_false, leftTranslate, uniformField, e1, e2, e5, mul_one]
  show distFromOne _ ≤ _
  rw [hp]
  have a1 := (distFromOne_expUnit_le (Z x μ)).trans (hq _ _)
  have a2 := (distFromOne_expUnit_le (Z (x + unitStep j μ) ν)).trans (hq _ _)
  have a3 := (distFromOne_expUnit_le (Z (x + unitStep j ν) μ)).trans (hq _ _)
  have a4 := (distFromOne_expUnit_le (Z x ν)).trans (hq _ _)
  have b1 := distFromOne_mul (expUnit (Z x μ)) (expUnit (Z (x + unitStep j μ) ν) *
        ((expUnit (Z (x + unitStep j ν) μ))⁻¹ * (expUnit (Z x ν))⁻¹))
  have b2 := distFromOne_mul (expUnit (Z (x + unitStep j μ) ν))
        ((expUnit (Z (x + unitStep j ν) μ))⁻¹ * (expUnit (Z x ν))⁻¹)
  have b3 := distFromOne_mul (expUnit (Z (x + unitStep j ν) μ))⁻¹ (expUnit (Z x ν))⁻¹
  rw [distFromOne_inv, distFromOne_inv] at b3
  linarith
end UniformFieldFirstDeriv
open UniformFieldFirstDeriv
open BlockOffsets
theorem uniformFieldFirstDerivZero_of_gaugeCovariance (hg : GaugeCovarianceOfFrame) :
    UniformFieldFirstDerivZero := by
  intro L t n₀ σ δ E E₃ f F y c X hf hF hσ hX
  obtain ⟨g, hgX⟩ := exists_adjointAction_eq_neg (X 0) (hX 0)
  let γ : F.Site F.depth → UnitQuaternion := fun _ => g
  have hflat : gaugeTransform γ (uniformField F F.depth) = uniformField F F.depth := by
    funext z i
    simp [gaugeTransform, uniformField, γ]
  have hball : ∀ᶠ τ in 𝓝 (0 : Fin 1 → ℝ), ‖τ‖ < σ / 4 := by
    have := Metric.ball_mem_nhds (0 : Fin 1 → ℝ) (by positivity : 0 < σ / 4)
    exact Filter.eventually_of_mem this fun τ h => by simpa using h
  have hev : ∀ᶠ τ in 𝓝 (0 : Fin 1 → ℝ),
      subtractTrivial f F y (gaugeTransform γ (leftTranslate (bondSpread c X τ) (uniformField F F.depth))) =
      subtractTrivial f F y (leftTranslate (bondSpread c X τ) (uniformField F F.depth)) := by
    refine hball.mono fun τ hτ => ?_
    have hsp : ∀ z i, ‖bondSpread c X τ z i‖ ≤ ‖τ‖ := by
      intro z i
      simp only [bondSpread, Fin.sum_univ_one]
      by_cases e : c 0 = (z, i)
      · rw [if_pos e, norm_smul, hX 0, mul_one]
        exact norm_le_pi_norm τ 0
      · rw [if_neg e, norm_zero]
        exact norm_nonneg _
    have hc : IsSmallCurvature σ (leftTranslate (bondSpread c X τ) (uniformField F F.depth)) := fun p _ =>
      (plaquetteDefect_leftTranslate_le _ p _ hsp).trans_lt (by linarith)
    show f F y _ - _ = f F y _ - _
    rw [hf.gauge_invariant F hF y _ γ hc]
  have e1 := hg.2.1 F F.depth 1 (subtractTrivial f F y) (subtractTrivial f F y) (uniformField F F.depth) γ c X hev
  rw [hflat] at e1
  have hX' : (fun l => adjointAction (γ (c l).1) (X l)) = -X := by
    funext l
    fin_cases l
    exact hgX
  rw [hX'] at e1
  have hneg : bondDeriv (subtractTrivial f F y) (uniformField F F.depth) c (-X) =
      -bondDeriv (subtractTrivial f F y) (uniformField F F.depth) c X := by
    unfold bondDeriv
    have e2 : (fun τ : Fin 1 → ℝ =>
        subtractTrivial f F y (leftTranslate (bondSpread c (-X) τ) (uniformField F F.depth))) =
        fun τ => (fun τ' => subtractTrivial f F y
          (leftTranslate (bondSpread c X τ') (uniformField F F.depth))) (-τ) := by
      funext τ
      congr 2
      funext z i
      simp only [bondSpread, Fin.sum_univ_one]
      split_ifs
      · show τ 0 • (-(X 0)) = (-(τ 0)) • X 0
        module
      · rfl
    rw [e2, iteratedFDeriv_one_apply, iteratedFDeriv_one_apply]
    have e3 := (ContinuousLinearEquiv.neg ℝ : (Fin 1 → ℝ) ≃L[ℝ] (Fin 1 → ℝ)).comp_right_fderiv
      (f := fun τ' => subtractTrivial f F y (leftTranslate (bondSpread c X τ') (uniformField F F.depth))) (x := 0)
    have e4 : ((fun τ' => subtractTrivial f F y (leftTranslate (bondSpread c X τ') (uniformField F F.depth))) ∘
        (ContinuousLinearEquiv.neg ℝ : (Fin 1 → ℝ) ≃L[ℝ] (Fin 1 → ℝ))) =
        fun τ => (fun τ' => subtractTrivial f F y
          (leftTranslate (bondSpread c X τ') (uniformField F F.depth))) (-τ) := rfl
    rw [e4] at e3
    rw [e3]
    simp
  rw [hneg] at e1
  linarith
end ColdStepAtMirrorFrames
end YangMills.Construction
end
