import YangMills.Construction.ColdChainAtEveryLevel.ComplexCriticalFamiliesProof
import YangMills.Construction.ColdChainAtEveryLevel.HolomorphicFixedPoint
import Mathlib
set_option autoImplicit false
noncomputable section
open Matrix
namespace YangMills.Construction.Analytic
variable {m : ℕ}
theorem realParts_add (t t' : Fin m → ℂ) : realParts (t + t') = realParts t + realParts t' := by
  funext i; simp [realParts]
theorem imagParts_add (t t' : Fin m → ℂ) : imagParts (t + t') = imagParts t + imagParts t' := by
  funext i; simp [imagParts]
theorem realParts_ofReal_smul (c : ℝ) (t : Fin m → ℂ) : realParts ((c : ℂ) • t) = c • realParts t := by
  funext i; simp [realParts]
theorem imagParts_ofReal_smul (c : ℝ) (t : Fin m → ℂ) : imagParts ((c : ℂ) • t) = c • imagParts t := by
  funext i; simp [imagParts]
theorem complexifiedSeminorm_isComplexCoordNorm {Y : (Fin m → ℝ) → ℝ} (hY : IsRealCoordSeminorm Y)
    (hdef : ∀ x, Y x = 0 → x = 0) :
    IsComplexCoordNorm (complexifiedSeminorm Y) where
  nonneg t := add_nonneg (hY.nonneg _) (hY.nonneg _)
  triangle t t' := by
    simp only [complexifiedSeminorm, realParts_add, imagParts_add]
    linarith [hY.triangle (realParts t) (realParts t'), hY.triangle (imagParts t) (imagParts t')]
  smul_real c t := by
    simp only [complexifiedSeminorm, realParts_ofReal_smul, imagParts_ofReal_smul, hY.smul_real]
    ring
  eq_zero t h := by
    have h1 := hY.nonneg (realParts t)
    have h2 := hY.nonneg (imagParts t)
    have e1 : realParts t = 0 := hdef _ (by unfold complexifiedSeminorm at h; linarith)
    have e2 : imagParts t = 0 := hdef _ (by unfold complexifiedSeminorm at h; linarith)
    funext i
    apply Complex.ext
    · exact congrFun e1 i
    · exact congrFun e2 i
theorem matrixFormPairing_eq_re_add_im (M : Matrix (Fin m) (Fin m) ℝ) (D : Fin m → ℂ) (α : Fin m → ℝ) :
    matrixFormPairing M D α =
      ((realParts D ⬝ᵥ (M *ᵥ α) : ℝ) : ℂ) + Complex.I * ((imagParts D ⬝ᵥ (M *ᵥ α) : ℝ) : ℂ) := by apply _root_.YangMills.Construction.ComplexCriticalFamilies.matrixFormPairing_eq_re_add_im <;> assumption
theorem matrixFormPairing_sub (M : Matrix (Fin m) (Fin m) ℝ) (D D' : Fin m → ℂ) (α : Fin m → ℝ) :
    matrixFormPairing M (D - D') α = matrixFormPairing M D α - matrixFormPairing M D' α := by
  simp only [matrixFormPairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
theorem matrixFormPairing_eq_directionPairing_vecMul (M : Matrix (Fin m) (Fin m) ℝ) (D : Fin m → ℂ)
    (α : Fin m → ℝ) :
    matrixFormPairing M D α = directionPairing (D ᵥ* M.map (fun x : ℝ => (x : ℂ))) α := by
  simp only [matrixFormPairing, directionPairing, Matrix.vecMul, dotProduct, Matrix.mulVec, Matrix.map_apply,
    Finset.mul_sum]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
theorem holomorphicZeroOfCoerciveFamily_of_fixedPoint (hF : HolomorphicFixedPointProperty) :
    HolomorphicZeroOfCoerciveFamilyProperty := by
  intro m k ι p q Y M g Ω κ ε Ca K r hι hY hdef hp hq hpY hYp hCa hK hr hΩ hco han hsz hsrc hlip
  obtain ⟨i₀⟩ := hι
  have hYc := complexifiedSeminorm_isComplexCoordNorm hY hdef
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hv
    apply hdef
    have h1 : ∀ i, p i v ≤ 0 := by
      intro i
      have := hco i v 0 le_rfl (fun α => by
        rw [Matrix.dotProduct_mulVec, hvM]
        simp)
      simpa using this
    exact le_antisymm (hYp v 0 le_rfl h1) (hY.nonneg v)
  set Mc : Matrix (Fin m) (Fin m) ℂ := M.map (fun x : ℝ => (x : ℂ)) with hMc
  set N : Matrix (Fin m) (Fin m) ℂ := (M⁻¹).map (fun x : ℝ => (x : ℂ)) with hN
  have hNM : N * Mc = 1 := by
    have h1 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
    have h2 := congrArg (fun Q : Matrix (Fin m) (Fin m) ℝ => Complex.ofRealHom.mapMatrix Q) h1
    simp only [map_mul, map_one] at h2
    exact h2
  set Lm : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ) := LinearMap.toContinuousLinearMap (Matrix.vecMulLinear N) with hLm
  have hLa : ∀ v, Lm v = v ᵥ* N := fun v => rfl
  set Φ : (Fin m → ℂ) × (Fin k → ℂ) → (Fin m → ℂ) := fun q => q.1 - Lm (g q) with hΦ
  have hback : ∀ v α, matrixFormPairing M (Lm v) α = directionPairing v α := by
    intro v α
    rw [matrixFormPairing_eq_directionPairing_vecMul, hLa, Matrix.vecMul_vecMul, hNM, Matrix.vecMul_one]
  have hdiff : ∀ ζ t t' α, matrixFormPairing M (Φ (t, ζ) - Φ (t', ζ)) α =
      matrixFormPairing M (t - t') α - directionPairing (g (t, ζ) - g (t', ζ)) α := by
    intro ζ t t' α
    have e : Φ (t, ζ) - Φ (t', ζ) = (t - t') - Lm (g (t, ζ) - g (t', ζ)) := by
      simp only [hΦ, map_sub]
      abel
    rw [e, matrixFormPairing_sub, hback]
  have hcoC : ∀ (D : Fin m → ℂ) (β : ℝ), 0 ≤ β → (∀ i α, ‖matrixFormPairing M D α‖ ≤ β * q i α) →
      complexifiedSeminorm Y D ≤ 2 * Ca * β := by
    intro D β hβ hb
    have hre : Y (realParts D) ≤ Ca * β := by
      refine hYp _ _ (by positivity) fun i => hco i _ β hβ fun α => ?_
      refine le_trans ?_ (hb i α)
      have h1 := Complex.abs_re_le_norm (matrixFormPairing M D α)
      rw [matrixFormPairing_eq_re_add_im] at h1 ⊢
      simpa using h1
    have him : Y (imagParts D) ≤ Ca * β := by
      refine hYp _ _ (by positivity) fun i => hco i _ β hβ fun α => ?_
      refine le_trans ?_ (hb i α)
      have h1 := Complex.abs_im_le_norm (matrixFormPairing M D α)
      rw [matrixFormPairing_eq_re_add_im] at h1 ⊢
      simpa using h1
    simp only [complexifiedSeminorm]
    linarith
  have hpc : ∀ i D, complexifiedSeminorm (p i) D ≤ complexifiedSeminorm Y D := fun i D =>
    add_le_add (hpY i _) (hpY i _)
  have hsrcΦ : ∀ ζ ∈ Ω, complexifiedSeminorm Y (Φ (0, ζ)) ≤ 2 * Ca * ε ζ := by
    intro ζ hζ
    refine hcoC _ _ (hsz ζ hζ).2.1 fun i α => ?_
    have e : Φ (0, ζ) = - Lm (g (0, ζ)) := by simp [hΦ]
    have e2 : matrixFormPairing M (- Lm (g (0, ζ))) α = - directionPairing (g (0, ζ)) α := by
      rw [← hback]
      simp [matrixFormPairing]
    rw [e, e2, norm_neg]
    exact hsrc ζ hζ i α
  have hcontr : ∀ ζ ∈ Ω, ∀ t t', complexifiedSeminorm Y t ≤ r → complexifiedSeminorm Y t' ≤ r →
      complexifiedSeminorm Y (Φ (t, ζ) - Φ (t', ζ)) ≤ (1 / 2) * complexifiedSeminorm Y (t - t') := by
    intro ζ hζ t t' ht ht'
    obtain ⟨hκ, -, -, h4⟩ := hsz ζ hζ
    have hn1 := hYc.nonneg t
    have hn2 := hYc.nonneg t'
    have hn3 := hYc.nonneg (t - t')
    set β := K * (complexifiedSeminorm Y t + complexifiedSeminorm Y t' + κ ζ) * complexifiedSeminorm Y (t - t')
      with hβd
    have hβ : 0 ≤ β := by positivity
    have h1 := hcoC (Φ (t, ζ) - Φ (t', ζ)) β hβ (fun i α => by
      rw [hdiff, norm_sub_rev]
      refine (hlip ζ hζ t t' ht ht' i α).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (hq i α)
      exact mul_le_mul_of_nonneg_left (hpc i _) (by positivity))
    refine h1.trans ?_
    have h2 : 2 * Ca * K * (complexifiedSeminorm Y t + complexifiedSeminorm Y t' + κ ζ) ≤ 1 / 2 := by
      have h3 : 4 * Ca * K * (complexifiedSeminorm Y t + complexifiedSeminorm Y t' + κ ζ) ≤
          4 * Ca * K * (2 * r + κ ζ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
      linarith
    calc 2 * Ca * β = 2 * Ca * K * (complexifiedSeminorm Y t + complexifiedSeminorm Y t' + κ ζ) *
          complexifiedSeminorm Y (t - t') := by
          rw [hβd]; ring
      _ ≤ (1 / 2) * complexifiedSeminorm Y (t - t') := mul_le_mul_of_nonneg_right h2 hn3
  obtain ⟨w, hw⟩ := hF m k (complexifiedSeminorm Y) Φ Ω r hr hΩ hYc
    (fun ζ hζ t ht => analyticAt_fst.sub ((Lm.analyticAt _).comp (han ζ hζ t ht)))
    (fun ζ hζ => (hsrcΦ ζ hζ).trans (by linarith [(hsz ζ hζ).2.2.1]))
    hcontr
  refine ⟨w, fun ζ hζ => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hw ζ hζ
  refine ⟨h1, ?_, ?_, ?_⟩
  · have e : Lm (g (w ζ, ζ)) = 0 := by
      have : w ζ - Lm (g (w ζ, ζ)) = w ζ := h2
      simpa using this
    have e2 : (g (w ζ, ζ) ᵥ* N) ᵥ* Mc = g (w ζ, ζ) := by
      rw [Matrix.vecMul_vecMul, hNM, Matrix.vecMul_one]
    rw [← e2, ← hLa, e]
    simp
  · refine h3.trans ?_
    have := hsrcΦ ζ hζ
    linarith
  · intro hreal
    have hmem := h4 {t | imagParts t = 0} (isClosed_eq (continuous_pi fun i =>
      Complex.continuous_im.comp (continuous_apply i)) continuous_const) (by
        funext i; simp [imagParts]) (by
        intro t ht htr
        have ht' : imagParts t = 0 := ht
        have h5 := hreal t ht' htr
        show imagParts (t - Lm (g (t, ζ))) = 0
        funext j
        have h6 : (Lm (g (t, ζ)) j).im = 0 := by
          rw [hLa]
          simp only [Matrix.vecMul, dotProduct, hN, Matrix.map_apply, Complex.im_sum]
          refine Finset.sum_eq_zero fun i _ => ?_
          have h7 : (g (t, ζ) i).im = 0 := congrFun h5 i
          simp [Complex.mul_im, h7]
        have h8 : (t j).im = 0 := congrFun ht' j
        simp [imagParts, h6, h8])
    exact hmem
end YangMills.Construction.Analytic
end
