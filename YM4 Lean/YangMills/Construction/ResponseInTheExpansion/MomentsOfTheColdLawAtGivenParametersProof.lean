import YangMills.Construction.ClusterExpansionOfAStep.CovarianceOfAFunctionOfSomeBondsProof
import YangMills.Construction.ResponseInTheExpansion.HessianAtTheFramesIsCoerciveAndLocal
import YangMills.Construction.ResponseInTheExpansion.MomentsOfTheColdLawAtGivenParameters
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation WeightedResponses MeasureTheory
namespace ResponseInTheExpansion
open RenormalizationStepParameters
private theorem sum_pow_le_three_pow_mul_sum_pow (a : Fin 3 → ℝ) (ha : ∀ i, 0 ≤ a i) (Q : ℕ) :
    (∑ i, a i) ^ Q ≤ 3 ^ Q * ∑ i, a i ^ Q := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ a ⟨0, Finset.mem_univ _⟩
  have h1 : ∑ i, a i ≤ 3 * a j := by
    have := Finset.sum_le_card_nsmul Finset.univ a (a j) (fun i hi => hj i hi)
    simpa using this
  have h2 : (∑ i, a i) ^ Q ≤ (3 * a j) ^ Q :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => ha i) h1 Q
  have h3 : a j ^ Q ≤ ∑ i, a i ^ Q :=
    Finset.single_le_sum (f := fun i => a i ^ Q) (fun i _ => pow_nonneg (ha i) Q) (Finset.mem_univ j)
  calc (∑ i, a i) ^ Q ≤ (3 * a j) ^ Q := h2
    _ = 3 ^ Q * a j ^ Q := mul_pow _ _ _
    _ ≤ 3 ^ Q * ∑ i, a i ^ Q := mul_le_mul_of_nonneg_left h3 (by positivity)
private theorem norm_pow_two_mul_le (v : EuclideanSpace ℝ (Fin 3)) (Q : ℕ) :
    ‖v‖ ^ (2 * Q) ≤ 3 ^ Q * ∑ i, v i ^ (2 * Q) := by
  have e : ‖v‖ ^ 2 = ∑ i, v i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  calc ‖v‖ ^ (2 * Q) = (∑ i, v i ^ 2) ^ Q := by rw [pow_mul, e]
    _ ≤ 3 ^ Q * ∑ i, (v i ^ 2) ^ Q := sum_pow_le_three_pow_mul_sum_pow _ (fun i => sq_nonneg _) Q
    _ = 3 ^ Q * ∑ i, v i ^ (2 * Q) := by simp only [pow_mul]
section Expectation
variable {ι : Type} [Fintype ι]
private theorem ballDensity_cutoff_nonneg (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) (η : BondField ι) :
    0 ≤ ballDensity (cutoffFactor ρ p) Ψ η := by apply _root_.YangMills.Construction.ConvexMeasures.LocalCovariance.ballDensity_nonneg <;> assumption
private theorem ballDensity_cutoff_eq_zero (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) (η : BondField ι) (b : ι)
    (h : ¬ ‖η b‖ < ρ) : ballDensity (cutoffFactor ρ p) Ψ η = 0 := by
  unfold ballDensity radialWeightProd
  rw [Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, h]), zero_mul]
private theorem integrable_mul_ballDensity_of_bounded {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} (b : ι)
    (hI : Integrable (ballDensity (cutoffFactor ρ p) Ψ)) {g : BondField ι → ℝ} (hg : Continuous g) {K : ℝ}
    (hK : ∀ η : BondField ι, ‖η b‖ < ρ → |g η| ≤ K) :
    Integrable fun η => g η * ballDensity (cutoffFactor ρ p) Ψ η := by
  refine Integrable.mono' (hI.const_mul K) (hg.aestronglyMeasurable.mul hI.aestronglyMeasurable)
    (ae_of_all _ fun η => ?_)
  by_cases h : ‖η b‖ < ρ
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (ballDensity_cutoff_nonneg ρ p Ψ η)]
    exact mul_le_mul_of_nonneg_right (hK η h) (ballDensity_cutoff_nonneg ρ p Ψ η)
  · rw [ballDensity_cutoff_eq_zero ρ p Ψ η b h]
    simp
private theorem ballExpectation_norm_pow_le (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) (b : ι) (Q : ℕ) :
    ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ (2 * Q)) ≤
      3 ^ Q * ∑ i, ballExpectation (cutoffFactor ρ p) Ψ (fun η => η b i ^ (2 * Q)) := by
  unfold ballExpectation
  by_cases hI : Integrable (ballDensity (cutoffFactor ρ p) Ψ)
  · have hZ : 0 ≤ ∫ η, ballDensity (cutoffFactor ρ p) Ψ η := integral_nonneg (ballDensity_cutoff_nonneg ρ p Ψ)
    have hcn : Continuous fun η : BondField ι => ‖η b‖ ^ (2 * Q) := by fun_prop
    have hci : ∀ i : Fin 3, Continuous fun η : BondField ι => η b i ^ (2 * Q) := fun i => by
      have : Continuous fun η : BondField ι => η b i :=
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).continuous.comp (continuous_apply b)
      exact this.pow _
    have hin : Integrable fun η => ‖η b‖ ^ (2 * Q) * ballDensity (cutoffFactor ρ p) Ψ η :=
      integrable_mul_ballDensity_of_bounded b hI hcn (K := |ρ| ^ (2 * Q)) (fun η h => by
        rw [abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (h.le.trans (le_abs_self _)) _)
    have hii : ∀ i : Fin 3, Integrable fun η => η b i ^ (2 * Q) * ballDensity (cutoffFactor ρ p) Ψ η := fun i =>
      integrable_mul_ballDensity_of_bounded b hI (hci i) (K := |ρ| ^ (2 * Q)) (fun η h => by
        rw [abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
        have h1 : |η b i| ≤ ‖η b‖ := by
          simpa using PiLp.norm_apply_le (η b) i
        exact h1.trans (h.le.trans (le_abs_self _)))
    have hsum : Integrable fun η => 3 ^ Q * ∑ i : Fin 3, η b i ^ (2 * Q) * ballDensity (cutoffFactor ρ p) Ψ η :=
      (integrable_finsetSum _ fun i _ => hii i).const_mul _
    have hmono : ∫ η, ‖η b‖ ^ (2 * Q) * ballDensity (cutoffFactor ρ p) Ψ η ≤
        ∫ η, 3 ^ Q * ∑ i : Fin 3, η b i ^ (2 * Q) * ballDensity (cutoffFactor ρ p) Ψ η := by
      refine integral_mono hin hsum fun η => ?_
      have h1 := mul_le_mul_of_nonneg_right (norm_pow_two_mul_le (η b) Q) (ballDensity_cutoff_nonneg ρ p Ψ η)
      calc ‖η b‖ ^ (2 * Q) * ballDensity (cutoffFactor ρ p) Ψ η
          ≤ 3 ^ Q * (∑ i, η b i ^ (2 * Q)) * ballDensity (cutoffFactor ρ p) Ψ η := h1
        _ = 3 ^ Q * ∑ i : Fin 3, η b i ^ (2 * Q) * ballDensity (cutoffFactor ρ p) Ψ η := by
          rw [mul_assoc, Finset.sum_mul]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hii i] at hmono
    rw [← Finset.sum_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hmono hZ
  · rw [integral_undef hI]
    simp
end Expectation
section Inverse
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem abs_dotProduct_inv_mulVec_le {H : Matrix ι ι ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hf : ∀ x : ι → ℝ, lam * ∑ p, x p ^ 2 ≤ ∑ p, x p * H.mulVec x p) (e : ι → ℝ) :
    |e ⬝ᵥ H⁻¹.mulVec e| ≤ (∑ p, e p ^ 2) / lam := by
  have hinj : Function.Injective H.mulVec := by
    intro u v huv
    have h0 : H.mulVec (u - v) = 0 := by rw [Matrix.mulVec_sub, huv, sub_self]
    have h1 := hf (u - v)
    rw [h0] at h1
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1
    have h2 : ∑ p, (u - v) p ^ 2 ≤ 0 := by
      by_contra hc
      exact absurd h1 (not_le.2 (mul_pos hlam (not_le.1 hc)))
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => sq_nonneg ((u - v) p))).1
      (le_antisymm h2 (Finset.sum_nonneg fun p _ => sq_nonneg _))
    funext p
    have := h3 p (Finset.mem_univ p)
    exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 this)
  have hU : IsUnit H := Matrix.mulVec_injective_iff_isUnit.1 hinj
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).1 hU
  set w := H⁻¹.mulVec e with hwdef
  have hw : H.mulVec w = e := by
    rw [hwdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H hdet, Matrix.one_mulVec]
  have h1 := hf w
  rw [hw] at h1
  have hs : e ⬝ᵥ w = ∑ p, w p * e p := by
    simp [dotProduct, mul_comm]
  rw [hs]
  set s := ∑ p, w p * e p with hsdef
  have hcs : s ^ 2 ≤ (∑ p, e p ^ 2) * ∑ p, w p ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w e
    rw [mul_comm (∑ p, e p ^ 2)]
    exact this
  have hA : 0 ≤ ∑ p, e p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hB : 0 ≤ ∑ p, w p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hs0 : 0 ≤ s := (mul_nonneg hlam.le hB).trans h1
  rw [abs_of_nonneg hs0, le_div_iff₀ hlam]
  rcases hs0.eq_or_lt with h | hpos
  · rw [← h, zero_mul]
    exact hA
  · refine le_of_mul_le_mul_left ?_ hpos
    have h2 := mul_le_mul_of_nonneg_left h1 hA
    nlinarith [mul_le_mul_of_nonneg_left hcs hlam.le]
end Inverse
private theorem exists_abs_wickPairingSum_le (q : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (G : Fin q → Fin q → ℝ) (M : ℝ), 1 ≤ M →
    (∀ i j, |G i j| ≤ M) → |wickPairingSum G| ≤ K * M ^ q := by
  classical
  refine ⟨(Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin q)))).card, by positivity, fun G M hM hG => ?_⟩
  unfold wickPairingSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ π ∈ (Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin q)))),
      |if ∀ B ∈ π.parts, B.card = 2 then
        ∏ B ∈ π.parts, (if h : B.Nonempty then G (B.min' h) (B.max' h) else 1) else 0| ≤ M ^ q := by
    intro π _
    have hM0 : (0 : ℝ) ≤ M := by linarith
    split_ifs with hπ
    · rw [Finset.abs_prod]
      have h1 : ∏ B ∈ π.parts, |if h : B.Nonempty then G (B.min' h) (B.max' h) else 1| ≤ ∏ _B ∈ π.parts, M := by
        refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun B _ => ?_
        split_ifs with h
        · exact hG _ _
        · simpa using hM
      refine h1.trans ?_
      rw [Finset.prod_const]
      refine pow_le_pow_right₀ hM ?_
      simpa using π.card_parts_le_card
    · simpa using pow_nonneg hM0 q
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul]
private theorem sixteen_le_frameRadius {x : ℝ} (hx : (2 : ℝ) ^ 1600 ≤ x) : 16 ≤ frameRadius x := by
  have h1 : (2 : ℝ) ^ 16 ≤ x ^ (1 / 100 : ℝ) := by
    have h2 : ((2 : ℝ) ^ 1600) ^ (1 / 100 : ℝ) ≤ x ^ (1 / 100 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hx (by norm_num)
    have e : ((2 : ℝ) ^ 1600) ^ (1 / 100 : ℝ) = 2 ^ 16 := by
      rw [← Real.rpow_natCast 2 1600, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast 2 16]
      norm_num
    rwa [e] at h2
  have h3 : (2 ^ 16 : ℕ) ≤ ⌈x ^ (1 / 100 : ℝ)⌉₊ := by
    have h4 : ((2 ^ 16 : ℕ) : ℝ) ≤ (⌈x ^ (1 / 100 : ℝ)⌉₊ : ℝ) :=
      calc ((2 ^ 16 : ℕ) : ℝ) = (2 : ℝ) ^ 16 := by norm_num
        _ ≤ _ := h1.trans (Nat.le_ceil _)
    exact Nat.cast_le.1 h4
  unfold frameRadius
  rw [Nat.le_div_iff_mul_le (by positivity)]
  calc 16 * 2 ^ 11 ≤ 2 ^ 16 := by norm_num
    _ ≤ _ := h3
variable {F : BlockFrame}
private theorem coldExpansionMoments_of_gaussianApprox (Tb : ParameterAssignment) (c : ColdChainParameters) (nss : ℕ) (y : ℝ)
    (hD : Tb.Admissible) (hties : Tb.Compatible c) (hy : Tb.floorMin ≤ y)
    (hsec : GaussianMomentApproxAt (Tb.stepParamsAt c nss y))
    (hH : frameHessianCoerciveLocalStatement) (hE : interpolationAtEndpoints) :
    coldCoordinateMomentsAt (Tb.stepParamsAt c nss y) := by
  classical
  intro Q
  obtain ⟨C, hC⟩ := hsec (2 * Q)
  obtain ⟨K, hK0, hK⟩ := exists_abs_wickPairingSum_le (2 * Q)
  obtain ⟨C₀, -, hHess⟩ := hH Tb c hD hties
  have hlam : 0 < Tb.lam := hD.chain.2.2.1
  have hσ : 0 < Tb.threshold := hD.σ_pos
  have hMpos : 0 < 1 / Tb.lam := by positivity
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 1 + 1 / Tb.lam := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by linarith
  refine ⟨3 ^ Q * (3 * (K * M ^ (2 * Q) + |C|)), fun t x f F V b hx hrow htor hcold => ?_⟩
  have hx16 : (2 : ℝ) ^ 1600 ≤ x := ((le_max_right _ _).trans hy).trans hx
  have hx1 : 1 ≤ x := le_trans (one_le_pow₀ (by norm_num)) hx16
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hm : 16 ≤ frameRadius x := sixteen_le_frameRadius hx16
  have hchain : IsBlockTorus Tb.side F := by
    obtain ⟨hL, -, n, hs, hn⟩ := htor
    have h1 : Tb.n₀ ≤ n := hn
    have h2 := hD.n₀_ge
    exact ⟨hL, n, by omega, hs⟩
  obtain ⟨-, hfloor, -⟩ := hHess F (frameRadius x) V hchain hm hcold
  have hρA : c.ρA = Tb.ρA := hties.2.2.1
  have hfloor' : ∀ u : ChartCoordinate F → ℝ, Tb.lam * ∑ p, u p ^ 2 ≤
      ∑ p, u p * (frameHessian Tb.coupling c.ρA (frameRadius x) V).mulVec u p := by
    rw [hρA]
    exact hfloor
  have hcold' : IsSmallCurvature (9 / 8 * (Tb.stepParamsAt c nss y).σ) V := fun p hp =>
    (hcold p hp).trans_le (by
      show Tb.threshold ≤ 9 / 8 * Tb.threshold
      linarith)
  have hΨ : (coldHalfLawAt (Tb.stepParamsAt c nss y) x f).exponent V =
      stepExponent false Tb.coupling c.ρA x (frameRadius x) f 1 V := by
    funext η
    have h1 := (hE F false Tb.coupling c.ρA 0 x 0 (frameRadius x) V).2.2.2.2.2.1 f η
    exact show familyLawExponent 1 Tb.coupling c.ρA x (frameRadius x) f V η =
        stepExponent false Tb.coupling c.ρA x (frameRadius x) f 1 V η from by
      simpa [segmentEnd] using h1
  have hpow : 0 < x ^ Q := by positivity
  have hcoord : ∀ i : Fin 3, ballExpectation (cutoffFactor (Tb.stepParamsAt c nss y).ballRadius
      (Tb.stepParamsAt c nss y).p)
      ((coldHalfLawAt (Tb.stepParamsAt c nss y) x f).exponent V) (fun η => η b i ^ (2 * Q)) ≤
      (K * M ^ (2 * Q) + |C|) * (x ^ Q)⁻¹ := by
    intro i
    let l : Fin (2 * Q) → ChartCoordinate F → ℝ := fun _ => Pi.single (b, i) 1
    have h := hC t x f F V hx hrow htor hcold' l
    have hsum1 : ∑ p, |(Pi.single (b, i) 1 : ChartCoordinate F → ℝ) p| = 1 := by
      rw [Finset.sum_eq_single (b, i)]
      · simp
      · intro p _ hp
        simp [hp]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hsq1 : ∑ p, (Pi.single (b, i) 1 : ChartCoordinate F → ℝ) p ^ 2 = 1 := by
      rw [Finset.sum_eq_single (b, i)]
      · simp
      · intro p _ hp
        simp [hp]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hlin : ∀ η : StepVariable (finiteCells F), ∏ j, linearFunctional (l j) η = η b i ^ (2 * Q) := by
      intro η
      have e : linearFunctional (Pi.single (b, i) 1 : ChartCoordinate F → ℝ) η = η b i := by
        unfold linearFunctional
        rw [Finset.sum_eq_single (b, i)]
        · simp
        · intro p _ hp
          simp [hp]
        · intro h
          exact absurd (Finset.mem_univ _) h
      simp only [l, e, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hone : ∏ j, ∑ p, |l j p| = 1 := by
      simp only [l, hsum1, Finset.prod_const_one]
    have hG : ∀ j j', |l j ⬝ᵥ Matrix.mulVec
        (frameHessian (Tb.stepParamsAt c nss y).a (Tb.stepParamsAt c nss y).chainParams.ρA
          (frameRadius x) V)⁻¹ (l j')| ≤ M := by
      intro j j'
      have h1 := abs_dotProduct_inv_mulVec_le hlam hfloor' (Pi.single (b, i) 1 : ChartCoordinate F → ℝ)
      rw [hsq1] at h1
      refine le_trans h1 ?_
      rw [hM]
      linarith
    have hP := hK _ M hM1 hG
    rw [hone, mul_one] at h
    simp only [hlin] at h
    have ea : x ^ (-((2 * Q : ℕ) : ℝ) / 2) = (x ^ Q)⁻¹ := by
      rw [show -((2 * Q : ℕ) : ℝ) / 2 = -(Q : ℝ) by push_cast; ring, Real.rpow_neg hx0.le, Real.rpow_natCast]
    have eb : x ^ (-(((2 * Q : ℕ) : ℝ) + 1) / 2) ≤ (x ^ Q)⁻¹ := by
      rw [← ea]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
    have eb0 : 0 ≤ x ^ (-(((2 * Q : ℕ) : ℝ) + 1) / 2) := by positivity
    rw [ea] at h
    have hinv : 0 ≤ (x ^ Q)⁻¹ := by positivity
    rw [hΨ]
    show cutoffMean (Tb.stepParamsAt c nss y).ballRadius (Tb.stepParamsAt c nss y).p
      (stepExponent false Tb.coupling c.ρA x (frameRadius x) f 1 V) (fun η => η b i ^ (2 * Q)) ≤ _
    have h2 := (abs_le.1 h).2
    have h3 : (x ^ Q)⁻¹ * wickPairingSum (fun j j' => l j ⬝ᵥ Matrix.mulVec
        (frameHessian (Tb.stepParamsAt c nss y).a (Tb.stepParamsAt c nss y).chainParams.ρA
          (frameRadius x) V)⁻¹ (l j')) ≤
        (x ^ Q)⁻¹ * (K * M ^ (2 * Q)) :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans hP) hinv
    have h4 : C * x ^ (-(((2 * Q : ℕ) : ℝ) + 1) / 2) ≤ |C| * (x ^ Q)⁻¹ :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) eb0).trans (mul_le_mul_of_nonneg_left eb (abs_nonneg C))
    have h5 := h2.trans h4
    have h6 := sub_le_iff_le_add.1 h5
    refine h6.trans ?_
    nlinarith
  show ballExpectation (cutoffFactor (Tb.stepParamsAt c nss y).ballRadius (Tb.stepParamsAt c nss y).p)
      ((coldHalfLawAt (Tb.stepParamsAt c nss y) x f).exponent V) (fun η => ‖η b‖ ^ (2 * Q)) ≤ _
  refine (ballExpectation_norm_pow_le _ _ _ b Q).trans ?_
  have hs : ∑ i : Fin 3, ballExpectation (cutoffFactor (Tb.stepParamsAt c nss y).ballRadius
      (Tb.stepParamsAt c nss y).p)
      ((coldHalfLawAt (Tb.stepParamsAt c nss y) x f).exponent V) (fun η => η b i ^ (2 * Q)) ≤
      3 * ((K * M ^ (2 * Q) + |C|) * (x ^ Q)⁻¹) := by
    refine (Finset.sum_le_sum fun i _ => hcoord i).trans ?_
    simp
  calc _ ≤ 3 ^ Q * (3 * ((K * M ^ (2 * Q) + |C|) * (x ^ Q)⁻¹)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring
theorem coldHalfLawMoments (hH : frameHessianCoerciveLocalStatement)
    (hE : interpolationAtEndpoints) : coldHalfLawMomentsStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L _ _ T _ _ hD _ hHalf _ _ => ⟨T.floorMin, fun y hy _ _ => ?_⟩⟩
  obtain ⟨c, nss, hties, h⟩ := hHalf
  exact ⟨c, nss, hties, coldExpansionMoments_of_gaussianApprox T c nss y hD hties hy
    (h y ((le_max_left _ _).trans hy)).secondOrderMoments hH hE⟩
end ResponseInTheExpansion
end YangMills.Construction
end
