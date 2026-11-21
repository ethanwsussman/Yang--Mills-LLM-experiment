import YangMills.Construction.ResponseInTheExpansion.RemaindersAreSlotsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation
namespace WeightedResponses
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem isOpen_setOf_forall_norm_lt (ρ : ℝ) : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by apply _root_.YangMills.SharedProofs.p5886 <;> assumption
theorem sqrt_mul_rpow_neg_half {x : ℝ} (hx : 0 < x) :
    Real.sqrt x * x ^ (-(1 / 2) : ℝ) = 1 ∧ x * x ^ (-(1 / 2) : ℝ) = Real.sqrt x := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SlotLemmas.sqrt_mul_rpow_neg_half <;> assumption
theorem hasLocalSize_of_bounded_partials (hSz : LocalSizeOfQuadraticBounds) {ρ x lam κ W : ℝ} {d : ι → ι → ℝ}
    {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hx : 0 < x) (hlam : 0 < lam) (hκ : 0 ≤ κ)
    (hW : 0 ≤ W) (hcut : IsCutoff ρ p) (hd : IsPseudoMetricOnBonds d)
    (hconv : IsUniformlyConvexDecaying ρ (x * lam / 4) κ d Ψ K)
    (hsum : ∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W)
    (hslope : ∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖)
    {J : BondField ι → ℝ} {Dd dZ : ι → ℝ} {h : ℝ} (hJ : ContDiffOn ℝ 1 J {η | ∀ b, ‖η b‖ < ρ})
    (hD0 : ∀ b, 0 ≤ Dd b)
    (hh : 0 ≤ h) (hlip : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |J η - J 0| ≤ ∑ b, ‖η b‖ * Dd b)
    (hgrad : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm J b η ≤ Dd b)
    (hsumD : x ^ (-(1 / 2) : ℝ) * ∑ b, Dd b ≤ h)
    (hDb : ∀ b, Dd b ≤ Real.sqrt x * h * Real.exp (-(2 * κ * dZ b))) :
    HasLocalSize ρ (cutoffFactor ρ p) Ψ (fun q => lpMomentConstant lam (1 / 2) W q * 1) x κ h dZ J := by
  obtain ⟨hs1, hs2⟩ := sqrt_mul_rpow_neg_half hx
  set s : ℝ := x ^ (-(1 / 2) : ℝ) with hs
  have hs0 : 0 ≤ s := (Real.rpow_pos_of_pos hx _).le
  set H : BondField ι → ℝ := fun η => J η - J 0 with hH
  have hpn : ∀ b, bondGradNorm H b = bondGradNorm J b := fun b => by
    funext η
    unfold bondGradNorm
    rw [hH, fderiv_sub_const]
  have hHc : ContDiffOn ℝ 1 H {η | ∀ b, ‖η b‖ < ρ} := hJ.sub contDiffOn_const
  have hval : IsQuadraticallyBoundedOnBalls ρ x (1 / 2) 1 h H := by
    refine ⟨fun b => s * Dd b / 2, h, hh, le_rfl, fun b => by have := hD0 b; positivity, ?_, fun η hη => ?_⟩
    · rw [← Finset.sum_div, ← Finset.mul_sum]
      linarith
    · refine (hlip η hη).trans ?_
      have hpt : ∀ b, ‖η b‖ * Dd b ≤ x * (s * Dd b / 2 * ‖η b‖ ^ 2) + s * Dd b / 2 := fun b => by
        have ht : ‖η b‖ ≤ (s * x * ‖η b‖ ^ 2 + s) / 2 := by
          have h1 : 0 ≤ (Real.sqrt x * ‖η b‖ - 1) ^ 2 := sq_nonneg _
          have h2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
          have h3 : 0 ≤ s * (Real.sqrt x * ‖η b‖ - 1) ^ 2 := mul_nonneg hs0 h1
          have h4 : s * (Real.sqrt x * ‖η b‖ - 1) ^ 2 =
              s * (Real.sqrt x * Real.sqrt x) * ‖η b‖ ^ 2 - 2 * (Real.sqrt x * s) * ‖η b‖ + s := by
            ring
          rw [h4, hs1, h2] at h3
          linarith
        calc ‖η b‖ * Dd b ≤ (s * x * ‖η b‖ ^ 2 + s) / 2 * Dd b := mul_le_mul_of_nonneg_right ht (hD0 b)
          _ = _ := by ring
      calc ∑ b, ‖η b‖ * Dd b ≤ ∑ b, (x * (s * Dd b / 2 * ‖η b‖ ^ 2) + s * Dd b / 2) :=
            Finset.sum_le_sum fun b _ => hpt b
        _ = x * ∑ b, s * Dd b / 2 * ‖η b‖ ^ 2 + (s * ∑ b, Dd b) / 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum]
        _ ≤ 1 * (x * ∑ b, s * Dd b / 2 * ‖η b‖ ^ 2 + h) := by
            linarith
  have hgr : ∀ b, IsQuadraticallyBoundedOnBalls ρ x (1 / 2) (Real.sqrt x * 1)
      (h * Real.exp (-(2 * κ * dZ b))) (bondGradNorm H b) := by
    intro b
    refine ⟨fun _ => 0, h * Real.exp (-(2 * κ * dZ b)), by positivity, le_rfl, fun _ => le_rfl, ?_, fun η hη => ?_⟩
    · simp only [Finset.sum_const_zero]
      positivity
    · simp only [zero_mul, Finset.sum_const_zero, mul_zero, zero_add, mul_one]
      have hnn : 0 ≤ bondGradNorm J b η := norm_nonneg _
      rw [hpn, abs_of_nonneg hnn]
      refine (hgrad η hη b).trans ?_
      have := hDb b
      linarith [mul_assoc (Real.sqrt x) h (Real.exp (-(2 * κ * dZ b)))]
  have hres := hSz ι ρ x lam κ W (1 / 2) d Ψ K p hρ hx hlam hκ hW (by norm_num) hcut hd hconv hsum hslope H 1 h dZ
    zero_le_one hh hHc hval hgr
  obtain ⟨-, H₀, hm⟩ := hres
  refine ⟨fun η hη => (hJ.contDiffAt ((isOpen_setOf_forall_norm_lt ρ).mem_nhds hη)).differentiableAt (by simp),
    H₀ + J 0, fun q hq => ?_⟩
  obtain ⟨m1, m2⟩ := hm q hq
  refine ⟨?_, fun b => ?_⟩
  · have e : (fun η => J η - (H₀ + J 0)) = fun η => H η - H₀ := by
      funext η
      simp only [hH]
      ring
    rw [e]
    exact m1
  · rw [← hpn]
    exact m2 b
theorem localSizeOfBoundedPartials_holds (hSz : LocalSizeOfQuadraticBounds) : LocalSizeOfBoundedPartials :=
  fun hρ hx hlam hκ hW hcut hd hconv hsum hslope _ _ _ _ hJ hD0 hh hlip hgrad hsumD hDb =>
    hasLocalSize_of_bounded_partials hSz hρ hx hlam hκ hW hcut hd hconv hsum hslope hJ hD0 hh hlip hgrad hsumD hDb
end WeightedResponses
end YangMills.Construction
end
