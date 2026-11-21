import YangMills.Construction.SummableBoundsOfTheFlow.MeanOfASlopeOfTheCut
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
open MeasureTheory
namespace YangMills.Construction.Estimates
theorem cutoffSlopeMeanBound : cutoffSlopeMeanBoundStatement := by
  intro ρ p Cr n N ι _ _ x κ C Cq₀ d Φ S e E₀ hE hx hS hL he heb
  set D : ColdStepAtMirrorFrames.BondField ι → ℝ :=
    ColdStepAtMirrorFrames.ballDensity (ColdStepAtMirrorFrames.cutoffFactor ρ p) Φ with hD
  have hcutNonneg : ∀ u, 0 ≤ ColdStepAtMirrorFrames.cutoffFactor ρ p u := fun u => by
    unfold ColdStepAtMirrorFrames.cutoffFactor
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hDnonneg : ∀ η, 0 ≤ D η := fun η =>
    mul_nonneg (Finset.prod_nonneg fun _ _ => hcutNonneg _) (Real.exp_pos _).le
  have hZ : 0 ≤ ∫ η, D η := integral_nonneg hDnonneg
  have hMoment := fun b => hL.cutoff_deriv_moments 1 1 N b le_rfl le_rfl
  have hTerm : ∀ (b : ι) (v : ColdStepAtMirrorFrames.BondVector) (w : ColdStepAtMirrorFrames.BondVector),
      |deriv p ‖v‖ * ‖v‖⁻¹ * ⟪v, w⟫| ≤ |deriv p ‖v‖| * ‖w‖ := by
    intro b v w
    by_cases hv : v = 0
    · simp only [hv, inner_zero_left, mul_zero, abs_zero]
      positivity
    · have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
      calc |deriv p ‖v‖| * ‖v‖⁻¹ * |⟪v, w⟫|
          ≤ |deriv p ‖v‖| * ‖v‖⁻¹ * (‖v‖ * ‖w‖) :=
            mul_le_mul_of_nonneg_left (abs_real_inner_le_norm v w) (by positivity)
        _ = |deriv p ‖v‖| * ‖w‖ := by
            field_simp
  have hPointwise : ∀ η, |cutoffSlope p e η| ≤ E₀ * ∑ b ∈ S, |iteratedDeriv 1 p ‖η b‖| ^ 1 := by
    intro η
    unfold cutoffSlope
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun b _ hb => by
      rw [he b hb]
      simp), Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    refine (hTerm b _ _).trans ?_
    rw [iteratedDeriv_one, pow_one, mul_comm]
    exact mul_le_mul_of_nonneg_right (heb b) (abs_nonneg _)
  have hIntegrable : Integrable fun η => E₀ * ∑ b ∈ S, |iteratedDeriv 1 p ‖η b‖| ^ 1 * D η :=
    (integrable_finset_sum _ fun b _ => (hMoment b).1).const_mul E₀
  have hIntegralLe : ∫ η, |cutoffSlope p e η * D η| ≤
      ∫ η, E₀ * ∑ b ∈ S, |iteratedDeriv 1 p ‖η b‖| ^ 1 * D η := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun η => abs_nonneg _) hIntegrable
      (Filter.Eventually.of_forall fun η => ?_)
    show |cutoffSlope p e η * D η| ≤ E₀ * ∑ b ∈ S, |iteratedDeriv 1 p ‖η b‖| ^ 1 * D η
    rw [abs_mul, abs_of_nonneg (hDnonneg η), ← Finset.sum_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hPointwise η) (hDnonneg η)
  have hSplit : ∫ η, E₀ * ∑ b ∈ S, |iteratedDeriv 1 p ‖η b‖| ^ 1 * D η =
      E₀ * ∑ b ∈ S, ∫ η, |iteratedDeriv 1 p ‖η b‖| ^ 1 * D η := by
    rw [integral_const_mul, integral_finsetSum _ fun b _ => (hMoment b).1]
  have hSum : ∑ b ∈ S, ColdStepAtMirrorFrames.ballExpectation (ColdStepAtMirrorFrames.cutoffFactor ρ p) Φ
      (fun η => |iteratedDeriv 1 p ‖η b‖| ^ 1) ≤ n * (|Cr 1 1 N| * (x ^ N)⁻¹) := by
    have hInv : 0 ≤ (x ^ N)⁻¹ := by positivity
    calc ∑ b ∈ S, ColdStepAtMirrorFrames.ballExpectation (ColdStepAtMirrorFrames.cutoffFactor ρ p) Φ
          (fun η => |iteratedDeriv 1 p ‖η b‖| ^ 1)
        ≤ ∑ _b ∈ S, |Cr 1 1 N| * (x ^ N)⁻¹ := Finset.sum_le_sum fun b _ =>
          (hMoment b).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hInv)
      _ = S.card * (|Cr 1 1 N| * (x ^ N)⁻¹) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hS) (by positivity)
  unfold ColdStepAtMirrorFrames.ballExpectation
  rw [abs_div, abs_of_nonneg hZ]
  calc |∫ η, cutoffSlope p e η *
        ColdStepAtMirrorFrames.ballDensity (ColdStepAtMirrorFrames.cutoffFactor ρ p) Φ η| / ∫ η, D η
      ≤ (∫ η, |cutoffSlope p e η * D η|) / ∫ η, D η :=
        div_le_div_of_nonneg_right (abs_integral_le_integral_abs) hZ
    _ ≤ (E₀ * ∑ b ∈ S, ∫ η, |iteratedDeriv 1 p ‖η b‖| ^ 1 * D η) / ∫ η, D η :=
        div_le_div_of_nonneg_right (by rw [← hSplit]; exact hIntegralLe) hZ
    _ = E₀ * ∑ b ∈ S, ColdStepAtMirrorFrames.ballExpectation (ColdStepAtMirrorFrames.cutoffFactor ρ p) Φ
          (fun η => |iteratedDeriv 1 p ‖η b‖| ^ 1) := by
        rw [mul_div_assoc, Finset.sum_div]
        rfl
    _ ≤ E₀ * (n * (|Cr 1 1 N| * (x ^ N)⁻¹)) := mul_le_mul_of_nonneg_left hSum hE
    _ = _ := by ring
end YangMills.Construction.Estimates
end
