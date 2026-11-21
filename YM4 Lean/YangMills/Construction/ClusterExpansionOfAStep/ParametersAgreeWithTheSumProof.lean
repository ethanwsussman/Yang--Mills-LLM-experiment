import YangMills.Construction.ClusterExpansionOfAStep.ParametersAgreeWithTheSum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusLumps RenormalizationStepParameters
theorem parameterFamilyMeetsClassSum_holds : ParameterChoiceMeetsClassSum := by
  intro T hT CE c y hCE hy hfl
  have hy1 : (1 : ℝ) ≤ y := by
    have h1 : T.floorMin ≤ y := hy
    have h2 : (2 : ℝ) ^ 1600 ≤ T.floorMin := le_max_right _ _
    have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ 1600 := one_le_pow₀ (by norm_num)
    exact h3.trans (h2.trans h1)
  have hthr : 0 < T.threshold ^ 2 := by have := hT.σ_pos; positivity
  have hrate : classSumRate (T.stepParameters y) T.cE = T.gasRate := by
    simp only [classSumRate, ParameterAssignment.gasRate, ParameterAssignment.stepParameters]
    ring
  refine
    { cE_pos := hT.cE_pos
      CE_nonneg := hCE
      κ₁_le := min_le_left _ _
      κ₁_le_cE := ?_
      side_ge := ?_
      range_ge := ?_
      log_bound := ?_
      root_le_rate := ?_
      coupling_shift := ?_ }
  · show T.κ₁ * T.threshold ^ 2 ≤ T.cE / 4
    have h : T.κ₁ ≤ T.cE / (4 * T.threshold ^ 2) := min_le_right _ _
    calc T.κ₁ * T.threshold ^ 2 ≤ T.cE / (4 * T.threshold ^ 2) * T.threshold ^ 2 :=
          mul_le_mul_of_nonneg_right h hthr.le
      _ = T.cE / 4 := by
          have hthr0 : T.threshold ≠ 0 := hT.σ_pos.ne'
          field_simp
  · show 80 ≤ T.side
    have := hT.L_ge
    omega
  · have h6 := (hfl y le_rfl).range_ge
    have h7 : (2 : ℝ) ^ 17 ≤ (clusterRange y : ℝ) := by
      have : (0 : ℝ) ≤ 2 ^ 18 * CE := by positivity
      linarith
    have h8 : (2 ^ 17 : ℕ) ≤ clusterRange y := by exact_mod_cast h7
    show 2 ^ 16 + 1 ≤ clusterRange y
    omega
  · intro x hx
    have hx' : y ≤ x := hx
    have h8 := (hfl x hx').log_powers.2.1
    have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hb : 0 ≤ (clusterRange x : ℝ) ^ 12 * Real.log x := by positivity
    have : 2 ^ 18 * CE * ((clusterRange x : ℝ) ^ 12 * Real.log x) ≤
        (2 ^ 18 * CE + 2 ^ 17) * ((clusterRange x : ℝ) ^ 12 * Real.log x) :=
      mul_le_mul_of_nonneg_right (by norm_num) hb
    nlinarith
  · intro x hx
    rw [hrate]
    exact (hfl x hx).log_powers.2.2
  · intro x x' hx hxx
    obtain ⟨h1, h2, h3, h4⟩ := (hfl x hx).stable_nearby.2 x' hxx
    exact ⟨h2, h1, h3, h4⟩
end YangMills.Construction.ClusterExpansionOfAStep
end
