import YangMills.Construction.FourPointCondition.LawsAtALevelOfTheWindowProof
import YangMills.Construction.ResponseInTheExpansion.TheFlowHasATower
import YangMills.Construction.ResponseInTheExpansion.TheWindowHasATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusLumps StepReturn RenormalizationStepParameters WeightedResponses Asymptotics Filter
private theorem abs_flow_succ_sub_le {p : StepParameters} (hR : ExpansionReturnsAt p) {β : ℝ}
    (h0 : HasExpansion p 0 β (wilsonWeight β)) (t : ℕ)
    (h : ∀ j ≤ t, p.y₁ ≤ (couplingFlow p β j).1) :
    |(couplingFlow p β (t + 1)).1 - (couplingFlow p β t).1| ≤ 2 * p.B := by apply _root_.YangMills.SharedProofs.p4489 <;> assumption
private theorem flow_sub_linear_le {p : StepParameters} (hR : ExpansionReturnsAt p) {β : ℝ}
    (h0 : HasExpansion p 0 β (wilsonWeight β)) (k K : ℕ)
    (h : ∀ j ≤ k + K, p.y₁ ≤ (couplingFlow p β j).1) :
    ∀ i ≤ K + 1, (couplingFlow p β k).1 - 2 * |p.B| * i ≤ (couplingFlow p β (k + i)).1 := by
  intro i
  induction i with
  | zero =>
    intro _
    simp
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have h2 := abs_flow_succ_sub_le hR h0 (k + i) fun j hj => h j (by omega)
    have h3 := (abs_le.1 h2).1
    have h4 := le_abs_self p.B
    have e : k + (i + 1) = k + i + 1 := by omega
    rw [e]
    push_cast
    nlinarith
private theorem exists_log_sq_threshold (y b : ℝ) (hb : 0 ≤ b) :
    ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → 1 ≤ x ∧ y + b * (2 * Real.log x ^ 2 + 1) ≤ x := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).def (c := 1 / (4 * b + 1)) (by positivity)
  have h2 := (h.and (eventually_ge_atTop (max 1 (2 * (y + b))))).and (eventually_ge_atTop (1 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 h2
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨⟨h3, h4⟩, h5⟩ := hx₀ x hx
  refine ⟨h5, ?_⟩
  have h6 : 2 * (y + b) ≤ x := (le_max_right _ _).trans h4
  have h7 : Real.log x ^ 2 ≤ 1 / (4 * b + 1) * x := by
    have e1 : ‖Real.log x ^ 2‖ = Real.log x ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have e2 : ‖id x‖ = x := by
      rw [id, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rwa [e1, e2] at h3
  have h8 : (4 * b + 1) * Real.log x ^ 2 ≤ x := by
    have := mul_le_mul_of_nonneg_left h7 (show (0 : ℝ) ≤ 4 * b + 1 by positivity)
    rwa [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
  nlinarith
theorem windowTowerExists (hTow : TowerAlongFlowStatement) : windowTowerExistsStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hr, H⟩ := hTow a ha
  refine ⟨L₀, rt₀, C₀, hr, fun L hodd hL Tb hTa hTL hD hC hHf hrt hc => ?_⟩
  obtain ⟨y₀, Hy⟩ := H L hodd hL Tb hTa hTL hD hC hHf hrt hc
  refine ⟨y₀, fun y hy hR hW => ?_⟩
  obtain ⟨hfit, hfl, k₃⟩ := Hy y hy hR hW
  refine ⟨hfit, hfl, ?_⟩
  obtain ⟨x₀, hx₀⟩ := exists_log_sq_threshold (Tb.stepParameters y).y₁
    (2 * |(Tb.stepParameters y).B|) (by positivity)
  refine ⟨x₀, fun β k hk hrun => ?_⟩
  obtain ⟨h1, h2⟩ := hx₀ _ hk
  set x := (couplingFlow (Tb.stepParameters y) β k).1 with hx
  set M := chainDepth x with hM
  have hβ : y ≤ β := hrun 0 (by omega)
  have h0 := hW β hβ
  have hab := flow_sub_linear_le hR h0 k (2 * M) hrun
  refine k₃ β (k + 2 * M) fun j hj => ?_
  by_cases hj' : j ≤ k + 2 * M
  · exact hrun j hj'
  · have e : j = k + (2 * M + 1) := by omega
    rw [e]
    have h3 := hab (2 * M + 1) le_rfl
    have h4 : (M : ℝ) ≤ Real.log x ^ 2 := Nat.floor_le (by positivity)
    push_cast at h3
    have h5 : 0 ≤ |(Tb.stepParameters y).B| := abs_nonneg _
    have h6 : 2 * |(Tb.stepParameters y).B| * (2 * (M : ℝ) + 1) ≤
        2 * |(Tb.stepParameters y).B| * (2 * Real.log x ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
end YangMills.Construction.ResponseInTheExpansion
end
