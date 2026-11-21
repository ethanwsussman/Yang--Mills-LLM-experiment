import YangMills.Construction.SummableBoundsOfTheFlow.AllowanceOfARecursion
import YangMills.Construction.SummableBoundsOfTheFlow.LineUpToTheNextLevel
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeOfTheOneLoopNumbers
import YangMills.Construction.SummableBoundsOfTheFlow.SummabilityBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CouplingFlow
open TorusLumps StepReturn FamilyNorms OneLoopSlope
theorem slopeConst_gt_ten {L : ℕ} (hL : 2 ^ 40 ≤ L) : 10 < slopeConst L := by
  have hcast : ((2 : ℝ) ^ 40) ≤ L := by exact_mod_cast hL
  have hlog : Real.log ((2 : ℝ) ^ 40) ≤ Real.log L := Real.log_le_log (by positivity) hcast
  rw [Real.log_pow] at hlog
  have htwo := Real.log_two_gt_d9
  have hpi := Real.pi_lt_d2
  have hpi_pos := Real.pi_pos
  have hpi_sq : Real.pi ^ 2 < 3.15 ^ 2 := pow_lt_pow_left₀ hpi hpi_pos.le (by norm_num)
  unfold slopeConst
  rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
  norm_num at hlog htwo hpi_sq ⊢
  nlinarith
theorem expansionCoupling_eq_of_hasExpansion {P : TorusLumps.StepParameters} (hret : ExpansionReturnsAt P)
    {t : ℕ} {x x' : ℝ} {D : TorusFunctional} (hx : P.y₁ ≤ x)
    (hD : HasExpansion P t x D) (hx' : HasExpansion P (t + 1) x' (kernelImage P x D)) :
    expansionCoupling P t x D = x' := by
  obtain ⟨x₁, -, huniq⟩ := hret t x D hx hD
  have hex : ∃ x' : ℝ, HasExpansion P (t + 1) x' (kernelImage P x D) := ⟨x', hx'⟩
  unfold expansionCoupling
  obtain ⟨-, f₁, hc₁, -⟩ := hex.choose_spec
  obtain ⟨-, f₂, hc₂, -⟩ := hx'
  rw [dif_pos hex, huniq _ _ hc₁, huniq _ _ hc₂]
variable {T : RenormalizationStepParameters.ParameterAssignment} {y C₁ M : ℝ}
theorem hasRefinedExpansion_along_flow (hF : RefinedExpansionHolds T y C₁ M) {β : ℝ} (hβ : y ≤ β) :
    ∀ t : ℕ, (∀ l < t, y ≤ couplingAt (T.stepParameters y) β l) →
    HasRefinedExpansion (T.stepParameters y) (2 * C₁) (FamilyNorms.ParameterAssignment.reference T t) t
      (couplingAt (T.stepParameters y) β t) (couplingFlow (T.stepParameters y) β t).2 := by
  intro t
  induction t with
  | zero => intro _; exact hF.wilson β hβ
  | succ t ih =>
    intro hl
    have hD := ih fun l hlt => hl l (Nat.lt_succ_of_lt hlt)
    have hyt := hl t (Nat.lt_succ_self t)
    obtain ⟨x', hx', -⟩ := hF.refined t _ _ hyt hD
    have he : expansionCoupling (T.stepParameters y) t (couplingAt (T.stepParameters y) β t)
        (couplingFlow (T.stepParameters y) β t).2 = x' :=
      expansionCoupling_eq_of_hasExpansion hF.returns hyt hD.1 hx'.1
    have hsucc : couplingAt (T.stepParameters y) β (t + 1) = x' := he
    rw [hsucc]
    exact hx'
theorem followsFlowAbove_couplingAt (hF : RefinedExpansionHolds T y C₁ M) {X : ℝ} (hX : y ≤ X) (β : ℝ) :
    FollowsFlowAbove (FamilyNorms.ParameterAssignment.oneLoop T) (FamilyNorms.ParameterAssignment.secondStep T)
      (C₁ * (2 * C₁ + 1)) X (couplingAt (T.stepParameters y) β) := by
  intro l hst
  have h0 : y ≤ couplingAt (T.stepParameters y) β 0 := hX.trans (hst 0 (Nat.zero_le _))
  have hβ : y ≤ β := h0
  have hD := hasRefinedExpansion_along_flow hF hβ l fun j hj => hX.trans (hst j hj.le)
  have hyl := hX.trans (hst l le_rfl)
  obtain ⟨x', hx', hr⟩ := hF.refined l _ _ hyl hD
  have hsucc : couplingAt (T.stepParameters y) β (l + 1) = x' :=
    expansionCoupling_eq_of_hasExpansion hF.returns hyl hD.1 hx'.1
  unfold stepRemainder
  rw [hsucc]
  exact hr
theorem flowBoundExists_of (h₁ : RefinedExpansionReturns) (h₂ : OneLoopCoefficientsHaveSlope)
    (h₃ : AllowanceOfRecursionHolds) (h₄ : TwoSidedDropToNextLevel) : FlowEstimateExists := by
  obtain ⟨Q, hQ, fL, cR, cS, fN, fC, C₀, hR0, hS0, hAll⟩ := h₁
  refine ⟨Q, hQ, fL, cR, cS, fN, fC, C₀, hR0, hS0, ?_⟩
  intro T hD a1 a2 a3 a4 a5 a6 hOn
  obtain ⟨y₀, C₁, M, hFy⟩ := hAll T hD a1 a2 a3 a4 a5 a6 hOn
  refine ⟨y₀, fun y hy => ?_⟩
  have hF := hFy y hy
  have hL40 : 2 ^ 40 ≤ T.side := hD.L_ge
  obtain ⟨c, hc⟩ := h₂ T.coupling hD.a_ge T.side hD.L_odd (le_trans (by norm_num) hL40)
  have hs : HasAverageSlope (FamilyNorms.ParameterAssignment.oneLoop T) (slopeConst T.side) c := hc T hD rfl rfl
  have hbig : 10 < slopeConst T.side := slopeConst_gt_ten hL40
  have hc₀ : 0 < slopeConst T.side := by linarith
  have hM : 0 ≤ M := (abs_nonneg _).trans (hF.secondStep_le 0)
  have hC : 0 < C₁ := hF.C₁_pos
  have hR : 0 ≤ C₁ * (2 * C₁ + 1) := by positivity
  obtain ⟨X₁, hline⟩ := h₄ (FamilyNorms.ParameterAssignment.oneLoop T) (FamilyNorms.ParameterAssignment.secondStep T)
    (slopeConst T.side) c M (C₁ * (2 * C₁ + 1)) hc₀ hM hR hF.secondStep_le hs
  obtain ⟨X, Cr, v₀, mw, hyX', hX8, hCr, hCrs, hmw, hv₀, hflow, hall⟩ :=
    h₃ (FamilyNorms.ParameterAssignment.oneLoop T) (FamilyNorms.ParameterAssignment.secondStep T) (slopeConst T.side) c M
      (C₁ * (2 * C₁ + 1)) (max y X₁) hc₀ hM hR hF.secondStep_le hs
  have hyX : y ≤ X := (le_max_left _ _).trans hyX'
  have hX₁ : X₁ ≤ X := (le_max_right _ _).trans hyX'
  have hbud := fun β => hall _ (followsFlowAbove_couplingAt hF hyX β)
  refine ⟨c, M, C₁ * (2 * C₁ + 1), X, Cr, v₀, mw, hF.admissible, hF.returns, hbig, hs, hF.secondStep_le, hyX, hX8,
    hCr, hCrs, hmw, hv₀, hflow, hbud, ?_, ?_, ?_, ?_⟩
  · intro β i j hij hl
    refine hline X hX₁ _ i j hij hl fun l hlt => ?_
    exact followsFlowAbove_couplingAt hF hyX β l fun m hm => hl m (lt_of_le_of_lt hm hlt)
  · intro β t hβ hl
    exact (hasRefinedExpansion_along_flow hF (hyX.trans hβ) t fun l hlt => hyX.trans (hl l hlt)).1
  · intro K g hg hv
    obtain ⟨β, ⟨hvK, hfl⟩, -⟩ := hflow.existsUnique_value K _ hv
    have hB := hbud β
    have e0 : couplingAt (T.stepParameters y) β 0 = β := rfl
    have hfl' : ∀ l ≤ K, X + 1 ≤ flow (FamilyNorms.ParameterAssignment.oneLoop T)
        (FamilyNorms.ParameterAssignment.secondStep T) (couplingAt (T.stepParameters y) β 0) l := by
      rw [e0]; exact hfl
    have hst := hB.staysAbove_of_flow K hfl'
    obtain ⟨-, h2, -⟩ := hB.near_value K _ hv (by rw [e0]; exact hvK) hfl'
    refine ⟨β, hst, h2.trans ?_⟩
    have hxK := hst K le_rfl
    have hX0 : 0 < X := by linarith
    have h3 : couplingAt (T.stepParameters y) β K ^ (-(1 / 4) : ℝ) ≤ X ^ (-(1 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hX0 hxK (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left h3 hCr]
  · intro β t hst hmt hunit
    have hsteps : ∀ l ≤ t, couplingAt (T.stepParameters y) β l = couplingAt (T.stepParameters y) β 0 - l := by
      intro l
      induction l with
      | zero => intro _; simp
      | succ l ih =>
        intro hl
        rw [hunit l (by omega), ih (by omega)]
        push_cast
        ring
    have hw := ((hbud β).boundsUpTo t hst).drop_window 0 mw le_rfl (by omega)
    rw [zero_add, hsteps mw hmt] at hw
    have hmw0 : (1 : ℝ) ≤ mw := by exact_mod_cast hmw
    nlinarith
end YangMills.Construction.CouplingFlow
end
