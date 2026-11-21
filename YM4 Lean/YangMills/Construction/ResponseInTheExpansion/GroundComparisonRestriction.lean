import YangMills.Construction.ClusterExpansionOfAStep.TwoSystemsOfTheGasProof
import YangMills.Construction.ResponseInTheExpansion.TwoGroundsAtOscillationsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GroundComparisonRestriction
open Dobrushin StepGas StepSettings RenormalizationStepParameters TorusFields
theorem scalar_bound {ρ c x W : ℝ} {N m : ℕ}
    (hρ : 0 ≤ ρ) (hcx : 0 ≤ c * x) (hW : 0 ≤ W)
    (hWx : 32 * W ≤ c * x) (hNm : 2 * m ≤ N) :
    (16 * 2 * Real.exp (-(2 * ρ * ((N - m : ℕ) : ℝ))) +
      0 * Real.exp (ρ * (N : ℝ))) * (Real.exp (-(8 * c * x)) * W) ≤
      Real.exp (-(2 * c * x) - ρ * (N : ℝ)) := by
  have hN : (N : ℝ) ≤ 2 * ((N - m : ℕ) : ℝ) := by
    exact_mod_cast (show N ≤ 2 * (N - m) by omega)
  have hfar : Real.exp (-(2 * ρ * ((N - m : ℕ) : ℝ))) ≤
      Real.exp (-(ρ * (N : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h32 : 32 * W ≤ Real.exp (6 * c * x) :=
    hWx.trans ((show c * x ≤ 6 * c * x + 1 by nlinarith).trans
      (Real.add_one_le_exp (6 * c * x)))
  have hpref : 32 * W * Real.exp (-(8 * c * x)) ≤ Real.exp (-(2 * c * x)) := by
    calc
      _ ≤ Real.exp (6 * c * x) * Real.exp (-(8 * c * x)) :=
        mul_le_mul_of_nonneg_right h32 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  simp only [zero_mul, add_zero]
  calc
    _ = (32 * W * Real.exp (-(8 * c * x))) *
        Real.exp (-(2 * ρ * ((N - m : ℕ) : ℝ))) := by ring
    _ ≤ Real.exp (-(2 * c * x)) * Real.exp (-(ρ * (N : ℝ))) :=
      mul_le_mul hpref hfar (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, sub_eq_add_neg]
theorem oscillationControlled_of_readsComponentsAt {R : StepSetup} {n : ℕ} [NeZero n]
    (G : GasGround R n) (Y : TorusSite n) {F : G.Config → ℝ}
    (hF : G.ReadsComponentsAt Y F) :
    G.pairConstraint.OscillationControlled (G.coreWeightFrom Y) 2 F := by
  classical
  have h := GasComparison.isLocalObservable_of_readsComponentsAt G Y hF
  refine ⟨by norm_num, hF.measurable, ⟨1, hF.abs_le_one⟩, ?_⟩
  refine ⟨fun i => mul_nonneg (by norm_num) (GasComparison.coreWeightFrom_pos G Y i).le, ?_⟩
  intro i σ σ' hσ hσ' hag
  refine (h.oscillation.2 i σ σ' hσ hσ' hag).trans ?_
  dsimp only
  split_ifs with hi
  · linarith [h.one_le_weight i hi]
  · exact mul_nonneg (by norm_num) (GasComparison.coreWeightFrom_pos G Y i).le

theorem expectationsClose_of_oscillation
    (h : ResponseInTheExpansion.twoGroundsOscillationComparison) :
    StepGas.ExpectationsCloseOfGroundsAgreeNear := by
  obtain ⟨rt₀, hrt₀, H⟩ := h
  refine ⟨rt₀, hrt₀, fun T hT hrt => ?_⟩
  obtain ⟨y₀, H⟩ := H T hT hrt
  have hκ₁ : 0 < T.κ₁ := lt_min (div_pos hT.κ_pos (by norm_num))
    (div_pos hT.cE_pos (by have := hT.σ_pos; positivity))
  have hch : 0 < T.gasRate := by
    have h1 : 0 < T.κ * T.threshold ^ 2 := mul_pos hT.κ_pos (pow_pos hT.σ_pos 2)
    have h2 : 0 < T.κ₁ * T.threshold ^ 2 := mul_pos hκ₁ (pow_pos hT.σ_pos 2)
    exact mul_pos (by norm_num) (lt_min hT.cE_pos (lt_min h1 h2))
  let W := ResponseInTheExpansion.blockSumConstant (T.rt / 2 ^ 8)
  have hW : 0 ≤ W := by
    dsimp [W, ResponseInTheExpansion.blockSumConstant]
    positivity
  refine ⟨max y₀ ((32 * W + 1) / T.gasRate),
    fun y hy R hR hx' n n' _ _ G G' Y Y' N A A' F F' hG hG' hN hAg hBl hFr hFr' hlink => ?_⟩
  obtain ⟨hy₀, hyW⟩ := max_le_iff.mp hy
  have hxW : 32 * W + 1 ≤ T.gasRate * R.coupling := by
    have hdiv := hyW.trans hR.le_coupling
    rw [div_le_iff₀ hch] at hdiv
    nlinarith
  have hcx : 0 ≤ T.gasRate * R.coupling := by linarith
  obtain ⟨g, -, Hg⟩ := H y hy₀ R hR hx' n n' G G' Y Y' N A A' hG hG' hN hAg hBl
  have hab : F G.allVacant = F' G'.allVacant := by
    apply hlink
    constructor <;> intro i hi hne <;> exact (hne rfl).elim
  have hlink' : ∀ τ : g.Config, G.pairConstraint.IsAdmissible (g.extendFirst τ) →
      |F (g.extendFirst τ) - F' (g.extendSecond τ)| ≤ 0 := by
    intro τ _
    rw [hlink _ _ (GasComparison.componentsMatch_extend g τ), sub_self, abs_zero]
  have main := Hg F F' 2 0 le_rfl
    (oscillationControlled_of_readsComponentsAt G Y hFr)
    (oscillationControlled_of_readsComponentsAt G' Y' hFr') hlink' hab
  have hbound := scalar_bound (ρ := T.rt / 2 ^ 8) (c := T.gasRate)
    (x := R.coupling) (W := W) (N := N) (m := R.frameReach)
    (by have := hT.rt_pos; positivity) hcx hW (by linarith) (by omega)
  exact main.trans (hbound.trans_eq (by congr 1 <;> ring))
end YangMills.Construction.GroundComparisonRestriction
end
