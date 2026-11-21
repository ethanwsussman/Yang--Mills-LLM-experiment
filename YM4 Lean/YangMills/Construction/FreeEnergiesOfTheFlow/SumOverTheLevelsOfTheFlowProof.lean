import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParametersProof
import YangMills.Construction.FreeEnergiesOfTheFlow.SumOverTheLevelsOfTheFlow
import YangMills.Construction.ResponseInTheExpansion.RunningCouplingSlope
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
private theorem geom_tail_sum_mul_le {c lam X : ℝ} (hc : 0 < c) (hr1 : Real.exp (-(c * lam)) ≤ 1) {n : ℕ}
    {x : ℕ → ℝ} (hx : ∀ u < n, X + lam * ((n : ℝ) - u) ≤ x u) (d : ℕ) :
    ∀ w : ℕ, w + d = n →
      (∑ u ∈ Finset.Ico w n, Real.exp (-(c * x u))) * (1 - Real.exp (-(c * lam))) ≤
        Real.exp (-(c * X)) * Real.exp (-(c * lam)) * (1 - Real.exp (-(c * lam)) ^ d) := by
  induction d with
  | zero =>
    intro w hw
    have hwn : w = n := by omega
    subst hwn
    simp
  | succ d ih =>
    intro w hw
    have hwn : w < n := by omega
    rw [Finset.sum_eq_sum_Ico_succ_bot hwn]
    have hrest := ih (w + 1) (by omega)
    have hterm : Real.exp (-(c * x w)) ≤
        Real.exp (-(c * X)) * Real.exp (-(c * lam)) ^ (d + 1) := by
      have hsub : ((n : ℝ) - w) = ((d + 1 : ℕ) : ℝ) := by
        have hn : (n : ℝ) = (w : ℝ) + ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hw.symm
        rw [hn]; ring
      have h1 := hx w hwn
      rw [hsub] at h1
      have h2 : Real.exp (-(c * X)) * Real.exp (-(c * lam)) ^ (d + 1) =
          Real.exp (-(c * (X + lam * ((d + 1 : ℕ) : ℝ)))) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      rw [h2]
      apply Real.exp_le_exp.mpr
      have h3 := mul_le_mul_of_nonneg_left h1 hc.le
      linarith
    have hterm' := mul_le_mul_of_nonneg_right hterm (sub_nonneg.mpr hr1)
    have hid : Real.exp (-(c * X)) * Real.exp (-(c * lam)) ^ (d + 1) * (1 - Real.exp (-(c * lam))) +
        Real.exp (-(c * X)) * Real.exp (-(c * lam)) * (1 - Real.exp (-(c * lam)) ^ d) =
        Real.exp (-(c * X)) * Real.exp (-(c * lam)) * (1 - Real.exp (-(c * lam)) ^ (d + 1)) := by
      ring
    rw [add_mul, ← hid]
    exact add_le_add hterm' hrest
private theorem tail_sum_exp_le_one {c lam X : ℝ} (hc : 0 < c) (hlam : 0 < lam) {n : ℕ} {x : ℕ → ℝ}
    (hx : ∀ u < n, X + lam * ((n : ℝ) - u) ≤ x u)
    (hX : Real.exp (-(c * X)) ≤ 1 - Real.exp (-(c * lam))) {w : ℕ} (hw : w ≤ n) :
    ∑ u ∈ Finset.Ico w n, Real.exp (-(c * x u)) ≤ 1 := by
  have hr0 : 0 < Real.exp (-(c * lam)) := Real.exp_pos _
  have hr1 : Real.exp (-(c * lam)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have := mul_pos hc hlam
    linarith
  have hA : 0 < Real.exp (-(c * X)) := Real.exp_pos _
  have h := geom_tail_sum_mul_le hc hr1.le hx (n - w) w (by omega)
  have hpow0 : 0 ≤ Real.exp (-(c * lam)) ^ (n - w) := pow_nonneg hr0.le _
  have hpow1 : Real.exp (-(c * lam)) ^ (n - w) ≤ 1 := pow_le_one₀ hr0.le hr1.le
  have hprod : Real.exp (-(c * lam)) * (1 - Real.exp (-(c * lam)) ^ (n - w)) ≤ 1 :=
    mul_le_one₀ hr1.le (sub_nonneg.mpr hpow1) (by linarith)
  have hbound : Real.exp (-(c * X)) * Real.exp (-(c * lam)) *
      (1 - Real.exp (-(c * lam)) ^ (n - w)) ≤ Real.exp (-(c * X)) := by
    rw [mul_assoc]
    exact mul_le_of_le_one_right hA.le hprod
  have hpos : 0 < 1 - Real.exp (-(c * lam)) := sub_pos.mpr hr1
  have hfin : (∑ u ∈ Finset.Ico w n, Real.exp (-(c * x u))) * (1 - Real.exp (-(c * lam))) ≤
      1 * (1 - Real.exp (-(c * lam))) := by
    rw [one_mul]
    exact (h.trans hbound).trans hX
  exact le_of_mul_le_mul_right hfin hpos
private theorem exists_floor_exp_half_le {c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam) :
    ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y → Real.exp (-(c * (y / 2))) ≤ 1 - Real.exp (-(c * lam)) := by
  have hr1 : Real.exp (-(c * lam)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have := mul_pos hc hlam
    linarith
  have hpos : 0 < 1 - Real.exp (-(c * lam)) := sub_pos.mpr hr1
  refine ⟨-(2 * Real.log (1 - Real.exp (-(c * lam))) / c), fun y hy => ?_⟩
  rw [← Real.le_log_iff_exp_le hpos]
  have h1 := mul_le_mul_of_nonneg_left hy hc.le
  have h2 : c * -(2 * Real.log (1 - Real.exp (-(c * lam))) / c) =
      -(2 * Real.log (1 - Real.exp (-(c * lam)))) := by
    field_simp
  rw [h2] at h1
  linarith
private theorem gasRate_pos {T : RenormalizationStepParameters.ParameterAssignment} (h : T.Admissible) : 0 < T.gasRate := by apply _root_.YangMills.Construction.StepFloors.gasRate_pos <;> assumption
theorem levelSumBound (hS : WeightedResponses.FlowDescendsLinearly) :
    levelSumBoundStatement := by
  unfold levelSumBoundStatement AtResponseParameters
  intro a ha
  obtain ⟨L₀, rt₀, hrt₀, hL⟩ := hS a ha
  refine ⟨L₀, rt₀, 0, hrt₀, ?_⟩
  intro L hodd hLL T hTa hTL hD _ _ hrt _ _
  obtain ⟨lam, c₅, hlam, hT⟩ := hL L hodd hLL
  obtain ⟨y₁, hy₁⟩ := hT T hTa hTL hD hrt
  have hch := gasRate_pos hD
  have h7 : 0 < 7 * T.gasRate := by linarith
  have h8 : 0 < 8 * T.gasRate := by linarith
  obtain ⟨Y₇, hY₇⟩ := exists_floor_exp_half_le h7 hlam
  obtain ⟨Y₈, hY₈⟩ := exists_floor_exp_half_le h8 hlam
  refine ⟨max (max y₁ (2 * c₅)) (max Y₇ Y₈), ?_⟩
  intro y hy hR β tp hflow w hw
  have hyy₁ : y₁ ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
  have hyc : 2 * c₅ ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans hy)
  have hy7 : Y₇ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hy8 : Y₈ ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans hy)
  have hslope := hy₁ y hyy₁ hR.returns_at (fun β hβ => hR.wilson_expansion β hβ)
  have hβ : (T.stepParameters y).y₁ ≤ β := hflow 0 (Nat.zero_le _)
  have hline : ∀ u < tp, y / 2 + lam * ((tp : ℝ) - u) ≤ ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β u := by
    intro u hu
    have h1 := hslope β hβ tp (fun k hk => hflow k hk.le) u hu.le
    have h2 : y ≤ ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β tp := hflow tp le_rfl
    have h3 : lam * ((tp : ℝ) - u) - c₅ ≤
        ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β u - ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β tp := h1
    linarith
  exact ⟨by
      have := tail_sum_exp_le_one h7 hlam hline (hY₇ y hy7) hw
      simpa only [mul_assoc] using this,
    by
      have := tail_sum_exp_le_one h8 hlam hline (hY₈ y hy8) hw
      simpa only [mul_assoc] using this⟩
end YangMills.Construction.FreeEnergies
end
