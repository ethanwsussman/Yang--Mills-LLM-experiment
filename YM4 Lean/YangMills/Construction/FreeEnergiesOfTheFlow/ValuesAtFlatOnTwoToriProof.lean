import YangMills.Construction.FreeEnergiesOfTheFlow.StepsOfTheFlowExist
import YangMills.Construction.FreeEnergiesOfTheFlow.ValueOfTheFlowAtTheFlatField
import YangMills.Construction.FreeEnergiesOfTheFlow.ValuesAtFlatOnTwoTori
import YangMills.Construction.FreeEnergiesOfTheFlow.ValuesOnTwoTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
open TorusLumps RenormalizationStepParameters StepSettings ClusterExpansionOfAStep WeightedResponses
private theorem summable_scaleRate (T : ParameterAssignment) (hL : 2 ≤ T.side) (hrt : 0 < T.rt) {nS : ℝ}
    (hnS : 1 ≤ nS) : Summable (scaleRate T nS) := by
  set c : ℝ := T.rt * nS / 2 ^ 10 with hc
  have hc0 : 0 < c := by positivity
  have hLr : (2 : ℝ) ≤ T.side := by exact_mod_cast hL
  have hbound : ∀ j : ℕ, scaleRate T nS j ≤ (2 * (720 / c ^ 6)) * (1 / 4 : ℝ) ^ j := by
    intro j
    have hu : 0 < c * (T.side : ℝ) ^ j := by positivity
    have hexp : Real.exp (-(c * (T.side : ℝ) ^ j)) ≤ 720 / (c * (T.side : ℝ) ^ j) ^ 6 := by
      have h1 := Real.pow_div_factorial_le_exp (c * (T.side : ℝ) ^ j) hu.le 6
      have h2 : (Nat.factorial 6 : ℝ) = 720 := by norm_num [Nat.factorial]
      rw [h2] at h1
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
      exact h1
    have e1 : T.rt * (T.side : ℝ) ^ j * nS / 2 ^ 10 = c * (T.side : ℝ) ^ j := by
      rw [hc]
      ring
    unfold scaleRate
    rw [e1]
    have h4 : (T.side : ℝ) ^ (4 * j) * (2 * (720 / (c * (T.side : ℝ) ^ j) ^ 6)) =
        2 * (720 / c ^ 6) * (1 / ((T.side : ℝ) ^ j) ^ 2) := by
      rw [pow_mul' (T.side : ℝ) 4 j]
      field_simp
    have h5 : (1 : ℝ) / ((T.side : ℝ) ^ j) ^ 2 ≤ (1 / 4 : ℝ) ^ j := by
      have h6 : (2 : ℝ) ^ j ≤ (T.side : ℝ) ^ j := pow_le_pow_left₀ (by norm_num) hLr j
      have h7 : (4 : ℝ) ^ j ≤ ((T.side : ℝ) ^ j) ^ 2 := by
        have : (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
        rw [this]
        exact pow_le_pow_left₀ (by positivity) h6 2
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) h7
    calc (T.side : ℝ) ^ (4 * j) * (2 * Real.exp (-(c * (T.side : ℝ) ^ j)))
        ≤ (T.side : ℝ) ^ (4 * j) * (2 * (720 / (c * (T.side : ℝ) ^ j) ^ 6)) := by gcongr
      _ = _ := h4
      _ ≤ _ := by gcongr
  refine Summable.of_nonneg_of_le (fun j => ?_) hbound
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
  unfold scaleRate
  positivity
theorem logFlowAtTrivialTwoTori_holds (hV : logFlowAtTrivialEqSum) (hT2 : blockActivityTwoTori)
    (hS : flowStepsExist) : logFlowAtTrivialTwoTori := by
  obtain ⟨r₁, hr₁, h₁⟩ := hV
  obtain ⟨r₂, hr₂, h₂⟩ := hT2
  obtain ⟨r₃, hr₃, h₃⟩ := hS
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (r₃ c)), fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (hr₃ c)),
    fun T hT hC hrt => ?_⟩
  obtain ⟨y₁, k₁⟩ := h₁ T hT hC (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, k₂⟩ := h₂ T hT hC (hrt.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨y₃, k₃⟩ := h₃ T hT hC (hrt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨max (max y₁ y₂) (max y₃ T.floorMin), fun y hy hSt => ?_⟩
  have e₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have e₂ : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have e₃ : y₃ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have e₄ : T.floorMin ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hfit := hT.fits y e₄
  obtain ⟨nS, hnS, two⟩ := k₂ y e₂ hSt
  have hL2 : 2 ≤ T.side := le_trans (by norm_num) hT.L_ge
  have hsum := summable_scaleRate T hL2 hT.rt_pos hnS
  refine ⟨nS, ∑' j, scaleRate T nS j, hnS, hsum, le_rfl, fun β t hr n n' _ _ hb hb' hnn hside => ?_⟩
  obtain ⟨R, hR⟩ := k₃ y e₃ hSt β t hr
  have v := (k₁ y e₁ hSt β t hr R hR n hb).2
  have v' := (k₁ y e₁ hSt β t hr R hR n' hb').2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hn'0 : (0 : ℝ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  have hx1 : 1 ≤ flowCoupling (T.stepParameters y) β t := hfit.y₁_ge.trans (hr t le_rfl)
  have hX : 1 ≤ flowCoupling (T.stepParameters y) β t ^ ((1 : ℝ) / 100) :=
    Real.one_le_rpow hx1 (by norm_num)
  have hnnS : nS ≤ n := by nlinarith
  rw [v, v', Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hterm : ∀ u ∈ Finset.range t,
      |(T.side : ℝ) ^ (4 * (t - 1 - u)) * (n' : ℝ) ^ 4 *
          blockActivityAtTrivial T.lam (R u) (fineSide T.side (t - 1 - u) n') 0 -
        (n' : ℝ) ^ 4 / (n : ℝ) ^ 4 * ((T.side : ℝ) ^ (4 * (t - 1 - u)) * (n : ℝ) ^ 4 *
          blockActivityAtTrivial T.lam (R u) (fineSide T.side (t - 1 - u) n) 0)| ≤
      (n' : ℝ) ^ 4 * scaleRate T nS (t - 1 - u) := by
    intro u hu
    have hu' : u < t := Finset.mem_range.mp hu
    have hb2 := two β t hr R hR n n' hb hb' hnn hside u hu'
    set k := t - 1 - u
    set a := blockActivityAtTrivial T.lam (R u) (fineSide T.side k n) 0
    set a' := blockActivityAtTrivial T.lam (R u) (fineSide T.side k n') 0
    have e : (T.side : ℝ) ^ (4 * k) * (n' : ℝ) ^ 4 * a' -
        (n' : ℝ) ^ 4 / (n : ℝ) ^ 4 * ((T.side : ℝ) ^ (4 * k) * (n : ℝ) ^ 4 * a) =
        (n' : ℝ) ^ 4 * ((T.side : ℝ) ^ (4 * k) * (a' - a)) := by
      field_simp
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n' : ℝ) ^ 4), abs_mul,
      abs_of_pos (by have : (0 : ℝ) < T.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
                     positivity : (0 : ℝ) < (T.side : ℝ) ^ (4 * k)), abs_sub_comm a' a]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    unfold scaleRate
    refine mul_le_mul_of_nonneg_left (hb2.trans ?_) (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    have hrt0 := hT.rt_pos
    have hLp : (0 : ℝ) ≤ (T.side : ℝ) ^ k := by positivity
    gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hrefl : ∑ u ∈ Finset.range t, scaleRate T nS (t - 1 - u) =
      ∑ j ∈ Finset.range t, scaleRate T nS j :=
    Finset.sum_range_reflect (scaleRate T nS) t
  rw [hrefl]
  refine hsum.sum_le_tsum _ fun j _ => ?_
  unfold scaleRate
  positivity
end YangMills.Construction.FreeEnergies
end
