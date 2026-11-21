import YangMills.Construction.CellOfTheFlow.SupportsAboutABlockAreFew
import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfAStepAreCounted
import YangMills.Construction.ClusterExpansionOfAStep.CountFloorCanBeMet
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParametersProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps RenormalizationStepParameters
private theorem gasRate_pos_of_admissible (P : ParameterAssignment) (hP : P.Admissible) : 0 < P.gasRate := by apply _root_.YangMills.Construction.StepFloors.gasRate_pos <;> assumption
theorem sqrtClusterWeightTailAtBlock (hsum : ClusterSumBound)
    (hfloor : CouplingFloorExists) : sqrtClusterWeightTailAtBlockStatement := by
  intro a _
  refine ⟨0, fun _ => 1, fun _ => one_pos, fun L _ _ P _ _ hP _ => ?_⟩
  have hrate := gasRate_pos_of_admissible P hP
  have hrate16 : 0 < P.gasRate / 16 := by positivity
  obtain ⟨y₂, hy₂⟩ := hfloor (P.gasRate / 16) P.side P.rt hrate16
  refine ⟨max (max P.floorMin y₂) 0, fun y hy _ _ x hx n _ Y ν => ?_⟩
  have hy₀ : max P.floorMin y₂ ≤ y := (le_max_left _ _).trans hy
  have hadm : (P.stepParameters y).Admissible := hP.fits y ((le_max_left _ _).trans hy₀)
  have hrange : (P.stepParameters y).RangeFloor (P.gasRate / 16) := fun x' hx' =>
    hy₂ x' (((le_max_right _ _).trans hy₀).trans hx')
  have hx0 : 0 ≤ x := ((le_max_right _ _).trans hy).trans hx
  have hrx : 0 ≤ P.gasRate * x := mul_nonneg hrate.le hx0
  have hbound := hsum (P.stepParameters y) (P.gasRate / 16) hadm hrate16 hrange x hx n Y
  have hterm : ∀ θ ∈ supportsAtBlock (P.stepParameters y).side (clusterRange x) Y,
      Real.exp (-(P.gasRate * x * (supportUnitCount (P.stepParameters y).side (clusterRange x) θ : ℝ))) ≤
        clusterWeight (P.stepParameters y).side (P.gasRate / 16) x (clusterRange x) θ *
            ((supportCore (P.stepParameters y).side (clusterRange x) θ).card : ℝ) ^ 4 *
          Real.exp (2 * (P.stepParameters y).rt *
            (siteDiameter (supportCore (P.stepParameters y).side (clusterRange x) θ) : ℝ)) := by
    intro θ hθ
    have hY : Y ∈ supportCore (P.stepParameters y).side (clusterRange x) θ := by
      classical
      unfold supportsAtBlock at hθ
      exact (Finset.mem_filter.mp hθ).2.2
    have hcard : (1 : ℝ) ≤ ((supportCore (P.stepParameters y).side (clusterRange x) θ).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨Y, hY⟩
    have hpow : (1 : ℝ) ≤ ((supportCore (P.stepParameters y).side (clusterRange x) θ).card : ℝ) ^ 4 :=
      one_le_pow₀ hcard
    have hdiam : 0 ≤ 2 * (P.stepParameters y).rt *
        (siteDiameter (supportCore (P.stepParameters y).side (clusterRange x) θ) : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hP.rt_pos)) (Nat.cast_nonneg _)
    have hweight : clusterWeight (P.stepParameters y).side (P.gasRate / 16) x (clusterRange x) θ =
        Real.exp (-(P.gasRate * x * (supportUnitCount (P.stepParameters y).side (clusterRange x) θ : ℝ))) := by
      unfold clusterWeight
      congr 1
      ring
    rw [hweight]
    have hpos := Real.exp_pos (-(P.gasRate * x * (supportUnitCount (P.stepParameters y).side (clusterRange x) θ : ℝ)))
    calc Real.exp (-(P.gasRate * x * (supportUnitCount (P.stepParameters y).side (clusterRange x) θ : ℝ)))
        = Real.exp (-(P.gasRate * x * (supportUnitCount (P.stepParameters y).side (clusterRange x) θ : ℝ))) * 1 * 1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hpow hpos.le) (Real.one_le_exp hdiam) zero_le_one
          (mul_nonneg hpos.le (by positivity))
  have hone : ∑ θ ∈ supportsAtBlock (P.stepParameters y).side (clusterRange x) Y,
      Real.exp (-(P.gasRate * x * (supportUnitCount (P.stepParameters y).side (clusterRange x) θ : ℝ))) ≤ 1 := by
    refine (Finset.sum_le_sum hterm).trans (hbound.trans ?_)
    rw [Real.exp_le_one_iff]
    have : 0 ≤ 8 * (P.gasRate / 16) * x := by
      have : 8 * (P.gasRate / 16) * x = P.gasRate * x / 2 := by ring
      rw [this]
      positivity
    linarith
  have hE := Real.exp_pos (-(7 * P.gasRate * x * ν))
  classical
  calc ∑ θ ∈ (supportsAtBlock (P.stepParameters y).side (clusterRange x) Y).filter
          (fun θ => ν ≤ supportUnitCount (P.stepParameters y).side (clusterRange x) θ),
        Real.sqrt (clusterWeight (P.stepParameters y).side P.gasRate x (clusterRange x) θ)
      ≤ ∑ θ ∈ (supportsAtBlock (P.stepParameters y).side (clusterRange x) Y).filter
          (fun θ => ν ≤ supportUnitCount (P.stepParameters y).side (clusterRange x) θ),
        Real.exp (-(7 * P.gasRate * x * ν)) *
          Real.exp (-(P.gasRate * x * (supportUnitCount (P.stepParameters y).side (clusterRange x) θ : ℝ))) := by
        refine Finset.sum_le_sum fun θ hθ => ?_
        have hν : (ν : ℝ) ≤ (supportUnitCount (P.stepParameters y).side (clusterRange x) θ : ℝ) := by
          exact_mod_cast (Finset.mem_filter.mp hθ).2
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        rw [← Real.exp_add, ← Real.exp_nat_mul]
        unfold clusterWeight
        rw [Real.exp_le_exp]
        have := mul_le_mul_of_nonneg_left hν hrx
        push_cast
        nlinarith
    _ = Real.exp (-(7 * P.gasRate * x * ν)) *
        ∑ θ ∈ (supportsAtBlock (P.stepParameters y).side (clusterRange x) Y).filter
          (fun θ => ν ≤ supportUnitCount (P.stepParameters y).side (clusterRange x) θ),
          Real.exp (-(P.gasRate * x * (supportUnitCount (P.stepParameters y).side (clusterRange x) θ : ℝ))) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (-(7 * P.gasRate * x * ν)) * 1 := by
        refine mul_le_mul_of_nonneg_left (le_trans ?_ hone) hE.le
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => (Real.exp_pos _).le
    _ ≤ 2 * Real.exp (-(7 * P.gasRate * x * ν)) := by linarith
end YangMills.Construction.CellWindows
end
