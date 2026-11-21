import YangMills.Construction.ClusterExpansionOfAStep.AMoveReadAtZero
import YangMills.Construction.ClusterExpansionOfAStep.ChartsOverTheTopOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.ColdAlongAMove
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction.TorusFields
open BlockAverages BondMoves TopLevelSites in
theorem coldNear : ColdNearStatement := by
  intro n _ V k c X τ₀ s hs
  set S : ℝ := ∑ l, ‖X l‖ with hS
  have hbond : ∀ (τ : Fin k → ℝ) (y : TorusSite n) (i : Fin 4),
      ‖((perturb c X τ V y i : UnitQuaternion) : ℍ[ℝ]) - (perturb c X τ₀ V y i : UnitQuaternion)‖ ≤
        S * ‖τ - τ₀‖ := by
    intro τ y i
    rw [perturb_eq_expUnit_mul, perturb_eq_expUnit_mul]
    refine (norm_mul_sub_mul_le _ _ _ _).trans ?_
    rw [sub_self, norm_zero, add_zero]
    refine (norm_expUnit_sub_le _ _).trans ?_
    have e : ((bondMoveLinear c X (y, i) τ : imaginaryQuaternions) : ℍ[ℝ]) -
        (bondMoveLinear c X (y, i) τ₀ : imaginaryQuaternions) =
        ((bondMoveLinear c X (y, i) (τ - τ₀) : imaginaryQuaternions) : ℍ[ℝ]) := by
      rw [map_sub]
      rfl
    rw [e]
    exact ((bondMoveLinear c X (y, i)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_bondMoveLinear_le c X (y, i)) (norm_nonneg _))
  have hone : ∀ (x : TorusSite n) (μ ν : Fin 4), ∀ᶠ τ in 𝓝 τ₀, μ < ν →
      curvature (perturb c X τ V) x μ ν < s := by
    intro x μ ν
    by_cases h : μ < ν
    · have hcont : Continuous fun τ : Fin k → ℝ =>
          curvature (perturb c X τ₀ V) x μ ν + 4 * (S * ‖τ - τ₀‖) := by
        fun_prop
      have hev := hcont.continuousAt.eventually_lt (continuousAt_const (y := s) (x := τ₀))
        (by simpa using hs x μ ν h)
      refine hev.mono fun τ hτ _ => ?_
      have h1 := curvature_le_add (perturb c X τ V) (perturb c X τ₀ V) x μ ν
      have h2 := hbond τ x μ
      have h3 := hbond τ (x + unitStep n μ) ν
      have h4 := hbond τ (x + unitStep n ν) μ
      have h5 := hbond τ x ν
      linarith
    · exact Eventually.of_forall fun τ hh => absurd hh h
  have hall := eventually_all.mpr fun x => eventually_all.mpr fun μ => eventually_all.mpr fun ν => hone x μ ν
  exact hall.mono fun τ hτ x μ ν h => hτ x μ ν h
end YangMills.Construction.TorusFields
end
