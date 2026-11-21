import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBoundedProof
import YangMills.Construction.TwoPoints.EverySmallerShapeServes
import YangMills.Construction.TwoPoints.RotationInvarianceFromOneDiagonalMirror
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TwoPoints.Shapes (shapeConst)
namespace SmallerShape
theorem uniformNorm_nonneg (f : (Fin 4 → ℝ) → ℝ) : 0 ≤ TestFunctions.uniformNorm f := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.uniformNorm_nonneg <;> assumption
theorem isShapedBump_of_shape_le {d θ θ₀ : ℝ} (hd : 0 < d) (hθ : 0 < θ) (hθle : θ ≤ θ₀)
    {x : Fin 4 → ℝ} {f : (Fin 4 → ℝ) → ℝ}
    (hf : TestFunctions.IsShapedBump TestFunctions.euclidDistR4 TestFunctions.closedBallR4
      (fun f => ∫ x, f x) d θ₀ x f) :
    TestFunctions.IsShapedBump TestFunctions.euclidDistR4 TestFunctions.closedBallR4
      (fun f => ∫ x, f x) d θ x f := by
  obtain ⟨hlip, hpos, hnz, hsupp, hmass, hsup⟩ := hf
  have hnorm := uniformNorm_nonneg f
  refine ⟨hlip, hpos, hnz, hsupp, le_trans ?_ hmass, le_trans hsup ?_⟩
  · have hd4 : 0 ≤ d ^ 4 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hθle hnorm) hd4
  · exact div_le_div_of_nonneg_left hnorm (mul_pos hθ hd) (mul_le_mul_of_nonneg_right hθle hd.le)
theorem separatedPairsR4_mono {d θ θ₀ : ℝ} (hd : 0 < d) (hθ : 0 < θ) (hθle : θ ≤ θ₀) :
    TestFunctions.separatedPairsR4 d θ₀ ⊆ TestFunctions.separatedPairsR4 d θ := by
  rintro p ⟨y₁, y₂, hy₁, hy₂, hlo, hhi⟩
  exact ⟨y₁, y₂, isShapedBump_of_shape_le hd hθ hθle hy₁,
    isShapedBump_of_shape_le hd hθ hθle hy₂, hlo, hhi⟩
theorem isSmallPositiveWith_of_shape_le {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    {θ θ₀ d₀ : ℝ} {u : ℝ → ℝ} (hθ : 0 < θ) (hθle : θ ≤ θ₀) (h : IsSmallPositiveWith S θ d₀ u) :
    IsSmallPositiveWith S θ₀ d₀ u where
  radius_pos := h.radius_pos
  rate_pos := h.rate_pos
  rate_tendsto := h.rate_tendsto
  nonneg := fun d hd p hp h₁ h₂ =>
    h.nonneg d hd p (separatedPairsR4_mono hd.1 hθ hθle hp) h₁ h₂
  le_rate := fun d hd p hp h₁ h₂ =>
    h.le_rate d hd p (separatedPairsR4_mono hd.1 hθ hθle hp) h₁ h₂
theorem statement_holds (hmain : DiagonalReflectionRotationInvariance.Statement) :
    SmallerShape.Statement := by
  obtain ⟨hconst, hform⟩ := hmain
  intro θ hθ hθle
  have hclauses : ∀ (L : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ),
      IsDisjointForm S → IsAdmissibleForm L S → ∀ (d₀ : ℝ) (u : ℝ → ℝ),
        IsSmallPositiveWith S θ d₀ u →
          IsSmallPositiveWith S shapeConst d₀ u ∧ HasRotationInvarianceConditions S := by
    intro L S hS hadm d₀ u hsmall
    have hsmall' := isSmallPositiveWith_of_shape_le hθ hθle hsmall
    exact ⟨hsmall', hform L S hS hadm ⟨d₀, u, hsmall'⟩⟩
  refine ⟨fun d hd => separatedPairsR4_mono hd hθ hθle, hclauses, ⟨hθ, hθle.trans hconst.2⟩, ?_⟩
  rintro L S hS hadm ⟨d₀, u, hsmall⟩
  exact (hclauses L S hS hadm d₀ u hsmall).2
end SmallerShape
end YangMills.Construction.TwoPoints
end
