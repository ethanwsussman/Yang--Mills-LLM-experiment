import YangMills.Construction.Towers.TheDensityOfAnAbelianField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
variable {L : ℕ}
open Classical in
def edgeIndicator (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.PositiveEdge (meshAt L 0 0) → ℝ :=
  fun c => if c = b then 1 else 0
def secondDerivative (z : ℝ) (x : FullSpace.Vertex L 0 0)
    (b b' : FullSpace.PositiveEdge (meshAt L 0 0)) : ℂ :=
  deriv (fun s : ℝ => deriv (fun t : ℝ =>
    densityAt z (fun c => s * edgeIndicator b c + t * edgeIndicator b' c) x) 0) 0
def secondDerivativeTerm (z : ℝ) (ξ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    (p : FullSpace.PositiveEdge (meshAt L 0 0) × FullSpace.PositiveEdge (meshAt L 0 0)) : ℂ :=
  secondDerivative z (0 : FullSpace.Vertex L 0 0) p.1 p.2 * (ξ p.1 : ℂ) * (ξ p.2 : ℂ)
def secondDerivativeSum (z : ℝ) (ξ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) : ℂ :=
  ∑' p, secondDerivativeTerm z ξ p
structure HasBoundedAngles (ξ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) : Prop where
  abs_le : ∀ b : FullSpace.PositiveEdge (meshAt L 0 0),
    |ξ b| ≤ 2 + TorusMetric.euclidNormVec (b.1.initial : InfiniteLattice.AmbientSpace)
  abs_faceAngle_le : ∀ p : FullSpace.Face L 0 0, |FullSpace.faceAngle ξ p| ≤ 4
end YangMills.Construction.Tower.AbelianFieldDensity
end
