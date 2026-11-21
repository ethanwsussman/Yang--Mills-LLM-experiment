import YangMills.Construction.Towers.TheDensityOfAnAbelianField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
open OperatorCalculus UnitLatticeL2
def ShiftedPositive : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ z : ℝ, 0 < z → ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      (∀ p : FullSpace.Face L 0 0, |FullSpace.faceAngle θ p| ≤ min (Real.pi / 2) (z / 48)) →
      IsBoundedBelowBy (addScalar (laplacianOp θ) z) (z / 2) ∧
        IsBoundedBelowBy (addScalar (massiveOp θ) z) (z / 2)) ∧
    (∀ (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (r : ℝ), (∀ v, |θ v| ≤ r) →
      ∀ p : FullSpace.Face L 0 0, |FullSpace.faceAngle θ p| ≤ 4 * r) ∧
    ∀ (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (f : ℝ) (p : FullSpace.Face L 0 0),
      FullSpace.faceAngle (fun v => f * θ v) p = f * FullSpace.faceAngle θ p
end YangMills.Construction.Tower.AbelianFieldDensity
end
