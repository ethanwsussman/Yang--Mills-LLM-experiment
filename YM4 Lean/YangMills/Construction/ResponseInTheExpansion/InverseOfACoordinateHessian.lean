import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearResponse
open ColdStepAtMirrorFrames
variable {ι : Type} [DecidableEq ι]
def bondCoordinateVector (p : ι × Fin 3) : BondField ι := bondVariation p.1 (EuclideanSpace.single p.2 1)
variable [Fintype ι]
def bondCoordinateHessian (A : BondField ι → ℝ) : Matrix (ι × Fin 3) (ι × Fin 3) ℝ :=
  fun p q => secondDerivAlong A 0 (bondCoordinateVector p) (bondCoordinateVector q)
def CoordinateHessianInverseBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : BondField ι → ℝ) (K d : ι → ι → ℝ) (lam κ W : ℝ),
    0 < lam → 0 ≤ κ → IsPseudoMetricOnBonds d → ContDiffAt ℝ 3 A 0 →
    (∀ u : BondField ι, lam * ∑ b, ‖u b‖ ^ 2 ≤ secondDerivAlong A 0 u u) →
    (∀ (b b' : ι) (e e' : BondVector),
      |secondDerivAlong A 0 (bondVariation b e) (bondVariation b' e')| ≤ K b b' * ‖e‖ * ‖e'‖) →
    (∀ b, ∑ b', K b b' * (Real.exp (2 * κ * d b b') - 1) ≤ lam / 16) →
    (∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W) →
    (bondCoordinateHessian A).IsSymm ∧ IsUnit (bondCoordinateHessian A).det ∧
      ∀ l : ι × Fin 3 → ℝ, ∑ p, |((bondCoordinateHessian A)⁻¹.mulVec l) p| ≤ 6 * W / lam * ∑ p, |l p|
end YangMills.Construction.LinearResponse
end
