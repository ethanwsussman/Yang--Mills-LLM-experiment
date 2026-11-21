import YangMills.Construction.HilbertSpaces.LimitsSeriesIntegralsAndTheLogarithmOfBoundedOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
namespace ResolventDecay
def resolventDecayRate (z C : ℝ) : ℝ := (1 / 2) * Real.log (1 + z / (4 * 12 * 5 ^ 4 * C))
def ResolventKernelDecays {J : Type} (pos : J → InfiniteLattice.AmbientSpace) (z C : ℝ) : Prop :=
  ∀ T : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2,
    IsSelfAdjointOp T → IsBoundedBelowBy (addScalar T z) (z / 2) →
    (∀ i' i, ‖matrixEntry T i' i‖ ≤ C) →
    (∀ i' i, ¬ TorusMetric.euclidNormVec (pos i' - pos i) ≤ 2 → matrixEntry T i' i = 0) →
    ∀ w : ℝ, 0 ≤ w → ∀ i' i,
      ‖matrixEntry (inverseOp (addScalar (addScalar T z) w)) i' i‖ ≤
        (z / 4 + w)⁻¹ *
          Real.exp (-(resolventDecayRate z C * TorusMetric.euclidNormVec (pos i' - pos i)))
end ResolventDecay
open ResolventDecay in
def RangeTwoResolventDecay : Prop :=
  ∀ z C : ℝ, 0 < z → 0 < C →
    0 < resolventDecayRate z C ∧
    ∀ L : ℕ, ResolventKernelDecays (vertexPos L) z C ∧
      ResolventKernelDecays (edgePos L) z C
end YangMills.Construction.Tower
end
