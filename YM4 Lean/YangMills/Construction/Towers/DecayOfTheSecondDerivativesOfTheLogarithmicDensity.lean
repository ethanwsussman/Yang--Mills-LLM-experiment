import YangMills.Construction.Towers.OperatorsDependingLocallyOnAField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
def LogDensityHessianDecay : Prop :=
  ∀ (z C : ℝ) (m m' : ℕ), 0 < z → 0 < C → ∃ K : ℝ,
    ∀ (J B : Type) (position : J → InfiniteLattice.AmbientSpace)
      (tail : B → InfiniteLattice.AmbientSpace)
      (T : (B → ℝ) → OneLoopNotation.BddOp (IndexL2 J)),
      IsLocalExpansionSetting position tail m m' z C T → ∀ (n : Fin 4 → ℤ) (b b' : B),
        ‖logTraceHessian position T z (PeriodicOperators.castVec n) b b'‖ ≤
          K * Real.exp (-(ResolventDecay.resolventDecayRate z C *
            (TorusMetric.euclidNormVec (PeriodicOperators.castVec n - tail b) +
              TorusMetric.euclidNormVec (PeriodicOperators.castVec n - tail b'))))
end YangMills.Construction.Tower.LocalFamilies
end
