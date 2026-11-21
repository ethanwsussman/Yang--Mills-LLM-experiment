import YangMills.Construction.Towers.ChainsOfLocalKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
open OperatorCalculus UnitLatticeL2 AbelianFieldDensity OneLoopNotation
def ResolventSecondOrderExpansion : Prop :=
  ∀ (z C : ℝ) (m m' : ℕ), 0 < z → 0 < C → ∃ M : ℝ, 0 ≤ M ∧
    ∀ (J E : Type) (pos : J → InfiniteLattice.AmbientSpace) (src : E → InfiniteLattice.AmbientSpace)
      (T : (E → ℝ) → BddOp (IndexL2 J)),
      IsLocalExpansionSetting pos src m m' z C T →
      ∀ ξ : E → ℝ, (∀ e, |ξ e| ≤ 2 + TorusMetric.euclidNormVec (src e)) →
      ∀ f : ℝ, |f| ≤ 1 → IsBoundedBelowBy (addScalar (T fun e => f * ξ e) z) (z / 2) →
      ∀ w : ℝ, 0 ≤ w →
        ‖traceAt pos (baseResolvent T z w) 0 -
            traceAt pos (shiftedResolventAlong T ξ z f w) 0 -
            (f : ℂ) * resolventFirstCoeff pos T ξ z w -
            ((1 / 2 * f ^ 2 : ℝ) : ℂ) * resolventSecondCoeff pos T ξ z w‖ ≤
          M * |f| ^ 3 * (z / 4 + w)⁻¹ ^ 2
end YangMills.Construction.Tower.LocalFamilies
end
