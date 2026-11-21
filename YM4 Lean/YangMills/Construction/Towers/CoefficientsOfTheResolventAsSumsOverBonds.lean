import YangMills.Construction.Towers.ChainsOfLocalKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
open YangMills.Construction.Tower.AbelianFieldDensity YangMills.Construction.Tower.LocalFamilies
open YangMills.Construction.OneLoopNotation
def ResolventCoeffSums.BondSumExpansion : Prop :=
  ∀ (z C : ℝ) (m m' : ℕ), 0 < z → 0 < C → ∃ M : ℝ, 0 ≤ M ∧
    ∀ (J B : Type) (pos : J → InfiniteLattice.AmbientSpace) (src : B → InfiniteLattice.AmbientSpace)
      (T : (B → ℝ) → BddOp (IndexL2 J)),
      IsLocalExpansionSetting pos src m m' z C T →
      ∀ ξ : B → ℝ, (∀ b, |ξ b| ≤ 2 + TorusMetric.euclidNormVec (src b)) →
      ∀ w : ℝ, 0 ≤ w →
        (Summable (fun b => ‖(ξ b : ℂ) * traceAt pos
            ((baseResolvent T z w).comp ((firstVar T b).comp (baseResolvent T z w))) 0‖) ∧
          ∑' b, ‖(ξ b : ℂ) * traceAt pos
            ((baseResolvent T z w).comp ((firstVar T b).comp (baseResolvent T z w))) 0‖ ≤
            M * (z / 4 + w)⁻¹ ^ 2 ∧
          resolventFirstCoeff pos T ξ z w =
            ∑' b, (ξ b : ℂ) * traceAt pos
              ((baseResolvent T z w).comp ((firstVar T b).comp (baseResolvent T z w))) 0) ∧
        Summable (fun q : B × B => ‖(ξ q.1 : ℂ) * (ξ q.2 : ℂ) *
            traceAt pos (secondOrderResolvent T z q.1 q.2 w) 0‖) ∧
          ∑' q : B × B, ‖(ξ q.1 : ℂ) * (ξ q.2 : ℂ) *
            traceAt pos (secondOrderResolvent T z q.1 q.2 w) 0‖ ≤ M * (z / 4 + w)⁻¹ ^ 2 ∧
          resolventSecondCoeff pos T ξ z w =
            ∑' q : B × B, (ξ q.1 : ℂ) * (ξ q.2 : ℂ) *
              traceAt pos (secondOrderResolvent T z q.1 q.2 w) 0
end YangMills.Construction.Tower.LocalFamilies
end
