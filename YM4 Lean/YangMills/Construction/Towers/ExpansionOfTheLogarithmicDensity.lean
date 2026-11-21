import YangMills.Construction.Towers.OperatorsDependingLocallyOnAField
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
open YangMills.Construction.Tower.AbelianFieldDensity
open YangMills.Construction.Tower.LocalFamilies YangMills.Construction.OneLoopNotation
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
def LogTraceQuadraticExpansion : Prop :=
  ∀ (z C : ℝ) (m m' : ℕ), 0 < z → 0 < C → ∃ K : ℝ,
    ∀ (J B : Type) (pos : J → InfiniteLattice.AmbientSpace) (src : B → InfiniteLattice.AmbientSpace)
      (T : (B → ℝ) → BddOp (IndexL2 J)),
      IsLocalExpansionSetting pos src m m' z C T →
      ∀ ξ : B → ℝ, (∀ b, |ξ b| ≤ 2 + TorusMetric.euclidNormVec (src b)) →
      ∀ f₀ : ℝ, 0 < f₀ → f₀ ≤ 1 →
      (∀ f : ℝ, |f| ≤ f₀ →
        UnitLatticeL2.IsBoundedBelowBy (addScalar (T fun b => f * ξ b) z) (z / 2)) →
      Summable (fun p : B × B => logTraceHessian pos T z 0 p.1 p.2 * (ξ p.1 : ℂ) * (ξ p.2 : ℂ)) ∧
      ∃ a : ℂ, ∀ f : ℝ, |f| ≤ f₀ →
        ‖logTraceAt pos T z (fun b => f * ξ b) 0 - logTraceAt pos T z (fun _ => 0) 0 -
            a * (f : ℂ) - ((1 / 2 * f ^ 2 : ℝ) : ℂ) *
              ∑' p : B × B, logTraceHessian pos T z 0 p.1 p.2 * (ξ p.1 : ℂ) * (ξ p.2 : ℂ)‖ ≤
          K * |f| ^ 3
end YangMills.Construction.Tower.LocalFamilies
end
