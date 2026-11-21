import YangMills.Construction.Towers.OperatorsDependingLocallyOnAField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
def LogTraceSecondDerivative.IntegralFormula : Prop :=
  ∀ (J B : Type) (pos : J → InfiniteLattice.AmbientSpace) (src : B → InfiniteLattice.AmbientSpace)
    (m m' : ℕ) (z C : ℝ) (T : (B → ℝ) → OneLoopNotation.BddOp (Tower.LocalFamilies.IndexL2 J)),
    0 < z → 0 < C → Tower.LocalFamilies.IsLocalExpansionSetting pos src m m' z C T →
    ∀ (n : Fin 4 → ℤ) (e e' : B),
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Tower.LocalFamilies.logTraceAt pos T z
        (Tower.LocalFamilies.twoBondField e e' p.1 p.2) (PeriodicOperators.castVec n)) 0 ∧
      MeasureTheory.IntegrableOn (fun w : ℝ => Tower.AbelianFieldDensity.traceAt pos
        (Tower.LocalFamilies.secondOrderResolvent T z e e' w) (PeriodicOperators.castVec n))
        (Set.Ioi 0) ∧
      Tower.LocalFamilies.logTraceHessian pos T z (PeriodicOperators.castVec n) e e' =
        ∫ w in Set.Ioi (0 : ℝ), Tower.AbelianFieldDensity.traceAt pos
          (Tower.LocalFamilies.secondOrderResolvent T z e e' w) (PeriodicOperators.castVec n)
end YangMills.Construction.Tower.LocalFamilies
end
