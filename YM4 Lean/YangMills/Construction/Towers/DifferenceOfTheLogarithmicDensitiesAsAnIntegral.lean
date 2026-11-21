import YangMills.Construction.Towers.OperatorsDependingLocallyOnAField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
def LogTraceDiffIntegral : Prop :=
  ∀ (J E : Type) (pos : J → InfiniteLattice.AmbientSpace) (src : E → InfiniteLattice.AmbientSpace)
    (m m' : ℕ) (z C : ℝ) (T : (E → ℝ) → OneLoopNotation.BddOp (IndexL2 J)),
    0 < z → 0 < C → IsLocalExpansionSetting pos src m m' z C T →
    (∀ θ : E → ℝ, UnitLatticeL2.IsBoundedBelowBy (OperatorCalculus.addScalar (T θ) z) (z / 2) →
      MeasureTheory.IntegrableOn (fun w : ℝ => AbelianFieldDensity.traceAt pos (baseResolvent T z w) 0 -
        AbelianFieldDensity.traceAt pos
          (OperatorCalculus.inverseOp (OperatorCalculus.addScalar (OperatorCalculus.addScalar (T θ) z) w)) 0)
        (Set.Ioi 0) ∧
      logTraceAt pos T z θ 0 - logTraceAt pos T z (fun _ => 0) 0 =
        ∫ w in Set.Ioi (0 : ℝ), (AbelianFieldDensity.traceAt pos (baseResolvent T z w) 0 -
          AbelianFieldDensity.traceAt pos
            (OperatorCalculus.inverseOp (OperatorCalculus.addScalar (OperatorCalculus.addScalar (T θ) z) w)) 0)) ∧
    ∀ X : OneLoopNotation.BddOp (IndexL2 J),
      MeasureTheory.IntegrableOn (fun w : ℝ => AbelianFieldDensity.traceAt pos
        ((baseResolvent T z w).comp (X.comp (baseResolvent T z w))) 0) (Set.Ioi 0)
end YangMills.Construction.Tower.LocalFamilies
end
