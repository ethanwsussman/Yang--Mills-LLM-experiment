import YangMills.Construction.Towers.OperatorsDependingLocallyOnAField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
open YangMills.Construction.Tower.AbelianFieldDensity YangMills.Construction.OneLoopNotation
def LocalFamilyVariations : Prop :=
  ∀ (J E : Type) (place : J → YangMills.Construction.InfiniteLattice.AmbientSpace)
    (foot : E → YangMills.Construction.InfiniteLattice.AmbientSpace)
    (m m' : ℕ) (z C : ℝ) (T : (E → ℝ) → BddOp (IndexL2 J)),
    0 < z → 0 < C → IsLocalExpansionSetting place foot m m' z C T → ∀ e e' : E,
      ContDiff ℝ 2 (fun q : ℝ × ℝ => T (twoBondField e e' q.1 q.2)) ∧
      (∀ i' i, ‖matrixEntry (firstVar T e) i' i‖ ≤ C ∧
        ‖matrixEntry (secondVar T e e') i' i‖ ≤ C) ∧
      (∀ i' i, ¬ YangMills.Construction.TorusMetric.euclidNormVec (place i' - place i) ≤ 2 →
        matrixEntry (firstVar T e) i' i = 0 ∧ matrixEntry (secondVar T e e') i' i = 0) ∧
      (∀ i' i, ¬ YangMills.Construction.TorusMetric.euclidNormVec (foot e - place i') ≤ 2 →
        matrixEntry (firstVar T e) i' i = 0 ∧ matrixEntry (secondVar T e e') i' i = 0) ∧
      (∀ i' i, ¬ YangMills.Construction.TorusMetric.euclidNormVec (foot e' - place i') ≤ 2 →
        matrixEntry (secondVar T e e') i' i = 0) ∧
      ‖firstVar T e‖ ≤ 12 * 5 ^ 4 * C ∧ ‖secondVar T e e'‖ ≤ 12 * 5 ^ 4 * C
end YangMills.Construction.Tower.LocalFamilies
end
