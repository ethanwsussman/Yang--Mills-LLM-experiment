import YangMills.Construction.Towers.ChainsOfLocalKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
def FieldVariationsAsEdgeSums : Prop :=
  ∀ (C : ℝ) (m' : ℕ), 0 < C → ∃ A : ℝ, 0 ≤ A ∧
    ∀ (J E : Type) (pos : J → InfiniteLattice.AmbientSpace) (src : E → InfiniteLattice.AmbientSpace)
      (m : ℕ) (z : ℝ) (T : (E → ℝ) → OneLoopNotation.BddOp (IndexL2 J)),
      0 < z → IsLocalExpansionSetting pos src m m' z C T →
      ∀ ξ : E → ℝ, (∀ e, |ξ e| ≤ 2 + TorusMetric.euclidNormVec (src e)) →
        IsCubicGrowthLocalFamily pos A
          (fun (e : E) (i' i : J) => (ξ e : ℂ) * UnitLatticeL2.matrixEntry (firstVar T e) i' i) ∧
        IsCubicGrowthLocalFamily pos A
          (fun (p : E × E) (i' i : J) =>
            (ξ p.1 : ℂ) * (ξ p.2 : ℂ) * UnitLatticeL2.matrixEntry (secondVar T p.1 p.2) i' i) ∧
        (∀ i' i, firstVariationKernel T ξ i' i =
          ∑' e, (ξ e : ℂ) * UnitLatticeL2.matrixEntry (firstVar T e) i' i) ∧
        ∀ i' i, secondVariationKernel T ξ i' i =
          ∑' p : E × E, (ξ p.1 : ℂ) * (ξ p.2 : ℂ) * UnitLatticeL2.matrixEntry (secondVar T p.1 p.2) i' i
end YangMills.Construction.Tower.LocalFamilies
end
