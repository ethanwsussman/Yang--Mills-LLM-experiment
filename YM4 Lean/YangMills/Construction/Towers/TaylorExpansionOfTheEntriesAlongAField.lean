import YangMills.Construction.Towers.ChainsOfLocalKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
open OperatorCalculus UnitLatticeL2 AbelianFieldDensity OneLoopNotation
def taylorKernels_cubicGrowth : Prop :=
  ∀ (J E : Type) (pos : J → InfiniteLattice.AmbientSpace) (src : E → InfiniteLattice.AmbientSpace)
    (m m' : ℕ) (z C : ℝ) (T : (E → ℝ) → BddOp (IndexL2 J)),
    0 < z → 0 < C → IsLocalExpansionSetting pos src m m' z C T →
    ∀ ξ : E → ℝ, (∀ e, |ξ e| ≤ 2 + TorusMetric.euclidNormVec (src e)) →
      IsCubicGrowthLocalKernel pos (4 * C) (firstVariationKernel T ξ) ∧
      IsCubicGrowthLocalKernel pos (16 * C) (secondVariationKernel T ξ) ∧
      ∀ f : ℝ, IsCubicGrowthLocalKernel pos (64 * C * |f| ^ 3) (taylorRemainderKernel T ξ f)
end YangMills.Construction.Tower.LocalFamilies
end
