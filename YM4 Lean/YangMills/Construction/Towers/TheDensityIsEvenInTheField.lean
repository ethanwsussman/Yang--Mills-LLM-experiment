import YangMills.Construction.Towers.TheDensityOfAnAbelianField
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
def DensityEvenInField : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z →
    ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, DensityDefined (L := L) z θ →
      DensityDefined (L := L) z (fun e => -θ e) ∧
        ∀ x : FullSpace.Vertex L 0 0, densityAt z (fun e => -θ e) x = densityAt z θ x
end YangMills.Construction.Tower.AbelianFieldDensity
end
