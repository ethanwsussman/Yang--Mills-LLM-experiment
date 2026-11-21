import YangMills.Construction.Towers.TheDensityOfAnAbelianField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
def DensityGaugeInvariant : Prop :=
  ∀ z : ℝ, 0 < z → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ (g : FullSpace.Vertex L 0 0 → ℝ) (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ),
      DensityDefined z θ →
        DensityDefined z (fun e => θ e + FullSpace.vertexDifference g e) ∧
          ∀ x : FullSpace.Vertex L 0 0,
            densityAt z (fun e => θ e + FullSpace.vertexDifference g e) x = densityAt z θ x
end YangMills.Construction.Tower.AbelianFieldDensity
end
