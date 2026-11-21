import YangMills.Construction.Towers.ContourFamiliesAtTheSideInfinity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open InfiniteLattice (AmbientSpace)
def ContourEndpoints : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 1 ≤ k → 1 ≤ j → j ≤ k →
    (∀ n : ℕ, 0 < n → ∀ (y : Vertex L n k j) (x : Vertex L n k (j - 1)),
      (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y →
        ∀ Γ ∈ PeriodicLattice.contourSet y x,
          PeriodicLattice.IsBondPathFromTo Γ
            (y.toSublattice (PeriodicLattice.levelDepth k (j - 1))) x) ∧
    ∀ (y : FullSpace.Vertex L k j) (x : FullSpace.Vertex L k (j - 1)),
      (x : AmbientSpace) ∈ FullSpace.cube L (meshAt L k (j - 1)) y →
        ∀ Γ ∈ FullSpace.contourSet L y x,
          FullSpace.LinksJoin (y : AmbientSpace) (x : AmbientSpace) Γ
end YangMills.Construction.Tower
end
