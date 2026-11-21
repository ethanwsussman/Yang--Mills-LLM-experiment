import YangMills.Construction.Towers.QuotientMapOnBonds
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
open InfiniteLattice (AmbientSpace)
def DoubleCubeLinksAndTorusImage : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 1 ≤ j → j ≤ k →
    ∀ c : FullSpace.Edge L k j, c.IsPositivelyOriented →
    (doubleCubeLinks L (meshAt L k (j - 1)) c =
        {b : FullSpace.Edge L k (j - 1) |
          (b.initial : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) c.initial ∪
              cube L (meshAt L k (j - 1)) c.terminal ∧
            (b.terminal : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) c.initial ∪
              cube L (meshAt L k (j - 1)) c.terminal} ∧
      ∀ b ∈ doubleCubeLinks L (meshAt L k (j - 1)) c,
        b.opposite ∈ doubleCubeLinks L (meshAt L k (j - 1)) c) ∧
    ∀ n : ℕ, 0 < n →
      (projEdge L n k j c).source = projVertex L n k j c.initial ∧
      (projEdge L n k j c).target = projVertex L n k j c.terminal ∧
      (projEdge L n k j c).IsPositivelyOriented ∧
      InjOn (TorusMetric.torusProj (PeriodicLattice.torusSide L n))
        (doubleCube L (meshAt L k (j - 1)) c) ∧
      TorusMetric.torusProj (PeriodicLattice.torusSide L n) ''
          cube L (meshAt L k (j - 1)) c.initial =
        PeriodicLattice.unitBlock (projVertex L n k j c.initial) ∧
      TorusMetric.torusProj (PeriodicLattice.torusSide L n) ''
          cube L (meshAt L k (j - 1)) c.terminal =
        PeriodicLattice.unitBlock (projVertex L n k j c.terminal) ∧
      BijOn (projEdge L n k (j - 1)) (doubleCubeLinks L (meshAt L k (j - 1)) c)
        (PeriodicLattice.bondsInDoubleBlock (projEdge L n k j c))
end YangMills.Construction.Tower.FullSpace
end
