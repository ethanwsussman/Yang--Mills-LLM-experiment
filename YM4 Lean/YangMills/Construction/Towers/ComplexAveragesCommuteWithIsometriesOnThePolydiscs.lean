import YangMills.Construction.Towers.AveragingMapNearTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def ComplexSmoothingEquivariance.Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k →
    ∀ f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace, IsDistancePreserving f →
      MapsSublatticeOnto (meshAt L k (j + 1)) f →
      ∀ e : Edge L k (j + 1), e.IsPositivelyOriented →
        ∀ V ∈ nearIdentityPolydisc L k j (polydiscRadius L) e,
          (∀ y ∈ ({e.initial, e.terminal} : Set (Vertex L k (j + 1))),
            ∀ x ∈ cubeVertices L (meshAt L k j) y,
              complexContourMean L (pushField f V) (vertexImage f y) (vertexImage f x) =
                complexContourMean L V y x) ∧
          complexSmoothing L (pushField f V) (edgeImage f e) = complexSmoothing L V e
end YangMills.Construction.Tower.FullSpace
end
