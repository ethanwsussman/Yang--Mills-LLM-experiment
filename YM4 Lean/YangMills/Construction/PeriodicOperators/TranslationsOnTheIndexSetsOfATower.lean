import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
namespace TowerTranslations
open Tower
def posEdgeForward {L k j : ℕ} (x : FullSpace.Vertex L k j) (μ : Fin 4) : PosEdge L k j :=
  ⟨InfiniteLattice.Link.forwardFrom x μ, μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, 1 ≤ k → j ≤ k → ∀ n : Fin 4 → ℤ,
    FullSpace.MapsSublatticeOnto (meshAt L k j) (intShift n) ∧
    (∀ x : FullSpace.Vertex L k j,
      ((FullSpace.vertexImage (intShift n) x : FullSpace.Vertex L k j) : InfiniteLattice.AmbientSpace) =
        (x : InfiniteLattice.AmbientSpace) + castVec n ∧
      (∀ μ : Fin 4, FullSpace.edgeImage (intShift n) (InfiniteLattice.Link.forwardFrom x μ) =
        InfiniteLattice.Link.forwardFrom (FullSpace.vertexImage (intShift n) x) μ) ∧
      (∀ (μ ν : Fin 4) (h : μ < ν),
        FullSpace.vertexImage (intShift n) '' FullSpace.faceCorners (⟨x, μ, ν, h⟩ : FullSpace.Face L k j) =
          FullSpace.faceCorners
            (⟨FullSpace.vertexImage (intShift n) x, μ, ν, h⟩ : FullSpace.Face L k j))) ∧
    (∀ (c : Fin 3) (x : FullSpace.Vertex L k j),
      ((colourVertices L k j).translate n (c, x) : Fin 3 × FullSpace.Vertex L k j) =
        (c, FullSpace.vertexImage (intShift n) x)) ∧
    (∀ (c : Fin 3) (b : PosEdge L k j) (μ : Fin 4),
      b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L k j) μ →
      ((colourEdges L k j).translate n (c, b) : Fin 3 × PosEdge L k j) =
        (c, posEdgeForward (FullSpace.vertexImage (intShift n) b.1.initial) μ)) ∧
    (∀ (c : Fin 3) (x : FullSpace.Vertex L k j) (μ ν : Fin 4) (h : μ < ν),
      ((colourFaces L k j).translate n (c, (⟨x, μ, ν, h⟩ : FullSpace.Face L k j)) :
          Fin 3 × FullSpace.Face L k j) =
        (c, (⟨FullSpace.vertexImage (intShift n) x, μ, ν, h⟩ : FullSpace.Face L k j)))
end TowerTranslations
end YangMills.Construction.PeriodicOperators
end
