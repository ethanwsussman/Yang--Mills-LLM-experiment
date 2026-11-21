import YangMills.Construction.ChessboardTori.ChessboardIntegral
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ReflectionGrid
variable {S : ChessboardSetup} (g : ReflectionGrid S)
def HasEdgeStraddlingWall (p : S.Plaquette) : Prop :=
  ∃ e : S.Link, S.IsEdgeOf e p ∧ ∃ (μ : Fin 4) (k : ℤ), g.Straddles e μ k
def InInteriorOfCell (p : S.Plaquette) : Prop :=
  ∃ C ∈ g.cellSet, (∀ z ∈ S.faceCorners p, (z : AmbientSpace) ∈ interior C) ∧
    p.center ∈ interior C
end ReflectionGrid
namespace CoupledGrid
variable (O : CoupledGrid)
def cellExpWeight (W : AmbientSpace → ℂ) (C : Set AmbientSpace) :
    O.toChessboardSetup.GaugeField → ℂ :=
  fun U => Complex.exp (O.toChessboardSetup.smeared (W * C.indicator 1) U)
end CoupledGrid
def ReflectionPeriodicWeightsAsCellFunctions.Statement : Prop :=
  ∀ (O : CoupledGrid) (W : AmbientSpace → ℂ), O.grid.IsReflectionPeriodic W →
    (∀ r : O.grid.reflectionGroup, W ∘ ⇑(r.1⁻¹) = Conventions.signedConjFun (orientationSign r.1) W) ∧
    (∀ (x : AmbientSpace) (k : Fin 4 → ℤ),
      W (x + TestFunctions.latticeTranslate (2 * O.grid.cellSide) k) = W x) ∧
    (∀ p : O.toChessboardSetup.Plaquette,
      (O.grid.HasEdgeStraddlingWall p ∨ O.grid.InInteriorOfCell p) ∧
      (O.grid.HasEdgeStraddlingWall p → p.center ∈ O.grid.walls) ∧
      (O.grid.InInteriorOfCell p → p.center ∉ O.grid.walls)) ∧
    (∀ C ∈ O.grid.cellSet,
      (∀ U : O.toChessboardSetup.GaugeField, O.toChessboardSetup.smeared (W * C.indicator 1) U =
        ∑ᶠ p ∈ {p : O.toChessboardSetup.Plaquette | p.center ∈ interior C},
          W p.center * (InfiniteLattice.faceEnergy U p : ℂ)) ∧
      O.cellExpWeight W C ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) C ∧
      ∀ C' ∈ O.grid.cellSet,
        O.grid.transportTo C C' (O.cellExpWeight W C) = O.cellExpWeight W C') ∧
    ∀ (n : EvenIndexVector), ∀ C ∈ O.grid.cellSet,
      O.chessboardPartitionOn n C (O.cellExpWeight W C) =
        (O.periodSubgroupOf n).weightedPartition W
end ChessboardTori
end YangMills.Construction
end
