import YangMills.Construction.RunningCouplingSlope.LocalFamiliesOfCells
import YangMills.Construction.RunningCouplingSlope.TriplesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
variable {L n k m : ℕ}
def levelVertexCell (x : Tower.Vertex L n k m) : Tower.Vertex L n k k :=
  fineVertexCell (x.toSublattice (PeriodicLattice.levelDepth k 0))
def FormSupportedInCell (y : Tower.Vertex L n k k) (B : Tower.Edge L n k m → Matrices.ComplexMatrix2) : Prop :=
  ∀ e : Tower.PositiveEdge L n k m, levelVertexCell e.1.source ≠ y → B e.1 = 0
def LevelFormsSupportedInCell (y : Tower.Vertex L n k k) (ξ : LevelForms L n k) : Prop :=
  FormSupportedInCell y (ξ.1 : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) ∧
    ∀ i : Fin k, FormSupportedInCell y (ξ.2 i : Tower.Edge L n k (i + 1) → Matrices.ComplexMatrix2)
def TripleSupportedInCell (y : Tower.Vertex L n k k) (σ : LevelTriple L n k) : Prop :=
  LevelFormsSupportedInCell y σ.1 ∧ LevelFormsSupportedInCell y σ.2.1 ∧
    FormSupportedInCell y (σ.2.2 : Tower.Edge L n k k → Matrices.ComplexMatrix2)
end RunningCouplingSlope
end YangMills.Construction
end
