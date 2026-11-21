import YangMills.Construction.ChessboardTori.CoarseGridsOfAGrid
import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
def coarseCellIndices (L b : ℕ) (k j : Fin 4 → ℤ) : Set (Fin 4 → ℤ) :=
  {i | ∀ μ, k μ + (L : ℤ) ^ b * j μ ≤ i μ ∧ i μ ≤ k μ + (L : ℤ) ^ b * j μ + (L : ℤ) ^ b - 1}
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def MoverSigns : Prop :=
  ∀ (k k' : Fin 4 → ℤ) (r : g.reflectionGroup), r.1 '' g.cell k = g.cell k' →
    orientationSign r.1 = (-1) ^ (∑ μ, (k' μ - k μ)) ∧
      ((∀ μ, Even (k' μ - k μ)) →
        (r.1 : AmbientSpace → AmbientSpace) = translate fun μ => g.cellSide * ((k' μ - k μ : ℤ) : ℝ))
def HalfOddInBlock : Prop :=
  ∀ B ∈ g.blocks, ∀ S ∈ g.cellSet,
    ((g.cellsWithin B).ncard : ℝ) = g.cellsAcross ^ 4 ∧
      (({S' ∈ g.cellsWithin B | ∃ r : g.reflectionGroup, r.1 '' S = S' ∧
          orientationSign r.1 = -1}).ncard : ℝ) =
        1 / 2 * g.cellsAcross ^ 4
def CoarseningWallsAndGroup (b : ℕ) (k : Fin 4 → ℤ) : Prop :=
  (∀ (μ : Fin 4) (n : ℤ),
    (g.coarsen b k).wall μ n = g.wall μ (k μ + n * (D.L : ℤ) ^ b) ∧
      (g.coarsen b k).reflect μ n = g.reflect μ (k μ + n * (D.L : ℤ) ^ b)) ∧
    ∃ h : (g.coarsen b k).reflectionGroup ≤ g.reflectionGroup,
      ∀ r : (g.coarsen b k).reflectionGroup,
        orientationSign r.1 = orientationSign (Subgroup.inclusion h r).1
def CoarseningCells (b : ℕ) (k : Fin 4 → ℤ) : Prop :=
  (∀ j : Fin 4 → ℤ,
    (g.coarsen b k).cell j = ⋃ i ∈ coarseCellIndices D.L b k j, g.cell i ∧
      (g.cell '' coarseCellIndices D.L b k j).ncard = D.L ^ (4 * b) ∧
      {S ∈ g.cellSet | S ⊆ (g.coarsen b k).cell j} = g.cell '' coarseCellIndices D.L b k j) ∧
    (∀ S ∈ g.cellSet, ∃! S', S' ∈ (g.coarsen b k).cellSet ∧ S ⊆ S') ∧
    (∀ S ∈ g.cellSet, ∀ S' ∈ (g.coarsen b k).cellSet, S ⊆ S' →
      cellObservables (D := D) S ⊆ cellObservables (D := D) S') ∧
    (2 * (g.coarsen b k).cellSide ≤ PeriodicLattice.torusSide D.L D.m →
      (g.coarsen b k).blocks ⊆ g.blocks)
def CoarseningTransports (b : ℕ) (k : Fin 4 → ℤ) : Prop :=
  (∀ S ∈ g.cellSet, ∀ S' ∈ (g.coarsen b k).cellSet, S ⊆ S' → ∀ F ∈ cellObservables (D := D) S,
    ∀ r : (g.coarsen b k).reflectionGroup,
      r.1 '' S ∈ g.cellSet ∧ r.1 '' S' ∈ (g.coarsen b k).cellSet ∧ r.1 '' S ⊆ r.1 '' S' ∧
        (g.coarsen b k).transportTo S' (r.1 '' S') F = g.transportTo S (r.1 '' S) F) ∧
    ∀ S' ∈ (g.coarsen b k).cellSet, ∀ (r₁ r₂ : (g.coarsen b k).reflectionGroup)
      (S₁ S₂ : Set AmbientSpace),
      S₁ ∈ g.cellSet → S₁ ⊆ S' → S₂ ∈ g.cellSet → S₂ ⊆ S' → (r₁, S₁) ≠ (r₂, S₂) →
        r₁.1 '' S₁ ≠ r₂.1 '' S₂
def CellsInEnclosingBaseCell : Prop :=
  ∀ O : Set (Set AmbientSpace), g.IsFiniteCellFamily O → ∀ S ∈ O,
    S ⊆ (g.enclosingCoarsening O).baseCell
end ReflectionGrid
def CellParityAndCoarsening.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.IsCoarse →
    g.MoverSigns ∧
      (2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m → g.HalfOddInBlock) ∧
      (∀ (b : ℕ) (k : Fin 4 → ℤ), g.CoarseningWallsAndGroup b k ∧
        g.CoarseningCells b k ∧ g.CoarseningTransports b k) ∧
      g.CellsInEnclosingBaseCell
end YangMills.Construction.ChessboardTori
end
