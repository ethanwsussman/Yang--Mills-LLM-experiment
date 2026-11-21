import YangMills.Construction.Geometry.ToriGeneralSide
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.GeneralTorus.CubePartitions
def centeredOffsets (k : ℕ) : Set (Fin 4 → ℤ) := {σ | ∀ μ, |(σ μ : ℝ)| ≤ ((k : ℝ) - 1) / 2}
def shiftedPoint (D : ScaleData) (s : ℝ) (z : D.Space) (σ : Fin 4 → ℤ) : D.Space :=
  z + torusProj D.torusSide fun μ => s * (σ μ : ℝ)
def shiftedSupCube (D : ScaleData) (s : ℝ) (z : D.Space) (σ : Fin 4 → ℤ) : Set D.Space :=
  supCube s (shiftedPoint D s z σ)
def latticeLine (D : ScaleData) (s : ℝ) (y : D.Space) (μ : Fin 4) : Set D.Space :=
  {x | x ∈ spacingLattice D.torusSide s ∧ ∀ ν, ν ≠ μ → x ν = y ν}
def PartitionCubes (D : ScaleData) (s : ℝ) : Prop :=
  IsEvenMultipleOf D.torusSide s ∧ 2 ≤ D.torusSide / s ∧
    (∀ y ∈ spacingLattice D.torusSide s, ∀ μ, ((latticeLine D s y μ).ncard : ℝ) = D.torusSide / s) ∧
    ⋃₀ D.cubePartition s = univ ∧
    (∀ Q ∈ D.cubePartition s, closure (interior Q) = Q) ∧
    (∀ y ∈ spacingLattice D.torusSide s, y ∈ interior (supCube s y)) ∧
    ∀ Q ∈ D.cubePartition s, ∀ Q' ∈ D.cubePartition s, ∀ x ∈ interior Q, x ∈ Q' → Q' = Q
def CoarseCubeDecomposition (D : ScaleData) (s : ℝ) (k : ℕ) : Prop :=
  ∀ z ∈ spacingLattice D.torusSide ((k : ℝ) * s),
    supCube ((k : ℝ) * s) z = ⋃ σ ∈ centeredOffsets k, shiftedSupCube D s z σ ∧
    (centeredOffsets k).ncard = k ^ 4 ∧
    InjOn (shiftedPoint D s z) (centeredOffsets k) ∧
    InjOn (shiftedSupCube D s z) (centeredOffsets k) ∧
    {x | x ∈ spacingLattice D.torusSide s ∧ x ∈ supCube ((k : ℝ) * s) z} =
      shiftedPoint D s z '' centeredOffsets k ∧
    {Q | Q ∈ D.cubePartition s ∧ Q ⊆ supCube ((k : ℝ) * s) z} =
      shiftedSupCube D s z '' centeredOffsets k
def LatticePointsInterior (D : ScaleData) (s : ℝ) (k : ℕ) : Prop :=
  ∀ x ∈ spacingLattice D.torusSide s,
    (∀ Q ∈ D.cubePartition ((k : ℝ) * s), x ∉ frontier Q) ∧
    ∃ Q ∈ D.cubePartition ((k : ℝ) * s), x ∈ interior Q ∧
      ∀ Q' ∈ D.cubePartition ((k : ℝ) * s), x ∈ Q' → Q' = Q
def CoarseUnionsAreFineUnions (D : ScaleData) (s : ℝ) (k : ℕ) : Prop :=
  ∀ X : Set D.Space, IsUnionOfCubes (D.cubePartition ((k : ℝ) * s)) X →
    IsUnionOfCubes (D.cubePartition s) X ∧
    (∀ y ∈ spacingLattice D.torusSide s, y ∈ X → supCube s y ⊆ X) ∧
    ∀ y ∈ spacingLattice D.torusSide s, y ∉ X → Disjoint (interior (supCube s y)) X
def ClosureOfDifference (D : ScaleData) (s : ℝ) : Prop :=
  (∀ X X' : Set D.Space, IsUnionOfCubes (D.cubePartition s) X →
    IsUnionOfCubes (D.cubePartition s) X' → X' ⊆ X →
    closure (X \ X') = ⋃₀ {Q | Q ∈ D.cubePartition s ∧ Q ⊆ X ∧ ¬Q ⊆ X'} ∧
    Disjoint (closure (X \ X')) (interior X')) ∧
  ∀ X : Set D.Space, IsUnionOfCubes (D.cubePartition s) X →
    closedComplement X = ⋃₀ {Q | Q ∈ D.cubePartition s ∧ ¬Q ⊆ X} ∧
    frontier X = X ∩ closedComplement X
def ThickeningsOfUnions (D : ScaleData) (s : ℝ) : Prop :=
  ∀ X : Set D.Space, IsUnionOfCubes (D.cubePartition s) X → ∀ j : ℕ,
    IsUnionOfCubes (D.cubePartition s) {x : D.Space | setSupDist {x} X ≤ ENNReal.ofReal ((j : ℝ) * s)}
def CubePartitionFacts : Prop :=
  ∀ (D : ScaleData) (s : ℝ) (k : ℕ), 0 < s → 1 ≤ k → Odd k →
    IsEvenMultipleOf D.torusSide ((k : ℝ) * s) →
    PartitionCubes D s ∧ CoarseCubeDecomposition D s k ∧
      LatticePointsInterior D s k ∧ CoarseUnionsAreFineUnions D s k ∧
      ClosureOfDifference D s ∧ ThickeningsOfUnions D s
end YangMills.Construction.GeneralTorus.CubePartitions
