import YangMills.Construction.Geometry.UnitLatticeBlocks
import YangMills.Construction.Torus.FormsAveragesAndOperatorsOnAGeneralTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.UnitSpacingLattice
open GeneralTorus
variable {Λ : UnitSpacingLattice}
instance edgeNonempty : Nonempty Λ.Edge := ⟨⟨0, 0⟩⟩
def shift (x : Λ.Point) (k : Fin 4 → ℤ) : Λ.Point := x + ∑ ν, k ν • Λ.basisVec ν
def shiftedEdge (x : Λ.Point) (μ : Fin 4) (k : Fin 4 → ℤ) : Λ.Edge := ⟨shift x k, μ⟩
variable (Λ) in
abbrev halfWidth : ℝ := halfSpan Λ.blockFactor
variable (Λ) in
def IsAverageIndex (μ : Fin 4) (k : Fin 4 → ℤ) : Prop :=
  -Λ.halfWidth ≤ (k μ : ℝ) ∧ (k μ : ℝ) ≤ 3 * Λ.halfWidth ∧
    ∀ ν, ν ≠ μ → |(k ν : ℝ)| ≤ Λ.halfWidth
def IsBlockAverageWeight (c : Λ.CenterEdge) (q : Λ.Edge → ℝ) : Prop :=
  (∀ k, Λ.IsAverageIndex c.axis k →
    q (shiftedEdge c.src c.axis k) =
      (Λ.blockFactor : ℝ) ^ (-4 - 1 : ℤ) * (tentMultiplicity Λ.blockFactor (k c.axis) : ℝ)) ∧
  ∀ b, (¬∃ k, Λ.IsAverageIndex c.axis k ∧ b = shiftedEdge c.src c.axis k) → q b = 0
def blockAverageWeight (c : Λ.CenterEdge) : Λ.Edge → ℝ :=
  Classical.epsilon (IsBlockAverageWeight c)
def axisPathEdge (c : Λ.CenterEdge) (i : ℕ) : Λ.Edge :=
  ⟨c.src + i • Λ.basisVec c.axis, c.axis⟩
def IsPivotEdge (c : Λ.CenterEdge) (b : Λ.Edge) : Prop :=
  b ∈ edgeCorridor c ∧ ∃ i, i < Λ.blockFactor ∧ b = axisPathEdge c i
def pivotEdge (c : Λ.CenterEdge) : Λ.Edge := Classical.epsilon (IsPivotEdge c)
variable (Λ) in
def CubesPartition : Prop :=
  (∀ y ∈ Λ.blockCenters, (Λ.cube y).Nonempty) ∧
    ∀ x, ∃! y, y ∈ Λ.blockCenters ∧ x ∈ Λ.cube y
variable (Λ) in
def EdgesFromACube : Prop :=
  ∀ (y : Λ.Point) (hy : y ∈ Λ.blockCenters) (k : Fin 4 → ℤ), (∀ ρ, |(k ρ : ℝ)| ≤ Λ.halfWidth) →
    ∀ ν : Fin 4,
      ((k ν : ℝ) < Λ.halfWidth →
        (shiftedEdge y ν k).InCube y ∧
        (∀ y' ∈ Λ.blockCenters, y' ≠ y → ¬(shiftedEdge y ν k).InCube y') ∧
        ∀ c : Λ.CenterEdge, shiftedEdge y ν k ∉ edgeCorridor c) ∧
      ((k ν : ℝ) = Λ.halfWidth →
        (∀ y' ∈ Λ.blockCenters, ¬(shiftedEdge y ν k).InCube y') ∧
        shiftedEdge y ν k ∈ edgeCorridor (⟨y, hy, ν⟩ : Λ.CenterEdge) ∧
        ∀ c : Λ.CenterEdge, shiftedEdge y ν k ∈ edgeCorridor c → c = ⟨y, hy, ν⟩)
def PointsOfTheTwoCubes (c : Λ.CenterEdge) : Prop :=
  Set.InjOn (shift c.src) {k | MemBondWindow Λ.blockFactor c.axis k} ∧
  shift c.src '' {k | MemBondWindow Λ.blockFactor c.axis k ∧
    (k c.axis : ℝ) ≤ Λ.halfWidth} = Λ.cube c.src ∧
  shift c.src '' {k | MemBondWindow Λ.blockFactor c.axis k ∧
    Λ.halfWidth < (k c.axis : ℝ)} = Λ.cube c.tgt
def EdgesOfTheWeights (c : Λ.CenterEdge) : Prop :=
  shiftedEdge c.src c.axis '' {k | Λ.IsAverageIndex c.axis k ∧
    (k c.axis : ℝ) < Λ.halfWidth} = {b | b.axis = c.axis ∧ b.InCube c.src} ∧
  shiftedEdge c.src c.axis '' {k | Λ.IsAverageIndex c.axis k ∧
    (k c.axis : ℝ) = Λ.halfWidth} = edgeCorridor c ∧
  shiftedEdge c.src c.axis '' {k | Λ.IsAverageIndex c.axis k ∧
    Λ.halfWidth < (k c.axis : ℝ)} = {b | b.axis = c.axis ∧ b.InCube c.tgt}
variable (Λ) in
def TentMultiplicityValues : Prop :=
  (∀ s : ℤ, -Λ.halfWidth ≤ (s : ℝ) → (s : ℝ) < Λ.halfWidth →
    (tentMultiplicity Λ.blockFactor s : ℝ) = s + Λ.halfWidth + 1 ∧
    (tentMultiplicity Λ.blockFactor s : ℝ) ∈ Set.Icc (1 : ℝ) ((Λ.blockFactor : ℝ) - 1)) ∧
  (∀ s : ℤ, (s : ℝ) = Λ.halfWidth → tentMultiplicity Λ.blockFactor s = Λ.blockFactor) ∧
  (∀ s : ℤ, Λ.halfWidth < (s : ℝ) → (s : ℝ) ≤ 3 * Λ.halfWidth →
    (tentMultiplicity Λ.blockFactor s : ℝ) = 3 * Λ.halfWidth + 1 - s ∧
    (tentMultiplicity Λ.blockFactor s : ℝ) ∈ Set.Icc (1 : ℝ) ((Λ.blockFactor : ℝ) - 1))
def BlockAverageWeightBounds (c : Λ.CenterEdge) : Prop :=
  (∀ b, 0 ≤ blockAverageWeight c b ∧ blockAverageWeight c b ≤ (Λ.blockFactor : ℝ) ^ (-4 : ℤ)) ∧
  ∑ᶠ b, blockAverageWeight c b = 1 ∧
  (Function.support (blockAverageWeight c)).encard =
    ((2 * Λ.blockFactor - 1) * Λ.blockFactor ^ 3 : ℕ)
def PivotEdgeOfACenterEdge (c : Λ.CenterEdge) : Prop :=
  (∃ i : ℕ, (i : ℝ) = Λ.halfWidth ∧ i < Λ.blockFactor ∧ axisPathEdge c i ∈ edgeCorridor c ∧
    (∀ j, j < Λ.blockFactor → axisPathEdge c j ∈ edgeCorridor c → j = i) ∧
    pivotEdge c = axisPathEdge c i) ∧
  (∀ y ∈ Λ.blockCenters, pivotEdge c ∉ Λ.axialTree y) ∧
  blockAverageWeight c (pivotEdge c) = (Λ.blockFactor : ℝ) ^ (-4 : ℤ) ∧
  ∀ c' : Λ.CenterEdge, c' ≠ c → blockAverageWeight c (pivotEdge c') = 0
def CubesCorridorsAndBlockAverageWeights : Prop :=
  ∀ Λ : UnitSpacingLattice,
    Λ.CubesPartition ∧ Λ.EdgesFromACube ∧ Λ.TentMultiplicityValues ∧
    ∀ c : Λ.CenterEdge,
      PointsOfTheTwoCubes c ∧
      IsBlockAverageWeight c (blockAverageWeight c) ∧
      (∀ B : Λ.Edge → ℝ, blockAverage B c = ∑ᶠ b, blockAverageWeight c b * B b) ∧
      EdgesOfTheWeights c ∧ BlockAverageWeightBounds c ∧ PivotEdgeOfACenterEdge c
end YangMills.Construction.UnitSpacingLattice
