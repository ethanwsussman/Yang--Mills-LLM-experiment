import YangMills.Construction.Lattice.CubesOfOrder
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice
open scoped Topology
noncomputable section
namespace YangMills.Construction.SeparatedSequences.BaseParameters
def FormsPartition {ι α : Type*} (A : ι → Set α) (S : Set α) : Prop :=
  (∀ a, (A a).Nonempty) ∧ Pairwise (fun a b => Disjoint (A a) (A b)) ∧ ⋃ a, A a = S
variable (P : BaseParameters)
def meshMultiples (i : ℕ) : Set ℝ := {c | ∃ n : ℤ, c = P.orderMesh i * (n : ℝ)}
def meshHalfMultiples (i : ℕ) : Set ℝ :=
  {c | ∃ n : ℤ, c = P.orderMesh i * ((n : ℝ) + 1 / 2)}
def AvoidsHalfMesh (i : ℕ) (x : P.Torus) : Prop :=
  ∀ c, P.IsLiftCoordinate x c → c ∉ P.meshHalfMultiples i
def orderScaleRatio (i i' : ℕ) : ℕ := P.L ^ (i - i')
def shiftedPoint (i' : ℕ) (y : P.Torus) (v : Fin 4 → ℤ) : P.Torus :=
  shiftBy P.L P.m P.K P.t y (P.orderMesh i' • ∑ μ, (v μ : ℝ) • coordVec μ)
def boundedOffsets (N : ℕ) : Set (Fin 4 → ℤ) := {v | ∀ μ, |(v μ : ℝ)| ≤ ((N : ℝ) - 1) / 2}
def IsOrderCubeUnion (i : ℕ) (X : Set P.Torus) : Prop :=
  ∃ C ⊆ {Q | P.IsOrderCube i Q}, X = ⋃₀ C
def OrderDepthIdentification (i : ℕ) : Prop :=
  P.lengthInUnits (torusSide P.L P.m) = P.torusSideInUnits ∧
    P.lengthInUnits (meshSize P.L (levelDepth P.K i)) = P.orderMesh i ∧
    P.orderCentreSet i = (sublattice P.L P.m (levelDepth P.K i) : Set P.Torus) ∧
    (∀ (y : P.orderCentreSet i) (y' : Site P.L P.m (levelDepth P.K i)), (y : P.Torus) = y' →
      P.closedOrderCube i y = cubeAround y') ∧
    {C | P.IsOrderCube i C} = standardCubePartition P.L P.m (levelDepth P.K i)
def LowOrderLevelIdentification : Prop :=
  ∀ n ≤ P.t, P.orderMesh n = P.levelMeshRatio n ∧
    P.orderCentreSet n = (sublattice P.L P.m (levelDepth P.K n) : Set P.Torus) ∧
    ∀ (y : P.orderCentreSet n) (y' : P.LatticeSite n), (y : P.Torus) = y' →
      P.closedOrderCube n y = cube (D := P) y'
def BlockCubesMatchOrders : Prop :=
  ∀ n ≤ P.K,
    (-(P.m : ℤ) ≤ P.scales.blockPartitionIndex n ↔ n + P.blockExp ≤ P.m + P.K) ∧
    (n + P.blockExp ≤ P.m + P.K →
      standardCubePartition P.L P.m (P.scales.blockPartitionIndex n) =
        {C | P.IsOrderCube (n + P.blockExp) C}) ∧
    ((∃ C, P.IsOrderCube (n + P.blockExp) C) ↔ n + P.blockExp ≤ P.m + P.K)
def NestedOrderLattices (i i' : ℕ) : Prop :=
  P.torusSideInUnits / P.orderMesh i = ((2 * P.L ^ (P.m + P.K - i) : ℕ) : ℝ) ∧
    Even (2 * P.L ^ (P.m + P.K - i)) ∧
    (∀ (x : P.Torus) (w w' : Fin 4 → ℝ) (μ : Fin 4),
      IsLevelLift P.L P.m P.K P.t x w → IsLevelLift P.L P.m P.K P.t x w' →
        (w μ ∈ P.meshMultiples i ↔ w' μ ∈ P.meshMultiples i) ∧
        (w μ ∈ P.meshHalfMultiples i ↔ w' μ ∈ P.meshHalfMultiples i)) ∧
    (∀ μ : Fin 4, ((((fun y : P.Torus => y μ) '' P.orderCentreSet i).ncard : ℕ) : ℝ) =
      P.torusSideInUnits / P.orderMesh i) ∧
    2 ≤ P.torusSideInUnits / P.orderMesh i ∧
    P.meshMultiples i ⊆ P.meshMultiples i' ∧
    P.orderCentreSet i ⊆ P.orderCentreSet i' ∧
    P.meshHalfMultiples i ⊆ P.meshHalfMultiples i' ∧
    Disjoint (P.meshHalfMultiples i') (P.meshMultiples i')
def OrderCubeCover (i : ℕ) : Prop :=
  (∀ x : P.Torus, ∃ y : P.orderCentreSet i, x ∈ P.closedOrderCube i y) ∧
    (∀ x : P.Torus, P.AvoidsHalfMesh i x →
      (∃! y : P.orderCentreSet i, x ∈ P.closedOrderCube i y) ∧
        ∀ y : P.orderCentreSet i, x ∈ P.closedOrderCube i y → x ∈ P.openOrderCube i y) ∧
    (∀ y : P.orderCentreSet i, ∀ x ∈ P.closedOrderCube i y \ P.openOrderCube i y,
      ∃ c, P.IsLiftCoordinate x c ∧ c ∈ P.meshHalfMultiples i) ∧
    ∀ y : P.orderCentreSet i, IsOpen (P.openOrderCube i y) ∧
      (∀ y' : P.orderCentreSet i, y' ≠ y → Disjoint (P.openOrderCube i y) (P.closedOrderCube i y')) ∧
      closure (P.openOrderCube i y) = P.closedOrderCube i y
def NestedOrderCubes (i i' : ℕ) : Prop :=
  ∀ y : P.orderCentreSet i,
    (∀ z : P.orderCentreSet i',
      ((z : P.Torus) ∈ P.closedOrderCube i y →
        P.closedOrderCube i' z ⊆ P.closedOrderCube i y ∧ P.openOrderCube i' z ⊆ P.openOrderCube i y) ∧
      ((z : P.Torus) ∉ P.closedOrderCube i y → Disjoint (P.openOrderCube i' z) (P.closedOrderCube i y))) ∧
    P.closedOrderCube i y =
      ⋃ z : {z : P.orderCentreSet i' // (z : P.Torus) ∈ P.closedOrderCube i y}, P.closedOrderCube i' z.1
def NestedOrderBlocks (i i' : ℕ) : Prop :=
  (∀ y : P.orderCentreSet i,
    P.orderCentreSet i' ∩ P.closedOrderCube i y =
        P.shiftedPoint i' y '' boundedOffsets (P.orderScaleRatio i i') ∧
      InjOn (P.shiftedPoint i' y) (boundedOffsets (P.orderScaleRatio i i')) ∧
      (P.shiftedPoint i' y '' boundedOffsets (P.orderScaleRatio i i')).ncard =
        P.orderScaleRatio i i' ^ dimension ∧
      P.shiftedPoint i' y '' boundedOffsets (P.orderScaleRatio i i') ⊆ P.openOrderCube i y) ∧
    FormsPartition (fun y : P.orderCentreSet i => P.orderCentreSet i' ∩ P.closedOrderCube i y)
      (P.orderCentreSet i')
def FineBlockStructure : Prop :=
  (∀ n ≤ P.t,
    (∀ y : P.LatticeSite n, (fineBlock (D := P) y).ncard = P.L ^ (n * dimension)) ∧
    (∀ (y : P.LatticeSite n) (μ : Fin 4),
      fineBlock (D := P) (y + unitStep P.L P.m (levelDepth P.K n) μ) =
        (fun x : P.Torus => x + (unitStep P.L P.m (levelDepth P.K n) μ : P.Torus)) ''
          fineBlock (D := P) y) ∧
    FormsPartition (fun y : P.LatticeSite n => fineBlock (D := P) y)
      (sublattice P.L P.m (levelDepth P.K 0) : Set P.Torus)) ∧
  (∀ y : P.LatticeSite 0, fineBlock (D := P) y = {(y : P.Torus)}) ∧
  ∀ n, n + 1 ≤ P.t → ∀ y : P.LatticeSite (n + 1),
    (coarseBlock (D := P) y).ncard = P.L ^ dimension ∧
    fineBlock (D := P) y =
      ⋃ z : {z : P.LatticeSite n // (z : P.Torus) ∈ coarseBlock (D := P) y},
        fineBlock (D := P) z.1 ∧
    Pairwise fun z z' : {z : P.LatticeSite n // (z : P.Torus) ∈ coarseBlock (D := P) y} =>
      Disjoint (fineBlock (D := P) z.1) (fineBlock (D := P) z'.1)
def OrderCubeRegions (i i' : ℕ) : Prop :=
  ∀ X : Set P.Torus, P.IsOrderCubeUnion i X →
    IsClosed X ∧
    X = ⋃ z : {z : P.orderCentreSet i' // (z : P.Torus) ∈ X}, P.closedOrderCube i' z.1 ∧
    (∀ z : P.orderCentreSet i', (z : P.Torus) ∉ X → Disjoint (P.openOrderCube i' z) X) ∧
    complementRegion (levelDepth P.K i') X =
      ⋃ z : {z : P.orderCentreSet i' // (z : P.Torus) ∉ X}, P.closedOrderCube i' z.1 ∧
    complementRegion (levelDepth P.K i') X = complementRegion (levelDepth P.K i) X ∧
    X ∪ complementRegion (levelDepth P.K i') X = univ ∧
    (∀ j ≤ P.m + P.K, ∀ x ∈ P.orderCentreSet j, P.AvoidsHalfMesh i' x) ∧
    ∀ x : P.Torus, P.AvoidsHalfMesh i' x →
      (∀ z : P.orderCentreSet i', x ∈ P.closedOrderCube i' z → (x ∈ X ↔ (z : P.Torus) ∈ X)) ∧
      (∃ U ∈ 𝓝 x, U ⊆ X ∨ Disjoint U X) ∧
      (x ∈ X ↔ x ∉ complementRegion (levelDepth P.K i') X)
def ShellCubeStructure (Ω : ℕ → Set P.Torus) : Prop :=
  ∀ n ≤ P.t,
    P.IsOrderCubeUnion n (P.memberAt Ω n) ∧
    P.IsOrderCubeUnion n (P.memberAt Ω (n + 1)) ∧
    P.layerSites Ω n =
      {y : P.LatticeSite n |
        (y : P.Torus) ∈ P.memberAt Ω n ∧ (y : P.Torus) ∉ P.memberAt Ω (n + 1)} ∧
    ∀ y ∈ P.layerSites Ω n,
      cube (D := P) y ⊆ SeparatedSequences.layerSet P.scales Ω n ∧
      ∀ c : P.orderCentreSet n, (c : P.Torus) = y →
        fineBlock (D := P) y ⊆ openOrderCubeAt c ∧
        openOrderCubeAt c ⊆ P.memberAt Ω n \ P.memberAt Ω (n + 1) ∧
        ∀ k, k ≠ n → Disjoint (openOrderCubeAt c) (SeparatedSequences.layerSet P.scales Ω k)
end YangMills.Construction.SeparatedSequences.BaseParameters
namespace YangMills.Construction.SeparatedSequences
def LatticeCubeStatement : Prop :=
  ∀ (P : SequenceDatum) (i i' : ℕ), i' ≤ i → i ≤ P.m + P.K →
    Odd (P.orderScaleRatio i i') ∧
    P.OrderDepthIdentification i ∧
    P.LowOrderLevelIdentification ∧
    P.BlockCubesMatchOrders ∧
    P.NestedOrderLattices i i' ∧
    P.OrderCubeCover i ∧
    P.NestedOrderCubes i i' ∧
    P.NestedOrderBlocks i i' ∧
    P.FineBlockStructure ∧
    P.OrderCubeRegions i i' ∧
    P.ShellCubeStructure P.region
end YangMills.Construction.SeparatedSequences
end
