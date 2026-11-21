import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.IndexBoxesAndBlocksOfOrderZero
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace Tower
namespace FullSpace
section Offsets
variable {a : ℝ}
def cubeOffsetPoint (a' : ℝ) (y : InfiniteLattice.LatticePoint a) (ν : Fin 4 → ℤ) :
    AmbientSpace :=
  (y : AmbientSpace) + ∑ μ, Pi.single μ ((ν μ : ℝ) * a')
def SameAxisAndSense {a' : ℝ} (c : InfiniteLattice.Link a)
    (b : InfiniteLattice.Link a') : Prop :=
  ∃ μ : Fin 4,
    (c.terminal - c.initial = InfiniteLattice.axisStep a μ ∧
        b.terminal - b.initial = InfiniteLattice.axisStep a' μ) ∨
      (c.terminal - c.initial = -InfiniteLattice.axisStep a μ ∧
        b.terminal - b.initial = -InfiniteLattice.axisStep a' μ)
end Offsets
structure CubesOfOrderPartition (L k j n : ℕ) : Prop where
  offsetPoint_mem : ∀ (y : Vertex L k j), ∀ ν ∈ offsetBox L n,
    cubeOffsetPoint (meshAt L k (j - n)) y ν ∈
      InfiniteLattice.latticeSubgroup (meshAt L k (j - n))
  offsetPoint_injOn : ∀ y : Vertex L k j,
    Set.InjOn (cubeOffsetPoint (meshAt L k (j - n)) y) (offsetBox L n)
  offsetBox_ncard : (offsetBox L n).ncard = L ^ (4 * n)
  cube_ncard : ∀ y : Vertex L k j,
    (cubeOfOrder L (meshAt L k (j - n)) n y).ncard = L ^ (4 * n)
  center_mem : ∀ y : Vertex L k j,
    (y : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n y
  pointReflection_image : ∀ y : Vertex L k j,
    (fun x : AmbientSpace => (y : AmbientSpace) - (x - (y : AmbientSpace))) ''
        cubeOfOrder L (meshAt L k (j - n)) n y =
      cubeOfOrder L (meshAt L k (j - n)) n y
  cube_add : ∀ y w : Vertex L k j,
    cubeOfOrder L (meshAt L k (j - n)) n (y + w) =
      (fun x : AmbientSpace => x + (w : AmbientSpace)) ''
        cubeOfOrder L (meshAt L k (j - n)) n y
  iUnion_cube : (⋃ y : Vertex L k j, cubeOfOrder L (meshAt L k (j - n)) n y) =
    (InfiniteLattice.latticeSubgroup (meshAt L k (j - n)) : Set AmbientSpace)
  pairwise_disjoint_cube : Pairwise (Function.onFun Disjoint
    fun y : Vertex L k j => cubeOfOrder L (meshAt L k (j - n)) n y)
structure CubeIsDisjointUnionOfSubcubes (L k j n : ℕ) (y : Vertex L k j) : Prop where
  cube_eq_biUnion : cubeOfOrder L (meshAt L k (j - n)) n y =
    ⋃ x ∈ cubeVertices L (meshAt L k (j - 1)) y,
      cubeOfOrder L (meshAt L k (j - n)) (n - 1) x
  pairwiseDisjoint_subcube : (cubeVertices L (meshAt L k (j - 1)) y).PairwiseDisjoint
    fun x => cubeOfOrder L (meshAt L k (j - n)) (n - 1) x
def EndpointsInOneCubeOrAcrossEdge (L k j : ℕ) (b : Edge L k (j - 1)) : Prop :=
  (∃ y : Vertex L k j, (b.initial : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) y ∧
      (b.terminal : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) y) ∨
    ∃ c : Edge L k j,
      ((b.initial : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) c.initial ∧
        (b.terminal : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) c.terminal) ∧
      SameAxisAndSense c b ∧
      ∀ c' : Edge L k j,
        ((b.initial : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) c'.initial ∧
          (b.terminal : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) c'.terminal) → c' = c
def MemAxisPathInCorridor (L k j : ℕ) (c : Edge L k j)
    (b : Edge L k (j - 1)) : Prop :=
  b ∈ axisPath (toFiner (meshAt L k (j - 1)) c.initial)
      (toFiner (meshAt L k (j - 1)) c.terminal) ∧
    b ∈ linkCorridor L (meshAt L k (j - 1)) c
structure StepsEdgesAndCorridors (L k j : ℕ) : Prop where
  step_mem_cube : ∀ (y : Vertex L k j) (x : Vertex L k (j - 1)) (ν : Fin 4 → ℤ),
    IsCubeOffset L y x ν → ∀ μ : Fin 4, 2 * ν μ < (L : ℤ) - 1 →
      ((x + InfiniteLattice.axisStep (meshAt L k (j - 1)) μ : Vertex L k (j - 1)) :
          AmbientSpace) ∈ cube L (meshAt L k (j - 1)) y
  step_mem_adjacent_cube : ∀ (y : Vertex L k j) (x : Vertex L k (j - 1)) (ν : Fin 4 → ℤ),
    IsCubeOffset L y x ν → ∀ μ : Fin 4, 2 * ν μ = (L : ℤ) - 1 →
      ((x + InfiniteLattice.axisStep (meshAt L k (j - 1)) μ : Vertex L k (j - 1)) :
          AmbientSpace) ∈
        cube L (meshAt L k (j - 1)) (y + InfiniteLattice.axisStep (meshAt L k j) μ)
  endpoints : ∀ b : Edge L k (j - 1), EndpointsInOneCubeOrAcrossEdge L k j b
  existsUnique_corridorEdge : ∀ (c : Edge L k j) (μ : Fin 4),
    c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k j) μ →
      ∃! b : Edge L k (j - 1), MemAxisPathInCorridor L k j c b
  corridorEdge_initial : ∀ (c : Edge L k j) (μ : Fin 4),
    c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k j) μ →
      ∀ b : Edge L k (j - 1), MemAxisPathInCorridor L k j c b →
        (b.initial : AmbientSpace) = (c.initial : AmbientSpace) +
          Pi.single μ ((((L : ℝ) - 1) / 2) * meshAt L k (j - 1))
structure PathsStayInCubes (L k j : ℕ) : Prop where
  contour_vertex_mem : ∀ (y : Vertex L k j) (x : Vertex L k (j - 1)),
    (x : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) y →
      ∀ Γ ∈ contourSet L y x, ∀ z : Vertex L k (j - 1),
        (z = toFiner (meshAt L k (j - 1)) y ∨ z = x ∨
            ∃ b ∈ Γ, z = b.initial ∨ z = b.terminal) →
          (z : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) y
  crossing_vertex_mem : ∀ (c : Edge L k j) (x : Vertex L k (j - 1)),
    (x : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) c.initial →
      ∀ z : Vertex L k (j - 1),
        (z = x ∨ z = shifted c x ∨ ∃ b ∈ crossingPath c x, z = b.initial ∨ z = b.terminal) →
          (z : AmbientSpace) ∈ doubleCube L (meshAt L k (j - 1)) c
def CubesCorridorsPivotEdgesAndPaths : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ k j n : ℕ, 1 ≤ k → 1 ≤ j → j ≤ k → 1 ≤ n → n ≤ j →
      CubesOfOrderPartition L k j n ∧
        (2 ≤ n → ∀ y : Vertex L k j, CubeIsDisjointUnionOfSubcubes L k j n y) ∧
        StepsEdgesAndCorridors L k j ∧ PathsStayInCubes L k j
end FullSpace
end Tower
end YangMills.Construction
end
