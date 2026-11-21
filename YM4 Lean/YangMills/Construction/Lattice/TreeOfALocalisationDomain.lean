import YangMills.Construction.Lattice.ConstantsOfTheTorusBound
import YangMills.Construction.Lattice.CubesVerticesAndEdgesInPhysicalUnits
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice
noncomputable section
namespace YangMills.Construction
namespace TorusBound
namespace Setup
variable (S : Setup)
def Adjacent {j : ℕ} (hj : j ≤ S.K) (hfit : S.LevelFits j) (T : Set S.Torus) (x y : S.Torus) :
    Prop :=
  ∃ e, S.TreeGraphJoins hj hfit T e x y
def TreeGraphConnected {j : ℕ} (hj : j ≤ S.K) (hfit : S.LevelFits j) (T : Set S.Torus) : Prop :=
  ∀ x ∈ S.treeGraphVertices hj hfit T, ∀ y ∈ S.treeGraphVertices hj hfit T,
    Relation.ReflTransGen (S.Adjacent hj hfit T) x y
def TreeGraphLoopless {j : ℕ} (hj : j ≤ S.K) (hfit : S.LevelFits j)
    (T : Set S.Torus) : Prop :=
  ∀ e ∈ S.treeGraphEdges hj hfit T, ∃ x y, x ≠ y ∧ S.TreeGraphJoins hj hfit T e x y
def TreeGraphConnectedBounded {j : ℕ} (hj : j ≤ S.K) (hfit : S.LevelFits j) (T : Set S.Torus)
    (N : ℕ) : Prop :=
  S.TreeGraphConnected hj hfit T ∧
  S.TreeGraphLoopless hj hfit T ∧
  (S.treeGraphVertices hj hfit T).encard ≤ (N : ℕ∞) + 1 ∧
  ∀ x ∈ S.treeGraphVertices hj hfit T, ∀ y ∈ S.treeGraphVertices hj hfit T,
    TorusMetric.torusEuclidNorm (x - y) ≤ (N : ℝ) * S.physicalCubeSide j
def TreeVerticesMeetCubes {j : ℕ} (hj : j ≤ S.K) (hfit : S.LevelFits j) (U T : Set S.Torus)
    (N : ℕ) : Prop :=
  (∀ C ∈ partitionCubesIn (S.cubeScaleIndex j) U, ∃ x ∈ S.treeGraphVertices hj hfit T, x ∈ C) ∧
  (∀ C ∈ partitionCubesIn (S.cubeScaleIndex j) U,
    C ∈ (S.levelUnitPartition hj hfit).cubesMeeting (S.treeGraphVertices hj hfit T)) ∧
  ((S.levelUnitPartition hj hfit).cubesMeeting (S.treeGraphVertices hj hfit T)).encard ≤
    16 * ((N : ℕ∞) + 1)
def ballReach (j : ℕ) (R : ℝ) : ℝ :=
  R + 1 / 2 * meshSize S.L (S.K : ℤ) + 3 / 2 * S.physicalCubeSide j
def cubesCentredNear (j : ℕ) (y : S.Torus) (ρ : ℝ) : Set (Set S.Torus) :=
  {C | ∃ z : Site S.L S.m (S.cubeScaleIndex j),
    C = S.cubeCentredAt z ∧ TorusMetric.torusSupNorm ((z : S.Torus) - y) ≤ ρ}
end Setup
def LocalisationDomainTreeClaim : Prop :=
  ∀ (S : Setup) (j : ℕ) (hj : j ≤ S.K) (hfit : S.LevelFits j) (κ : DomainKind)
    (U : Set S.Torus), U ∈ S.regionsBy κ j →
    (∀ (N : ℕ) (T : Set S.Torus), (partitionCubesIn (S.cubeScaleIndex j) U).Nonempty →
      (N : ℝ) = S.extent j U → IsEdgeTreeWithCount (S.levelUnitPartition hj hfit) U T N →
      (∀ C ∈ partitionCubesIn (S.cubeScaleIndex j) U, GraphIntersects T C) →
        S.TreeGraphConnectedBounded hj hfit T N ∧ S.TreeVerticesMeetCubes hj hfit U T N) ∧
    (∀ p₁ ∈ S.plaquettesOfThickened j U, ∀ p₂ ∈ S.plaquettesOfThickened j U,
      TorusMetric.torusEuclidNorm (p₁.barycenter - p₂.barycenter) <
        (S.extent j U + 10) * S.physicalCubeSide j) ∧
    ∀ (y : S.Torus) (R : ℝ), 0 < R →
      ((∃ p ∈ S.plaquettesOfThickened j U,
          TorusMetric.torusEuclidNorm (p.barycenter - y) ≤ R) →
        ∃ z : Site S.L S.m (S.cubeScaleIndex j), S.cubeCentredAt z ∈ partitionCubesIn (S.cubeScaleIndex j) U ∧
          TorusMetric.torusSupNorm ((z : S.Torus) - y) ≤ S.ballReach j R) ∧
      (S.cubesCentredNear j y (S.ballReach j R)).Finite ∧
      ∀ c : ConstantParameters, c.L = S.L → c.cubeExp = S.cubeExp →
        ((S.cubesCentredNear j y (S.ballReach j R)).ncard : ℝ) ≤
          c.ballCubeCount R ((S.K : ℕ) - j)
end TorusBound
end YangMills.Construction
end
