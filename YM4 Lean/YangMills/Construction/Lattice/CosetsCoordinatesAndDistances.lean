import YangMills.Construction.Lattice.CubesVerticesAndEdgesInPhysicalUnits
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace TorusBound
namespace Coordinates
variable (D : Setup)
def latticeCoset (j : ℕ) : Set ℝ := {t | ∃ a : ℤ, t = D.physicalCubeSide j * (a : ℝ)}
def halfLatticeCoset (j : ℕ) : Set ℝ := {t | PeriodicLattice.IsGridPoint (D.physicalCubeSide j) t}
def IsTranslationInvariant (C : Set ℝ) (t : ℝ) : Prop := (fun x => x + t) '' C = C
def CosetProperties (j : ℕ) : Prop :=
  D.side ∈ latticeCoset D j ∧ 0 < D.physicalCubeSide j ∧ D.physicalCubeSide j < D.side ∧
  IsTranslationInvariant (latticeCoset D j) D.side ∧
  IsTranslationInvariant (halfLatticeCoset D j) D.side ∧
  ∀ C ∈ ({latticeCoset D j, halfLatticeCoset D j} : Set (Set ℝ)),
    ∀ (y : D.Torus) (μ : Fin 4) (w w' : Fin 4 → ℝ),
      D.IsLiftOfPoint y w → D.IsLiftOfPoint y w' → w μ ∈ C → w' μ ∈ C
def CentreLifts (j : ℕ) : Prop :=
  ∀ w : Fin 4 → ℝ,
    (∃ c : PeriodicLattice.Site D.L D.m (D.cubeScaleIndex j), D.IsLiftOfPoint (c : D.Torus) w) ↔
      ∀ μ, w μ ∈ latticeCoset D j
def CubeMembershipByLifts (j : ℕ) : Prop :=
  ∀ (c : PeriodicLattice.Site D.L D.m (D.cubeScaleIndex j)) (w : Fin 4 → ℝ),
    D.IsLiftOfPoint (c : D.Torus) w →
    ∀ y : D.Torus, y ∈ D.cubeCentredAt c ↔
      ∃ w' : Fin 4 → ℝ, D.IsLiftOfPoint y w' ∧
        ∀ μ, (w' - w) μ ∈ Icc (-(D.physicalCubeSide j / 2)) (D.physicalCubeSide j / 2)
variable {D}
variable {j : ℕ} (hj : j ≤ D.K) (h : D.LevelFits j)
def CubeVerticesByLifts : Prop :=
  ∀ (c : PeriodicLattice.Site D.L D.m (D.cubeScaleIndex j)) (w : Fin 4 → ℝ),
    D.IsLiftOfPoint (c : D.Torus) w →
    ∀ v : D.Torus, (D.levelUnitPartition hj h).IsCornerOf v (D.cubeCentredAt c) ↔
      ∃ ε : Fin 4 → ℝ, PeriodicLattice.LevelUnitPartition.IsSigns ε ∧
        v = D.torusCover (w + (D.physicalCubeSide j / 2) • ε)
def VertexIffHalfIntegral : Prop :=
  ∀ v : D.Torus, D.IsLevelVertex hj h v ↔ ∀ μ, D.IsHalfIntegralCoord j μ v
def EdgeParametrization : Prop :=
  ∀ A : Set D.Torus, D.IsLevelEdge hj h A ↔
    ∃ (w : Fin 4 → ℝ) (ν : Fin 4), (∀ μ, w μ ∈ halfLatticeCoset D j) ∧
      A = D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν
def EdgeAxisUnique : Prop :=
  ∀ A : Set D.Torus, D.IsLevelEdge hj h A → ∃! ν : Fin 4, D.IsEdgeAxis hj h ν A
def EdgeCoordinates : Prop :=
  ∀ (A : Set D.Torus) (ν : Fin 4), D.IsLevelEdge hj h A → D.IsEdgeAxis hj h ν A →
    (∀ μ, μ ≠ ν → (∀ y ∈ A, ∀ y' ∈ A, y μ = y' μ) ∧ ∀ y ∈ A, D.IsHalfIntegralCoord j μ y) ∧
    ∀ y ∈ A, D.IsHalfIntegralCoord j ν y ↔ (D.levelUnitPartition hj h).IsEdgeEndpoint A y
def EdgeEndpointsByLifts : Prop :=
  ∀ (w : Fin 4 → ℝ) (ν : Fin 4), (∀ μ, w μ ∈ halfLatticeCoset D j) →
    {x | (D.levelUnitPartition hj h).IsEdgeEndpoint
        (D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν) x} =
      {D.torusCover w, D.torusCover (w + D.physicalCubeSide j • PeriodicLattice.coordVec ν)} ∧
    D.torusCover w ≠ D.torusCover (w + D.physicalCubeSide j • PeriodicLattice.coordVec ν)
variable (D)
def NormMinimaAttained : Prop :=
  ∀ x : D.Torus,
    IsLeast (TorusMetric.supNormVec ''
      (TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) ⁻¹' {x}))
      (TorusMetric.torusSupNorm x) ∧
    IsLeast (TorusMetric.euclidNormVec ''
      (TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m) ⁻¹' {x}))
      (TorusMetric.torusEuclidNorm x)
def NormComparison : Prop :=
  ∀ x : D.Torus, TorusMetric.torusSupNorm x ≤ TorusMetric.torusEuclidNorm x ∧
    TorusMetric.torusEuclidNorm x ≤ 2 * TorusMetric.torusSupNorm x
def MetricAxioms : Prop :=
  ∀ x y z : D.Torus,
    TorusMetric.torusSupNorm (x - y) = TorusMetric.torusSupNorm (y - x) ∧
    TorusMetric.torusEuclidNorm (x - y) = TorusMetric.torusEuclidNorm (y - x) ∧
    TorusMetric.torusSupNorm (x - z) ≤
      TorusMetric.torusSupNorm (x - y) + TorusMetric.torusSupNorm (y - z) ∧
    TorusMetric.torusEuclidNorm (x - z) ≤
      TorusMetric.torusEuclidNorm (x - y) + TorusMetric.torusEuclidNorm (y - z) ∧
    (TorusMetric.torusSupNorm (x - y) = 0 → x = y)
def ProjNonexpanding : Prop :=
  ∀ u v : Fin 4 → ℝ,
    TorusMetric.torusSupNorm (D.torusCover u - D.torusCover v) ≤ Setup.maxNorm (u - v) ∧
    TorusMetric.torusEuclidNorm (D.torusCover u - D.torusCover v) ≤ Setup.l2Norm (u - v)
def IsSupClosed (A : Set D.Torus) : Prop :=
  ∀ x : D.Torus, (∀ ε : ℝ, 0 < ε → ∃ a ∈ A, TorusMetric.torusSupNorm (x - a) < ε) → x ∈ A
def CosetsAndDistancesStatement : Prop :=
  ∀ (D : Setup) (j : ℕ) (hj : j ≤ D.K) (h : D.LevelFits j),
    CosetProperties D j ∧
    CentreLifts D j ∧ CubeMembershipByLifts D j ∧ CubeVerticesByLifts hj h ∧
    VertexIffHalfIntegral hj h ∧
    EdgeParametrization hj h ∧ EdgeAxisUnique hj h ∧ EdgeCoordinates hj h ∧
    EdgeEndpointsByLifts hj h ∧
    NormMinimaAttained D ∧ NormComparison D ∧ MetricAxioms D ∧
    ProjNonexpanding D ∧
    ∀ A : Set D.Torus, D.IsLevelEdge hj h A → IsSupClosed D A
end Coordinates
end TorusBound
end YangMills.Construction
end
