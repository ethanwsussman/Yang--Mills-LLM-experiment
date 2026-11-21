import YangMills.Construction.Lattice.LocalHolderSeminormsAndLifts
import YangMills.Construction.Lattice.OneScaleOperatorBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def Scales.gridPointsNear {d L j N : ℕ} (S : Scales d L j N) (w₀ : Fin d → ℝ) (r : ℕ) :
    Set (InfiniteLattice.GridSite d S.unitMesh.h) :=
  {y | ∀ μ, w₀ μ - (r : ℝ) - 1 < (y : Fin d → ℝ) μ ∧ (y : Fin d → ℝ) μ ≤ w₀ μ + (r : ℝ)}
def LiftsOfTorusAllDimensions : Prop :=
  ∀ (d L j N : ℕ) (S : Scales d L j N),
    (∀ (u u' : Torus d N) (v v' : Fin d → ℝ), IsLiftOf v u → IsLiftOf v' u' →
      IsLeast
        (Set.range fun n : Fin d → ℤ =>
          InfiniteLattice.l1Length fun μ => v μ - v' μ + (N : ℝ) * (n μ : ℝ))
        (taxicabDist u u') ∧
      IsLeast
        (Set.range fun n : Fin d → ℤ =>
          InfiniteLattice.supLength fun μ => v μ - v' μ + (N : ℝ) * (n μ : ℝ))
        (maxDist u u')) ∧
    (∀ u u' : Torus d N, taxicabDist u u' = taxicabDist u' u ∧ maxDist u u' = maxDist u' u) ∧
    (∀ u u' u'' : Torus d N,
      taxicabDist u u'' ≤ taxicabDist u u' + taxicabDist u' u'' ∧
      maxDist u u'' ≤ maxDist u u' + maxDist u' u'') ∧
    (∀ u u' : Torus d N, maxDist u u' ≤ taxicabDist u u' ∧ taxicabDist u u' ≤ (d : ℝ) * maxDist u u') ∧
    (∀ v : Fin d → ℝ,
      (∃ x : GridPoint d S.fineMesh, IsLiftOf v (x : Torus d N)) ↔
        v ∈ InfiniteLattice.gridSubgroup d S.fineMesh.h) ∧
    (∀ v : Fin d → ℝ,
      (∃ x : GridPoint d S.unitMesh, IsLiftOf v (x : Torus d N)) ↔
        v ∈ InfiniteLattice.gridSubgroup d S.unitMesh.h) ∧
    (∀ v v' : Fin d → ℝ,
      taxicabDist (quotientMap v : Torus d N) (quotientMap v') ≤ InfiniteLattice.l1Length (v - v') ∧
      maxDist (quotientMap v : Torus d N) (quotientMap v') ≤ InfiniteLattice.supLength (v - v') ∧
      (InfiniteLattice.l1Length (v - v') ≤ 1 →
        taxicabDist (quotientMap v : Torus d N) (quotientMap v') = InfiniteLattice.l1Length (v - v'))) ∧
    (∀ (x x' : GridPoint d S.fineMesh) (x₀ : Fin d → ℝ), IsLiftOf x₀ (x : Torus d N) →
      ∃ x₀' : Fin d → ℝ, IsLiftOf x₀' (x' : Torus d N) ∧
        InfiniteLattice.l1Length (x₀ - x₀') = taxicabDist (x : Torus d N) x' ∧
        InfiniteLattice.supLength (x₀ - x₀') = maxDist (x : Torus d N) x') ∧
    (∀ (μ : Fin d) (f : SiteFun d S.fineMesh),
      pullbackToGrid (forwardDiff S.fineMesh μ f) = InfiniteLattice.forwardDiff μ (pullbackToGrid f) ∧
      pullbackToGrid (LinearMap.adjoint (forwardDiff S.fineMesh μ) f) =
        InfiniteLattice.backwardDiff μ (pullbackToGrid f)) ∧
    (∀ f : SiteFun d S.fineMesh,
      pullbackToGrid (discreteLaplacian S.fineMesh f) = InfiniteLattice.laplacian (pullbackToGrid f)) ∧
    (∀ (w : GridPoint d S.fineMesh) (w₀ : Fin d → ℝ) (r : ℕ), IsLiftOf w₀ (w : Torus d N) → 1 ≤ r →
      (S.gridPointsNear w₀ r).ncard = (2 * r + 1) ^ d ∧
      (∀ y ∈ S.gridPointsNear w₀ r,
        taxicabDist ((quotientSite S.unitMesh y : GridPoint d S.unitMesh) : Torus d N) (w : Torus d N) ≤
          (d : ℝ) * ((r : ℝ) + 1)) ∧
      maxBall S.fineMesh (r : ℝ) (w : Torus d N) ⊆
        ⋃ y ∈ S.gridPointsNear w₀ r,
          (S.fineCell (quotientSite S.unitMesh y) : Set (GridPoint d S.fineMesh)))
end YangMills.Construction.PeriodicLattice
