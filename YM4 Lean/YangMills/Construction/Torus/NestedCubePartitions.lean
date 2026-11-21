import YangMills.Construction.Torus.SeparatedChains
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Torus.NestedCubes
variable {d : ℕ} {S : ℝ}
def centeredBox (d : ℕ) (N : ℝ) : Set (Fin d → ℤ) := {k | ∀ μ, |(k μ : ℝ)| ≤ (N - 1) / 2}
def offsetPoint (S σ : ℝ) (z : Fin d → ℝ) (k : Fin d → ℤ) : PeriodicTorus d S :=
  torusProj d S fun μ => z μ + σ * (k μ : ℝ)
structure IsCenteredGrid (S σ N : ℝ) (z : Fin d → ℝ) (P : Set (PeriodicTorus d S)) : Prop where
  image_eq : offsetPoint S σ z '' centeredBox d N = P
  injOn : InjOn (offsetPoint S σ z) (centeredBox d N)
  ncard_eq : ((centeredBox d N).ncard : ℝ) = N ^ d
structure Properties (d : ℕ) (S σ σ' : ℝ) : Prop where
  spacingLattice_le : spacingLattice d S σ ≤ spacingLattice d S σ'
  cube_eq_sUnion : ∀ Q ∈ cubePartition d S σ,
    Q = ⋃₀ {Q' ∈ cubePartition d S σ' | Q' ⊆ Q}
  isCubeUnion_of_coarse : ∀ X : Set (PeriodicTorus d S), IsCubeUnion σ X → IsCubeUnion σ' X
  isCenteredGrid_inter_cube : ∀ z ∈ spacingLattice d S σ, ∀ z' : Fin d → ℝ,
    torusProj d S z' = z →
    IsCenteredGrid S σ' (σ / σ') z'
      ((spacingLattice d S σ' : Set (PeriodicTorus d S)) ∩ cubeAt z σ)
  inter_cube_subset_interior : ∀ z ∈ spacingLattice d S σ,
    (spacingLattice d S σ' : Set (PeriodicTorus d S)) ∩ cubeAt z σ ⊆ interior (cubeAt z σ)
def PropertiesOfOddRefinement : Prop :=
  ∀ (d : ℕ) (S σ σ' : ℝ) (N k : ℕ), 0 < d → 0 < σ' → Odd N → σ = (N : ℝ) * σ' → 2 ≤ k →
    S = (k : ℝ) * σ → Properties d S σ σ'
end YangMills.Construction.Torus.NestedCubes
end
