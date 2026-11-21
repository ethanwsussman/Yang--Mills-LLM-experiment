import YangMills.Construction.Torus.SeparatedChains
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Torus.CubePartition
structure Properties (d : ℕ) (S σ : ℝ) : Prop where
  finite : (cubePartition d S σ).Finite
  isClosed_cube : ∀ Q ∈ cubePartition d S σ, IsClosed Q
  closure_interior : ∀ Q ∈ cubePartition d S σ, closure (interior Q) = Q
  sUnion_eq_univ : ⋃₀ cubePartition d S σ = univ
  center_mem_interior : ∀ c ∈ spacingLattice d S σ, c ∈ interior (cubeAt c σ)
  cubeAt_injective : ∀ c ∈ spacingLattice d S σ, ∀ c' ∈ spacingLattice d S σ,
    cubeAt c σ = cubeAt c' σ → c = c'
  interior_not_mem_of_ne : ∀ Q ∈ cubePartition d S σ, ∀ Q' ∈ cubePartition d S σ,
    Q' ≠ Q → ∀ p ∈ interior Q, p ∉ Q'
  closure_diff_eq : ∀ X Y : Set (PeriodicTorus d S), IsCubeUnion σ X → IsCubeUnion σ Y → Y ⊆ X →
    closure (X \ Y) = ⋃₀ {Q ∈ cubePartition d S σ | Q ⊆ X ∧ ¬ Q ⊆ Y}
  disjoint_interior : ∀ X Y : Set (PeriodicTorus d S), IsCubeUnion σ X → IsCubeUnion σ Y →
    Y ⊆ X → ∀ Q ∈ cubePartition d S σ, Q ⊆ X → ¬ Q ⊆ Y → Disjoint (interior Q) Y
  compl_subset_cubeComplement : ∀ Y : Set (PeriodicTorus d S), IsCubeUnion σ Y →
    Yᶜ ⊆ cubeComplement σ Y
  frontier_subset_cubeComplement : ∀ Y : Set (PeriodicTorus d S), IsCubeUnion σ Y →
    frontier Y ⊆ cubeComplement σ Y
  cubeComplement_antitone : ∀ X Y : Set (PeriodicTorus d S), IsCubeUnion σ X →
    IsCubeUnion σ Y → Y ⊆ X → cubeComplement σ X ⊆ cubeComplement σ Y
  cubeComplement_eq_closure_compl : ∀ Y : Set (PeriodicTorus d S), IsCubeUnion σ Y →
    cubeComplement σ Y = closure Yᶜ
def PropertiesOfIntegerMultiple : Prop :=
  ∀ (d : ℕ) (S σ : ℝ) (k : ℕ), 0 < d → 0 < σ → 2 ≤ k → S = (k : ℝ) * σ → Properties d S σ
end YangMills.Construction.Torus.CubePartition
end
