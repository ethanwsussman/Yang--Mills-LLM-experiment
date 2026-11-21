import YangMills.Construction.Torus.SeparatedChains
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.Dirichlet.LatticeSiteCells
variable {d : ℕ} {S : ℝ}
structure LatticeSiteFacts (L : ℕ) (ξ : ℝ) (t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)) : Prop where
  exists_cell_of_mem : ∀ x ∈ spacingLattice d S ξ, x ∈ Ω 0 → ∃ y ∈ unionShellSites L ξ t Ω,
    x ∈ interior (siteCube L ξ Ω y) ∧
    (∀ z ∈ unionShellSites L ξ t Ω, z ≠ y → x ∉ siteCube L ξ Ω z) ∧
    cubeAt x ξ ⊆ siteCube L ξ Ω y ∧
    ∀ m, y ∈ shellSites L ξ Ω m → x ∈ shell Ω m ∧ ∀ m' ≤ t, m' ≠ m → x ∉ shell Ω m'
  disjoint_of_not_mem : ∀ x ∈ spacingLattice d S ξ, x ∉ Ω 0 →
    Disjoint (interior (cubeAt x ξ)) (Ω 0)
def AllLatticeSiteFacts : Prop :=
  ∀ (d L : ℕ) (S ξ : ℝ) (M R₁ t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)), 0 < d → 3 ≤ L → Odd L →
    IsSeparatedChain L ξ M R₁ t Ω → LatticeSiteFacts L ξ t Ω
end YangMills.Construction.Dirichlet.LatticeSiteCells
end
