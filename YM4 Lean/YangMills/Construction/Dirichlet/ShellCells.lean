import YangMills.Construction.Torus.SeparatedChains
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.Dirichlet.ShellCells
variable {d : ℕ} {S : ℝ}
structure ShellCellFacts (L : ℕ) (ξ : ℝ) (M t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)) (n : ℕ) : Prop where
  shellIndex_eq : ∀ y ∈ shellSites L ξ Ω n, shellIndex L ξ Ω y = n
  cells_eq : {Q | ∃ y ∈ shellSites L ξ Ω n, Q = siteCube L ξ Ω y} =
    {Q ∈ cubePartition d S (scaleSpacing L ξ n) | Q ⊆ shell Ω n}
  shell_eq_iUnion : shell Ω n = ⋃ y ∈ shellSites L ξ Ω n, siteCube L ξ Ω y
  disjoint_cubeComplement : ∀ y ∈ shellSites L ξ Ω n, Disjoint (interior (siteCube L ξ Ω y))
    (cubeComplement ((M : ℝ) * scaleSpacing L ξ n) (Ω n))
  disjoint_nextDomain : ∀ y ∈ shellSites L ξ Ω n, Disjoint (interior (siteCube L ξ Ω y)) (Ω (n + 1))
  disjoint_otherShell : ∀ y ∈ shellSites L ξ Ω n, ∀ m ≤ t, m ≠ n →
    Disjoint (interior (siteCube L ξ Ω y)) (shell Ω m)
  disjoint_otherCell : ∀ y ∈ shellSites L ξ Ω n, ∀ z ∈ unionShellSites L ξ t Ω, z ≠ y →
    Disjoint (interior (siteCube L ξ Ω y)) (siteCube L ξ Ω z)
  mem_interior_shell : ∀ y ∈ shellSites L ξ Ω n, y ∈ interior (shell Ω n)
def AllShellCellFacts : Prop :=
  ∀ (d L : ℕ) (S ξ : ℝ) (M R₁ t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)), 0 < d → 3 ≤ L → Odd L →
    IsSeparatedChain L ξ M R₁ t Ω → ∀ n ≤ lastNonemptyIndex Ω, ShellCellFacts L ξ M t Ω n
end YangMills.Construction.Dirichlet.ShellCells
end
