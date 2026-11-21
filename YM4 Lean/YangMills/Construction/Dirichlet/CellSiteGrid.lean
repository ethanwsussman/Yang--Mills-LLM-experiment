import YangMills.Construction.Dirichlet.LatticeCalculus
import YangMills.Construction.Torus.NestedCubePartitions
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.Torus.NestedCubes
noncomputable section
namespace YangMills.Construction.Dirichlet.CellSiteGrid
variable {d : ℕ} {S : ℝ}
def PathProductAdj {N : ℕ} (a b : Fin d → Fin N) : Prop :=
  ∃ μ, (SimpleGraph.pathGraph N).Adj (a μ) (b μ) ∧ ∀ ν, ν ≠ μ → a ν = b ν
structure CellGridFacts (L : ℕ) (ξ : ℝ) (Ω : ℕ → Set (PeriodicTorus d S)) (y : PeriodicTorus d S)
    (z : Fin d → ℝ) : Prop where
  sites_eq_centeredGrid : IsCenteredGrid S ξ (shellSpacing L ξ Ω y / ξ) z
    ((spacingLattice d S ξ : Set (PeriodicTorus d S)) ∩ siteCube L ξ Ω y)
  isNeighbor_iff : ∀ k ∈ centeredBox d (shellSpacing L ξ Ω y / ξ),
    ∀ k' ∈ centeredBox d (shellSpacing L ξ Ω y / ξ),
    ∀ x x' : YangMills.Construction.Dirichlet.LatticeSite d S ξ,
      (x : PeriodicTorus d S) = offsetPoint S ξ z k → (x' : PeriodicTorus d S) = offsetPoint S ξ z k' →
      (YangMills.Construction.Dirichlet.IsNeighbor x x' ↔
        ∃ μ, k' = k + Pi.single μ 1 ∨ k' = k - Pi.single μ 1)
  exists_equiv_pathProduct : ∃ N : ℕ, (N : ℝ) = shellSpacing L ξ Ω y / ξ ∧
    ∃ e : (Fin d → Fin N) ≃ {x : YangMills.Construction.Dirichlet.LatticeSite d S ξ //
        (x : PeriodicTorus d S) ∈ siteCube L ξ Ω y},
      ∀ a b, YangMills.Construction.Dirichlet.IsNeighbor (e a).1 (e b).1 ↔ PathProductAdj a b
  exists_path : ∀ x x' : YangMills.Construction.Dirichlet.LatticeSite d S ξ,
    (x : PeriodicTorus d S) ∈ siteCube L ξ Ω y → (x' : PeriodicTorus d S) ∈ siteCube L ξ Ω y →
    ∃ (r : ℕ) (w : ℕ → YangMills.Construction.Dirichlet.LatticeSite d S ξ),
      (r : ℝ) = lOneNorm ((x : PeriodicTorus d S) - (x' : PeriodicTorus d S)) / ξ ∧ w 0 = x ∧
      w r = x' ∧
      (∀ i < r, YangMills.Construction.Dirichlet.IsNeighbor (w i) (w (i + 1))) ∧
      ∀ i ≤ r, (w i : PeriodicTorus d S) ∈ siteCube L ξ Ω y
  lOneNorm_sub_le : ∀ x : YangMills.Construction.Dirichlet.LatticeSite d S ξ,
    (x : PeriodicTorus d S) ∈ siteCube L ξ Ω y →
    lOneNorm ((x : PeriodicTorus d S) - y) ≤ 1 / 2 * (d : ℝ) * shellSpacing L ξ Ω y
def AllCellGridFacts : Prop :=
  ∀ (d L : ℕ) (S ξ : ℝ) (M R₁ t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)), 0 < d → 3 ≤ L → Odd L →
    IsSeparatedChain L ξ M R₁ t Ω → ∀ n ≤ lastNonemptyIndex Ω, ∀ y ∈ shellSites L ξ Ω n,
      ∀ z : Fin d → ℝ, torusProj d S z = y → CellGridFacts L ξ Ω y z
end YangMills.Construction.Dirichlet.CellSiteGrid
end
