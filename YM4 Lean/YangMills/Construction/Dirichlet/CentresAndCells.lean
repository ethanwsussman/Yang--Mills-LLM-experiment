import YangMills.Construction.Torus.PartitionsShellsCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Dirichlet
open Torus
variable {d L : ℕ} {S aMinus aPlus : ℝ}
def weightedNormSq (𝒮 : BlockSetting d L aMinus aPlus S) (v : LatticeSite d S 𝒮.ξ → ℝ) : ℝ :=
  𝒮.ξ ^ d * ∑ᶠ x, 𝒮.localWeight x * v x ^ 2
structure CentreCellFacts (𝒮 : BlockSetting d L aMinus aPlus S) : Prop where
  finite_site : Finite (LatticeSite d S 𝒮.ξ)
  centres_finite : 𝒮.centres.Finite
  centreSpacing_pos : ∀ y, 0 < 𝒮.centreSpacing y
  localScale_pos : ∀ x, 0 < 𝒮.localScale x
  mem_spacingLattice : ∀ y ∈ 𝒮.centres, y ∈ spacingLattice d S 𝒮.ξ
  centreIndex_le : ∀ y ∈ 𝒮.centres, 𝒮.centreIndex y ≤ 𝒮.t
  cell_subset : ∀ y ∈ 𝒮.centres, 𝒮.cell y ⊆ 𝒮.Ω 0
  existsUnique_cell : ∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.Ω 0 →
    ∃! y, y ∈ 𝒮.centres ∧ (x : PeriodicTorus d S) ∈ 𝒮.cell y
  localScale_eq : ∀ y ∈ 𝒮.centres, ∀ x : LatticeSite d S 𝒮.ξ,
    (x : PeriodicTorus d S) ∈ 𝒮.cell y → 𝒮.localScale x = 𝒮.centreSpacing y
  equiv_boxGrid : ∀ y ∈ 𝒮.centres, ∃ N : ℕ, 0 < N ∧ (N : ℝ) = 𝒮.centreSpacing y / 𝒮.ξ ∧
    ∃ e : (Fin d → Fin N) ≃ {x : LatticeSite d S 𝒮.ξ // (x : PeriodicTorus d S) ∈ 𝒮.cell y},
      ∀ a b, IsNeighbor (e a).1 (e b).1 ↔ BoxGridAdj a b
def CentreCellFactsHold : Prop :=
  ∀ (d L : ℕ) (aMinus aPlus S : ℝ), Parameters d L aMinus aPlus →
    ∀ 𝒮 : BlockSetting d L aMinus aPlus S, CentreCellFacts 𝒮
end Dirichlet
end YangMills.Construction
