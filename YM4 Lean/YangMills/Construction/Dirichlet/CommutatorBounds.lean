import YangMills.Construction.Dirichlet.CentresNearBumps
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Torus Dirichlet
namespace Dirichlet.Commutator
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
def CommutatorFormula : Prop :=
  ∀ (h ψ : LatticeSite d S 𝒮.ξ → ℝ) (x : LatticeSite d S 𝒮.ξ), (x : PeriodicTorus d S) ∈ 𝒮.Ω 0 →
    𝒮.commutatorOp h ψ x =
      (𝒮.ξ ^ 2)⁻¹ * (∑ᶠ x' ∈ {x' : LatticeSite d S 𝒮.ξ | IsNeighbor x x'}, (h x' - h x) * ψ x') -
        𝒮.a (𝒮.centreIndex (𝒮.centreOf x)) * (𝒮.centreSpacing (𝒮.centreOf x) ^ 2)⁻¹ *
          (𝒮.ξ / 𝒮.centreSpacing (𝒮.centreOf x)) ^ d *
          ∑ᶠ x' ∈ {x' : LatticeSite d S 𝒮.ξ | (x' : PeriodicTorus d S) ∈ 𝒮.cell (𝒮.centreOf x)},
            (h x' - h x) * ψ x'
structure CellHypotheses (y : PeriodicTorus d S) (c N : ℝ) (h ψ : LatticeSite d S 𝒮.ξ → ℝ) : Prop where
  h_step : ∀ x x' : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.cell y → IsNeighbor x x' →
    |h x' - h x| ≤ c * 𝒮.ξ / ((𝒮.M : ℝ) * 𝒮.centreSpacing y)
  ψ_step : ∀ x x' : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.cell y → IsNeighbor x x' →
    |ψ x' - ψ x| ≤ 𝒮.ξ * 𝒮.centreSpacing y * N
  h_laplacian : ∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.cell y →
    |latticeLaplacian h x| ≤ c / ((𝒮.M : ℝ) * 𝒮.centreSpacing y) ^ 2
  ψ_size : ∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.cell y →
    |ψ x| ≤ 𝒮.centreSpacing y ^ 2 * N
  h_diff : ∀ x x' : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.cell y →
    (x' : PeriodicTorus d S) ∈ 𝒮.cell y →
    |h x' - h x| ≤ c * siteLOneDist x x' / ((𝒮.M : ℝ) * 𝒮.centreSpacing y)
def CellBound : Prop :=
  ∀ y ∈ 𝒮.centres, ∀ c N : ℝ, 0 ≤ c → 0 ≤ N → ∀ h ψ : LatticeSite d S 𝒮.ξ → ℝ,
    CellHypotheses 𝒮 y c N h ψ →
      supNormOn (𝒮.cell y) (𝒮.commutatorOp h ψ) ≤
        (2 * (d : ℝ) + 1 + aPlus * (d : ℝ)) * c * (𝒮.M : ℝ)⁻¹ * N
def nearCells (Q : CentredCube d S) : Set (PeriodicTorus d S) :=
  ⋃ y ∈ 𝒮.centresNearBump Q, 𝒮.cell y
structure CutoffSiteFacts (Q : CentredCube d S) (x : LatticeSite d S 𝒮.ξ) : Prop where
  mem_innerRegion : (x : PeriodicTorus d S) ∈ 𝒮.innerRegion Q
  centre_mem : 𝒮.centreOf x ∈ 𝒮.centresNearBump Q
  neighbor_mem : ∀ x' : LatticeSite d S 𝒮.ξ, IsNeighbor x x' → (x' : PeriodicTorus d S) ∈ 𝒮.Ω 0 →
    (x' : PeriodicTorus d S) ∈ 𝒮.innerRegion Q
  boundary_external : ∀ b : LatticeBond d S 𝒮.ξ, IsBoundaryBond (𝒮.innerRegion Q) b →
    b.source = x ∨ b.target = x → b ∈ externalBoundaryBonds (𝒮.Ω 0) (𝒮.innerRegion Q)
  boundary_mem_rule : ∀ b : LatticeBond d S 𝒮.ξ, IsBoundaryBond (𝒮.innerRegion Q) b →
    b.source = x ∨ b.target = x → ∀ E : Set (LatticeBond d S 𝒮.ξ),
      IsBoundaryRule (𝒮.Ω 0) (𝒮.innerRegion Q) E → b ∈ E
structure CubeSupport (Q : CentredCube d S) : Prop where
  site_facts : ∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.Ω 0 → 𝒮.latticeCutoff Q x ≠ 0 →
    CutoffSiteFacts 𝒮 Q x
  nearCells_subset : nearCells 𝒮 Q ⊆ 𝒮.innerRegion Q
  eq_zero_off : ∀ ψ : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) ψ →
    ∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∉ nearCells 𝒮 Q →
      𝒮.commutatorOp (𝒮.latticeCutoff Q) ψ x = 0
  eq_of_eqOn : ∀ ψ ψ' : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) ψ →
    VanishesOff (𝒮.Ω 0) ψ' →
    (∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ nearCells 𝒮 Q → ψ x = ψ' x) →
      𝒮.commutatorOp (𝒮.latticeCutoff Q) ψ = 𝒮.commutatorOp (𝒮.latticeCutoff Q) ψ'
def CommutatorClaim : Prop :=
  ∀ (d L : ℕ) (aMinus aPlus : ℝ), Parameters d L aMinus aPlus →
    ∀ (S : ℝ) (𝒮 : BlockSetting d L aMinus aPlus S),
      CommutatorFormula 𝒮 ∧ CellBound 𝒮 ∧
        (3 * L * (L + 12) ≤ 𝒮.M → L * (L + 9) ≤ 𝒮.R₁ * 𝒮.M →
          ∀ Q ∈ 𝒮.coverCubes, CubeSupport 𝒮 Q)
end Dirichlet.Commutator
end YangMills.Construction
