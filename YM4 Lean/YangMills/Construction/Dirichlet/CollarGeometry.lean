import YangMills.Construction.Dirichlet.LatticeCalculus
import YangMills.Construction.Dirichlet.Parameters
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.Dirichlet.Geometry
variable {d L : ℕ} {S aMinus aPlus : ℝ}
def openBox (c : Fin d → ℝ) (σ : ℝ) : Set (Fin d → ℝ) := {v | ∀ μ, |v μ - c μ| < σ / 2}
def closedBox (c : Fin d → ℝ) (σ : ℝ) : Set (Fin d → ℝ) := {v | ∀ μ, |v μ - c μ| ≤ σ / 2}
def scaledIntLattice (ξ : ℝ) : Set (Fin d → ℝ) := {v | ∃ k : Fin d → ℤ, v = fun μ => (k μ : ℝ) * ξ}
def IsEuclidNeighbor (ξ : ℝ) (v w : Fin d → ℝ) : Prop :=
  ∃ μ, w = v + Pi.single μ ξ ∨ w = v - Pi.single μ ξ
variable (𝒮 : BlockSetting d L aMinus aPlus S)
structure FrontiersAndScaleRatios : Prop where
  frontier_disjoint : ∀ m m', 1 ≤ m → m ≤ 𝒮.t → 1 ≤ m' → m' ≤ 𝒮.t → m ≠ m' →
    Disjoint (frontier (𝒮.Ω m)) (frontier (𝒮.Ω m'))
  localScale_ratio : ∀ x x' : LatticeSite d S 𝒮.ξ, IsNeighbor x x' →
    𝒮.localScale x' / 𝒮.localScale x ∈ ({(L : ℝ)⁻¹, 1, (L : ℝ)} : Set ℝ)
def BlockDistInCells : Prop :=
  ∀ y ∈ 𝒮.centres, ∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.cell y →
    𝒮.blockDist x y ≤ (d : ℝ) / 2
def liftedBox (y : PeriodicTorus d S) (lift : Fin d → ℝ) : Set (Fin d → ℝ) :=
  closedBox lift (2 * ((L : ℝ) + 9) * 𝒮.centreSpacing y)
structure LiftedBoxFacts (y : PeriodicTorus d S) (lift : Fin d → ℝ) : Prop where
  bijOn : BijOn (torusProj d S) (liftedBox 𝒮 y lift) (𝒮.collar y)
  image_sites : torusProj d S '' (liftedBox 𝒮 y lift ∩ scaledIntLattice 𝒮.ξ) =
    𝒮.collar y ∩ (spacingLattice d S 𝒮.ξ : Set (PeriodicTorus d S))
  neighbor_iff : ∀ v ∈ liftedBox 𝒮 y lift ∩ scaledIntLattice 𝒮.ξ,
    ∀ w ∈ liftedBox 𝒮 y lift ∩ scaledIntLattice 𝒮.ξ,
    ∀ x x' : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) = torusProj d S v →
      (x' : PeriodicTorus d S) = torusProj d S w → (IsNeighbor x x' ↔ IsEuclidNeighbor 𝒮.ξ v w)
  dist_preserved : ∀ p ∈ liftedBox 𝒮 y lift, ∀ q ∈ liftedBox 𝒮 y lift,
    ‖p - q‖ ≤ ((L : ℝ) + 10) * 𝒮.centreSpacing y →
      supNorm (torusProj d S p - torusProj d S q) = ‖p - q‖ ∧
        lOneNorm (torusProj d S p - torusProj d S q) = ∑ μ, |p μ - q μ|
structure CollarFacts (n : ℕ) (y : PeriodicTorus d S) : Prop where
  injOn : ∀ c : Fin d → ℝ,
    InjOn (torusProj d S) (openBox c (2 * ((L : ℝ) + 10) * 𝒮.centreSpacing y))
  lifted : ∀ lift : Fin d → ℝ, torusProj d S lift = y → LiftedBoxFacts 𝒮 y lift
  inter_eq_empty : 𝒮.collar y ∩ 𝒮.Ω (n + 2) = ∅
  subset : 1 ≤ n → 𝒮.collar y ⊆ 𝒮.Ω (n - 1) ∧ 𝒮.collar y ⊆ 𝒮.Ω 0
  localScale_lower : ∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.collar y →
    (L : ℝ)⁻¹ * 𝒮.centreSpacing y ≤ 𝒮.localScale x
  localScale_upper : ∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.collar y →
    𝒮.localScale x ≤ (L : ℝ) * 𝒮.centreSpacing y
  blockDist_le : ∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.collar y →
    𝒮.blockDist x y ≤ (L : ℝ) * (𝒮.centreSpacing y)⁻¹ * lOneNorm ((x : PeriodicTorus d S) - y)
def GeometryHolds : Prop :=
  ∀ (d L : ℕ) (aMinus aPlus S : ℝ), Parameters d L aMinus aPlus →
    ∀ 𝒮 : BlockSetting d L aMinus aPlus S,
      FrontiersAndScaleRatios 𝒮 ∧ BlockDistInCells 𝒮 ∧
        (L + 10 ≤ 𝒮.M → L * (L + 9) ≤ 𝒮.R₁ * 𝒮.M →
          ∀ (n : ℕ) (y : PeriodicTorus d S), y ∈ shellSites L 𝒮.ξ 𝒮.Ω n → CollarFacts 𝒮 n y)
end YangMills.Construction.Dirichlet.Geometry
