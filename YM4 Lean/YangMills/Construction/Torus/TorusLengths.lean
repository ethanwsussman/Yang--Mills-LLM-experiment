import YangMills.Construction.Torus.SeparatedChains
import YangMills.Construction.WeightedGreen.IntegerExpSums
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.WeightedGreen
noncomputable section
namespace YangMills.Construction.Torus
structure LengthAxioms (d : ℕ) (S : ℝ) : Prop where
  lOneNorm_nonneg : ∀ p : PeriodicTorus d S, 0 ≤ lOneNorm p
  lOneNorm_zero : lOneNorm (0 : PeriodicTorus d S) = 0
  lOneNorm_neg : ∀ p : PeriodicTorus d S, lOneNorm (-p) = lOneNorm p
  lOneNorm_add_le : ∀ p q : PeriodicTorus d S, lOneNorm (p + q) ≤ lOneNorm p + lOneNorm q
  supNorm_nonneg : ∀ p : PeriodicTorus d S, 0 ≤ supNorm p
  supNorm_zero : supNorm (0 : PeriodicTorus d S) = 0
  supNorm_le_lOneNorm : ∀ p : PeriodicTorus d S, supNorm p ≤ lOneNorm p
  lOneNorm_le_supNorm : ∀ p : PeriodicTorus d S, lOneNorm p ≤ (d : ℝ) * supNorm p
  continuous_supNorm : Continuous (supNorm : PeriodicTorus d S → ℝ)
  continuous_torusProj : Continuous (torusProj d S)
  torusProj_surjective : Function.Surjective (torusProj d S)
  exists_near_lattice_point : ∀ σ : ℝ, 0 < σ → ∀ p : PeriodicTorus d S,
    ∃ z ∈ spacingLattice d S σ, supNorm (p - z) ≤ σ / 2
structure LatticeSumBounds (d : ℕ) (S σ : ℝ) : Prop where
  finite : (spacingLattice d S σ : Set (PeriodicTorus d S)).Finite
  expSum_le : ∀ a : ℝ, 0 < a → ∀ z₀ ∈ spacingLattice d S σ,
    ∑ᶠ z ∈ (spacingLattice d S σ : Set (PeriodicTorus d S)), Real.exp (-a * lOneNorm (z - z₀) / σ) ≤
      intExpSum a ^ d
def TorusLengthsStatement : Prop :=
  ∀ (d : ℕ) (S : ℝ), 0 < S → LengthAxioms d S ∧
    ∀ (σ : ℝ) (k : ℕ), 0 < σ → 0 < k → S = (k : ℝ) * σ → LatticeSumBounds d S σ
end YangMills.Construction.Torus
