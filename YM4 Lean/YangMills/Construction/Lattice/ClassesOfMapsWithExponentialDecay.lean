import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences
open Set PeriodicLattice
open scoped ENNReal
variable {L m : ℕ} (S : ScaleData)
def decayWeight (Ω : ℕ → Set (FourTorus L m)) (δ : ℝ) (y y' : FourTorus L m) : ℝ≥0∞ :=
  open Classical in
  if layerWeightedDist S Ω y y' = ⊤ then 0
  else ENNReal.ofReal (Real.exp (-(δ * (layerWeightedDist S Ω y y').toReal)))
structure IsLayerSeminormFamily {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    (Ω : ℕ → Set (FourTorus L m)) (N : FourTorus L m → Z → ℝ≥0∞) : Prop where
  ne_top : ∀ y ∈ layerPoints S Ω, ∀ z, N y z ≠ ⊤
  add_le : ∀ y ∈ layerPoints S Ω, ∀ z z', N y (z + z') ≤ N y z + N y z'
  smul_eq : ∀ y ∈ layerPoints S Ω, ∀ (c : ℂ) (z : Z), N y (c • z) = ENNReal.ofReal ‖c‖ * N y z
  eq_zero : ∀ z, (∀ y ∈ layerPoints S Ω, N y z = 0) → z = 0
def expDecayMaps {Z' Z : Type*} [AddCommGroup Z'] [Module ℂ Z'] [FiniteDimensional ℂ Z']
    [AddCommGroup Z] [Module ℂ Z] [FiniteDimensional ℂ Z] (Ω : ℕ → Set (FourTorus L m)) (δ B : ℝ)
    (N' : FourTorus L m → Z' → ℝ≥0∞) (N : FourTorus L m → Z → ℝ≥0∞) : Set (Z' →ₗ[ℂ] Z) :=
  {T | ∀ g, ∀ y ∈ layerPoints S Ω,
    N y (T g) ≤ ENNReal.ofReal B * ⨆ y' ∈ layerPoints S Ω, decayWeight S Ω δ y y' * N' y' g}
end YangMills.Construction.SeparatedSequences
