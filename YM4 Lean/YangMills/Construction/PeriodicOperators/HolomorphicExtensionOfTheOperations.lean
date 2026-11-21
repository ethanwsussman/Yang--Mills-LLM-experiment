import YangMills.Construction.Towers.TheTwoOperatorFunctionsAsFunctionsOfValues
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.HolomorphicCoordinateClosure
structure ClosureProperties (P : PeriodicData) (ρ : ℝ) (T : Set P.Carrier) : Prop where
  of_subset : ∀ (S : Set P.Carrier) (g : (P.Carrier → ℂ) → ℂ), S ⊆ T →
    HolomorphicInValuesBelow P ρ S g → HolomorphicInValuesBelow P ρ T g
  of_radius_le : ∀ (r : ℝ) (g : (P.Carrier → ℂ) → ℂ), 0 < r → r ≤ ρ →
    HolomorphicInValuesBelow P ρ T g → HolomorphicInValuesBelow P r T g
  congr_below : ∀ g h : (P.Carrier → ℂ) → ℂ, (∀ ζ, IsSupBelow P ζ ρ → g ζ = h ζ) →
    HolomorphicInValuesBelow P ρ T g → HolomorphicInValuesBelow P ρ T h
  const : ∀ c : ℂ, HolomorphicInValuesBelow P ρ T fun _ => c
  coord : ∀ ξ ∈ T, HolomorphicInValuesBelow P ρ T fun ζ => ζ ξ
  add : ∀ g h : (P.Carrier → ℂ) → ℂ, HolomorphicInValuesBelow P ρ T g →
    HolomorphicInValuesBelow P ρ T h → HolomorphicInValuesBelow P ρ T fun ζ => g ζ + h ζ
  mul : ∀ g h : (P.Carrier → ℂ) → ℂ, HolomorphicInValuesBelow P ρ T g →
    HolomorphicInValuesBelow P ρ T h → HolomorphicInValuesBelow P ρ T fun ζ => g ζ * h ζ
  sum : ∀ {ι : Type} (s : Finset ι) (g : ι → (P.Carrier → ℂ) → ℂ),
    (∀ i ∈ s, HolomorphicInValuesBelow P ρ T (g i)) →
      HolomorphicInValuesBelow P ρ T fun ζ => ∑ i ∈ s, g i ζ
def ClosureHolds : Prop :=
  ∀ (P : PeriodicData) (ρ : ℝ) (T : Set P.Carrier), 0 < ρ → T.Finite → ClosureProperties P ρ T
end YangMills.Construction.PeriodicOperators.HolomorphicCoordinateClosure
end
