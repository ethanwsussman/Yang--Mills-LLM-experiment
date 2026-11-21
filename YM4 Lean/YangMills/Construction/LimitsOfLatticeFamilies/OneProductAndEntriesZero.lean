import YangMills.Construction.LimitsOfLatticeFamilies.SpacesOfFunctionsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
def CommonProductAndZeroComponent : Prop :=
  ∀ (s : Conventions.StandingParameters) (Y : ModelSpace) (n : ℕ), 1 ≤ n → ∀ r : ℝ≥0∞, 0 < r →
    (∀ g ∈ sepTuplesIn s Y n r, ∀ g' ∈ sepTuplesIn s Y n r,
      (∃ i, g i ≠ g' i ∧ ∀ l, l ≠ i → g l = g' l) →
      ∃ A : Fin n → Set (Y.Carrier s), (∀ l, A l ⊆ ballAtBase s Y r) ∧
        (∀ l k, l ≠ k → Disjoint (A l) (A k)) ∧ (∀ l, g l ∈ c1CompactSupp s Y (A l)) ∧
        ∀ l, g' l ∈ c1CompactSupp s Y (A l)) ∧
    (∀ Ψ : TupleFunctional (sepTuplesIn s Y n r), IsMultilinearSep Ψ →
      ∀ h ∈ sepTuplesIn s Y n r, ∀ i, h i = 0 → Ψ.extend h = 0) ∧
    (∀ g ∈ lipSepTuplesIn s Y n r, ∀ g' ∈ lipSepTuplesIn s Y n r,
      (∃ i, g i ≠ g' i ∧ ∀ l, l ≠ i → g l = g' l) →
      ∃ A : Fin n → Set (Y.Carrier s), (∀ l, A l ⊆ ballAtBase s Y r) ∧
        (∀ l k, l ≠ k → Disjoint (A l) (A k)) ∧ (∀ l, g l ∈ lipCompactSupp s Y (A l)) ∧
        ∀ l, g' l ∈ lipCompactSupp s Y (A l)) ∧
    ∀ Ψ : TupleFunctional (lipSepTuplesIn s Y n r), IsMultilinearLip Ψ →
      ∀ h ∈ lipSepTuplesIn s Y n r, ∀ i, h i = 0 → Ψ.extend h = 0
end YangMills.Construction.LatticeLimits
end
