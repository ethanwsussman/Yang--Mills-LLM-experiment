import YangMills.Construction.LimitsOfLatticeFamilies.IsometriesTranslationsAndEnlargedSupports
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
def MinSeparationPos : Prop :=
  ∀ (s : Conventions.StandingParameters) (Y : ModelSpace), ∀ n, 2 ≤ n → ∀ f ∈ sepTuples s Y n,
    0 < minSeparation s Y f ∧
    (minSeparation s Y f = ⊤ ↔
      ∀ i k, (supportIn s Y (f i)).Nonempty → (supportIn s Y (f k)).Nonempty → i = k) ∧
    (minSeparation s Y f = ⊤ → (∃ i, f i = 0) ∧
      ∀ (a : Y.Carrier s) (ρ : ℝ≥0∞), 0 < ρ → ∀ Ψ : TupleFunctional (sepTuplesIn s Y n ρ),
        IsMultilinearSep Ψ → shiftTuple a f ∈ sepTuplesIn s Y n ρ →
          Ψ.extend (shiftTuple a f) = 0)
end YangMills.Construction.LatticeLimits
end
