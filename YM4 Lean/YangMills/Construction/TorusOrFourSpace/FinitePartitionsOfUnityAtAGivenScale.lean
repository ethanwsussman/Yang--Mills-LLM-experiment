import YangMills.Construction.TorusOrFourSpace.FunctionsOfClassC1SupportsAndNorms
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
def SmallScalePartitionsOfUnity : Prop :=
  ∀ (D : Params) (E : Kind) (K : Set (Pt D E)), IsCompactQ D E K →
    ∀ η : ℝ, 0 < η →
      ∃ (P : ℕ) (_ : 1 ≤ P) (θ : Fin P → Pt D E → ℝ),
        (∀ k, θ k ∈ smoothUnitIntervalSet D E) ∧
        (∀ k, IsCompactQ D E (supportQ D E (θ k))) ∧
        (∀ k, setDiam D E (supportQ D E (θ k)) < ENNReal.ofReal η) ∧
        ∀ y ∈ K, ∑ k, θ k y = 1
end YangMills.Construction.PeriodicSpace
