import YangMills.Construction.TorusOrFourSpace.ChoicesOfDenseSetsComponentsAndTheirFamily
import YangMills.Construction.TorusOrFourSpace.StockOfSupportsAndTheCountableFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
def CountableChoiceFamilyFacts : Prop :=
  ∀ (D : Params) (E : Kind),
    ((supportStock D E).Countable ∧ ∀ Q ∈ supportStock D E, IsCompactQ D E Q) ∧
    (∀ Q ∈ supportStock D E,
      c1VanishingOutside D E Q = c1SupportedIn D E Q ∧
      (∀ f ∈ c1VanishingOutside D E Q, ∀ y, y ∉ Q → gradVec D E f y = 0) ∧
      IsSeparableBanachWrt D E (euclidC1Norm D E) (c1VanishingOutside D E Q) ∧
      ∀ A, A ⊆ c1VanishingOutside D E Q →
        IsDenseWrt D E (euclidC1Norm D E) (c1VanishingOutside D E Q) A →
        IsDenseWrt D E (sharpNormQ D E) (c1VanishingOutside D E Q) A) ∧
    (∀ S W : Set (E.Pt D), IsCompactQ D E S → IsOpenQ D E W → S ⊆ W →
      ∃ Q ∈ supportStock D E, S ⊆ Q ∧ Q ⊆ W) ∧
    ∀ C : supportStock D E → Set (E.Pt D → ℝ), IsCountableDenseChoice D E C →
      (tupleFamily D E C).Countable ∧
      ∀ (n : ℕ) (φ : Fin n → E.Pt D → ℝ) (Q : Fin n → supportStock D E),
        (⟨n, φ⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ tupleFamily D E C →
        IsBuiltFrom D E C φ Q →
        φ ∈ sepC1Tuples D E n ∧
        (∀ i, supportQ D E (φ i) ⊆ (Q i : Set (E.Pt D))) ∧
        (2 ≤ n →
          minPairwiseDist D E (fun i => (Q i : Set (E.Pt D))) ≤ supportGap D E φ ∧
          0 < minPairwiseDist D E (fun i => (Q i : Set (E.Pt D))))
end YangMills.Construction.PeriodicSpace
