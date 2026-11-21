import YangMills.Construction.TorusOrFourSpace.ChoicesOfDenseSetsComponentsAndTheirFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.CountableDenseFamilies
def Statement : Prop :=
  ∀ (D : Params) (E : Kind),
    (∀ C : supportStock D E → Set (E.Pt D → ℝ),
      IsCountableDenseChoice D E C ↔ IsDenseFamily D E C) ∧
    (∀ C : supportStock D E → Set (E.Pt D → ℝ), IsCountableDenseChoice D E C →
      choiceTupleFamily D E C = tupleFamily D E C) ∧
    (∀ C : supportStock D E → Set (E.Pt D → ℝ), IsCountableDenseChoice D E C →
      ∀ (n : ℕ) (φ : Fin n → E.Pt D → ℝ),
        (⟨n, φ⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ choiceTupleFamily D E C →
        ∀ Q : Fin n → Set (E.Pt D),
          IsListedOver D E C φ Q ↔
            ∃ hQ : ∀ i, Q i ∈ supportStock D E,
              IsBuiltFrom D E C φ fun i => ⟨Q i, hQ i⟩)
end YangMills.Construction.PeriodicSpace.Kind.CountableDenseFamilies
