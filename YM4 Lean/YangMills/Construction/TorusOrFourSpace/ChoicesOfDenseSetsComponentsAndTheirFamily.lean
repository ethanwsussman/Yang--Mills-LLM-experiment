import YangMills.Construction.TorusOrFourSpace.BoxesStockOfSupportsAndFamilyOfTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicSpace
namespace Kind
variable (D : Params) (E : Kind)
def IsDenseChoice (C : supportStock D E → Set (E.Pt D → ℝ)) : Prop :=
  ∀ Q, C Q ⊆ c1VanishingOutside D E Q ∧
    IsDenseWrt D E (euclidC1Norm D E) (c1VanishingOutside D E Q) (C Q)
def IsCountableDenseChoice (C : supportStock D E → Set (E.Pt D → ℝ)) : Prop :=
  IsDenseChoice D E C ∧ ∀ Q, (C Q).Countable
def choiceComponents (C : supportStock D E → Set (E.Pt D → ℝ)) : Set (E.Pt D → ℝ) :=
  ⋃ Q, C Q
def IsListedOver (C : supportStock D E → Set (E.Pt D → ℝ)) {n : ℕ}
    (φ : Fin n → E.Pt D → ℝ) (Q : Fin n → Set (E.Pt D)) : Prop :=
  ∃ hQ : ∀ i, Q i ∈ supportStock D E,
    Pairwise (fun i j => Disjoint (Q i) (Q j)) ∧ ∀ i, φ i ∈ C ⟨Q i, hQ i⟩
def choiceTupleFamily (C : supportStock D E → Set (E.Pt D → ℝ)) :
    Set (Σ n : ℕ, Fin n → E.Pt D → ℝ) :=
  {p | 1 ≤ p.1 ∧ ∃ Q, IsListedOver D E C p.2 Q}
end Kind
end PeriodicSpace
end YangMills.Construction
