import YangMills.Construction.TorusOrFourSpace.ArbitraryFamilyOfDenseSets
import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNorm
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace
namespace DenseFamilies
open Kind VectorClasses
variable (D : Params) (E : Kind)
def StockClassProperties (Q : Set (E.Pt D)) : Prop :=
  c1VanishingOutside D E Q = c1SupportedIn D E Q ∧
    IsLinearSubspaceSet D E (c1VanishingOutside D E Q) ∧
    ∀ A : Set (E.Pt D → ℝ), A ⊆ c1VanishingOutside D E Q →
      (IsDenseWrt D E (euclidC1Norm D E) (c1VanishingOutside D E Q) A ↔
        IsDenseWrt D E (c1NormQ D E) (c1VanishingOutside D E Q) A)
def FamilyMembersOfLength (F : DenseChoiceFamily D E) (n : ℕ) : Prop :=
  (∀ φ : Fin n → E.Pt D → ℝ, (⟨n, φ⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ F.tuples →
      ∃ Q : Fin n → supportStock D E, F.Builds φ Q) ∧
    ∀ (φ : Fin n → E.Pt D → ℝ) (Q : Fin n → supportStock D E),
      (⟨n, φ⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ F.tuples → F.Builds φ Q →
        (∀ i, φ i ∈ c1SupportedIn D E (Q i : Set (E.Pt D))) ∧
        (∀ i, supportQ D E (φ i) ⊆ (Q i : Set (E.Pt D))) ∧
        φ ∈ sepC1Tuples D E n
end DenseFamilies
open Kind DenseFamilies in
def DenseFamilies.Claim : Prop :=
  ∀ (D : Params) (E : Kind),
    ((∀ Q ∈ supportStock D E, StockClassProperties D E Q) ∧ Nonempty (DenseChoiceFamily D E)) ∧
    ∀ (F : DenseChoiceFamily D E) (n : ℕ), 1 ≤ n → FamilyMembersOfLength D E F n
end YangMills.Construction.PeriodicSpace
