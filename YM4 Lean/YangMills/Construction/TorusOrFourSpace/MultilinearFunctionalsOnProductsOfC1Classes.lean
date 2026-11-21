import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNorm
import YangMills.Construction.TorusOrFourSpace.CutOffsOnAProductOfOpenSets
import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsAndProductsOfClasses
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
section Components
variable (P : Params) (Q : Kind)
def C1SupportedLinearWithRealTestFns : Prop :=
  (∀ S : Set (Q.Pt P),
    VectorClasses.IsLinearSubspaceSet P Q (c1SupportedIn P Q S)) ∧
  ∀ U : Set (Q.Pt P), IsOpenQ P Q U → ∀ f : Q.Pt P → ℝ,
    (fun x => (f x : ℂ)) ∈ Tuple.singleTestFns P Q U → f ∈ c1SupportedIn P Q U
def ProductSetSubsetSepC1 (n : ℕ) : Prop :=
  ∀ S : Fin n → Set (Q.Pt P), (∀ a b, a ≠ b → Disjoint (S a) (S b)) →
    productSet P Q (fun a => c1SupportedIn P Q (S a)) ⊆ sepC1Tuples P Q n
def MultilinearOnDisjointProducts (n : ℕ) : Prop :=
  ∀ F : sepC1Tuples P Q n → ℝ,
    IsMultilinearOn P Q (sepC1Tuples P Q n) F →
    ∀ S : Fin n → Set (Q.Pt P), (∀ a b, a ≠ b → Disjoint (S a) (S b)) →
      IsMultilinearOnProduct P Q (sepC1Tuples P Q n) (fun a => c1SupportedIn P Q (S a)) F
def DisjointCompactInfDistPosFinite : Prop :=
  ∀ K₁ K₂ : Set (Q.Pt P), IsCompactQ P Q K₁ → IsCompactQ P Q K₂ → Disjoint K₁ K₂ →
    K₁.Nonempty → K₂.Nonempty → 0 < setInfDist P Q K₁ K₂ ∧ setInfDist P Q K₁ K₂ < ∞
end Components
namespace DisjointProducts
def Claim : Prop :=
  ∀ (P : Params) (Q : Kind) (n : ℕ), 1 ≤ n →
    C1SupportedLinearWithRealTestFns P Q ∧
    ProductSetSubsetSepC1 P Q n ∧
    MultilinearOnDisjointProducts P Q n ∧
    MultilinearZeroAtZeroCoordinate P Q (sepC1Tuples P Q n) ∧
    DisjointCompactInfDistPosFinite P Q
end DisjointProducts
end YangMills.Construction.PeriodicSpace.Kind
