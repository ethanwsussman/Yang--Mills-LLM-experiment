import YangMills.Construction.TorusOrFourSpace.ClassesOfFunctionsWithSupportInASet
import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsAndSetsAtPositiveDistance
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
section Parts
variable (D : Params) (E : Kind)
def productSet {n : ℕ} (W : Fin n → Set (E.Pt D → ℝ)) : Set (FnTuple D E n) :=
  Set.pi Set.univ W
def IsMultilinearOnProduct {n : ℕ} (K : Set (FnTuple D E n)) (W : Fin n → Set (E.Pt D → ℝ))
    (Ψ : K → ℝ) : Prop :=
  productSet D E W ⊆ K ∧
    ∀ g ∈ productSet D E W, ∀ j : Fin n, ∀ f₁ ∈ W j, ∀ f₂ ∈ W j, ∀ (a b : ℝ)
      (h₁ : Function.update g j f₁ ∈ K) (h₂ : Function.update g j f₂ ∈ K)
      (h₃ : Function.update g j (a • f₁ + b • f₂) ∈ K),
      Ψ ⟨_, h₃⟩ = a * Ψ ⟨_, h₁⟩ + b * Ψ ⟨_, h₂⟩
def InBallPairwiseApart {n : ℕ} (ρ : ℝ≥0∞) (A : Fin n → Set (E.Pt D)) : Prop :=
  (∀ k, A k ⊆ centredBall D E ρ) ∧ PairwisePositiveSetDist D E A
def pairSupports {n : ℕ} (f f' : FnTuple D E n) (j : Fin n) : Fin n → Set (E.Pt D) :=
  Function.update (fun k => supportQ D E (f k)) j (supportQ D E (f j) ∪ supportQ D E (f' j))
def ProductsSubset {n : ℕ} (ρ : ℝ≥0∞) (K : Set (FnTuple D E n))
    (V : Set (E.Pt D) → Set (E.Pt D → ℝ)) : Prop :=
  ∀ A : Fin n → Set (E.Pt D), InBallPairwiseApart D E ρ A →
    productSet D E (fun k => V (A k)) ⊆ K
def PairInCommonProduct {n : ℕ} (ρ : ℝ≥0∞) (K : Set (FnTuple D E n))
    (V : Set (E.Pt D) → Set (E.Pt D → ℝ)) : Prop :=
  ∀ (j : Fin n) (f f' : FnTuple D E n), f ∈ K → f' ∈ K → (∀ k, k ≠ j → f k = f' k) →
    (∀ k, IsCompactQ D E (pairSupports D E f f' j k)) ∧
    (∀ k k', k ≠ k' →
      Disjoint (pairSupports D E f f' j k) (pairSupports D E f f' j k')) ∧
    InBallPairwiseApart D E ρ (pairSupports D E f f' j) ∧
    f ∈ productSet D E (fun k => V (pairSupports D E f f' j k)) ∧
    f' ∈ productSet D E (fun k => V (pairSupports D E f f' j k)) ∧
    ∀ a a' : ℝ, Function.update f j (a • f j + a' • f' j) ∈
      productSet D E (fun k => V (pairSupports D E f f' j k))
def MultilinearIffOnProducts {n : ℕ} (ρ : ℝ≥0∞) (K : Set (FnTuple D E n))
    (V : Set (E.Pt D) → Set (E.Pt D → ℝ)) : Prop :=
  ∀ Ψ : K → ℝ, IsMultilinearOn D E K Ψ ↔
    ∀ A : Fin n → Set (E.Pt D), InBallPairwiseApart D E ρ A →
      IsMultilinearOnProduct D E K (fun k => V (A k)) Ψ
def MultilinearZeroAtZeroCoordinate {n : ℕ} (K : Set (FnTuple D E n)) : Prop :=
  ∀ Ψ : K → ℝ, IsMultilinearOn D E K Ψ →
    ∀ (f : K) (j : Fin n), f.1 j = 0 → Ψ f = 0
def EqUnionProducts {n : ℕ} (ρ : ℝ≥0∞) (K : Set (FnTuple D E n))
    (V : Set (E.Pt D) → Set (E.Pt D → ℝ)) : Prop :=
  K = ⋃ (A : Fin n → Set (E.Pt D)) (_ : InBallPairwiseApart D E ρ A),
    productSet D E (fun k => V (A k))
def ProductStructure {n : ℕ} (ρ : ℝ≥0∞) (K : Set (FnTuple D E n))
    (V : Set (E.Pt D) → Set (E.Pt D → ℝ)) : Prop :=
  ProductsSubset D E ρ K V ∧ PairInCommonProduct D E ρ K V ∧
    MultilinearIffOnProducts D E ρ K V ∧ MultilinearZeroAtZeroCoordinate D E K ∧
    EqUnionProducts D E ρ K V
def MultilinearIffOnOpenProducts (n : ℕ) : Prop :=
  ∀ Ψ : sepC1Tuples D E n → ℝ,
    IsMultilinearOn D E (sepC1Tuples D E n) Ψ ↔
      ∀ O : Fin n → Set (E.Pt D), (∀ k, IsOpenQ D E (O k)) →
        (∀ k k', k ≠ k' → Disjoint (closureQ D E (O k)) (closureQ D E (O k'))) →
        IsMultilinearOnProduct D E (sepC1Tuples D E n) (fun k => c1SupportedIn D E (O k)) Ψ
end Parts
namespace MultilinearProducts
def Statement : Prop :=
  ∀ (D : Params) (E : Kind) (n : ℕ), 1 ≤ n →
    (∀ ρ : ℝ≥0∞, 0 < ρ →
      ProductStructure D E ρ (sepC1TuplesWithin D E n (centredBall D E ρ))
        (c1SupportedIn D E) ∧
      ProductStructure D E ρ
        (sepLipTuplesWithin D E n (centredBall D E ρ)) (lipschitzSupportedIn D E)) ∧
    MultilinearIffOnOpenProducts D E n
end MultilinearProducts
end YangMills.Construction.PeriodicSpace.Kind
