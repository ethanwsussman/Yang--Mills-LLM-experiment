import YangMills.Construction.ComplexAnalysis.BanachValuedHolomorphy
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.BanachValued.ConjugationInner
open YangMills.Construction.Coordinates
variable {p : ℕ}
def conjPoint (z : ComplexCoordinates p) : ComplexCoordinates p := fun j => conj (z j)
def conjSet (O : Set (ComplexCoordinates p)) : Set (ComplexCoordinates p) :=
  {z | conjPoint z ∈ O}
def IsCoordHolomorphicOn (O : Set (ComplexCoordinates p)) (f : ComplexCoordinates p → ℂ) : Prop :=
  ComplexCoordinates.IsHolomorphicIn O ((Equiv.funUnique (Fin 1) ℂ).symm ∘ f)
def Properties : Prop :=
  ∀ (p : ℕ), 1 ≤ p → ∀ O : Set (ComplexCoordinates p), IsOpen O →
    (∀ f : ComplexCoordinates p → ℂ, IsHolomorphicOnOpen O f ↔ IsCoordHolomorphicOn O f) ∧
    (∀ f : ComplexCoordinates p → ℂ, IsCoordHolomorphicOn O f →
      IsCoordHolomorphicOn (conjSet O) fun z => conj (f (conjPoint z))) ∧
    ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (Φ : ComplexCoordinates p → K) (ψ : K), IsHolomorphicOnOpen O Φ →
        IsCoordHolomorphicOn O (fun z => inner ℂ ψ (Φ z)) ∧
        IsCoordHolomorphicOn (conjSet O) fun z => inner ℂ (Φ (conjPoint z)) ψ
end YangMills.Construction.BanachValued.ConjugationInner
