import YangMills.Construction.Lattice.GaugeFieldSpacesAndRealAnalyticMaps
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.Matrices
namespace GroupLieProduct
namespace Subspaces
variable {S R S' R' S₁ S₂ R₁ R₂ : Type}
def ofParts (W : R → ComplexMatrix2) (Z : S → ComplexMatrix2) : R ⊕ S → ComplexMatrix2 :=
  Sum.elim W Z
def groupComponent (q : R ⊕ S → ComplexMatrix2) : R → ComplexMatrix2 := fun r => q (.inl r)
def algebraComponent (q : R ⊕ S → ComplexMatrix2) : S → ComplexMatrix2 := fun s => q (.inr s)
def subspaceTimesGroup (E : Submodule ℝ (S → ComplexMatrix2)) (R : Type) :
    Set (R ⊕ S → ComplexMatrix2) :=
  {q | algebraComponent q ∈ E ∧ groupComponent q ∈ compactPi R}
def IsOpenInSubspaceTimesGroup (E : Submodule ℝ (S → ComplexMatrix2))
    (V : Set (R ⊕ S → ComplexMatrix2)) : Prop :=
  E ≤ hermitianTracelessFunctions S ∧ ComplexMatrix2.IsRelativelyOpen (subspaceTimesGroup E R) V
def sumSubmodule (E₁ : Submodule ℝ (S₁ → ComplexMatrix2)) (E₂ : Submodule ℝ (S₂ → ComplexMatrix2)) :
    Submodule ℝ (S₁ ⊕ S₂ → ComplexMatrix2) :=
  E₁.comap (LinearMap.funLeft ℝ ComplexMatrix2 Sum.inl) ⊓
    E₂.comap (LinearMap.funLeft ℝ ComplexMatrix2 Sum.inr)
def pairPoint (p : R₁ ⊕ S₁ → ComplexMatrix2) (q : R₂ ⊕ S₂ → ComplexMatrix2) :
    (R₁ ⊕ R₂) ⊕ (S₁ ⊕ S₂) → ComplexMatrix2 :=
  ofParts (Sum.elim (groupComponent p) (groupComponent q))
    (Sum.elim (algebraComponent p) (algebraComponent q))
def IsSubspaceAnalyticToCoords [Fintype S] [Fintype R] {l : ℕ}
    (E : Submodule ℝ (S → ComplexMatrix2)) (V : Set (R ⊕ S → ComplexMatrix2))
    (f : (R ⊕ S → ComplexMatrix2) → YangMills.Construction.Coordinates.ComplexCoordinates l) :
    Prop :=
  IsOpenInSubspaceTimesGroup E V ∧
    ∀ p ∈ V, ∃ U : Set (R ⊕ S → ComplexMatrix2), p ∈ U ∧
      ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R S) U ∧
      U ∩ subspaceTimesGroup E R ⊆ V ∧
      ∃ Φ : (R ⊕ S → ComplexMatrix2) → YangMills.Construction.Coordinates.ComplexCoordinates l,
        (∀ b, IsHolomorphicToCoords b (Equiv.refl _) U Φ) ∧
          EqOn Φ f (U ∩ subspaceTimesGroup E R)
def IsSubspaceAnalyticToProduct [Fintype S] [Fintype R] (E : Submodule ℝ (S → ComplexMatrix2))
    (E' : Submodule ℝ (S' → ComplexMatrix2)) (V : Set (R ⊕ S → ComplexMatrix2))
    (f : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2) : Prop :=
  IsOpenInSubspaceTimesGroup E V ∧ E' ≤ hermitianTracelessFunctions S' ∧
    MapsTo f V (subspaceTimesGroup E' R') ∧
    ∀ p ∈ V, ∃ U : Set (R ⊕ S → ComplexMatrix2), p ∈ U ∧
      ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R S) U ∧
      U ∩ subspaceTimesGroup E R ⊆ V ∧
      ∃ Ψ : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2,
        (∀ b, IsHolomorphicToProduct b U Ψ) ∧ EqOn Ψ f (U ∩ subspaceTimesGroup E R)
def HasLocalHolomorphicExtensionToCoords [Fintype S] [Fintype R] {l : ℕ}
    (V : Set (R ⊕ S → ComplexMatrix2))
    (f : (R ⊕ S → ComplexMatrix2) → YangMills.Construction.Coordinates.ComplexCoordinates l) :
    Prop :=
  ComplexMatrix2.IsRelativelyOpen (subspaceTimesGroup (hermitianTracelessFunctions S) R) V ∧
    ∀ p ∈ V, ∃ U : Set (R ⊕ S → ComplexMatrix2), p ∈ U ∧
      ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R S) U ∧
      ∃ Φ : (R ⊕ S → ComplexMatrix2) → YangMills.Construction.Coordinates.ComplexCoordinates l,
        (∀ b, IsHolomorphicToCoords b (Equiv.refl _) U Φ) ∧ EqOn Φ f (U ∩ V)
def HasLocalHolomorphicExtensionToProduct [Fintype S] [Fintype R]
    (V : Set (R ⊕ S → ComplexMatrix2))
    (f : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2) : Prop :=
  ComplexMatrix2.IsRelativelyOpen (subspaceTimesGroup (hermitianTracelessFunctions S) R) V ∧
    MapsTo f V (subspaceTimesGroup (hermitianTracelessFunctions S') R') ∧
    ∀ p ∈ V, ∃ U : Set (R ⊕ S → ComplexMatrix2), p ∈ U ∧
      ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R S) U ∧
      ∃ Ψ : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2,
        (∀ b, IsHolomorphicToProduct b U Ψ) ∧ EqOn Ψ f (U ∩ V)
def IsAnalyticOnSubspace [Fintype S] (E : Submodule ℝ (S → ComplexMatrix2))
    (E' : Submodule ℝ (S' → ComplexMatrix2)) (O : Set (S → ComplexMatrix2))
    (f : (S → ComplexMatrix2) → S' → ComplexMatrix2) : Prop :=
  IsSubspaceAnalyticToProduct (R := Empty) (R' := Empty) E E' {q | algebraComponent q ∈ O}
    fun q => ofParts Empty.elim (f (algebraComponent q))
end Subspaces
end GroupLieProduct
end YangMills.Construction.Matrices
