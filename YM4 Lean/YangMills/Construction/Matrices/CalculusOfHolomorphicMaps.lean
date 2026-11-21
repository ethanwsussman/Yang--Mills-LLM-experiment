import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction
namespace Matrices
namespace GroupLieProduct
namespace HolomorphicCalculus
def CompToCoords (ι κ ι' κ' : Type) [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ'] :
    Prop :=
  ∀ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (W : Set (ι ⊕ κ → ComplexMatrix2))
    (Ψ : (ι ⊕ κ → ComplexMatrix2) → ι' ⊕ κ' → ComplexMatrix2),
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W → IsHolomorphicToProduct b W Ψ →
    ∀ (E : Type) (l : ℕ) (e : E ≃ Coordinates.ComplexCoordinates l)
      (W' : Set (ι' ⊕ κ' → ComplexMatrix2)) (Φ : (ι' ⊕ κ' → ComplexMatrix2) → E),
      IsHolomorphicToCoords b e W' Φ →
      ContinuousOn Ψ W ∧ ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) (W ∩ Ψ ⁻¹' W') ∧
        IsHolomorphicToCoords b e (W ∩ Ψ ⁻¹' W') (Φ ∘ Ψ)
def CompToProduct (ι κ ι' κ' ι'' κ'' : Type) [Fintype ι] [Fintype κ] [Fintype ι']
    [Fintype κ'] : Prop :=
  ∀ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (W : Set (ι ⊕ κ → ComplexMatrix2))
    (Ψ : (ι ⊕ κ → ComplexMatrix2) → ι' ⊕ κ' → ComplexMatrix2),
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W → IsHolomorphicToProduct b W Ψ →
    ∀ (W' : Set (ι' ⊕ κ' → ComplexMatrix2))
      (Φ : (ι' ⊕ κ' → ComplexMatrix2) → ι'' ⊕ κ'' → ComplexMatrix2),
      IsHolomorphicToProduct b W' Φ →
      ContinuousOn Ψ W ∧ ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) (W ∩ Ψ ⁻¹' W') ∧
        IsHolomorphicToProduct b (W ∩ Ψ ⁻¹' W') (Φ ∘ Ψ)
def RestrictToCoords (ι κ : Type) [Fintype ι] [Fintype κ] : Prop :=
  ∀ (E : Type) (l k : ℕ) (e : E ≃ Coordinates.ComplexCoordinates l) (ν : ι ⊕ κ ≃ Fin k)
    (O : Set (ι ⊕ κ → ComplexMatrix2)) (h : (ι ⊕ κ → ComplexMatrix2) → E),
    Coordinates.ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv ν) e O h →
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) (O ∩ GroupLieProduct ι κ) ∧
      ∀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
        IsHolomorphicToCoords b e (O ∩ GroupLieProduct ι κ) h
def RestrictToProduct (ι κ ι' κ' : Type) [Fintype ι] [Fintype κ] : Prop :=
  ∀ (k k' : ℕ) (ν : ι ⊕ κ ≃ Fin k) (ν' : ι' ⊕ κ' ≃ Fin k') (O : Set (ι ⊕ κ → ComplexMatrix2))
    (h : (ι ⊕ κ → ComplexMatrix2) → ι' ⊕ κ' → ComplexMatrix2),
    Coordinates.ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv ν) (matrixPiEquiv ν') O h →
    MapsTo h (O ∩ GroupLieProduct ι κ) (GroupLieProduct ι' κ') →
    ∀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
      IsHolomorphicToProduct b (O ∩ GroupLieProduct ι κ) h
def AddMul (ι κ : Type) [Fintype ι] [Fintype κ] : Prop :=
  ∀ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (W : Set (ι ⊕ κ → ComplexMatrix2))
    (f g : (ι ⊕ κ → ComplexMatrix2) → ℂ),
    IsHolomorphicToCoords b (Equiv.funUnique (Fin 1) ℂ).symm W f →
    IsHolomorphicToCoords b (Equiv.funUnique (Fin 1) ℂ).symm W g →
    IsHolomorphicToCoords b (Equiv.funUnique (Fin 1) ℂ).symm W (fun p => f p + g p) ∧
      IsHolomorphicToCoords b (Equiv.funUnique (Fin 1) ℂ).symm W (fun p => f p * g p)
def IUnionToCoords (ι κ : Type) [Fintype ι] [Fintype κ] : Prop :=
  ∀ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (J : Type)
    (U : J → Set (ι ⊕ κ → ComplexMatrix2)),
    (∀ j, ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) (U j)) →
    ∀ (E : Type) (l : ℕ) (e : E ≃ Coordinates.ComplexCoordinates l)
      (Φ : (ι ⊕ κ → ComplexMatrix2) → E),
      IsHolomorphicToCoords b e (⋃ j, U j) Φ ↔
        ∀ j, IsHolomorphicToCoords b e (U j) Φ
def IUnionToProduct (ι κ ι' κ' : Type) [Fintype ι] [Fintype κ] : Prop :=
  ∀ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (J : Type)
    (U : J → Set (ι ⊕ κ → ComplexMatrix2)),
    (∀ j, ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) (U j)) →
    ∀ Φ : (ι ⊕ κ → ComplexMatrix2) → ι' ⊕ κ' → ComplexMatrix2,
      IsHolomorphicToProduct b (⋃ j, U j) Φ ↔ ∀ j, IsHolomorphicToProduct b (U j) Φ
def MonoToCoords (ι κ : Type) [Fintype ι] [Fintype κ] : Prop :=
  ∀ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (W W₀ : Set (ι ⊕ κ → ComplexMatrix2))
    (E : Type) (l : ℕ) (e : E ≃ Coordinates.ComplexCoordinates l)
    (Φ : (ι ⊕ κ → ComplexMatrix2) → E),
    IsHolomorphicToCoords b e W Φ → ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W₀ →
    W₀ ⊆ W → IsHolomorphicToCoords b e W₀ Φ
def MonoToProduct (ι κ ι' κ' : Type) [Fintype ι] [Fintype κ] : Prop :=
  ∀ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (W W₀ : Set (ι ⊕ κ → ComplexMatrix2))
    (Φ : (ι ⊕ κ → ComplexMatrix2) → ι' ⊕ κ' → ComplexMatrix2),
    IsHolomorphicToProduct b W Φ → ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W₀ →
    W₀ ⊆ W → IsHolomorphicToProduct b W₀ Φ
def OfLieCoords (ι κ : Type) [Fintype ι] [Fintype κ] [IsEmpty ι] : Prop :=
  ∀ W : Set (ι ⊕ κ → ComplexMatrix2), ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W →
    (∀ (E : Type) (l : ℕ) (e : E ≃ Coordinates.ComplexCoordinates l)
      (b b' : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
      (Φ : (ι ⊕ κ → ComplexMatrix2) → E),
      IsHolomorphicToCoords b e W Φ ↔
        ∀ ν : ι ⊕ κ ≃ Fin (Fintype.card (ι ⊕ κ)),
          Coordinates.ComplexCoordinates.IsHolomorphicIn (tupleOfCoords b' ν ⁻¹' W)
            (e ∘ Φ ∘ tupleOfCoords b' ν)) ∧
    ∀ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
      (ν : ι ⊕ κ ≃ Fin (Fintype.card (ι ⊕ κ))),
      IsOpen (tupleOfCoords b ν ⁻¹' W)
def Properties : Prop :=
  (∀ (ι κ ι' κ' : Type) [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ'],
    CompToCoords ι κ ι' κ') ∧
  (∀ (ι κ ι' κ' ι'' κ'' : Type) [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ'] [Fintype ι'']
    [Fintype κ''], CompToProduct ι κ ι' κ' ι'' κ'') ∧
  (∀ (ι κ : Type) [Fintype ι] [Fintype κ], RestrictToCoords ι κ) ∧
  (∀ (ι κ ι' κ' : Type) [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ'],
    RestrictToProduct ι κ ι' κ') ∧
  (∀ (ι κ : Type) [Fintype ι] [Fintype κ], AddMul ι κ) ∧
  (∀ (ι κ : Type) [Fintype ι] [Fintype κ], IUnionToCoords ι κ) ∧
  (∀ (ι κ ι' κ' : Type) [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ'],
    IUnionToProduct ι κ ι' κ') ∧
  (∀ (ι κ : Type) [Fintype ι] [Fintype κ], MonoToCoords ι κ) ∧
  (∀ (ι κ ι' κ' : Type) [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ'],
    MonoToProduct ι κ ι' κ') ∧
  (∀ (ι κ : Type) [Fintype ι] [Fintype κ] [IsEmpty ι], OfLieCoords ι κ)
end HolomorphicCalculus
end GroupLieProduct
end Matrices
end YangMills.Construction
