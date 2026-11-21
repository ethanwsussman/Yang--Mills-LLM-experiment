import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.Matrices.EntrywiseHolomorphy
abbrev matrixKinds (n : ℕ) : Fin n → Coordinates.ComplexCoordinates.Component := fun _ => .matrix
abbrev groupKinds (n : ℕ) : Fin n → ComplexMatrix2.FactorKind := fun _ => .group
abbrev targetKind : Unit → ComplexMatrix2.FactorKind := fun _ => .group
abbrev unimodularPow (n : ℕ) : Set (Fin n → ComplexMatrix2) :=
  ComplexMatrix2.complexifiedProduct (groupKinds n)
abbrev unitaryPow (n : ℕ) : Set (Fin n → ComplexMatrix2) :=
  ComplexMatrix2.compactProduct (groupKinds n)
def IsEntrywiseHolomorphic {n : ℕ} (O : Set (Fin n → ComplexMatrix2))
    (F : (Fin n → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  Coordinates.ComplexCoordinates.IsHolomorphicVia
    (Coordinates.ComplexCoordinates.productEquiv (matrixKinds n))
    Coordinates.ComplexCoordinates.matrixEquiv O F
def RestrictionStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ O : Set (Fin n → ComplexMatrix2), IsOpen O →
    ∀ F : (Fin n → ComplexMatrix2) → ComplexMatrix2,
    IsEntrywiseHolomorphic O F →
    (∀ X ∈ O ∩ unimodularPow n, F X ∈ ComplexMatrix2.unitDeterminant) →
    (ComplexMatrix2.IsRelativelyOpen (unimodularPow n) (O ∩ unimodularPow n) ∧
      (∀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
        Coordinates.ComplexCoordinates.IsHolomorphicOnSL2Power b (O ∩ unimodularPow n) F) ∧
      ComplexMatrix2.IsHolomorphicBetween (groupKinds n) targetKind (O ∩ unimodularPow n)
        fun X _ => F X) ∧
    ∀ S : Set (Fin n → ComplexMatrix2), S ⊆ O ∩ unitaryPow n →
      ComplexMatrix2.IsRelativelyOpen (unitaryPow n) S →
      (∀ X ∈ S, F X ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) →
      ComplexMatrix2.IsRealAnalyticBetween (groupKinds n) targetKind S fun X _ => F X
end YangMills.Construction.Matrices.EntrywiseHolomorphy
