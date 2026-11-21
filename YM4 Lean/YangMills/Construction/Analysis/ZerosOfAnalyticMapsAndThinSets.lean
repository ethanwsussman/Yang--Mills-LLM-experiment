import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.Analysis
def VanishingFromRealPoints (q : ℕ) : Prop :=
  ∀ D : Set (YangMills.Construction.Coordinates.ComplexCoordinates q), IsOpen D → Convex ℝ D →
    (∀ z ∈ D, (fun j => ((z j).re : ℂ) : YangMills.Construction.Coordinates.ComplexCoordinates q) ∈ D) →
    ∀ f : YangMills.Construction.Coordinates.ComplexCoordinates q → ℂ,
      YangMills.Construction.Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) D (fun z _ => f z) →
    ∀ U : Set (YangMills.Construction.Coordinates.ComplexCoordinates q), U.Nonempty →
      U ⊆ D ∩ YangMills.Construction.Coordinates.ComplexCoordinates.realLocus q →
      YangMills.Construction.Matrices.ComplexMatrix2.IsRelativelyOpen
        (YangMills.Construction.Coordinates.ComplexCoordinates.realLocus q) U →
      (∀ x ∈ U, f x = 0) →
      ∀ z ∈ D, f z = 0
def VanishingOfRealAnalytic (q : ℕ) : Prop :=
  ∀ D : Set (YangMills.Construction.Coordinates.ComplexCoordinates q),
    YangMills.Construction.Matrices.ComplexMatrix2.IsRelativelyOpen
      (YangMills.Construction.Coordinates.ComplexCoordinates.realLocus q) D → IsConnected D →
    ∀ f : YangMills.Construction.Coordinates.ComplexCoordinates q → ℂ,
      YangMills.Construction.Coordinates.ComplexCoordinates.IsRealAnalyticIn (N' := 1) D (fun z _ => f z) →
    ∀ W : Set (YangMills.Construction.Coordinates.ComplexCoordinates q), W.Nonempty →
      YangMills.Construction.Matrices.ComplexMatrix2.IsRelativelyOpen D W → (∀ x ∈ W, f x = 0) →
      ∀ x ∈ D, f x = 0
def NowhereDenseClosedSets (q : ℕ) : Prop :=
  (∀ P : MvPolynomial (Fin q) ℝ, P ≠ 0 →
    IsClosed {x : Fin q → ℝ | MvPolynomial.eval x P = 0} ∧
      interior {x : Fin q → ℝ | MvPolynomial.eval x P = 0} = ∅) ∧
  (∀ A : AffineSubspace ℝ (Fin q → ℝ), (A : Set (Fin q → ℝ)).Nonempty → A ≠ ⊤ →
    IsClosed (A : Set (Fin q → ℝ)) ∧ interior (A : Set (Fin q → ℝ)) = ∅) ∧
  (∀ (n : ℕ) (S : Fin n → Set (Fin q → ℝ)),
    (∀ i, IsClosed (S i)) → (∀ i, interior (S i) = ∅) →
      IsClosed (⋃ i, S i) ∧ interior (⋃ i, S i) = ∅ ∧
        IsOpen (⋃ i, S i)ᶜ ∧ Dense (⋃ i, S i)ᶜ)
def ComplementOfCodimTwoSubspaces (q : ℕ) : Prop :=
  2 ≤ q → ∀ (n : ℕ), 1 ≤ n → ∀ A : Fin n → AffineSubspace ℝ (Fin q → ℝ),
    (∀ i, (A i : Set (Fin q → ℝ)).Nonempty) →
    (∀ i, Module.finrank ℝ (A i).direction + 2 ≤ q) →
      IsOpen (⋃ i, (A i : Set (Fin q → ℝ)))ᶜ ∧ Dense (⋃ i, (A i : Set (Fin q → ℝ)))ᶜ ∧
        IsConnected (⋃ i, (A i : Set (Fin q → ℝ)))ᶜ
def ZerosOfAnalyticMapsAndThinSets : Prop :=
  ∀ q : ℕ, 1 ≤ q →
    VanishingFromRealPoints q ∧ VanishingOfRealAnalytic q ∧ NowhereDenseClosedSets q ∧
      ComplementOfCodimTwoSubspaces q
end YangMills.Construction.Analysis
end
