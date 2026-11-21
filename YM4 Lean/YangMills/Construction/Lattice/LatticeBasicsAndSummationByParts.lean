import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.ComponentFamiliesOfForms
import Mathlib
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def plaquetteFamilyExteriorDerivTranspose (ξ : ℝ) (U : Bond L m j → ComplexMatrix2)
    (F : PlaquetteFamily L m j) : AxisSiteFamily L m j :=
  fun μ x => ∑ ν ∈ Finset.univ.erase μ,
    covDerivTranspose ξ U ν (plaquetteFamilyComponent F ν μ) x
namespace LatticeBasics
def SiteFacts (L m : ℕ) (j : ℤ) : Prop :=
  (∀ (x : Site L m j) (n : Fin 4 → ℤ),
    shiftedPoint x n ∈ sublattice L m j ∧
      (shiftedPoint x n = (x : FourTorus L m) ↔
        ∃ k : Fin 4 → ℤ, n = (gridSideLength L m j : ℤ) • k)) ∧
  Nat.card (Site L m j) = gridSideLength L m j ^ 4 ∧
  2 ≤ gridSideLength L m j ∧
  ∀ n : Fin 4 → ℤ, ∃ φ : Site L m j → Site L m j,
    Function.Bijective φ ∧ ∀ x, (φ x : FourTorus L m) = shiftedPoint x n
def BondFacts (L m : ℕ) (j : ℤ) : Prop :=
  (∀ (μ : Fin 4) (x : Site L m j), (Bond.forwardFrom x μ).IsPositivelyOriented) ∧
  (∀ b : Bond L m j, b.IsPositivelyOriented →
    ∃! p : Fin 4 × Site L m j, Bond.forwardFrom p.2 p.1 = b) ∧
  (∀ b : Bond L m j, b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented) ∧
  (∀ b : Bond L m j, (b.IsPositivelyOriented ∧ b.opposite.IsPositivelyOriented) ↔
    ∃ μ ν : Fin 4, b.target = b.source + unitStep L m j μ ∧ b.source = b.target + unitStep L m j ν) ∧
  ∀ b : Bond L m j, b.opposite.opposite = b
def TraceFacts : Prop :=
  (∀ T : ComplexMatrix2, IsUnit T →
    (∀ X : ComplexMatrix2, ComplexMatrix2.fullTrace (T * X * T⁻¹) = ComplexMatrix2.fullTrace X) ∧
    (∀ X Y : ComplexMatrix2, ComplexMatrix2.fullTrace (X * ComplexMatrix2.conjugateBy T Y) =
      ComplexMatrix2.fullTrace (ComplexMatrix2.conjugateBy T⁻¹ X * Y)) ∧
    (∀ X : ComplexMatrix2, ComplexMatrix2.conjugateBy T⁻¹ X = T⁻¹ * X * T) ∧
    Function.LeftInverse (ComplexMatrix2.conjugateBy T⁻¹) (ComplexMatrix2.conjugateBy T) ∧
    Function.RightInverse (ComplexMatrix2.conjugateBy T⁻¹) (ComplexMatrix2.conjugateBy T) ∧
    IsLinearMap ℂ (ComplexMatrix2.conjugateBy T) ∧
    IsLinearMap ℂ (ComplexMatrix2.conjugateBy T⁻¹) ∧
    (∀ X ∈ ComplexMatrix2.traceless, ComplexMatrix2.conjugateBy T X ∈ ComplexMatrix2.traceless ∧
      ComplexMatrix2.conjugateBy T⁻¹ X ∈ ComplexMatrix2.traceless)) ∧
  (∀ X : ComplexMatrix2, (∀ Y : ComplexMatrix2, ComplexMatrix2.fullTrace (X * Y) = 0) → X = 0) ∧
  ∀ X ∈ ComplexMatrix2.traceless,
    (∀ Y ∈ ComplexMatrix2.traceless, ComplexMatrix2.fullTrace (X * Y) = 0) → X = 0
def TraceFormNondegenerateOnFamilies : Prop :=
  ∀ V : Submodule ℂ ComplexMatrix2, V = ComplexMatrix2.traceless ∨ V = ⊤ →
    ∀ (I : Type) [Fintype I] (f : I → ComplexMatrix2), (∀ ι, f ι ∈ V) →
      (∀ g : I → ComplexMatrix2, (∀ ι, g ι ∈ V) →
        ∑ ι, ComplexMatrix2.fullTrace (f ι * g ι) = 0) → f = 0
def SummationByParts (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) : Prop :=
  ∀ (f g : Site L m j → ComplexMatrix2) (ν : Fin 4),
    ∑ᶠ x : Site L m j, ComplexMatrix2.fullTrace (f x * covDeriv ξ U ν g x) =
      ∑ᶠ x : Site L m j, ComplexMatrix2.fullTrace (covDerivTranspose ξ U ν f x * g x)
def PlaquetteTransposeFacts (ξ : ℝ) (U : Bond L m j → ComplexMatrix2) : Prop :=
  (∀ (F : PlaquetteFamily L m j) (μ : Fin 4) (x : Site L m j),
    plaquetteFamilyExteriorDerivTranspose ξ U F μ x =
      ((ξ⁻¹ : ℝ) : ℂ) • ∑ ν ∈ Finset.univ.erase μ,
        (plaquetteFamilyComponent F μ ν x -
          ComplexMatrix2.conjugateBy (U (Bond.forwardFrom (x - unitStep L m j ν) ν))⁻¹
            (plaquetteFamilyComponent F μ ν (x - unitStep L m j ν)))) ∧
  IsLinearMap ℂ (plaquetteFamilyExteriorDerivTranspose ξ U) ∧
  ∀ (F : PlaquetteFamily L m j) (A : AxisSiteFamily L m j),
    plaquetteFamilyInner ξ F (plaquetteFamilyExteriorDeriv ξ U A) =
      axisFamilyInner ξ (plaquetteFamilyExteriorDerivTranspose ξ U F) A
def Conclusion : Prop :=
  ∀ (L m : ℕ) (j : ℤ) (ξ : ℝ) (U : Bond L m j → ComplexMatrix2),
    Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    -(m : ℤ) ≤ j → 0 < ξ → IsGaugeField complexGaugeGroup Set.univ U →
    SiteFacts L m j ∧ BondFacts L m j ∧ TraceFacts ∧ TraceFormNondegenerateOnFamilies ∧
      SummationByParts ξ U ∧ PlaquetteTransposeFacts ξ U
end LatticeBasics
end PeriodicLattice
end YangMills.Construction
end
