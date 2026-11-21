import YangMills.Construction.ComplexAnalysis.BanachValuedHolomorphy
import YangMills.Construction.SpectralTheory.FunctionsOfSelfAdjointOperators
import YangMills.Construction.SpectralTheory.ResolvedOperatorsAndTheirJointSpectralMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.ResolvedFacts
open HilbertSpaceBasics (UnboundedOp IsContraction)
open OperatorTransport (IsBoundedAdjoint IsContractionSemigroup IsUnitaryGroup IsUnitaryMap
  IsSelfAdjointUnbounded IsNonnegUnbounded conjOp)
open BorelSpectral SpectralTheorem
open SelfAdjointFunctions (fnCalc expI)
open ResolvedOps (IsDiagonalized expComplex)
def rightClosedHalfPlane : Set ℂ := {ζ | 0 ≤ ζ.re}
def rightOpenHalfPlane : Set (Coordinates.ComplexCoordinates 1) := {z | 0 < (z 0).re}
def realSpectralIntegral {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {n : ℕ} {Y : Set (Fin n → ℝ)} (E : SpectralMeasure Y H) (g : Y → ℝ) : UnboundedOp H :=
  spectralIntegralOp E fun y => ((g y : ℝ) : ℂ)
section
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def CoordIntegralSelfAdjointAndDetermines : Prop :=
  ∀ E : SpectralMeasure RealLineSet H,
    IsSelfAdjointUnbounded (spectralIntegralOp E coordVar) ∧
      ∀ E' : SpectralMeasure RealLineSet H,
        spectralIntegralOp E' coordVar = spectralIntegralOp E coordVar → E' = E
def NonnegIffNegHalfLineNull : Prop :=
  ∀ A : UnboundedOp H, IsDiagonalized A →
    (IsNonnegUnbounded A ↔
      spectralMeasure A (realLineSet negHalfLine) = 0)
def ExpIFormsUnitaryGroup : Prop :=
  ∀ B : UnboundedOp H, IsDiagonalized B →
    IsUnitaryGroup (fun s => (expI B s : H →ₗ[ℂ] H)) ∧
      ∀ s, IsBoundedAdjoint (expI B (-s)) (expI B s)
def ComplexExpOfNonneg : Prop :=
  ∀ A : UnboundedOp H, IsDiagonalized A → IsNonnegUnbounded A →
    (∀ ζ ∈ rightClosedHalfPlane, IsContraction (expComplex A ζ)) ∧
    (∀ ζ ∈ rightClosedHalfPlane, ∀ ζ' ∈ rightClosedHalfPlane,
      expComplex A ζ * expComplex A ζ' = expComplex A (ζ + ζ')) ∧
    (∀ ζ ∈ rightClosedHalfPlane, IsBoundedAdjoint (expComplex A (conj ζ)) (expComplex A ζ)) ∧
    expComplex A 0 = 1 ∧
    (∀ ψ : H, ContinuousOn (fun ζ => expComplex A ζ ψ) rightClosedHalfPlane) ∧
    IsContractionSemigroup (fun t : ℝ≥0 => expComplex A ((t : ℝ) : ℂ)) ∧
    BanachValued.IsOperatorHolomorphicOn rightOpenHalfPlane
      (fun z : Coordinates.ComplexCoordinates 1 => expComplex A (z 0))
def ExpDeterminesOp : Prop :=
  (∀ B B' : UnboundedOp H, IsDiagonalized B → IsDiagonalized B' →
    (∀ s, expI B s = expI B' s) → B = B') ∧
  ∀ A A' : UnboundedOp H, IsDiagonalized A → IsDiagonalized A' →
    IsNonnegUnbounded A → IsNonnegUnbounded A' →
    (∀ k : ℕ, expComplex A (k : ℂ) = expComplex A' (k : ℂ)) → A = A'
def RealIntegralsDiagonalized : Prop :=
  ∀ (n : ℕ) (Y : Set (Fin n → ℝ)) (E : SpectralMeasure Y H), Y.Nonempty →
    (∀ (g : Y → ℝ) (hg : Measurable g),
      IsDiagonalized (realSpectralIntegral E g) ∧
      spectralMeasure (realSpectralIntegral E g) = pushforwardToLine E g hg ∧
      ∀ u : ℝ → ℂ, Measurable u →
        fnCalc (realSpectralIntegral E g) u = spectralIntegralOp E fun y => u (g y)) ∧
    ∀ g g' : Y → ℝ, Measurable g → Measurable g' →
      ResolvedOps.StronglyCommute (realSpectralIntegral E g) (realSpectralIntegral E g')
def ConjOpDiagonalized (H' : Type*) [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] : Prop :=
  ∀ (A : UnboundedOp H) (V : H →ₗ[ℂ] H') (hV : IsUnitaryMap V), IsDiagonalized A →
    IsDiagonalized (conjOp hV A) ∧
    (∀ Δ, (spectralMeasure (conjOp hV A) Δ : H' →ₗ[ℂ] H') =
      (spectralMeasure A).unitaryPushforward hV Δ) ∧
    ∀ u : ℝ → ℂ, Measurable u →
      fnCalc (conjOp hV A) u = conjOp hV (fnCalc A u)
end
def DiagonalizedFacts : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    CoordIntegralSelfAdjointAndDetermines H ∧
    NonnegIffNegHalfLineNull H ∧
    ExpIFormsUnitaryGroup H ∧
    ComplexExpOfNonneg H ∧
    ExpDeterminesOp H ∧
    RealIntegralsDiagonalized H ∧
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'],
      ConjOpDiagonalized H H'
end YangMills.Construction.ResolvedFacts
