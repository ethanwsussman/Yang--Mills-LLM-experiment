import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
variable {L n k i j : ℕ}
def HasSurjectiveDifferential
    (f : (Edge L n k i → Matrices.ComplexMatrix2) → Edge L n k j → Matrices.ComplexMatrix2)
    (U : Edge L n k i → Matrices.ComplexMatrix2) : Prop :=
  ∀ A' ∈ edgeFormSpace L n k j, ∃ A ∈ edgeFormSpace L n k i, leftDifferential f U A = A'
def IsAnalyticSubmersionNearIdentity
    (f : (Edge L n k i → Matrices.ComplexMatrix2) → Edge L n k j → Matrices.ComplexMatrix2) :
    Prop :=
  ∃ 𝒰 : Set (Edge L n k i → Matrices.ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
    IsDifferentiableFieldMap 𝒰 f ∧ IsAnalyticFieldMap 𝒰 f ∧
    ∀ U ∈ 𝒰, HasSurjectiveDifferential f U
def fibreWithin (𝒰 : Set (Edge L n k i → Matrices.ComplexMatrix2))
    (f : (Edge L n k i → Matrices.ComplexMatrix2) → Edge L n k j → Matrices.ComplexMatrix2)
    (W : Edge L n k j → Matrices.ComplexMatrix2) : Set (Edge L n k i → Matrices.ComplexMatrix2) :=
  {U | U ∈ 𝒰 ∧ f U = W}
def HasKernelTangentSpaces
    (f : (Edge L n k i → Matrices.ComplexMatrix2) → Edge L n k j → Matrices.ComplexMatrix2)
    (N : Set (Edge L n k i → Matrices.ComplexMatrix2)) : Prop :=
  ∀ U ∈ N, ∀ A : Edge L n k i → Matrices.ComplexMatrix2,
    A ∈ (fieldCurveData L n k i).tangentSpan N U ↔
      A ∈ edgeFormSpace L n k i ∧ leftDifferential f U A = 0
def HasSubmanifoldFibresNearIdentity
    (f : (Edge L n k i → Matrices.ComplexMatrix2) → Edge L n k j → Matrices.ComplexMatrix2) :
    Prop :=
  ∃ 𝒰 : Set (Edge L n k i → Matrices.ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
    IsDifferentiableFieldMap 𝒰 f ∧
    EventuallyNearIdentity (fieldSpace L n k j) fun W =>
      IsAnalyticFieldSubmanifold (fibreWithin 𝒰 f W) ∧
        HasKernelTangentSpaces f (fibreWithin 𝒰 f W)
def SmoothingFibres : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    (∀ A ∈ edgeFormSpace L n k 0,
      leftDifferential (smoothingIter L n k (i + 1)) (trivialField L n k 0) A =
        linearSmoothingIter L n k (i + 1) A) ∧
    EventuallyNearIdentity (fieldSpace L n k i)
      (HasSurjectiveDifferential (smoothingStep L n k i)) ∧
    EventuallyNearIdentity (fieldSpace L n k 0)
      (HasSurjectiveDifferential (smoothingIter L n k (i + 1))) ∧
    IsAnalyticSubmersionNearIdentity (smoothingStep L n k i) ∧
    IsAnalyticSubmersionNearIdentity (smoothingIter L n k (i + 1)) ∧
    HasSubmanifoldFibresNearIdentity (smoothingStep L n k i) ∧
    HasSubmanifoldFibresNearIdentity (smoothingIter L n k (i + 1))
end Tower
end YangMills.Construction
end
