import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
section
variable {L m k i : ℕ}
def IsAnalyticComplexFieldFunction (U : Set (Edge L m k i → Matrices.ComplexMatrix2))
    (F : (Edge L m k i → Matrices.ComplexMatrix2) → ℂ) : Prop :=
  IsOpenFieldSet PeriodicLattice.compactGaugeGroup U ∧ ∃ _ : Fintype (PositiveEdge L m k i),
    Matrices.GroupLieProduct.Subspaces.IsSubspaceAnalyticToCoords (R := PositiveEdge L m k i)
      (S := Empty) (l := 1) ⊥
      {q | fieldOfPositiveValues (Matrices.GroupLieProduct.Subspaces.groupComponent q) ∈ U}
      fun q _ => F (fieldOfPositiveValues (Matrices.GroupLieProduct.Subspaces.groupComponent q))
end
def PreservesOpenAndNhdsOfOne {ι ι' : Type} (P : Set (ι → Matrices.ComplexMatrix2))
    (P' : Set (ι' → Matrices.ComplexMatrix2))
    (c : (ι → Matrices.ComplexMatrix2) → ι' → Matrices.ComplexMatrix2) : Prop :=
  ∀ S ⊆ P, (Matrices.ComplexMatrix2.IsRelativelyOpen P S ↔
      Matrices.ComplexMatrix2.IsRelativelyOpen P' (c '' S)) ∧
    (EventuallyNearIdentity P (· ∈ S) ↔ EventuallyNearIdentity P' (· ∈ c '' S))
section
variable {L m k j : ℕ}
def ScalingPreservesFieldsAndForms (hL : 0 < L) (hj : j ≤ k) (i : ℕ) : Prop :=
  BijOn (transportTotal (scaleEdge (n := m) hL hj i)) (fieldSpace L m k i)
      (fieldSpace L (scaledExponent m k j) j i) ∧
    transportTotal (scaleEdge (n := m) hL hj i) (trivialField L m k i) =
      trivialField L (scaledExponent m k j) j i ∧
    (∃ T : edgeFormSpace L m k i ≃ₗ[ℝ]
        Matrices.GroupLieProduct.hermitianTracelessFunctions
          (PositiveEdge L (scaledExponent m k j) j i),
      ∀ B : edgeFormSpace L m k i,
        (T B : PositiveEdge L (scaledExponent m k j) j i → Matrices.ComplexMatrix2) =
          restrictToPositiveEdges (transportTotal (scaleEdge hL hj i)
            (B : Edge L m k i → Matrices.ComplexMatrix2))) ∧
    (∃ T : edgeFormSpace L m k i ≃ₗ[ℝ] edgeFormSpace L (scaledExponent m k j) j i,
      ∀ B : edgeFormSpace L m k i,
        (T B : Edge L (scaledExponent m k j) j i → Matrices.ComplexMatrix2) =
          transportTotal (scaleEdge hL hj i) (B : Edge L m k i → Matrices.ComplexMatrix2)) ∧
    (∀ B ∈ edgeFormSpace L m k i, ∀ B' ∈ edgeFormSpace L m k i,
      edgeFormPairing (transportTotal (scaleEdge hL hj i) B)
        (transportTotal (scaleEdge hL hj i) B') = edgeFormPairing B B') ∧
    ∀ V ∈ fieldSpace L m k i, ∀ B ∈ edgeFormSpace L m k i,
      transportTotal (scaleEdge hL hj i) (PeriodicLattice.expTwist B V) =
        PeriodicLattice.expTwist (transportTotal (scaleEdge hL hj i) B)
          (transportTotal (scaleEdge hL hj i) V)
def ScalingPreservesOpenSets (hL : 0 < L) (hj : j ≤ k) (i : ℕ) : Prop :=
  PreservesOpenAndNhdsOfOne (fieldSpace L m k i)
      (fieldSpace L (scaledExponent m k j) j i)
      (transportTotal (scaleEdge hL hj i)) ∧
    (∀ S ⊆ fieldSpace L m k i, IsOpenFieldSet PeriodicLattice.compactGaugeGroup S ↔
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup (transportTotal (scaleEdge hL hj i) '' S)) ∧
    MapsTo (transportTotal (scaleVertex (n := m) hL hj i).toEquiv) (gaugeGroupAt L m k i)
      (gaugeGroupAt L (scaledExponent m k j) j i) ∧
    PreservesOpenAndNhdsOfOne (gaugeGroupAt L m k i)
      (gaugeGroupAt L (scaledExponent m k j) j i)
      (transportTotal (scaleVertex hL hj i).toEquiv)
def ScalingPreservesAnalyticity (hL : 0 < L) (hj : j ≤ k) (i i' : ℕ) : Prop :=
  ∀ D : Set (Edge L m k i → Matrices.ComplexMatrix2),
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup D →
    (∀ F : (Edge L m k i → Matrices.ComplexMatrix2) → ℝ, IsAnalyticFieldFunction D F ↔
      IsAnalyticFieldFunction (transportTotal (scaleEdge hL hj i) '' D)
        (transportTotalScalar (scaleEdge hL hj i) F)) ∧
    (∀ F : (Edge L m k i → Matrices.ComplexMatrix2) → ℂ, IsAnalyticComplexFieldFunction D F ↔
      IsAnalyticComplexFieldFunction (transportTotal (scaleEdge hL hj i) '' D)
        (transportTotalScalar (scaleEdge hL hj i) F)) ∧
    ∀ φ : (Edge L m k i → Matrices.ComplexMatrix2) → Edge L m k i' → Matrices.ComplexMatrix2,
      MapsTo φ D (fieldSpace L m k i') →
      (IsAnalyticFieldMap D φ ↔
        IsAnalyticFieldMap (transportTotal (scaleEdge hL hj i) '' D)
          (transportTotalFunValued (scaleEdge hL hj i) (scaleEdge hL hj i') φ))
end
def ScalingNearTrivialField : Prop :=
  ∀ (L m k j i i' : ℕ) (hL : 0 < L) (hj : j ≤ k), Conventions.IsAdmissibleBlockingFactor L →
    0 < m → i ≤ j → i' ≤ j →
    ScalingPreservesFieldsAndForms (m := m) hL hj i ∧
      ScalingPreservesOpenSets (m := m) hL hj i ∧
      ScalingPreservesAnalyticity (m := m) hL hj i i'
end Tower
end YangMills.Construction
end
