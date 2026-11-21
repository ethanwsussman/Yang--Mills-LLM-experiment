import YangMills.Construction.Matrices.SpecialUnitaryScalarVectorParts
import YangMills.Construction.PowerSeries.ConvergentSeries
import YangMills.Construction.Towers.DilationNearTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace AnalyticNearField
variable {L n k j j' : ℕ}
def relPreimage (W : Set (Edge L n k j → Matrices.ComplexMatrix2))
    (p : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2)
    (W' : Set (Edge L n k j' → Matrices.ComplexMatrix2)) : Set (Edge L n k j → Matrices.ComplexMatrix2) :=
  {V | V ∈ W ∧ p V ∈ W'}
def pauliBasisForm (e : PositiveEdge L n k j) (a : Fin 3) : Edge L n k j → Matrices.ComplexMatrix2 :=
  open Classical in edgeFormOfPositiveValues fun e' => if e' = e then Matrices.ComplexMatrix2.pauliFamily a else 0
def formOfCoeffs (x : PositiveEdge L n k j × Fin 3 → ℝ) : Edge L n k j → Matrices.ComplexMatrix2 :=
  ∑ᶠ i, x i • pauliBasisForm i.1 i.2
def formOfCoords {N : ℕ} (ν : PositiveEdge L n k j × Fin 3 ≃ Fin N) (y : Fin N → ℝ) :
    Edge L n k j → Matrices.ComplexMatrix2 :=
  formOfCoeffs (y ∘ ν)
def IsZeroNhd (O : Set (Edge L n k j → Matrices.ComplexMatrix2)) : Prop :=
  Matrices.ComplexMatrix2.IsRelativelyOpen (edgeFormSpace L n k j : Set (Edge L n k j → Matrices.ComplexMatrix2)) O ∧ 0 ∈ O
def coordRegion {N : ℕ} (ν : PositiveEdge L n k j × Fin 3 ≃ Fin N)
    (O : Set (Edge L n k j → Matrices.ComplexMatrix2)) : Set (Fin N → ℝ) :=
  {y | formOfCoords ν y ∈ O}
def IsAnalyticSmoothOn {N : ℕ} (D : Set (Fin N → ℝ)) (f : (Fin N → ℝ) → ℂ) : Prop :=
  Coordinates.ComplexCoordinates.IsRealAnalyticIn (N' := 1) (PowerSeries.RealSeries.realEmbed '' D)
    (fun z _ => f fun i => (z i).re) ∧ ContDiffOn ℝ ∞ f D
def CompositionAndExpTwist : Prop :=
  ∀ L n k j j' j'' : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k → j' ≤ k → j'' ≤ k →
    (∀ (W : Set (Edge L n k j → Matrices.ComplexMatrix2)) (W' : Set (Edge L n k j' → Matrices.ComplexMatrix2))
        (p : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2),
        IsAnalyticFieldMap W p →
          (∀ F : (Edge L n k j' → Matrices.ComplexMatrix2) → ℂ, IsAnalyticComplexFieldFunction W' F →
            IsOpenFieldSet PeriodicLattice.compactGaugeGroup (relPreimage W p W') ∧
              IsAnalyticComplexFieldFunction (relPreimage W p W') (F ∘ p)) ∧
          ∀ F : (Edge L n k j' → Matrices.ComplexMatrix2) → Edge L n k j'' → Matrices.ComplexMatrix2,
            IsAnalyticFieldMap W' F →
            IsOpenFieldSet PeriodicLattice.compactGaugeGroup (relPreimage W p W') ∧
              IsAnalyticFieldMap (relPreimage W p W') (F ∘ p)) ∧
    ∀ (U : Edge L n k j → Matrices.ComplexMatrix2) (Nb : Set (Edge L n k j → Matrices.ComplexMatrix2)),
      U ∈ fieldSpace L n k j → U ∈ Nb →
        (∀ F : (Edge L n k j → Matrices.ComplexMatrix2) → ℂ, IsAnalyticComplexFieldFunction Nb F →
          ∃ O : Set (Edge L n k j → Matrices.ComplexMatrix2), IsZeroNhd O ∧
            (∀ C ∈ O, PeriodicLattice.expTwist C U ∈ Nb) ∧
            ∀ (N : ℕ) (ν : PositiveEdge L n k j × Fin 3 ≃ Fin N),
              IsAnalyticSmoothOn (coordRegion ν O)
                fun y => F (PeriodicLattice.expTwist (formOfCoords ν y) U)) ∧
        ∀ F : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2,
          IsAnalyticFieldMap Nb F →
          ∃ O : Set (Edge L n k j → Matrices.ComplexMatrix2), IsZeroNhd O ∧
            (∀ C ∈ O, PeriodicLattice.expTwist C U ∈ Nb) ∧
            ∀ (N : ℕ) (ν : PositiveEdge L n k j × Fin 3 ≃ Fin N) (e : Edge L n k j') (r s : Fin 2),
              IsAnalyticSmoothOn (coordRegion ν O)
                fun y => F (PeriodicLattice.expTwist (formOfCoords ν y) U) e r s
end AnalyticNearField
end Tower
end YangMills.Construction
end
