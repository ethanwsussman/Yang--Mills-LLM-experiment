import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace GibbsAtFixedSpacing.SpacesOfFieldsAndMeasures
def GaugeFieldsCompactMetrizable (a : ℝ) : Prop :=
  IsClosed {U : Link a → Matrices.ComplexMatrix2.specialUnitary | ∀ l, U l.opposite = (U l)⁻¹} ∧
    CompactSpace (GaugeField a) ∧ TopologicalSpace.MetrizableSpace (GaugeField a)
def IsSupNormDense {a : ℝ} (D : Set (GaugeField a → ℂ)) : Prop :=
  ∀ F ∈ continuousFns a, ∀ ε : ℝ, 0 < ε → ∃ H ∈ D, observableSupNorm (F - H) < ε
def LocalFnsDenseStarSubalgebra (a : ℝ) : Prop :=
  continuousLocal a ⊆ continuousFns a ∧
  (∃ A : Subalgebra ℂ (GaugeField a → ℂ),
    (A : Set (GaugeField a → ℂ)) = continuousLocal a) ∧
  (∀ z : ℂ, (fun _ => z) ∈ continuousLocal a) ∧
  (∀ F ∈ continuousLocal a, (fun U => starRingEnd ℂ (F U)) ∈ continuousLocal a) ∧
  (∀ U U' : GaugeField a, U ≠ U' → ∃ F ∈ continuousLocal a, F U ≠ F U') ∧
  IsSupNormDense (continuousLocal a)
def ProbCompactMetrizable (a : ℝ) : Prop :=
  CompactSpace (BorelProb a) ∧ TopologicalSpace.MetrizableSpace (BorelProb a)
def LocalFnsSeparateProb (a : ℝ) : Prop :=
  ∀ ν ν' : BorelProb a,
    (∀ F ∈ continuousLocal a, ν.integral F = ν'.integral F) → ν = ν'
def LocalFnsSeparable (a : ℝ) : Prop :=
  ∃ D : Set (GaugeField a → ℂ), D ⊆ continuousLocal a ∧ D.Countable ∧ IsSupNormDense D
def FieldAndMeasureSpaceProperties : Prop :=
  ∀ a : ℝ, 0 < a →
    GaugeFieldsCompactMetrizable a ∧ LocalFnsDenseStarSubalgebra a ∧
      ProbCompactMetrizable a ∧ LocalFnsSeparateProb a ∧ LocalFnsSeparable a
end GibbsAtFixedSpacing.SpacesOfFieldsAndMeasures
end YangMills.Construction
