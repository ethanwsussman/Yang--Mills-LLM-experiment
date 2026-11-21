import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def HaarIsLeftInvariantProbability : Prop :=
  (inferInstance : TopologicalSpace Matrices.ComplexMatrix2.specialUnitary) =
      TopologicalSpace.induced
        (fun g : Matrices.ComplexMatrix2.specialUnitary =>
          Coordinates.ComplexCoordinates.matrixEquiv (g : Matrices.ComplexMatrix2)) inferInstance ∧
    IsTopologicalGroup Matrices.ComplexMatrix2.specialUnitary ∧
    CompactSpace Matrices.ComplexMatrix2.specialUnitary ∧
    IsProbabilityMeasure Matrices.ComplexMatrix2.haarProb ∧
    ∀ (h : Matrices.ComplexMatrix2.specialUnitary) (E : Set Matrices.ComplexMatrix2.specialUnitary),
      MeasurableSet E →
        Matrices.ComplexMatrix2.haarProb ((fun g => h * g) ⁻¹' E) =
          Matrices.ComplexMatrix2.haarProb E
def HaarIsInversionAndTranslationInvariant : Prop :=
  ∀ E : Set Matrices.ComplexMatrix2.specialUnitary, MeasurableSet E →
    Matrices.ComplexMatrix2.haarProb ((fun g => g⁻¹) ⁻¹' E) = Matrices.ComplexMatrix2.haarProb E ∧
      (∀ h : Matrices.ComplexMatrix2.specialUnitary,
        Matrices.ComplexMatrix2.haarProb ((fun g => g * h) ⁻¹' E) =
          Matrices.ComplexMatrix2.haarProb E) ∧
      ∀ h h' : Matrices.ComplexMatrix2.specialUnitary,
        Matrices.ComplexMatrix2.haarProb ((fun g => h * g * h'⁻¹) ⁻¹' E) =
          Matrices.ComplexMatrix2.haarProb E
def GaugeTransformIsMeasurePreservingHomeomorph (L m K : ℕ)
    (u : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  ∃ Φ : gaugeFieldsAtLevel L m K 0 ≃ gaugeFieldsAtLevel L m K 0,
    (∀ U : gaugeFieldsAtLevel L m K 0, (Φ U).1 = gaugeTransform u U.1) ∧
    Continuous[gaugeFieldsAtLevelTopology L m K 0, gaugeFieldsAtLevelTopology L m K 0] Φ ∧
    Continuous[gaugeFieldsAtLevelTopology L m K 0, gaugeFieldsAtLevelTopology L m K 0] Φ.symm ∧
    ∀ E : Set (gaugeFieldsAtLevel L m K 0),
      MeasurableSet[@borel _ (gaugeFieldsAtLevelTopology L m K 0)] E →
        productHaarMeasure L m (levelDepth K 0) (Subtype.val '' (Φ ⁻¹' E)) =
          productHaarMeasure L m (levelDepth K 0) (Subtype.val '' E)
def IsBoundedBorelOnGaugeFields (L m K : ℕ)
    (F : (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) → ℝ) : Prop :=
  (∃ C : ℝ, ∀ U : gaugeFieldsAtLevel L m K 0, |F U.1| ≤ C) ∧
    @Measurable _ _ (@borel _ (gaugeFieldsAtLevelTopology L m K 0)) _
      fun U : gaugeFieldsAtLevel L m K 0 => F U.1
def HaarAndWilsonInvariance : Prop :=
  HaarIsLeftInvariantProbability ∧
    HaarIsInversionAndTranslationInvariant ∧
    ∀ (s : Conventions.StandingParameters) (u : SiteAtLevel s.L s.m s.K 0 → Matrices.ComplexMatrix2),
      IsGaugeMap compactGaugeGroup u →
        GaugeTransformIsMeasurePreservingHomeomorph s.L s.m s.K u ∧
          ∀ (β : ℝ), 0 < β → ∀ F : (BondAtLevel s.L s.m s.K 0 → Matrices.ComplexMatrix2) → ℝ,
            IsBoundedBorelOnGaugeFields s.L s.m s.K F →
              ∫ U, F (gaugeTransform u U) ∂(wilsonGibbsMeasure s.L s.m s.K β) =
                ∫ U, F U ∂(wilsonGibbsMeasure s.L s.m s.K β)
end YangMills.Construction.PeriodicLattice
end
