import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def IsAxisShiftInvariantSet (μ : Fin 4) (I : Set (GaugeField 1)) : Prop :=
  MeasurableSet I ∧
    (shift (axisStep 1 μ)).actOn (I.indicator (1 : GaugeField 1 → ℂ)) = I.indicator 1
@[reducible] def axisShiftInvariantSigma (μ : Fin 4) : MeasurableSpace (GaugeField 1) where
  MeasurableSet' := IsAxisShiftInvariantSet μ
  measurableSet_empty := ⟨MeasurableSet.empty,
    ((shift (axisStep 1 μ)).actOn_indicator_eq_iff ∅).mpr rfl⟩
  measurableSet_compl S hS := ⟨hS.1.compl,
    ((shift (axisStep 1 μ)).actOn_indicator_eq_iff Sᶜ).mpr (by
      rw [Set.preimage_compl,
        ((shift (axisStep 1 μ)).actOn_indicator_eq_iff S).mp hS.2])⟩
  measurableSet_iUnion g hg := ⟨MeasurableSet.iUnion fun i => (hg i).1,
    ((shift (axisStep 1 μ)).actOn_indicator_eq_iff (⋃ i, g i)).mpr (by
      rw [Set.preimage_iUnion]
      exact Set.iUnion_congr fun i =>
        ((shift (axisStep 1 μ)).actOn_indicator_eq_iff (g i)).mp (hg i).2)⟩
def IsCondExpOf (ν : Measure (GaugeField 1)) (𝓕 : MeasurableSpace (GaugeField 1))
    (B E : GaugeField 1 → ℂ) : Prop :=
  Measurable[𝓕] E ∧ Integrable E ν ∧
    ∀ I : Set (GaugeField 1), MeasurableSet[𝓕] I →
      ∫ U, I.indicator (1 : GaugeField 1 → ℂ) U * E U ∂ν =
        ∫ U, I.indicator (1 : GaugeField 1 → ℂ) U * B U ∂ν
def condExpGiven (ν : Measure (GaugeField 1))
    (𝓕 : MeasurableSpace (GaugeField 1)) (B : GaugeField 1 → ℂ) : GaugeField 1 → ℂ :=
  condExp 𝓕 ν B
theorem isCondExpRepresentative_condExpGiven (ν : Measure (GaugeField 1))
    [IsProbabilityMeasure ν] {𝓕 : MeasurableSpace (GaugeField 1)}
    (h𝓕 : 𝓕 ≤ borel (GaugeField 1))
    {B : GaugeField 1 → ℂ} (hB : Integrable B ν) :
    IsCondExpOf ν 𝓕 B (condExpGiven ν 𝓕 B) := by
  have hmul : ∀ (I : Set (GaugeField 1)) (g : GaugeField 1 → ℂ),
      (fun U => I.indicator (1 : GaugeField 1 → ℂ) U * g U) = I.indicator g := by
    intro I g
    funext U
    by_cases hU : U ∈ I <;> simp [hU]
  refine ⟨stronglyMeasurable_condExp.measurable, integrable_condExp, fun I hI => ?_⟩
  have hset := setIntegral_condExp h𝓕 hB hI
  rw [← integral_indicator (h𝓕 I hI), ← integral_indicator (h𝓕 I hI)] at hset
  rw [hmul, hmul]
  exact hset
def plateauUnitSpacing (ν : Measure (GaugeField 1)) (A B : GaugeField 1 → ℂ) : ℂ :=
  ∫ U, conj (condExpGiven ν (shiftInvariantSigma 1) A U) *
    condExpGiven ν (shiftInvariantSigma 1) B U ∂ν
end YangMills.Construction.InfiniteLattice
