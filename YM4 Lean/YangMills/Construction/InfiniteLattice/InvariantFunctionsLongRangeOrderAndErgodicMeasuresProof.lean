import YangMills.Construction.InfiniteLattice.ConditionalExpectationGivenTheInvariantFieldProof
import YangMills.Construction.InfiniteLattice.InvariantFunctionsLongRangeOrderAndErgodicMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory InfiniteLattice Filter
open scoped ComplexConjugate
namespace LatticePhases
namespace InvariantErgodic
variable {a : ℝ}
theorem shiftInvariantMeasurable_fixed {J : GaugeField a → ℂ}
    (hJ : Measurable[shiftInvariantSigma a] J) (v : LatticePoint a) :
    (shift v).actOn J = J := by
  funext U
  have hInv : IsShiftInvariantSet (J ⁻¹' {J U}) := hJ (measurableSet_singleton (J U))
  have hPre := ((shift v).actOn_indicator_eq_iff _).mp (hInv.2 v)
  exact show U ∈ (shift v).pullbackField ⁻¹' (J ⁻¹' {J U}) from by
    rw [hPre]
    rfl
theorem condExpRepresentative_integrable {ρ : Measure (GaugeField a)} {A Y : GaugeField a → ℂ}
    (hY : IsIntegrableCondExpRepresentative ρ A Y) : Integrable Y ρ := by apply _root_.YangMills.Construction.LatticePhases.CondExpInvariant.integrable_of_isCondExpVersion <;> assumption
theorem varianceOf_eq_sub {ρ : Measure (GaugeField a)} [IsProbabilityMeasure ρ]
    {Y : GaugeField a → ℂ} (hY : Integrable Y ρ)
    (hYY : Integrable (fun U => conj (Y U) * Y U) ρ) :
    ((varianceOf ρ Y : ℝ) : ℂ) =
      ∫ U, conj (Y U) * Y U ∂ρ - ((‖∫ U, Y U ∂ρ‖ ^ 2 : ℝ) : ℂ) := by
  set μY : ℂ := ∫ U, Y U ∂ρ with hμY
  have hYc : Integrable (fun U => conj (Y U)) ρ :=
    hY.mono (Complex.continuous_conj.comp_aestronglyMeasurable hY.1)
      (ae_of_all _ fun U => by simp)
  have hNormSq : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = conj z * z := fun z => by
    rw [Complex.conj_mul']
    push_cast
    rfl
  have hPoint : ∀ U, ((‖Y U - μY‖ ^ 2 : ℝ) : ℂ) =
      conj (Y U) * Y U - conj μY * Y U - μY * conj (Y U) + conj μY * μY := fun U => by
    rw [hNormSq, map_sub]
    ring
  have hInt : ∫ U, ((‖Y U - μY‖ ^ 2 : ℝ) : ℂ) ∂ρ =
      ∫ U, conj (Y U) * Y U ∂ρ - conj μY * μY - μY * conj μY + conj μY * μY := by
    simp_rw [hPoint]
    have h₁ : Integrable (fun U => conj (Y U) * Y U - conj μY * Y U) ρ :=
      hYY.sub (hY.const_mul _)
    have h₂ : Integrable (fun U => conj (Y U) * Y U - conj μY * Y U - μY * conj (Y U)) ρ :=
      h₁.sub (hYc.const_mul _)
    rw [integral_add h₂ (integrable_const _), integral_sub h₁ (hYc.const_mul _),
      integral_sub hYY (hY.const_mul _), integral_const_mul, integral_const_mul, integral_conj,
      integral_const]
    simp [hμY]
  unfold varianceOf
  rw [← hμY, ← integral_complex_ofReal, hInt, hNormSq μY]
  ring
theorem varianceOf_nonneg (ρ : Measure (GaugeField a)) (Y : GaugeField a → ℂ) :
    0 ≤ varianceOf ρ Y :=
  integral_nonneg fun _ => by positivity
theorem ae_eq_const_of_zeroOne {ρ : Measure (GaugeField a)} [IsProbabilityMeasure ρ]
    (h01 : ∀ S : Set (GaugeField a), MeasurableSet[shiftInvariantSigma a] S → ρ S = 0 ∨ ρ S = 1)
    {J : GaugeField a → ℂ} (hJ : Measurable[shiftInvariantSigma a] J) :
    ∃ c : ℂ, ∀ᵐ U ∂ρ, J U = c := by
  obtain ⟨c, hc⟩ := exists_eventuallyEq_const_of_forall_separating (l := ae ρ) (f := J)
    (MeasurableSet (α := ℂ)) (fun C hC => by
      have hInv : MeasurableSet[shiftInvariantSigma a] (J ⁻¹' C) := hJ hC
      have hBorel : MeasurableSet (J ⁻¹' C) := (show IsShiftInvariantSet (J ⁻¹' C) from hInv).1
      rcases h01 _ hInv with h | h
      · right
        exact ae_iff.mpr (by simp only [not_not]; exact h)
      · left
        exact (mem_ae_iff_prob_eq_one hBorel).mpr h)
  exact ⟨c, hc⟩
theorem condExpRepresentative_ae_eq_mean {ρ : Measure (GaugeField a)} [IsProbabilityMeasure ρ]
    (h01 : ∀ S : Set (GaugeField a), MeasurableSet[shiftInvariantSigma a] S → ρ S = 0 ∨ ρ S = 1)
    {A Y : GaugeField a → ℂ} (hY : IsIntegrableCondExpRepresentative ρ A Y)
    (hMean : ∫ U, Y U ∂ρ = ∫ U, A U ∂ρ) : ∀ᵐ U ∂ρ, Y U = ∫ V, A V ∂ρ := by
  obtain ⟨c, hc⟩ := ae_eq_const_of_zeroOne h01 hY.1
  have hcMean : ∫ U, Y U ∂ρ = c := by
    rw [integral_congr_ae (show Y =ᵐ[ρ] fun _ => c from hc)]
    simp
  rw [← hMean, hcMean]
  exact hc
end InvariantErgodic
open InvariantErgodic CondExpInvariant in
theorem invariantFunctionsAndErgodicity_holds
    (hCondExp : CondExpInvariant.Claim) :
    InvariantFunctionsAndErgodicity := by
  intro D
  refine ⟨fun J hJ v => shiftInvariantMeasurable_fixed hJ v, ?_, ?_⟩
  · intro ρ hT A hA Y hY
    obtain ⟨-, -, hMeanAll, -, hPlateau⟩ := hCondExp D ρ.toMeasure hT A A hA hA
    have hMeanY := (hMeanAll Y hY).1
    obtain ⟨hYY, hPair⟩ := hPlateau.2.1 Y Y hY hY
    refine ⟨?_, varianceOf_nonneg _ _⟩
    rw [varianceOf_eq_sub (condExpRepresentative_integrable hY) hYY, hMeanY, hPair]
    rfl
  · intro ρ hErg
    obtain ⟨-, hT, h01⟩ := hErg
    refine ⟨fun J hJ => ?_, fun A B hA hB => ?_⟩
    · obtain ⟨c, hc⟩ := ae_eq_const_of_zeroOne h01 hJ
      exact ⟨c, (ρ.holdsAS_iff _).mpr hc⟩
    · have hAB := hCondExp D ρ.toMeasure hT A B hA hB
      have hBA := hCondExp D ρ.toMeasure hT B A hB hA
      have hAA := hCondExp D ρ.toMeasure hT A A hA hA
      have hVerA := hAB.1.2.1
      have hVerB := hBA.1.2.1
      have hAeA := condExpRepresentative_ae_eq_mean h01 hVerA (hAB.2.2.1 _ hVerA).1
      have hAeB := condExpRepresentative_ae_eq_mean h01 hVerB (hBA.2.2.1 _ hVerB).1
      have hPairConst : ∀ (F G : GaugeField D.mesh → ℂ),
          (∀ᵐ U ∂ρ.toMeasure, condExpShiftInvariant ρ.toMeasure F U = ρ.eval F) →
          (∀ᵐ U ∂ρ.toMeasure, condExpShiftInvariant ρ.toMeasure G U = ρ.eval G) →
          plateauPairing ρ.toMeasure F G = conj (ρ.eval F) * ρ.eval G := by
        intro F G hF hG
        unfold plateauPairing
        rw [integral_congr_ae (show
          (fun U => conj (condExpShiftInvariant ρ.toMeasure F U) *
            condExpShiftInvariant ρ.toMeasure G U) =ᵐ[ρ.toMeasure]
            fun _ => conj (ρ.eval F) * ρ.eval G by
          filter_upwards [hF, hG] with U h₁ h₂
          rw [h₁, h₂])]
        simp
      refine ⟨fun Y hY => ?_, hPairConst A B hAeA hAeB, ?_⟩
      · exact (ρ.holdsAS_iff _).mpr (condExpRepresentative_ae_eq_mean h01 hY (hAA.2.2.1 Y hY).1)
      · have hPairAA := hPairConst A A hAeA hAeA
        unfold plateauVariance
        rw [plateauForm_eq_plateauPairing, hPairAA]
        have hSq : conj (ρ.eval A) * ρ.eval A = ((‖∫ U, A U ∂ρ.toMeasure‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.conj_mul']
          push_cast
          rfl
        rw [hSq, sub_self]
end LatticePhases
end YangMills.Construction
end
