import YangMills.Construction.InfiniteLattice.BondsAndTheirVariablesProof
import YangMills.Construction.InfiniteLattice.PeriodsFoldCompactnessAndLimitsOfToriProof
import YangMills.Construction.InfiniteLattice.RationalPolynomialsAndTheBorelSetsOfTheStates
import YangMills.Construction.InfiniteLattice.RegularConditionalProbabilitiesGivenTheInvariantField
import YangMills.Construction.InfiniteLattice.SumsIntegralsAndImageMeasuresOfTheStatesAreFormedProof
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice.Disintegration
variable {a : ℝ}
theorem shiftInvariantSigma_le :
    shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
  fun _ hs => hs.1
theorem isClosed_gaugeFieldSet :
    IsClosed {U : Link a → Matrices.ComplexMatrix2.specialUnitary |
      ∀ l, U l.opposite = (U l)⁻¹} := by apply _root_.YangMills.Construction.CutoffLinks.LinksAndTheirVariables.isClosed_setOf_opposite_eq_inv <;> assumption
theorem polishSpace_specialUnitary : PolishSpace Matrices.ComplexMatrix2.specialUnitary := by
  have : PolishSpace Matrices.ComplexMatrix2 := inferInstanceAs (PolishSpace (Fin 2 → Fin 2 → ℂ))
  have hclosed : IsClosed (Matrices.ComplexMatrix2.specialUnitary : Set Matrices.ComplexMatrix2) :=
    (isCompact_iff_compactSpace.mpr
      (inferInstance : CompactSpace Matrices.ComplexMatrix2.specialUnitary)).isClosed
  exact hclosed.polishSpace
theorem standardBorelSpace_gaugeField : StandardBorelSpace (GaugeField a) := by
  have : Countable (Link a) := GibbsAtFixedSpacing.instCountableLink
  have := polishSpace_specialUnitary
  have : PolishSpace (GaugeField a) := (isClosed_gaugeFieldSet (a := a)).polishSpace
  infer_instance
theorem integrable_of_isBoundedObservable {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (μ : Measure (GaugeField a)) [IsFiniteMeasure μ] : Integrable F μ := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsFoldAndCompactness.integrable_of_isBoundedObservable <;> assumption
theorem isBoundedObservable_of_continuous {F : GaugeField a → ℂ} (hF : Continuous F) :
    IsBoundedObservable F := by apply _root_.YangMills.Construction.InfiniteLattice.WellDefinedStates.isBoundedObservable_of_continuous <;> assumption
theorem exists_isInvariantDisintegration (ν : GaugeFieldProbability a)
    (hν : IsShiftInvariant ν.1) : ∃ κ, IsInvariantDisintegration ν.1 κ := by
  have := ν.2
  have := standardBorelSpace_gaugeField (a := a)
  refine ⟨fun U => ⟨condExpKernel ν.1 (shiftInvariantSigma a) U, inferInstance⟩, ν.2, hν,
    fun F hF => ⟨?_, ?_⟩⟩
  · exact (hF.1.stronglyMeasurable.integral_condExpKernel (μ := ν.1)
      (m := shiftInvariantSigma a)).measurable
  · exact (condExp_ae_eq_integral_condExpKernel shiftInvariantSigma_le
      (integrable_of_isBoundedObservable hF ν.1)).symm
theorem measurable_of_isInvariantDisintegration
    (hDense : RatPolyDense a)
    (hGen : RatPolyGeneratesStateBorel a)
    {ν : Measure (GaugeField a)} {κ : GaugeField a → GaugeFieldProbability a}
    (hκ : IsInvariantDisintegration ν κ) : Measurable[shiftInvariantSigma a] κ := by
  have hgen : instMeasurableSpaceGaugeFieldProbability a =
      ⨆ F ∈ ratPolyObservables a,
        MeasurableSpace.comap (fun ρ : GaugeFieldProbability a => realExpectation ρ F)
          inferInstance := hGen.2.2.2.1
  rw [measurable_iff_comap_le, hgen, MeasurableSpace.comap_iSup]
  refine iSup_le fun F => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun hF => ?_
  rw [MeasurableSpace.comap_comp, ← measurable_iff_comap_le]
  have hobs : IsBoundedObservable fun U => (F U : ℂ) :=
    isBoundedObservable_of_continuous (hDense.2.1 F hF).1
  have hm := (hκ.2.2 _ hobs).1
  have heq : ((fun ρ : GaugeFieldProbability a => realExpectation ρ F) ∘ κ) =
      fun U => ((κ U).expect fun V => (F V : ℂ)).re := by
    funext U
    simp only [Function.comp, realExpectation, GaugeFieldProbability.expect,
      integral_complex_ofReal, Complex.ofReal_re]
  rw [heq]
  exact Complex.measurable_re.comp hm
theorem disintegrationImageProperties_of (hDense : RatPolyDense a)
    (hGen : RatPolyGeneratesStateBorel a)
    {ν : GaugeFieldProbability a} {κ : GaugeField a → GaugeFieldProbability a}
    (hκ : IsInvariantDisintegration ν.1 κ) :
    DisintegrationImageProperties ν κ := by
  have := ν.2
  have hκI : Measurable[shiftInvariantSigma a] κ :=
    measurable_of_isInvariantDisintegration hDense hGen hκ
  have hκm : Measurable κ := hκI.mono shiftInvariantSigma_le le_rfl
  have hmap : ∀ Φ : GaugeFieldProbability a → ℂ, Measurable Φ →
      ∫ ρ, Φ ρ ∂(disintegrationImage ν.1 κ) = ∫ U, Φ (κ U) ∂ν.1 := fun Φ hΦ =>
    integral_map hκm.aemeasurable hΦ.aestronglyMeasurable
  refine ⟨fun E hE => hκI hE, hκm, fun Φ hΦ _ => ⟨hΦ.comp hκI, hmap Φ hΦ⟩,
    fun Φ hΦ => ⟨hΦ.comp hκI, lintegral_map hΦ hκm⟩, fun F hF => ?_⟩
  rw [hmap _ (hGen.2.2.2.2 F hF)]
  calc ∫ U, (κ U).expect F ∂ν.1 = ∫ U, condExpShiftInvariant ν.1 F U ∂ν.1 :=
        integral_congr_ae (hκ.2.2 F hF).2
    _ = ν.expect F := integral_condExp shiftInvariantSigma_le
theorem ofReal_norm_sub_sq_expand (z c : ℂ) :
    ((‖z - c‖ ^ 2 : ℝ) : ℂ) =
      ((‖z‖ ^ 2 : ℝ) : ℂ) - conj c * z - c * conj z + ((‖c‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  rw [← Complex.mul_conj', ← Complex.mul_conj', ← Complex.mul_conj', map_sub]
  ring
theorem disintegrationFixesInvariantObservables_of {ν : GaugeFieldProbability a}
    {κ : GaugeField a → GaugeFieldProbability a}
    (hκ : IsInvariantDisintegration ν.1 κ) :
    DisintegrationFixesInvariantObservables ν κ := by
  intro J hJ hJI
  have := ν.2
  have version : ∀ G : GaugeField a → ℂ, IsBoundedObservable G →
      Measurable[shiftInvariantSigma a] G →
      ∀ᵐ U ∂ν.1, (κ U).expect G = G U := fun G hG hGI => by
    have e1 := (hκ.2.2 G hG).2
    have e2 : condExpShiftInvariant ν.1 G = G :=
      condExp_of_stronglyMeasurable shiftInvariantSigma_le hGI.stronglyMeasurable
        (integrable_of_isBoundedObservable hG ν.1)
    rw [e2] at e1
    exact e1.mono fun U hU => hU
  obtain ⟨C, hC⟩ := hJ.2
  have hconj : Continuous fun z : ℂ => conj z := Complex.continuous_conj
  have hsq : Continuous fun z : ℂ => ((‖z‖ ^ 2 : ℝ) : ℂ) := by fun_prop
  have hH : IsBoundedObservable fun V => conj (J V) :=
    ⟨hconj.measurable.comp hJ.1, C, fun U => by simpa using hC U⟩
  have hS : IsBoundedObservable fun V => ((‖J V‖ ^ 2 : ℝ) : ℂ) := by
    refine ⟨hsq.measurable.comp hJ.1, C ^ 2, fun U => ?_⟩
    have n0 : 0 ≤ ‖J U‖ := norm_nonneg _
    have n1 := hC U
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    nlinarith
  filter_upwards [version J hJ hJI, version _ hH (hconj.measurable.comp hJI),
    version _ hS (hsq.measurable.comp hJI)] with U e1 e2 e3
  refine ⟨e1, ?_⟩
  have := (κ U).2
  have iJ := integrable_of_isBoundedObservable hJ (κ U).1
  have iH := integrable_of_isBoundedObservable hH (κ U).1
  have iS := integrable_of_isBoundedObservable hS (κ U).1
  simp only [GaugeFieldProbability.expect] at e1 e2 e3 ⊢
  simp only [ofReal_norm_sub_sq_expand]
  have i1 : Integrable (fun V => ((‖J V‖ ^ 2 : ℝ) : ℂ) - conj (J U) * J V) (κ U).1 :=
    iS.sub (iJ.const_mul _)
  have i2 : Integrable (fun V => ((‖J V‖ ^ 2 : ℝ) : ℂ) - conj (J U) * J V -
      J U * conj (J V)) (κ U).1 := i1.sub (iH.const_mul _)
  rw [integral_add i2 (integrable_const _), integral_sub i1 (iH.const_mul _),
    integral_sub iS (iJ.const_mul _), integral_const_mul, integral_const_mul, e1, e2, e3,
    integral_const]
  simp only [probReal_univ, one_smul]
  push_cast
  rw [← Complex.mul_conj']
  ring
theorem invariantDisintegrationTheorem_holds (hRat : RatPolyAndStateBorelSets) :
    InvariantDisintegrationTheorem := by
  intro s ν hν
  obtain ⟨hDense, -, hGen, -⟩ := hRat s.L s.K s.isAdmissible.1
    s.isAdmissible.2 s.K.pos
  exact ⟨exists_isInvariantDisintegration ν hν, fun κ hκ =>
    ⟨disintegrationImageProperties_of hDense hGen hκ,
      disintegrationFixesInvariantObservables_of hκ⟩⟩
end YangMills.Construction.InfiniteLattice.Disintegration
