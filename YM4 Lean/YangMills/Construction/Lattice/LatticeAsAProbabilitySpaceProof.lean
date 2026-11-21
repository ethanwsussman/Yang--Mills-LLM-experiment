import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionFacts
import YangMills.Construction.Lattice.LatticeAsAProbabilitySpace
import YangMills.Construction.Matrices.UnitaryLogarithmClosedForm
import YangMills.Construction.Probability.ExpectationBasicProperties
import YangMills.Construction.SystemOfAdmissibleConstants.TentsOfASmallSideProof
import YangMills.Construction.Torus.CellsOfATranslatedLatticeAndBallsOfTheTorusProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeProbability.ProbabilitySpaceProof
open YangMills.Construction.Probability (IsBoundedRealRV IsBoundedComplexRV)
instance instSecondCountableComplexMatrix2 : SecondCountableTopology Matrices.ComplexMatrix2 :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
section Carried
variable {X : Type*} [MeasurableSpace X] {S : Set X}
theorem integral_eq_integral_comap_subtype {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hS : MeasurableSet S) (ν : Measure X) (hnull : ν Sᶜ = 0) (G : X → E) :
    ∫ x, G x ∂ν = ∫ u : S, G u ∂(ν.comap Subtype.val) := by
  rw [integral_subtype_comap hS G, Measure.restrict_eq_self_of_ae_mem]
  exact measure_eq_zero_iff_ae_notMem.1 hnull |>.mono fun x hx => by simpa using hx
theorem comap_subtype_smul_withDensity (hS : MeasurableSet S) (ν : Measure X) (c : ℝ≥0∞)
    (φ : X → ℝ≥0∞) :
    (c • ν.withDensity φ).comap Subtype.val =
      c • (ν.comap (Subtype.val : S → X)).withDensity fun u => φ u := by
  ext A hA
  have hemb := MeasurableEmbedding.subtype_coe hS
  rw [hemb.comap_apply, Measure.smul_apply, Measure.smul_apply,
    withDensity_apply _ (hemb.measurableSet_image.2 hA), withDensity_apply _ hA,
    setLIntegral_subtype hS A φ]
end Carried
abbrev cutoffData (s : Conventions.StandingParameters) (β : ℝ) (hβ : 0 < β) :
    ReflectionPositivity.CutoffMirrors.MirrorData :=
  ⟨s, β, hβ, 0⟩
section Cutoff
variable {s : Conventions.StandingParameters} {β : ℝ} (hβ : 0 < β)
  (hA : ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies.Statement)
include hβ hA
theorem finite_plaq : Finite (Plaq s) :=
  (hA (cutoffData s β hβ)).1.2.2.1
theorem finite_bond : Finite (PeriodicLattice.Bond s.L s.m ((s.K : ℕ) : ℤ)) :=
  (hA (cutoffData s β hβ)).1.2.1
theorem productTopology_eq :
    (ReflectionPositivity.CutoffMirrors.MirrorData.productTopology (cutoffData s β hβ)) =
      (inferInstance : TopologicalSpace (GaugeConfig s)) :=
  (hA (cutoffData s β hβ)).1.2.2.2.2.2.2.1
theorem gaugeConfig_measurableSpace_eq_borel :
    (inferInstance : MeasurableSpace (GaugeConfig s)) = borel (GaugeConfig s) := by
  have h := (hA (cutoffData s β hβ)).1.2.2.2.2.2.2.2.1
  have ht := productTopology_eq (s := s) hβ hA
  have hb : borel (GaugeConfig s) =
      @borel _ (ReflectionPositivity.CutoffMirrors.MirrorData.productTopology (cutoffData s β hβ)) := by
    rw [ht]
  rw [hb, ReflectionPositivity.CutoffMirrors.MirrorData.productTopology, borel_comap]
  exact h.symm
theorem borelSpace_gaugeConfig : BorelSpace (GaugeConfig s) :=
  ⟨gaugeConfig_measurableSpace_eq_borel hβ hA⟩
theorem continuous_of_continuousForProduct {Y : Type*} [TopologicalSpace Y]
    {F : GaugeConfig s → Y}
    (h : ReflectionPositivity.CutoffMirrors.MirrorData.ContinuousForProduct (cutoffData s β hβ) F) :
    Continuous F := by
  have ht := productTopology_eq (s := s) hβ hA
  unfold ReflectionPositivity.CutoffMirrors.MirrorData.ContinuousForProduct at h
  rwa [ht] at h
theorem measurableSet_compactGaugeFields :
    MeasurableSet (PeriodicLattice.compactGaugeFields s.L s.m ((s.K : ℕ) : ℤ)) := by
  have hset : PeriodicLattice.compactGaugeFields s.L s.m ((s.K : ℕ) : ℤ) =
      ⋂ b : PeriodicLattice.Bond s.L s.m ((s.K : ℕ) : ℤ),
        ({U | U b ∈ (Matrices.ComplexMatrix2.specialUnitary : Set Matrices.ComplexMatrix2)} ∩
          {U | U b.opposite = star (U b)}) := by
    ext U
    simp only [PeriodicLattice.compactGaugeFields, PeriodicLattice.IsGaugeField, mem_ofPred_eq,
      mem_iInter, mem_inter_iff, mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ b
      refine ⟨h1 b, ?_⟩
      rw [h2 b]
      exact Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 (Matrix.mem_specialUnitaryGroup_iff.1 (h1 b)).1)
    · intro h
      refine ⟨fun b => (h b).1, fun b => ?_⟩
      rw [(h b).2]
      exact (Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 (Matrix.mem_specialUnitaryGroup_iff.1 (h b).1).1)).symm
  rw [hset]
  have hc : IsClosed (Matrices.ComplexMatrix2.specialUnitary : Set Matrices.ComplexMatrix2) := by
    have : (Matrices.ComplexMatrix2.specialUnitary : Set Matrices.ComplexMatrix2) =
        {A | star A * A = 1} ∩ {A | Matrix.det A = 1} := by
      ext A
      simp only [SetLike.mem_coe, Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff',
        mem_inter_iff, mem_ofPred_eq]
    rw [this]
    exact (isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_eq (Continuous.matrix_det continuous_id) continuous_const)
  refine MeasurableSet.iInter fun b => ?_
  refine ((measurable_pi_apply b) hc.measurableSet).inter ?_
  have h1 : Continuous fun U : PeriodicLattice.Bond s.L s.m ((s.K : ℕ) : ℤ) → Matrices.ComplexMatrix2 =>
      U b.opposite :=
    continuous_apply _
  have h2 : Continuous fun U : PeriodicLattice.Bond s.L s.m ((s.K : ℕ) : ℤ) → Matrices.ComplexMatrix2 =>
      star (U b) :=
    continuous_star.comp (continuous_apply b)
  exact (isClosed_eq h1 h2).measurableSet
theorem productHaarMeasure_compl_eq_zero :
    PeriodicLattice.productHaarMeasure s.L s.m ((s.K : ℕ) : ℤ)
      (PeriodicLattice.compactGaugeFields s.L s.m ((s.K : ℕ) : ℤ))ᶜ = 0 := by
  have hS := measurableSet_compactGaugeFields (s := s) hβ hA
  obtain ⟨-, -, -, hbij, -, -, -, -, hinv, -⟩ := (hA (cutoffData s β hβ)).1
  have hpre : (PeriodicLattice.gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond s.L s.m ((s.K : ℕ) : ℤ) →
        Matrices.ComplexMatrix2.specialUnitary) → _) ⁻¹'
      (PeriodicLattice.compactGaugeFields s.L s.m ((s.K : ℕ) : ℤ))ᶜ = ∅ := by
    ext g
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    obtain ⟨U, rfl⟩ := hbij.2 g
    have h := hinv U
    exact h ▸ U.2
  unfold PeriodicLattice.productHaarMeasure
  by_cases hm : AEMeasurable (PeriodicLattice.gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond s.L s.m ((s.K : ℕ) : ℤ) →
        Matrices.ComplexMatrix2.specialUnitary) → _)
      (PeriodicLattice.gaugeFieldHaar s.L s.m ((s.K : ℕ) : ℤ))
  · rw [Measure.map_apply_of_aemeasurable hm hS.compl, hpre, measure_empty]
  · rw [Measure.map_of_not_aemeasurable hm]
    rfl
theorem wilsonGibbsMeasure_compl_eq_zero :
    PeriodicLattice.wilsonGibbsMeasure s.L s.m s.K β
      (PeriodicLattice.compactGaugeFields s.L s.m ((s.K : ℕ) : ℤ))ᶜ = 0 := by
  unfold PeriodicLattice.wilsonGibbsMeasure
  rw [Measure.smul_apply, withDensity_absolutelyContinuous _ _
    (productHaarMeasure_compl_eq_zero (s := s) hβ hA), smul_zero]
theorem gibbsMeasureOn_eq : gibbsMeasureOn s β =
    (ENNReal.ofReal (PeriodicLattice.partitionFunction s.L s.m s.K β))⁻¹ •
      (haarMeasureOn s).withDensity
        (fun U => ENNReal.ofReal (PeriodicLattice.boltzmannWeight β U.1)) :=
  comap_subtype_smul_withDensity (measurableSet_compactGaugeFields hβ hA) _ _ _
theorem energyBounds :
    (cutoffData s β hβ).EnergiesBoundedAndMeasureProbability := (hA _).2.2
theorem partitionFunction_pos : 0 < PeriodicLattice.partitionFunction s.L s.m s.K β :=
  (energyBounds hβ hA).2.2.2.2.2.2.2.2.1
theorem isProbabilityMeasure_gibbs : IsProbabilityMeasure (gibbsMeasureOn s β) :=
  (energyBounds hβ hA).2.2.2.2.2.2.2.2.2.2.2
theorem continuous_boltzmannWeight :
    Continuous fun U : GaugeConfig s => PeriodicLattice.boltzmannWeight β U.1 :=
  continuous_of_continuousForProduct hβ hA (energyBounds hβ hA).2.2.2.2.1
theorem complexExpectation_eq (F : GaugeConfig s → ℂ) :
    Probability.complexExpectation (gibbsMeasureOn s β) F =
      ((PeriodicLattice.partitionFunction s.L s.m s.K β : ℝ) : ℂ)⁻¹ *
        ∫ U, F U * ((PeriodicLattice.boltzmannWeight β U.1 : ℝ) : ℂ) ∂haarMeasureOn s := by
  have := borelSpace_gaugeConfig (s := s) hβ hA
  have hZ := partitionFunction_pos (s := s) hβ hA
  have hm : Measurable fun U : GaugeConfig s =>
      ENNReal.ofReal (PeriodicLattice.boltzmannWeight β U.1) :=
    ENNReal.measurable_ofReal.comp (continuous_boltzmannWeight hβ hA).measurable
  unfold Probability.complexExpectation
  rw [gibbsMeasureOn_eq hβ hA, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le, Complex.real_smul]
  push_cast
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  have hpos : 0 ≤ PeriodicLattice.boltzmannWeight β U.1 := (Real.exp_pos _).le
  simp only [ENNReal.toReal_ofReal hpos, Complex.real_smul]
  ring
theorem gibbsIsProbabilitySpace_holds : GibbsIsProbabilitySpace s β := by
  have := borelSpace_gaugeConfig (s := s) hβ hA
  have hB := gaugeConfig_measurableSpace_eq_borel (s := s) hβ hA
  refine ⟨hB, gibbsMeasureOn_eq hβ hA, isProbabilityMeasure_gibbs hβ hA, fun F => ?_,
    fun F _ => complexExpectation_eq hβ hA F, fun G _ => ?_⟩
  · rw [← hB]
    constructor
    · intro h
      have hm : Measurable F := by
        have h1 : Measurable fun U => (((F U).re : ℝ) : ℂ) + ((F U).im : ℂ) * Complex.I :=
          (Complex.measurable_ofReal.comp h.measurable_re).add
            ((Complex.measurable_ofReal.comp h.measurable_im).mul_const _)
        simpa only [Complex.re_add_im] using h1
      exact ⟨hm, h.bounded⟩
    · rintro ⟨hm, hb⟩
      exact ⟨Complex.measurable_re.comp hm, Complex.measurable_im.comp hm, hb⟩
  · exact integral_eq_integral_comap_subtype (measurableSet_compactGaugeFields hβ hA) _
      (wilsonGibbsMeasure_compl_eq_zero hβ hA) G
theorem plaquetteEnergyBoundedRV_holds : PlaquetteEnergyBoundedRV s := by
  have := borelSpace_gaugeConfig (s := s) hβ hA
  refine ⟨finite_plaq hβ hA, fun p => ?_⟩
  have hc : Continuous (plaquetteEnergyOn s p) :=
    continuous_of_continuousForProduct hβ hA ((energyBounds hβ hA).1 p).1
  have hb := ((energyBounds (s := s) hβ hA).1 p).2
  refine ⟨hc, fun U => ⟨(hb U).1, (hb U).2⟩, hc.measurable, 2, fun U => ?_⟩
  have h2 : plaquetteEnergyOn s p U ∈ Icc (0 : ℝ) 2 := hb U
  rw [abs_of_nonneg h2.1]
  exact h2.2
theorem observableOn_isBoundedRealRV (f : s.Torus → ℝ) :
    IsBoundedRealRV (observableOn s f) := by
  have := borelSpace_gaugeConfig (s := s) hβ hA
  have h := (energyBounds (s := s) hβ hA).2.1 f
  obtain ⟨C, hC⟩ := h.2
  exact ⟨(continuous_of_continuousForProduct hβ hA h.1).measurable, C, hC⟩
end Cutoff
section Distances
open YangMills.Construction.TestFunctions
theorem torusSide_pos (s : Conventions.StandingParameters) :
    0 < PeriodicLattice.torusSide s.L s.m := by apply _root_.YangMills.Construction.TorusMeasure.TranslatedLatticeCells.torusSide_pos <;> assumption
theorem euclidDistTorus_nonneg {S : ℝ} (x y : TorusMetric.Torus4 S) :
    0 ≤ euclidDistTorus x y := by apply _root_.YangMills.SharedProofs.p31350 <;> assumption
theorem euclidDistTorus_le_side (s : Conventions.StandingParameters) (u u₀ : s.Torus) :
    euclidDistTorus u u₀ ≤ s.side := by
  have hS := torusSide_pos s
  change TorusMetric.torusEuclidNorm (u - u₀) ≤ PeriodicLattice.torusSide s.L s.m
  choose b hb hb' using fun k => TorusMetric.exists_coe_eq_abs_eq_norm ((u - u₀) k)
  have hcov : TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) b = u - u₀ := funext hb
  unfold TorusMetric.torusEuclidNorm
  have hle : sInf (TorusMetric.euclidNormVec '' TorusMetric.torusProj
      (PeriodicLattice.torusSide s.L s.m) ⁻¹' {u - u₀}) ≤ TorusMetric.euclidNormVec b := by
    refine csInf_le ⟨0, ?_⟩ (mem_image_of_mem _ hcov)
    rintro _ ⟨v, -, rfl⟩
    exact Real.sqrt_nonneg _
  refine hle.trans ?_
  · have h2 : ∀ k, b k ^ 2 ≤ (PeriodicLattice.torusSide s.L s.m / 2) ^ 2 := fun k => by
      have h1 : |b k| ≤ PeriodicLattice.torusSide s.L s.m / 2 := by
        rw [hb' k]
        simpa [abs_of_pos hS] using AddCircle.norm_le_half_period
          (p := PeriodicLattice.torusSide s.L s.m) (x := (u - u₀) k) hS.ne'
      exact sq_le_sq' (by linarith [(abs_le.1 h1).1]) (abs_le.1 h1).2
    calc TorusMetric.euclidNormVec b
        ≤ Real.sqrt (∑ _k : Fin 4, (PeriodicLattice.torusSide s.L s.m / 2) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => h2 k)
      _ = PeriodicLattice.torusSide s.L s.m := by
          have : ∑ _k : Fin 4, (PeriodicLattice.torusSide s.L s.m / 2) ^ 2 =
              PeriodicLattice.torusSide s.L s.m ^ 2 := by
            simp
            ring
          rw [this, Real.sqrt_sq hS.le]
variable {E : Type*} [NormedAddCommGroup E]
theorem lipConstTorus_nonneg {S : ℝ} (f : TorusMetric.Torus4 S → E) : 0 ≤ lipConstTorus f :=
  Real.sInf_nonneg fun _ hC => hC.1
theorem norm_sub_le_lipConstTorus_mul {S : ℝ} {f : TorusMetric.Torus4 S → E}
    (hf : IsLipschitzFor euclidDistTorus f) (x y : TorusMetric.Torus4 S) :
    ‖f x - f y‖ ≤ lipConstTorus f * euclidDistTorus x y := by
  obtain ⟨C, hC0, hC⟩ := hf
  rcases (euclidDistTorus_nonneg x y).eq_or_lt with h | h
  · have h1 := hC x y
    rw [← h] at h1 ⊢
    simpa using h1
  · rw [← div_le_iff₀ h]
    refine le_csInf ⟨C, hC0, hC⟩ ?_
    rintro C' ⟨-, hC'⟩
    rw [div_le_iff₀ h]
    exact hC' x y
theorem lipschitzImpliesBounded_holds (s : Conventions.StandingParameters) :
    LipschitzImpliesBounded s E := by
  intro f hf
  have key : ∀ u u₀ : s.Torus, ‖f u‖ ≤ ‖f u₀‖ + s.side * lipConstTorus f := fun u u₀ => by
    calc ‖f u‖ = ‖f u₀ + (f u - f u₀)‖ := by simp
      _ ≤ ‖f u₀‖ + ‖f u - f u₀‖ := norm_add_le _ _
      _ ≤ ‖f u₀‖ + lipConstTorus f * euclidDistTorus u u₀ := by
          gcongr
          exact norm_sub_le_lipConstTorus_mul hf u u₀
      _ ≤ ‖f u₀‖ + s.side * lipConstTorus f := by
          have := mul_le_mul_of_nonneg_left (euclidDistTorus_le_side s u u₀)
            (lipConstTorus_nonneg f)
          linarith [mul_comm (lipConstTorus f) s.side]
  exact ⟨⟨‖f 0‖ + s.side * lipConstTorus f, fun u => key u 0⟩, key⟩
end Distances
section Observables
open YangMills.Construction.TestFunctions
variable {s : Conventions.StandingParameters} {β : ℝ} (hβ : 0 < β)
  (hA : ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies.Statement)
  (hE : Probability.ExpectationBasicProperties)
  {n : ℕ}
theorem observableOn_eq_sum [Fintype (Plaq s)] (f : s.Torus → ℝ) (U : GaugeConfig s) :
    observableOn s f U =
      ∑ p : Plaq s, plaquetteEnergyOn s p U * f p.barycenter := by
  simp only [observableOn, PeriodicLattice.smearedObservable, plaquetteEnergyOn, smul_eq_mul]
  exact finsum_eq_sum_of_fintype _
include hβ hA hE in
theorem observablesBoundedRV_holds : ObservablesBoundedRV s := by
  have := finite_plaq (s := s) hβ hA
  have := Fintype.ofFinite (Plaq s)
  have hP := isProbabilityMeasure_gibbs (s := s) hβ hA
  obtain ⟨V, hV⟩ := (hE (GaugeConfig s) (gibbsMeasureOn s β)).1.1
  have hObs := observableOn_isBoundedRealRV (s := s) hβ hA
  have hmem : ∀ f, observableOn s f ∈ V := fun f => by
    exact show observableOn s f ∈ (V : Set (GaugeConfig s → ℝ)) from by
      rw [hV]
      exact hObs f
  let T : (s.Torus → ℝ) →ₗ[ℝ] V :=
    { toFun := fun f => ⟨observableOn s f, hmem f⟩
      map_add' := fun f g => by
        apply Subtype.ext
        funext U
        simp only [Submodule.coe_add, Pi.add_apply, observableOn_eq_sum, mul_add,
          Finset.sum_add_distrib]
      map_smul' := fun c f => by
        apply Subtype.ext
        funext U
        simp only [Submodule.coe_smul, Pi.smul_apply, observableOn_eq_sum, smul_eq_mul,
          RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  refine ⟨hObs, ?_, ⟨V, T, hV, fun f => rfl⟩, ?_⟩
  · intro f f' h
    funext U
    simp only [observableOn_eq_sum, h]
  · let W : Submodule ℝ (s.Torus → ℝ) :=
      { carrier := {f | IsLipschitzFor euclidDistTorus f}
        add_mem' := by
          rintro f g ⟨C, hC0, hC⟩ ⟨C', hC0', hC'⟩
          refine ⟨C + C', add_nonneg hC0 hC0', fun x y => ?_⟩
          calc ‖(f + g) x - (f + g) y‖ = ‖(f x - f y) + (g x - g y)‖ := by
                simp only [Pi.add_apply]
                congr 1
                ring
            _ ≤ ‖f x - f y‖ + ‖g x - g y‖ := norm_add_le _ _
            _ ≤ (C + C') * euclidDistTorus x y := by
                rw [add_mul]
                exact add_le_add (hC x y) (hC' x y)
        zero_mem' := ⟨0, le_rfl, fun x y => by simp⟩
        smul_mem' := by
          rintro c f ⟨C, hC0, hC⟩
          refine ⟨|c| * C, mul_nonneg (abs_nonneg c) hC0, fun x y => ?_⟩
          have h1 : (c • f) x - (c • f) y = c * (f x - f y) := by
            simp only [Pi.smul_apply, smul_eq_mul]
            ring
          rw [h1, norm_mul, Real.norm_eq_abs, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hC x y) (abs_nonneg c) }
    exact ⟨W, V, T.comp W.subtype, rfl, hV, fun f => rfl⟩
include hβ hA
theorem momentGeneratingFunction_eq (f : Fin n → s.Torus → ℝ) (t : Fin n → ℂ) :
    Cumulants.momentGeneratingFunction (PeriodicLattice.wilsonGibbsMeasure s.L s.m s.K β)
        (fun i => PeriodicLattice.smearedObservable (f i)) t =
      Cumulants.momentGeneratingFunction (gibbsMeasureOn s β) (observableVector s f) t :=
  integral_eq_integral_comap_subtype (measurableSet_compactGaugeFields hβ hA) _
    (wilsonGibbsMeasure_compl_eq_zero hβ hA) _
theorem cumulantOfObservables_eq (f : Fin n → s.Torus → ℝ) :
    cumulantOfObservables s β f =
      Cumulants.mixedCumulant (gibbsMeasureOn s β) (observableVector s f) := by
  unfold cumulantOfObservables PeriodicLattice.gibbsCumulant Cumulants.mixedCumulant
  simp only [momentGeneratingFunction_eq hβ hA f]
theorem expectationExpSum_eq (f : Fin n → s.Torus → ℝ) :
    expectationExpSum s β f =
      Cumulants.tupleMomentGeneratingFunction (gibbsMeasureOn s β) (observableVector s f) := by
  funext z
  exact integral_eq_integral_comap_subtype (measurableSet_compactGaugeFields hβ hA) _
    (wilsonGibbsMeasure_compl_eq_zero hβ hA) _
theorem cumulantEqMixedCumulant_holds (hG : Cumulants.TupleLogMGF.TupleMGFAndLogTheorem)
    (f : Fin n → s.Torus → ℝ) (hn : 1 ≤ n) : CumulantEqMixedCumulant s β f := by
  have hP := isProbabilityMeasure_gibbs (s := s) hβ hA
  obtain ⟨-, hL, hR, -, -⟩ := hG (GaugeConfig s) (gibbsMeasureOn s β) n
    (observableVector s f) hn fun i => observableOn_isBoundedRealRV hβ hA _
  have hc := cumulantOfObservables_eq hβ hA f
  have hl : (fun z => ComplexVariables.logPrincipal (expectationExpSum s β f z)) =
      Cumulants.logMomentGeneratingFunction (gibbsMeasureOn s β) (observableVector s f) := by
    rw [expectationExpSum_eq hβ hA f]
    rfl
  unfold CumulantEqMixedCumulant
  rw [hl]
  exact ⟨hc, hL.hasMixedPartial, hc.trans hL.mixedCumulant_eq, hR.hasPartials,
    hc.trans hR.mixedCumulant_eq⟩
end Observables
section Sources
variable {s : Conventions.StandingParameters} {β : ℝ} (hβ : 0 < β)
  (hA : ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies.Statement)
  (hI : Matrices.ComplexMatrix2.UnitaryLogarithmProperties)
  {n : ℕ}
include hI in
theorem fullTrace_im_eq_zero {A : Matrices.ComplexMatrix2}
    (h : A ∈ Matrices.ComplexMatrix2.specialUnitary) :
    (Matrices.ComplexMatrix2.fullTrace A).im = 0 := by
  obtain ⟨t, -, ht⟩ := (hI.2.1 A h).1
  have h2 : Matrices.ComplexMatrix2.fullTrace A = 2 * (t : ℂ) := by
    rw [← ht]
    simp only [Matrices.ComplexMatrix2.halfTrace]
    ring
  rw [h2]
  simp
theorem plaquetteHolonomy_mem (U : GaugeConfig s) (p : Plaq s) :
    PeriodicLattice.plaquetteHolonomy U.1 p ∈ Matrices.ComplexMatrix2.specialUnitary := by
  unfold PeriodicLattice.plaquetteHolonomy PeriodicLattice.pathHolonomy
  refine Submonoid.list_prod_mem _ fun A hA => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hA
  exact U.2.1 b (mem_univ _)
include hI in
theorem plaquetteEnergy_eq_ofReal (U : GaugeConfig s) (p : Plaq s) :
    PeriodicLattice.plaquetteEnergy U.1 p = ((plaquetteEnergyOn s p U : ℝ) : ℂ) := by
  have h := fullTrace_im_eq_zero hI (plaquetteHolonomy_mem U p)
  apply Complex.ext
  · simp [PeriodicLattice.plaquetteEnergy, plaquetteEnergyOn, PeriodicLattice.plaquetteCost]
  · simp [PeriodicLattice.plaquetteEnergy, plaquetteEnergyOn, PeriodicLattice.plaquetteCost, h]
include hβ hA hI in
theorem sourcedBoltzmannWeight_eq (f : Fin n → s.Torus → ℝ) (z : Fin n → ℂ) (U : GaugeConfig s) :
    PeriodicLattice.sourcedBoltzmannWeight β (PeriodicLattice.complexSource f z) U.1 =
      ComplexVariables.expComp (fun ω => ∑ i, z i * (observableVector s f i ω : ℂ)) U *
        ((PeriodicLattice.boltzmannWeight β U.1 : ℝ) : ℂ) := by
  have := finite_plaq (s := s) hβ hA
  have := Fintype.ofFinite (Plaq s)
  have hact : PeriodicLattice.wilsonAction U.1 = ∑ p : Plaq s, plaquetteEnergyOn s p U :=
    finsum_eq_sum_of_fintype _
  have hw : PeriodicLattice.barycenterWeightedEnergy
      (fun x => (β : ℂ) - PeriodicLattice.complexSource f z x) U.1 =
      ∑ p : Plaq s, ((β : ℂ) - ∑ i, z i * (f i p.barycenter : ℂ)) *
        ((plaquetteEnergyOn s p U : ℝ) : ℂ) := by
    unfold PeriodicLattice.barycenterWeightedEnergy PeriodicLattice.plaquetteWeightedEnergy
    rw [finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun p _ => by
      rw [plaquetteEnergy_eq_ofReal hI U p]
      rfl
  unfold PeriodicLattice.sourcedBoltzmannWeight ComplexVariables.expComp
    PeriodicLattice.boltzmannWeight
  rw [hw, hact, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [observableVector, observableOn_eq_sum]
  push_cast
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h1 : ∀ (i : Fin n) (p : Plaq s),
      z i * ((plaquetteEnergyOn s p U : ℂ) * (f i p.barycenter : ℂ)) =
        z i * (f i p.barycenter : ℂ) * (plaquetteEnergyOn s p U : ℂ) := fun _ _ => by ring
  simp only [h1, neg_mul, Finset.sum_neg_distrib]
  ring
include hβ hA hI in
theorem generatingFunction_eq_mul (f : Fin n → s.Torus → ℝ) (z : Coordinates.ComplexCoordinates n) :
    PeriodicLattice.generatingFunction s.L s.m s.K β f z =
      ((PeriodicLattice.partitionFunction s.L s.m s.K β : ℝ) : ℂ) *
        Cumulants.tupleMomentGeneratingFunction (gibbsMeasureOn s β) (observableVector s f) z := by
  have hZ := partitionFunction_pos (s := s) hβ hA
  have hne : ((PeriodicLattice.partitionFunction s.L s.m s.K β : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hZ.ne'
  unfold PeriodicLattice.generatingFunction Cumulants.tupleMomentGeneratingFunction
  rw [complexExpectation_eq hβ hA, ← mul_assoc, mul_inv_cancel₀ hne, one_mul,
    integral_eq_integral_comap_subtype (measurableSet_compactGaugeFields hβ hA) _
      (productHaarMeasure_compl_eq_zero hβ hA)]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun U => sourcedBoltzmannWeight_eq hβ hA hI f z U)
end Sources
section Logarithm
open YangMills.Construction.ComplexVariables
variable {n : ℕ}
theorem iteratedPartials_const_add (c : ℂ) (F : Coordinates.ComplexCoordinates n → ℂ)
    (l : List (Fin n)) (hl : l ≠ []) :
    iteratedPartials l (fun z => 1 * c + 1 * F z) = iteratedPartials l F := by
  induction l with
  | nil => exact absurd rfl hl
  | cons i l ih =>
    by_cases h : l = []
    · subst h
      funext z
      simp only [iteratedPartials, List.foldr_cons, List.foldr_nil, partialDeriv]
      have h1 : diffQuot (fun z => 1 * c + 1 * F z) z i = diffQuot F z i := by
        funext ζ
        simp [diffQuot]
      rw [h1]
    · have h1 := ih h
      unfold iteratedPartials at h1 ⊢
      simp only [List.foldr_cons]
      rw [h1]
variable {s : Conventions.StandingParameters} {β : ℝ} (hβ : 0 < β)
  (hA : ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies.Statement)
  (hG : Cumulants.TupleLogMGF.TupleMGFAndLogTheorem)
  (hT : ComplexVariables.HolomorphicFacts.StandardFacts)
  (hI : Matrices.ComplexMatrix2.UnitaryLogarithmProperties)
include hβ hA hG hI in
theorem generatingFunctionRatio_holds (f : Fin n → s.Torus → ℝ) (hn : 1 ≤ n) :
    GeneratingFunctionRatio s β f := by
  have hP := isProbabilityMeasure_gibbs (s := s) hβ hA
  obtain ⟨hEnt, -, -, -, -⟩ := hG (GaugeConfig s) (gibbsMeasureOn s β) n
    (observableVector s f) hn fun i => observableOn_isBoundedRealRV hβ hA _
  have hZ := partitionFunction_pos (s := s) hβ hA
  have hne : ((PeriodicLattice.partitionFunction s.L s.m s.K β : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hZ.ne'
  have h0 : PeriodicLattice.generatingFunction s.L s.m s.K β f 0 =
      ((PeriodicLattice.partitionFunction s.L s.m s.K β : ℝ) : ℂ) := by
    rw [generatingFunction_eq_mul hβ hA hI f 0, hEnt.apply_zero, mul_one]
  refine ⟨fun z => ?_, h0⟩
  rw [h0, generatingFunction_eq_mul hβ hA hI f z, mul_div_cancel_left₀ _ hne]
include hβ hA hG hT hI in
theorem logGeneratingFunctionCumulant_holds (f : Fin n → s.Torus → ℝ) (hn : 1 ≤ n) :
    LogGeneratingFunctionCumulant s β f := by
  have hP := isProbabilityMeasure_gibbs (s := s) hβ hA
  obtain ⟨hEnt, hL, -, -, -⟩ := hG (GaugeConfig s) (gibbsMeasureOn s β) n
    (observableVector s f) hn fun i => observableOn_isBoundedRealRV hβ hA _
  have hZ := partitionFunction_pos (s := s) hβ hA
  have hZf := generatingFunction_eq_mul (s := s) hβ hA hI f
  obtain ⟨-, hSumUniv, -, -, -, -⟩ := hT n hn univ isOpen_univ
  obtain ⟨hHol, hSum, -, -, hLog, -⟩ := hT n hn _ hL.isOpen
  have hEntire : IsEntireFun (PeriodicLattice.generatingFunction s.L s.m s.K β f) := by
    have h1 := (hSumUniv.2.2.2.2.1 _ _ hEnt.entire hEnt.entire
      ((PeriodicLattice.partitionFunction s.L s.m s.K β : ℝ) : ℂ) 0).1
    have h2 : PeriodicLattice.generatingFunction s.L s.m s.K β f = fun z =>
        ((PeriodicLattice.partitionFunction s.L s.m s.K β : ℝ) : ℂ) *
            Cumulants.tupleMomentGeneratingFunction (gibbsMeasureOn s β) (observableVector s f) z +
          0 * Cumulants.tupleMomentGeneratingFunction (gibbsMeasureOn s β)
            (observableVector s f) z := by
      funext z
      rw [hZf z, zero_mul, add_zero]
    rw [h2]
    exact h1
  have hval : ∀ z ∈ Cumulants.logDomain (gibbsMeasureOn s β) (observableVector s f),
      PeriodicLattice.generatingFunction s.L s.m s.K β f z ∈ nonpositiveRayComplement ∧
        logPrincipal (PeriodicLattice.generatingFunction s.L s.m s.K β f z) =
          ((Real.log (PeriodicLattice.partitionFunction s.L s.m s.K β) : ℝ) : ℂ) +
            Cumulants.logMomentGeneratingFunction (gibbsMeasureOn s β) (observableVector s f) z := by
    intro z hz
    have hs : Cumulants.tupleMomentGeneratingFunction (gibbsMeasureOn s β)
        (observableVector s f) z ∈ nonpositiveRayComplement := hLog.2.2.2.2.2.2.1 hz
    refine ⟨fun x hx h => ?_, ?_⟩
    · rw [hZf z] at h
      have hne : ((PeriodicLattice.partitionFunction s.L s.m s.K β : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hZ.ne'
      refine hs (x / PeriodicLattice.partitionFunction s.L s.m s.K β)
        (div_nonpos_of_nonpos_of_nonneg hx hZ.le) ?_
      push_cast
      rw [eq_div_iff hne, ← h]
      ring
    · rw [hZf z]
      exact Complex.log_ofReal_mul hZ (hL.mgf_ne_zero z hz)
  have hFh := (hSum.2.2.2.2.1 (fun _ =>
    ((Real.log (PeriodicLattice.partitionFunction s.L s.m s.K β) : ℝ) : ℂ))
    (Cumulants.logMomentGeneratingFunction (gibbsMeasureOn s β) (observableVector s f))
    (hSum.1 _).1 hL.holomorphic 1 1).1
  have hGeq : EqOn (fun z => logPrincipal
      (PeriodicLattice.generatingFunction s.L s.m s.K β f z))
      (fun z => 1 * ((Real.log (PeriodicLattice.partitionFunction s.L s.m s.K β) : ℝ) : ℂ) +
        1 * Cumulants.logMomentGeneratingFunction (gibbsMeasureOn s β) (observableVector s f) z)
      (Cumulants.logDomain (gibbsMeasureOn s β) (observableVector s f)) := fun z hz => by
    simp only [one_mul]
    exact (hval z hz).2
  obtain ⟨hGh, hGJ⟩ := (hHol _ hFh).2.2.2.2.2.2.2 _ hL.isOpen subset_rfl _ hGeq
  refine ⟨hEntire, hval, ((hHol _ hGh).2.2.1 Finset.univ).1, ?_⟩
  have hne : (Finset.univ : Finset (Fin n)).sort ≠ [] := by
    intro h
    have h1 := Finset.length_sort (s := (Finset.univ : Finset (Fin n))) (r := (· ≤ ·))
    rw [h] at h1
    simp at h1
    omega
  have h2 := hGJ Finset.univ hL.zero_mem
  unfold mixedPartialAtOrigin
  rw [h2, cumulantOfObservables_eq hβ hA f, hL.mixedCumulant_eq]
  unfold partialOverFinset
  rw [iteratedPartials_const_add _ _ _ hne]
end Logarithm
theorem probabilitySpaceTheorem
    (hA : ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies.Statement)
    (hG : Cumulants.TupleLogMGF.TupleMGFAndLogTheorem)
    (hE : Probability.ExpectationBasicProperties)
    (hT : ComplexVariables.HolomorphicFacts.StandardFacts)
    (hI : Matrices.ComplexMatrix2.UnitaryLogarithmProperties) : ProbabilitySpaceTheorem.claim := by
  intro s β hβ
  refine ⟨gibbsIsProbabilitySpace_holds hβ hA, plaquetteEnergyBoundedRV_holds hβ hA,
    ⟨euclidDistTorus_le_side s, lipschitzImpliesBounded_holds s,
      lipschitzImpliesBounded_holds s⟩, observablesBoundedRV_holds hβ hA hE,
    fun n f hn => cumulantEqMixedCumulant_holds hβ hA hG f hn,
    fun n f hn _ => ⟨generatingFunctionRatio_holds hβ hA hG hI f hn,
      logGeneratingFunctionCumulant_holds hβ hA hG hT hI f hn⟩⟩
end YangMills.Construction.LatticeProbability.ProbabilitySpaceProof
end
