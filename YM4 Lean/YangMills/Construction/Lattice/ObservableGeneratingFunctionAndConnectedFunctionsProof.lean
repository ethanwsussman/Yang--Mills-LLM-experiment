import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsOfSeveralVariables
import YangMills.Construction.Cumulants.GeneratingFunctionIsEntireWithItsPrincipalLogarithm
import YangMills.Construction.Lattice.ConfigurationSpaceBareDensityAndNormalisingIntegralProof
import YangMills.Construction.Lattice.ObservableGeneratingFunctionAndConnectedFunctions
import YangMills.Construction.Lattice.SourceDiscAndSourceClass
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.LawInAState.GridDataAtEveryExponentProofForm
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TorusBound.ObservableCumulants
open YangMills.Construction.PeriodicLattice
open YangMills.Construction.PeriodicLattice.GaugeFieldSpace
open YangMills.Construction.Cumulants.GeneratingLog
local instance : SecondCountableTopology Matrices.ComplexMatrix2 :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
section PlaquetteSums
variable {L m : ℕ} {j : ℤ}
theorem continuous_plaquetteEnergy (p : Plaquette L m j) :
    Continuous fun U : Bond L m j → Matrices.ComplexMatrix2 => plaquetteCost U p := by apply _root_.YangMills.Construction.EqualSideGridsAtEveryExponent.continuous_plaquetteCost <;> assumption
variable [Fintype (Plaquette L m j)]
theorem smearedObservable_eq_sum {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (w : FourTorus L m → E) (U : Bond L m j → Matrices.ComplexMatrix2) :
    smearedObservable w U = ∑ p : Plaquette L m j, plaquetteCost U p • w p.barycenter :=
  finsum_eq_sum_of_fintype _
theorem wilsonAction_eq_sum (U : Bond L m j → Matrices.ComplexMatrix2) :
    wilsonAction U = ∑ p : Plaquette L m j, plaquetteCost U p :=
  finsum_eq_sum_of_fintype _
theorem continuous_smearedObservable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : FourTorus L m → E) :
    Continuous fun U : Bond L m j → Matrices.ComplexMatrix2 => smearedObservable w U := by
  simp only [smearedObservable_eq_sum]
  exact continuous_finsetSum _ fun p _ => (continuous_plaquetteEnergy p).smul continuous_const
theorem continuous_wilsonAction :
    Continuous fun U : Bond L m j → Matrices.ComplexMatrix2 => wilsonAction U := by
  simp only [wilsonAction_eq_sum]
  exact continuous_finsetSum _ fun p _ => continuous_plaquetteEnergy p
theorem smearedObservable_add_smul (w w' : FourTorus L m → ℂ) (c : ℂ)
    (U : Bond L m j → Matrices.ComplexMatrix2) :
    smearedObservable (w + c • w') U = smearedObservable w U + c * smearedObservable w' U := by
  simp only [smearedObservable_eq_sum]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  ring
theorem conj_smearedObservable (w : FourTorus L m → ℂ) (U : Bond L m j → Matrices.ComplexMatrix2) :
    (starRingEnd ℂ) (smearedObservable w U) =
      smearedObservable (fun x => (starRingEnd ℂ) (w x)) U := by
  simp only [smearedObservable_eq_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
theorem im_smearedObservable (w : FourTorus L m → ℂ) (hw : ∀ x, (w x).im = 0)
    (U : Bond L m j → Matrices.ComplexMatrix2) :
    (smearedObservable w U).im = 0 := by
  rw [smearedObservable_eq_sum, Complex.im_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Complex.real_smul, Complex.mul_im, hw]
  simp
theorem smearedObservable_complexSource {n : ℕ} (f : Fin n → FourTorus L m → ℝ) (z : Fin n → ℂ)
    (U : Bond L m j → Matrices.ComplexMatrix2) :
    smearedObservable (complexSource f z) U =
      ∑ i, z i * ((smearedObservable (f i) U : ℝ) : ℂ) := by
  simp only [smearedObservable_eq_sum]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [complexSource, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]
  ring
end PlaquetteSums
section FieldSubset
variable {L m K : ℕ}
theorem entrywiseTopology_eq :
    Matrices.ComplexMatrix2.entrywiseTopology =
      (inferInstance : TopologicalSpace Matrices.ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.GaugeFieldSpace.entrywiseTopology_eq_instance <;> assumption
theorem measurableSet_compactGaugeFields (hS : CompactMetrizableFieldSpace L m K) :
    MeasurableSet (compactGaugeFields L m (K : ℤ)) := by
  obtain ⟨-, -, -, -, hcomp, -, hcont⟩ := hS
  have hval : @Continuous (compactGaugeFields L m (K : ℤ))
      (Bond L m (K : ℤ) → Matrices.ComplexMatrix2) (productTopology L m K) _ Subtype.val := by
    refine @continuous_pi _ _ _ (productTopology L m K) _ _ fun b => ?_
    have h := hcont b
    rwa [entrywiseTopology_eq] at h
  have hc : IsCompact (range (Subtype.val : compactGaugeFields L m (K : ℤ) → _)) :=
    @isCompact_range _ _ (productTopology L m K) _ hcomp _ hval
  rw [Subtype.range_coe] at hc
  exact hc.isClosed.measurableSet
theorem exists_norm_bound_of_continuous {E : Type*} [NormedAddCommGroup E]
    (hS : CompactMetrizableFieldSpace L m K)
    {F : (Bond L m (K : ℤ) → Matrices.ComplexMatrix2) → E}
    (hF : @Continuous (compactGaugeFields L m (K : ℤ)) E (productTopology L m K) _
      fun U => F U.1) :
    ∃ C : ℝ, ∀ U ∈ compactGaugeFields L m (K : ℤ), ‖F U‖ ≤ C := by
  obtain ⟨-, -, -, -, hcomp, -, -⟩ := hS
  obtain ⟨C, hC⟩ :=
    (@isCompact_range _ _ (productTopology L m K) _ hcomp _ hF).isBounded.exists_norm_le
  exact ⟨C, fun U hU => hC _ ⟨⟨U, hU⟩, rfl⟩⟩
end FieldSubset
section RestrictedObservable
variable {L m K : ℕ}
theorem continuous_smearedObservable_restrict {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype (Plaquette L m (K : ℤ))] {β : ℝ}
    (hD : BoltzmannWeightBounds L m K β) (w : FourTorus L m → E) :
    @Continuous (compactGaugeFields L m (K : ℤ)) E (productTopology L m K) _
      fun U => smearedObservable (j := (K : ℤ)) w U.1 := by
  let _ := productTopology L m K
  simp only [smearedObservable_eq_sum]
  exact continuous_finsetSum _ fun p _ => (hD.1 p).smul continuous_const
end RestrictedObservable
section GibbsDensity
variable {L m K : ℕ} {β : ℝ}
theorem measurable_boltzmannWeight [Fintype (Plaquette L m (K : ℤ))] :
    Measurable fun U : Bond L m (K : ℤ) → Matrices.ComplexMatrix2 =>
      ENNReal.ofReal (boltzmannWeight β U) := by
  have h : Continuous fun U : Bond L m (K : ℤ) → Matrices.ComplexMatrix2 =>
      boltzmannWeight β U :=
    Real.continuous_exp.comp (continuous_const.mul continuous_wilsonAction)
  exact h.measurable.ennreal_ofReal
theorem integral_wilsonGibbsMeasure [Fintype (Plaquette L m (K : ℤ))]
    (hZ : 0 < partitionFunction L m K β) (F : (Bond L m (K : ℤ) → Matrices.ComplexMatrix2) → ℂ) :
    ∫ U, F U ∂wilsonGibbsMeasure L m K β =
      ((partitionFunction L m K β)⁻¹ : ℝ) • ∫ U, (boltzmannWeight β U : ℂ) * F U
        ∂productHaarMeasure L m (K : ℤ) := by
  unfold wilsonGibbsMeasure
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul
    measurable_boltzmannWeight
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hZ.le]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  have h0 : 0 ≤ boltzmannWeight β U := (Real.exp_pos _).le
  show (ENNReal.ofReal (boltzmannWeight β U)).toReal • F U = _
  rw [ENNReal.toReal_ofReal h0, Complex.real_smul]
end GibbsDensity
variable (D : Setup)
theorem boltzmannWeight_mul_exp (w : D.Torus → ℂ) (U : D.LinkConfig) :
    (boltzmannWeight D.β U : ℂ) * Complex.exp (D.obs w U) =
      Complex.exp (-(D.β : ℂ) * (wilsonAction U : ℂ) + D.obs w U) := by
  unfold boltzmannWeight
  rw [Complex.exp_add, Complex.ofReal_exp]
  push_cast
  rfl
theorem observableProperties (hS : CompactMetrizableFieldSpace D.L D.m D.K)
    (hD : BoltzmannWeightBounds D.L D.m D.K D.β) : ObservableProperties D := by
  let : Fintype (Plaquette D.L D.m ((D.K : ℕ) : ℤ)) := @Fintype.ofFinite _ hS.2.1
  refine ⟨fun w w' _ _ c U _ => smearedObservable_add_smul w w' c U,
    fun w _ U _ => conj_smearedObservable w U,
    fun w _ => ⟨continuous_smearedObservable_restrict hD w, ?_,
      fun hw U _ => im_smearedObservable w hw U⟩⟩
  exact exists_norm_bound_of_continuous hS (continuous_smearedObservable_restrict hD w)
theorem partitionFun_zero [Fintype (Plaquette D.L D.m ((D.K : ℕ) : ℤ))] :
    D.partitionFun 0 = (partitionFunction D.L D.m D.K D.β : ℂ) := by
  unfold partitionFunction
  rw [← integral_complex_ofReal]
  unfold Setup.partitionFun
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  have h := boltzmannWeight_mul_exp D 0 U
  have h0 : D.obs (0 : D.Torus → ℂ) U = 0 := by
    simp [smearedObservable_eq_sum]
  rw [h0, Complex.exp_zero, mul_one] at h
  beta_reduce
  rw [h0]
  exact h.symm
theorem partitionRatio (hS : CompactMetrizableFieldSpace D.L D.m D.K)
    (hN : PartitionFunctionBounds D.L D.m D.K D.β) : PartitionRatio D := by
  let : Fintype (Plaquette D.L D.m ((D.K : ℕ) : ℤ)) := @Fintype.ofFinite _ hS.2.1
  have hZ : 0 < partitionFunction D.L D.m D.K D.β := (Real.exp_pos _).trans_le hN.2.1
  refine ⟨partitionFun_zero D, hZ, fun w _ => ?_⟩
  rw [partitionFun_zero D]
  show ∫ U, Complex.exp (D.obs w U) ∂wilsonGibbsMeasure D.L D.m D.K D.β = _
  rw [integral_wilsonGibbsMeasure hZ]
  simp only [boltzmannWeight_mul_exp]
  rw [Complex.real_smul, div_eq_inv_mul]
  push_cast
  rfl
section SourceFamily
variable {n : ℕ} (f : Fin n → D.Torus → ℝ)
def restrictedObservable (i : Fin n) : D.LinkConfig → ℝ :=
  (compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)).indicator fun U => D.obs (f i) U
theorem restrictedObservable_bounded (hS : CompactMetrizableFieldSpace D.L D.m D.K)
    (hD : BoltzmannWeightBounds D.L D.m D.K D.β) (i : Fin n) :
    Probability.IsBoundedRealRV (restrictedObservable D f i) := by
  let : Fintype (Plaquette D.L D.m ((D.K : ℕ) : ℤ)) := @Fintype.ofFinite _ hS.2.1
  refine ⟨(continuous_smearedObservable (f i)).measurable.indicator
    (measurableSet_compactGaugeFields hS), ?_⟩
  obtain ⟨C, hC⟩ :=
    exists_norm_bound_of_continuous hS (continuous_smearedObservable_restrict hD (f i))
  refine ⟨max C 0, fun U => ?_⟩
  by_cases hU : U ∈ compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)
  · rw [restrictedObservable, indicator_of_mem hU]
    exact (hC U hU).trans (le_max_left _ _)
  · rw [restrictedObservable, indicator_of_notMem hU, abs_zero]
    exact le_max_right _ _
theorem momentGeneratingFunction_restricted
    (hc : wilsonGibbsMeasure D.L D.m D.K D.β
      (compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ))ᶜ = 0) :
    Cumulants.momentGeneratingFunction D.gibbs (restrictedObservable D f) =
      Cumulants.momentGeneratingFunction D.gibbs fun i => D.obs (f i) := by
  have hae : ∀ᵐ U ∂D.gibbs, U ∈ compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) :=
    mem_ae_iff.mpr hc
  funext z
  unfold Cumulants.momentGeneratingFunction
  refine integral_congr_ae (hae.mono fun U hU => ?_)
  simp only [restrictedObservable, indicator_of_mem hU]
theorem familyGeneratingFunProperties (hn : 1 ≤ n) (hf : D.IsRealFamily f)
    (hS : CompactMetrizableFieldSpace D.L D.m D.K) (hD : BoltzmannWeightBounds D.L D.m D.K D.β)
    (hR : PartitionRatio D) [IsProbabilityMeasure D.gibbs]
    (hc : wilsonGibbsMeasure D.L D.m D.K D.β
      (compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ))ᶜ = 0)
    (hdisc : SourceDiskAndClass.Statement)
    (hent : Cumulants.GeneratingLog.EntireAndLogCumulant)
    (hholo : SeveralComplexVariables.HolomorphicCalculusRules) :
    FamilyGeneratingFunProperties D f := by
  let : Fintype (Plaquette D.L D.m ((D.K : ℕ) : ℤ)) := @Fintype.ofFinite _ hS.2.1
  have hres := momentGeneratingFunction_restricted D f hc
  obtain ⟨H, Hz⟩ := hent D.LinkConfig D.gibbs n (restrictedObservable D f) hn
    (restrictedObservable_bounded D f hS hD)
  have hgen : D.familyGeneratingFun f =
      Cumulants.momentGeneratingFunction D.gibbs (restrictedObservable D f) := by
    rw [hres]
    rfl
  have hdom : D.logGenDomain f = nearOneSet D.gibbs (restrictedObservable D f) := by
    ext z
    simp only [Setup.logGenDomain, nearOneSet, mem_ofPred_eq, hgen]
  have hlog : D.logFamilyGeneratingFun f = logOfGenerating D.gibbs (restrictedObservable D f) := by
    funext z
    simp only [Setup.logFamilyGeneratingFun, logOfGenerating, Function.comp_apply, hgen]
  have hcum : D.truncatedCorrelation f =
      Cumulants.mixedCumulant D.gibbs (restrictedObservable D f) := by
    unfold Setup.truncatedCorrelation gibbsCumulant Cumulants.mixedCumulant
    rw [hres]
  set O := nearOneSet D.gibbs (restrictedObservable D f) with hO
  set G := logOfGenerating D.gibbs (restrictedObservable D f) with hG'
  set c : ℂ := ((Real.log (D.partitionFun 0).re : ℝ) : ℂ) with hcdef
  have hconst : ComplexVariables.IsHolomorphicScalar O fun _ => c :=
    ⟨H.isOpen, continuousOn_const, fun a _ k => Filter.Eventually.of_forall fun ζ =>
      differentiableAt_const _⟩
  have hG : D.logPartitionFun f = fun z => c + 1 * G z := by
    funext z
    simp only [Setup.logPartitionFun, hlog, one_mul, hcdef]
  obtain ⟨hsum, -, -, -, -, -, -, hlin, hread, -⟩ :=
    hholo n hn O H.isOpen (fun _ => c) G hconst H.holomorphic
  have hGh : ComplexVariables.IsHolomorphicScalar O (D.logPartitionFun f) := by
    rw [hG]
    exact hsum.1 1
  have hformed := (hholo n hn O H.isOpen _ _ hGh hGh).2.2.2.2.2.2.1.1
  have hmix : TorusBoundNotation.mixedDeriv (D.logPartitionFun f) 0 =
      TorusBoundNotation.mixedDeriv G 0 := by
    rw [hG, hlin.1 1 H.zero_mem]
    beta_reduce
    rw [(hread ⟨0, hn⟩ fun _ _ _ _ _ => rfl).2 H.zero_mem]
    simp
  refine ⟨fun z => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hw := (hdisc D f 1 hf one_pos).2.1 z
    rw [← hR.2.2 _ hw]
    show ∫ U, _ ∂wilsonGibbsMeasure D.L D.m D.K D.β = ∫ U, _ ∂wilsonGibbsMeasure D.L D.m D.K D.β
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    exact congrArg Complex.exp (smearedObservable_complexSource f z U).symm
  · rw [hgen]
    exact H.entire
  · rw [hgen]
    exact H.value_at_zero
  · rw [hdom]
    exact H.isOpen
  · rw [hdom]
    exact H.zero_mem
  · rw [hdom, hlog]
    exact H.holomorphic
  · rw [hdom]
    exact hformed
  · rw [hmix, hcum]
    exact H.cumulant_eq
  · rintro ⟨i, hi⟩
    rw [hcum]
    refine Hz i ?_
    have h0 : (fun U => D.obs (f i) U) = 0 := by
      funext U
      simp [smearedObservable_eq_sum, hi]
    unfold restrictedObservable
    rw [h0]
    exact indicator_zero' _
end SourceFamily
theorem statement_holds (hdensity : PeriodicLattice.GaugeFieldSpace.FieldSpaceAndPartitionBounds)
    (hdisc : SourceDiskAndClass.Statement)
    (hent : Cumulants.GeneratingLog.EntireAndLogCumulant)
    (hholo : SeveralComplexVariables.HolomorphicCalculusRules)
    (hweight : PeriodicLattice.WilsonWeightGaugeInvariance.statement) : Statement := by
  intro D
  obtain ⟨hS, hB, -⟩ := hdensity D.toStandingParameters
  obtain ⟨hD, hN⟩ := hB D.β D.β_pos
  have hL : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  obtain ⟨-, -, -, -, -, -, -, hprob, hc, -⟩ := hweight D.L D.m D.K D.β hL D.m.pos D.K.pos
  have hR := partitionRatio D hS hN
  refine ⟨observableProperties D hS hD, hR, fun n f hf => ?_⟩
  have : IsProbabilityMeasure D.gibbs := hprob
  exact familyGeneratingFunProperties D f hf.1 hf hS hD hR hc hdisc hent hholo
end YangMills.Construction.TorusBound.ObservableCumulants
end
