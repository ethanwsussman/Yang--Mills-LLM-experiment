import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsOfSeveralVariablesProof
import YangMills.Construction.Cumulants.CumulantLessTheMixedDerivativeOfACounterterm
import YangMills.Construction.Lattice.FirstConsequencesOfTheFiveProperties
import YangMills.Construction.Lattice.MixedDerivativeOfTheTotalSourceEnergy
import YangMills.Construction.Lattice.ObservableGeneratingFunctionAndConnectedFunctions
import YangMills.Construction.Lattice.SourceDiscAndSourceClass
import YangMills.Construction.Lattice.SublevelSetsAndSourceDiscs
import YangMills.Construction.Lattice.TorusBound
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.LawInAState.GridDataAtEveryExponentProofForm
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.TorusBound
open PeriodicLattice
local instance : SecondCountableTopology Matrices.ComplexMatrix2 :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
section UltravioletConstant
variable (hS : ScaleSumBounds) (c : ConstantParameters)
include hS
theorem uvConstant_lt_top {d : ℝ} (hd : 0 < d) : c.uvConstant d < ⊤ := by
  have hsum := (hS.1 c).2.1 d hd
  unfold ConstantParameters.uvConstant
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (c.volumeTerm_nonneg d) hsum]
  exact ENNReal.ofReal_lt_top
theorem uvConstant_wellBehaved : c.UVConstantWellBehaved where
  pos d hd := (hS.1 c).2.2.2.1 d hd
  lt_top _ hd := uvConstant_lt_top hS c hd
  antitoneOn := (hS.1 c).2.2.2.2.1
  eq_of_params c' h₁ h₂ h₃ h₄ d hd := hS.2.2.1 c' c h₁ h₂ h₃ h₄ d hd
  satisfies d hd := (hS.1 c).2.2.2.2.2.2.1 d hd
  uvBound_eq_of_params c' h₂ h₃ h₄ := hS.2.1 c' c h₂ h₃ h₄
theorem ofReal_uvReal {d : ℝ} (hd : 0 < d) :
    ENNReal.ofReal (c.uvReal d) = c.uvConstant d :=
  ENNReal.ofReal_toReal (uvConstant_lt_top hS c hd).ne
omit hS in
theorem uvReal_nonneg (d : ℝ) : 0 ≤ c.uvReal d := ENNReal.toReal_nonneg
theorem truncatedConstant_antitoneOn_Ioi {ϱ : ℝ} (hϱ : 0 < ϱ) (n : ℕ) :
    AntitoneOn (c.truncatedConstant ϱ n) (Ioi 0) := by
  intro a ha b _ hab
  have h : c.uvReal b ≤ c.uvReal a :=
    ENNReal.toReal_mono (uvConstant_lt_top hS c ha).ne ((hS.1 c).2.2.2.2.1 ha ‹_› hab)
  have hr : 0 ≤ ((n : ℝ) / ϱ) ^ n := by positivity
  unfold ConstantParameters.truncatedConstant
  exact mul_le_mul_of_nonneg_right (by linarith) hr
end UltravioletConstant
theorem truncatedCoeff_le_volumeCoeff (c : ConstantParameters) {ϱ : ℝ} (hϱ : 0 < ϱ) {n : ℕ}
    (hn : 2 ≤ n) (d ℓ : ℝ) (hQ : 1 ≤ c.partitionBound ℓ) :
    c.truncatedCoeff ϱ n d (ℓ ^ 4) (c.partitionBound ℓ) ≤ c.volumeCoeff ϱ n d (ℓ ^ 4) := by
  set v := ℓ ^ 4 with hv
  have hv0 : 0 ≤ v := by positivity
  set u := c.uvReal d with hu
  have hu0 : 0 ≤ u := uvReal_nonneg c d
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcV : 1 / 2 ≤ c.volumeExponent := le_max_right _ _
  have hs : c.Eplus + c.Clow ≤ c.volumeExponent := le_max_left _ _
  have hncV : 1 ≤ (n : ℝ) * c.volumeExponent := by nlinarith
  set E := Real.exp ((n : ℝ) * c.volumeExponent * v) with hE
  have hvE : v ≤ E := by
    have h₁ : v + 1 ≤ Real.exp v := Real.add_one_le_exp v
    have h₂ : Real.exp v ≤ E := Real.exp_le_exp.2 (by nlinarith)
    linarith
  have hQE : c.partitionBound ℓ ^ n ≤ E := by
    unfold ConstantParameters.partitionBound
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    rw [← hv, ← mul_assoc]
    have hn0 : (0 : ℝ) ≤ n := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hn0) hv0
  have h₄ : (2 * c.partitionBound ℓ + 2) ^ n ≤ 4 ^ n * E := by
    calc (2 * c.partitionBound ℓ + 2) ^ n ≤ (4 * c.partitionBound ℓ) ^ n :=
          pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 4 ^ n * c.partitionBound ℓ ^ n := mul_pow _ _ _
      _ ≤ 4 ^ n * E := mul_le_mul_of_nonneg_left hQE (by positivity)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hr : 0 ≤ ((n : ℝ) / ϱ) ^ n := by positivity
  have hmain : v * u + Real.log 2 * (2 * c.partitionBound ℓ + 2) ^ n ≤
      (u + 4 ^ n * Real.log 2) * E := by
    have h₁ : v * u ≤ E * u := mul_le_mul_of_nonneg_right hvE hu0
    have h₂ := mul_le_mul_of_nonneg_left h₄ hlog
    nlinarith
  unfold ConstantParameters.truncatedCoeff ConstantParameters.volumeCoeff
    ConstantParameters.truncatedConstant
  calc (v * c.uvReal d + Real.log 2 * (2 * c.partitionBound ℓ + 2) ^ n) * ((n : ℝ) / ϱ) ^ n
      ≤ ((u + 4 ^ n * Real.log 2) * E) * ((n : ℝ) / ϱ) ^ n :=
        mul_le_mul_of_nonneg_right hmain hr
    _ = (c.uvReal d + 4 ^ n * Real.log 2) * ((n : ℝ) / ϱ) ^ n *
          Real.exp ((n : ℝ) * c.volumeExponent * v) := by
        rw [hE]
        ring
section HolomorphyOnOpenSets
variable {n : ℕ}
theorem isHolomorphicScalar_congr {O : Set (Coordinates.ComplexCoordinates n)}
    {F G : Coordinates.ComplexCoordinates n → ℂ}
    (hF : ComplexVariables.IsHolomorphicScalar O F) (h : EqOn F G O) :
    ComplexVariables.IsHolomorphicScalar O G := by apply _root_.YangMills.Construction.SeveralComplexVariables.isHolomorphicScalar_of_eqOn <;> assumption
end HolomorphyOnOpenSets
section BoundedObservables
variable {L m : ℕ} {j : ℤ}
theorem continuous_plaquetteEnergy (p : Plaquette L m j) :
    Continuous fun U : Bond L m j → Matrices.ComplexMatrix2 => plaquetteCost U p := by apply _root_.YangMills.Construction.EqualSideGridsAtEveryExponent.continuous_plaquetteCost <;> assumption
theorem smearedObservable_eq_sum [Fintype (Plaquette L m j)] (g : FourTorus L m → ℝ)
    (U : Bond L m j → Matrices.ComplexMatrix2) :
    smearedObservable g U = ∑ p : Plaquette L m j, plaquetteCost U p • g p.barycenter :=
  finsum_eq_sum_of_fintype _
theorem continuous_smearedObservable [Fintype (Plaquette L m j)] (g : FourTorus L m → ℝ) :
    Continuous fun U : Bond L m j → Matrices.ComplexMatrix2 => smearedObservable g U := by
  simp only [smearedObservable_eq_sum]
  exact continuous_finsetSum _ fun p _ => (continuous_plaquetteEnergy p).smul continuous_const
end BoundedObservables
theorem exists_boundedRV_eq_obs (D : Setup)
    (hfin : Finite (Plaquette D.L D.m ((D.K : ℕ) : ℤ)))
    (hW : ∀ U ∈ compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ), ∀ p,
      plaquetteCost U p ∈ Icc (0 : ℝ) 2)
    (g : D.Torus → ℝ) :
    ∃ X : D.LinkConfig → ℝ, Probability.IsBoundedRealRV X ∧
      ∀ U ∈ compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ), X U = D.obs g U := by
  let : Fintype (Plaquette D.L D.m ((D.K : ℕ) : ℤ)) := @Fintype.ofFinite _ hfin
  set C : ℝ := ∑ p : Plaquette D.L D.m ((D.K : ℕ) : ℤ), 2 * |g p.barycenter| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun p _ => by positivity
  have hbound : ∀ U ∈ compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ), |D.obs g U| ≤ C := by
    intro U hU
    show |smearedObservable g U| ≤ C
    rw [smearedObservable_eq_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    have hp := hW U hU p
    rw [smul_eq_mul, abs_mul, abs_of_nonneg hp.1]
    exact mul_le_mul_of_nonneg_right hp.2 (abs_nonneg _)
  refine ⟨fun U => max (-C) (min C (D.obs g U)), ⟨?_, C, fun U => ?_⟩, fun U hU => ?_⟩
  · have hc : Continuous fun U : D.LinkConfig => D.obs g U := continuous_smearedObservable g
    exact (continuous_const.max (continuous_const.min hc)).measurable
  · rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · have h := abs_le.mp (hbound U hU)
    show max (-C) (min C (D.obs g U)) = D.obs g U
    rw [min_eq_right h.2, max_eq_right h.1]
section RadiusFamilyRatio
variable {D : Setup} {ϱ : ℝ} {hϱ : 0 < ϱ} (e : D.RadiusFamily ϱ hϱ) {n : ℕ}
  (f : Fin n → D.Torus → ℝ) (hf : D.IsRealFamily f)
theorem energyOnDisc_of_mem {z : Fin n → ℂ} (hz : z ∈ D.disc ϱ f) :
    energyOnDisc e f hf z = e.totalEnergy ⟨D.smear z f, smear_mem_sources f hf hz⟩ :=
  dif_pos hz
theorem partitionRatio_of_mem {z : Fin n → ℂ} (hz : z ∈ D.disc ϱ f) :
    partitionRatio e f hf z = e.normalizedZ ⟨D.smear z f, smear_mem_sources f hf hz⟩ /
      e.normalizedZ (D.zeroSourceAt ϱ hϱ) :=
  dif_pos hz
theorem partitionRatio_eq_asExpectation
    (hzero : e.normalizedZ (D.zeroSourceAt ϱ hϱ) =
      Complex.exp (-(e.vacuumTerm : ℂ)) * D.partitionFun 0)
    (hZ0 : D.partitionFun 0 ≠ 0)
    (hΓ : ∀ z, D.familyGeneratingFun f z = D.partitionFun (D.smear z f) / D.partitionFun 0)
    {z : Fin n → ℂ} (hz : z ∈ D.disc ϱ f) :
    partitionRatio e f hf z = partitionRatioAsExpectation e f hf z := by
  have hE : Complex.exp (-(e.vacuumTerm : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hG : (D.expect fun U =>
      Complex.exp (∑ i, z i * ((D.obs (f i) U : ℝ) : ℂ))) =
      D.partitionFun (D.smear z f) / D.partitionFun 0 := hΓ z
  rw [partitionRatio_of_mem e f hf hz, hzero]
  unfold partitionRatioAsExpectation
  rw [energyOnDisc_of_mem e f hf hz, hG]
  unfold Setup.RadiusFamily.normalizedZ
  rw [sub_eq_add_neg, Complex.exp_add]
  field_simp
theorem norm_partitionRatio_le {Eplus Clow : ℝ} (hS : e.UpperStable Eplus)
    (hF : e.FloorBounded Clow) {z : Fin n → ℂ} (hz : z ∈ D.disc ϱ f) :
    ‖partitionRatio e f hf z‖ ≤ Real.exp ((Eplus + Clow) * D.side ^ 4) := by
  rw [partitionRatio_of_mem e f hf hz, norm_div]
  have hnum := hS ⟨D.smear z f, smear_mem_sources f hf hz⟩
  have hden : Real.exp (-Clow * D.side ^ 4) ≤
      ‖e.normalizedZ (D.zeroSourceAt ϱ hϱ)‖ :=
    hF.2.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hexp : Real.exp ((Eplus + Clow) * D.side ^ 4) =
      Real.exp (Eplus * D.side ^ 4) / Real.exp (-Clow * D.side ^ 4) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hexp]
  exact div_le_div₀ (Real.exp_pos _).le hnum (Real.exp_pos _) hden
end RadiusFamilyRatio
theorem torusBoundHolds_of_ingredients
    (hSums : ScaleSumBounds)
    (hMixed : TotalEnergyDerivative.MixedDerivBound)
    (hCum : Cumulants.CumulantNearCountertermDeriv)
    (hSub : SublevelSets.SublevelAndDiskStatement)
    (hFirst : Consequences.AllHold)
    (hObs : ObservableCumulants.Statement)
    (hHolo : SeveralComplexVariables.HolomorphicCalculusRules)
    (hDisc : SourceDiskAndClass.Statement)
    (hDensity : GaugeFieldSpace.FieldSpaceAndPartitionBounds)
    (hWeight : WilsonWeightGaugeInvariance.statement) : TorusBoundHolds := by
  refine ⟨fun c => uvConstant_wellBehaved hSums c, ?_⟩
  intro D Ce κe Eplus Clow ϱ hCe hκe hϱ e hL hA hB hUp hFl n f hf
  refine ⟨fun D' h₁ h₂ => ?_, ?_⟩
  · simp only [ConstantParameters.ofSetup, h₁, h₂]
  set c := ConstantParameters.ofSetup D Ce κe Eplus Clow hCe hκe with hc
  have hn : 1 ≤ n := hf.1
  obtain ⟨hNorms, -, hOpen, -, -, hMem0, -, -⟩ := hDisc D f ϱ hf hϱ
  obtain ⟨-, hRatio, hSys⟩ := hObs D
  obtain ⟨hΓeq, hΓent, hΓ0, -, -, -, -, -, hvanish⟩ := hSys n f hf
  obtain ⟨-, hValue, hAdd, -, -, -⟩ := hFirst D ϱ hϱ e Eplus Clow
  obtain ⟨-, hZzero, -, -⟩ := hValue hL
  have hsum := hAdd hUp hFl
  obtain ⟨hHol, hZero, hBound⟩ := hMixed D ϱ hϱ Ce κe hCe hκe e hL hA hB n f hf
  have hHol' : ComplexVariables.IsHolomorphicScalar (D.disc ϱ f) (energyOnDisc e f hf) := hHol
  have hZero' : energyOnDisc e f hf 0 = 0 := hZero
  have hZ0 : D.partitionFun 0 ≠ 0 := by
    rw [hRatio.1]
    exact_mod_cast hRatio.2.1.ne'
  have hv0 : 0 ≤ D.side ^ 4 := by positivity
  have hQ1 : 1 ≤ c.partitionBound D.side := Real.one_le_exp (mul_nonneg hsum hv0)
  have hprod0 : 0 ≤ ∏ i, D.sharpNorm (f i) :=
    Finset.prod_nonneg fun i _ => (hNorms i).2.2.2.1
  have hquot : ∀ z ∈ D.disc ϱ f, partitionRatio e f hf z = partitionRatioAsExpectation e f hf z :=
    fun z hz => partitionRatio_eq_asExpectation e f hf hZzero hZ0 hΓeq hz
  have hquotBound : ∀ z ∈ D.disc ϱ f, ‖partitionRatio e f hf z‖ ≤ c.partitionBound D.side :=
    fun z hz => norm_partitionRatio_le e f hf hUp hFl hz
  have hΓd : ComplexVariables.IsHolomorphicScalar (D.disc ϱ f) (D.familyGeneratingFun f) :=
    (hHolo n hn univ isOpen_univ _ _ hΓent hΓent).2.1 _ hOpen (subset_univ _)
  have hneg := (hHolo n hn _ hOpen _ _ hHol' hHol').1.1 (-2)
  have hexp := (hHolo n hn _ hOpen _ _ hneg hneg).1.2.2
  have hprod := (hHolo n hn _ hOpen _ _ hexp hΓd).1.2.1
  have hquotHol : ComplexVariables.IsHolomorphicScalar (D.disc ϱ f) (partitionRatio e f hf) := by
    refine isHolomorphicScalar_congr hprod fun z hz => ?_
    rw [hquot z hz]
    show Complex.exp (energyOnDisc e f hf z + -2 * energyOnDisc e f hf z) *
      D.familyGeneratingFun f z = Complex.exp (-energyOnDisc e f hf z) *
        D.familyGeneratingFun f z
    congr 2
    ring
  have hMixedBound : ∀ d : ℝ, 2 ≤ n → TestFunctions.HasSeparatedSupportsTorus f d →
      ‖TorusBoundNotation.mixedDeriv (energyOnDisc e f hf) 0‖ ≤
        c.mixedDerivCoeff ϱ n d (D.side ^ 4) * ∏ i, D.sharpNorm (f i) := by
    intro d hn2 hsep
    have hd : 0 < d := hsep.1
    have h := (hBound hn2 d hsep).1
    have hu : (ConstantParameters.ofSetup D Ce κe 0 0 hCe hκe).uvConstant d = c.uvConstant d :=
      hSums.2.2.1 _ _ rfl rfl rfl rfl d hd
    have hu0 := uvReal_nonneg c d
    have hb0 : 0 ≤ TotalEnergyDerivative.sharpNormFactor D ϱ f :=
      mul_nonneg (by positivity) hprod0
    rw [hu, ← ofReal_uvReal hSums c hd, ← ENNReal.ofReal_mul hv0,
      ← ENNReal.ofReal_mul (mul_nonneg hv0 hu0),
      ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hv0 hu0) hb0)] at h
    have hfac : c.mixedDerivCoeff ϱ n d (D.side ^ 4) * ∏ i, D.sharpNorm (f i) =
        D.side ^ 4 * c.uvReal d * TotalEnergyDerivative.sharpNormFactor D ϱ f := by
      unfold ConstantParameters.mixedDerivCoeff TotalEnergyDerivative.sharpNormFactor
      ring
    rw [hfac]
    exact h
  have hL1 : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  obtain ⟨hW, -, -, -, -, -, -, hprob, hcarried, -⟩ :=
    hWeight D.L D.m D.K D.β hL1 D.m.pos D.K.pos
  have hfin := (hDensity D.toStandingParameters).1.2.1
  have hConnected : ∀ d : ℝ, 2 ≤ n → TestFunctions.HasSeparatedSupportsTorus f d →
      ‖D.truncatedCorrelation f‖ ≤
        c.truncatedCoeff ϱ n d (D.side ^ 4) (c.partitionBound D.side) *
          ∏ i, D.sharpNorm (f i) := by
    intro d hn2 hsep
    have hu0 := uvReal_nonneg c d
    have hfac0 : 0 ≤ c.truncatedCoeff ϱ n d (D.side ^ 4) (c.partitionBound D.side) := by
      unfold ConstantParameters.truncatedCoeff
      positivity
    by_cases hz : ∃ i, ∀ x, f i x = 0
    · rw [hvanish hz, norm_zero]
      exact mul_nonneg hfac0 hprod0
    · push Not at hz
      have hpos : ∀ i, 0 < D.sharpNorm (f i) := fun i =>
        lt_of_le_of_ne (hNorms i).2.2.2.1 fun h => by
          obtain ⟨x, hx⟩ := hz i
          exact hx ((hNorms i).2.2.2.2 h.symm x)
      obtain ⟨a, -, hda, -, hna⟩ := hSub.2 D n f ϱ hf hpos hϱ
      choose X hX hXe using fun i =>
        exists_boundedRV_eq_obs D hfin (fun U hU p => (hW U hU p).1) (f i)
      have : IsProbabilityMeasure D.gibbs := hprob
      have hae : ∀ᵐ U ∂D.gibbs, U ∈ compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) :=
        mem_ae_iff.mpr hcarried
      have hgenObs : Cumulants.momentGeneratingFunction D.gibbs X =
          Cumulants.momentGeneratingFunction D.gibbs fun i => D.obs (f i) := by
        funext z
        unfold Cumulants.momentGeneratingFunction
        refine integral_congr_ae (hae.mono fun U hU => ?_)
        simp only [hXe _ U hU]
      have hgenΓ : ∀ z, Cumulants.momentGeneratingFunction D.gibbs X z =
          D.familyGeneratingFun f z := fun z => by
        rw [hgenObs]
        rfl
      have hcumEq : Cumulants.mixedCumulant D.gibbs X = D.truncatedCorrelation f := by
        unfold Setup.truncatedCorrelation gibbsCumulant Cumulants.mixedCumulant
        rw [hgenObs]
      have hbd : ∀ z ∈ a.unitSet, ‖Complex.exp (-energyOnDisc e f hf z) *
          Cumulants.momentGeneratingFunction D.gibbs X z‖ ≤ c.partitionBound D.side := by
        intro z hz'
        rw [← hda] at hz'
        have h := hquotBound z hz'
        rw [hquot z hz'] at h
        rw [hgenΓ]
        exact h
      have hHolA : ComplexVariables.IsHolomorphicScalar a.unitSet (energyOnDisc e f hf) := by
        rw [← hda]
        exact hHol'
      have h := hCum n a D.LinkConfig D.gibbs X (energyOnDisc e f hf) (c.partitionBound D.side) hX
        hHolA hZero' hbd
      rw [hcumEq, mul_assoc (Real.log 2 * _), hna] at h
      have hm := hMixedBound d hn2 hsep
      have htri : ‖D.truncatedCorrelation f‖ ≤
          ‖D.truncatedCorrelation f - TorusBoundNotation.mixedDeriv (energyOnDisc e f hf) 0‖ +
            ‖TorusBoundNotation.mixedDeriv (energyOnDisc e f hf) 0‖ := by
        simpa using norm_add_le
          (D.truncatedCorrelation f - TorusBoundNotation.mixedDeriv (energyOnDisc e f hf) 0)
          (TorusBoundNotation.mixedDeriv (energyOnDisc e f hf) 0)
      have hsplit : c.truncatedCoeff ϱ n d (D.side ^ 4) (c.partitionBound D.side) *
            ∏ i, D.sharpNorm (f i) =
          Real.log 2 * (2 * c.partitionBound D.side + 2) ^ n *
              (((n : ℝ) / ϱ) ^ n * ∏ i, D.sharpNorm (f i)) +
            c.mixedDerivCoeff ϱ n d (D.side ^ 4) * ∏ i, D.sharpNorm (f i) := by
        unfold ConstantParameters.truncatedCoeff ConstantParameters.mixedDerivCoeff
        ring
      rw [hsplit]
      linarith
  exact
    { energy_holomorphic := hHol'
      energy_zero := hZero'
      mixed_bound := fun d hn2 hsep =>
        ⟨(hHolo n hn _ hOpen _ _ hHol' hHol').2.2.2.2.2.2.1.1, hMixedBound d hn2 hsep⟩
      ratio_holomorphic := hquotHol
      ratio_zero := by
        rw [hquot 0 hMem0]
        show Complex.exp (-energyOnDisc e f hf 0) * D.familyGeneratingFun f 0 = 1
        rw [hZero', hΓ0]
        simp
      ratio_bound := hquotBound
      ratio_eq := hquot
      one_le_partitionBound := hQ1
      truncated_bound := hConnected
      volume_bound := fun d hn2 _ =>
        mul_le_mul_of_nonneg_right (truncatedCoeff_le_volumeCoeff c hϱ hn2 d D.side hQ1) hprod0
      eq_of_sum := fun c' h =>
        ⟨by unfold ConstantParameters.volumeExponent; rw [h],
          fun ℓ => by unfold ConstantParameters.partitionBound; rw [h]⟩
      truncatedConstant_eq_of_params := fun c' h₁ h₂ h₃ h₄ d hd => by
        have h : c'.uvConstant d = c.uvConstant d := hSums.2.2.1 c' c h₁ h₂ h₃ h₄ d hd
        unfold ConstantParameters.truncatedConstant ConstantParameters.uvReal
        rw [h]
      truncatedConstant_antitoneOn := fun _ => truncatedConstant_antitoneOn_Ioi hSums c hϱ n }
end YangMills.Construction.TorusBound
end
