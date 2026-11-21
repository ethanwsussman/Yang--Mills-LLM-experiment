import Formulation.GibbsCalibration
import YangMills.Construction.Lattice.HaarAndGaugeInvarianceProof
import YangMills.Construction.Lattice.WilsonWeightGaugeInvarianceProof
import YangMills.Construction.Lattice.ObservableGeneratingFunctionAndConnectedFunctionsProof
import YangMills.Construction.TheStatementsProvedTogether.FromReflectedSeriesMultiplyProof

/-! The original periodic SU(2) model at one cutoff. Its connected two-point function is a continuous Wilson covariance and vanishes in the zero-temperature limit. -/

open MeasureTheory
namespace YangMills
open Construction Construction.PeriodicLattice

theorem connectedSchwinger_two_eq_covariance (s : Conventions.StandingParameters)
    (β : ℝ) (hβ : 0 < β) (f : Fin 2 → s.Torus → ℝ) :
    (SchwingerFunctions.connectedSchwinger s.L s.m s.K β f).re =
    (∫ U, smearedObservable (f 0) U * smearedObservable (f 1) U ∂wilsonGibbsMeasure s.L s.m s.K β) -
      (∫ U, smearedObservable (f 0) U ∂wilsonGibbsMeasure s.L s.m s.K β) *
      ∫ U, smearedObservable (f 1) U ∂wilsonGibbsMeasure s.L s.m s.K β := by
  let μ := LatticeProbability.gibbsMeasureOn s β
  let O := LatticeProbability.observableVector s f
  have hs := TheStatementsProvedTogether.lattice_gauge_probability_space s β hβ
  let : IsProbabilityMeasure μ := hs.1.2.2.1
  have hO (i : Fin 2) : Probability.IsBoundedRealRV (O i) := hs.2.2.2.1.1 (f i)
  have hco := (hs.2.2.2.2.1 2 f (by decide)).1
  change SchwingerFunctions.connectedSchwinger s.L s.m s.K β f =
    Cumulants.mixedCumulant μ O at hco
  have hv : O = ![O 0, O 1] := by funext i; fin_cases i <;> rfl
  rw [hco, hv, (TheStatementsProvedTogether.moment_generating_function_regular _ μ).2
    (O 0) (O 1) (hO 0).measurable (hO 1).measurable (hO 0).bounded (hO 1).bounded,
    Complex.ofReal_re]
  have equal (F : (Bond s.L s.m (s.K : ℤ) → Matrices.ComplexMatrix2) → ℝ)
      (hF : Probability.IsBoundedRealRV (fun U : LatticeProbability.GaugeConfig s => F U.1)) :
      (∫ U : LatticeProbability.GaugeConfig s, F U.1 ∂μ) = ∫ U, F U ∂wilsonGibbsMeasure s.L s.m s.K β := by
    have hf : Probability.IsBoundedComplexRV (fun U : LatticeProbability.GaugeConfig s => (F U.1 : ℂ)) :=
      ⟨hF.measurable, measurable_const, by simpa using hF.bounded⟩
    have he := hs.1.2.2.2.2.2 (fun U => (F U : ℂ)) hf
    change (∫ U, (F U : ℂ) ∂wilsonGibbsMeasure s.L s.m s.K β) =
      (∫ U : LatticeProbability.GaugeConfig s, (F U.1 : ℂ) ∂μ) at he
    exact Complex.ofReal_injective (integral_complex_ofReal.symm.trans (he.symm.trans integral_complex_ofReal))
  have prodBound : Probability.IsBoundedRealRV (fun U => O 0 U * O 1 U) := by
    obtain ⟨A,hA⟩ := (hO 0).bounded
    obtain ⟨B,hB⟩ := (hO 1).bounded
    exact ⟨(hO 0).measurable.mul (hO 1).measurable, ⟨A * B, fun U => by
      rw [abs_mul]; exact mul_le_mul (hA U) (hB U) (abs_nonneg _) ((abs_nonneg _).trans (hA U))⟩⟩
  exact congrArg₂ (· - ·) (equal (fun U => smearedObservable (f 0) U * smearedObservable (f 1) U) prodBound)
    (congrArg₂ (· * ·) (equal (fun U => smearedObservable (f 0) U) (hO 0)) (equal (fun U => smearedObservable (f 1) U) (hO 1)))

end YangMills

open Filter Set MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.ReferenceCalibration
open Construction Construction.PeriodicLattice Construction.Matrices
open TorusBound.ObservableCumulants

variable (s : Conventions.StandingParameters) (K : ℕ+)
private abbrev Fields := Bond s.L s.m ((K : ℕ) : ℤ) → ComplexMatrix2
private abbrev Links := PositivelyOrientedBond s.L s.m ((K : ℕ) : ℤ)
private abbrev Configs := Links s K → ComplexMatrix2.specialUnitary
private abbrev Faces := Plaquette s.L s.m ((K : ℕ) : ℤ)
private local instance : Fintype (Faces s K) := by
  classical
  exact @Fintype.ofFinite _ (WilsonPlaquetteSum.finite_plaquette (by have := s.isAdmissible.2; omega) K)
private local instance : Finite (Links s K) := by
  have := Counting.bond_finite (L := s.L) (m := (s.m : ℕ)) (j := ((K : ℕ) : ℤ))
    (by have := s.isAdmissible.2; omega) (by have := s.m.pos; omega)
  exact Subtype.finite
private local instance : IsProbabilityMeasure (ComplexMatrix2.haarPi (Links s K)) := by
  unfold ComplexMatrix2.haarPi
  infer_instance
private local instance : (ComplexMatrix2.haarPi (Links s K)).IsOpenPosMeasure :=
  ⟨fun U hU hne => (TheStatementsProvedTogether.ReflectionPositivityChain.haar_open_pos_fin_pow
    (Links s K) U hU hne).ne'⟩
private abbrev action (v : Configs s K) := wilsonAction (gaugeFieldOfPositive v)
private abbrev energy (f : FourTorus s.L s.m → ℝ) (U : Fields s K) := smearedObservable f U

private theorem cost_nonneg (v : Configs s K) (p : Faces s K) :
    0 ≤ plaquetteCost (gaugeFieldOfPositive v) p := by
  apply (WilsonWeightGaugeInvariance.plaquetteEnergy_mem_Icc _ p).1
  apply WilsonWeightGaugeInvariance.gaugeFieldOfPositive_mem _ v
  exact fun _ => Counting.not_isPositivelyOriented_opposite
    (by have := s.isAdmissible.2; omega) (by have := K.pos; have := s.m.pos; omega)

private theorem energy_at_min (f : FourTorus s.L s.m → ℝ) (v : Configs s K)
    (hv : action s K v = 0) : energy s K f (gaugeFieldOfPositive v) = 0 := by
  rw [action, wilsonAction_eq_sum] at hv
  rw [energy, smearedObservable_eq_sum]
  exact Finset.sum_eq_zero fun p hp => by
    rw [(Finset.sum_eq_zero_iff_of_nonneg (fun q _ => cost_nonneg s K v q)).mp hv p hp, zero_smul]

private theorem action_one : action s K 1 = 0 := by
  have hfield : gaugeFieldOfPositive (1 : Configs s K) = 1 := by
    funext b
    simp [gaugeFieldOfPositive]
  rw [action, hfield, wilsonAction_eq_sum]
  apply Finset.sum_eq_zero
  intro p _
  simp [plaquetteCost, plaquetteHolonomy, pathHolonomy, Plaquette.boundaryBonds,
    ComplexMatrix2.fullTrace, Matrix.trace]

private theorem expectation_formula (β : ℝ) (F : Fields s K → ℝ) :
    (∫ U, F U ∂wilsonGibbsMeasure s.L s.m K β) =
    (∫ v : Configs s K, F (gaugeFieldOfPositive v) * Real.exp (-β * action s K v)
      ∂ComplexMatrix2.haarPi (Links s K)) /
    (∫ v : Configs s K, Real.exp (-β * action s K v) ∂ComplexMatrix2.haarPi (Links s K)) := by
  have hZ : partitionFunction s.L s.m K β =
      ∫ v : Configs s K, Real.exp (-β * action s K v) ∂ComplexMatrix2.haarPi (Links s K) := by
    unfold partitionFunction productHaarMeasure
    rw [HaarWilsonInvarianceProof.measurableEmbedding_gaugeFieldOfPositive.integral_map]
    rfl
  have hz : 0 ≤ partitionFunction s.L s.m K β := by
    rw [hZ]
    exact integral_nonneg fun _ => (Real.exp_pos _).le
  rw [HaarWilsonInvarianceProof.integral_wilsonGibbsMeasure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hz, hZ, smul_eq_mul, div_eq_inv_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with v
  simp only [boltzmannWeight, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, action]
  ring

private theorem expectation_continuous (F : Fields s K → ℝ) (hF : Continuous F) :
    Continuous (fun β : ℝ => ∫ U, F U ∂wilsonGibbsMeasure s.L s.m K β) := by
  simp_rw [expectation_formula]
  let μ := ComplexMatrix2.haarPi (Links s K)
  have ha : Continuous (action s K) := continuous_wilsonAction.comp
    HaarWilsonInvarianceProof.continuous_gaugeFieldOfPositive
  have hw : Continuous (fun z : ℝ × Configs s K => Real.exp (-z.1 * action s K z.2)) :=
    Real.continuous_exp.comp (continuous_fst.neg.mul (ha.comp continuous_snd))
  have param {u : ℝ → Configs s K → ℝ} (hu : Continuous u.uncurry) :
      Continuous (fun b => ∫ v, u b v ∂μ) := by
    simpa using continuous_parametric_integral_of_continuous (μ := μ) hu (isCompact_univ (X := Configs s K))
  apply Continuous.div
  · apply param
    exact (((hF.comp HaarWilsonInvarianceProof.continuous_gaugeFieldOfPositive).comp continuous_snd).mul hw)
  · apply param
    exact hw
  · intro β
    apply ne_of_gt
    exact integral_exp_pos ((Real.continuous_exp.comp (continuous_const.mul ha)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

private theorem expectation_cold (F : Fields s K → ℝ) (hF : Continuous F)
    (hf : ∀ v, action s K v = 0 → F (gaugeFieldOfPositive v) = 0) :
    Tendsto (fun β : ℝ => ∫ U, F U ∂wilsonGibbsMeasure s.L s.m K β) atTop (𝓝 0) := by
  simp_rw [expectation_formula]
  apply Formulation.cold_gibbs_expectation
    (ComplexMatrix2.haarPi (Links s K)) (action s K) (fun v => F (gaugeFieldOfPositive v))
    (continuous_wilsonAction.comp HaarWilsonInvarianceProof.continuous_gaugeFieldOfPositive)
    (hF.comp HaarWilsonInvarianceProof.continuous_gaugeFieldOfPositive) _ 1 (action_one s K) hf
  intro v
  rw [action, wilsonAction_eq_sum]
  exact Finset.sum_nonneg fun p _ => cost_nonneg s K v p

def energyCovariance (f : Fin 2 → FourTorus s.L s.m → ℝ) (β : ℝ) :=
  let μ := wilsonGibbsMeasure s.L s.m K β
  (∫ U, energy s K (f 0) U * energy s K (f 1) U ∂μ) -
    (∫ U, energy s K (f 0) U ∂μ) * (∫ U, energy s K (f 1) U ∂μ)

theorem covariance_continuous (f : Fin 2 → FourTorus s.L s.m → ℝ) :
    Continuous (energyCovariance s K f) :=
  (expectation_continuous s K _ ((continuous_smearedObservable (f 0)).mul
    (continuous_smearedObservable (f 1)))).sub ((expectation_continuous s K _
    (continuous_smearedObservable (f 0))).mul (expectation_continuous s K _ (continuous_smearedObservable (f 1))))

theorem covariance_cold (f : Fin 2 → FourTorus s.L s.m → ℝ) :
    Tendsto (energyCovariance s K f) atTop (𝓝 0) := by
  have h (i : Fin 2) := expectation_cold s K _ (continuous_smearedObservable (f i))
    (energy_at_min s K (f i))
  have hp := expectation_cold s K _ ((continuous_smearedObservable (f 0)).mul
    (continuous_smearedObservable (f 1))) (fun v hv => by
      change energy s K (f 0) (gaugeFieldOfPositive v) * energy s K (f 1) (gaugeFieldOfPositive v) = 0
      rw [energy_at_min s K (f 0) v hv, zero_mul])
  unfold energyCovariance
  exact (show (0:ℝ) - 0 * 0 = 0 by norm_num) ▸ hp.sub ((h 0).mul (h 1))

theorem reference_covariance_eq (f : Fin 2 → FourTorus s.L s.m → ℝ) {β : ℝ} (hβ : 0 < β) :
    (SchwingerFunctions.connectedSchwinger s.L s.m K β f).re = energyCovariance s K f β :=
  YangMills.connectedSchwinger_two_eq_covariance ⟨s.L, s.isAdmissible, K, s.m⟩ β hβ f
end YangMills.ReferenceCalibration
end
