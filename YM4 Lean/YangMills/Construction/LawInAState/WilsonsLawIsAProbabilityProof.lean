import YangMills.Construction.Lattice.CombGaugeRoundACoarsePlaquetteProof
import YangMills.Construction.Lattice.WilsonWeightGaugeInvarianceProof
import YangMills.Construction.LawInAState.WilsonsLawIsAProbability
import YangMills.Construction.SystemOfAdmissibleConstants.SizeOfAnObservableOnABallProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace YangMills.Construction.WilsonLaw
open PeriodicLattice
variable {L m : ℕ} {j : ℤ}
private theorem site_finite (hL : 0 < L) (K : ℕ) : Finite (Site L m (K : ℤ)) := by apply _root_.YangMills.Construction.PeriodicLattice.WilsonWeightGaugeInvariance.site_finite <;> assumption
private theorem plaquette_finite [Finite (Site L m j)] : Finite (Plaquette L m j) := by apply _root_.YangMills.Construction.GradLaplacianCommutation.plaquette_finite <;> assumption
private theorem gaugeFieldOfPositive_mem
    (v : PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) (b : Bond L m j) :
    gaugeFieldOfPositive v b ∈ Matrices.ComplexMatrix2.specialUnitary := by apply _root_.YangMills.SharedProofs.p42206 <;> assumption
private theorem measurable_gaugeFieldOfPositive :
    Measurable (gaugeFieldOfPositive : (PositivelyOrientedBond L m j → Matrices.ComplexMatrix2.specialUnitary) →
      Bond L m j → Matrices.ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.measurable_gaugeFieldOfPositive <;> assumption
private theorem isProbability_productHaarMeasure : IsProbabilityMeasure (productHaarMeasure L m j) := by apply _root_.YangMills.Construction.PeriodicLattice.WilsonWeightGaugeInvariance.isProbabilityMeasure_productHaarMeasure <;> assumption
private theorem pathHolonomy_mem {U : Bond L m j → Matrices.ComplexMatrix2}
    (hU : ∀ b, U b ∈ Matrices.ComplexMatrix2.specialUnitary)
    (Γ : List (Bond L m j)) : pathHolonomy U Γ ∈ Matrices.ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.PeriodicLattice.CoarsePlaquetteGauge.pathHolonomy_mem <;> assumption
private theorem abs_plaquetteCost_le {U : Bond L m j → Matrices.ComplexMatrix2}
    (hU : ∀ b, U b ∈ Matrices.ComplexMatrix2.specialUnitary)
    (p : Plaquette L m j) : |plaquetteCost U p| ≤ 2 := by
  have hV := pathHolonomy_mem hU p.boundaryBonds
  have hW : pathHolonomy U p.boundaryBonds ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.1 hV).1
  have h0 := entry_norm_bound_of_unitary hW 0 0
  have h1 := entry_norm_bound_of_unitary hW 1 1
  have htr : Matrices.ComplexMatrix2.fullTrace (pathHolonomy U p.boundaryBonds) =
      pathHolonomy U p.boundaryBonds 0 0 + pathHolonomy U p.boundaryBonds 1 1 := by
    simp [Matrices.ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
  have hre : |(Matrices.ComplexMatrix2.fullTrace (pathHolonomy U p.boundaryBonds)).re| ≤ 2 := by
    rw [htr, Complex.add_re]
    have a0 := Complex.abs_re_le_norm (pathHolonomy U p.boundaryBonds 0 0)
    have a1 := Complex.abs_re_le_norm (pathHolonomy U p.boundaryBonds 1 1)
    exact (abs_add_le _ _).trans (by linarith)
  have := abs_le.1 hre
  have e : plaquetteCost U p =
      1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (pathHolonomy U p.boundaryBonds)).re := rfl
  rw [e, abs_le]
  constructor <;> linarith [this.1, this.2]
private theorem continuous_boltzmannWeight [Finite (Plaquette L m j)] (β : ℝ) :
    Continuous (boltzmannWeight β : (Bond L m j → Matrices.ComplexMatrix2) → ℝ) := by apply _root_.YangMills.Construction.PeriodicLattice.WilsonWeightGaugeInvariance.continuous_boltzmannWeight <;> assumption
private theorem integrable_boltzmannWeight [Finite (Plaquette L m j)] (β : ℝ) :
    Integrable (boltzmannWeight β : (Bond L m j → Matrices.ComplexMatrix2) → ℝ)
      (productHaarMeasure L m j) := by
  have := Fintype.ofFinite (Plaquette L m j)
  have := isProbability_productHaarMeasure (L := L) (m := m) (j := j)
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hm := (continuous_boltzmannWeight (L := L) (m := m) (j := j) β).measurable
  refine Integrable.of_bound hm.aestronglyMeasurable
    (Real.exp (|β| * (2 * Fintype.card (Plaquette L m j)))) ?_
  unfold productHaarMeasure
  rw [ae_map_iff measurable_gaugeFieldOfPositive.aemeasurable
    (measurableSet_le (hm.norm) measurable_const)]
  refine Filter.Eventually.of_forall fun v => ?_
  have hU := gaugeFieldOfPositive_mem v
  unfold boltzmannWeight
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  have e : wilsonAction (gaugeFieldOfPositive v) =
      ∑ p, plaquetteCost (gaugeFieldOfPositive v) p := finsum_eq_sum_of_fintype _
  have h₁ : |wilsonAction (gaugeFieldOfPositive v)| ≤ 2 * Fintype.card (Plaquette L m j) := by
    rw [e]
    calc |∑ p, plaquetteCost (gaugeFieldOfPositive v) p|
        ≤ ∑ p, |plaquetteCost (gaugeFieldOfPositive v) p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p : Plaquette L m j, (2 : ℝ) :=
          Finset.sum_le_sum fun p _ => abs_plaquetteCost_le hU p
      _ = 2 * Fintype.card (Plaquette L m j) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          ring
  calc -β * wilsonAction (gaugeFieldOfPositive v)
      ≤ |-β * wilsonAction (gaugeFieldOfPositive v)| := le_abs_self _
    _ = |β| * |wilsonAction (gaugeFieldOfPositive v)| := by rw [abs_mul, abs_neg]
    _ ≤ _ := by gcongr
theorem liftedWilsonMeasure_isProbability : LiftedWilsonMeasureIsProbability := by
  intro L e K β hL
  have hL0 : 0 < L := by omega
  have : Finite (Site L e (K : ℤ)) := site_finite hL0 K
  have : Finite (Plaquette L e (K : ℤ)) := plaquette_finite
  have hprob := isProbability_productHaarMeasure (L := L) (m := e) (j := (K : ℤ))
  have hint := integrable_boltzmannWeight (L := L) (m := e) (j := (K : ℤ)) β
  have hZ : 0 < partitionFunction L e K β := integral_exp_pos hint
  have hW : IsProbabilityMeasure (wilsonGibbsMeasure L e K β) := by
    refine ⟨?_⟩
    have hmass : (productHaarMeasure L e (K : ℤ)).withDensity
        (fun U => ENNReal.ofReal (boltzmannWeight β U)) univ =
        ENNReal.ofReal (partitionFunction L e K β) := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact (ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun U => (Real.exp_pos _).le)).symm
    unfold wilsonGibbsMeasure
    rw [Measure.smul_apply, hmass, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simpa using hZ) ENNReal.ofReal_ne_top
  exact Measure.isProbabilityMeasure_map
    (InfiniteLattice.measurable_liftField L e (K : ℤ)).aemeasurable
end YangMills.Construction.WilsonLaw
end
