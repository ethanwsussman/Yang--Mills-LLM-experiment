import YangMills.Construction.InfiniteLattice.DescentOfAnArrayToATorusIsDefined
import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfATorusIsFaithful
import YangMills.Construction.InfiniteLattice.TorusOfAPeriodLatticeIsFaithful
import YangMills.Construction.ReflectionPositivity.ReflectionPreservesThePerturbedMeasuresProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace PeriodicDescentDefined
theorem isProbabilityMeasure_normalizedDensity {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (g : X → ℝ) (hg : ∀ x, 0 ≤ g x) (hgi : Integrable g μ) (hgpos : 0 < ∫ x, g x ∂μ) :
    IsProbabilityMeasure ((ENNReal.ofReal (∫ x, g x ∂μ))⁻¹ •
      μ.withDensity fun x => ENNReal.ofReal (g x)) := by
  refine ⟨?_⟩
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg), smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simpa using hgpos) ENNReal.ofReal_ne_top
theorem actOn_shift_add (x y : LatticePoint 1) (F : GaugeField 1 → ℂ) :
    (shift (x + y)).actOn F =
      (shift y).actOn ((shift x).actOn F) := by
  funext U
  refine congrArg F (Subtype.ext (funext fun ℓ => congrArg U.1 ?_))
  apply Link.ext <;> apply Subtype.ext <;>
    simp [LatticeSymmetry.linkMap, LatticeSymmetry.pointMap, shift, add_assoc]
variable (A : LocalObservableArray) (Λ : PeriodSublattice 1)
theorem borelSpace_quotientField : BorelSpace Λ.QuotientField := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  exact Pi.borelSpace
theorem isProbabilityMeasure_quotientHaar : IsProbabilityMeasure Λ.quotientHaar := by apply _root_.YangMills.Construction.InfiniteLattice.PerturbedReflInvariance.quotientHaar_isProbabilityMeasure <;> assumption
theorem integrable_of_continuous {g : Λ.QuotientField → ℝ} (hg : Continuous g) :
    Integrable g Λ.quotientHaar := by
  have := borelSpace_quotientField Λ
  have := isProbabilityMeasure_quotientHaar Λ
  exact hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
theorem translate_mem (facts : ElementaryLatticeFacts) (i : A.Label) :
    A.translate i ∈ continuousLocalFunctions 1 := by
  have h := (facts 1 1 one_pos one_pos).2.2.2.2.2.2.2.1 (shift (i.1 : LatticePoint 1))
    (shift (i.1 : LatticePoint 1))
  rw [← h.2.2.2.2.1]
  exact mem_image_of_mem _ (A.gen_mem i.2)
theorem continuous_periodicSum [Finite (A.Cosets Λ)] (lift : Λ.LiftIsFaithful)
    (facts : ElementaryLatticeFacts) :
    Continuous (A.periodicSum Λ) :=
  continuous_finsum
    (fun _ => Complex.continuous_re.comp
      (lift.continuous_periodize _ (translate_mem A facts _)))
    (locallyFinite_of_finite _)
theorem continuous_tiltedWeight [Finite (A.Cosets Λ)] [Finite Λ.QuotientPlaquette]
    (lift : Λ.LiftIsFaithful) (facts : ElementaryLatticeFacts)
    (β t : ℝ) : Continuous (A.tiltedWeight Λ β t) := by
  have hS := continuous_periodicSum A Λ lift facts
  have hP : Continuous fun U => ∑ᶠ p : Λ.QuotientPlaquette, Λ.quotientFaceEnergy U p :=
    continuous_finsum (fun p => lift.continuous_quotientFaceEnergy p) (locallyFinite_of_finite _)
  exact Real.continuous_exp.comp ((continuous_const.mul hS).sub (continuous_const.mul hP))
theorem tiltedWeight_zero (β : ℝ) : A.tiltedWeight Λ β 0 = Λ.boltzmannWeight β := by
  funext U
  simp [LocalObservableArray.tiltedWeight, PeriodSublattice.boltzmannWeight]
end PeriodicDescentDefined
open PeriodicDescentDefined in
theorem PeriodicDescentDefined.proof
    (faithful : QuotientTorusFaithful.Statement)
    (lift : PeriodicLiftIsFaithful)
    (facts : ElementaryLatticeFacts) :
    PeriodicDescentDefined.Statement := by
  intro β _ A t Λ _
  have hF := faithful 1 one_pos Λ
  have hL := lift 1 one_pos Λ
  have : Λ.periods.FiniteIndex := hF.periods_finiteIndex
  have : Finite Λ.QuotientPlaquette := hF.finite_quotientPlaquette
  have := borelSpace_quotientField Λ
  have := isProbabilityMeasure_quotientHaar Λ
  have hC : Finite (A.Cosets Λ) := AddSubgroup.finite_quotient_of_finiteIndex
  have hS := continuous_periodicSum A Λ hL facts
  have hw := continuous_tiltedWeight A Λ hL facts β t
  have hint : Integrable (A.tiltedWeight Λ β t) Λ.quotientHaar := integrable_of_continuous Λ hw
  have hpos : 0 < A.tiltedPartition Λ β t := integral_exp_pos hint
  have hprob : IsProbabilityMeasure (A.tiltedMeasure Λ β t) :=
    isProbabilityMeasure_normalizedDensity _ _ (fun _ => (Real.exp_pos _).le) hint hpos
  have hzero : A.tiltedPartition Λ β 0 = Λ.partitionFunction β := by
    unfold LocalObservableArray.tiltedPartition PeriodSublattice.partitionFunction
    rw [tiltedWeight_zero A Λ β]
  refine ⟨hC, ?_, hS, ?_, hpos, hprob, ?_, hzero, ?_⟩
  · intro x y ι h
    have hmem : ((-x + y : A.sublattice) : LatticePoint 1) ∈ Λ.periods :=
      AddSubgroup.mem_addSubgroupOf.mp (QuotientAddGroup.eq.mp h)
    have hy : (y : LatticePoint 1) = (x : LatticePoint 1) + ((-x + y : A.sublattice) : LatticePoint 1) := by
      simp
    change Λ.periodize ((shift (x : LatticePoint 1)).actOn (A.gen ι)) =
      Λ.periodize ((shift (y : LatticePoint 1)).actOn (A.gen ι))
    rw [hy, actOn_shift_add]
    exact (hL.periodize_actOn_shift _ (translate_mem A facts (x, ι)) _ hmem).symm
  · obtain ⟨C, hC'⟩ := isCompact_univ.exists_bound_of_continuousOn hS.continuousOn
    exact ⟨C, fun U => by simpa using hC' U (mem_univ U)⟩
  · exact Measure.isProbabilityMeasure_map hL.isEmbedding_lift.continuous.measurable.aemeasurable
  · unfold LocalObservableArray.tiltedMeasure PeriodSublattice.gibbsMeasure
    rw [hzero, tiltedWeight_zero A Λ β]
end YangMills.Construction.InfiniteLattice
