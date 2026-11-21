import Formulation.WilsonQuaternionModel
import Formulation.ContinuumLimit
import Formulation.ReferenceCoupling
import YangMills.Construction.TheStatementsProvedTogether.FromTheTopOfTheTrajectoryProof
import YangMills.Construction.Continuum.FactsOfCentredMomentsMirrorsClassesAndTheSeparatingFamilyProof

noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Wilson
open Construction Complex
open Construction.PeriodicLattice Construction.TorusFields
open Construction.ClusterExpansionOfAStep Construction.QuaternionModel

private theorem action_eq {N : ℕ} [NeZero N] (U : Field su2Model N) :
    action su2Model U = TorusFields.wilsonAction Finset.univ U := by
  symm
  exact Finset.sum_subtype _ (fun p => by simp [plaquettesIn]) _

private theorem law_eq (N : ℕ) [NeZero N] (β : ℝ) : law su2Model N β = WeightedResponses.wilsonLaw β N := by
  unfold law WeightedResponses.wilsonLaw
  simp_rw [action_eq]
  rfl

theorem bump_eq : bump = YangMills.fixedReferenceBump := by
  funext x
  simp [bump,YangMills.fixedReferenceBump, TopAux.NonemptyTestClasses.scaledBump,
    TopAux.NonemptyTestClasses.unitBump,Pi.smul_apply,smul_eq_mul]

theorem physicalLevel_eq (g₀ : ℝ) : fixedPhysicalLevel su2Model g₀ = YangMills.fixedPhysicalLevel g₀ := by
  norm_num [fixedPhysicalLevel, su2Model, YangMills.fixedPhysicalLevel, translatedBump,
    bump_eq, TorusMetric.euclidNormVec]

variable {L m K : ℕ} [NeZero L]
private abbrev embed := gaugeFieldOfTorusField (n:=siteCount L m K) L m (K:ℤ)

private theorem smear_eq (h : CubicTorusEmbedsInLattice L m K (siteCount L m K))
    (f : Point → ℝ) (W : Field su2Model (siteCount L m K)) :
    smearedObservable (TestFunctions.periodize (torusSide L m) f) (embed W) = smear su2Model L m K f W := by
  change TorusFields.TorusField (siteCount L m K) at W
  erw [h.smearedObservable_eq]
  unfold smear
  refine Finset.sum_congr rfl fun p _ => ?_
  have eqpos : (plaquetteOfOriented L m K p).barycenter = TorusMetric.torusProj (torusSide L m)
      (fun i => (((p.1.1 i).val : ℝ) + (if i = p.1.2.1 then 1/2 else 0) +
          (if i = p.1.2.2 then 1/2 else 0)) * meshSize L (K:ℤ)) := funext (h.barycenter_eq p)
  rw [eqpos, TestFunctions.periodize_torusProj]
  rfl

private theorem model_embedding (hL : 2 ≤ L) (hm : 1 ≤ m) :
    CubicTorusEmbedsInLattice L m K (siteCount L m K) :=
  TheStatementsProvedTogether.quaternion_model_eq_wilson_SU2.2.1 L m K _ rfl
    (TheStatementsProvedTogether.quaternion_model_eq_wilson_SU2.2.2.1 L m K hL hm).2

private theorem integral_on_fields {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : CubicTorusEmbedsInLattice L m K (siteCount L m K)) (β : ℝ)
    (F : (Bond L m (K:ℤ) → Matrices.ComplexMatrix2) → E)
    (hF : AEStronglyMeasurable F (wilsonGibbsMeasure L m K β)) :
    (∫ U, F U ∂wilsonGibbsMeasure L m K β) = ∫ W, F (embed W) ∂law su2Model (siteCount L m K) β := by
  rw [law_eq,h.wilsonGibbs_eq_map] at *
  exact integral_map h.fields.measurable_gaugeField.aemeasurable hF

private theorem centered_real_eq (β : ℝ) (hL : 2 ≤ L) (hm : 1 ≤ m) {n : ℕ} (f : Fin n → Point → ℝ) :
    let μ := wilsonGibbsMeasure L m K β
    let F := fun i => smearedObservable (j:=(K:ℤ)) (TestFunctions.periodize (torusSide L m) (f i))
    (∫ U, ∏ i, (F i U - ∫ V, F i V ∂μ) ∂μ) = centeredMoment su2Model L m K β f := by
  classical
  intro μ F
  have h : CubicTorusEmbedsInLattice L m K (siteCount L m K) := model_embedding hL hm
  let : Fintype (Plaquette L m (K:ℤ)) := Fintype.ofEquiv _ (Equiv.ofBijective _ h.plaquette_bijective)
  have hf i : Continuous (F i) := TorusBound.ObservableCumulants.continuous_smearedObservable _
  have he i : (∫ V, F i V ∂μ) = ∫ W, smear su2Model L m K (f i) W ∂law su2Model (siteCount L m K) β := by
    rw [integral_on_fields h β (F i) (hf i).aestronglyMeasurable]
    exact integral_congr_ae (.of_forall (smear_eq h (f i)))
  rw [integral_on_fields h β (fun U => ∏ i, (F i U - ∫ V, F i V ∂μ))
    ((continuous_finsetProd Finset.univ fun i _ => (hf i).sub continuous_const).aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards with W
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg₂ (· - ·) (smear_eq h (f i) W) (he i)

theorem centeredMoment_eq (β : ℝ) (hL : 2 ≤ L) (hm : 1 ≤ m) {n : ℕ}
    (X : TestSpaces.SepTupleOfCard n) :
    (centeredMoment su2Model L m K β X.1 : ℂ) = YangMills.su2_centeredMoment L m K β X := by
  rw [← centered_real_eq β hL hm]
  unfold YangMills.su2_centeredMoment gibbsExpectation
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with U
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [Complex.ofReal_sub]
  apply congrArg₂ (· - ·)
  · exact (ContinuumSetting.smearedObservable_ofReal _ _).symm
  · rw [← integral_complex_ofReal]
    exact integral_congr_ae (.of_forall fun V => (ContinuumSetting.smearedObservable_ofReal _ V).symm)

theorem referenceResponse_eq {L : ℕ} [NeZero L] (hL : Conventions.IsAdmissibleBlockingFactor L)
    (M K : ℕ+) {β : ℝ} (hb : 0 < β) :
    referenceResponse su2Model L M K β = YangMills.referenceResponse L M K β := by
  classical
  let s : Conventions.StandingParameters := ⟨L,hL,K,M⟩
  have h2 : 2 ≤ L := by have := hL.2; omega
  let H : CubicTorusEmbedsInLattice L M K (siteCount L M K) := model_embedding h2 M.pos
  let : Fintype (Plaquette L (M:ℕ) ((K:ℕ):ℤ)) := Fintype.ofEquiv _ (Equiv.ofBijective _ H.plaquette_bijective)
  let μ := wilsonGibbsMeasure L M K β
  let : IsProbabilityMeasure μ := H.wilsonGibbs_isProbability β
  let : IsProbabilityMeasure (WeightedResponses.wilsonLaw β (siteCount L M K)) := H.wilsonLaw_isProbability β
  let f : Fin 2 → Point → ℝ := ![bump,translatedBump]
  let F (i : Fin 2) := smearedObservable (j:=((K:ℕ):ℤ)) (TestFunctions.periodize (torusSide L M) (f i))
  have hF i : Continuous (F i) := TorusBound.ObservableCumulants.continuous_smearedObservable _
  have hmem (i : Fin 2) : MemLp (F i) 2 μ := by
    change MemLp _ _ (wilsonGibbsMeasure _ _ _ _)
    rw [H.wilsonGibbs_eq_map, memLp_map_measure_iff (hF i).aestronglyMeasurable H.fields.measurable_gaugeField.aemeasurable]
    exact ((hF i).comp H.isClosedEmbedding.continuous).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ht (i : Fin 2) : fixedReferenceTests L M i = TestFunctions.periodize _ (f i) := by
    fin_cases i
    · exact congrArg (TestFunctions.periodize (torusSide L M)) bump_eq.symm
    · exact congrArg (TestFunctions.periodize (torusSide L M)) (funext fun x => (congrFun bump_eq (x - Pi.single 0 3)).symm)
  rw [referenceResponse, ← centered_real_eq β h2 M.pos, YangMills.referenceResponse,
    connectedSchwinger_two_eq_covariance s β hb]
  simp only [ht,Fin.prod_univ_two]
  change cov[F 0,F 1;μ] = _
  exact covariance_eq_sub (hmem 0) (hmem 1)

theorem couplingsAt_eq {L : ℕ} [NeZero L] (hL : Conventions.IsAdmissibleBlockingFactor L)
    (M K : ℕ+) (g₀ : ℝ) :
    couplingsAt su2Model L M K g₀ = {g : ℝ | 0 < g ∧ YangMills.referenceResponse L M K (g^2)⁻¹ = YangMills.fixedPhysicalLevel g₀} := by
  ext g
  by_cases hg : 0 < g
  · simp [couplingsAt,hg,referenceResponse_eq hL M K (inv_pos.2 (sq_pos_of_pos hg)),physicalLevel_eq]
  · simp [couplingsAt,hg]

theorem bareCoupling_eq {L : ℕ} [NeZero L] (hL : Conventions.IsAdmissibleBlockingFactor L)
    (M K : ℕ+) (g₀ : ℝ) : bareCoupling su2Model L M K g₀ = renormalizedBareCoupling L M K g₀ := by
  exact congrArg sInf (couplingsAt_eq hL M K g₀)

end YangMills.Wilson
