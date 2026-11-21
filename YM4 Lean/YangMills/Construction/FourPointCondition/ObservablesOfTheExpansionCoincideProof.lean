import YangMills.Construction.LawInAState.GridDataAtEveryExponentProofForm
import YangMills.Construction.QuaternionicWilsonModel.TheQuaternionModelIsSUTwoWithWilsonsWeightProof
import YangMills.Construction.ResponseInTheExpansion.TheChainIsALawProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FourPointCondition
namespace UrsellComparison
private def latticePlaquetteOf (L m K : ℕ) {n : ℕ} (q : WeightedResponses.OrientedPlaquette n) :
    PeriodicLattice.Plaquette L m (K : ℤ) :=
  ⟨ClusterExpansionOfAStep.periodicLatticeSite L m (K : ℤ) q.1.1, q.1.2.1, q.1.2.2, q.2⟩
private theorem latticePlaquetteOf_bijective {L m K n : ℕ} [NeZero n]
    (hF : ClusterExpansionOfAStep.TorusFieldsAreGaugeFields L m K n) :
    Function.Bijective (latticePlaquetteOf L m K (n := n)) := by
  constructor
  · intro q q' hqq
    have hOrigin : ClusterExpansionOfAStep.periodicLatticeSite L m (K : ℤ) q.1.1 =
        ClusterExpansionOfAStep.periodicLatticeSite L m (K : ℤ) q'.1.1 :=
      congrArg PeriodicLattice.Plaquette.origin hqq
    have hFirst : q.1.2.1 = q'.1.2.1 := congrArg PeriodicLattice.Plaquette.firstAxis hqq
    have hSecond : q.1.2.2 = q'.1.2.2 := congrArg PeriodicLattice.Plaquette.secondAxis hqq
    exact Subtype.ext (Prod.ext (hF.siteBijective.1 hOrigin) (Prod.ext hFirst hSecond))
  · intro P
    obtain ⟨x, hx⟩ := hF.siteBijective.2 P.origin
    exact ⟨⟨(x, P.firstAxis, P.secondAxis), P.firstAxis_lt_secondAxis⟩,
      PeriodicLattice.Plaquette.ext hx rfl rfl⟩
private theorem re_fullTrace_quaternionToMatrix (q : Quaternion ℝ) :
    (Matrices.ComplexMatrix2.fullTrace (SoftAverages.quaternionToMatrix q)).re = 2 * q.re := by
  simp [Matrices.ComplexMatrix2.fullTrace, Matrix.trace_fin_two, SoftAverages.quaternionToMatrix_apply]
  ring
private theorem plaquetteCost_gaugeField {L m K n : ℕ} [NeZero n]
    (hF : ClusterExpansionOfAStep.TorusFieldsAreGaugeFields L m K n) (W : TorusFields.TorusField n)
    (q : WeightedResponses.OrientedPlaquette n) :
    PeriodicLattice.plaquetteCost (ClusterExpansionOfAStep.gaugeFieldOfTorusField L m (K : ℤ) W)
        (latticePlaquetteOf L m K q) = WeightedResponses.plaquetteEnergyOf W q.1 := by
  unfold PeriodicLattice.plaquetteCost WeightedResponses.plaquetteEnergyOf TorusFields.plaquetteEnergy
    latticePlaquetteOf
  rw [hF.plaquetteHolonomy_eq W q.1.1 q.1.2.1 q.1.2.2 q.2, re_fullTrace_quaternionToMatrix]
  ring
private theorem coe_periodicLatticeSite {L m K n : ℕ} [NeZero n] (x : TorusFields.TorusSite n)
    (μ : Fin 4) :
    ((ClusterExpansionOfAStep.periodicLatticeSite L m (K : ℤ) x : PeriodicLattice.Site L m (K : ℤ)) :
        PeriodicLattice.FourTorus L m) μ =
      ((((x μ).val : ℝ) * PeriodicLattice.meshSize L (K : ℤ) : ℝ) :
        AddCircle (PeriodicLattice.torusSide L m)) := by apply _root_.YangMills.SharedProofs.p20856 <;> assumption
private theorem pointOnAxis_half (L m : ℕ) (μ i : Fin 4) (s : ℝ) :
    PeriodicLattice.pointOnAxis L m μ (s / 2) i =
      (((if i = μ then (1 / 2 : ℝ) else 0) * s : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) := by apply _root_.YangMills.SharedProofs.p60603 <;> assumption
private theorem barycenter_latticePlaquetteOf {L m K : ℕ} [NeZero L]
    [NeZero (WeightedResponses.fineSide L K (2 * L ^ m))]
    (q : WeightedResponses.OrientedPlaquette (WeightedResponses.fineSide L K (2 * L ^ m))) :
    (latticePlaquetteOf L m K q).barycenter = WeightedResponses.plaquetteBarycenterAt L K m q.1 := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  funext i
  simp only [PeriodicLattice.Plaquette.barycenter, latticePlaquetteOf, Pi.add_apply,
    WeightedResponses.plaquetteBarycenterAt, TorusMetric.torusProj]
  rw [coe_periodicLatticeSite, pointOnAxis_half, pointOnAxis_half, ← AddCircle.coe_add,
    ← AddCircle.coe_add]
  congr 1
  simp only [PeriodicLattice.meshSize, zpow_neg, zpow_natCast]
  field_simp
private theorem curvatureObservable_eq_sum {n : ℕ} [NeZero n] (h : WeightedResponses.PlaquetteWeight n)
    (W : TorusFields.TorusField n) :
    WeightedResponses.curvatureObservable h W =
      ∑ q : WeightedResponses.OrientedPlaquette n, h q.1 * WeightedResponses.plaquetteEnergyOf W q.1 := by
  unfold WeightedResponses.curvatureObservable
  refine Finset.sum_subtype _ (fun P => ?_) _
  simp [TorusFields.plaquettesIn]
private theorem smearedObservable_eq_sum {L m K : ℕ} [NeZero L]
    [NeZero (WeightedResponses.fineSide L K (2 * L ^ m))]
    (hF : ClusterExpansionOfAStep.TorusFieldsAreGaugeFields L m K (WeightedResponses.fineSide L K (2 * L ^ m)))
    (f : PeriodicLattice.FourTorus L m → ℝ)
    (U : PeriodicLattice.Bond L m (K : ℤ) → Matrices.ComplexMatrix2) :
    PeriodicLattice.smearedObservable f U =
      ∑ q : WeightedResponses.OrientedPlaquette (WeightedResponses.fineSide L K (2 * L ^ m)),
        PeriodicLattice.plaquetteCost U (latticePlaquetteOf L m K q) *
          f (WeightedResponses.plaquetteBarycenterAt L K m q.1) := by
  unfold PeriodicLattice.smearedObservable
  rw [← finsum_comp_equiv (Equiv.ofBijective _ (latticePlaquetteOf_bijective hF)),
    finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Equiv.ofBijective_apply, smul_eq_mul, barycenter_latticePlaquetteOf]
private theorem smearedObservable_gaugeField {L m K : ℕ} [NeZero L]
    [NeZero (WeightedResponses.fineSide L K (2 * L ^ m))]
    (hF : ClusterExpansionOfAStep.TorusFieldsAreGaugeFields L m K (WeightedResponses.fineSide L K (2 * L ^ m)))
    (f : PeriodicLattice.FourTorus L m → ℝ)
    (W : TorusFields.TorusField (WeightedResponses.fineSide L K (2 * L ^ m))) :
    PeriodicLattice.smearedObservable f (ClusterExpansionOfAStep.gaugeFieldOfTorusField L m (K : ℤ) W) =
      WeightedResponses.curvatureObservable (WeightedResponses.testWeight L K m f) W := by
  rw [smearedObservable_eq_sum hF, curvatureObservable_eq_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [plaquetteCost_gaugeField hF, mul_comm]
  rfl
private theorem continuous_plaquetteCost {L m : ℕ} {j : ℤ} (P : PeriodicLattice.Plaquette L m j) :
    Continuous fun U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2 =>
      PeriodicLattice.plaquetteCost U P := by apply _root_.YangMills.Construction.EqualSideGridsAtEveryExponent.continuous_plaquetteCost <;> assumption
private theorem measurable_plaquetteCost {L m : ℕ} {j : ℤ} (P : PeriodicLattice.Plaquette L m j) :
    Measurable fun U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2 =>
      PeriodicLattice.plaquetteCost U P := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact (continuous_plaquetteCost P).measurable
private theorem measurable_smearedObservable {L m K : ℕ} [NeZero L]
    [NeZero (WeightedResponses.fineSide L K (2 * L ^ m))]
    (hF : ClusterExpansionOfAStep.TorusFieldsAreGaugeFields L m K (WeightedResponses.fineSide L K (2 * L ^ m)))
    (f : PeriodicLattice.FourTorus L m → ℝ) :
    Measurable (PeriodicLattice.smearedObservable (j := (K : ℤ)) f) := by
  have hSum : PeriodicLattice.smearedObservable (j := (K : ℤ)) f = fun U =>
      ∑ q : WeightedResponses.OrientedPlaquette (WeightedResponses.fineSide L K (2 * L ^ m)),
        PeriodicLattice.plaquetteCost U (latticePlaquetteOf L m K q) *
          f (WeightedResponses.plaquetteBarycenterAt L K m q.1) :=
    funext (smearedObservable_eq_sum hF f)
  rw [hSum]
  exact Finset.measurable_sum _ fun q _ => (measurable_plaquetteCost _).mul_const _
private theorem continuous_wilsonAction {n : ℕ} [NeZero n] :
    Continuous (TorusFields.wilsonAction (n := n) Finset.univ) := by apply _root_.YangMills.SharedProofs.p11090 <;> assumption
private theorem partition_pos (β : ℝ) {n : ℕ} [NeZero n] :
    0 < ∫ W, Real.exp (-β * TorusFields.wilsonAction Finset.univ W) ∂(TorusFields.fieldHaar n) := by
  have hCont : Continuous fun W : TorusFields.TorusField n =>
      Real.exp (-β * TorusFields.wilsonAction Finset.univ W) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_wilsonAction)
  exact integral_exp_pos (hCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
private theorem wilsonWeight_eq_exp (β : ℝ) {n : ℕ} [NeZero n] :
    TorusLumps.wilsonWeight β n = fun W => Real.exp (-β * TorusFields.wilsonAction Finset.univ W) := by apply _root_.YangMills.Construction.WeightedResponses.ChainLaw.wilsonWeight_eq_exp <;> assumption
private theorem wilsonLaw_eq_normalized (β : ℝ) {n : ℕ} [NeZero n] :
    WeightedResponses.wilsonLaw β n =
      (ENNReal.ofReal (∫ W, TorusLumps.wilsonWeight β n W ∂(TorusFields.fieldHaar n)))⁻¹ •
        (TorusFields.fieldHaar n).withDensity fun W => ENNReal.ofReal (TorusLumps.wilsonWeight β n W) := by
  have hMeas : Measurable fun W : TorusFields.TorusField n =>
      ENNReal.ofReal (Real.exp (-β * TorusFields.wilsonAction Finset.univ W)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul continuous_wilsonAction)).measurable
  simp only [wilsonWeight_eq_exp]
  rw [← withDensity_smul _ hMeas]
  unfold WeightedResponses.wilsonLaw
  congr 1
  funext W
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_div_of_pos (partition_pos β), div_eq_mul_inv, mul_comm]
private theorem wilsonGibbsMeasure_eq_map {L m K n : ℕ} [NeZero n]
    (hF : ClusterExpansionOfAStep.TorusFieldsAreGaugeFields L m K n) (β : ℝ) :
    PeriodicLattice.wilsonGibbsMeasure L m K β =
      (WeightedResponses.wilsonLaw β n).map (ClusterExpansionOfAStep.gaugeFieldOfTorusField L m (K : ℤ)) := by
  rw [hF.wilsonGibbsMeasure_eq β, wilsonLaw_eq_normalized, Measure.map_smul]
private theorem momentGeneratingFunction_eq {L m K : ℕ} [NeZero L]
    [NeZero (WeightedResponses.fineSide L K (2 * L ^ m))]
    (hF : ClusterExpansionOfAStep.TorusFieldsAreGaugeFields L m K (WeightedResponses.fineSide L K (2 * L ^ m)))
    (β : ℝ) {p : ℕ} (f : Fin p → PeriodicLattice.FourTorus L m → ℝ) (t : Fin p → ℂ) :
    Cumulants.momentGeneratingFunction (PeriodicLattice.wilsonGibbsMeasure L m K β)
        (fun j U => PeriodicLattice.smearedObservable (f j) U) t =
      Cumulants.momentGeneratingFunction
        (WeightedResponses.wilsonLaw β (WeightedResponses.fineSide L K (2 * L ^ m)))
        (fun i => WeightedResponses.curvatureObservable (WeightedResponses.testWeight L K m (f i))) t := by
  unfold Cumulants.momentGeneratingFunction
  rw [wilsonGibbsMeasure_eq_map hF, integral_map hF.measurable_gaugeField.aemeasurable]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    simp only [smearedObservable_gaugeField hF]
  · refine Measurable.aestronglyMeasurable ?_
    refine Complex.measurable_exp.comp (Finset.measurable_sum _ fun i _ => ?_)
    exact (Complex.measurable_ofReal.comp (measurable_smearedObservable hF (f i))).const_mul _
private theorem fineSide_eq_two_mul_pow (L m K : ℕ) :
    WeightedResponses.fineSide L K (2 * L ^ m) = 2 * L ^ (m + K) := by
  rw [WeightedResponses.fineSide_eq, pow_add]
  ring
private theorem two_lt_fineSide {L m K : ℕ} (hL : 3 ≤ L) (hm : 1 ≤ m) :
    2 < WeightedResponses.fineSide L K (2 * L ^ m) := by
  rw [fineSide_eq_two_mul_pow]
  have hPow : L ≤ L ^ (m + K) := Nat.le_self_pow (by omega) L
  omega
end UrsellComparison
open UrsellComparison in
theorem torusUrsellEqWeightedCurvature
    (hW : ClusterExpansionOfAStep.WilsonMeasureOnTorusFields) :
    torusUrsellEqWeightedCurvatureStatement := by
  intro L _ m K p β hL hm f
  have hF : ClusterExpansionOfAStep.TorusFieldsAreGaugeFields L m K (WeightedResponses.fineSide L K (2 * L ^ m)) :=
    hW L m K _ (fineSide_eq_two_mul_pow L m K) (two_lt_fineSide hL hm)
  unfold PeriodicLattice.torusUrsellFunction PeriodicLattice.gibbsCumulant
    WeightedResponses.connectedCurvature Cumulants.mixedCumulant
  have hLog : (fun t => Complex.log (Cumulants.momentGeneratingFunction
      (PeriodicLattice.wilsonGibbsMeasure L m K β)
      (fun j U => PeriodicLattice.smearedObservable (f j) U) t)) = fun t => Complex.log
        (Cumulants.momentGeneratingFunction
          (WeightedResponses.wilsonLaw β (WeightedResponses.fineSide L K (2 * L ^ m)))
          (fun i => WeightedResponses.curvatureObservable (WeightedResponses.testWeight L K m (f i))) t) :=
    funext fun t => congrArg Complex.log (momentGeneratingFunction_eq hF β f t)
  rw [hLog]
end YangMills.Construction.FourPointCondition
end
