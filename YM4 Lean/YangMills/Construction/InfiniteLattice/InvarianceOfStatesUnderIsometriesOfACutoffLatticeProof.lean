import YangMills.Construction.Cumulants.JointCumulantsOfBoundedVariables
import YangMills.Construction.InfiniteLattice.BondsPlaquettesCircuitsAndConfigurationsOfTheLatticeOfACutoff
import YangMills.Construction.InfiniteLattice.FactsFromTopologyMeasureAndFunctionTheory
import YangMills.Construction.InfiniteLattice.FactsOfOneLatticeAtOneSpacing
import YangMills.Construction.InfiniteLattice.InvarianceOfStatesUnderIsometriesOfACutoffLattice
import YangMills.Construction.InfiniteLattice.InvarianceOfTheTorusMeasuresUnderLatticeIsometries
import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfASpacingAndTheirActions
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAtASpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Function
noncomputable section
namespace YangMills.Construction.CutoffLatticeStates.MotionInvariance
open InfiniteLattice RefinedLatticeSymmetries
section General
variable {a : ℝ}
theorem isBoundedObservable_of_continuous [CompactSpace (GaugeField a)] {F : GaugeField a → ℂ}
    (hF : Continuous F) : IsBoundedObservable F :=
  ⟨hF.measurable, ‖(⟨F, hF⟩ : C(GaugeField a, ℂ))‖,
    fun U => ContinuousMap.norm_coe_le_norm (⟨F, hF⟩ : C(GaugeField a, ℂ)) U⟩
theorem isLatticeMotionInvariant_of_integral_continuous
    [TopologicalSpace.MetrizableSpace (GaugeField a)]
    (μ : Measure (GaugeField a)) [IsProbabilityMeasure μ] (r : latticeMotions a)
    (h : ∀ F : C(GaugeField a, ℂ),
      ∫ U, F (latticeMotionField r U) ∂μ = ∫ U, F U ∂μ) :
    IsLatticeMotionInvariant μ r := by
  have hm := (continuous_latticeMotionField r).measurable
  have hmap : μ.map (latticeMotionField r) = μ := by
    let := TopologicalSpace.metrizableSpaceMetric (GaugeField a)
    have : IsProbabilityMeasure (μ.map (latticeMotionField r)) :=
      Measure.isProbabilityMeasure_map hm.aemeasurable
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    rw [integral_map hm.aemeasurable f.continuous.aestronglyMeasurable]
    have h2 : ∫ U, ((f (latticeMotionField r U) : ℝ) : ℂ) ∂μ = ∫ U, ((f U : ℝ) : ℂ) ∂μ :=
      h ⟨fun U => ((f U : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
    rw [integral_complex_ofReal, integral_complex_ofReal] at h2
    exact_mod_cast h2
  intro F hF
  calc ∫ U, latticeMotionAct r F U ∂μ
      = ∫ U, F U ∂(μ.map (latticeMotionField r)) :=
        (integral_map hm.aemeasurable hF.1.aestronglyMeasurable).symm
    _ = ∫ U, F U ∂μ := by rw [hmap]
theorem measure_preimage_latticeMotionField (μ : Measure (GaugeField a)) [IsProbabilityMeasure μ]
    (r : latticeMotions a) (h : IsLatticeMotionInvariant μ r)
    {E : Set (GaugeField a)} (hE : MeasurableSet E) :
    μ (latticeMotionField r ⁻¹' E) = μ E := by
  have hm := (continuous_latticeMotionField r).measurable
  have hF : IsBoundedObservable (E.indicator fun _ => (1 : ℂ)) := by
    refine ⟨measurable_const.indicator hE, 1, fun U => ?_⟩
    by_cases hU : U ∈ E <;> simp [hU]
  have h1 := h _ hF
  have h2 : latticeMotionAct r (E.indicator fun _ => (1 : ℂ)) =
      (latticeMotionField r ⁻¹' E).indicator fun _ => (1 : ℂ) := by
    funext U
    change E.indicator (fun _ => (1 : ℂ)) (latticeMotionField r U) = _
    by_cases hU : latticeMotionField r U ∈ E
    · rw [indicator_of_mem hU, indicator_of_mem (show U ∈ latticeMotionField r ⁻¹' E from hU)]
    · rw [indicator_of_notMem hU,
        indicator_of_notMem (show U ∉ latticeMotionField r ⁻¹' E from hU)]
  rw [h2, integral_indicator_const _ (hm hE), integral_indicator_const _ hE] at h1
  have h3 : μ.real (latticeMotionField r ⁻¹' E) = μ.real E := by
    simpa using h1
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h3
theorem isMotionInvariant_of_isPeriodicGibbs (hG : InfiniteLattice.PeriodicGibbsAtSpacing.Statement)
    {β : ℝ} (ha : 0 < a) (hβ : 0 < β) (μ : Measure (GaugeField a)) [IsProbabilityMeasure μ]
    (h : IsPeriodicGibbs β μ) : IsMotionInvariant μ := by
  intro r F hF
  obtain ⟨ht, hw, -⟩ := (hG a ha β hβ).1 μ h
  obtain ⟨w, hwm, v, hv, hr⟩ := r.2
  let t : latticeMotions a := ⟨fun x => w x, w, hwm, 0, zero_mem _, fun x => by simp⟩
  obtain ⟨w', hw', hcoe⟩ := exists_linearEquiv_of_mem_hypercubicGroup hwm
  have hinvW : IsSymmetricUnder μ (latticeMotionSymmetry t) :=
    hw _ w' hw' fun x => by
      change w x = w' x
      rw [← hcoe]
      rfl
  have hinvT := ht ⟨v, hv⟩
  have hcomp : latticeMotionAct r F =
      (shift (⟨v, hv⟩ : LatticePoint a)).actOn
        ((latticeMotionSymmetry t).actOn F) := by
    funext U
    change F _ = F _
    congr 1
    refine Subtype.ext (funext fun b => ?_)
    have hb : (latticeMotionSymmetry r).linkMap b = (shift (⟨v, hv⟩ : LatticePoint a)).linkMap
        ((latticeMotionSymmetry t).linkMap b) :=
      Link.ext (Subtype.ext (hr b.initial)) (Subtype.ext (hr b.terminal))
    exact congrArg (fun c => U.1 c) hb
  rw [hcomp]
  exact (hinvT _ (hF.latticeMotionAct t)).trans (hinvW F hF)
end General
def setupWithExponent (s : Conventions.StandingParameters) (β : ℝ) (hβ : 0 < β) (k : ℕ)
    (hk : 0 < k) : FixedSpacing.Params :=
  { toStandingParameters := { s with m := ⟨k, hk⟩ }, β := β, β_pos := hβ }
section Standing
variable (s : Conventions.StandingParameters)
theorem liftedWilsonMeasure_isMotionInvariant (hCov : LatticeCovering.CoveringStatement)
    (hInv : TorusMeasureSymmetry.InvarianceStatement)
    {β : ℝ} (hβ : 0 < β) (k : ℕ) (hk : 0 < k) :
    ∃ _ : IsProbabilityMeasure (liftedWilsonMeasure s.L k s.K β),
      IsMotionInvariant (liftedWilsonMeasure s.L k s.K β) := by
  have hp : IsProbabilityMeasure (liftedWilsonMeasure s.L k s.K β) :=
    (hCov (setupWithExponent s β hβ k hk)).2.2.1.2.2.2.2.2
  exact ⟨hp, fun r F hF => (hInv (setupWithExponent s β hβ k hk) r).2 F hF⟩
theorem isMotionInvariant_of_mem_weakLimitPoints [CompactSpace (RefinedGaugeField s.L s.K)]
    [TopologicalSpace.MetrizableSpace (RefinedGaugeField s.L s.K)] {β : ℝ}
    (hinv : ∀ k : ℕ, 0 < k → ∃ _ : IsProbabilityMeasure (liftedWilsonMeasure s.L k s.K β),
      IsMotionInvariant (liftedWilsonMeasure s.L k s.K β))
    (μ : Measure (RefinedGaugeField s.L s.K)) [IsProbabilityMeasure μ]
    (hμ : μ ∈ weakLimitPoints s.L s.K β) :
    IsMotionInvariant μ := by
  intro r
  refine isLatticeMotionInvariant_of_integral_continuous μ r fun F => ?_
  let G : C(RefinedGaugeField s.L s.K, ℂ) :=
    ⟨fun U => F (latticeMotionField r U),
      F.continuous.comp (continuous_latticeMotionField r)⟩
  have key : ∀ ε : ℝ, 0 < ε → ‖expectation μ G - expectation μ F‖ < 2 * ε := by
    intro ε hε
    obtain ⟨k, hk, -, hj⟩ := hμ.2 2 ![F, G] ε hε (PeriodicLattice.torusSide s.L 1) ⟨1, one_pos, rfl⟩
    obtain ⟨hp, hi⟩ := hinv k hk
    have h0 := hj 0
    have h1 := hj 1
    have heq : expectation (liftedWilsonMeasure s.L k s.K β) G =
        expectation (liftedWilsonMeasure s.L k s.K β) F :=
      hi r F (isBoundedObservable_of_continuous F.continuous)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    rw [heq] at h1
    have e : expectation μ G - expectation μ F =
        -(expectation (liftedWilsonMeasure s.L k s.K β) F - expectation μ G) +
          (expectation (liftedWilsonMeasure s.L k s.K β) F - expectation μ F) := by ring
    rw [e]
    calc _ ≤ ‖-(expectation (liftedWilsonMeasure s.L k s.K β) F - expectation μ G)‖ +
          ‖expectation (liftedWilsonMeasure s.L k s.K β) F - expectation μ F‖ := norm_add_le _ _
      _ < 2 * ε := by
        rw [norm_neg]
        linarith
  have hz : expectation μ G - expectation μ F = 0 := by
    by_contra hne
    have := key (‖expectation μ G - expectation μ F‖ / 2) (by positivity)
    linarith
  exact sub_eq_zero.mp hz
theorem faceEnergy_latticeMotionField
    (hGeom : RefinedLatticeSymmetries.RefinedLatticeSymmetryTheorem)
    (r : refinedLatticeMotions s.L s.K) (p : ElementaryPlaquette (refinedSpacing s.L s.K))
    (U : RefinedGaugeField s.L s.K) :
    faceEnergy (latticeMotionField r U) p = faceEnergy U (mapPlaquette r p) := by
  obtain ⟨-, hB, -, hP, hC, hCfg, -⟩ := hGeom s
  obtain ⟨-, h8, -, hact, -, -⟩ := hC p
  have hne : {γ | IsCircuit p γ}.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [h8]; norm_num)
  obtain ⟨γ, e, e', hfr, c, hc, rfl⟩ := hne
  rcases hq : affineDecomposition r with ⟨w, v⟩
  have hpair : IsAffineDecomposition (refinedSpacing s.L s.K) r.1 (w, v) :=
    hq ▸ isAffineDecomposition_affineDecomposition r
  have hstep := ((hB.2.2.2 r).2.2.2.2 w v hpair).1
  have himage : ∀ e₀ : MeshStep s.L s.K, ∃ f : MeshStep s.L s.K, f.1 = w e₀.1 := fun e₀ => by
    have h0 : w e₀.1 ∈ w '' PeriodicLattice.PlaquetteCircuits.meshVectors s.L ((s.K : ℕ) : ℤ) :=
      mem_image_of_mem _ e₀.2
    rw [hstep] at h0
    exact ⟨⟨_, h0⟩, rfl⟩
  obtain ⟨f, hf⟩ := himage e
  obtain ⟨f', hf'⟩ := himage e'
  obtain ⟨hfr', hcorner, hquad⟩ :=
    ((hP r).2.2.2.2.2.2 w v hpair).2 p e e' f f' c hfr hc hf hf'
  have hcirc : IsCircuit (mapPlaquette r p) (mapLoop r (circuitFrom c e e')) :=
    ⟨f, f', hfr', pointImage r c, hcorner.symm, hquad⟩
  rw [hact (latticeMotionField r U) _ ⟨e, e', hfr, c, hc, rfl⟩,
    (hC (mapPlaquette r p)).2.2.2.1 U _ hcirc]
  unfold realTraceLoop
  rw [(hCfg r).2.2 U]
theorem observableTransport
    (hGeom : RefinedLatticeSymmetries.RefinedLatticeSymmetryTheorem)
    {E : Type*} [AddCommMonoid E] [Module ℝ E] (r : refinedLatticeMotions s.L s.K)
    (f : AmbientSpace → E) : ObservableTransport r f := by
  refine ⟨?_, rfl⟩
  funext U
  obtain ⟨hPts, -, -, hP, -, -, -⟩ := hGeom s
  have hleft : LeftInverse (motionInverse r) r.1 := ((hPts.2.2 r).2.2.2.2.2).1
  have hbij := (hP r).2.2.2.2.1
  have hbary := (hP r).2.2.1
  unfold smearedEnergy
  rw [← finsum_comp (g := fun q => faceEnergy U q • (f ∘ motionInverse r) q.center)
    (mapPlaquette r) hbij]
  refine finsum_congr fun p => ?_
  simp only [comp_apply]
  rw [faceEnergy_latticeMotionField s hGeom, hbary, hleft]
theorem continuous_complexSmearedEnergy
    (hGeom : RefinedLatticeSymmetries.RefinedLatticeSymmetryTheorem)
    (hFacts : FixedSpacing.BasicFacts) {f : AmbientSpace → ℝ}
    (hf : HasCompactSupport f) :
    Continuous (complexSmearedEnergy f : RefinedGaugeField s.L s.K → ℂ) := by
  obtain ⟨-, -, -, -, hC, -, -⟩ := hGeom s
  let D : FixedSpacing.Setup := ⟨s.L, s.isAdmissible, s.K, s.m, 1, one_pos⟩
  have hfin : {p : ElementaryPlaquette (refinedSpacing s.L s.K) | p.center ∈ tsupport f}.Finite :=
    (hFacts D).2.2.2.2.2.2.1 _ hf.isCompact.isBounded
  have hsum : ∀ U : RefinedGaugeField s.L s.K, smearedEnergy f U =
      ∑ p ∈ hfin.toFinset, faceEnergy U p • f p.center := by
    intro U
    refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
    have hne : f p.center ≠ 0 := fun h0 => hp (by simp [h0])
    simpa using subset_tsupport f hne
  have hc : Continuous (fun U : RefinedGaugeField s.L s.K => smearedEnergy f U) := by
    simp only [hsum]
    exact continuous_finsetSum _ fun p _ => ((hC p).2.2.2.2.1).smul continuous_const
  exact Complex.continuous_ofReal.comp hc
theorem connectedFunctionsInvariant_of_invariant
    (hGeom : RefinedLatticeSymmetries.RefinedLatticeSymmetryTheorem)
    (hCum : Cumulants.BoundedComplexCumulants.CumulantProperties)
    (hFacts : FixedSpacing.BasicFacts)
    [CompactSpace (RefinedGaugeField s.L s.K)]
    (r : refinedLatticeMotions s.L s.K)
    (μ μ' : Measure (RefinedGaugeField s.L s.K)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] (hμ : IsLatticeMotionInvariant μ r)
    (hμ' : IsLatticeMotionInvariant μ' r) (n : ℕ) (hn : 1 ≤ n) (X : Fin n → AmbientSpace → ℝ)
    (hX : ∀ i, IsBoundedBorelCompactlySupported (X i)) : ConnectedFunctionsInvariant r μ μ' X := by
  have hcont : ∀ i, Continuous (complexSmearedEnergy (X i) : RefinedGaugeField s.L s.K → ℂ) :=
    fun i => continuous_complexSmearedEnergy s hGeom hFacts (hX i).2.2
  have hobs : ∀ i, IsBoundedObservable (complexSmearedEnergy (X i) : RefinedGaugeField s.L s.K → ℂ) :=
    fun i => isBoundedObservable_of_continuous (hcont i)
  have hψ := (continuous_latticeMotionField r).measurable
  have hmove : ∀ i, (complexSmearedEnergy (pushTuple r X i) : RefinedGaugeField s.L s.K → ℂ) =
      complexSmearedEnergy (X i) ∘ latticeMotionField r := fun i => by
    funext U
    have h1 := congrFun (observableTransport s hGeom r (X i)).1 U
    have h2 := congrFun (observableTransport s hGeom r (X i)).2 U
    simp only [complexSmearedEnergy, comp_apply]
    rw [h1, h2]
    rfl
  have hmoment : ∀ (μ₁ μ₂ : Measure (RefinedGaugeField s.L s.K)) [IsProbabilityMeasure μ₁]
      [IsProbabilityMeasure μ₂], IsLatticeMotionInvariant μ₁ r → IsLatticeMotionInvariant μ₂ r →
      centeredMomentAgainst μ₁ μ₂ (pushTuple r X) = centeredMomentAgainst μ₁ μ₂ X := by
    intro μ₁ μ₂ _ _ h₁ h₂
    have hconst : ∀ i, expectation μ₂ (complexSmearedEnergy (pushTuple r X i)) =
        expectation μ₂ (complexSmearedEnergy (X i)) := fun i => by
      rw [hmove i]
      exact h₂ _ (hobs i)
    have hprod : (fun U : RefinedGaugeField s.L s.K =>
        ∏ i, (complexSmearedEnergy (pushTuple r X i) U -
          expectation μ₂ (complexSmearedEnergy (pushTuple r X i)))) =
        latticeMotionAct r fun U => ∏ i, (complexSmearedEnergy (X i) U -
          expectation μ₂ (complexSmearedEnergy (X i))) := by
      funext U
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hconst i, hmove i]
      rfl
    unfold centeredMomentAgainst
    rw [hprod]
    exact h₁ _ (isBoundedObservable_of_continuous
      (continuous_finsetProd _ fun i _ => (hcont i).sub continuous_const))
  refine ⟨?_, hmoment μ μ hμ hμ, hmoment μ' μ hμ' hμ⟩
  have hY := fun i => (hobs i : Cumulants.IsBoundedComplexObservable _)
  have h := ((hCum _ μ n _ hY hn).2.1 _ hψ
    fun E hE => measure_preimage_latticeMotionField μ r hμ hE).1
  unfold connectedFunction
  rw [← h]
  exact congrArg _ (funext hmove)
end Standing
theorem statesInvariantUnderMotions
    (hGeom : RefinedLatticeSymmetries.RefinedLatticeSymmetryTheorem)
    (hCov : LatticeCovering.CoveringStatement)
    (hInv : TorusMeasureSymmetry.InvarianceStatement)
    (hGibbs : InfiniteLattice.PeriodicGibbsAtSpacing.Statement)
    (hCum : Cumulants.BoundedComplexCumulants.CumulantProperties)
    (hTop : InfiniteLattice.AmbientFacts.AllFacts)
    (hFacts : FixedSpacing.BasicFacts) : StatesInvariantUnderMotions := by
  intro s β hβ
  have hspace := ((hTop.1 (setupWithExponent s β hβ s.m s.m.pos)).1).2
  have : CompactSpace (RefinedGaugeField s.L s.K) := hspace.1
  have : TopologicalSpace.MetrizableSpace (RefinedGaugeField s.L s.K) := hspace.2
  have htorus := fun k hk => liftedWilsonMeasure_isMotionInvariant s hCov hInv hβ k hk
  have ha : 0 < refinedSpacing s.L s.K := zpow_pos (by
    have := s.isAdmissible.2
    positivity) _
  refine ⟨htorus, fun μ _ hμ => isMotionInvariant_of_mem_weakLimitPoints s htorus μ hμ,
    fun μ _ hμ => isMotionInvariant_of_isPeriodicGibbs hGibbs ha hβ μ hμ, fun r => ⟨fun p U => ?_,
    fun f _ => observableTransport s hGeom r f, fun f _ => observableTransport s hGeom r f,
    fun μ μ' _ _ hμ hμ' n hn X hX =>
      connectedFunctionsInvariant_of_invariant s hGeom hCum hFacts r μ μ' hμ hμ' n hn X hX⟩⟩
  obtain ⟨-, -, -, hP, -, -, -⟩ := hGeom s
  exact ⟨(hP r).2.1 p, (hP r).2.2.1 p, faceEnergy_latticeMotionField s hGeom r p U⟩
end YangMills.Construction.CutoffLatticeStates.MotionInvariance
