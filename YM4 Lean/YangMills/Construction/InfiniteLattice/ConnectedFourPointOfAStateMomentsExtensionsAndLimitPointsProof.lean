import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.Cumulants.JointCumulantThroughMoments
import YangMills.Construction.InfiniteLattice.ConnectedFourPointOfAStateMomentsExtensionsAndLimitPoints
import YangMills.Construction.InfiniteLattice.ContinuousObservablesAndTheWilsonKernelOfACutoff
import YangMills.Construction.InfiniteLattice.SpacePlaquettesFunctionsOfPlaquettesAndLatticeIsometries
import YangMills.Construction.Lattice.ConnectedFunctionsAreAFiniteSumOverPlaquettes
import YangMills.Construction.Lattice.LatticesCubesDoubleBlocksAndLocalityOfAveragesProof
import YangMills.Construction.SystemOfAdmissibleConstants.OneProductOfPiecesProof
import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevelProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.FourPointMoments
open YangMills.Construction.InfiniteLattice YangMills.Construction.InfiniteLattice.PeriodicExtensions
open YangMills.Construction.TorusMetric (euclidNormVec torusProj torusEuclidNorm)
private theorem abs_coord_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem euclidNormVec_eq_norm (v : Fin 4 → ℝ) : euclidNormVec v = ‖WithLp.toLp 2 v‖ := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_eq_norm <;> assumption
private theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
private theorem euclidNormVec_sub_le (x y c : Fin 4 → ℝ) :
    euclidNormVec (x - y) ≤ euclidNormVec (x - c) + euclidNormVec (y - c) := by
  have h : x - y = (x - c) - (y - c) := by abel
  rw [h, euclidNormVec_eq_norm, euclidNormVec_eq_norm (x - c), euclidNormVec_eq_norm (y - c),
    WithLp.toLp_sub]
  exact norm_sub_le _ _
private theorem isCompact_closedBallR4 (c : Fin 4 → ℝ) (r : ℝ) :
    IsCompact (TestFunctions.closedBallR4 c r) := by apply _root_.YangMills.SharedProofs.p20989 <;> assumption
private theorem smearedEnergy_ofReal {a : ℝ} (f : AmbientSpace → ℝ) (U : GaugeField a) :
    smearedEnergy (fun x => (f x : ℂ)) U = ((smearedEnergy f U : ℝ) : ℂ) := by apply _root_.YangMills.SharedProofs.p95543 <;> assumption
private theorem smearedObservable_ofReal {L m : ℕ} {j : ℤ} (f : AmbientSpace → ℝ)
    (U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) :
    PeriodicLattice.smearedObservable
        (TestFunctions.periodize (PeriodicLattice.torusSide L m) fun x => (f x : ℂ)) U =
      ((PeriodicLattice.smearedObservable
        (TestFunctions.periodize (PeriodicLattice.torusSide L m) f) U : ℝ) : ℂ) := by apply _root_.YangMills.SharedProofs.p19060 <;> assumption
private theorem IsBoundedBorelCompactlySupported.ofReal {f : AmbientSpace → ℝ}
    (h : IsBoundedBorelCompactlySupported f) :
    IsBoundedBorelCompactlySupported fun x => (f x : ℂ) := by
  obtain ⟨hm, ⟨C, hC⟩, hc⟩ := h
  refine ⟨Complex.measurable_ofReal.comp hm, ⟨C, fun x => by simpa using hC x⟩, ?_⟩
  exact hc.comp_left Complex.ofReal_zero
private theorem IsBallQuadruple.boundedBorelCompactlySupported {ρ : ℝ}
    {f : Fin 4 → AmbientSpace → ℝ} (hq : IsBallQuadruple ρ f) (k : Fin 4) :
    IsBoundedBorelCompactlySupported (f k) := by
  obtain ⟨c, hc⟩ := hq.supports_subset_ball
  exact ⟨hq.measurable k, hq.bounded k,
    (isCompact_closedBallR4 c ρ).of_isClosed_subset (isClosed_tsupport _) (hc k)⟩
private theorem normalizedActionMeasure_facts (hExp : ConnectedFunctionExpansion.Statement)
    {L m K : ℕ} {β : ℝ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K)
    (hβ : 0 < β) :
    IsProbabilityMeasure (PeriodicLattice.normalizedActionMeasure L m K β) ∧
      (PeriodicLattice.normalizedActionMeasure L m K β).map (fun U => U.1) =
        PeriodicLattice.wilsonGibbsMeasure L m K β := by
  obtain ⟨-, -, hp, -, hw⟩ := (hExp L m K hL hm).2.2.2.2.1 β
  exact ⟨hp, (hw hK hβ).2⟩
private theorem measurableEmbedding_linkValues (hProd : GaugeFieldProduct.Statement) {L m K : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) :
    MeasurableEmbedding (fun U : PeriodicLattice.CompactGaugeField L m (K : ℤ) => U.1) := by
  have hc : CompactSpace (PeriodicLattice.CompactGaugeField L m (K : ℤ)) :=
    (hProd.1 L m (K : ℤ) hL hm (by positivity)).2.2.1.2.2.1
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hb : ∀ b, Continuous fun U : PeriodicLattice.CompactGaugeField L m (K : ℤ) =>
      PeriodicLattice.CompactGaugeField.linkValue U b := fun b =>
    continuous_iInf_dom (i := b) continuous_induced_dom
  have hcont : Continuous (fun U : PeriodicLattice.CompactGaugeField L m (K : ℤ) => U.1) :=
    continuous_pi fun b => continuous_subtype_val.comp (hb b)
  exact (hcont.isClosedEmbedding Subtype.val_injective).measurableEmbedding
private theorem integral_wilsonGibbsMeasure_eq {L m K : ℕ} {β : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hemb : MeasurableEmbedding (fun U : PeriodicLattice.CompactGaugeField L m (K : ℤ) => U.1))
    (hmap : (PeriodicLattice.normalizedActionMeasure L m K β).map (fun U => U.1) =
      PeriodicLattice.wilsonGibbsMeasure L m K β)
    (F : (PeriodicLattice.Bond L m (K : ℤ) → Matrices.ComplexMatrix2) → E) :
    ∫ U, F U ∂PeriodicLattice.wilsonGibbsMeasure L m K β =
      ∫ U, F U.1 ∂PeriodicLattice.normalizedActionMeasure L m K β := by
  rw [← hmap]
  exact hemb.integral_map F
private theorem momentFormulaOnTori_holds (hProd : GaugeFieldProduct.Statement)
    (hExp : ConnectedFunctionExpansion.Statement)
    (hMom : Cumulants.MixedCumulantMomentExpansion) {L K : ℕ} {β : ℝ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) (hβ : 0 < β) :
    MomentFormulaOnTori L K β := by
  intro m hm h hT
  obtain ⟨hp, hmap⟩ := normalizedActionMeasure_facts hExp hL hm hK hβ
  have hemb := measurableEmbedding_linkValues (K := K) hProd hL hm
  have hbdd : ∀ i, Probability.IsBoundedRealRV
      (PeriodicLattice.observableOnFields (J := K) (h i)) := fun i => by
    obtain ⟨-, -, -, hall, -⟩ := (hExp L m K hL hm).2.2.2.2.1 β
    have hsup : ∀ k, ConnectedFunctionExpansion.IsBoundedOnTorus (h k) := fun k => by
      obtain ⟨C, hC⟩ := hT.1 k
      exact ((iSup_le fun y => ENNReal.ofReal_le_ofReal (hC y)).trans_lt
        ENNReal.ofReal_lt_top).ne
    obtain ⟨hX, -⟩ := hall 3 h hsup
    exact ⟨(hX i).1, (hX i).2⟩
  have hΓ : (fun t : Fin 4 → ℂ => Complex.log (Cumulants.momentGeneratingFunction
        (PeriodicLattice.wilsonGibbsMeasure L m K β)
        (fun i U => PeriodicLattice.smearedObservable (h i) U) t)) =
      fun t => Complex.log (Cumulants.momentGeneratingFunction
        (PeriodicLattice.normalizedActionMeasure L m K β)
        (fun i => PeriodicLattice.observableOnFields (J := K) (h i)) t) :=
    funext fun t => congrArg Complex.log (integral_wilsonGibbsMeasure_eq hemb hmap _)
  have hcum : SchwingerFunctions.connectedSchwinger L m K β h = Cumulants.mixedCumulant
      (PeriodicLattice.normalizedActionMeasure L m K β)
      (fun i => PeriodicLattice.observableOnFields (J := K) (h i)) := by
    unfold SchwingerFunctions.connectedSchwinger PeriodicLattice.gibbsCumulant
      Cumulants.mixedCumulant
    rw [hΓ]
  rw [hcum, hMom _ _ 4 _ (by norm_num) hbdd]
  unfold momentCumulantSum
  refine Finset.sum_congr rfl fun P _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun J _ => ?_
  congr 1
  exact (integral_wilsonGibbsMeasure_eq hemb hmap fun U =>
    ∏ i ∈ J, PeriodicLattice.smearedObservable (h i) U).symm
private theorem RealWeakState.continuous_value {a : ℝ} (F : C(GaugeField a, ℝ)) :
    Continuous fun ν : RealWeakState a => ν.value F :=
  continuous_iInf_dom (i := F) continuous_induced_dom
private theorem meshSize_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (j : ℤ) :
    0 < PeriodicLattice.meshSize L j := by apply _root_.YangMills.Construction.PeriodicLattice.GeometryAndLocalityOfBlockAverages.meshSize_pos <;> assumption
private theorem limitsInGibbsSet_holds (hProd : GaugeFieldProduct.Statement)
    (hExp : ConnectedFunctionExpansion.Statement) {L K : ℕ} {β : ℝ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) (hβ : 0 < β) :
    LimitsInGibbsSet L K β := by
  have hprob : ∀ m : ℕ, 0 < m → IsProbabilityMeasure (liftedWilsonMeasure L m K β) :=
    fun m hm => by
    obtain ⟨hp, hmap⟩ := normalizedActionMeasure_facts hExp hL hm hK hβ
    have : IsProbabilityMeasure (PeriodicLattice.wilsonGibbsMeasure L m K β) := by
      rw [← hmap]
      exact Measure.isProbabilityMeasure_map
        (measurableEmbedding_linkValues (K := K) hProd hL hm).measurable.aemeasurable
    exact Measure.isProbabilityMeasure_map (measurable_liftField L m (K : ℤ)).aemeasurable
  refine ⟨hprob, fun ν => ⟨fun m hS hC => ?_, fun h => h, fun hV => ?_⟩⟩
  · let σ : ℕ → RealWeakState (PeriodicLattice.meshSize L (K : ℤ)) :=
      fun i => ⟨liftedWilsonMeasure L (m i) K β, hprob _ (m i).pos⟩
    have hT : Tendsto σ atTop (𝓝 ν) := (RealWeakState.tendstoWeakly_iff_tendsto σ ν).1 hC
    intro N hN s
    have h1 : ∀ᶠ i in atTop,
        i ∉ {i : ℕ | 1 ≤ i ∧ ¬ s ≤ (fun i => PeriodicLattice.torusSide L (m i)) i} := by
      rw [← Nat.cofinite_eq_atTop]
      exact (hS.2 s).eventually_cofinite_notMem
    obtain ⟨i, hiN, hi, hi1⟩ :=
      ((hT.eventually_mem hN).and (h1.and (eventually_ge_atTop 1))).exists
    refine ⟨m i, (m i).pos, ?_, σ i, hiN, rfl⟩
    by_contra hc
    exact hi ⟨hi1, hc⟩
  · obtain ⟨-, φ, hφ, hF⟩ := hV
    have hpos : ∀ i, 0 < φ (i + 1) := fun i =>
      lt_of_lt_of_le (Nat.succ_pos i) (hφ.le_apply)
    let σ : ℕ → RealWeakState (PeriodicLattice.meshSize L (K : ℤ)) :=
      fun i => ⟨liftedWilsonMeasure L (φ (i + 1)) K β, hprob _ (hpos i)⟩
    have hc := (CutoffStates.compactSpace_and_metrizableSpace_gaugeField
      (meshSize_pos hL (K : ℤ))).1
    have hC : RealWeakState.TendstoWeakly σ ν := by
      intro F
      exact (tendsto_add_atTop_iff_nat 1).2 (hF (BoundedContinuousFunction.mkOfCompact F))
    have hT : Tendsto σ atTop (𝓝 ν) := (RealWeakState.tendstoWeakly_iff_tendsto σ ν).1 hC
    intro N hN s
    have hL1 : (1 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 1 < L)
    obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt s hL1
    obtain ⟨i, hiN, hi⟩ := ((hT.eventually_mem hN).and (eventually_ge_atTop n₀)).exists
    refine ⟨φ (i + 1), hpos i, ?_, σ i, hiN, rfl⟩
    have hle : n₀ ≤ φ (i + 1) := (hi.trans (Nat.le_succ i)).trans hφ.le_apply
    have h2 : (L : ℝ) ^ n₀ ≤ (L : ℝ) ^ φ (i + 1) := pow_le_pow_right₀ hL1.le hle
    have h3 : (0 : ℝ) ≤ (L : ℝ) ^ φ (i + 1) := by positivity
    simp only [PeriodicLattice.torusSide]
    linarith
private theorem continuous_torusProj (ℓ : ℝ) : Continuous (torusProj ℓ) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusProj <;> assumption
private theorem tsupport_periodize_subset {ℓ : ℝ} [Fact (0 < ℓ)] {g : AmbientSpace → ℝ}
    (hg : HasCompactSupport g) :
    tsupport (TestFunctions.periodize ℓ g) ⊆ torusProj ℓ '' tsupport g := by
  have hcl : IsClosed (torusProj ℓ '' tsupport g) := (hg.image (continuous_torusProj ℓ)).isClosed
  refine closure_minimal ?_ hcl
  intro y hy
  obtain ⟨v, rfl⟩ := TestFunctions.torusProj_surjective ℓ y
  rw [Function.mem_support, TestFunctions.periodize_torusProj] at hy
  by_contra hno
  apply hy
  have hz : ∀ k, g (v + TestFunctions.latticeTranslate ℓ k) = 0 := fun k => by
    by_contra hk
    exact hno ⟨_, subset_tsupport _ hk, TestFunctions.torusProj_add_latticeTranslate ℓ v k⟩
  simp [TestFunctions.periodicSum, hz]
private theorem le_torusEuclidNorm_sub {ℓ d : ℝ} {x y : Fin 4 → ℝ} (hℓ : 0 < ℓ)
    (hd : d ≤ euclidNormVec (x - y)) (hxy : euclidNormVec (x - y) ≤ ℓ / 2) :
    d ≤ torusEuclidNorm (torusProj ℓ x - torusProj ℓ y) := by
  have hsub : torusProj ℓ x - torusProj ℓ y = torusProj ℓ (x - y) := by
    funext μ
    simp [torusProj]
  rw [hsub]
  unfold torusEuclidNorm
  refine le_csInf ⟨_, x - y, rfl, rfl⟩ ?_
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨k, rfl⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq hv
  by_cases hk : k = 0
  · subst hk
    have h0 : TestFunctions.latticeTranslate ℓ 0 = 0 := by
      funext μ
      simp [TestFunctions.latticeTranslate]
    rw [h0, add_zero]
    exact hd
  · obtain ⟨μ, hμ⟩ : ∃ μ, k μ ≠ 0 := by
      by_contra hc
      exact hk (funext fun μ => by
        by_contra hμ
        exact hc ⟨μ, hμ⟩)
    have h1 : ℓ ≤ |TestFunctions.latticeTranslate ℓ k μ| := by
      have hone : (1 : ℝ) ≤ |(k μ : ℝ)| := by
        have : (1 : ℤ) ≤ |k μ| := Int.one_le_abs hμ
        exact_mod_cast this
      simp only [TestFunctions.latticeTranslate, abs_mul, abs_of_pos hℓ]
      nlinarith
    have h2 := abs_coord_le_euclidNormVec (TestFunctions.latticeTranslate ℓ k) μ
    have h3 := euclidNormVec_sub_le ((x - y) + TestFunctions.latticeTranslate ℓ k) (x - y) 0
    simp only [sub_zero, add_sub_cancel_left] at h3
    linarith
private theorem exists_separated_periodizeAll {L m : ℕ} {ρ : ℝ} {f : Fin 4 → AmbientSpace → ℝ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hq : IsBallQuadruple ρ f)
    (hside : 4 * ρ ≤ PeriodicLattice.torusSide L m) :
    ∃ d : ℝ, TestFunctions.HasSeparatedSupportsTorus (SchwingerFunctions.periodizeAll L m f) d := by
  obtain ⟨c, hc⟩ := hq.supports_subset_ball
  obtain ⟨d, hd, hsep⟩ := hq.separated
  have hpos : 0 < PeriodicLattice.torusSide L m := by
    have : (0 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 0 < L)
    simp only [PeriodicLattice.torusSide]
    positivity
  have : Fact (0 < PeriodicLattice.torusSide L m) := ⟨hpos⟩
  refine ⟨d, hd, fun i k hik => ?_⟩
  refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_
  obtain ⟨x, hx, rfl⟩ :=
    tsupport_periodize_subset (hq.boundedBorelCompactlySupported i).2.2 ha
  obtain ⟨y, hy, rfl⟩ :=
    tsupport_periodize_subset (hq.boundedBorelCompactlySupported k).2.2 hb
  have hle : TestFunctions.setDistR4 (tsupport (f i)) (tsupport (f k)) ≤
      ENNReal.ofReal (euclidNormVec (x - y)) := by
    unfold TestFunctions.setDistR4
    exact iInf₂_le_of_le x hx (iInf₂_le y hy)
  have hd' : d ≤ euclidNormVec (x - y) :=
    (ENNReal.ofReal_le_ofReal_iff (euclidNormVec_nonneg _)).1 ((hsep i k hik).trans hle)
  have hxc : euclidNormVec (x - c) ≤ ρ := hc i hx
  have hyc : euclidNormVec (y - c) ≤ ρ := hc k hy
  have hdiam : euclidNormVec (x - y) ≤ PeriodicLattice.torusSide L m / 2 := by
    have := euclidNormVec_sub_le x y c
    linarith
  exact ENNReal.ofReal_le_ofReal (le_torusEuclidNorm_sub hpos hd' hdiam)
private theorem periodizedEvaluation_holds (hPer : PeriodizationIdentities.Statement)
    {L K : ℕ} {β ρ : ℝ} {f : Fin 4 → AmbientSpace → ℝ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K)
    (hβ : 0 < β) (hq : IsBallQuadruple ρ f) : IsPeriodizedObservable L K β ρ f := by
  intro m hm hside
  have hB := hq.boundedBorelCompactlySupported
  have hall := hPer L m K hL hm hK β hβ
  obtain ⟨c, hc⟩ := hq.supports_subset_ball
  refine ⟨⟨TestFunctions.closedBallR4 c ρ, fun k => ⟨fun x hx y hy => ?_,
    (subset_tsupport _).trans (hc k)⟩⟩, exists_separated_periodizeAll hL hq hside,
    fun U k => ?_, ?_⟩
  · have hxc : euclidNormVec (x - c) ≤ ρ := hx
    have hyc : euclidNormVec (y - c) ≤ ρ := hy
    have := euclidNormVec_sub_le x y c
    linarith
  · have h := hall.2.1 _ (IsBoundedBorelCompactlySupported.ofReal (hB k)) U
    rw [smearedEnergy_ofReal, smearedObservable_ofReal] at h
    exact Complex.ofReal_injective h
  · exact (hall.2.2.2.1 4 f (by norm_num) hB).2.2.1
private theorem continuous_smearedEnergy (hSym : CutoffStructure.FieldSpaceAndSymmetries)
    {a : ℝ} (ha : 0 < a) {f : AmbientSpace → ℝ} (hf : IsBoundedBorelCompactlySupported f) :
    Continuous fun U : GaugeField a => smearedEnergy f U := by
  have h := ((hSym a ha).2.2.2.2.1.2 _ (IsBoundedBorelCompactlySupported.ofReal hf)).2.1
  have h' : (fun U : GaugeField a => smearedEnergy f U) =
      fun U => (smearedEnergy (fun x => (f x : ℂ)) U).re := by
    funext U
    rw [smearedEnergy_ofReal, Complex.ofReal_re]
  rw [h']
  exact Complex.continuous_re.comp h
private theorem continuous_fourPointUrsell {L K : ℕ} {f : Fin 4 → AmbientSpace → ℝ}
    (hform : MomentFormulaForStates L K f)
    (hc : ∀ k, Continuous fun U : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) =>
      smearedEnergy (f k) U) :
    Continuous fun ν : RealWeakState (PeriodicLattice.meshSize L (K : ℤ)) =>
      fourPointUrsell ν.measure f := by
  have h : (fun ν : RealWeakState (PeriodicLattice.meshSize L (K : ℤ)) =>
      fourPointUrsell ν.measure f) = fun ν =>
      momentCumulantSum fun J => ν.value fun U => ∏ i ∈ J, smearedEnergy (f i) U :=
    funext hform
  rw [h]
  unfold momentCumulantSum
  refine continuous_finsetSum _ fun P _ => continuous_const.mul
    (continuous_finsetProd _ fun J _ => Complex.continuous_ofReal.comp ?_)
  exact RealWeakState.continuous_value ⟨fun U => ∏ i ∈ J, smearedEnergy (f i) U,
    continuous_finsetProd _ fun i _ => hc i⟩
private theorem boundsPassToLimits_holds {L K : ℕ} {β ρ : ℝ} {f : Fin 4 → AmbientSpace → ℝ}
    (hread : IsPeriodizedObservable L K β ρ f)
    (hcont : Continuous fun ν : RealWeakState (PeriodicLattice.meshSize L (K : ℤ)) =>
      fourPointUrsell ν.measure f) : BoundsPassToLimits L K β ρ f := by
  intro c C ℓ₀ hℓ hb ν hν
  have hre := Complex.continuous_re.comp hcont
  have hcl : IsClosed {σ : RealWeakState (PeriodicLattice.meshSize L (K : ℤ)) |
      c ≤ (fourPointUrsell σ.measure f).re ∧ (fourPointUrsell σ.measure f).re ≤ C} :=
    (isClosed_le continuous_const hre).inter (isClosed_le hre continuous_const)
  by_contra hno
  have hN := hcl.isOpen_compl.mem_nhds hno
  obtain ⟨m, hm, hs, σ, hσ, hσm⟩ := hν _ hN (max ℓ₀ (4 * ρ))
  have h4 : 4 * ρ ≤ PeriodicLattice.torusSide L m := (le_max_right _ _).trans hs
  apply hσ
  have he := (hread m hm h4).2.2.2
  change c ≤ (fourPointUrsell σ.measure f).re ∧ (fourPointUrsell σ.measure f).re ≤ C
  rw [hσm, he]
  exact hb m hm hs
theorem momentsExtensionsAndLimits_holds
    (hProd : GaugeFieldProduct.Statement)
    (hExp : ConnectedFunctionExpansion.Statement)
    (hMom : Cumulants.MixedCumulantMomentExpansion)
    (hPer : PeriodizationIdentities.Statement)
    (hSym : CutoffStructure.FieldSpaceAndSymmetries) :
    MomentsExtensionsAndLimits := by
  intro L K hL hK β hβ
  refine ⟨momentFormulaOnTori_holds hProd hExp hMom hL hK hβ,
    limitsInGibbsSet_holds hProd hExp hL hK hβ, fun ρ f _ hq => ?_⟩
  have hB := hq.boundedBorelCompactlySupported
  have hform : MomentFormulaForStates L K f := by
    intro ν
    have hX := (hPer L 1 K hL one_pos hK β hβ).2.2.2.1 4 f (by norm_num) hB
    exact hMom _ ν.measure 4 (fun i U => smearedEnergy (f i) U) (by norm_num)
      fun i => ⟨(hX.2.1 i).1, (hX.2.1 i).2⟩
  have hc : ∀ k, Continuous fun U : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) =>
      smearedEnergy (f k) U := fun k =>
    continuous_smearedEnergy hSym (meshSize_pos hL (K : ℤ)) (hB k)
  have hcont := continuous_fourPointUrsell hform hc
  have hread : IsPeriodizedObservable L K β ρ f := periodizedEvaluation_holds hPer hL hK hβ hq
  exact ⟨hform, hread, ⟨hc, hcont⟩, boundsPassToLimits_holds hread hcont⟩
end YangMills.Construction.InfiniteLattice.FourPointMoments
end
