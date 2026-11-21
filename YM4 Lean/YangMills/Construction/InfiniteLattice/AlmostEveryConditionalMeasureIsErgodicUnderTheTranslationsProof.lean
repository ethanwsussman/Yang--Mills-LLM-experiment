import YangMills.Construction.InfiniteLattice.AlmostEveryConditionalMeasureIsErgodicUnderTheTranslations
import YangMills.Construction.InfiniteLattice.ConditionalExpectationGivenTheInvariantField
import YangMills.Construction.InfiniteLattice.GibbsStatesReadThroughKernelsAndSymmetries
import YangMills.Construction.InfiniteLattice.InvariantFunctionsLongRangeOrderAndErgodicMeasures
import YangMills.Construction.InfiniteLattice.MeansOfCorrelationsOverCubes
import YangMills.Construction.InfiniteLattice.TestExistenceVersionsAndIntegralOfRegularConditionalProbabilities
import YangMills.Construction.InfiniteLattice.TopologyAndDensityOnTheConfigurationsOfOneLattice
import YangMills.Construction.InfiniteLattice.VanishingLongRangeOrderOnADenseSetGivesErgodicity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticePhases
open MeasureTheory Filter InfiniteLattice
open scoped Topology ComplexConjugate
namespace ErgodicConditionals
theorem shiftInvariantSigma_le (a : ℝ) :
    shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
  fun _ h => h.1
theorem centredCubePoints_finite {a : ℝ} (ha : 0 < a) (n : ℕ+) :
    (centredCubePoints a n).Finite := by
  have hbox : (Set.Icc (fun _ : Fin 4 => -(n : ℤ)) (fun _ => (n : ℤ))).Finite := Set.finite_Icc _ _
  have himg := hbox.image (fun (x : Fin 4 → ℤ) (i : Fin 4) => (x i : ℝ) * a)
  refine Set.Finite.of_finite_image (f := fun y : LatticePoint a => (y : AmbientSpace)) (himg.subset ?_)
    (Subtype.val_injective.injOn)
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨k, hk⟩ := y.2
  refine ⟨k, ?_, funext fun i => (hk i).symm⟩
  have hcoord : ∀ i, |(k i : ℝ)| ≤ (n : ℝ) := fun i => by
    have h1 : |(y : AmbientSpace) i| ≤ PeriodicLattice.supNormVec (y : AmbientSpace) :=
      Finset.le_sup' (fun i => |(y : AmbientSpace) i|) (Finset.mem_univ i)
    have h2 : |(k i : ℝ) * a| ≤ (n : ℝ) * a := by
      rw [← hk i]
      exact h1.trans hy
    rw [abs_mul, abs_of_pos ha] at h2
    exact le_of_mul_le_mul_right h2 ha
  constructor
  · intro i
    have := (abs_le.mp (hcoord i)).1
    show -(n : ℤ) ≤ k i
    exact_mod_cast this
  · intro i
    have := (abs_le.mp (hcoord i)).2
    show k i ≤ (n : ℤ)
    exact_mod_cast this
theorem isBoundedObservable_conj_mul_shift {a : ℝ} {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) (y : LatticePoint a) :
    IsBoundedObservable fun U => conj (F U) * (shift y).actOn F U := by
  obtain ⟨hm, C, hC⟩ := hF
  refine ⟨?_, C * C, fun U => ?_⟩
  · have h2 : Measurable ((shift y).actOn F) :=
      hm.comp (shift y).continuous_pullbackField.measurable
    exact (Complex.continuous_conj.measurable.comp hm).mul h2
  · rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul (hC _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
theorem norm_eval_le {X : Type*} [MeasurableSpace X] (ρ : ProbMeasure X) {F : X → ℂ} {C : ℝ}
    (hC : ∀ x, ‖F x‖ ≤ C) : ‖ρ.eval F‖ ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := ρ.toMeasure) (Filter.Eventually.of_forall hC)
  simpa [ProbMeasure.eval] using h
theorem cubeCorrelationMean_eq_sum {a : ℝ} (ha : 0 < a) (ρ : ProbMeasure (GaugeField a))
    (F : GaugeField a → ℂ) (n : ℕ+) :
    cubeCorrelationMean ρ F n = ((centredCubePoints a n).ncard : ℂ)⁻¹ *
      ∑ y ∈ (centredCubePoints_finite ha n).toFinset,
        ρ.eval fun U => conj (F U) * (shift y).actOn F U := by
  rw [cubeCorrelationMean, finsum_mem_eq_finite_toFinset_sum _ (centredCubePoints_finite ha n)]
theorem norm_cubeCorrelationMean_le {a : ℝ} (ha : 0 < a) (ρ : ProbMeasure (GaugeField a))
    {F : GaugeField a → ℂ} {C : ℝ} (hC : ∀ U, ‖F U‖ ≤ C) (n : ℕ+) :
    ‖cubeCorrelationMean ρ F n‖ ≤ C * C := by
  have hfin := centredCubePoints_finite ha n
  have hterm : ∀ y : LatticePoint a,
      ‖ρ.eval fun U => conj (F U) * (shift y).actOn F U‖ ≤ C * C := fun y =>
    norm_eval_le ρ fun U => by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (hC _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
  have hC2 : 0 ≤ C * C := mul_self_nonneg C
  rw [cubeCorrelationMean_eq_sum ha, norm_mul, norm_inv, Complex.norm_natCast,
    Set.ncard_eq_toFinset_card _ hfin]
  set N := hfin.toFinset.card with hN
  have hsum := norm_sum_le_of_le hfin.toFinset (fun y _ => hterm y)
  rw [Finset.sum_const, nsmul_eq_mul, ← hN] at hsum
  by_cases h0 : N = 0
  · simp [h0, hC2]
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero h0
    calc (N : ℝ)⁻¹ * _ ≤ (N : ℝ)⁻¹ * (N * (C * C)) := by gcongr
      _ = C * C := by field_simp
variable (S : Setup)
def toProbMeasure (ν : periodicGibbsSet S.L S.K S.β) : ProbMeasure (GaugeField S.mesh) :=
  ⟨ν.1, ν.2.1.1⟩
theorem measurable_cubeCorrelationMean {ν : periodicGibbsSet S.L S.K S.β}
    {κ : GaugeField S.mesh → ProbMeasure (GaugeField S.mesh)}
    (hκ : IsInvariantConditionalFamily S ν κ)
    {F : GaugeField S.mesh → ℂ} (hF : IsBoundedObservable F) (n : ℕ+) :
    Measurable[shiftInvariantSigma S.mesh] fun U => cubeCorrelationMean (κ U) F n := by
  simp only [cubeCorrelationMean_eq_sum S.mesh_pos]
  exact (Finset.measurable_sum _ fun y _ =>
    (hκ _ (isBoundedObservable_conj_mul_shift hF y)).1).const_mul _
theorem integral_cubeCorrelationMean
    (hfam : InvariantConditionalFamilies.Statement)
    {ν : periodicGibbsSet S.L S.K S.β}
    {κ : GaugeField S.mesh → ProbMeasure (GaugeField S.mesh)}
    (hκ : IsInvariantConditionalFamily S ν κ)
    {F : GaugeField S.mesh → ℂ} (hF : IsBoundedObservable F) (n : ℕ+) :
    ∫ U, cubeCorrelationMean (κ U) F n ∂(toProbMeasure S ν).toMeasure =
      cubeCorrelationMean (toProbMeasure S ν) F n := by
  simp only [cubeCorrelationMean_eq_sum S.mesh_pos]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    exact ((hfam S ν).2.2.2 κ hκ _ (isBoundedObservable_conj_mul_shift hF y)).symm
  · intro y _
    obtain ⟨hm, C, hC⟩ := isBoundedObservable_conj_mul_shift hF y
    exact Integrable.of_bound
      (((hκ _ (isBoundedObservable_conj_mul_shift hF y)).1.mono (shiftInvariantSigma_le S.mesh)
        le_rfl).aestronglyMeasurable)
      C (Filter.Eventually.of_forall fun U => norm_eval_le _ hC)
theorem measurable_of_tendsto_pnat {Ω : Type*} (m : MeasurableSpace Ω) {f : ℕ+ → Ω → ℂ}
    {g : Ω → ℂ} (hf : ∀ n, Measurable[m] (f n))
    (hg : ∀ U, Tendsto (fun n => f n U) atTop (𝓝 (g U))) : Measurable[m] g :=
  measurable_of_tendsto_metrizable' atTop hf (tendsto_pi_nhds.2 hg)
theorem ae_plateauVariance_eq_zero
    (hgibbs : AlmostEveryConditionalIsPeriodicGibbs)
    (hmeans : CorrelationMeansConverge)
    (hinvariant : InvariantFunctionsAndErgodicity)
    (hfam : InvariantConditionalFamilies.Statement)
    (hkern : GibbsKernelsAndSymmetries.Assertion)
    (hcond : CondExpInvariant.Claim)
    {ν : periodicGibbsSet S.L S.K S.β}
    {κ : GaugeField S.mesh → ProbMeasure (GaugeField S.mesh)}
    (hκ : IsInvariantConditionalFamily S ν κ)
    {F : GaugeField S.mesh → ℂ} (hF : IsBoundedObservable F) :
    MeasurableSet[shiftInvariantSigma S.mesh]
        {U | U ∈ conditionalGibbsLocus S κ ∧
          plateauVariance (κ U).toMeasure F = 0} ∧
      ∀ᵐ U ∂(toProbMeasure S ν).toMeasure, U ∈ conditionalGibbsLocus S κ →
        plateauVariance (κ U).toMeasure F = 0 := by
  obtain ⟨hV, hν, hper⟩ := hgibbs S ν κ hκ
  set μ : Measure (GaugeField S.mesh) := (toProbMeasure S ν).toMeasure with hμ
  set V := conditionalGibbsLocus S κ with hVdef
  have hinvU : ∀ U ∈ V, IsShiftInvariant (κ U).toMeasure := fun U hU =>
    ((hkern S S.β S.β_pos).2.1 (κ U) (hper U hU)).2.1
  have hνinv : IsShiftInvariant μ :=
    ((hkern S S.β S.β_pos).2.1 (toProbMeasure S ν) ν.2).2.1
  have hVb : MeasurableSet V := shiftInvariantSigma_le _ _ hV
  have hVae : ∀ᵐ U ∂μ, U ∈ V := mem_ae_iff.2 ((prob_compl_eq_zero_iff hVb).2 hν)
  obtain ⟨-, C, hC⟩ := id hF
  set P : GaugeField S.mesh → ℂ := fun U => plateauPairing (κ U).toMeasure F F with hP
  set w : GaugeField S.mesh → ℂ := fun U => ((‖(κ U).eval F‖ ^ 2 : ℝ) : ℂ) with hw
  have hvalm : Measurable[shiftInvariantSigma S.mesh] fun U => (κ U).eval F := (hκ F hF).1
  have hwm : Measurable[shiftInvariantSigma S.mesh] w :=
    (show Measurable fun z : ℂ => ((‖z‖ ^ 2 : ℝ) : ℂ) by fun_prop).comp hvalm
  have hlim : ∀ U ∈ V, Tendsto (fun n => cubeCorrelationMean (κ U) F n) atTop (𝓝 (P U)) :=
    fun U hU => (hmeans S (κ U) F (hinvU U hU) hF).1
  have hbound : ∀ n U, ‖cubeCorrelationMean (κ U) F n‖ ≤ C * C := fun n U =>
    norm_cubeCorrelationMean_le S.mesh_pos (κ U) hC n
  have hPm : Measurable[shiftInvariantSigma S.mesh] (V.indicator P) := by
    refine measurable_of_tendsto_pnat (shiftInvariantSigma S.mesh)
      (f := fun n => V.indicator fun U => cubeCorrelationMean (κ U) F n)
      (fun n => (measurable_cubeCorrelationMean S hκ hF n).indicator hV) fun U => ?_
    by_cases hU : U ∈ V
    · simpa [Set.indicator_of_mem hU] using hlim U hU
    · simp [Set.indicator_of_notMem hU]
  have hPb : ∀ U, ‖V.indicator P U‖ ≤ C * C := fun U => by
    by_cases hU : U ∈ V
    · rw [Set.indicator_of_mem hU]
      exact le_of_tendsto (hlim U hU).norm (Filter.Eventually.of_forall fun n => hbound n U)
    · rw [Set.indicator_of_notMem hU, norm_zero]
      exact mul_self_nonneg C
  have hPi : Integrable (V.indicator P) μ :=
    Integrable.of_bound (hPm.mono (shiftInvariantSigma_le S.mesh) le_rfl).aestronglyMeasurable
      (C * C) (Filter.Eventually.of_forall hPb)
  have hwb : ∀ U, ‖w U‖ ≤ C * C := fun U => by
    have h := norm_eval_le (κ U) hC
    have hn : ‖w U‖ = ‖(κ U).eval F‖ ^ 2 := by
      simp only [hw, Complex.norm_real, norm_pow, norm_norm]
    rw [hn, sq]
    exact mul_le_mul h h (norm_nonneg _) ((norm_nonneg _).trans h)
  have hwi : Integrable w μ :=
    Integrable.of_bound (hwm.mono (shiftInvariantSigma_le S.mesh) le_rfl).aestronglyMeasurable
      (C * C) (Filter.Eventually.of_forall hwb)
  have hint1 : ∫ U, V.indicator P U ∂μ = plateauPairing μ F F := by
    have hdct : Tendsto (fun n : ℕ+ => ∫ U, cubeCorrelationMean (κ U) F n ∂μ) atTop
        (𝓝 (∫ U, V.indicator P U ∂μ)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun _ => C * C)
        (Filter.Eventually.of_forall fun n =>
          ((measurable_cubeCorrelationMean S hκ hF n).mono (shiftInvariantSigma_le S.mesh)
            le_rfl).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun U => hbound n U)
        (integrable_const _) (hVae.mono fun U hU => ?_)
      simpa [Set.indicator_of_mem hU] using hlim U hU
    exact tendsto_nhds_unique (hdct.congr fun n => integral_cubeCorrelationMean S hfam hκ hF n)
      (hmeans S (toProbMeasure S ν) F hνinv hF).1
  have hint2 : ∫ U, w U ∂μ = plateauPairing μ F F := by
    have hY := ((hfam S ν).2.2.1 κ hκ F hF).1
    obtain ⟨-, -, -, -, ⟨-, hpl, -, -⟩⟩ := hcond S μ hνinv F F hF hF
    rw [← (hpl _ _ hY hY).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    show ((‖(κ U).eval F‖ ^ 2 : ℝ) : ℂ) = conj ((κ U).eval F) * (κ U).eval F
    rw [Complex.conj_mul']
    push_cast
    rfl
  set q : GaugeField S.mesh → ℂ :=
    V.indicator fun U => plateauVariance (κ U).toMeasure F with hq
  have hq_eq : q = V.indicator P - V.indicator w := by
    funext U
    by_cases hU : U ∈ V
    · simp only [hq, Pi.sub_apply, Set.indicator_of_mem hU]
      rfl
    · simp [hq, Set.indicator_of_notMem hU]
  have hqm : Measurable[shiftInvariantSigma S.mesh] q := by
    rw [hq_eq]
    exact hPm.sub (hwm.indicator hV)
  have hqi : Integrable q μ := by
    rw [hq_eq]
    exact hPi.sub (hwi.indicator hVb)
  have hqint : ∫ U, q U ∂μ = 0 := by
    have hae : q =ᵐ[μ] fun U => V.indicator P U - w U :=
      hVae.mono fun U hU => by simp [hq_eq, Set.indicator_of_mem hU]
    rw [integral_congr_ae hae, integral_sub hPi hwi, hint1, hint2, sub_self]
  have hqre : ∀ U, 0 ≤ (q U).re ∧ q U = (((q U).re : ℝ) : ℂ) := fun U => by
    by_cases hU : U ∈ V
    · obtain ⟨⟨Y, hY⟩, -⟩ := (hcond S (κ U).toMeasure (hinvU U hU) F F hF hF).1
      obtain ⟨h1, h2⟩ := (hinvariant S).2.1 (κ U) (hinvU U hU) F hF Y hY
      have hqU : q U = ((varianceOf (κ U).toMeasure Y : ℝ) : ℂ) := by
        simp only [hq, Set.indicator_of_mem hU]
        exact h1
      rw [hqU]
      simpa using h2
    · simp [hq, Set.indicator_of_notMem hU]
  have hti : Integrable (fun U => (q U).re) μ := hqi.re
  have htint : ∫ U, (q U).re ∂μ = 0 := by
    have h : (((∫ U, (q U).re ∂μ : ℝ)) : ℂ) = ∫ U, q U ∂μ := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Filter.Eventually.of_forall fun U => (hqre U).2.symm)
    rw [hqint] at h
    exact_mod_cast h
  have hzero := (integral_eq_zero_iff_of_nonneg (fun U => (hqre U).1) hti).1 htint
  refine ⟨?_, ?_⟩
  · have hset : {U | U ∈ V ∧ plateauVariance (κ U).toMeasure F = 0} = V ∩ q ⁻¹' {0} := by
      ext U
      constructor
      · rintro ⟨hU, h0⟩
        refine ⟨hU, ?_⟩
        simp [hq, Set.indicator_of_mem hU, h0]
      · rintro ⟨hU, h0⟩
        refine ⟨hU, ?_⟩
        have h0' : q U = 0 := h0
        simpa [hq, Set.indicator_of_mem hU] using h0'
    rw [hset]
    exact hV.inter (hqm (measurableSet_singleton 0))
  · filter_upwards [hzero] with U hU hUV
    have h1 : q U = 0 := by
      rw [(hqre U).2]
      have hU' : (q U).re = 0 := hU
      rw [hU']
      simp
    simpa [hq, Set.indicator_of_mem hUV] using h1
theorem dense_denseLocalSet (htop : TopologyDensityHolds) (S : Setup)
    (hsub : ∀ G ∈ S.denseLocalSet, Continuous G)
    (hdense : ∀ F ∈ continuousLocalFunctions S.mesh, ∀ ε : ℝ, 0 < ε →
      ∃ H ∈ S.denseLocalSet, uniformSup (F - H) < ε)
    (F : C(GaugeField S.mesh, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ B ∈ {B : C(GaugeField S.mesh, ℂ) | (B : GaugeField S.mesh → ℂ) ∈ S.denseLocalSet},
      uniformSup (fun U => F U - B U) < ε := by
  have htd := htop S
  have hcomp : CompactSpace (GaugeField S.mesh) := htd.compact
  obtain ⟨H, hH, hFH⟩ := htd.dense_local.2 F F.continuous (ε / 2) (half_pos hε)
  obtain ⟨G, hG, hHG⟩ := hdense H hH (ε / 2) (half_pos hε)
  have hHc : Continuous H := (htd.dense_local.1 hH)
  have hGc : Continuous G := hsub G hG
  refine ⟨⟨G, hGc⟩, hG, ?_⟩
  have hb1 : BddAbove (Set.range fun U => ‖(⇑F - H) U‖) :=
    (isCompact_range (F.continuous.sub hHc).norm).bddAbove
  have hb2 : BddAbove (Set.range fun U => ‖(H - G) U‖) :=
    (isCompact_range (hHc.sub hGc).norm).bddAbove
  have hle : uniformSup (fun U => F U - G U) ≤ uniformSup (⇑F - H) + uniformSup (H - G) := by
    refine Real.iSup_le (fun U => ?_) (add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)
      (Real.iSup_nonneg fun _ => norm_nonneg _))
    have h1 : ‖(⇑F - H) U‖ ≤ uniformSup (⇑F - H) := le_ciSup hb1 U
    have h2 : ‖(H - G) U‖ ≤ uniformSup (H - G) := le_ciSup hb2 U
    calc ‖F U - G U‖ = ‖(⇑F - H) U + (H - G) U‖ := by simp
      _ ≤ ‖(⇑F - H) U‖ + ‖(H - G) U‖ := norm_add_le _ _
      _ ≤ _ := add_le_add h1 h2
  show uniformSup (fun U => F U - G U) < ε
  linarith
theorem almostEveryConditionalIsErgodic
    (hgibbs : AlmostEveryConditionalIsPeriodicGibbs)
    (hcrit : ShiftErgodicityCriterion.Statement)
    (hmeans : CorrelationMeansConverge)
    (hinvariant : InvariantFunctionsAndErgodicity)
    (hfam : InvariantConditionalFamilies.Statement)
    (hkern : GibbsKernelsAndSymmetries.Assertion)
    (htop : TopologyDensityHolds)
    (hcond : CondExpInvariant.Claim) :
    AlmostEveryConditionalIsErgodic := by
  intro S ν κ hκ
  set μ : Measure (GaugeField S.mesh) := (toProbMeasure S ν).toMeasure with hμ
  have htd := htop S
  have hspec : IsCountableDenseLocal S.mesh S.denseLocalSet :=
    denseLocalSet_spec S.L S.K (by
      obtain ⟨B, hc, hd, -⟩ := htd.countable_dense_local
      exact ⟨B, hd.1, hc, hd.2⟩)
  obtain ⟨hsub, hcount, hdense⟩ := hspec
  obtain ⟨hV, hν, hper⟩ := hgibbs S ν κ hκ
  have hobs : ∀ B ∈ S.denseLocalSet, IsBoundedObservable B := fun B hB => (hsub hB).1
  have hcont : ∀ B ∈ S.denseLocalSet, Continuous B :=
    fun B hB => htd.dense_local.1 (hsub hB)
  have hone := fun B (hB : B ∈ S.denseLocalSet) =>
    ae_plateauVariance_eq_zero S hgibbs hmeans hinvariant hfam hkern hcond hκ (hobs B hB)
  have hset : ergodicConditionalLocus S κ =
      conditionalGibbsLocus S κ ∩
        ⋂ B ∈ S.denseLocalSet, {U | U ∈ conditionalGibbsLocus S κ ∧
          plateauVariance (κ U).toMeasure B = 0} := by
    ext U
    simp only [ergodicConditionalLocus, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_iInter]
    exact ⟨fun h => ⟨h.1, fun B hB => ⟨h.1, h.2 B hB⟩⟩, fun h => ⟨h.1, fun B hB => (h.2 B hB).2⟩⟩
  have hmeas : MeasurableSet[shiftInvariantSigma S.mesh] (ergodicConditionalLocus S κ) := by
    rw [hset]
    exact hV.inter (MeasurableSet.biInter hcount fun B hB => (hone B hB).1)
  refine ⟨hmeas, ?_, fun U hU => ?_⟩
  · have hVb : MeasurableSet (conditionalGibbsLocus S κ) :=
      shiftInvariantSigma_le _ _ hV
    have hVae : ∀ᵐ U ∂μ, U ∈ conditionalGibbsLocus S κ :=
      mem_ae_iff.2 ((prob_compl_eq_zero_iff hVb).2 hν)
    have hall := (ae_ball_iff hcount).2 fun B hB => (hone B hB).2
    have hae : ∀ᵐ U ∂μ, U ∈ ergodicConditionalLocus S κ := by
      filter_upwards [hVae, hall] with U hU h
      exact ⟨hU, fun B hB => h B hB hU⟩
    exact (prob_compl_eq_zero_iff (μ := μ) (shiftInvariantSigma_le _ _ hmeas)).1 (mem_ae_iff.1 hae)
  · have hp := hper U hU.1
    have hinv : IsShiftInvariant (κ U).toMeasure :=
      ((hkern S S.β S.β_pos).2.1 (κ U) hp).2.1
    exact ⟨hp, hinv, hcrit S (κ U) {B | (B : GaugeField S.mesh → ℂ) ∈ S.denseLocalSet} hinv
      (dense_denseLocalSet htop S hcont hdense) fun B hB => hU.2 B hB⟩
end ErgodicConditionals
end YangMills.Construction.LatticePhases
