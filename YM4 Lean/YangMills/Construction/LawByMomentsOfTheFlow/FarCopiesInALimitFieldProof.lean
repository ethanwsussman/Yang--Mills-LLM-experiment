import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslationsProof
import YangMills.Construction.FreeEnergiesOfTheFlow.MeansGivenAStateReadTheCases
import YangMills.Construction.HullsInEveryVolume.NoisesCarryTheChain
import YangMills.Construction.HullsInEveryVolume.TheChainOfTheNoisesIsBorel
import YangMills.Construction.LawByMomentsOfTheFlow.CopiesGivenAField
import YangMills.Construction.LawByMomentsOfTheFlow.FarCopiesThatDecorrelateHaveOneMean
import YangMills.Construction.LawByMomentsOfTheFlow.FarFunctionsAreNearlyIndependent
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAlongTheTelescopeProof
import YangMills.Construction.LawByMomentsOfTheFlow.NearFunctionsMoveWithATranslation
import YangMills.Construction.LawByMomentsOfTheFlow.TheChainMovesWithATranslation
import YangMills.Construction.ResponseInTheExpansion.ChainIsMarkovBackwards
import YangMills.Construction.ResponseInTheExpansion.StatesAreReadFromAbove
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction
open WeightedResponses ResponseInTheExpansion StepSettings StepCosts TorusFields TorusLumps RenormalizationStepParameters HullTrees ChainNoise FreeEnergies
  MomentMethod HullsInEveryVolume BaseTranslations ClusterExpansionOfAStep CellWindows
namespace MomentLaw
namespace FarCopiesConditional
section Truncation
variable {R : StepSetup} {n : ℕ} [NeZero n]
private def supportSize (A : Finset (TorusSite (n * R.params.side))) (sz : R.labels.Ω → ℝ) (Yt : Finset (TorusSite (n * R.params.side)))
    (ωt : Yt → R.labels.Ω) : ℝ :=
  1 + ∑ y ∈ A, siteScore sz Yt ωt y
open Classical in
private def truncateCase (A : Finset (TorusSite (n * R.params.side))) (sz : R.labels.Ω → ℝ) (B : ℝ) (F : CaseFunction R n) :
    CaseFunction R n :=
  fun W Yt ωt bad b => if supportSize A sz Yt ωt ≤ B then F W Yt ωt bad b else 0
private theorem one_le_supportSize {A : Finset (TorusSite (n * R.params.side))} {sz : R.labels.Ω → ℝ} (h0 : ∀ w, 0 ≤ sz w)
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω) : 1 ≤ supportSize A sz Yt ωt := by
  unfold supportSize
  have : 0 ≤ ∑ y ∈ A, siteScore sz Yt ωt y := Finset.sum_nonneg fun y _ => by
    unfold siteScore
    split_ifs
    · exact h0 _
    · exact le_rfl
  linarith
private theorem measurable_supportSize {A : Finset (TorusSite (n * R.params.side))} {sz : R.labels.Ω → ℝ} (hs : Measurable sz)
    (Yt : Finset (TorusSite (n * R.params.side))) : Measurable fun ωt : Yt → R.labels.Ω => supportSize A sz Yt ωt := by
  classical
  unfold supportSize
  refine measurable_const.add (Finset.measurable_sum _ fun y _ => ?_)
  unfold siteScore
  by_cases hy : y ∈ Yt
  · simp only [dif_pos hy]
    exact hs.comp (measurable_pi_apply _)
  · simp only [dif_neg hy]
    exact measurable_const
private theorem mem_supBall_add {m : ℕ} [NeZero m] {o y : TorusSite m} {a b : ℝ} (hb : 0 ≤ b) (h : y ∈ supBall o a) :
    y ∈ supBall o (a + b) :=
  Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1, (Finset.mem_filter.mp h).2.trans (by linarith)⟩
private theorem truncateCase_nearlyLocal {o : TorusSite (n * R.params.side)} {Rr a : ℕ} {Sz : ℝ}
    {A : Finset (TorusSite (n * R.params.side))} {sz : R.labels.Ω → ℝ} {F : CaseFunction R n}
    (h : IsQuasiLocalCaseFunction R o Rr a Sz A sz F) {B : ℝ} (hB : 1 ≤ B) (hSz : 0 ≤ Sz) :
    IsNearlyLocalCaseFunction R o Rr (Sz * B ^ a) (truncateCase A sz B F) := by
  classical
  have hpow : ∀ {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω}, supportSize A sz Yt ωt ≤ B →
      Sz * (1 + ∑ y ∈ A, siteScore sz Yt ωt y) ^ a ≤ Sz * B ^ a := by
    intro Yt ωt hN
    have h1 := one_le_supportSize (A := A) h.weight_nonneg Yt ωt
    unfold supportSize at h1 hN
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hN a) hSz
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W Yt ωt bad b
    unfold truncateCase
    split_ifs with hN
    · exact (h.abs_le _ _ _ _ _).trans (hpow hN)
    · rw [abs_zero]
      positivity
  · intro Yt bad b
    unfold truncateCase
    refine Measurable.ite ?_ (h.measurable Yt bad b) measurable_const
    exact measurableSet_le ((measurable_supportSize h.weight_measurable Yt).comp measurable_snd) measurable_const
  · intro W Yt ωt bad b u hl hb hc
    have e : supportSize A sz Yt (R.labels.act Yt u ωt) = supportSize A sz Yt ωt := by
      unfold supportSize
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      unfold siteScore
      by_cases hy : y ∈ Yt
      · simp only [dif_pos hy]
        exact h.weight_gauge Yt u ωt ⟨y, hy⟩
      · simp only [dif_neg hy]
    unfold truncateCase
    rw [e, h.gaugeInvariant W Yt ωt bad b u hl hb hc]
  · intro m hm W W' Yt Yt' ωt ωt' bad bad' b b' hl hl' hw hY hbase
    have e : supportSize A sz Yt ωt = supportSize A sz Yt' ωt' := by
      unfold supportSize
      congr 1
      refine Finset.sum_congr rfl fun y hy => ?_
      obtain ⟨h1, h2⟩ := hY y (mem_supBall_add (Nat.cast_nonneg m) (h.mem_ball y hy))
      unfold siteScore
      by_cases hy' : y ∈ Yt
      · simp only [dif_pos hy', dif_pos (h1.mp hy')]
        rw [h2 hy' (h1.mp hy')]
      · simp only [dif_neg hy', dif_neg (fun q => hy' (h1.mpr q))]
    unfold truncateCase
    rw [← e]
    split_ifs with hN
    · refine (h.sub_le_of_agree m hm W W' Yt Yt' ωt ωt' bad bad' b b' hl hl' hw hY hbase).trans ?_
      exact mul_le_mul_of_nonneg_right (hpow hN) (Real.exp_pos _).le
    · rw [sub_zero, abs_zero]
      positivity
end Truncation
section Translation
variable {ℓ : StepParameters}
private def translateFamily (T : StageTower ℓ) (u n : ℕ) [NeZero n] (v : Fin 4 → ℤ)
    (Ψ : TorusField n → CaseFunction (T.stage u).toStepSetup n) : TorusField n → CaseFunction (T.stage u).toStepSetup n :=
  fun V => translateCaseFunction v (Ψ (TorusFields.translate (siteOfInt v) V))
private theorem topField_translateSample (s n : ℕ) [NeZero n] (v : Fin 4 → ℤ) (x : MarkedSample ℓ s n) :
    topField ℓ s n (translateSample s n v x) = TorusFields.translate (siteOfInt v) (topField ℓ s n x) := by
  cases s <;> rfl
private theorem caseLift_translateSample (T : StageTower ℓ) (u n : ℕ) [NeZero n] (v : Fin 4 → ℤ)
    (Ψ : TorusField n → CaseFunction (T.stage u).toStepSetup n) (x : MarkedSample ℓ (u + 1) n)
    (hst : stageState T u (n * ℓ.side) (translateSample u (n * ℓ.side) (fun i => (ℓ.side : ℤ) * v i) x.1) =
      translateStageState T u (n * ℓ.side) (fun i => (ℓ.side : ℤ) * v i) (stageState T u (n * ℓ.side) x.1)) :
    caseLift T u n Ψ (translateSample (u + 1) n v x) = caseLift T u n (translateFamily T u n v Ψ) x := by
  show Ψ (TorusFields.translate (siteOfInt v) x.2.2.1) (topField ℓ u (n * ℓ.side) (translateSample u (n * ℓ.side) (fun i => (ℓ.side : ℤ) * v i) x.1))
      (stageState T u (n * ℓ.side) (translateSample u (n * ℓ.side) (fun i => (ℓ.side : ℤ) * v i) x.1)).2.1
      (stageState T u (n * ℓ.side) (translateSample u (n * ℓ.side) (fun i => (ℓ.side : ℤ) * v i) x.1)).2.2
      (translateBonds (siteOfInt fun i => (ℓ.side : ℤ) * v i) x.2.2.2) (translateBases v x.2.1) = _
  rw [hst, topField_translateSample]
  rfl
private theorem sampleBelow_translateSample (t : ℕ) : ∀ (d n : ℕ) [NeZero n] (v : Fin 4 → ℤ) (x : MarkedSample ℓ (t + d) n),
    sampleBelow ℓ t d n (translateSample (t + d) n v x) =
      translateSample t (fineSide ℓ.side d n) (fun i => (ℓ.side : ℤ) ^ d * v i) (sampleBelow ℓ t d n x) := by
  intro d
  induction d with
  | zero =>
    intro n _ v x
    have e : (fun i => (ℓ.side : ℤ) ^ 0 * v i) = v := by
      funext i
      simp
    rw [e]
    rfl
  | succ d ih =>
    intro n _ v x
    have e : (fun i => (ℓ.side : ℤ) ^ (d + 1) * v i) = fun i => (ℓ.side : ℤ) ^ d * ((ℓ.side : ℤ) * v i) := by
      funext i
      ring
    rw [e]
    exact ih (n * ℓ.side) (fun i => (ℓ.side : ℤ) * v i) x.1
end Translation
section Cases
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem measurable_fieldWithStoredLinks (q : CoarseState R n) : Measurable q.fieldWithStoredLinks := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fieldWithStoredLinks <;> assumption
private theorem measurable_fillLabels (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable (q.fillLabels Yt) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fillLabels <;> assumption
private theorem caseIntegrable_of_bounded (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n) {F : CaseFunction R n}
    (h1 : CaseIntegrable R C V q fun _ _ _ _ _ => 1)
    (hFm : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => F p.1 Yt p.2 bad b) {U : ℝ} (hU : 0 ≤ U)
    (hle : ∀ W Yt ωt bad b, |F W Yt ωt bad b| ≤ U) : CaseIntegrable R C V q F := by
  classical
  intro bad hbad Yt b
  have e : (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) => caseTerm R C V q F bad Yt b p.1 p.2) =
      fun p => F (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b *
        caseTerm R C V q (fun _ _ _ _ _ => 1) bad Yt b p.1 p.2 := by
    funext p
    unfold caseTerm
    split_ifs <;> simp
  have hm : AEStronglyMeasurable (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      caseTerm R C V q F bad Yt b p.1 p.2) ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) := by
    rw [e]
    exact ((hFm Yt bad b).comp (((measurable_fieldWithStoredLinks q).comp measurable_fst).prodMk
      ((measurable_fillLabels q Yt).comp measurable_snd))).aestronglyMeasurable.mul (h1 bad hbad Yt b).1
  refine Integrable.mono' ((h1 bad hbad Yt b).norm.const_mul U) hm (Filter.Eventually.of_forall fun p => ?_)
  show ‖caseTerm R C V q F bad Yt b p.1 p.2‖ ≤ U * ‖caseTerm R C V q (fun _ _ _ _ _ => 1) bad Yt b p.1 p.2‖
  have e' : caseTerm R C V q F bad Yt b p.1 p.2 = F (q.fieldWithStoredLinks p.1) Yt (q.fillLabels Yt p.2) bad b *
      caseTerm R C V q (fun _ _ _ _ _ => 1) bad Yt b p.1 p.2 := congrFun e p
  rw [e', Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hle _ _ _ _ _) (abs_nonneg _)
abbrev _root_.YangMills.SharedProofs.p19766 := @caseIntegrable_of_bounded
private theorem tendsto_caseMean_truncate {C : Finset (TorusSite n)} {V : TorusField n} {q : CoarseState R n}
    {A : Finset (TorusSite (n * R.params.side))} {sz : R.labels.Ω → ℝ}
    (hs : Measurable sz) {F : CaseFunction R n} (hF : CaseIntegrable R C V q F) :
    Tendsto (fun j : ℕ => caseMean R C V q (truncateCase A sz ((j : ℝ) + 1) F)) atTop (𝓝 (caseMean R C V q F)) := by
  classical
  unfold caseMean
  refine Tendsto.div_const ?_ _
  unfold caseIntegral
  refine tendsto_finsetSum _ fun bad hbad => tendsto_finsetSum _ fun Yt _ => tendsto_finsetSum _ fun b _ => ?_
  have hI := hF bad hbad Yt b
  have e : ∀ (j : ℕ) (p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω)),
      caseTerm R C V q (truncateCase A sz ((j : ℝ) + 1) F) bad Yt b p.1 p.2 =
      if supportSize A sz Yt (q.fillLabels Yt p.2) ≤ (j : ℝ) + 1 then caseTerm R C V q F bad Yt b p.1 p.2 else 0 := by
    intro j p
    unfold caseTerm truncateCase
    split_ifs <;> simp
  have hset : ∀ j : ℕ, MeasurableSet {p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) |
      supportSize A sz Yt (q.fillLabels Yt p.2) ≤ (j : ℝ) + 1} := fun j =>
    measurableSet_le ((measurable_supportSize hs Yt).comp ((measurable_fillLabels q Yt).comp measurable_snd)) measurable_const
  have hIj : ∀ j : ℕ, Integrable (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      caseTerm R C V q (truncateCase A sz ((j : ℝ) + 1) F) bad Yt b p.1 p.2)
      ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) := by
    intro j
    have e2 : (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
        caseTerm R C V q (truncateCase A sz ((j : ℝ) + 1) F) bad Yt b p.1 p.2) =
        Set.indicator {p | supportSize A sz Yt (q.fillLabels Yt p.2) ≤ (j : ℝ) + 1} fun p => caseTerm R C V q F bad Yt b p.1 p.2 := by
      funext p
      rw [e j p]
      simp [Set.indicator]
    rw [e2]
    exact hI.indicator (hset j)
  have hprod : ∀ j : ℕ, ∫ W, ∫ ν, caseTerm R C V q (truncateCase A sz ((j : ℝ) + 1) F) bad Yt b W ν
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∫ p, caseTerm R C V q (truncateCase A sz ((j : ℝ) + 1) F) bad Yt b p.1 p.2
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) := fun j =>
    (integral_prod _ (hIj j)).symm
  have hlim : ∫ W, ∫ ν, caseTerm R C V q F bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∫ p, caseTerm R C V q F bad Yt b p.1 p.2 ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ)) :=
    (integral_prod _ hI).symm
  simp_rw [hprod, hlim]
  refine tendsto_integral_of_dominated_convergence (fun p => ‖caseTerm R C V q F bad Yt b p.1 p.2‖) (fun j => (hIj j).1) hI.norm
    (fun j => Filter.Eventually.of_forall fun p => ?_) (Filter.Eventually.of_forall fun p => ?_)
  · rw [e j p]
    split_ifs
    · exact le_rfl
    · simp
  · refine tendsto_const_nhds.congr' ?_
    obtain ⟨j₀, hj₀⟩ := exists_nat_ge (supportSize A sz Yt (q.fillLabels Yt p.2))
    filter_upwards [eventually_ge_atTop j₀] with j hj
    rw [e j p, if_pos]
    have : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
    linarith
end Cases
section ConditionalExpectations
private theorem condExp_comp_measurePreserving {Ω Ω' Z : Type} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [mZ : MeasurableSpace Z] {μ : Measure Ω}
    {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] {π : Ω → Ω'} (hπ : MeasurePreserving π μ μ') {φ : Ω' → Z}
    (hφ : Measurable φ) {f : Ω' → ℝ} (hf : Integrable f μ') :
    μ[f ∘ π | (MeasurableSpace.comap φ mZ).comap π] =ᵐ[μ] (μ'[f | MeasurableSpace.comap φ mZ]) ∘ π := by
  have hm' : MeasurableSpace.comap φ mZ ≤ mΩ' := hφ.comap_le
  have hle : (MeasurableSpace.comap φ mZ).comap π ≤ mΩ := (MeasurableSpace.comap_mono hm').trans hπ.measurable.comap_le
  have hfi : Integrable (f ∘ π) μ := hπ.integrable_comp_of_integrable hf
  have hcm : @Measurable _ _ ((MeasurableSpace.comap φ mZ).comap π) (MeasurableSpace.comap φ mZ) π :=
    measurable_iff_comap_le.mpr le_rfl
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hle hfi ?_ ?_ ?_
  · intro s _ _
    exact (hπ.integrable_comp_of_integrable integrable_condExp).integrableOn
  · rintro s ⟨t, ht, rfl⟩ _
    have ht' : MeasurableSet t := hm' t ht
    have e1 : ∫ x in π ⁻¹' t, (μ'[f | MeasurableSpace.comap φ mZ] ∘ π) x ∂μ =
        ∫ y in t, (μ'[f | MeasurableSpace.comap φ mZ]) y ∂μ' := by
      rw [← hπ.map_eq]
      refine (setIntegral_map ht' ?_ hπ.measurable.aemeasurable).symm
      rw [hπ.map_eq]
      exact (stronglyMeasurable_condExp.mono hm').aestronglyMeasurable
    have e2 : ∫ x in π ⁻¹' t, (f ∘ π) x ∂μ = ∫ y in t, f y ∂μ' := by
      rw [← hπ.map_eq]
      refine (setIntegral_map ht' ?_ hπ.measurable.aemeasurable).symm
      rw [hπ.map_eq]
      exact hf.aestronglyMeasurable
    rw [e1, e2]
    exact setIntegral_condExp hm' hf ht
  · exact (stronglyMeasurable_condExp.comp_measurable hcm).aestronglyMeasurable
end ConditionalExpectations
section Torus
variable {ℓ : StepParameters}
private structure TorusData (T : StageTower ℓ) (β : ℝ) (u d n : ℕ) [NeZero n] : Prop where
  prob : IsProbabilityMeasure (markedSampleLaw T β (u + 1 + d) n)
  prob' : IsProbabilityMeasure (markedSampleLaw T β (u + 1) (fineSide ℓ.side d n))
  below : MeasurePreserving (sampleBelow ℓ (u + 1) d n) (markedSampleLaw T β (u + 1 + d) n)
    (markedSampleLaw T β (u + 1) (fineSide ℓ.side d n))
  upper : upperSigma T (u + 1) d n ≤ markedSampleMeasurableSpace ℓ (u + 1 + d) n
  state : Measurable (stageState T (u + 1) (fineSide ℓ.side d n))
  markov : ∀ (G : MarkedSample ℓ (u + 1) (fineSide ℓ.side d n) → ℝ) (B : ℝ), Measurable G → (∀ v, |G v| ≤ B) →
    (markedSampleLaw T β (u + 1 + d) n)[fun w => G (sampleBelow ℓ (u + 1) d n w) | upperSigma T (u + 1) d n]
      =ᵐ[markedSampleLaw T β (u + 1 + d) n]
      (markedSampleLaw T β (u + 1 + d) n)[fun w => G (sampleBelow ℓ (u + 1) d n w) |
        (stageSigma T (u + 1) (fineSide ℓ.side d n)).comap (sampleBelow ℓ (u + 1) d n)]
  read : ReadsCasesAt T β u (fineSide ℓ.side d n)
  one : ∀ᵐ x ∂(markedSampleLaw T β (u + 1) (fineSide ℓ.side d n)),
    CaseIntegrableAtSample T u (fineSide ℓ.side d n) (fun _ _ _ _ _ _ => 1) x
variable {T : StageTower ℓ} {β : ℝ} {u d n : ℕ} [NeZero n]
private theorem condExp_upper_eq_caseMean (h : TorusData T β u d n)
    (Ψ : TorusField (fineSide ℓ.side d n) → CaseFunction (T.stage u).toStepSetup (fineSide ℓ.side d n))
    (hm : Measurable (caseLift T u _ Ψ)) {K : ℝ} (hb : ∀ x, |caseLift T u _ Ψ x| ≤ K)
    (hi : ∀ᵐ x ∂(markedSampleLaw T β (u + 1) (fineSide ℓ.side d n)), CaseIntegrableAtSample T u _ Ψ x) :
    (markedSampleLaw T β (u + 1 + d) n)[fun w => caseLift T u _ Ψ (sampleBelow ℓ (u + 1) d n w) | upperSigma T (u + 1) d n]
      =ᵐ[markedSampleLaw T β (u + 1 + d) n] fun w => caseMeanAtSample T u _ Ψ (sampleBelow ℓ (u + 1) d n w) := by
  haveI := h.prob
  haveI := h.prob'
  have hint : Integrable (caseLift T u _ Ψ) (markedSampleLaw T β (u + 1) (fineSide ℓ.side d n)) :=
    Integrable.of_bound hm.aestronglyMeasurable K (ae_of_all _ fun x => by simpa using hb x)
  have r := (h.read.2 h.one).1 Ψ hm K (ae_of_all _ hb) hi
  refine (h.markov _ K hm hb).trans ?_
  refine (condExp_comp_measurePreserving h.below h.state hint).trans ?_
  exact h.below.quasiMeasurePreserving.ae_eq_comp r
private theorem caseLift_truncate (Φ : TorusField (fineSide ℓ.side d n) → CaseFunction (T.stage u).toStepSetup (fineSide ℓ.side d n))
    (A : Finset (TorusSite (fineSide ℓ.side d n * ℓ.side))) (sz : (T.stage u).labels.Ω → ℝ) (B : ℝ)
    (x : MarkedSample ℓ (u + 1) (fineSide ℓ.side d n)) :
    caseLift T u _ (fun V => truncateCase A sz B (Φ V)) x =
      open Classical in if supportWeightOfSample T u _ A sz x ≤ B then caseLift T u _ Φ x else 0 := rfl
private theorem condExp_upper_eq_caseMean_of_truncations (h : TorusData T β u d n)
    (Φ : TorusField (fineSide ℓ.side d n) → CaseFunction (T.stage u).toStepSetup (fineSide ℓ.side d n))
    (A : Finset (TorusSite (fineSide ℓ.side d n * ℓ.side))) (sz : (T.stage u).labels.Ω → ℝ) (hs : Measurable sz)
    (hcm : ∀ j : ℕ, Measurable (caseLift T u _ fun V => truncateCase A sz ((j : ℝ) + 1) (Φ V)))
    (hcb : ∀ j : ℕ, ∃ K : ℝ, ∀ x, |caseLift T u _ (fun V => truncateCase A sz ((j : ℝ) + 1) (Φ V)) x| ≤ K)
    (hci : ∀ j : ℕ, ∀ᵐ x ∂(markedSampleLaw T β (u + 1) (fineSide ℓ.side d n)),
      CaseIntegrableAtSample T u _ (fun V => truncateCase A sz ((j : ℝ) + 1) (Φ V)) x)
    (hΦ : ∀ᵐ x ∂(markedSampleLaw T β (u + 1) (fineSide ℓ.side d n)), CaseIntegrableAtSample T u _ Φ x)
    (hX : Integrable (fun w => caseLift T u _ Φ (sampleBelow ℓ (u + 1) d n w)) (markedSampleLaw T β (u + 1 + d) n)) :
    (markedSampleLaw T β (u + 1 + d) n)[fun w => caseLift T u _ Φ (sampleBelow ℓ (u + 1) d n w) | upperSigma T (u + 1) d n]
      =ᵐ[markedSampleLaw T β (u + 1 + d) n] fun w => caseMeanAtSample T u _ Φ (sampleBelow ℓ (u + 1) d n w) := by
  classical
  haveI := h.prob
  haveI := h.prob'
  obtain ⟨ν, hν⟩ : ∃ ν, ν = markedSampleLaw T β (u + 1 + d) n := ⟨_, rfl⟩
  rw [← hν] at hX ⊢
  haveI : IsProbabilityMeasure ν := hν ▸ h.prob
  have hbm : Measurable (sampleBelow ℓ (u + 1) d n) := h.below.measurable
  obtain ⟨f, hf⟩ : ∃ f : ℕ → MarkedSample ℓ (u + 1 + d) n → ℝ, f = fun (j : ℕ) w =>
      caseLift T u _ (fun V => truncateCase A sz ((j : ℝ) + 1) (Φ V)) (sampleBelow ℓ (u + 1) d n w) := ⟨_, rfl⟩
  obtain ⟨X, hXd⟩ : ∃ X : MarkedSample ℓ (u + 1 + d) n → ℝ, X = fun w => caseLift T u _ Φ (sampleBelow ℓ (u + 1) d n w) :=
    ⟨_, rfl⟩
  rw [← hXd] at hX ⊢
  have hfi : ∀ j, Integrable (f j) ν := fun j => by
    obtain ⟨K, hK⟩ := hcb j
    rw [hf]
    exact Integrable.of_bound ((hcm j).comp hbm).aestronglyMeasurable K (ae_of_all _ fun w => by simpa using hK _)
  have hg : ∀ j, ν[f j | upperSigma T (u + 1) d n] =ᵐ[ν]
      fun w => caseMeanAtSample T u _ (fun V => truncateCase A sz ((j : ℝ) + 1) (Φ V)) (sampleBelow ℓ (u + 1) d n w) := fun j => by
    obtain ⟨K, hK⟩ := hcb j
    rw [hf, hν]
    exact condExp_upper_eq_caseMean h _ (hcm j) hK (hci j)
  have hall := ae_all_iff.mpr hg
  have hlim : ∀ᵐ w ∂ν, Tendsto (fun j : ℕ => caseMeanAtSample T u _ (fun V => truncateCase A sz ((j : ℝ) + 1) (Φ V))
      (sampleBelow ℓ (u + 1) d n w)) atTop (𝓝 (caseMeanAtSample T u _ Φ (sampleBelow ℓ (u + 1) d n w))) := by
    have := h.below.quasiMeasurePreserving.ae hΦ
    rw [← hν] at this
    exact this.mono fun w hw => tendsto_caseMean_truncate hs hw
  obtain ⟨a, ha⟩ : ∃ a : ℕ → MarkedSample ℓ (u + 1 + d) n → ℝ, a = fun (j : ℕ) w =>
      |(ν[f j | upperSigma T (u + 1) d n]) w - (ν[X | upperSigma T (u + 1) d n]) w| := ⟨_, rfl⟩
  have ham : ∀ j, Measurable (a j) := fun j => by
    rw [ha]
    exact ((stronglyMeasurable_condExp.mono h.upper).measurable.sub (stronglyMeasurable_condExp.mono h.upper).measurable).abs
  have hai : ∀ j, Integrable (a j) ν := fun j => by
    rw [ha]
    exact (integrable_condExp.sub integrable_condExp).abs
  have hale : ∀ j, ∫ w, a j w ∂ν ≤ ∫ w, |f j w - X w| ∂ν := fun j => by
    have e : (fun w => a j w) =ᵐ[ν] fun w => |(ν[fun z => f j z - X z | upperSigma T (u + 1) d n]) w| := by
      have := condExp_sub (hfi j) hX (upperSigma T (u + 1) d n)
      filter_upwards [this] with w hw
      rw [ha]
      show _ = |(ν[f j - X | upperSigma T (u + 1) d n]) w|
      rw [hw]
      rfl
    rw [integral_congr_ae e]
    exact integral_abs_condExp_le _
  have hfX : ∀ j w, |f j w - X w| ≤ |X w| := fun j w => by
    rw [hf, hXd]
    simp only
    rw [caseLift_truncate]
    split_ifs
    · simp
    · simp
  have hzero : Tendsto (fun j => ∫ w, |f j w - X w| ∂ν) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := ν) (F := fun j w => |f j w - X w|) (f := fun _ => (0 : ℝ))
      (fun w => |X w|) (fun j => ((hfi j).sub hX).abs.1) hX.abs
      (fun j => Filter.Eventually.of_forall fun w => by simpa using hfX j w) (Filter.Eventually.of_forall fun w => by
        refine tendsto_const_nhds.congr' ?_
        obtain ⟨j₀, hj₀⟩ := exists_nat_ge (supportWeightOfSample T u _ A sz (sampleBelow ℓ (u + 1) d n w))
        filter_upwards [eventually_ge_atTop j₀] with j hj
        have hjr : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
        rw [hf, hXd]
        simp only
        rw [caseLift_truncate, if_pos (by linarith)]
        simp)
    simpa using this
  have hazero : Tendsto (fun j => ∫ w, a j w ∂ν) atTop (𝓝 0) :=
    squeeze_zero (fun j => integral_nonneg fun w => by rw [ha]; exact abs_nonneg _) hale hzero
  have hlz : Tendsto (fun j => ∫⁻ w, ENNReal.ofReal (a j w) ∂ν) atTop (𝓝 0) := by
    have e : ∀ j, ∫⁻ w, ENNReal.ofReal (a j w) ∂ν = ENNReal.ofReal (∫ w, a j w ∂ν) := fun j =>
      (ofReal_integral_eq_lintegral_ofReal (hai j) (ae_of_all _ fun w => by rw [ha]; exact abs_nonneg _)).symm
    simp_rw [e]
    simpa using ENNReal.tendsto_ofReal hazero
  have hF : ∫⁻ w, liminf (fun j => ENNReal.ofReal (a j w)) atTop ∂ν ≤ liminf (fun j => ∫⁻ w, ENNReal.ofReal (a j w) ∂ν) atTop :=
    lintegral_liminf_le fun j => (ham j).ennreal_ofReal
  have hmeas : Measurable fun w => liminf (fun j => ENNReal.ofReal (a j w)) atTop :=
    Measurable.liminf fun j => (ham j).ennreal_ofReal
  rw [hlz.liminf_eq, nonpos_iff_eq_zero] at hF
  have hz := (lintegral_eq_zero_iff hmeas).mp hF
  filter_upwards [hall, hlim, hz] with w h1 h2 h3
  have h4 : Tendsto (fun j => a j w) atTop
      (𝓝 |caseMeanAtSample T u _ Φ (sampleBelow ℓ (u + 1) d n w) - (ν[X | upperSigma T (u + 1) d n]) w|) := by
    have : (fun j => a j w) = fun (j : ℕ) => |caseMeanAtSample T u _ (fun V => truncateCase A sz ((j : ℝ) + 1) (Φ V))
        (sampleBelow ℓ (u + 1) d n w) - (ν[X | upperSigma T (u + 1) d n]) w| := by
      funext j
      rw [ha]
      simp only
      rw [h1 j]
    rw [this]
    exact (h2.sub tendsto_const_nhds).abs
  have h5 := (ENNReal.tendsto_ofReal h4).liminf_eq
  have h6 : ENNReal.ofReal |caseMeanAtSample T u _ Φ (sampleBelow ℓ (u + 1) d n w) - (ν[X | upperSigma T (u + 1) d n]) w| = 0 := by
    rw [← h5]
    simpa using h3
  have h7 := ENNReal.ofReal_eq_zero.mp h6
  have h8 : |caseMeanAtSample T u _ Φ (sampleBelow ℓ (u + 1) d n w) - (ν[X | upperSigma T (u + 1) d n]) w| = 0 :=
    le_antisymm h7 (abs_nonneg _)
  exact (sub_eq_zero.mp (abs_eq_zero.mp h8)).symm
private theorem torus_covariance_bound (hC : conditionalCopyCovarianceStatement) (h : TorusData T β u d n)
    {τ τ' : MarkedSample ℓ (u + 1 + d) n → MarkedSample ℓ (u + 1 + d) n}
    (hτ : MeasurePreserving τ (markedSampleLaw T β (u + 1 + d) n) (markedSampleLaw T β (u + 1 + d) n))
    (hτ' : MeasurePreserving τ' (markedSampleLaw T β (u + 1 + d) n) (markedSampleLaw T β (u + 1 + d) n))
    (hl : ∀ x, τ' (τ x) = x) (hr : ∀ x, τ (τ' x) = x)
    (hG : @Measurable _ _ (upperSigma T (u + 1) d n) (upperSigma T (u + 1) d n) τ)
    (hG' : @Measurable _ _ (upperSigma T (u + 1) d n) (upperSigma T (u + 1) d n) τ')
    {Ψ Ψk : TorusField (fineSide ℓ.side d n) → CaseFunction (T.stage u).toStepSetup (fineSide ℓ.side d n)}
    (hm : Measurable (caseLift T u _ Ψ)) (hkm : Measurable (caseLift T u _ Ψk)) {K : ℝ} (hb : ∀ x, |caseLift T u _ Ψ x| ≤ K)
    (hkb : ∀ x, |caseLift T u _ Ψk x| ≤ K)
    (hi : ∀ᵐ x ∂(markedSampleLaw T β (u + 1) (fineSide ℓ.side d n)), CaseIntegrableAtSample T u _ Ψ x)
    (hki : ∀ᵐ x ∂(markedSampleLaw T β (u + 1) (fineSide ℓ.side d n)), CaseIntegrableAtSample T u _ Ψk x)
    (hpi : ∀ᵐ x ∂(markedSampleLaw T β (u + 1) (fineSide ℓ.side d n)),
      CaseIntegrableAtSample T u _ (fun V W Yt ωt bad b => Ψ V W Yt ωt bad b * Ψk V W Yt ωt bad b) x)
    (hlift : ∀ w, caseLift T u _ Ψ (sampleBelow ℓ (u + 1) d n (τ w)) = caseLift T u _ Ψk (sampleBelow ℓ (u + 1) d n w)) {δ : ℝ}
    (hcov : ∀ᵐ x ∂(markedSampleLaw T β (u + 1) (fineSide ℓ.side d n)),
      |caseMeanAtSample T u _ (fun V W Yt ωt bad b => Ψ V W Yt ωt bad b * Ψk V W Yt ωt bad b) x -
        caseMeanAtSample T u _ Ψ x * caseMeanAtSample T u _ Ψk x| ≤ δ)
    {R : MarkedSample ℓ (u + 1 + d) n → ℝ} (hR : @Measurable _ _ (upperSigma T (u + 1) d n) _ R) {C : ℝ} (hRb : ∀ w, |R w| ≤ C)
    {X E : MarkedSample ℓ (u + 1 + d) n → ℝ}
    (hXE : (markedSampleLaw T β (u + 1 + d) n)[X | upperSigma T (u + 1) d n] =ᵐ[markedSampleLaw T β (u + 1 + d) n] E)
    (hX2 : MemLp X 2 (markedSampleLaw T β (u + 1 + d) n)) {A e : ℝ} (hA : 0 ≤ A) (he : 0 ≤ e)
    (hXA : ∫ w, X w ^ 2 ∂(markedSampleLaw T β (u + 1 + d) n) ≤ A ^ 2)
    (hbA : ∫ w, caseLift T u _ Ψ (sampleBelow ℓ (u + 1) d n w) ^ 2 ∂(markedSampleLaw T β (u + 1 + d) n) ≤ A ^ 2)
    (hXe : ∫ w, (X w - caseLift T u _ Ψ (sampleBelow ℓ (u + 1) d n w)) ^ 2 ∂(markedSampleLaw T β (u + 1 + d) n) ≤ e ^ 2) :
    |∫ w, (R w * (X w - E w)) * (R (τ w) * (X (τ w) - E (τ w))) ∂(markedSampleLaw T β (u + 1 + d) n)| ≤
      C ^ 2 * (δ + 8 * A * e) := by
  haveI := h.prob
  haveI := h.prob'
  have hπ : Measurable (sampleBelow ℓ (u + 1) d n) := h.below.measurable
  have hXbm : Measurable fun w => caseLift T u _ Ψ (sampleBelow ℓ (u + 1) d n w) := hm.comp hπ
  have hpm : Measurable (caseLift T u _ fun V W Yt ωt bad b => Ψ V W Yt ωt bad b * Ψk V W Yt ωt bad b) := hm.mul hkm
  have hpb : ∀ x, |caseLift T u _ (fun V W Yt ωt bad b => Ψ V W Yt ωt bad b * Ψk V W Yt ωt bad b) x| ≤ K * K := fun x => by
    show |caseLift T u _ Ψ x * caseLift T u _ Ψk x| ≤ _
    rw [abs_mul]
    exact mul_le_mul (hb x) (hkb x) (abs_nonneg _) ((abs_nonneg _).trans (hb x))
  have e1 := condExp_upper_eq_caseMean h _ hpm hpb hpi
  have e2 := condExp_upper_eq_caseMean h Ψ hm hb hi
  have e3 := condExp_upper_eq_caseMean h Ψk hkm hkb hki
  have hc := h.below.quasiMeasurePreserving.ae hcov
  have hcov' : ∀ᵐ x ∂(markedSampleLaw T β (u + 1 + d) n),
      |((markedSampleLaw T β (u + 1 + d) n)[fun z => caseLift T u _ Ψ (sampleBelow ℓ (u + 1) d n z) *
            caseLift T u _ Ψ (sampleBelow ℓ (u + 1) d n (τ z)) | upperSigma T (u + 1) d n]) x -
        ((markedSampleLaw T β (u + 1 + d) n)[fun z => caseLift T u _ Ψ (sampleBelow ℓ (u + 1) d n z) | upperSigma T (u + 1) d n]) x *
        ((markedSampleLaw T β (u + 1 + d) n)[(fun z => caseLift T u _ Ψ (sampleBelow ℓ (u + 1) d n z)) ∘ τ |
          upperSigma T (u + 1) d n]) x| ≤ δ := by
    have f1 : (fun z => caseLift T u _ Ψ (sampleBelow ℓ (u + 1) d n z) * caseLift T u _ Ψ (sampleBelow ℓ (u + 1) d n (τ z))) =
        fun z => caseLift T u _ (fun V W Yt ωt bad b => Ψ V W Yt ωt bad b * Ψk V W Yt ωt bad b) (sampleBelow ℓ (u + 1) d n z) := by
      funext z
      rw [hlift z]
      rfl
    have f3 : (fun z => caseLift T u _ Ψ (sampleBelow ℓ (u + 1) d n z)) ∘ τ =
        fun z => caseLift T u _ Ψk (sampleBelow ℓ (u + 1) d n z) := by
      funext z
      exact hlift z
    rw [f1, f3]
    filter_upwards [e1, e2, e3, hc] with x a1 a2 a3 a4
    rw [a1, a2, a3]
    exact a4
  have key := hC _ (markedSampleLaw T β (u + 1 + d) n) (upperSigma T (u + 1) d n) τ τ' h.upper hτ hτ' hl hr hG hG' R (R ∘ τ) X
    (fun w => caseLift T u _ Ψ (sampleBelow ℓ (u + 1) d n w)) C δ A e hR.stronglyMeasurable (hR.comp hG).stronglyMeasurable hRb
    (fun x => hRb _) hX2 (MemLp.of_bound hXbm.aestronglyMeasurable K (ae_of_all _ fun w => by simpa using hb _)) hXbm
    ⟨K, fun x => hb _⟩ hA he hXA hbA hXe hcov'
  have hEτ := hτ.quasiMeasurePreserving.ae_eq_comp hXE
  have hcongr : (fun w => (R w * (X w - E w)) * (R (τ w) * (X (τ w) - E (τ w)))) =ᵐ[markedSampleLaw T β (u + 1 + d) n]
      fun w => R w * (R ∘ τ) w * ((X w - ((markedSampleLaw T β (u + 1 + d) n)[X | upperSigma T (u + 1) d n]) w) *
        (X (τ w) - ((markedSampleLaw T β (u + 1 + d) n)[X | upperSigma T (u + 1) d n]) (τ w))) := by
    filter_upwards [hXE, hEτ] with w a1 a2
    have a2' : ((markedSampleLaw T β (u + 1 + d) n)[X | upperSigma T (u + 1) d n]) (τ w) = E (τ w) := a2
    rw [a1, a2']
    simp only [Function.comp]
    ring
  rw [integral_congr_ae hcongr]
  exact key
end Torus
section Iterates
variable {ℓ : StepParameters} {T : StageTower ℓ} {β : ℝ} {u d n : ℕ} [NeZero n]
private theorem caseLift_iterate {N : ℕ} [NeZero N] {v : Fin 4 → ℤ}
    (hst : ∀ x : MarkedSample ℓ u (N * ℓ.side),
      stageState T u (N * ℓ.side) (translateSample u (N * ℓ.side) (fun i => (ℓ.side : ℤ) * v i) x) =
      translateStageState T u (N * ℓ.side) (fun i => (ℓ.side : ℤ) * v i) (stageState T u (N * ℓ.side) x)) (k : ℕ) :
    ∀ (Ψ : TorusField N → CaseFunction (T.stage u).toStepSetup N) (x : MarkedSample ℓ (u + 1) N),
      caseLift T u N Ψ ((translateSample (u + 1) N v)^[k] x) = caseLift T u N ((translateFamily T u N v)^[k] Ψ) x := by
  induction k with
  | zero => intro Ψ x; rfl
  | succ k ih =>
    intro Ψ x
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply, caseLift_translateSample T u N v Ψ _ (hst _)]
    exact ih _ x
private theorem nearlyLocal_iterate {N : ℕ} [NeZero N] {v : Fin 4 → ℤ} {a : TorusSite (N * ℓ.side)} {Rr : ℕ} {Sz : ℝ}
    (hmv : ∀ (o : TorusSite (N * ℓ.side)) (F : CaseFunction (T.stage u).toStepSetup N),
      IsNearlyLocalCaseFunction (T.stage u).toStepSetup o Rr Sz F →
      IsNearlyLocalCaseFunction (T.stage u).toStepSetup (o + a) Rr Sz (translateCaseFunction v F))
    {o : TorusSite (N * ℓ.side)} {Ψ : TorusField N → CaseFunction (T.stage u).toStepSetup N}
    (hΨ : ∀ V, IsNearlyLocalCaseFunction (T.stage u).toStepSetup o Rr Sz (Ψ V)) (k : ℕ) :
    ∀ V, IsNearlyLocalCaseFunction (T.stage u).toStepSetup (o + k • a) Rr Sz (((translateFamily T u N v)^[k] Ψ) V) := by
  induction k with
  | zero =>
    intro V
    simpa using hΨ V
  | succ k ih =>
    intro V
    rw [Function.iterate_succ_apply', succ_nsmul, ← add_assoc]
    exact hmv _ _ (ih _)
private theorem iterate_covariance_bound (hC : conditionalCopyCovarianceStatement) (hf : TorusData T β u d n)
    {m m' : MarkedSample ℓ (u + 1 + d) n → MarkedSample ℓ (u + 1 + d) n}
    (hm : MeasurePreserving m (markedSampleLaw T β (u + 1 + d) n) (markedSampleLaw T β (u + 1 + d) n))
    (hm' : MeasurePreserving m' (markedSampleLaw T β (u + 1 + d) n) (markedSampleLaw T β (u + 1 + d) n))
    (hl : ∀ x, m' (m x) = x) (hr : ∀ x, m (m' x) = x)
    (hG : @Measurable _ _ (upperSigma T (u + 1) d n) (upperSigma T (u + 1) d n) m)
    (hG' : @Measurable _ _ (upperSigma T (u + 1) d n) (upperSigma T (u + 1) d n) m')
    {v : Fin 4 → ℤ}
    (hsemi : ∀ w, sampleBelow ℓ (u + 1) d n (m w) = translateSample (u + 1) (fineSide ℓ.side d n) v (sampleBelow ℓ (u + 1) d n w))
    (hm₁ : Measurable (translateSample (ℓ := ℓ) (u + 1) (fineSide ℓ.side d n) v))
    (hst : ∀ x : MarkedSample ℓ u (fineSide ℓ.side d n * ℓ.side),
      stageState T u (fineSide ℓ.side d n * ℓ.side) (translateSample u (fineSide ℓ.side d n * ℓ.side) (fun i => (ℓ.side : ℤ) * v i) x) =
        translateStageState T u (fineSide ℓ.side d n * ℓ.side) (fun i => (ℓ.side : ℤ) * v i)
          (stageState T u (fineSide ℓ.side d n * ℓ.side) x))
    {a o : TorusSite (fineSide ℓ.side d n * ℓ.side)} {Rr : ℕ} {Sz : ℝ} (hSz : 0 ≤ Sz)
    (hmv : ∀ (o : TorusSite (fineSide ℓ.side d n * ℓ.side)) (F : CaseFunction (T.stage u).toStepSetup (fineSide ℓ.side d n)),
      IsNearlyLocalCaseFunction (T.stage u).toStepSetup o Rr Sz F →
      IsNearlyLocalCaseFunction (T.stage u).toStepSetup (o + a) Rr Sz (translateCaseFunction v F))
    {Ψ : TorusField (fineSide ℓ.side d n) → CaseFunction (T.stage u).toStepSetup (fineSide ℓ.side d n)}
    (hΨ : ∀ V, IsNearlyLocalCaseFunction (T.stage u).toStepSetup o Rr Sz (Ψ V)) (hΨm : Measurable (caseLift T u _ Ψ))
    (hpos : ∀ᵐ x ∂(markedSampleLaw T β (u + 1) (fineSide ℓ.side d n)),
      0 < coarseStateWeight (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup x.2.2.1) x.2.2.1
        (stageState T (u + 1) _ x).2)
    (k : ℕ) {δ : ℝ}
    (hfar : ∀ (V : TorusField (fineSide ℓ.side d n)) (q : CoarseState (T.stage u).toStepSetup (fineSide ℓ.side d n)),
      0 < coarseStateWeight (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup V) V q →
      ∀ F G : CaseFunction (T.stage u).toStepSetup (fineSide ℓ.side d n),
        IsNearlyLocalCaseFunction (T.stage u).toStepSetup o Rr Sz F →
        IsNearlyLocalCaseFunction (T.stage u).toStepSetup (o + k • a) Rr Sz G →
        |caseMean (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup V) V q
            (fun W Yt ωt bad b => F W Yt ωt bad b * G W Yt ωt bad b) -
          caseMean (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup V) V q F *
            caseMean (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup V) V q G| ≤ δ)
    {R : MarkedSample ℓ (u + 1 + d) n → ℝ} (hR : @Measurable _ _ (upperSigma T (u + 1) d n) _ R) {C : ℝ} (hRb : ∀ w, |R w| ≤ C)
    {X E : MarkedSample ℓ (u + 1 + d) n → ℝ}
    (hXE : (markedSampleLaw T β (u + 1 + d) n)[X | upperSigma T (u + 1) d n] =ᵐ[markedSampleLaw T β (u + 1 + d) n] E)
    (hX2 : MemLp X 2 (markedSampleLaw T β (u + 1 + d) n)) {A e : ℝ} (hA : 0 ≤ A) (he : 0 ≤ e)
    (hXA : ∫ w, X w ^ 2 ∂(markedSampleLaw T β (u + 1 + d) n) ≤ A ^ 2)
    (hbA : ∫ w, caseLift T u _ Ψ (sampleBelow ℓ (u + 1) d n w) ^ 2 ∂(markedSampleLaw T β (u + 1 + d) n) ≤ A ^ 2)
    (hXe : ∫ w, (X w - caseLift T u _ Ψ (sampleBelow ℓ (u + 1) d n w)) ^ 2 ∂(markedSampleLaw T β (u + 1 + d) n) ≤ e ^ 2) :
    |∫ w, (R w * (X w - E w)) * (R (m^[k] w) * (X (m^[k] w) - E (m^[k] w))) ∂(markedSampleLaw T β (u + 1 + d) n)| ≤
      C ^ 2 * (δ + 8 * A * e) := by
  haveI := hf.prob
  haveI := hf.prob'
  have hk := nearlyLocal_iterate hmv hΨ k
  have hliftk := fun x => caseLift_iterate (T := T) (u := u) hst k Ψ x
  obtain ⟨Ψk, hΨk⟩ : ∃ Ψk, Ψk = (translateFamily T u _ v)^[k] Ψ := ⟨_, rfl⟩
  rw [← hΨk] at hk hliftk
  have hkm : Measurable (caseLift T u _ Ψk) := by
    have e : caseLift T u _ Ψk = caseLift T u _ Ψ ∘ (translateSample (u + 1) (fineSide ℓ.side d n) v)^[k] :=
      funext fun x => (hliftk x).symm
    rw [e]
    exact hΨm.comp (hm₁.iterate k)
  have hb : ∀ x, |caseLift T u _ Ψ x| ≤ Sz := fun x => (hΨ _).abs_le _ _ _ _ _
  have hkb : ∀ x, |caseLift T u _ Ψk x| ≤ Sz := fun x => (hk _).abs_le _ _ _ _ _
  have hi : ∀ᵐ x ∂(markedSampleLaw T β (u + 1) (fineSide ℓ.side d n)), CaseIntegrableAtSample T u _ Ψ x :=
    hf.one.mono fun x hx => caseIntegrable_of_bounded _ _ _ hx (hΨ _).measurable hSz (hΨ _).abs_le
  have hki : ∀ᵐ x ∂(markedSampleLaw T β (u + 1) (fineSide ℓ.side d n)), CaseIntegrableAtSample T u _ Ψk x :=
    hf.one.mono fun x hx => caseIntegrable_of_bounded _ _ _ hx (hk _).measurable hSz (hk _).abs_le
  have hpi : ∀ᵐ x ∂(markedSampleLaw T β (u + 1) (fineSide ℓ.side d n)),
      CaseIntegrableAtSample T u _ (fun V W Yt ωt bad b => Ψ V W Yt ωt bad b * Ψk V W Yt ωt bad b) x :=
    hf.one.mono fun x hx => caseIntegrable_of_bounded _ _ _ hx
      (fun Yt bad b => ((hΨ _).measurable Yt bad b).mul ((hk _).measurable Yt bad b))
      (mul_nonneg hSz hSz) fun W Yt ωt bad b => by
        rw [abs_mul]
        exact mul_le_mul ((hΨ _).abs_le _ _ _ _ _) ((hk _).abs_le _ _ _ _ _) (abs_nonneg _) hSz
  have hsk : ∀ w, sampleBelow ℓ (u + 1) d n (m^[k] w) =
      (translateSample (u + 1) (fineSide ℓ.side d n) v)^[k] (sampleBelow ℓ (u + 1) d n w) :=
    fun w => (Function.Semiconj.iterate_right (f := sampleBelow ℓ (u + 1) d n) (ga := m)
      (gb := translateSample (u + 1) (fineSide ℓ.side d n) v) hsemi k) w
  refine torus_covariance_bound hC hf (hm.iterate k) (hm'.iterate k) (Function.LeftInverse.iterate hl k)
    (Function.RightInverse.iterate hr k)
    (@Measurable.iterate _ (upperSigma T (u + 1) d n) _ hG k) (@Measurable.iterate _ (upperSigma T (u + 1) d n) _ hG' k)
    hΨm hkm hb hkb hi hki hpi (fun w => by rw [hsk, hliftk]) ?_ hR hRb hXE hX2 hA he hXA hbA hXe
  exact hpos.mono fun x hx => hfar _ _ hx _ _ (hΨ _) (hk _)
end Iterates
section TranslationFacts
private def ChainTranslationFacts (Tb : ParameterAssignment) (y : ℝ) : Prop :=
  ∀ (g β : ℝ) (K m : ℕ) (T : StageTower (Tb.stepParameters y)) (t d n : ℕ) [NeZero n],
    HullChainAtLevel Tb y g β K m T (t + d) n → ∀ w : Fin 4 → ℤ,
      (∀ rule : NoiseRule (Tb.stepParameters y), rule.IsAdmissible T →
        ∀ p : TorusField (fineSide (Tb.stepParameters y).side (t + d) n) × ChainNoise.ChainNoise (Tb.stepParameters y) (t + d) n,
          rule.chain T (t + d) n
              (pairTranslate (Tb.stepParameters y) (t + d) n (fun i => ((Tb.stepParameters y).side : ℤ) * w i) p).1
              (pairTranslate (Tb.stepParameters y) (t + d) n (fun i => ((Tb.stepParameters y).side : ℤ) * w i) p).2 =
            translateSample (t + d) n (fun i => ((Tb.stepParameters y).side : ℤ) * w i) (rule.chain T (t + d) n p.1 p.2)) ∧
      (∀ x : MarkedSample (Tb.stepParameters y) (t + d) n,
        stageState T (t + d) n (translateSample (t + d) n (fun i => ((Tb.stepParameters y).side : ℤ) * w i) x) =
          translateStageState T (t + d) n (fun i => ((Tb.stepParameters y).side : ℤ) * w i) (stageState T (t + d) n x)) ∧
      (∀ x : MarkedSample (Tb.stepParameters y) (t + d) n,
        translateSample (t + d) n (fun i => ((Tb.stepParameters y).side : ℤ) * -w i)
          (translateSample (t + d) n (fun i => ((Tb.stepParameters y).side : ℤ) * w i) x) = x) ∧
      Measurable (translateSample (ℓ := Tb.stepParameters y) (t + d) n fun i => ((Tb.stepParameters y).side : ℤ) * w i) ∧
      @Measurable _ _ (upperSigma T t d n) (upperSigma T t d n)
        (translateSample (t + d) n fun i => ((Tb.stepParameters y).side : ℤ) * w i)
private def NearlyLocalTranslationFacts (Tb : ParameterAssignment) (y : ℝ) : Prop :=
  ∀ (g β : ℝ) (K m : ℕ) (T : StageTower (Tb.stepParameters y)) (u n : ℕ) [NeZero n],
    HullChainAtLevel Tb y g β K m T (u + 1) n → ∀ (w : Fin 4 → ℤ) (o : TorusSite (n * (Tb.stepParameters y).side)) (Rr : ℕ) (Sz : ℝ)
      (F : CaseFunction (T.stage u).toStepSetup n), IsNearlyLocalCaseFunction (T.stage u).toStepSetup o Rr Sz F →
      IsNearlyLocalCaseFunction (T.stage u).toStepSetup
        (o + siteOfInt fun i => ((Tb.stepParameters y).side : ℤ) * (((Tb.stepParameters y).side : ℤ) * w i)) Rr Sz
        (translateCaseFunction (fun i => ((Tb.stepParameters y).side : ℤ) * w i) F)
private theorem measurable_sigma_of_forall {A : Type} {γ : A → Type} [∀ a, MeasurableSpace (γ a)] {f : Sigma γ → ℝ}
    (h : ∀ a, Measurable fun b => f ⟨a, b⟩) : Measurable f := by
  intro s hs
  refine MeasurableSpace.measurableSet_iInf.2 fun a => ?_
  exact h a hs
variable {ℓ : StepParameters}
private theorem measurable_supportWeight {T : StageTower ℓ} {u N : ℕ} [NeZero N] (hst : Measurable (stageState T u (N * ℓ.side)))
    (A : Finset (TorusSite (N * ℓ.side))) {sz : (T.stage u).labels.Ω → ℝ} (hs : Measurable sz) :
    Measurable (supportWeightOfSample T u N A sz) := by
  have h1 : Measurable fun q : StageState T u (N * ℓ.side) => 1 + ∑ y ∈ A, siteScore sz q.2.1 q.2.2 y := by
    have h2 : Measurable fun z : (Σ Y : Finset (TorusSite (N * ℓ.side)), (Y → (T.stage u).labels.Ω)) =>
        1 + ∑ y ∈ A, siteScore sz z.1 z.2 y :=
      measurable_sigma_of_forall fun Y => measurable_supportSize (R := (T.stage u).toStepSetup) (A := A) hs Y
    exact h2.comp measurable_snd
  exact h1.comp (hst.comp measurable_fst)
end TranslationFacts
section NoisePairs
variable {Tb : ParameterAssignment} {y g β : ℝ} {K mm : ℕ} {T : StageTower (Tb.stepParameters y)} {u d n : ℕ} [NeZero n]
private theorem noise_covariance_bound (h : u + 1 + d = K) (hC : conditionalCopyCovarianceStatement)
    (hCh : ChainTranslationFacts Tb y) (hNr : NearlyLocalTranslationFacts Tb y)
    (hK : HullChainAtLevel Tb y g β K mm T K n) (hK1 : HullChainAtLevel Tb y g β K mm T (u + 1) (fineSide (Tb.stepParameters y).side d n))
    (hK0 : HullChainAtLevel Tb y g β K mm T u (fineSide (Tb.stepParameters y).side d n * (Tb.stepParameters y).side))
    (hf : TorusData T β u d n) {rule : NoiseRule (Tb.stepParameters y)} (hrule : rule.IsAdmissible T) (w : Fin 4 → ℤ)
    (hmap : ((wilsonLaw β (fineSide (Tb.stepParameters y).side K n)).prod (chainNoiseLaw (Tb.stepParameters y) K n)).map
      (fun p => rule.chain T K n p.1 p.2) = markedSampleLaw T β K n)
    (hDm : Measurable fun p : TorusField (fineSide (Tb.stepParameters y).side K n) × ChainNoise.ChainNoise (Tb.stepParameters y) K n =>
      rule.chain T K n p.1 p.2)
    (hτ : MeasurePreserving (pairTranslate (Tb.stepParameters y) K n fun i => ((Tb.stepParameters y).side : ℤ) * w i)
      ((wilsonLaw β (fineSide (Tb.stepParameters y).side K n)).prod (chainNoiseLaw (Tb.stepParameters y) K n))
      ((wilsonLaw β (fineSide (Tb.stepParameters y).side K n)).prod (chainNoiseLaw (Tb.stepParameters y) K n)))
    (hst : Measurable (stageState T u (fineSide (Tb.stepParameters y).side d n * (Tb.stepParameters y).side)))
    (hpos : ∀ᵐ x ∂(markedSampleLaw T β (u + 1) (fineSide (Tb.stepParameters y).side d n)),
      0 < coarseStateWeight (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup x.2.2.1) x.2.2.1
        (stageState T (u + 1) _ x).2)
    {Φ : TorusField (fineSide (Tb.stepParameters y).side d n) →
      CaseFunction (T.stage u).toStepSetup (fineSide (Tb.stepParameters y).side d n)}
    {A : Finset (TorusSite (fineSide (Tb.stepParameters y).side d n * (Tb.stepParameters y).side))}
    {o : TorusSite (fineSide (Tb.stepParameters y).side d n * (Tb.stepParameters y).side)}
    {sz : (T.stage u).labels.Ω → ℝ} {Rr a : ℕ} {Sz : ℝ}
    (hcl : ∀ V, IsQuasiLocalCaseFunction (T.stage u).toStepSetup o Rr a Sz A sz (Φ V)) (hSz : 0 ≤ Sz)
    (hLm : Measurable (caseLift T u _ Φ))
    (hCI : ∀ᵐ x ∂(markedSampleLaw T β (u + 1) (fineSide (Tb.stepParameters y).side d n)), CaseIntegrableAtSample T u _ Φ x)
    {C₁ C₂ C₄ C : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₄ : 0 ≤ C₄)
    (hN : ∫⁻ x, ENNReal.ofReal (supportWeightOfSample T u _ A sz x)
      ∂(markedSampleLaw T β (u + 1) (fineSide (Tb.stepParameters y).side d n)) ≤ ENNReal.ofReal C₁)
    {gR gX gE : MarkedSample (Tb.stepParameters y) K n → ℝ}
    (hgX : ∀ z, gX z = caseLift T u _ Φ (sampleBelow (Tb.stepParameters y) (u + 1) d n (h.symm ▸ z)))
    (hgE : ∀ z, gE z = caseMeanAtSample T u _ Φ (sampleBelow (Tb.stepParameters y) (u + 1) d n (h.symm ▸ z)))
    (hRr : @Measurable _ _ (upperSigma T (u + 1) d n) _ fun z : MarkedSample (Tb.stepParameters y) (u + 1 + d) n => gR (h ▸ z))
    (hRb : ∀ z, |gR z| ≤ C)
    (hX2 : ∫⁻ p, ENNReal.ofReal (|gX (rule.chain T K n p.1 p.2)| ^ 2)
      ∂((wilsonLaw β (fineSide (Tb.stepParameters y).side K n)).prod (chainNoiseLaw (Tb.stepParameters y) K n)) ≤ ENNReal.ofReal C₂)
    (hX4 : ∫⁻ p, ENNReal.ofReal (|gX (rule.chain T K n p.1 p.2)| ^ 4)
      ∂((wilsonLaw β (fineSide (Tb.stepParameters y).side K n)).prod (chainNoiseLaw (Tb.stepParameters y) K n)) ≤ ENNReal.ofReal C₄)
    {B t e : ℝ} (hB : 1 ≤ B) (ht : 0 < t) (he : 0 ≤ e) (hee : C₄ / (2 * t) + t / 2 * (C₁ / B) ≤ e ^ 2) (k : ℕ) {δ : ℝ}
    (hfar : ∀ (V : TorusField (fineSide (Tb.stepParameters y).side d n))
      (q : CoarseState (T.stage u).toStepSetup (fineSide (Tb.stepParameters y).side d n)),
      0 < coarseStateWeight (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup V) V q →
      ∀ F G : CaseFunction (T.stage u).toStepSetup (fineSide (Tb.stepParameters y).side d n),
        IsNearlyLocalCaseFunction (T.stage u).toStepSetup o Rr (Sz * B ^ a) F →
        IsNearlyLocalCaseFunction (T.stage u).toStepSetup
          (o + k • siteOfInt fun i => ((Tb.stepParameters y).side : ℤ) *
            (((Tb.stepParameters y).side : ℤ) * ((Tb.stepParameters y).side ^ d * w i))) Rr (Sz * B ^ a) G →
        |caseMean (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup V) V q
            (fun W Yt ωt bad b => F W Yt ωt bad b * G W Yt ωt bad b) -
          caseMean (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup V) V q F *
            caseMean (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup V) V q G| ≤ δ) :
    |∫ p, (gR (rule.chain T K n p.1 p.2) * (gX (rule.chain T K n p.1 p.2) - gE (rule.chain T K n p.1 p.2))) *
        (gR (rule.chain T K n ((pairTranslate (Tb.stepParameters y) K n fun i => ((Tb.stepParameters y).side : ℤ) * w i)^[k] p).1
              ((pairTranslate (Tb.stepParameters y) K n fun i => ((Tb.stepParameters y).side : ℤ) * w i)^[k] p).2) *
          (gX (rule.chain T K n ((pairTranslate (Tb.stepParameters y) K n fun i => ((Tb.stepParameters y).side : ℤ) * w i)^[k] p).1
              ((pairTranslate (Tb.stepParameters y) K n fun i => ((Tb.stepParameters y).side : ℤ) * w i)^[k] p).2) -
            gE (rule.chain T K n ((pairTranslate (Tb.stepParameters y) K n fun i => ((Tb.stepParameters y).side : ℤ) * w i)^[k] p).1
              ((pairTranslate (Tb.stepParameters y) K n fun i => ((Tb.stepParameters y).side : ℤ) * w i)^[k] p).2)))
        ∂((wilsonLaw β (fineSide (Tb.stepParameters y).side K n)).prod (chainNoiseLaw (Tb.stepParameters y) K n))| ≤
      C ^ 2 * (δ + 8 * (1 + C₂) * e) := by
  subst h
  classical
  haveI := hf.prob
  haveI := hf.prob'
  have hπ : Measurable (sampleBelow (Tb.stepParameters y) (u + 1) d n) := hf.below.measurable
  obtain ⟨c1, -, c3, c4, c5⟩ := hCh g β _ mm T (u + 1) d n hK w
  obtain ⟨-, -, c3', c4', c5'⟩ := hCh g β _ mm T (u + 1) d n hK (-w)
  have eneg : (fun i => ((Tb.stepParameters y).side : ℤ) * -(-w) i) = fun i => ((Tb.stepParameters y).side : ℤ) * w i := by
    funext i
    simp
  rw [eneg] at c3'
  obtain ⟨m, hmd⟩ : ∃ m, m = translateSample (ℓ := Tb.stepParameters y) (u + 1 + d) n
      fun i => ((Tb.stepParameters y).side : ℤ) * w i := ⟨_, rfl⟩
  obtain ⟨m', hmd'⟩ : ∃ m', m' = translateSample (ℓ := Tb.stepParameters y) (u + 1 + d) n
      fun i => ((Tb.stepParameters y).side : ℤ) * (-w) i := ⟨_, rfl⟩
  rw [← hmd] at c4 c5
  rw [← hmd'] at c4' c5'
  have hsem : ∀ p, rule.chain T (u + 1 + d) n
      (pairTranslate (Tb.stepParameters y) (u + 1 + d) n (fun i => ((Tb.stepParameters y).side : ℤ) * w i) p).1
      (pairTranslate (Tb.stepParameters y) (u + 1 + d) n (fun i => ((Tb.stepParameters y).side : ℤ) * w i) p).2 =
      m (rule.chain T (u + 1 + d) n p.1 p.2) := by
    intro p
    rw [hmd]
    exact c1 rule hrule p
  have hl : ∀ x, m' (m x) = x := fun x => by
    rw [hmd, hmd']
    exact c3 x
  have hr : ∀ x, m (m' x) = x := fun x => by
    rw [hmd, hmd']
    exact c3' x
  have hmP : MeasurePreserving m (markedSampleLaw T β (u + 1 + d) n) (markedSampleLaw T β (u + 1 + d) n) := by
    refine ⟨c4, ?_⟩
    conv_lhs => rw [← hmap]
    rw [Measure.map_map c4 hDm]
    have e1 : m ∘ (fun p : TorusField (fineSide (Tb.stepParameters y).side (u + 1 + d) n) ×
        ChainNoise.ChainNoise (Tb.stepParameters y) (u + 1 + d) n => rule.chain T (u + 1 + d) n p.1 p.2) =
        (fun p => rule.chain T (u + 1 + d) n p.1 p.2) ∘
          (pairTranslate (Tb.stepParameters y) (u + 1 + d) n fun i => ((Tb.stepParameters y).side : ℤ) * w i) :=
      funext fun p => (hsem p).symm
    rw [e1, ← Measure.map_map hDm hτ.measurable, hτ.map_eq, hmap]
  have hmP' : MeasurePreserving m' (markedSampleLaw T β (u + 1 + d) n) (markedSampleLaw T β (u + 1 + d) n) := by
    refine ⟨c4', ?_⟩
    conv_lhs => rw [← hmP.map_eq]
    rw [Measure.map_map c4' c4]
    have e1 : m' ∘ m = id := funext hl
    rw [e1, Measure.map_id]
  obtain ⟨w', hw'⟩ : ∃ w' : Fin 4 → ℤ, w' = fun i => ((Tb.stepParameters y).side : ℤ) ^ d * w i := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin 4 → ℤ, v = fun i => ((Tb.stepParameters y).side : ℤ) * w' i := ⟨_, rfl⟩
  have hsemi : ∀ z, sampleBelow (Tb.stepParameters y) (u + 1) d n (m z) =
      translateSample (u + 1) (fineSide (Tb.stepParameters y).side d n) v (sampleBelow (Tb.stepParameters y) (u + 1) d n z) := by
    intro z
    have ev : (fun i => ((Tb.stepParameters y).side : ℤ) ^ d * (((Tb.stepParameters y).side : ℤ) * w i)) = v := by
      funext i
      rw [hv, hw']
      ring
    rw [hmd, sampleBelow_translateSample, ev]
  have hstm := fun x => (hCh g β _ mm T u 0 _ hK0 v).2.1 x
  have hm₁ : Measurable (translateSample (ℓ := Tb.stepParameters y) (u + 1) (fineSide (Tb.stepParameters y).side d n) v) := by
    have := (hCh g β _ mm T (u + 1) 0 _ hK1 w').2.2.2.1
    rw [hv]
    exact this
  have hs : Measurable sz := (hcl (trivialField _)).weight_measurable
  have hNm := measurable_supportWeight hst A hs
  have hBa : 0 ≤ Sz * B ^ a := mul_nonneg hSz (pow_nonneg (by linarith) _)
  have hlm : ∀ B' : ℝ, Measurable (caseLift T u _ fun V => truncateCase A sz B' (Φ V)) := by
    intro B'
    have e1 : caseLift T u _ (fun V => truncateCase A sz B' (Φ V)) =
        fun x => if supportWeightOfSample T u _ A sz x ≤ B' then caseLift T u _ Φ x else 0 :=
      funext fun x => by rw [caseLift_truncate]
    rw [e1]
    exact Measurable.ite (measurableSet_le hNm measurable_const) hLm measurable_const
  have hnear : ∀ (B' : ℝ), 1 ≤ B' → ∀ V,
      IsNearlyLocalCaseFunction (T.stage u).toStepSetup o Rr (Sz * B' ^ a) (truncateCase A sz B' (Φ V)) :=
    fun B' h1 V => truncateCase_nearlyLocal (hcl V) h1 hSz
  have hXeq : gX = fun z => caseLift T u _ Φ (sampleBelow (Tb.stepParameters y) (u + 1) d n z) := funext hgX
  have hEeq : gE = fun z => caseMeanAtSample T u _ Φ (sampleBelow (Tb.stepParameters y) (u + 1) d n z) := funext hgE
  have hXm : Measurable gX := by
    rw [hXeq]
    exact hLm.comp hπ
  have lint : ∀ q : ℕ, ∫⁻ z, ENNReal.ofReal (|gX z| ^ q) ∂(markedSampleLaw T β (u + 1 + d) n) =
      ∫⁻ p, ENNReal.ofReal (|gX (rule.chain T (u + 1 + d) n p.1 p.2)| ^ q)
        ∂((wilsonLaw β (fineSide (Tb.stepParameters y).side (u + 1 + d) n)).prod
          (chainNoiseLaw (Tb.stepParameters y) (u + 1 + d) n)) := fun q => by
    conv_lhs => rw [← hmap]
    exact lintegral_map ((hXm.abs.pow_const q).ennreal_ofReal) hDm
  have e4 : ∀ x : ℝ, |x| ^ 4 = x ^ 4 := fun x => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have l2 : ∫⁻ z, ENNReal.ofReal (gX z ^ 2) ∂(markedSampleLaw T β (u + 1 + d) n) ≤ ENNReal.ofReal C₂ := by
    have e1 : (fun z => ENNReal.ofReal (gX z ^ 2)) = fun z => ENNReal.ofReal (|gX z| ^ 2) := funext fun z => by rw [sq_abs]
    rw [e1, lint 2]
    exact hX2
  have l4 : ∫⁻ z, ENNReal.ofReal (gX z ^ 4) ∂(markedSampleLaw T β (u + 1 + d) n) ≤ ENNReal.ofReal C₄ := by
    have e1 : (fun z => ENNReal.ofReal (gX z ^ 4)) = fun z => ENNReal.ofReal (|gX z| ^ 4) := funext fun z => by rw [e4]
    rw [e1, lint 4]
    exact hX4
  have p2 : ∀ z, 0 ≤ gX z ^ 2 := fun z => by positivity
  have p4 : ∀ z, 0 ≤ gX z ^ 4 := fun z => by positivity
  have i2 : Integrable (fun z => gX z ^ 2) (markedSampleLaw T β (u + 1 + d) n) :=
    (lintegral_ofReal_ne_top_iff_integrable (hXm.pow_const 2).aestronglyMeasurable (ae_of_all _ p2)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top l2)
  have i4 : Integrable (fun z => gX z ^ 4) (markedSampleLaw T β (u + 1 + d) n) :=
    (lintegral_ofReal_ne_top_iff_integrable (hXm.pow_const 4).aestronglyMeasurable (ae_of_all _ p4)).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top l4)
  have b2 : ∫ z, gX z ^ 2 ∂(markedSampleLaw T β (u + 1 + d) n) ≤ C₂ := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ p2) (hXm.pow_const 2).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hC₂ l2
  have b4 : ∫ z, gX z ^ 4 ∂(markedSampleLaw T β (u + 1 + d) n) ≤ C₄ := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ p4) (hXm.pow_const 4).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hC₄ l4
  have hXmem : MemLp gX 2 (markedSampleLaw T β (u + 1 + d) n) :=
    (memLp_two_iff_integrable_sq hXm.aestronglyMeasurable).mpr i2
  obtain ⟨Ψ, hΨd⟩ : ∃ Ψ, Ψ = fun V => truncateCase A sz B (Φ V) := ⟨_, rfl⟩
  obtain ⟨Xb, hXbd⟩ : ∃ Xb, Xb = fun z => caseLift T u _ Ψ (sampleBelow (Tb.stepParameters y) (u + 1) d n z) := ⟨_, rfl⟩
  have hΨm : Measurable (caseLift T u _ Ψ) := by
    rw [hΨd]
    exact hlm B
  have hbm : Measurable Xb := by
    rw [hXbd]
    exact hΨm.comp hπ
  have hXbv : ∀ z, Xb z =
      if supportWeightOfSample T u _ A sz (sampleBelow (Tb.stepParameters y) (u + 1) d n z) ≤ B then gX z else 0 := by
    intro z
    rw [hXbd, hΨd]
    simp only
    rw [caseLift_truncate, hgX z]
  have hsq : ∀ z, Xb z ^ 2 ≤ gX z ^ 2 := fun z => by
    rw [hXbv]
    split_ifs
    · exact le_rfl
    · simpa using p2 z
  have ib2 : Integrable (fun z => Xb z ^ 2) (markedSampleLaw T β (u + 1 + d) n) :=
    i2.mono' (hbm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hsq z)
  have hA2 : C₂ ≤ (1 + C₂) ^ 2 := by nlinarith
  have hbA : ∫ z, Xb z ^ 2 ∂(markedSampleLaw T β (u + 1 + d) n) ≤ (1 + C₂) ^ 2 :=
    (integral_mono ib2 i2 hsq).trans (b2.trans hA2)
  obtain ⟨S', hS'⟩ : ∃ S' : Set (MarkedSample (Tb.stepParameters y) (u + 1) (fineSide (Tb.stepParameters y).side d n)),
      S' = {x | B < supportWeightOfSample T u _ A sz x} := ⟨_, rfl⟩
  have hS'm : MeasurableSet S' := by
    rw [hS']
    exact measurableSet_lt measurable_const hNm
  obtain ⟨S, hSd⟩ : ∃ S : Set (MarkedSample (Tb.stepParameters y) (u + 1 + d) n),
      S = sampleBelow (Tb.stepParameters y) (u + 1) d n ⁻¹' S' := ⟨_, rfl⟩
  have hSm : MeasurableSet S := by
    rw [hSd]
    exact hπ hS'm
  have hB0 : 0 < B := by linarith
  have hmark : (markedSampleLaw T β (u + 1 + d) n).real S ≤ C₁ / B := by
    have e1 : (markedSampleLaw T β (u + 1 + d) n) S =
        (markedSampleLaw T β (u + 1) (fineSide (Tb.stepParameters y).side d n)) S' := by
      rw [hSd]
      exact hf.below.measure_preimage hS'm.nullMeasurableSet
    have hmk := mul_meas_ge_le_lintegral (μ := markedSampleLaw T β (u + 1) (fineSide (Tb.stepParameters y).side d n))
      (f := fun x => ENNReal.ofReal (supportWeightOfSample T u _ A sz x)) hNm.ennreal_ofReal (ENNReal.ofReal B)
    have hsub : S' ⊆ {x | ENNReal.ofReal B ≤ ENNReal.ofReal (supportWeightOfSample T u _ A sz x)} := by
      intro x hx
      rw [hS'] at hx
      exact ENNReal.ofReal_le_ofReal (le_of_lt hx)
    have h3 : ENNReal.ofReal B * (markedSampleLaw T β (u + 1) (fineSide (Tb.stepParameters y).side d n)) S' ≤ ENNReal.ofReal C₁ :=
      (mul_le_mul' le_rfl (measure_mono hsub)).trans (hmk.trans hN)
    have h4 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0.le, ENNReal.toReal_ofReal hC₁] at h4
    rw [le_div_iff₀ hB0, Measure.real, e1, mul_comm]
    exact h4
  have hpw : ∀ z, (gX z - Xb z) ^ 2 ≤ gX z ^ 4 / (2 * t) + t / 2 * S.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hz : supportWeightOfSample T u _ A sz (sampleBelow (Tb.stepParameters y) (u + 1) d n z) ≤ B
    · have hi0 : 0 ≤ S.indicator (fun _ => (1 : ℝ)) z := Set.indicator_nonneg (fun _ _ => zero_le_one) z
      rw [hXbv, if_pos hz, sub_self]
      have h1 : 0 ≤ gX z ^ 4 / (2 * t) := div_nonneg (p4 z) (by positivity)
      have h2 : 0 ≤ t / 2 * S.indicator (fun _ => (1 : ℝ)) z := mul_nonneg (by positivity) hi0
      have h3 : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h3]
      exact add_nonneg h1 h2
    · have hzS : z ∈ S := by
        rw [hSd, Set.mem_preimage, hS']
        exact not_le.mp hz
      rw [hXbv, if_neg hz, Set.indicator_of_mem hzS, sub_zero, mul_one]
      have key : gX z ^ 4 / (2 * t) + t / 2 - gX z ^ 2 = (gX z ^ 2 - t) ^ 2 / (2 * t) := by
        field_simp
        ring
      have : 0 ≤ (gX z ^ 2 - t) ^ 2 / (2 * t) := by positivity
      linarith
  have hXe : ∫ z, (gX z - Xb z) ^ 2 ∂(markedSampleLaw T β (u + 1 + d) n) ≤ e ^ 2 := by
    have iS : Integrable (S.indicator fun _ => (1 : ℝ)) (markedSampleLaw T β (u + 1 + d) n) := (integrable_const _).indicator hSm
    have iR : Integrable (fun z => gX z ^ 4 / (2 * t) + t / 2 * S.indicator (fun _ => (1 : ℝ)) z)
        (markedSampleLaw T β (u + 1 + d) n) :=
      (i4.div_const _).add (iS.const_mul _)
    have iL : Integrable (fun z => (gX z - Xb z) ^ 2) (markedSampleLaw T β (u + 1 + d) n) :=
      iR.mono' ((hXm.sub hbm).pow_const 2).aestronglyMeasurable (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hpw z)
    refine (integral_mono iL iR hpw).trans ?_
    rw [integral_add (i4.div_const _) (iS.const_mul _), integral_div, integral_const_mul, integral_indicator_const _ hSm]
    simp only [smul_eq_mul, mul_one]
    have h1 : (∫ z, gX z ^ 4 ∂(markedSampleLaw T β (u + 1 + d) n)) / (2 * t) ≤ C₄ / (2 * t) :=
      div_le_div_of_nonneg_right b4 (by positivity)
    have h2 : t / 2 * (markedSampleLaw T β (u + 1 + d) n).real S ≤ t / 2 * (C₁ / B) :=
      mul_le_mul_of_nonneg_left hmark (by positivity)
    linarith
  have hsize : ∀ j : ℕ, (1 : ℝ) ≤ (j : ℝ) + 1 := fun j => by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hXE : (markedSampleLaw T β (u + 1 + d) n)[gX | upperSigma T (u + 1) d n] =ᵐ[markedSampleLaw T β (u + 1 + d) n] gE := by
    have := condExp_upper_eq_caseMean_of_truncations hf Φ A sz hs (fun j => hlm _)
      (fun j => ⟨_, fun x => (hnear _ (hsize j) _).abs_le _ _ _ _ _⟩)
      (fun j => hf.one.mono fun x hx => caseIntegrable_of_bounded _ _ _ hx (hnear _ (hsize j) _).measurable
        (mul_nonneg hSz (pow_nonneg (by linarith [hsize j]) _)) (hnear _ (hsize j) _).abs_le) hCI
      (by rw [← hXeq]; exact hXmem.integrable one_le_two)
    rw [← hXeq, ← hEeq] at this
    exact this
  have hRm : Measurable gR := hRr.mono hf.upper le_rfl
  have hΨn : ∀ V, IsNearlyLocalCaseFunction (T.stage u).toStepSetup o Rr (Sz * B ^ a) (Ψ V) := fun V => by
    rw [hΨd]
    exact hnear B hB V
  have hmv : ∀ (o₁ : TorusSite (fineSide (Tb.stepParameters y).side d n * (Tb.stepParameters y).side))
      (F : CaseFunction (T.stage u).toStepSetup (fineSide (Tb.stepParameters y).side d n)),
      IsNearlyLocalCaseFunction (T.stage u).toStepSetup o₁ Rr (Sz * B ^ a) F →
      IsNearlyLocalCaseFunction (T.stage u).toStepSetup
        (o₁ + siteOfInt fun i => ((Tb.stepParameters y).side : ℤ) * (((Tb.stepParameters y).side : ℤ) * w' i)) Rr (Sz * B ^ a)
        (translateCaseFunction v F) := by
    intro o₁ F hF
    have := hNr g β _ mm T u _ hK1 w' o₁ Rr (Sz * B ^ a) F hF
    rw [hv]
    exact this
  have hfar' : ∀ (V : TorusField (fineSide (Tb.stepParameters y).side d n))
      (q : CoarseState (T.stage u).toStepSetup (fineSide (Tb.stepParameters y).side d n)),
      0 < coarseStateWeight (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup V) V q →
      ∀ F G : CaseFunction (T.stage u).toStepSetup (fineSide (Tb.stepParameters y).side d n),
        IsNearlyLocalCaseFunction (T.stage u).toStepSetup o Rr (Sz * B ^ a) F →
        IsNearlyLocalCaseFunction (T.stage u).toStepSetup
          (o + k • siteOfInt fun i => ((Tb.stepParameters y).side : ℤ) * (((Tb.stepParameters y).side : ℤ) * w' i)) Rr
          (Sz * B ^ a) G →
        |caseMean (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup V) V q
            (fun W Yt ωt bad b => F W Yt ωt bad b * G W Yt ωt bad b) -
          caseMean (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup V) V q F *
            caseMean (T.stage u).toStepSetup (hotCoreSites (T.stage u).toStepSetup V) V q G| ≤ δ := by
    rw [hw']
    exact hfar
  have hA0 : 0 ≤ 1 + C₂ := by linarith
  have main := iterate_covariance_bound hC hf hmP hmP' hl hr c5 c5' hsemi hm₁ hstm hBa hmv hΨn hΨm hpos k hfar' hRr hRb hXE
    hXmem hA0 he (b2.trans hA2) (by rw [hXbd] at hbA; exact hbA) (by rw [hXbd] at hXe; exact hXe)
  have htr : ∀ p, rule.chain T (u + 1 + d) n
      ((pairTranslate (Tb.stepParameters y) (u + 1 + d) n fun i => ((Tb.stepParameters y).side : ℤ) * w i)^[k] p).1
      ((pairTranslate (Tb.stepParameters y) (u + 1 + d) n fun i => ((Tb.stepParameters y).side : ℤ) * w i)^[k] p).2 =
      m^[k] (rule.chain T (u + 1 + d) n p.1 p.2) :=
    fun p => (Function.Semiconj.iterate_right (f := fun p : TorusField (fineSide (Tb.stepParameters y).side (u + 1 + d) n) ×
      ChainNoise.ChainNoise (Tb.stepParameters y) (u + 1 + d) n => rule.chain T (u + 1 + d) n p.1 p.2)
      (ga := pairTranslate (Tb.stepParameters y) (u + 1 + d) n fun i => ((Tb.stepParameters y).side : ℤ) * w i)
      (gb := m) hsem k) p
  have hEm : AEStronglyMeasurable gE (markedSampleLaw T β (u + 1 + d) n) :=
    (stronglyMeasurable_condExp.mono hf.upper).aestronglyMeasurable.congr hXE
  have hq := (hmP.iterate k).quasiMeasurePreserving
  have hfm : AEStronglyMeasurable (fun z => (gR z * (gX z - gE z)) * (gR (m^[k] z) * (gX (m^[k] z) - gE (m^[k] z))))
      (markedSampleLaw T β (u + 1 + d) n) := by
    have a1 : AEStronglyMeasurable gR (markedSampleLaw T β (u + 1 + d) n) := hRm.aestronglyMeasurable
    have a2 : AEStronglyMeasurable gX (markedSampleLaw T β (u + 1 + d) n) := hXm.aestronglyMeasurable
    exact (a1.mul (a2.sub hEm)).mul ((a1.comp_quasiMeasurePreserving hq).mul
      ((a2.comp_quasiMeasurePreserving hq).sub (hEm.comp_quasiMeasurePreserving hq)))
  have hint := integral_map (μ := (wilsonLaw β (fineSide (Tb.stepParameters y).side (u + 1 + d) n)).prod
      (chainNoiseLaw (Tb.stepParameters y) (u + 1 + d) n))
    hDm.aemeasurable (by rw [hmap]; exact hfm)
  rw [hmap] at hint
  simp_rw [htr]
  rw [← hint]
  exact main
end NoisePairs
section Points
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem stageOnFlow_of_point {j : ℕ} (hj : j ≤ S.data.windowLevel) :
    StageOnFlow Λ.table Λ.response Λ.floor S.β j ⟨S.tower.stage j, S.resp j⟩ := by apply _root_.YangMills.SharedProofs.p6811 <;> assumption
private theorem towerFollowsFlow_of_point : TowerFollowsFlow S.tower S.β S.data.windowLevel := by apply _root_.YangMills.SharedProofs.p11317 <;> assumption
private theorem hullChain_of_point (hg : 0 < Λ.g) (hfl : Λ.floor ≤ (Λ.g ^ 2)⁻¹) :
    HullChain Λ.table Λ.floor Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower := by apply _root_.YangMills.SharedProofs.p4319 <;> assumption
private theorem isBlockTorusSide_fineSide {d : ℕ} (h4 : 4096 ≤ Λ.stepParams.n₀) :
    IsBlockTorusSide Λ.stepParams (fineSide Λ.stepParams.side d (S.data.period Λ.stepParams.side)) := by
  have hLpos : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn₀ := S.side_le
  have hm : S.data.sideExponent ≠ 0 := by
    intro h0
    unfold LevelTestFunctions.LevelData.period at hn₀
    rw [h0, pow_zero] at hn₀
    nlinarith
  rw [fineSide_eq]
  refine ⟨?_, hn₀.trans (Nat.le_mul_of_pos_right _ (pow_pos hLpos _))⟩
  unfold LevelTestFunctions.LevelData.period
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ hm) _) _
end Points
section Assembly
variable {Λ : MomentParameters}
private theorem exists_cast_add_intCast {m : ℕ} [NeZero m] (x : ZMod m) (z : ℤ) :
    ∃ k : ℤ, (((x + (z : ZMod m) : ZMod m)).cast : ℤ) = (x.cast : ℤ) + z + (m : ℤ) * k := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.exists_cast_add_intCast <;> assumption
private theorem parentBlock_add {n L : ℕ} [NeZero n] [NeZero L] (x : TorusSite (n * L)) (v : Fin 4 → ℤ) :
    parentBlock L (x + siteOfInt fun i => (L : ℤ) * v i) = parentBlock L x + siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.parentBlock_add_scale <;> assumption
private theorem le_supDist_translate {m L : ℕ} [NeZero m] [NeZero L] (o : TorusSite (m * L)) (c k : ℕ) (hs : 2 * (k * c) ≤ m) :
    k * c ≤ TorusFields.supDist (parentBlock L o)
      (parentBlock L (o + k • siteOfInt fun i => (L : ℤ) * ((Pi.single 0 (c : ℤ) : Fin 4 → ℤ) i))) := by
  have e1 : (k • siteOfInt fun i => (L : ℤ) * ((Pi.single 0 (c : ℤ) : Fin 4 → ℤ) i) : TorusSite (m * L)) =
      siteOfInt fun i => (L : ℤ) * ((Pi.single 0 ((k * c : ℕ) : ℤ) : Fin 4 → ℤ) i) := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [siteOfInt]
      ring
    · simp [siteOfInt, Pi.single_eq_of_ne hi]
  rw [e1, parentBlock_add, supDist_comm]
  have h1 := Finset.le_sup (f := fun i =>
    (((parentBlock L o + siteOfInt (Pi.single 0 ((k * c : ℕ) : ℤ)) : TorusSite m) i - parentBlock L o i).valMinAbs).natAbs)
    (Finset.mem_univ (0 : Fin 4))
  refine le_trans ?_ h1
  have e2 : ((parentBlock L o + siteOfInt (Pi.single 0 ((k * c : ℕ) : ℤ)) : TorusSite m) 0 - parentBlock L o 0) =
      ((k * c : ℕ) : ZMod m) := by
    simp [siteOfInt]
  simp only [e2]
  rw [ZMod.valMinAbs_natCast_of_le_half (by omega), Int.natAbs_natCast]
private theorem measurePreserving_sampleBelow (hD : forgetLastStepStatement) {ℓ : StepParameters} (hfit : ℓ.Admissible)
    (T : StageTower ℓ) (hcut : ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (hco : T.MarksMeasurable)
    (β : ℝ) (t : ℕ) :
    ∀ (d n : ℕ) [NeZero n],
      MeasurePreserving (sampleBelow ℓ t d n) (markedSampleLaw T β (t + d) n) (markedSampleLaw T β t (fineSide ℓ.side d n)) := by
  intro d
  induction d with
  | zero =>
    intro n _
    exact MeasurePreserving.id _
  | succ d ih =>
    intro n _
    exact (ih (n * ℓ.side)).comp (hD ℓ hfit hfit.depth_lt T hcut hco β (t + d) n).2
private def FarCovarianceBound (Λ : MomentParameters) : Prop :=
  ∀ (K : ℕ) (β Sz : ℝ) (Rr : ℕ), ∃ Cs : ℝ, ∀ S : MomentPoint Λ, S.data.windowLevel = K → S.β = β →
    ∀ (u n : ℕ) [NeZero n], u < K → n = S.levelSide (u + 1) → ∀ (V : TorusField n) (Y : Finset (TorusSite n))
      (ω : Y → (S.tower.stage (u + 1)).labels.Ω),
      0 < coarseStateWeight (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩ →
      ∀ (o o' : TorusSite (n * Λ.stepParams.side)) (F G : CaseFunction (S.tower.stage u).toStepSetup n),
        IsNearlyLocalCaseFunction (S.tower.stage u).toStepSetup o Rr Sz F →
        IsNearlyLocalCaseFunction (S.tower.stage u).toStepSetup o' Rr Sz G →
        CaseIntegrable (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩
          (fun _ _ _ _ _ => 1) ∧
        |caseMean (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩
            (fun W Yt ωt bad b => F W Yt ωt bad b * G W Yt ωt bad b) -
            caseMean (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩ F *
              caseMean (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩ G| ≤
          Cs * Real.exp (-(Λ.stepParams.rt *
            (TorusFields.supDist (parentBlock Λ.stepParams.side o) (parentBlock Λ.stepParams.side o') : ℝ) / 2 ^ 8))
private structure MomentHypotheses (Λ : MomentParameters) : Prop where
  copies : conditionalCopyCovarianceStatement
  moves : ChainTranslationFacts Λ.table Λ.floor
  nears : NearlyLocalTranslationFacts Λ.table Λ.floor
  fit : Λ.stepParams.Admissible
  side : 4096 ≤ Λ.stepParams.n₀
  rate : 0 < Λ.stepParams.rt
  g_pos : 0 < Λ.g
  floor : Λ.floor ≤ (Λ.g ^ 2)⁻¹
  live : ∀ S : MomentPoint Λ, ∀ u ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide Λ.stepParams n →
    ∀ᵐ w ∂(S.law u n),
      IsLiveState Λ.stepParams (S.tower.stage u).coupling (S.tower.stage u).labelWeight (S.state u n w).1 (S.state u n w).2.1
        (S.state u n w).2.2
  read : ∀ (T : StageTower Λ.stepParams) (β : ℝ) (s n : ℕ) [NeZero n], IsTowerAtParameters Λ.table Λ.floor T β s →
    ColdStepAtMirrorFrames.IsCutoff (Λ.stepParams.threshold / 64) T.base.barrierFn →
    T.MarksMeasurable → (T.stage s).toStepSetup.IsWellPosed → IsBlockTorusSide Λ.stepParams (n * Λ.stepParams.side) →
    Λ.stepParams.side ∣ n → ReadsCasesAt T β s n
  noises : ∀ (g β : ℝ) (K m : ℕ) (T : StageTower Λ.stepParams), HullChain Λ.table Λ.floor g β K m T →
    ∀ rule : NoiseRule Λ.stepParams, rule.IsAdmissible T →
    ∀ (u n : ℕ) [NeZero n], HullChainAtLevel Λ.table Λ.floor g β K m T u n →
      ((wilsonLaw β (fineSide Λ.stepParams.side u n)).prod (chainNoiseLaw Λ.stepParams u n)).map
        (fun p => rule.chain T u n p.1 p.2) = markedSampleLaw T β u n
  borel : noiseChainMeasurableStatement
  below : forgetLastStepStatement
  markov : chainMarkovBackwardsStatement
  above : upperSigmaDeterminesStatesStatement
  states : StageStatesMeasurableStatement
  forms : ∀ S : MomentPoint Λ, ∀ u ≤ S.data.windowLevel, (S.tower.stage u).toStepSetup.IsWellPosed
private theorem single_torus_bound (H : MomentHypotheses Λ) (S : MomentPoint Λ) {rule : NoiseRule Λ.stepParams}
    (hrule : rule.IsAdmissible S.tower) {p : ℕ} (hp : 1 ≤ p)
    (hτ : MeasurePreserving (pairTranslate Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)
      (translationVector Λ.stepParams.side p)) S.sampleLaw S.sampleLaw)
    {u : ℕ} (hu : u + 1 ≤ S.data.windowLevel)
    {Φ : TorusField (S.sideAtLevel (u + 1)) → CaseFunction (S.tower.stage u).toStepSetup (S.sideAtLevel (u + 1))}
    {A : Finset (TorusSite (S.sideAtLevel (u + 1) * Λ.stepParams.side))}
    {o : TorusSite (S.sideAtLevel (u + 1) * Λ.stepParams.side)} {sz : (S.tower.stage u).labels.Ω → ℝ} {Rr a : ℕ} {Sz : ℝ}
    (hcl : ∀ V, IsQuasiLocalCaseFunction (S.tower.stage u).toStepSetup o Rr a Sz A sz (Φ V)) (hSz : 0 ≤ Sz)
    (hLm : Measurable (caseLift S.tower u _ Φ))
    (hCI : ∀ᵐ x ∂(markedSampleLaw S.tower S.β (u + 1) (S.sideAtLevel (u + 1))), CaseIntegrableAtSample S.tower u _ Φ x)
    {C₁ C₂ C₄ C : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₄ : 0 ≤ C₄)
    (hN : ∫⁻ x, ENNReal.ofReal (supportWeightOfSample S.tower u _ A sz x)
      ∂(markedSampleLaw S.tower S.β (u + 1) (S.sideAtLevel (u + 1))) ≤ ENNReal.ofReal C₁)
    {gR gX gE : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side) → ℝ}
    (hgX : ∀ z, gX z = caseLift S.tower u _ Φ (S.sampleAtLevel (u + 1) hu z))
    (hgE : ∀ z, gE z = caseMeanAtSample S.tower u _ Φ (S.sampleAtLevel (u + 1) hu z))
    (hRr : IsMeasurableAbove S (u + 1) gR) (hRb : ∀ z, |gR z| ≤ C)
    (hX2 : ∫⁻ q, ENNReal.ofReal (|gX (S.sampleOf rule q)| ^ 2) ∂S.sampleLaw ≤ ENNReal.ofReal C₂)
    (hX4 : ∫⁻ q, ENNReal.ofReal (|gX (S.sampleOf rule q)| ^ 4) ∂S.sampleLaw ≤ ENNReal.ofReal C₄)
    {B t e : ℝ} (hB : 1 ≤ B) (ht : 0 < t) (he : 0 ≤ e) (hee : C₄ / (2 * t) + t / 2 * (C₁ / B) ≤ e ^ 2) (k : ℕ) {Cs : ℝ}
    (hCs : ∀ (u n : ℕ) [NeZero n], u < S.data.windowLevel → n = S.levelSide (u + 1) → ∀ (V : TorusField n)
      (Y : Finset (TorusSite n)) (ω : Y → (S.tower.stage (u + 1)).labels.Ω),
      0 < coarseStateWeight (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩ →
      ∀ (o o' : TorusSite (n * Λ.stepParams.side)) (F G : CaseFunction (S.tower.stage u).toStepSetup n),
        IsNearlyLocalCaseFunction (S.tower.stage u).toStepSetup o Rr (Sz * B ^ a) F →
        IsNearlyLocalCaseFunction (S.tower.stage u).toStepSetup o' Rr (Sz * B ^ a) G →
        CaseIntegrable (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩
          (fun _ _ _ _ _ => 1) ∧
        |caseMean (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩
            (fun W Yt ωt bad b => F W Yt ωt bad b * G W Yt ωt bad b) -
            caseMean (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩ F *
              caseMean (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup V) V ⟨Y, ω⟩ G| ≤
          Cs * Real.exp (-(Λ.stepParams.rt *
            (TorusFields.supDist (parentBlock Λ.stepParams.side o) (parentBlock Λ.stepParams.side o') : ℝ) / 2 ^ 8)))
    (hsmall : 2 * (k * (Λ.stepParams.side * (Λ.stepParams.side ^ (S.data.windowLevel - (u + 1)) * p))) ≤ S.sideAtLevel (u + 1)) :
    |∫ q, (gR (S.sampleOf rule q) * (gX (S.sampleOf rule q) - gE (S.sampleOf rule q))) *
        (gR (S.sampleOf rule ((pairTranslate Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)
            (translationVector Λ.stepParams.side p))^[k] q)) *
          (gX (S.sampleOf rule ((pairTranslate Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)
              (translationVector Λ.stepParams.side p))^[k] q)) -
            gE (S.sampleOf rule ((pairTranslate Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)
              (translationVector Λ.stepParams.side p))^[k] q)))) ∂S.sampleLaw| ≤
      C ^ 2 * (|Cs| * Real.exp (-(Λ.stepParams.rt * (k : ℝ) / 2 ^ 8)) + 8 * (1 + C₂) * e) := by
  classical
  have hfit := H.fit
  have hLpos : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hd : u + 1 + (S.data.windowLevel - (u + 1)) = S.data.windowLevel := Nat.add_sub_of_le hu
  have hrun := hullChain_of_point S H.g_pos H.floor
  have a0 : HullChainAtLevel Λ.table Λ.floor Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower S.data.windowLevel
      (S.data.period Λ.stepParams.side) := ⟨hrun, le_rfl, by
    unfold torusSideAtLevel
    rw [Nat.sub_self]
    rfl⟩
  have a1 : HullChainAtLevel Λ.table Λ.floor Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower (u + 1)
      (S.sideAtLevel (u + 1)) := ⟨hrun, hu, rfl⟩
  have a2 : HullChainAtLevel Λ.table Λ.floor Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower u
      (S.sideAtLevel (u + 1) * Λ.stepParams.side) := ⟨hrun, by omega, by
    show fineSide Λ.stepParams.side (S.data.windowLevel - (u + 1)) (S.data.period Λ.stepParams.side) * Λ.stepParams.side =
      fineSide Λ.stepParams.side (S.data.windowLevel - u) (S.data.period Λ.stepParams.side)
    have e1 : S.data.windowLevel - u = (S.data.windowLevel - (u + 1)) + 1 := by omega
    rw [fineSide_eq, fineSide_eq, e1, pow_succ]
    ring⟩
  have hbs : IsBlockTorusSide Λ.stepParams (S.sideAtLevel (u + 1)) := isBlockTorusSide_fineSide S H.side
  have hbs2 : IsBlockTorusSide Λ.stepParams (S.sideAtLevel (u + 1) * Λ.stepParams.side) :=
    ⟨Dvd.intro_left _ rfl, hbs.2.trans (Nat.le_mul_of_pos_right _ hLpos)⟩
  have hstand : IsTowerAtParameters Λ.table Λ.floor S.tower S.β u :=
    { startsAtWilson := S.startsAtWilson
      coupling_eq := fun j hj => towerFollowsFlow_of_point S j (by omega)
      onFamily := fun j hj => (stageOnFlow_of_point S (by omega)).onFamily.onFamily }
  have hread := H.read S.tower S.β u (S.sideAtLevel (u + 1)) hstand S.isCutoff S.marksMeasurable (H.forms S u (by omega)) hbs2 hbs.1
  have hpos : ∀ᵐ x ∂(markedSampleLaw S.tower S.β (u + 1) (S.sideAtLevel (u + 1))),
      0 < coarseStateWeight (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup x.2.2.1) x.2.2.1
        (stageState S.tower (u + 1) _ x).2 := by
    refine (H.live S (u + 1) hu (S.sideAtLevel (u + 1)) hbs).mono fun x hx => ?_
    have h3 : 0 < coarseWeightExpansion (S.tower.stage u).toStepSetup (S.sideAtLevel (u + 1)) (stageState S.tower (u + 1) _ x).1
        (stageState S.tower (u + 1) _ x).2.1 (stageState S.tower (u + 1) _ x).2.2 := hx.2
    unfold coarseWeightExpansion at h3
    rw [dif_neg (NeZero.ne _)] at h3
    exact h3
  have hnS : S.sideAtLevel (u + 1) = S.levelSide (u + 1) := by
    show fineSide Λ.stepParams.side (S.data.windowLevel - (u + 1)) (S.data.period Λ.stepParams.side) =
      S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (u + 1))
    exact fineSide_eq _ _ _
  have hnear : ∀ V, IsNearlyLocalCaseFunction (S.tower.stage u).toStepSetup o Rr (Sz * B ^ a) (truncateCase A sz B (Φ V)) :=
    fun V => truncateCase_nearlyLocal (hcl V) hB hSz
  have hf : TorusData S.tower S.β u (S.data.windowLevel - (u + 1)) (S.data.period Λ.stepParams.side) :=
    { prob := (H.below Λ.stepParams hfit hfit.depth_lt S.tower S.isCutoff S.marksMeasurable S.β _ _).1
      prob' := (H.below Λ.stepParams hfit hfit.depth_lt S.tower S.isCutoff S.marksMeasurable S.β _ _).1
      below := measurePreserving_sampleBelow H.below hfit S.tower S.isCutoff S.marksMeasurable S.β (u + 1) _ _
      upper := (H.above Λ.stepParams hfit S.tower (u + 1) _ _).1
      state := H.states Λ.stepParams hfit S.tower (u + 1) _
      markov := fun G b hG hb =>
        H.markov Λ.stepParams hfit hfit.depth_lt S.tower S.isCutoff S.marksMeasurable S.β (u + 1) _ _ G b hG hb
      read := hread
      one := hpos.mono fun x hx => (hCs u _ (by omega) hnS x.2.2.1 (stageState S.tower (u + 1) _ x).2.1
        (stageState S.tower (u + 1) _ x).2.2 hx o o _ _ (hnear x.2.2.1) (hnear x.2.2.1)).1 }
  have hmap := H.noises Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower hrun rule hrule S.data.windowLevel
    (S.data.period Λ.stepParams.side) a0
  have h64 : 64 ≤ S.data.period Λ.stepParams.side := by
    have h1 := S.side_le
    have h2 := H.side
    nlinarith
  have hDm := H.borel Λ.stepParams hfit S.tower rule S.marksMeasurable hrule S.data.windowLevel (S.data.period Λ.stepParams.side)
    (isBlockTorusSide_fineSide (d := 0) S H.side).1 h64
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → ℤ, w = Pi.single 0 (p : ℤ) := ⟨_, rfl⟩
  have hew : (fun i => (Λ.stepParams.side : ℤ) * w i) = translationVector Λ.stepParams.side p := by
    funext i
    rw [hw]
    unfold translationVector
    by_cases hi : i = 0
    · subst hi
      simp
      ring
    · simp [Pi.single_eq_of_ne hi]
  have hst := H.states Λ.stepParams hfit S.tower u (S.sideAtLevel (u + 1) * Λ.stepParams.side)
  have main := noise_covariance_bound hd H.copies H.moves H.nears a0 a1 a2 hf hrule w hmap hDm (by rw [hew]; exact hτ) hst hpos
    hcl hSz hLm hCI hC₁ hC₂ hC₄ hN (gR := gR) (gX := gX) (gE := gE) (C := C) hgX hgE (hRr _ hd) hRb hX2 hX4 hB ht he hee k
    (δ := |Cs| * Real.exp (-(Λ.stepParams.rt * (k : ℝ) / 2 ^ 8))) ?_
  · rw [hew] at main
    exact main
  · rintro V ⟨Y, ω⟩ hq F G hF hG
    refine (hCs u _ (by omega) hnS V Y ω hq o _ F G hF hG).2.trans ?_
    obtain ⟨c, hc⟩ : ∃ c : ℕ, c = Λ.stepParams.side * (Λ.stepParams.side ^ (S.data.windowLevel - (u + 1)) * p) := ⟨_, rfl⟩
    have ev : (fun i => (Λ.stepParams.side : ℤ) * ((Λ.stepParams.side : ℤ) *
        ((Λ.stepParams.side : ℤ) ^ (S.data.windowLevel - (u + 1)) * w i))) =
        fun i => (Λ.stepParams.side : ℤ) * ((Pi.single 0 (c : ℤ) : Fin 4 → ℤ) i) := by
      funext i
      rw [hw, hc]
      by_cases hi : i = 0
      · subst hi
        simp
      · simp [Pi.single_eq_of_ne hi]
    have hdist := le_supDist_translate (m := S.sideAtLevel (u + 1)) (L := Λ.stepParams.side) o c k (by rw [hc]; exact hsmall)
    rw [← ev] at hdist
    have hcpos : 1 ≤ c := by
      rw [hc]
      exact Nat.mul_pos hLpos (Nat.mul_pos (pow_pos hLpos _) hp)
    have hkD : (k : ℝ) ≤ (TorusFields.supDist (parentBlock Λ.stepParams.side o) (parentBlock Λ.stepParams.side
        (o + k • siteOfInt fun i => (Λ.stepParams.side : ℤ) * ((Λ.stepParams.side : ℤ) *
          ((Λ.stepParams.side : ℤ) ^ (S.data.windowLevel - (u + 1)) * w i)))) : ℝ) := by
      have : k ≤ k * c := Nat.le_mul_of_pos_right _ hcpos
      exact_mod_cast this.trans hdist
    have hrt := H.rate
    have hexp : Real.exp (-(Λ.stepParams.rt * (TorusFields.supDist (parentBlock Λ.stepParams.side o) (parentBlock Λ.stepParams.side
        (o + k • siteOfInt fun i => (Λ.stepParams.side : ℤ) * ((Λ.stepParams.side : ℤ) *
          ((Λ.stepParams.side : ℤ) ^ (S.data.windowLevel - (u + 1)) * w i)))) : ℝ) / 2 ^ 8)) ≤
        Real.exp (-(Λ.stepParams.rt * (k : ℝ) / 2 ^ 8)) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hkD hrt.le
      have h2 : (0 : ℝ) < 2 ^ 8 := by norm_num
      have h3 := div_le_div_of_nonneg_right this h2.le
      linarith
    calc _ ≤ |Cs| * Real.exp (-(Λ.stepParams.rt * (TorusFields.supDist (parentBlock Λ.stepParams.side o) (parentBlock Λ.stepParams.side
          (o + k • siteOfInt fun i => (Λ.stepParams.side : ℤ) * ((Λ.stepParams.side : ℤ) *
            ((Λ.stepParams.side : ℤ) ^ (S.data.windowLevel - (u + 1)) * w i)))) : ℝ) / 2 ^ 8)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
end Assembly
section Core
variable {Λ : MomentParameters}
private theorem farCopies_core (H : MomentHypotheses Λ) (hFar : FarCovarianceBound Λ)
    (hKeep : ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S), (translatedTori F.points F.period).IsPreserving)
    (hDec : decorrelatedTranslatesMeanStatement) :
    ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (u : ℕ) (hu : ∀ i, u + 1 ≤ (F.points i).data.windowLevel)
    (Φ : ∀ i, TorusField ((F.points i).sideAtLevel (u + 1)) →
      CaseFunction ((F.points i).tower.stage u).toStepSetup ((F.points i).sideAtLevel (u + 1)))
    (Rr a : ℕ) (Sz : ℝ) (A : ∀ i, Finset (TorusSite ((F.points i).sideAtLevel (u + 1) * Λ.stepParams.side)))
    (o : ∀ i, TorusSite ((F.points i).sideAtLevel (u + 1) * Λ.stepParams.side))
    (sz : ∀ i, ((F.points i).tower.stage u).labels.Ω → ℝ) (jX jE jR : F.Index),
    (∀ i V, IsQuasiLocalCaseFunction ((F.points i).tower.stage u).toStepSetup (o i) Rr a Sz (A i) (sz i) (Φ i V)) →
    (∀ i, Measurable (FreeEnergies.caseLift (F.points i).tower u _ (Φ i))) →
    (∀ i, ∀ᵐ x ∂(markedSampleLaw (F.points i).tower (F.points i).β (u + 1) ((F.points i).sideAtLevel (u + 1))),
      FreeEnergies.CaseIntegrableAtSample (F.points i).tower u _ (Φ i) x) →
    (∃ C : ℝ, ∀ i, ∫⁻ x, ENNReal.ofReal (supportWeightOfSample (F.points i).tower u _ (A i) (sz i) x)
      ∂(markedSampleLaw (F.points i).tower (F.points i).β (u + 1) ((F.points i).sideAtLevel (u + 1))) ≤ ENNReal.ofReal C) →
    (∀ i w, F.observables jX (F.points i) w =
      FreeEnergies.caseLift (F.points i).tower u _ (Φ i) ((F.points i).sampleAtLevel (u + 1) (hu i) w)) →
    (∀ i w, F.observables jE (F.points i) w =
      FreeEnergies.caseMeanAtSample (F.points i).tower u _ (Φ i) ((F.points i).sampleAtLevel (u + 1) (hu i) w)) →
    (∃ C : ℝ, ∀ i w, |F.observables jR (F.points i) w| ≤ C) →
    (∀ i, IsMeasurableAbove (F.points i) (u + 1) (F.observables jR (F.points i))) →
    F.condMean (fun v => v (jR, 0) * v (jX, 0)) =ᵐ[F.law] F.condMean (fun v => v (jR, 0) * v (jE, 0)) := by
  intro S F u hu Φ Rr a Sz A o sz jX jE jR hcl hLm hCI hN hgX hgE hRb hRr
  classical
  haveI : Countable F.Index := F.countable_index
  refine hDec (translatedTori F.points F.period) F.Index (fun j => sampleFamily F.rule F.points F.period (F.observables j)) F.law
    (hKeep S F) F.hasBoundedMoments F.isJointLimitLaw jR jX jE ?_
  intro ε hε
  obtain ⟨Cr, hCr⟩ := hRb
  obtain ⟨Cn, hCn⟩ := hN
  obtain ⟨M2, hM2⟩ := (F.hasBoundedMoments jX).moment_bound 2
  obtain ⟨M4, hM4⟩ := (F.hasBoundedMoments jX).moment_bound 4
  have hSz : 0 ≤ Sz := by
    have h1 := (hcl 0 (trivialField _)).abs_le (trivialField _) ∅ (fun y => absurd y.2 (Finset.notMem_empty _)) ∅ (fun _ => 0)
    have h2 : ∑ y ∈ A 0, siteScore (sz 0) (∅ : Finset (TorusSite ((F.points 0).sideAtLevel (u + 1) * Λ.stepParams.side)))
        (fun y => absurd y.2 (Finset.notMem_empty _)) y = 0 :=
      Finset.sum_eq_zero fun y _ => by simp [siteScore]
    rw [h2, add_zero, one_pow, mul_one] at h1
    exact (abs_nonneg _).trans h1
  obtain ⟨C₁, hC₁d⟩ : ∃ C₁, C₁ = max Cn 0 := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂d⟩ : ∃ C₂, C₂ = max M2 0 := ⟨_, rfl⟩
  obtain ⟨C₄, hC₄d⟩ : ∃ C₄, C₄ = max M4 0 := ⟨_, rfl⟩
  obtain ⟨Cc, hCcd⟩ : ∃ Cc, Cc = max Cr 1 := ⟨_, rfl⟩
  have hC₁ : 0 ≤ C₁ := hC₁d ▸ le_max_right _ _
  have hC₂ : 0 ≤ C₂ := hC₂d ▸ le_max_right _ _
  have hC₄ : 0 ≤ C₄ := hC₄d ▸ le_max_right _ _
  have hCc1 : 1 ≤ Cc := hCcd ▸ le_max_right _ _
  have hCc0 : 0 < Cc := by linarith
  have hA0 : 0 < 1 + C₂ := by linarith
  obtain ⟨e, hed⟩ : ∃ e, e = ε / (16 * Cc ^ 2 * (1 + C₂)) := ⟨_, rfl⟩
  have he0 : 0 < e := by
    rw [hed]
    positivity
  obtain ⟨t, htd⟩ : ∃ t, t = C₄ / e ^ 2 + 1 := ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [htd]
    positivity
  obtain ⟨B, hBd⟩ : ∃ B, B = t * C₁ / e ^ 2 + 1 := ⟨_, rfl⟩
  have hB1 : 1 ≤ B := by
    have : 0 ≤ t * C₁ / e ^ 2 := by positivity
    rw [hBd]
    linarith
  have hB0 : 0 < B := by linarith
  have he2 : 0 < e ^ 2 := by positivity
  have hee : C₄ / (2 * t) + t / 2 * (C₁ / B) ≤ e ^ 2 := by
    have h1 : C₄ / (2 * t) ≤ e ^ 2 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : t * e ^ 2 = C₄ + e ^ 2 := by
        rw [htd]
        field_simp
      nlinarith
    have h2 : t / 2 * (C₁ / B) ≤ e ^ 2 / 2 := by
      have e1 : t / 2 * (C₁ / B) = t * C₁ / (2 * B) := by
        field_simp
      rw [e1, div_le_iff₀ (by positivity)]
      have : B * e ^ 2 = t * C₁ + e ^ 2 := by
        rw [hBd]
        field_simp
      nlinarith
    linarith
  obtain ⟨Cs, hCs⟩ := hFar S.data.windowLevel S.β (Sz * B ^ a) Rr
  have hrt := H.rate
  obtain ⟨η, hηd⟩ : ∃ η, η = ε / (2 * Cc ^ 2 * (|Cs| + 1)) := ⟨_, rfl⟩
  have hη : 0 < η := by
    rw [hηd]
    positivity
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → Real.exp (-(Λ.stepParams.rt * (k : ℝ) / 2 ^ 8)) ≤ η := by
    obtain ⟨k₀, hk⟩ := exists_nat_ge (-Real.log η * 2 ^ 8 / Λ.stepParams.rt)
    refine ⟨k₀, fun k hk' => ?_⟩
    have h1 : -Real.log η * 2 ^ 8 / Λ.stepParams.rt ≤ k := hk.trans (by exact_mod_cast hk')
    rw [div_le_iff₀ hrt] at h1
    rw [← Real.le_log_iff_exp_le hη]
    have h2 : Λ.stepParams.rt * (k : ℝ) / 2 ^ 8 ≥ -Real.log η := by
      rw [ge_iff_le, le_div_iff₀ (by norm_num)]
      linarith
    linarith
  have hL2 : 1 < Λ.stepParams.side := by
    have := H.fit.L_ge
    omega
  refine ⟨k₀, fun k hk => ⟨k * (Λ.stepParams.side * F.period) + 1, fun i hi => ?_⟩⟩
  obtain ⟨hp', hs', heq⟩ := F.points_eq i
  have hKi : (F.points i).data.windowLevel = S.data.windowLevel := by rw [heq]; rfl
  have hβi : (F.points i).β = S.β := by rw [heq]; rfl
  have hTi : (F.points i).tower = S.tower := by rw [heq]; rfl
  have hmi : (F.points i).data.sideExponent = F.exponents i := by rw [heq]; rfl
  have hsmall : 2 * (k * (Λ.stepParams.side * (Λ.stepParams.side ^ ((F.points i).data.windowLevel - (u + 1)) * F.period))) ≤
      (F.points i).sideAtLevel (u + 1) := by
    show _ ≤ fineSide Λ.stepParams.side ((F.points i).data.windowLevel - (u + 1)) ((F.points i).data.period Λ.stepParams.side)
    rw [fineSide_eq]
    unfold LevelTestFunctions.LevelData.period
    rw [hmi]
    have h1 : i ≤ F.exponents i := F.strictMono_exponents.le_apply
    have h2 : F.exponents i < Λ.stepParams.side ^ F.exponents i := Nat.lt_pow_self hL2
    have h3 : k * (Λ.stepParams.side * F.period) ≤ Λ.stepParams.side ^ F.exponents i := by omega
    calc 2 * (k * (Λ.stepParams.side * (Λ.stepParams.side ^ ((F.points i).data.windowLevel - (u + 1)) * F.period))) =
          2 * (k * (Λ.stepParams.side * F.period)) * Λ.stepParams.side ^ ((F.points i).data.windowLevel - (u + 1)) := by ring
      _ ≤ 2 * Λ.stepParams.side ^ F.exponents i * Λ.stepParams.side ^ ((F.points i).data.windowLevel - (u + 1)) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3)
  have hb := single_torus_bound H (F.points i) (rule := F.rule) (by rw [hTi]; exact F.rule_admissible) F.one_le_period
    ((hKeep S F).measurePreserving i) (hu i)
    (hcl i) hSz (hLm i) (hCI i) hC₁ hC₂ hC₄ ((hCn i).trans (ENNReal.ofReal_le_ofReal (hC₁d ▸ le_max_left _ _))) (C := Cc)
    (gR := F.observables jR (F.points i)) (gX := F.observables jX (F.points i)) (gE := F.observables jE (F.points i))
    (hgX i) (hgE i) (hRr i)
    (fun z => (hCr i z).trans (hCcd ▸ le_max_left _ _))
    ((hM2 i).trans (ENNReal.ofReal_le_ofReal (hC₂d ▸ le_max_left _ _)))
    ((hM4 i).trans (ENNReal.ofReal_le_ofReal (hC₄d ▸ le_max_left _ _))) hB1 ht0 he0.le hee k (Cs := Cs)
    (fun u' n _ hlt hn => hCs (F.points i) hKi hβi u' n (hKi ▸ hlt) hn) hsmall
  refine hb.trans ?_
  have hE := hk₀ k hk
  have h1 : Cc ^ 2 * (|Cs| * Real.exp (-(Λ.stepParams.rt * (k : ℝ) / 2 ^ 8))) ≤ ε / 2 := by
    have h2 : |Cs| * Real.exp (-(Λ.stepParams.rt * (k : ℝ) / 2 ^ 8)) ≤ (|Cs| + 1) * η :=
      mul_le_mul (by linarith) hE (Real.exp_pos _).le (by positivity)
    have h3 : Cc ^ 2 * ((|Cs| + 1) * η) = ε / 2 := by
      rw [hηd]
      field_simp
    calc _ ≤ Cc ^ 2 * ((|Cs| + 1) * η) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ε / 2 := h3
  have h2 : Cc ^ 2 * (8 * (1 + C₂) * e) = ε / 2 := by
    rw [hed]
    field_simp
    ring
  have h3 : Cc ^ 2 * (|Cs| * Real.exp (-(Λ.stepParams.rt * (k : ℝ) / 2 ^ 8)) + 8 * (1 + C₂) * e) =
      Cc ^ 2 * (|Cs| * Real.exp (-(Λ.stepParams.rt * (k : ℝ) / 2 ^ 8))) + Cc ^ 2 * (8 * (1 + C₂) * e) := by ring
  rw [h3]
  linarith
end Core
end FarCopiesConditional
open FarCopiesConditional in
theorem farCopiesConditional_holds (hFF : farCovarianceDecayStatement) (hLive : liveStatesStatement)
    (hM : conditionalMeanReadsCasesStatement) (hMk : chainMarkovBackwardsStatement) (hD : forgetLastStepStatement)
    (hUp : upperSigmaDeterminesStatesStatement) (hSt : StageStatesMeasurableStatement)
    (hCh : chainTranslationStatement) (hNr : nearlyLocalTranslateStatement)
    (hDec : decorrelatedTranslatesMeanStatement) (hCp : conditionalCopyCovarianceStatement) (hPt : largerToriStatement)
    (hNo : noiseRepresentationStatement) (hBo : noiseChainMeasurableStatement) (hLv : StagesAreWellPosed) :
    farCopiesConditionalStatement := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, p₁, P₁⟩ := hFF a ha
  obtain ⟨L₂, r₂, C₂, p₂, P₂⟩ := hLive a ha
  obtain ⟨L₃, r₃, C₃, p₃, P₃⟩ := hCh a ha
  obtain ⟨L₄, r₄, C₄, p₄, P₄⟩ := hNr a ha
  obtain ⟨L₅, r₅, C₅, p₅, P₅⟩ := hPt a ha
  obtain ⟨L₆, r₆, C₆, p₆, P₆⟩ := hNo a ha
  obtain ⟨L₇, r₇, p₇, P₇⟩ := hM a ha
  refine ⟨max L₁ (max L₂ (max L₃ (max L₄ (max L₅ (max L₆ L₇))))),
    fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (min (r₄ c) (min (r₅ c) (min (r₆ c) (r₇ c)))))),
    max C₁ (max C₂ (max C₃ (max C₄ (max C₅ C₆)))),
    fun c => lt_min (p₁ c) (lt_min (p₂ c) (lt_min (p₃ c) (lt_min (p₄ c) (lt_min (p₅ c) (lt_min (p₆ c) (p₇ c)))))),
    fun L hodd hLe Tb hTa hTL hDr hCold hHalf hrt hCder => ?_⟩
  simp only [max_le_iff] at hLe hCder
  simp only [le_min_iff] at hrt
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hLe
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hCder
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := hrt
  have Q₁ := P₁ L hodd l1 Tb hTa hTL hDr hCold hHalf t1 c1
  have Q₂ := P₂ L hodd l2 Tb hTa hTL hDr hCold hHalf t2 c2
  obtain ⟨M₃, Q₃⟩ := P₃ L hodd l3 Tb hTa hTL hDr hCold hHalf t3 c3
  obtain ⟨M₄, Q₄⟩ := P₄ L hodd l4 Tb hTa hTL hDr hCold hHalf t4 c4
  obtain ⟨M₅, Q₅⟩ := P₅ L hodd l5 Tb hTa hTL hDr hCold hHalf t5 c5
  obtain ⟨M₆, Q₆⟩ := P₆ L hodd l6 Tb hTa hTL hDr hCold hHalf t6 c6
  obtain ⟨y₇, Q₇⟩ := P₇ L hodd l7 Tb hTa hTL hDr t7
  obtain ⟨y₈, V₁⟩ := hLv Tb hDr
  refine ⟨max M₃ (max M₄ (max M₅ M₆)), fun Kr hKc hη hN hfit hret => ?_⟩
  simp only [max_le_iff] at hKc
  obtain ⟨k3, k4, k5, k6⟩ := hKc
  obtain ⟨y₁, R₁⟩ := Q₁ Kr hfit
  obtain ⟨y₂, R₂⟩ := Q₂ Kr hfit
  obtain ⟨y₃, R₃⟩ := Q₃ Kr k3 hη hN hfit hret
  obtain ⟨y₄, R₄⟩ := Q₄ Kr k4 hη hN hfit hret
  obtain ⟨y₅, R₅⟩ := Q₅ Kr k5 hη hN hfit hret
  obtain ⟨y₆, R₆⟩ := Q₆ Kr k6 hη hN hfit hret
  refine ⟨max y₁ (max y₂ (max y₃ (max y₄ (max y₅ (max y₆ (max y₇ (max y₈ Tb.floorMin))))))),
    fun y hy hRet hWil g hg hgy k _ hk2 hk8 Rd dd hdd => ?_⟩
  simp only [max_le_iff] at hy
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e0⟩ := hy
  have Fa : FarCovarianceBound ⟨Tb, Kr, y, g, k, Rd, dd⟩ := R₁ y e1 hRet hWil g hg hgy k hk2 hk8 Rd dd hdd
  obtain ⟨Cl, cl, Xl, -, -, Lv⟩ := R₂ y e2 hRet hWil g hg hgy k hk2 hk8 Rd dd hdd
  have Pts := R₅ y e5 hRet hWil g hg hgy k hk2 hk8 Rd dd hdd
  have Noi := R₆ y e6 hRet hWil
  have Re := Q₇ y e7 hRet hWil
  have hfits : (Tb.stepParameters y).Admissible := hDr.fits y e0
  refine farCopies_core (Λ := ⟨Tb, Kr, y, g, k, Rd, dd⟩) ?_ Fa
    (fun S F => ((Pts S).2.2.2 F.rule F.exponents F.points F.period F.rule_admissible F.one_le_period F.strictMono_exponents
      F.points_eq).1) hDec
  refine ⟨hCp, R₃ y e3 hRet hWil, R₄ y e4 hRet hWil, hfits, hDr.n₀_ge, hDr.rt_pos, hg, hgy, fun S => Lv S, Re,
    fun g' β K m T h => (Noi g' β K m T h).2, hBo, hD, hMk, hUp, hSt, ?_⟩
  intro S u hu
  have hFo := V₁ y e8 Kr S.β S.labelFacts S.initial S.isInitial S.data.windowLevel S.onFlow u hu
  have pack : ∀ z : StageWithResponse (Tb.stepParameters y), z = flowStages Tb y S.β S.labelFacts S.initial u →
      z.1.toStepSetup.IsWellPosed := by
    rintro _ rfl
    exact hFo
  exact pack ⟨S.tower.stage u, S.resp u⟩ (S.stage_eq u hu)
end MomentLaw
end YangMills.Construction
end
