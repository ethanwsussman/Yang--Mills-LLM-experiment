import YangMills.Construction.FreeEnergiesOfTheFlow.FittedResponsesAreMeansProof
import YangMills.Construction.FreeEnergiesOfTheFlow.StateOfAStepIsBorelProof
import YangMills.Construction.LawOnABoxOfTheFlow.DensityOfTheStateAlongTheFlow
import YangMills.Construction.ResponseInTheExpansion.MeanGivenTheStateOfAStep
import YangMills.Construction.ResponseInTheExpansion.MeansGivenAStateAreMeansOverItsCases
import YangMills.Construction.ResponseInTheExpansion.TheChainIsALaw
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings TorusLumps TorusFields StepCosts WeightedResponses
namespace CaseMeans
section Factorization
private theorem exists_measurable_factor {X K : Type} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace K]
    [StandardBorelSpace K] {π : X → K} (hπ : Measurable π) {Φ : X → ℝ} (hΦ : Measurable Φ)
    (hconst : ∀ x x', π x = π x' → Φ x = Φ x') :
    ∃ h : K → ℝ, Measurable h ∧ ∀ x, h (π x) = Φ x := by
  classical
  let g : Set.range π → ℝ := fun y => Φ y.2.choose
  have hg : ∀ x, g ⟨π x, Set.mem_range_self x⟩ = Φ x := fun x =>
    hconst _ _ (Set.mem_range_self x : π x ∈ Set.range π).choose_spec
  have gm : Measurable g := by
    intro B hB
    have e : π ⁻¹' (Subtype.val '' (g ⁻¹' B)) = Φ ⁻¹' B := by
      ext x
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hy' : y = ⟨π x, Set.mem_range_self x⟩ := Subtype.ext hyx
        rw [hy'] at hy
        show Φ x ∈ B
        rw [← hg x]
        exact hy
      · intro hx
        refine ⟨⟨π x, Set.mem_range_self x⟩, ?_, rfl⟩
        show g ⟨π x, Set.mem_range_self x⟩ ∈ B
        rw [hg x]
        exact hx
    have h1 : MeasurableSet (π ⁻¹' (Subtype.val '' (g ⁻¹' B))) := by
      rw [e]
      exact hΦ hB
    have h2 := (hπ.measurableSet_preimage_iff_preimage_val).1 h1
    rwa [Set.preimage_image_eq _ Subtype.val_injective] at h2
  obtain ⟨h, hm, he⟩ := Measurable.exists_eq_measurable_comp (f := (Subtype.val : Set.range π → K)) (g := g) gm
  refine ⟨h, hm, fun x => ?_⟩
  rw [← hg x, he]
  rfl
private theorem measurable_sigmaMk {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    Measurable (Sigma.mk a : β a → Sigma β) :=
  measurable_iff_le_map.2 (iInf_le _ a)
private theorem measurable_of_sigma_fibers {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] {γ : Type}
    [MeasurableSpace γ] {f : Sigma β → γ} (h : ∀ a, Measurable fun y : β a => f ⟨a, y⟩) : Measurable f := by apply _root_.YangMills.SharedProofs.p3239 <;> assumption
private theorem measurableSet_sigma_fst_eq {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
private def finCode {α : Type} [Fintype α] (a : α) : ℕ := (Fintype.equivFin α a : ℕ)
private theorem finCode_injective {α : Type} [Fintype α] : Function.Injective (finCode (α := α)) := fun a a' h =>
  (Fintype.equivFin α).injective (Fin.ext h)
end Factorization
section Samples
variable {ℓ : TorusLumps.StepParameters}
private instance (L n : ℕ) : DiscreteMeasurableSpace (BaseChoice L n) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) : DiscreteMeasurableSpace (BondSet m) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) [NeZero m] : Fintype (BondSet m) := inferInstanceAs (Fintype (Finset (TorusBond m)))
private instance torusField_standardBorel (n : ℕ) [NeZero n] : StandardBorelSpace (TorusField n) :=
  StandardBorelSpace.pi_countable
private theorem markedSample_standardBorel (s : ℕ) :
    ∀ (n : ℕ) [NeZero n], StandardBorelSpace (MarkedSample ℓ s n) := by
  induction s with
  | zero =>
    intro n _
    exact torusField_standardBorel n
  | succ s ih =>
    intro n _
    have h1 := ih (n * ℓ.side)
    have h2 : StandardBorelSpace (BaseChoice ℓ.side n) := inferInstance
    have h3 : StandardBorelSpace (BondSet (n * ℓ.side)) := inferInstance
    have h4 : StandardBorelSpace (TorusField n × BondSet (n * ℓ.side)) := StandardBorelSpace.prod
    have h5 : StandardBorelSpace (StepOutcome ℓ n) := StandardBorelSpace.prod
    exact (StandardBorelSpace.prod : StandardBorelSpace (MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n))
private def labelledSetCode {Λ : LabelSpace} {m : ℕ} [NeZero m] (q : Σ Y : Finset (TorusSite m), (Y → Λ.Ω)) :
    ℕ × ℝ :=
  (finCode q.1, MeasureTheory.embeddingReal (q.1 → Λ.Ω) q.2)
private theorem labelledSetCode_measurable {Λ : LabelSpace} {m : ℕ} [NeZero m] :
    Measurable (labelledSetCode (Λ := Λ) (m := m)) :=
  measurable_of_sigma_fibers fun Y => by
    show Measurable fun y : Y → Λ.Ω => ((finCode Y, MeasureTheory.embeddingReal (Y → Λ.Ω) y) : ℕ × ℝ)
    exact measurable_const.prodMk (MeasureTheory.measurable_embeddingReal (Y → Λ.Ω))
private theorem labelledSetCode_injective {Λ : LabelSpace} {m : ℕ} [NeZero m] :
    Function.Injective (labelledSetCode (Λ := Λ) (m := m)) := by
  rintro ⟨Y, ω⟩ ⟨Y', ω'⟩ h
  have h1 : Y = Y' := finCode_injective (congrArg Prod.fst h)
  subst h1
  have h2 : ω = ω' :=
    (MeasureTheory.measurableEmbedding_embeddingReal (Y → Λ.Ω)).injective (congrArg Prod.snd h)
  rw [h2]
private theorem stageState_fst (T : StageTower ℓ) (s n : ℕ) [NeZero n] (u : MarkedSample ℓ s n) :
    (stageState T s n u).1 = topField ℓ s n u := by apply _root_.YangMills.SharedProofs.p2480 <;> assumption
open Classical in
private theorem exists_sample_of_labelWeight_ne_zero (T : StageTower ℓ) {β : ℝ}
    (hs : StageTower.StartsAtWilson T β) (t : ℕ) :
    ∀ (m : ℕ) [NeZero m] (W : TorusField m) (Y : Finset (TorusSite m)) (ω : Y → (T.stage t).labels.Ω),
      (T.stage t).labelWeight m W Y ω ≠ 0 → ∃ u : MarkedSample ℓ t m, stageState T t m u = (W, ⟨Y, ω⟩) := by
  induction t with
  | zero =>
    intro m _ W Y ω h
    have hd := hs.labelWeight_eq m W Y ω
    by_cases hY : Y = thickening (2 * clusterRange T.base.coupling) (torusHotSites ℓ W)
    · subst hY
      refine ⟨W, ?_⟩
      have e : ω = fun _ => T.basePoint := funext fun y => hs.eq_basePoint (ω y)
      rw [e]
      rfl
    · exact absurd (hd.trans (if_neg hY)) h
  | succ t ih =>
    intro m _ V Y ω h
    have h1 : coarseStateWeight (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup V) V ⟨Y, ω⟩ ≠ 0 := by
      intro h0
      apply h
      show coarseWeightExpansion (T.stage t).toStepSetup m V Y ω = 0
      unfold coarseWeightExpansion
      rw [dif_neg (NeZero.ne m)]
      exact h0
    have h2 : coarseStateMass (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup V) V ⟨Y, ω⟩ ≠ 0 := by
      intro h0
      apply h1
      unfold coarseStateWeight
      rw [h0]
      rfl
    obtain ⟨bad, -, h3⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
    obtain ⟨Yt, -, h4⟩ := Finset.exists_ne_zero_of_sum_ne_zero h3
    obtain ⟨b, -, h5⟩ := Finset.exists_ne_zero_of_sum_ne_zero h4
    have h6 : ∃ (W : TorusField (m * ℓ.side))
        (ν : CoarseState.unlabelled (R := (T.stage t).toStepSetup) ⟨Y, ω⟩ Yt → (T.stage t).labels.Ω),
        IsHullState ℓ (T.stage t).toStepSetup.range
          (CoarseState.fieldWithStoredLinks (R := (T.stage t).toStepSetup) ⟨Y, ω⟩ W) Yt ∧
        coarseStateOf (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup V)
          (CoarseState.fieldWithStoredLinks (R := (T.stage t).toStepSetup) ⟨Y, ω⟩ W) Yt
          (CoarseState.fillLabels (R := (T.stage t).toStepSetup) ⟨Y, ω⟩ Yt ν) bad b = ⟨Y, ω⟩ ∧
        stepWeight (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup V) V
          (CoarseState.fieldWithStoredLinks (R := (T.stage t).toStepSetup) ⟨Y, ω⟩ W) Yt
          (CoarseState.fillLabels (R := (T.stage t).toStepSetup) ⟨Y, ω⟩ Yt ν) bad b ≠ 0 := by
      by_contra hc
      push Not at hc
      apply h5
      refine Eq.trans (lintegral_congr (g := fun _ => 0) fun W => ?_) (by simp)
      refine Eq.trans (lintegral_congr (g := fun _ => 0) fun ν => ?_) (by simp)
      by_cases ht : IsHullState ℓ (T.stage t).toStepSetup.range
            (CoarseState.fieldWithStoredLinks (R := (T.stage t).toStepSetup) ⟨Y, ω⟩ W) Yt ∧
          coarseStateOf (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup V)
            (CoarseState.fieldWithStoredLinks (R := (T.stage t).toStepSetup) ⟨Y, ω⟩ W) Yt
            (CoarseState.fillLabels (R := (T.stage t).toStepSetup) ⟨Y, ω⟩ Yt ν) bad b = ⟨Y, ω⟩
      · rw [if_pos ht, hc W ν ht.1 ht.2]
        simp
      · rw [if_neg ht]
    obtain ⟨W, ν, -, h7, h8⟩ := h6
    have h9 : (T.stage t).labelWeight (m * ℓ.side)
        (CoarseState.fieldWithStoredLinks (R := (T.stage t).toStepSetup) ⟨Y, ω⟩ W) Yt
        (CoarseState.fillLabels (R := (T.stage t).toStepSetup) ⟨Y, ω⟩ Yt ν) ≠ 0 := by
      intro h0
      apply h8
      unfold stepWeight
      have h0' : (T.stage t).toStepSetup.labelWeight (m * (T.stage t).toStepSetup.params.side)
        (CoarseState.fieldWithStoredLinks (R := (T.stage t).toStepSetup) ⟨Y, ω⟩ W) Yt
        (CoarseState.fillLabels (R := (T.stage t).toStepSetup) ⟨Y, ω⟩ Yt ν) = 0 := h0
      rw [h0']
      simp
    obtain ⟨u, hu⟩ := ih (m * ℓ.side) _ _ _ h9
    refine ⟨(u, (b, V, bad)), ?_⟩
    show (V, coarseStateOf (T.stage t).toStepSetup (hotCoreSites (T.stage t).toStepSetup V)
      (stageState T t (m * ℓ.side) u).1
      (stageState T t (m * ℓ.side) u).2.1 (stageState T t (m * ℓ.side) u).2.2 bad b) = (V, ⟨Y, ω⟩)
    rw [hu]
    exact Prod.ext rfl h7
private theorem measurableSet_hotCore (hB : StageStatesMeasurableStatement) (hadm : ℓ.Admissible)
    (T : StageTower ℓ) (R : StepSetup) (hR : R.params = ℓ) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)) :
    MeasurableSet {V : TorusField n | thickening (2 * R.nextRange) (torusHotSites ℓ V) = a} := by
  let T' : StageTower ℓ := { T with base := { T.base with coupling := R.nextCoupling } }
  have h := hB ℓ hadm T' 0 n
  have e : {V : TorusField n | thickening (2 * R.nextRange) (torusHotSites ℓ V) = a} =
      (stageState T' 0 n) ⁻¹' (Prod.snd ⁻¹' {z | z.1 = a}) := rfl
  rw [e]
  exact h (measurable_snd (measurableSet_sigma_fst_eq a))
end Samples
section StepConditioning
variable {ℓ : TorusLumps.StepParameters}
private theorem condExp_eq_caseMean_step (hG : conditionalMeanGivenCoarseState)
    (hBo : StageStatesMeasurableStatement)
    (T : StageTower ℓ) (β : ℝ) (s n : ℕ) [NeZero n] (hs : StageTower.StartsAtWilson T β)
    (hmark : T.MarksMeasurable)
    (hR : (T.stage s).toStepSetup.IsWellPosed) (hn : ℓ.n₀ ≤ n) (hd : ℓ.side ∣ n)
    (hp0 : IsProbabilityMeasure (markedSampleLaw T β s (n * ℓ.side)))
    (hp1 : IsProbabilityMeasure (markedSampleLaw T β (s + 1) n))
    {Z : ENNReal} (hZ0 : Z ≠ 0) (hZt : Z ≠ ⊤)
    (hD : HasStateDensity (T.stage s).toStepSetup n Z (markedSampleLaw T β s (n * ℓ.side))
      (stageState T s (n * ℓ.side)))
    (F : TorusField n → CaseFunction (T.stage s).toStepSetup n)
    (hm : Measurable fun u : MarkedSample ℓ (s + 1) n => F u.2.2.1 (topField ℓ s (n * ℓ.side) u.1)
      (stageState T s (n * ℓ.side) u.1).2.1 (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1)
    (hb : ∃ C : ℝ, ∀ u : MarkedSample ℓ (s + 1) n, |F u.2.2.1 (topField ℓ s (n * ℓ.side) u.1)
      (stageState T s (n * ℓ.side) u.1).2.1 (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1| ≤ C) :
    ((markedSampleLaw T β (s + 1) n)[fun u : MarkedSample ℓ (s + 1) n => F u.2.2.1 (topField ℓ s (n * ℓ.side) u.1)
        (stageState T s (n * ℓ.side) u.1).2.1 (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1 |
        stageSigma T (s + 1) n]) =ᵐ[markedSampleLaw T β (s + 1) n]
      fun u => caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
        (stageState T (s + 1) n u).2 (F u.2.2.1) := by
  classical
  obtain ⟨C, hC⟩ := hb
  have hadm : ℓ.Admissible := hR.admissible
  have hst : Measurable (stageState T s (n * ℓ.side)) := hBo ℓ hadm T s (n * ℓ.side)
  have hstd := markedSample_standardBorel (ℓ := ℓ) (s + 1) n
  let π : MarkedSample ℓ (s + 1) n → TorusField n × TorusField (n * ℓ.side) × (ℕ × ℝ) × ℕ × ℕ := fun u =>
    (u.2.2.1, (stageState T s (n * ℓ.side) u.1).1, labelledSetCode (stageState T s (n * ℓ.side) u.1).2,
      finCode u.2.2.2, finCode u.2.1)
  have hπ : Measurable π := by
    have hst1 : Measurable fun u : MarkedSample ℓ (s + 1) n => stageState T s (n * ℓ.side) u.1 :=
      hst.comp measurable_fst
    have h1 : Measurable fun u : MarkedSample ℓ (s + 1) n => u.2.2.1 :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    have h2 : Measurable fun u : MarkedSample ℓ (s + 1) n => finCode u.2.2.2 :=
      (Measurable.of_discrete (f := fun d : BondSet (n * ℓ.side) => finCode d)).comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))
    have h3 : Measurable fun u : MarkedSample ℓ (s + 1) n => finCode u.2.1 :=
      (Measurable.of_discrete (f := fun d : BaseChoice ℓ.side n => finCode d)).comp
        (measurable_fst.comp measurable_snd)
    exact h1.prodMk ((measurable_fst.comp hst1).prodMk
      ((labelledSetCode_measurable.comp (measurable_snd.comp hst1)).prodMk (h2.prodMk h3)))
  have hfac : ∀ u u' : MarkedSample ℓ (s + 1) n, π u = π u' →
      F u.2.2.1 (topField ℓ s (n * ℓ.side) u.1) (stageState T s (n * ℓ.side) u.1).2.1
        (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1 =
      F u'.2.2.1 (topField ℓ s (n * ℓ.side) u'.1) (stageState T s (n * ℓ.side) u'.1).2.1
        (stageState T s (n * ℓ.side) u'.1).2.2 u'.2.2.2 u'.2.1 := by
    intro u u' h
    have e1 : u.2.2.1 = u'.2.2.1 :=
      congrArg (fun z : TorusField n × TorusField (n * ℓ.side) × (ℕ × ℝ) × ℕ × ℕ => z.1) h
    have e2 : (stageState T s (n * ℓ.side) u.1).1 = (stageState T s (n * ℓ.side) u'.1).1 :=
      congrArg (fun z : TorusField n × TorusField (n * ℓ.side) × (ℕ × ℝ) × ℕ × ℕ => z.2.1) h
    have e3 : (stageState T s (n * ℓ.side) u.1).2 = (stageState T s (n * ℓ.side) u'.1).2 :=
      labelledSetCode_injective
        (congrArg (fun z : TorusField n × TorusField (n * ℓ.side) × (ℕ × ℝ) × ℕ × ℕ => z.2.2.1) h)
    have e4 : u.2.2.2 = u'.2.2.2 :=
      finCode_injective
        (congrArg (fun z : TorusField n × TorusField (n * ℓ.side) × (ℕ × ℝ) × ℕ × ℕ => z.2.2.2.1) h)
    have e5 : u.2.1 = u'.2.1 :=
      finCode_injective
        (congrArg (fun z : TorusField n × TorusField (n * ℓ.side) × (ℕ × ℝ) × ℕ × ℕ => z.2.2.2.2) h)
    rw [← stageState_fst, ← stageState_fst]
    let Fc : TorusField n → TorusField (n * ℓ.side) →
        (Σ Y : Finset (TorusSite (n * ℓ.side)), (Y → (T.stage s).labels.Ω)) →
        Finset (TorusBond (n * ℓ.side)) → BaseChoice ℓ.side n → ℝ := fun V W q bad b => F V W q.1 q.2 bad b
    show Fc u.2.2.1 (stageState T s (n * ℓ.side) u.1).1 (stageState T s (n * ℓ.side) u.1).2 u.2.2.2 u.2.1 =
      Fc u'.2.2.1 (stageState T s (n * ℓ.side) u'.1).1 (stageState T s (n * ℓ.side) u'.1).2 u'.2.2.2 u'.2.1
    rw [e1, e2, e3, e4, e5]
  obtain ⟨h, hhm, hhe⟩ := exists_measurable_factor hπ hm hfac
  let clip : ℝ → ℝ := fun t => max (-|C|) (min |C| t)
  have hclip : ∀ t : ℝ, |t| ≤ C → clip t = t := fun t ht => by
    have h1 : t ≤ |C| := (le_abs_self t).trans (ht.trans (le_abs_self C))
    have h2 : -|C| ≤ t := by
      have := neg_abs_le t
      have h3 : |t| ≤ |C| := ht.trans (le_abs_self C)
      linarith
    show max (-|C|) (min |C| t) = t
    rw [min_eq_right h1, max_eq_right h2]
  have hbd : ∀ t : ℝ, |clip t| ≤ |C| := fun t => by
    have h0 := abs_nonneg C
    refine abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  let Fh : TorusField n → CaseFunction (T.stage s).toStepSetup n := fun V W Yt ωt bad b =>
    clip (h (V, W, labelledSetCode (Λ := (T.stage s).labels) ⟨Yt, ωt⟩, finCode bad, finCode b))
  have hFm : ∀ (Yt : Finset (TorusSite (n * ℓ.side))) (bad : Finset (TorusBond (n * ℓ.side))) (b : BaseChoice ℓ.side n),
      Measurable fun p : TorusField n × TorusField (n * ℓ.side) × (Yt → (T.stage s).labels.Ω) =>
        Fh p.1 p.2.1 Yt p.2.2 bad b := by
    intro Yt bad b
    have h1 : Measurable fun p : TorusField n × TorusField (n * ℓ.side) × (Yt → (T.stage s).labels.Ω) =>
        ((p.1, p.2.1, labelledSetCode (Λ := (T.stage s).labels) ⟨Yt, p.2.2⟩, finCode bad, finCode b) :
          TorusField n × TorusField (n * ℓ.side) × (ℕ × ℝ) × ℕ × ℕ) :=
      measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        ((labelledSetCode_measurable.comp ((measurable_sigmaMk Yt).comp (measurable_snd.comp measurable_snd))).prodMk
          measurable_const))
    have h2 := hhm.comp h1
    exact measurable_const.max (measurable_const.min h2)
  have hagree : ∀ (a : MarkedSample ℓ s (n * ℓ.side)) (d : StepOutcome ℓ n),
      caseValueAt Fh (stageState T s (n * ℓ.side) a) d = caseValueAt F (stageState T s (n * ℓ.side) a) d := by
    intro a d
    have h1 := hhe (a, d)
    have h2 := hC (a, d)
    rw [← stageState_fst] at h2
    show clip (h (d.2.1, (stageState T s (n * ℓ.side) a).1, labelledSetCode (stageState T s (n * ℓ.side) a).2,
      finCode d.2.2, finCode d.1)) = F d.2.1 (stageState T s (n * ℓ.side) a).1 (stageState T s (n * ℓ.side) a).2.1
        (stageState T s (n * ℓ.side) a).2.2 d.2.2 d.1
    have h3 : h (d.2.1, (stageState T s (n * ℓ.side) a).1, labelledSetCode (stageState T s (n * ℓ.side) a).2,
        finCode d.2.2, finCode d.1) = F d.2.1 (stageState T s (n * ℓ.side) a).1 (stageState T s (n * ℓ.side) a).2.1
        (stageState T s (n * ℓ.side) a).2.2 d.2.2 d.1 := by
      have h1' : h (d.2.1, (stageState T s (n * ℓ.side) a).1, labelledSetCode (stageState T s (n * ℓ.side) a).2,
          finCode d.2.2, finCode d.1) = F d.2.1 (topField ℓ s (n * ℓ.side) a) (stageState T s (n * ℓ.side) a).2.1
          (stageState T s (n * ℓ.side) a).2.2 d.2.2 d.1 := h1
      rw [← stageState_fst T s (n * ℓ.side) a] at h1'
      exact h1'
    rw [h3]
    exact hclip _ h2
  have hterm : ∀ (Cc : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState (T.stage s).toStepSetup n)
      (bad : Finset (TorusBond (n * ℓ.side))) (Yt : Finset (TorusSite (n * ℓ.side))) (b : BaseChoice ℓ.side n)
      (W : TorusField (n * ℓ.side)) (ν : q.unlabelled Yt → (T.stage s).labels.Ω),
      caseTerm (T.stage s).toStepSetup Cc V q (F V) bad Yt b W ν =
        caseTerm (T.stage s).toStepSetup Cc V q (Fh V) bad Yt b W ν := by
    intro Cc V q bad Yt b W ν
    unfold caseTerm
    by_cases ht : IsHullState (T.stage s).toStepSetup.params (T.stage s).toStepSetup.range
        (q.fieldWithStoredLinks W) Yt ∧
        coarseStateOf (T.stage s).toStepSetup Cc (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q
    · rw [if_pos ht, if_pos ht]
      by_cases hw : stepWeight (T.stage s).toStepSetup Cc V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = 0
      · rw [hw, mul_zero, mul_zero]
      · have hq : (T.stage s).labelWeight (n * ℓ.side) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) ≠ 0 := by
          intro h0
          apply hw
          unfold stepWeight
          have h0' : (T.stage s).toStepSetup.labelWeight (n * (T.stage s).toStepSetup.params.side)
              (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) = 0 := h0
          rw [h0']
          simp
        obtain ⟨a, ha⟩ := exists_sample_of_labelWeight_ne_zero T hs s (n * ℓ.side) _ _ _ hq
        have h1 := hagree a (b, V, bad)
        rw [ha] at h1
        have h2 : Fh V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b =
            F V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b := h1
        rw [h2]
    · rw [if_neg ht, if_neg ht]
  have hmean : ∀ (Cc : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState (T.stage s).toStepSetup n),
      caseMean (T.stage s).toStepSetup Cc V q (F V) = caseMean (T.stage s).toStepSetup Cc V q (Fh V) := by
    intro Cc V q
    unfold caseMean caseIntegral
    simp only [hterm Cc V q]
  have hlaw : stepJointLaw (T.stage s).toStepSetup n (markedSampleLaw T β s (n * ℓ.side))
      (stageState T s (n * ℓ.side)) = markedSampleLaw T β (s + 1) n := by
    have e : (fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
        ENNReal.ofReal (stepOutcomeDensity (T.stage s).toStepSetup (stageState T s (n * ℓ.side) u.1).1 u.2)) =
        fun u => ENNReal.ofReal (stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2) := by
      funext u
      rw [stageState_fst]
    unfold stepJointLaw
    rw [e]
    rfl
  have hfin : IsFiniteMeasure (stepJointLaw (T.stage s).toStepSetup n (markedSampleLaw T β s (n * ℓ.side))
      (stageState T s (n * ℓ.side))) := by
    rw [hlaw]
    exact ⟨lt_of_eq_of_lt hp1.measure_univ ENNReal.one_lt_top⟩
  have hhull : ∀ a : Finset (TorusSite n),
      MeasurableSet {V : TorusField n | hotCoreSites (T.stage s).toStepSetup V = a} := fun a =>
    measurableSet_hotCore hBo hadm T (T.stage s).toStepSetup rfl n a
  have key := hG (T.stage s).toStepSetup hR n hn hd (fun bad => hmark s n bad) hhull (MarkedSample ℓ s (n * ℓ.side))
    (markedSampleLaw T β s (n * ℓ.side)) (stageState T s (n * ℓ.side)) hst Z hZ0 hZt hD hfin Fh |C| hFm
    (fun V W Yt ωt bad b => hbd _)
  have eΦ : (fun u : MarkedSample ℓ (s + 1) n => F u.2.2.1 (topField ℓ s (n * ℓ.side) u.1)
      (stageState T s (n * ℓ.side) u.1).2.1 (stageState T s (n * ℓ.side) u.1).2.2 u.2.2.2 u.2.1) =
      fun u => caseValueAt Fh (stageState T s (n * ℓ.side) u.1) u.2 := by
    funext u
    rw [hagree, ← stageState_fst]
    rfl
  have eM : (fun u : MarkedSample ℓ (s + 1) n => caseMean (T.stage s).toStepSetup
      (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1 (stageState T (s + 1) n u).2 (F u.2.2.1)) =
      fun u => caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
        (stageState T (s + 1) n u).2 (Fh u.2.2.1) := funext fun u => hmean _ _ _
  rw [eΦ, eM, ← hlaw]
  exact key
end StepConditioning
end CaseMeans
open CaseMeans in
theorem conditionalMeanIsCaseMean (hG : conditionalMeanGivenCoarseState)
    (hDn : StageDensity.stageStateDensityStatement) (hBo : StageStatesMeasurableStatement)
    (hTw : TwoPointByTotalCovarianceStatement) (hCh : ChainIsProbabilityLaw) :
    conditionalMeanIsCaseMeanStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, hrt, h⟩ := hDn a ha
  refine ⟨L₀, rt₀, hrt, fun L hL hL₀ Tb hTa hTL hTd hTr => ?_⟩
  obtain ⟨y₀, h2⟩ := h L hL hL₀ Tb hTa hTL hTd hTr
  refine ⟨y₀, fun y hy hret hrow T β s n _ hstand hcut hmark hR hside hd F hm hb => ?_⟩
  have hadm : (Tb.stepParameters y).Admissible := hR.admissible
  have hden := h2 y hy hret hrow T β s (n * (Tb.stepParameters y).side) hstand hmark hside
  have hp0 := (hTw (Tb.stepParameters y) hadm hadm.depth_lt T hcut hmark β (fun _ => 0) s
    (n * (Tb.stepParameters y).side)).1
  have hp1 := (hTw (Tb.stepParameters y) hadm hadm.depth_lt T hcut hmark β (fun _ => 0) (s + 1) n).1
  have hpos := (hCh (Tb.stepParameters y) hadm hadm.depth_lt β (fun _ => 0) s (n * (Tb.stepParameters y).side)).2.1
  have hLpos : 0 < (Tb.stepParameters y).side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn : (Tb.stepParameters y).n₀ ≤ n := by
    have := hside.2
    rw [mul_comm] at this
    exact Nat.le_of_mul_le_mul_right this hLpos
  exact condExp_eq_caseMean_step hG hBo T β s n hstand.startsAtWilson hmark hR hn hd hp0 hp1
    (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top hden F hm hb
end YangMills.Construction.ResponseInTheExpansion
end
