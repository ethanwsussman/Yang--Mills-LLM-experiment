import YangMills.Construction.ClusterExpansionOfAStep.PlacesOfABlock
import YangMills.Construction.FreeEnergiesOfTheFlow.ScoresOverAStepDefs
import YangMills.Construction.LawInAState.MomentsOfTheCentredResponsesProof
import YangMills.Construction.ResponseInTheExpansion.MeanOfAProductOverSpins
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open StepSettings StepGas TorusLumps TorusFields WeightedResponses Dobrushin BlockPlaces
variable {R : StepSetup} {n : ℕ} [NeZero n] (A : ResponseSetup R) (G : GasGround R n)
open Classical in
def spinSiteScore (i : G.GasSpin) (y : TorusSite (n * R.params.side)) : G.SpinValue i → ℝ :=
  Sum.elim (fun _ => 0) fun w => if h : y ∈ i.1.2 then A.score (w.1.2.1 ⟨y, h⟩) else 0
variable {A G}
theorem spinSiteScore_nonneg (hs : ∀ w, 0 ≤ A.score w) (i : G.GasSpin) (y : TorusSite (n * R.params.side))
    (v : G.SpinValue i) : 0 ≤ spinSiteScore A G i y v := by
  classical
  rcases v with u | w
  · simp [spinSiteScore]
  · simp only [spinSiteScore, Sum.elim_inr]
    split_ifs
    · exact hs _
    · exact le_rfl
theorem measurable_spinSiteScore (hb : Measurable A.score) (i : G.GasSpin) (y : TorusSite (n * R.params.side)) :
    Measurable (spinSiteScore A G i y) := by
  classical
  unfold spinSiteScore
  refine Measurable.sumElim measurable_const ?_
  by_cases h : y ∈ i.1.2
  · simp only [h, dite_true]
    have h1 : Measurable fun w : G.SpinState i => (w.1 : SupportState i.1).2.1 :=
      measurable_fst.comp (measurable_snd.comp measurable_subtype_coe)
    exact hb.comp ((measurable_pi_apply _).comp h1)
  · simp only [h, dite_false]
    exact measurable_const
theorem siteScore_nonneg {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) {m : ℕ} (Y : Finset (TorusSite m))
    (ω : Y → Ω) (y : TorusSite m) : 0 ≤ siteScore s Y ω y := by apply _root_.YangMills.SharedProofs.p22275 <;> assumption
theorem siteScore_configSetting_le (hs : ∀ w, 0 ≤ A.score w) (σ : G.Config) (y : TorusSite (n * R.params.side)) :
    siteScore A.score (configSetting G σ).support (configSetting G σ).labelling y ≤
      recordedSiteScore A G y + ∑ i, spinSiteScore A G i y (σ i) := by
  classical
  set γ := G.familyOf σ with hγ
  have hsum : 0 ≤ ∑ i, spinSiteScore A G i y (σ i) :=
    Finset.sum_nonneg fun i _ => spinSiteScore_nonneg hs i y _
  have hrec : 0 ≤ recordedSiteScore A G y := siteScore_nonneg hs _ _ _
  have hY : (configSetting G σ).support = G.recordedSites ∪ γ.sites := rfl
  unfold siteScore
  by_cases hy : y ∈ (configSetting G σ).support
  · rw [dif_pos hy]
    by_cases hg : y ∈ γ.sites
    · have hl : (configSetting G σ).labelling ⟨y, hy⟩ = γ.labelAt hg := dif_pos hg
      rw [hl]
      obtain ⟨hθ, hyθ⟩ := (GasFamily.exists_of_mem_sites hg).choose_spec
      set θ := (GasFamily.exists_of_mem_sites hg).choose with hθdef
      have hsup : G.IsGasSupport θ := by
        by_contra hc
        have : γ θ = Sum.inl () := dif_neg hc
        simp [GasFamily.Occupies, this] at hθ
      rcases hv : σ ⟨θ, hsup⟩ with u | w
      · exfalso
        have : γ θ = Sum.inl () := by
          show G.familyOf σ θ = _
          unfold GasGround.familyOf
          rw [dif_pos hsup]
          simp [hv]
        simp [GasFamily.Occupies, this] at hθ
      · have hγθ : γ θ = Sum.inr w.1 := by
          show G.familyOf σ θ = _
          unfold GasGround.familyOf
          rw [dif_pos hsup]
          simp [hv]
        have hstate : γ.state hθ = w.1 := by
          unfold GasFamily.state
          simp [hγθ]
        have hlab : γ.labelAt hg = (w.1 : SupportState θ).2.1 ⟨y, hyθ⟩ := by
          show (γ.state (GasFamily.exists_of_mem_sites hg).choose_spec.1).2.1
            ⟨y, (GasFamily.exists_of_mem_sites hg).choose_spec.2⟩ = _
          rw [hstate]
        have hterm : spinSiteScore A G ⟨θ, hsup⟩ y (σ ⟨θ, hsup⟩) = A.score (γ.labelAt hg) := by
          rw [hv, hlab]
          simp [spinSiteScore, hyθ]
        have hle := Finset.single_le_sum (f := fun i => spinSiteScore A G i y (σ i))
          (fun i _ => spinSiteScore_nonneg hs i y _) (Finset.mem_univ (⟨θ, hsup⟩ : G.GasSpin))
        rw [hterm] at hle
        linarith
    · have hm : y ∈ G.recordedSites := by
        rw [hY] at hy
        exact (Finset.mem_union.mp hy).resolve_right hg
      have hl : (configSetting G σ).labelling ⟨y, hy⟩ = G.recordedLabel ⟨y, hm⟩ := dif_neg hg
      have hrec' : recordedSiteScore A G y = A.score (G.recordedLabel ⟨y, hm⟩) := by
        unfold recordedSiteScore siteScore
        rw [dif_pos hm]
      rw [hl, ← hrec']
      linarith
  · rw [dif_neg hy]
    linarith
theorem sum_recordedSiteScore_le_parentBlocks (hs : ∀ w, 0 ≤ A.score w) (h₁ : 0 ≤ A.responseParams.s₁)
    (S : Finset (TorusSite (n * R.params.side))) :
    ∑ y ∈ S, recordedSiteScore A G y ≤ ∑ Y ∈ parentBlocks S, coarseSiteScore A G.state Y := by
  classical
  have hmaps : ∀ y ∈ S, parentBlock R.params.side y ∈ parentBlocks S := fun y hy => Finset.mem_image_of_mem _ hy
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun Y _ => ?_
  have hnon : 0 ≤ coarseSiteScore A G.state Y := siteScore_nonneg (fun w => by
    rcases w with u | rec
    · exact h₁
    · show 0 ≤ coarseLabelScore A.responseParams.s₁ A.score (Sum.inr rec)
      simp only [coarseLabelScore]
      refine add_nonneg h₁ (Finset.sum_nonneg fun o _ => ?_)
      rcases rec.siteLabel o with u | a
      · simp
      · exact hs a) _ _ _
  rcases hrec : G.state.markAt Y with _ | rec
  · refine le_trans (le_of_eq ?_) hnon
    refine Finset.sum_eq_zero fun y hy => ?_
    have hb := (Finset.mem_filter.mp hy).2
    unfold recordedSiteScore siteScore
    rw [dif_neg]
    intro hm
    have h1 := (Finset.mem_filter.mp hm).2
    have h2 : G.state.labelAt y = Sum.inl () := by
      unfold CoarseState.labelAt
      rw [hb, hrec]
    simp [h2] at h1
  · have hmem : Y ∈ G.state.1 := by
      by_contra hc
      unfold CoarseState.markAt at hrec
      rw [dif_neg hc] at hrec
      exact absurd hrec (by simp)
    have hq : G.state.2 ⟨Y, hmem⟩ = Sum.inr rec := by
      unfold CoarseState.markAt at hrec
      rw [dif_pos hmem] at hrec
      rcases hv : G.state.2 ⟨Y, hmem⟩ with u | rec'
      · simp [hv] at hrec
      · simp only [hv, Option.some.injEq] at hrec
        rw [hrec]
    have hval : coarseSiteScore A G.state Y =
        A.responseParams.s₁ + ∑ o : BlockOffset R.params.side, Sum.elim (fun _ => 0) A.score (rec.siteLabel o) := by
      unfold coarseSiteScore siteScore
      rw [dif_pos hmem, hq]
      rfl
    have hterm : ∀ y ∈ S.filter (fun y => parentBlock R.params.side y = Y), recordedSiteScore A G y =
        Sum.elim (fun _ => 0) A.score (rec.siteLabel (siteOffset y)) := by
      intro y hy
      have hb := (Finset.mem_filter.mp hy).2
      have hlab : G.state.labelAt y = rec.siteLabel (siteOffset y) := by
        unfold CoarseState.labelAt
        rw [hb, hrec]
      unfold recordedSiteScore siteScore
      by_cases hm : y ∈ G.recordedSites
      · rw [dif_pos hm]
        have h1 := (Finset.mem_filter.mp hm).2
        have e : G.recordedLabel ⟨y, hm⟩ = (G.state.labelAt y).getRight h1 := rfl
        have key : ∀ (x : WithNone R.labels.Ω) (h : x.isRight = true),
            A.score (Sum.getRight x h) = Sum.elim (fun _ => 0) A.score x := by
          rintro (u | a) h
          · simp at h
          · rfl
        rw [e, key _ h1, hlab]
      · rw [dif_neg hm, ← hlab]
        rcases hl : G.state.labelAt y with u | a
        · rfl
        · exfalso
          apply hm
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hl]⟩
    rw [Finset.sum_congr rfl hterm, hval]
    have hinj : Set.InjOn (fun y : TorusSite (n * R.params.side) => (siteOffset y : BlockOffset R.params.side))
        (S.filter (fun y => parentBlock R.params.side y = Y) : Finset _) := by
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      rw [← blockSite_parentBlock_siteOffset a, ← blockSite_parentBlock_siteOffset b, ha', hb']
      exact congrArg _ hab
    have hsum : ∑ y ∈ S.filter (fun y => parentBlock R.params.side y = Y),
        Sum.elim (fun _ => (0 : ℝ)) A.score (rec.siteLabel (siteOffset y)) ≤
        ∑ o : BlockOffset R.params.side, Sum.elim (fun _ => (0 : ℝ)) A.score (rec.siteLabel o) := by
      rw [← Finset.sum_image (f := fun o => Sum.elim (fun _ => (0 : ℝ)) A.score (rec.siteLabel o)) hinj]
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun o _ _ => ?_
      rcases rec.siteLabel o with u | a
      · simp
      · exact hs a
    linarith
theorem weightedMean_const_le {m : ℕ} {free : Finset (TorusBond m)} (d : FreeCoords free → ℝ) {c : ℝ}
    (hc : 0 ≤ c) : weightedMean d (fun _ => c) ≤ c := by
  unfold weightedMean
  rw [integral_const_mul, mul_div_assoc]
  by_cases h : ∫ η, d η = 0
  · simp [h, hc]
  · rw [div_self h, mul_one]
theorem weightedMean_const_nonneg {m : ℕ} {free : Finset (TorusBond m)} (d : FreeCoords free → ℝ) {c : ℝ}
    (hc : 0 ≤ c) : 0 ≤ weightedMean d (fun _ => c) := by
  unfold weightedMean
  rw [integral_const_mul, mul_div_assoc]
  by_cases h : ∫ η, d η = 0
  · simp [h]
  · rw [div_self h, mul_one]
    exact hc
theorem expectation_le_mul_prod (hP : MeanOfProductStatement) {z : G.GasSpin → ℝ}
    (hW : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight z) (g : ∀ i, G.SpinValue i → ℝ)
    (e : G.GasSpin → ℝ) (hm : ∀ i, Measurable (g i)) (h1 : ∀ i s, 1 ≤ g i s)
    (ha : ∀ i, g i (G.pairConstraint.vacant i) = 1) (he : ∀ i, 0 ≤ e i)
    (hx : G.pairConstraint.HasSmallExcess (G.referenceMeasure ∅) G.weight g e) {H : G.Config → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hH0 : ∀ σ, 0 ≤ H σ) (hH : ∀ σ, H σ ≤ c * ∏ i, g i (σ i)) :
    G.expectation ∅ H ≤ c * ∏ i, (1 + e i) := by
  have hprod : 0 ≤ ∏ i, (1 + e i) := Finset.prod_nonneg fun i _ => by linarith [he i]
  have key := hP G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasure ∅) G.weight z hW g e hm h1 ha he hx
  unfold GasGround.expectation
  have hlaw : G.gibbsLaw ∅ = G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight := rfl
  rw [hlaw]
  by_cases hi : Integrable H (G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight)
  · have e1 := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hH0)
    have e2 : ∫⁻ σ, ENNReal.ofReal (H σ) ∂(G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight) ≤
        ∫⁻ σ, ENNReal.ofReal c * ∏ i, ENNReal.ofReal (g i (σ i))
          ∂(G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight) := by
      refine lintegral_mono fun σ => ?_
      have hg0 : ∀ i ∈ Finset.univ, 0 ≤ g i (σ i) := fun i _ => le_trans zero_le_one (h1 i _)
      rw [← ENNReal.ofReal_prod_of_nonneg hg0, ← ENNReal.ofReal_mul hc]
      exact ENNReal.ofReal_le_ofReal (hH σ)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at e2
    have e3 : ENNReal.ofReal c * ∫⁻ σ, ∏ i, ENNReal.ofReal (g i (σ i))
          ∂(G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight) ≤
        ENNReal.ofReal c * ENNReal.ofReal (∏ i, (1 + e i)) := by gcongr
    rw [← ENNReal.ofReal_mul hc] at e3
    have e4 : ENNReal.ofReal (∫ σ, H σ ∂(G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight)) ≤
        ENNReal.ofReal (c * ∏ i, (1 + e i)) := by
      rw [e1]
      exact e2.trans e3
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc hprod)).mp e4
  · rw [integral_undef hi]
    exact mul_nonneg hc hprod
theorem sum_biUnion_le_sum_sum {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (s : Finset ι) (t : ι → Finset κ)
    (f : κ → ℝ) (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    have h0 : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x := Finset.sum_nonneg fun x _ => hf x
    linarith
theorem sum_spin_weight_le_card_parentBlocks_mul {G : GasGround R n} (w : GasSupport R n → ℝ) (hc : ∀ θ, 0 ≤ w θ)
    {b : ℝ} (hcount : ∀ Y : TorusSite n, ∑ θ ∈ supportsAtBlock R.params.side R.range Y, w θ ≤ b)
    (S : Finset (TorusSite (n * R.params.side))) :
    (open Classical in ∑ i : G.GasSpin, if (S ∩ i.1.2).Nonempty then w i.1 else 0) ≤
      ((parentBlocks S).card : ℝ) * b := by
  classical
  have hinj : Function.Injective (fun i : G.GasSpin => i.1) := Subtype.val_injective
  set U : Finset (GasSupport R n) :=
    (parentBlocks S).biUnion fun Y => supportsAtBlock R.params.side R.range Y with hU
  have h1 : (∑ i : G.GasSpin, if (S ∩ i.1.2).Nonempty then w i.1 else 0) ≤ ∑ θ ∈ U, w θ := by
    rw [← Finset.sum_filter]
    have hsub : ((Finset.univ.filter fun i : G.GasSpin => (S ∩ i.1.2).Nonempty).image fun i => i.1) ⊆ U := by
      intro θ hθ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hθ
      obtain ⟨z, hz⟩ := (Finset.mem_filter.mp hi).2
      have hzS := (Finset.mem_inter.mp hz).1
      have hzθ := (Finset.mem_inter.mp hz).2
      refine Finset.mem_biUnion.mpr ⟨parentBlock R.params.side z, Finset.mem_image_of_mem _ hzS, ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2.isCluster, ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, ?_⟩
      refine Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr rfl⟩, ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, ?_, ?_⟩
      · exact Finset.mem_union_right _ hzθ
      · simp [supDist]
    calc _ = ∑ θ ∈ (Finset.univ.filter fun i : G.GasSpin => (S ∩ i.1.2).Nonempty).image (fun i => i.1), w θ := by
          rw [Finset.sum_image fun a _ b _ h => hinj h]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun θ _ _ => hc θ
  refine h1.trans ?_
  calc ∑ θ ∈ U, w θ ≤ ∑ Y ∈ parentBlocks S, ∑ θ ∈ supportsAtBlock R.params.side R.range Y, w θ :=
        sum_biUnion_le_sum_sum _ _ _ hc
    _ ≤ ∑ _Y ∈ parentBlocks S, b := Finset.sum_le_sum fun Y _ => hcount Y
    _ = _ := by simp
end YangMills.Construction.FreeEnergies
end
