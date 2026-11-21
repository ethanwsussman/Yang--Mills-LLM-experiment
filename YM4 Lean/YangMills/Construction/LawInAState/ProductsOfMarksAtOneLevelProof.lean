import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.LawInAState.MomentsOfTheCentredResponsesProof
import YangMills.Construction.LawInAState.ObservablesOnTheLeastTorusAreIntegrable
import YangMills.Construction.LawInAState.WeightsOfMarksOnTheLeastTorus
import YangMills.Construction.LawInAState.WilsonsLawOnTheLeastTorusInTheExpansion
import YangMills.Construction.ResponseInTheExpansion.ScoresMoveNoCorrelation
import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABond
import YangMills.Construction.TransfersOffTheWalk.ManyLevelsOfSupportsApart
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace YangMills.Construction.StateLaws
open TorusFields TorusLumps WeightedResponses RenormalizationStepParameters StepCosts BoxResponses FreeEnergies TransfersOffTheWalk
open ResponseInTheExpansion ClusterExpansionOfAStep
section Abstract
variable {Ω ι : Type} [MeasurableSpace Ω] {μ : Measure Ω} [DecidableEq ι]
private theorem integral_prod_add_sub_le (I : Finset ι) (a b : ι → Ω → ℝ) (g : ι → ℝ) (E : Finset ι → ℝ)
    (ha : ∀ J ∈ I.powerset, Integrable (fun w => ∏ i ∈ J, a i w) μ)
    (hb : ∀ J ∈ I.powerset, Integrable (fun w => ∏ i ∈ J, b i w) μ)
    (hE : ∀ J ∈ I.powerset, |∫ w, ∏ i ∈ J, a i w ∂μ - ∫ w, ∏ i ∈ J, b i w ∂μ| ≤ E J) :
    |∫ w, ∏ i ∈ I, (a i w + g i) ∂μ - ∫ w, ∏ i ∈ I, (b i w + g i) ∂μ| ≤
      ∑ J ∈ I.powerset, (∏ i ∈ I \ J, |g i|) * E J := by
  have hexp : ∀ c : ι → Ω → ℝ, (∀ J ∈ I.powerset, Integrable (fun w => ∏ i ∈ J, c i w) μ) →
      ∫ w, ∏ i ∈ I, (c i w + g i) ∂μ = ∑ J ∈ I.powerset, (∏ i ∈ I \ J, g i) * ∫ w, ∏ i ∈ J, c i w ∂μ := by
    intro c hc
    have h1 : ∀ w, ∏ i ∈ I, (c i w + g i) = ∑ J ∈ I.powerset, (∏ i ∈ I \ J, g i) * ∏ i ∈ J, c i w := by
      intro w
      rw [Finset.prod_add]
      exact Finset.sum_congr rfl fun J _ => mul_comm _ _
    simp only [h1]
    rw [integral_finsetSum _ fun J hJ => (hc J hJ).const_mul _]
    exact Finset.sum_congr rfl fun J _ => integral_const_mul _ _
  rw [hexp a ha, hexp b hb, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun J hJ => ?_)
  rw [← mul_sub, abs_mul, Finset.abs_prod]
  exact mul_le_mul_of_nonneg_left (hE J hJ) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
end Abstract
section Marks
variable {ℓ : StepParameters}
private def markScoreWeights (ℓ : StepParameters) (al : ℕ → ℝ) {m : ℕ} : (s n : ℕ) → [NeZero n] →
    (Fin m → PlaquetteWeight (fineSide ℓ.side s n)) → ScoreWeights ℓ m s n
  | 0, _, _, _ => ()
  | s + 1, n, _, h => (markScoreWeights ℓ al s (n * ℓ.side) h,
      fun i c => ℓ.coupling * al s * bondBlockMean ℓ.side (s + 1) n (h i) c)
private theorem chainMark_eq_add (x al : ℕ → ℝ) {m : ℕ} : (s n : ℕ) → [NeZero n] →
    (h : Fin m → PlaquetteWeight (fineSide ℓ.side s n)) → (j : Fin m) → (u : ChainSample ℓ s n) →
    chainMark ℓ x al s n (h j) u = curvatureObservable (h j) (initialField ℓ s n u) +
      weightedScoreSum ℓ x s n (markScoreWeights ℓ al s n h) j u
  | 0, _, _, _, _, _ => by
    simp [chainMark, weightedScoreSum, initialField]
  | s + 1, n, _, h, j, u => by
    have ih := chainMark_eq_add x al s (n * ℓ.side) h j u.1
    show chainMark ℓ x al s (n * ℓ.side) (h j) u.1 + _ = curvatureObservable (h j) (initialField ℓ s (n * ℓ.side) u.1) +
      (weightedScoreSum ℓ x s (n * ℓ.side) (markScoreWeights ℓ al s (n * ℓ.side) h) j u.1 + _)
    rw [ih, add_assoc]
    rfl
private theorem mem_weightSupportSites_of_blockMean_ne_zero (L : ℕ) [NeZero L] : ∀ (t n : ℕ) [NeZero n] (y : TorusSite n)
    (h : PlaquetteWeight (fineSide L t n)), blockMean L t n y h ≠ 0 → y ∈ weightSupportSites L t n h := by
  intro t
  induction t with
  | zero =>
    intro n _ y h hne
    have hsum : ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * h p ≠ 0 := by
      intro h0
      apply hne
      show (1 / 24 : ℝ) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * h p = 0
      rw [h0, mul_zero]
    obtain ⟨p, hp, hpn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    have hc : vertexMultiplicity y p ≠ 0 := left_ne_zero_of_mul hpn
    have hh : h p ≠ 0 := right_ne_zero_of_mul hpn
    have hmem : y ∈ plaquetteVertices p.1 p.2.1 p.2.2 := by
      by_contra hy
      apply hc
      simp [vertexMultiplicity, List.count_eq_zero_of_not_mem hy]
    simp only [weightSupportSites, Finset.mem_filter, Finset.mem_univ, true_and]
    have hord : p.2.1 < p.2.2 := by
      have := hp
      simp only [plaquettesIn, Finset.mem_filter] at this
      exact this.2.1
    refine ⟨p, ⟨hord, y, hmem, ?_⟩, hh⟩
    show y ∈ ({y} : Finset (TorusSite n))
    exact Finset.mem_singleton_self _
  | succ t ih =>
    intro n _ Y h hne
    have hsum : ∑ y ∈ sitesInBlocks L {Y}, blockMean L t (n * L) y h ≠ 0 := by
      intro h0
      apply hne
      show ((L : ℝ) ^ 4)⁻¹ * ∑ y ∈ sitesInBlocks L {Y}, blockMean L t (n * L) y h = 0
      rw [h0, mul_zero]
    obtain ⟨y, hy, hyn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    have h1 := ih (n * L) y h hyn
    simp only [weightSupportSites, Finset.mem_filter, Finset.mem_univ, true_and] at h1 ⊢
    obtain ⟨p, ⟨hord, c, hc, hcb⟩, hp⟩ := h1
    refine ⟨p, ⟨hord, c, hc, ?_⟩, hp⟩
    rw [fineBlock]
    exact Finset.mem_biUnion.mpr ⟨y, hy, hcb⟩
abbrev _root_.YangMills.SharedProofs.p53316 := @mem_weightSupportSites_of_blockMean_ne_zero
private theorem supDist_unitStep_le_one {n : ℕ} [NeZero n] (c : TorusBond n) :
    supDist c.1 (c.1 + unitStep n c.2) ≤ 1 := by
  have h : unitStep n c.2 = siteOfInt (Pi.single c.2 1) := by
    funext a
    by_cases ha : a = c.2
    · subst ha
      simp [unitStep, siteOfInt]
    · simp [unitStep, siteOfInt, Pi.single_apply, ha]
  rw [h]
  refine supDist_add_siteOfInt_le _ _ _ fun a => ?_
  by_cases ha : a = c.2
  · subst ha
    simp
  · simp [Pi.single_apply, ha]
abbrev _root_.YangMills.SharedProofs.p29700 := @supDist_unitStep_le_one
private theorem exists_endpoint_of_bondBlockMean_ne_zero (L t n : ℕ) [NeZero L] [NeZero n]
    (h : PlaquetteWeight (fineSide L t n)) (c : TorusBond n) (hc : bondBlockMean L t n h c ≠ 0) :
    ∃ y : TorusSite n, (y = c.1 ∨ y = c.1 + unitStep n c.2) ∧ y ∈ weightSupportSites L t n h := by
  by_cases h1 : blockMean L t n c.1 h = 0
  · have h2 : blockMean L t n (c.1 + unitStep n c.2) h ≠ 0 := by
      intro h2
      apply hc
      unfold bondBlockMean
      rw [h1, h2]
      simp
    exact ⟨_, Or.inr rfl, mem_weightSupportSites_of_blockMean_ne_zero L t n _ h h2⟩
  · exact ⟨_, Or.inl rfl, mem_weightSupportSites_of_blockMean_ne_zero L t n _ h h1⟩
private theorem disjoint_of_separated (al x D : ℕ → ℝ) {m : ℕ} : (s n : ℕ) → [NeZero n] →
    (h : Fin m → PlaquetteWeight (fineSide ℓ.side s n)) →
    SeparatedAlongTower ℓ x D s n h → ScoreWeights.Disjoint s n (markScoreWeights ℓ al s n h)
  | 0, _, _, _, _ => trivial
  | s + 1, n, _, h, ⟨⟨_, h8, hap⟩, hrest⟩ => by
    refine ⟨disjoint_of_separated al x D s (n * ℓ.side) h hrest, fun c i i' hii => ?_⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have h1' : bondBlockMean ℓ.side (s + 1) n (h i) c ≠ 0 := right_ne_zero_of_mul h1
    have h2' : bondBlockMean ℓ.side (s + 1) n (h i') c ≠ 0 := right_ne_zero_of_mul h2
    obtain ⟨y, hy, hyA⟩ := exists_endpoint_of_bondBlockMean_ne_zero _ _ _ _ c h1'
    obtain ⟨y', hy', hyA'⟩ := exists_endpoint_of_bondBlockMean_ne_zero _ _ _ _ c h2'
    have hfar := hap i i' hii y hyA y' hyA'
    have hnear : supDist y y' ≤ 1 := by
      rcases hy with rfl | rfl <;> rcases hy' with rfl | rfl
      · simp [supDist_self]
      · exact supDist_unitStep_le_one c
      · rw [supDist_comm]
        exact supDist_unitStep_le_one c
      · simp [supDist_self]
    have : (supDist y y' : ℝ) ≤ 1 := by exact_mod_cast hnear
    linarith
private theorem separated_comp (x D : ℕ → ℝ) {m m' : ℕ} (idx : Fin m' → Fin m) (hidx : Function.Injective idx) :
    (s n : ℕ) → [NeZero n] → (h : Fin m → PlaquetteWeight (fineSide ℓ.side s n)) →
    SeparatedAlongTower ℓ x D s n h → SeparatedAlongTower ℓ x D s n (fun j => h (idx j))
  | 0, _, _, _, _ => trivial
  | s + 1, n, _, h, ⟨⟨h0, h8, hap⟩, hrest⟩ =>
    ⟨⟨h0, h8, fun i j hij => hap (idx i) (idx j) fun e => hij (hidx e)⟩,
      separated_comp x D idx hidx s (n * ℓ.side) h hrest⟩
end Marks
section Bounded
variable {Ω ι : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
private theorem ae_bounded_prod (S : Finset ι) (f : ι → Ω → ℝ) (hb : ∀ i ∈ S, ∃ C : ℝ, ∀ᵐ w ∂μ, |f i w| ≤ C) :
    ∃ C : ℝ, ∀ᵐ w ∂μ, |∏ i ∈ S, f i w| ≤ C := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨1, Eventually.of_forall fun w => by simp⟩
  | insert a S ha ih =>
    obtain ⟨C₁, h₁⟩ := hb a (Finset.mem_insert_self _ _)
    obtain ⟨C₂, h₂⟩ := ih fun i hi => hb i (Finset.mem_insert_of_mem hi)
    refine ⟨|C₁| * |C₂|, ?_⟩
    filter_upwards [h₁, h₂] with w hw₁ hw₂
    rw [Finset.prod_insert ha, abs_mul]
    exact mul_le_mul (hw₁.trans (le_abs_self _)) (hw₂.trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)
private theorem integrable_prod_of_bounded (S : Finset ι) (f : ι → Ω → ℝ) (hm : ∀ i ∈ S, AEStronglyMeasurable (f i) μ)
    (hb : ∀ i ∈ S, ∃ C : ℝ, ∀ᵐ w ∂μ, |f i w| ≤ C) : Integrable (fun w => ∏ i ∈ S, f i w) μ := by
  obtain ⟨C, hC⟩ := ae_bounded_prod S f hb
  exact Integrable.of_bound (Finset.aestronglyMeasurable_fun_prod _ hm) C (hC.mono fun w h => by rwa [Real.norm_eq_abs])
end Bounded
section Chain
variable {ℓ : StepParameters}
private theorem continuous_curvatureObservable {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    Continuous (curvatureObservable h) := by
  unfold curvatureObservable
  exact continuous_finsetSum _ fun p _ => continuous_const.mul (continuous_plaquetteEnergy p.1 p.2.1 p.2.2)
abbrev _root_.YangMills.SharedProofs.p1196 := @continuous_curvatureObservable
private theorem bounded_curvatureObservable {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    ∃ C : ℝ, ∀ W, |curvatureObservable h W| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (continuous_curvatureObservable h).continuousOn
  exact ⟨C, fun W => by simpa using hC W (Set.mem_univ _)⟩
private theorem initialField_forgetMarks (ℓ : StepParameters) : (s n : ℕ) → (u : MarkedSample ℓ s n) →
    initialField ℓ s n (forgetMarks ℓ s n u) = bottomField ℓ s n u
  | 0, _, _ => rfl
  | s + 1, n, u => initialField_forgetMarks ℓ s (n * ℓ.side) u.1
private theorem measurable_finalField (ℓ : StepParameters) : (s n : ℕ) → Measurable (finalField ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => measurable_snd.comp measurable_snd
private theorem measurable_initialField (ℓ : StepParameters) : (s n : ℕ) → Measurable (initialField ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => (measurable_initialField ℓ s (n * ℓ.side)).comp measurable_fst
private theorem measurable_forgetMarks (s : ℕ) : ∀ n : ℕ, Measurable (forgetMarks ℓ s n) := by
  induction s with
  | zero =>
    intro n
    exact measurable_id
  | succ s ih =>
    intro n
    exact show Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
        ((forgetMarks ℓ s (n * ℓ.side) u.1, u.2.1, u.2.2.1) :
          ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n) from
      ((ih (n * ℓ.side)).comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_snd).prodMk
          (measurable_fst.comp (measurable_snd.comp measurable_snd)))
abbrev _root_.YangMills.SharedProofs.p23598 := @measurable_forgetMarks
private theorem measurable_bondScore_sample (hT : BondScoreProperties) (hfit : ℓ.Admissible) (y : ℝ) (s n : ℕ)
    [NeZero n] (c : TorusBond n) :
    Measurable fun u : ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n =>
      bondScore ℓ y (finalField ℓ s (n * ℓ.side) u.1) u.2.2 u.2.1 c := by
  classical
  have hsum : (fun u : ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n =>
      bondScore ℓ y (finalField ℓ s (n * ℓ.side) u.1) u.2.2 u.2.1 c) = fun u =>
      ∑ b : BaseChoice ℓ.side n, if u.2.1 = b then
        bondScore ℓ y (finalField ℓ s (n * ℓ.side) u.1) u.2.2 b c else 0 := by
    funext u
    simp
  rw [hsum]
  refine Finset.measurable_sum _ fun b _ => ?_
  have hset : MeasurableSet {u : ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n | u.2.1 = b} :=
    (measurable_fst.comp measurable_snd) (show MeasurableSet ({b} : Set (BaseChoice ℓ.side n)) from trivial)
  have h1 : Measurable fun u : ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n =>
      (finalField ℓ s (n * ℓ.side) u.1, u.2.2) :=
    ((measurable_finalField ℓ s (n * ℓ.side)).comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  have h2 := (hT ℓ hfit y n b c).2.2.2.2.comp h1
  exact Measurable.ite hset h2 measurable_const
abbrev _root_.YangMills.SharedProofs.p68546 := @measurable_bondScore_sample
private theorem measurable_weightedScoreSum (hT : BondScoreProperties) (hfit : ℓ.Admissible) (x : ℕ → ℝ) {m : ℕ} :
    (s n : ℕ) → [NeZero n] → (w : ScoreWeights ℓ m s n) → (i : Fin m) →
      Measurable (weightedScoreSum ℓ x s n w i)
  | 0, _, _, _, _ => measurable_const
  | s + 1, n, _, w, i =>
    ((measurable_weightedScoreSum hT hfit x s (n * ℓ.side) w.1 i).comp measurable_fst).add
      (Finset.measurable_sum _ fun c _ =>
        (measurable_bondScore_sample hT hfit (x s) s n c).const_mul (w.2 i c))
private theorem bounded_weightedScoreSum (hT : BondScoreProperties) (hfit : ℓ.Admissible) (x : ℕ → ℝ) {m : ℕ} :
    (s n : ℕ) → [NeZero n] → (w : ScoreWeights ℓ m s n) → (i : Fin m) →
      ∃ C : ℝ, ∀ u, |weightedScoreSum ℓ x s n w i u| ≤ C
  | 0, _, _, _, _ => ⟨0, fun u => by simp [weightedScoreSum]⟩
  | s + 1, n, _, w, i => by
    obtain ⟨C, hC⟩ := bounded_weightedScoreSum hT hfit x s (n * ℓ.side) w.1 i
    refine ⟨C + ∑ c : TorusBond n, |w.2 i c| * 2, fun u => ?_⟩
    show |weightedScoreSum ℓ x s (n * ℓ.side) w.1 i u.1 + ∑ c : TorusBond n, w.2 i c *
      bondScore ℓ (x s) (finalField ℓ s (n * ℓ.side) u.1) u.2.2 u.2.1 c| ≤ _
    refine (abs_add_le _ _).trans (add_le_add (hC _) ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun c _ => ?_)))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hT ℓ hfit (x s) n u.2.1 c).2.2.1 _ _) (abs_nonneg _)
private theorem chainMark_measurable_bounded (hT : BondScoreProperties) (hfit : ℓ.Admissible) (x al : ℕ → ℝ)
    (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side s n)) :
    Measurable (fun u => chainMark ℓ x al s n h (forgetMarks ℓ s n u)) ∧
      ∃ C : ℝ, ∀ u, |chainMark ℓ x al s n h (forgetMarks ℓ s n u)| ≤ C := by
  have he : ∀ v, chainMark ℓ x al s n h v = curvatureObservable h (initialField ℓ s n v) +
      weightedScoreSum ℓ x s n (markScoreWeights ℓ al s n (fun _ : Fin 1 => h)) 0 v := fun v =>
    chainMark_eq_add x al s n (fun _ : Fin 1 => h) 0 v
  constructor
  · have h1 : Measurable (chainMark ℓ x al s n h) := by
      rw [show chainMark ℓ x al s n h = _ from funext he]
      exact ((continuous_curvatureObservable h).measurable.comp (measurable_initialField ℓ s n)).add
        (measurable_weightedScoreSum hT hfit x s n _ 0)
    exact h1.comp (measurable_forgetMarks s n)
  · obtain ⟨C₁, h₁⟩ := bounded_curvatureObservable h
    obtain ⟨C₂, h₂⟩ := bounded_weightedScoreSum hT hfit x s n (markScoreWeights ℓ al s n (fun _ : Fin 1 => h)) 0
    refine ⟨C₁ + C₂, fun u => ?_⟩
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add (h₁ _) (h₂ _))
private theorem integral_prod_curvature_eq_chainMark (hS : ScoresPreserveCorrelations)
    (hT : TwoPointByTotalCovarianceStatement) (hSc : BondScoreProperties) (hf : ℓ.Admissible)
    (T : WeightedResponses.StageTower ℓ) (hcut : ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn)
    (hcoin : T.MarksMeasurable) (β : ℝ) (al x D : ℕ → ℝ) (s n : ℕ) [NeZero n] {p : ℕ}
    (h : Fin p → PlaquetteWeight (fineSide ℓ.side s n)) (hap : SeparatedAlongTower ℓ x D s n h) (κ : Fin p → ℝ)
    (B : Finset (Fin p)) :
    ∫ u, ∏ i ∈ B, (curvatureObservable (h i) (bottomField ℓ s n u) - κ i) ∂(markedSampleLaw T β s n) =
      ∫ u, ∏ i ∈ B, (chainMark ℓ (fun j => (T.stage j).coupling) al s n (h i) (forgetMarks ℓ s n u) - κ i)
        ∂(markedSampleLaw T β s n) := by
  have hL := hf.depth_lt
  obtain ⟨-, -, -, hchain, -, -⟩ := hT ℓ hf hL T hcut hcoin β al s n
  have hmw := measurable_forgetMarks (ℓ := ℓ) s n
  let e : Fin B.card ≃ {i // i ∈ B} := B.equivFin.symm
  let idx : Fin B.card → Fin p := fun j => (e j).1
  have hidx : Function.Injective idx := fun a b h => e.injective (Subtype.ext h)
  let hq : Fin B.card → PlaquetteWeight (fineSide ℓ.side s n) := fun j => h (idx j)
  let w := markScoreWeights ℓ al s n hq
  have hsep : ScoreWeights.Disjoint s n w :=
    disjoint_of_separated al x D s n hq (separated_comp x D idx hidx s n h hap)
  let X : Fin B.card → TorusField (fineSide ℓ.side s n) → ℝ := fun j => curvatureObservable (hq j)
  have hXm : ∀ j, Measurable (X j) := fun j => (continuous_curvatureObservable (hq j)).measurable
  have hXb : ∀ j, ∃ C : ℝ, ∀ W, |X j W| ≤ C := fun j => bounded_curvatureObservable (hq j)
  have hmain := hS ℓ hf hL β (fun j => (T.stage j).coupling) s n B.card X w (fun j => κ (idx j)) hXm hXb hsep
  have hprod : ∀ g : Fin p → ℝ, ∏ i ∈ B, g i = ∏ j : Fin B.card, g (idx j) := by
    intro g
    rw [← Finset.prod_coe_sort B g]
    exact (Equiv.prod_comp e fun i : {i // i ∈ B} => g i.1).symm
  have hxm : ∀ j, Measurable fun v : ChainSample ℓ s n => X j (initialField ℓ s n v) := fun j =>
    (hXm j).comp (measurable_initialField ℓ _ _)
  have hF₀ : Measurable fun v : ChainSample ℓ s n => ∏ j, (X j (initialField ℓ s n v) - κ (idx j)) :=
    Finset.measurable_fun_prod _ fun j _ => (hxm j).sub measurable_const
  have hF₁ : Measurable fun v : ChainSample ℓ s n =>
      ∏ j, (X j (initialField ℓ s n v) + weightedScoreSum ℓ (fun j => (T.stage j).coupling) s n w j v - κ (idx j)) :=
    Finset.measurable_fun_prod _ fun j _ =>
      ((hxm j).add (measurable_weightedScoreSum hSc hf _ s n w j)).sub measurable_const
  have hl : ∫ u, ∏ i ∈ B, (curvatureObservable (h i) (bottomField ℓ s n u) - κ i) ∂(markedSampleLaw T β s n) =
      ∫ v, ∏ j, (X j (initialField ℓ s n v) - κ (idx j)) ∂(chainJointLaw ℓ β (fun j => (T.stage j).coupling) s n) := by
    rw [← hchain, integral_map hmw.aemeasurable hF₀.aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show ∏ i ∈ B, (curvatureObservable (h i) (bottomField ℓ s n u) - κ i) = _
    rw [hprod fun i => curvatureObservable (h i) (bottomField ℓ s n u) - κ i]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [initialField_forgetMarks]
  have hr : ∫ u, ∏ i ∈ B, (chainMark ℓ (fun j => (T.stage j).coupling) al s n (h i) (forgetMarks ℓ s n u) - κ i)
        ∂(markedSampleLaw T β s n) =
      ∫ v, ∏ j, (X j (initialField ℓ s n v) + weightedScoreSum ℓ (fun j => (T.stage j).coupling) s n w j v - κ (idx j))
        ∂(chainJointLaw ℓ β (fun j => (T.stage j).coupling) s n) := by
    rw [← hchain, integral_map hmw.aemeasurable hF₁.aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show ∏ i ∈ B, (chainMark ℓ (fun j => (T.stage j).coupling) al s n (h i) (forgetMarks ℓ s n u) - κ i) = _
    rw [hprod fun i => chainMark ℓ (fun j => (T.stage j).coupling) al s n (h i) (forgetMarks ℓ s n u) - κ i]
    refine Finset.prod_congr rfl fun j _ => ?_
    show chainMark ℓ (fun j => (T.stage j).coupling) al s n (hq j) (forgetMarks ℓ s n u) - _ = _
    rw [chainMark_eq_add (fun j => (T.stage j).coupling) al s n hq j (forgetMarks ℓ s n u)]
  rw [hl, hr, hmain]
private theorem sum_sites_eq_sum_bonds {n : ℕ} [NeZero n] (h : TorusSite n → ℝ) (A : TorusBond n → ℝ) :
    ∑ Y : TorusSite n, h Y * ∑ i : Fin 4, (A (Y, i) + A (Y - unitStep n i, i)) =
      ∑ c : TorusBond n, (h c.1 + h (c.1 + unitStep n c.2)) * A c := by apply _root_.YangMills.SharedProofs.p11136 <;> assumption
private theorem finalField_forgetMarks (s n : ℕ) (u : MarkedSample ℓ s n) :
    finalField ℓ s n (forgetMarks ℓ s n u) = topField ℓ s n u := by
  cases s with
  | zero => rfl
  | succ s => rfl
abbrev _root_.YangMills.SharedProofs.p8091 := @finalField_forgetMarks
private theorem completedObservable_eq_chainMark (T : WeightedResponses.StageTower ℓ) (al : ℕ → ℝ) :
    (s n : ℕ) → [NeZero n] → (h : PlaquetteWeight (fineSide ℓ.side s n)) →
    (u : MarkedSample ℓ s n) → completedObservable T al s n h u =
      chainMark ℓ (fun j => (T.stage j).coupling) al s n h (forgetMarks ℓ s n u)
  | 0, _, _, _, _ => by
    simp [completedObservable, cumulativeSource, chainMark, forgetMarks, bottomField]
  | s + 1, n, _, h, u => by
    have ih := completedObservable_eq_chainMark T al s (n * ℓ.side) h u.1
    have hsrc : sourceTerm T al s n h u = ∑ c : TorusBond n, ℓ.coupling * al s * bondBlockMean ℓ.side (s + 1) n h c *
        bondScore ℓ (T.stage s).coupling (finalField ℓ s (n * ℓ.side) (forgetMarks ℓ s (n * ℓ.side) u.1))
          u.2.2.1 u.2.1 c := by
      rw [finalField_forgetMarks]
      show ℓ.coupling / 2 * al s * ∑ Y : TorusSite n, blockMean ℓ.side (s + 1) n Y h *
        ∑ i : Fin 4, (bondScore ℓ (T.stage s).coupling (topField ℓ s (n * ℓ.side) u.1) u.2.2.1 u.2.1 (Y, i) +
          bondScore ℓ (T.stage s).coupling (topField ℓ s (n * ℓ.side) u.1) u.2.2.1 u.2.1 (Y - unitStep n i, i)) = _
      rw [sum_sites_eq_sum_bonds (fun Y => blockMean ℓ.side (s + 1) n Y h)
        (fun c => bondScore ℓ (T.stage s).coupling (topField ℓ s (n * ℓ.side) u.1) u.2.2.1 u.2.1 c), Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      unfold bondBlockMean
      ring
    exact (add_assoc _ _ _).symm.trans (congrArg₂ (· + ·) ih hsrc)
end Chain
section Moments
variable {Ω ι : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
private theorem integral_prod_le_of_moments (S : Finset ι) (Nf : ι → Ω → ℝ)
    (hm : ∀ i ∈ S, AEStronglyMeasurable (Nf i) μ)
    (h1 : ∀ i ∈ S, ∀ w, 1 ≤ Nf i w) (hc : S.card ≤ 32) (M : ℝ) (hM : 0 ≤ M)
    (hI : ∀ i ∈ S, Integrable (fun w => Nf i w ^ 32) μ) (hb : ∀ i ∈ S, ∫ w, Nf i w ^ 32 ∂μ ≤ M) :
    Integrable (fun w => ∏ i ∈ S, Nf i w) μ ∧ ∫ w, ∏ i ∈ S, Nf i w ∂μ ≤ 1 + 32 * M := by
  have hpt : ∀ w, ∏ i ∈ S, Nf i w ≤ 1 + ∑ i ∈ S, Nf i w ^ 32 := by
    intro w
    have hsum : 0 ≤ ∑ i ∈ S, Nf i w ^ 32 :=
      Finset.sum_nonneg fun i hi => pow_nonneg (by linarith [h1 i hi w]) _
    by_cases hne : S.Nonempty
    · obtain ⟨i₀, hi₀, hmax⟩ := S.exists_max_image (fun i => Nf i w) hne
      have h2 : ∏ i ∈ S, Nf i w ≤ ∏ _i ∈ S, Nf i₀ w :=
        Finset.prod_le_prod (fun i hi => by linarith [h1 i hi w]) fun i hi => hmax i hi
      rw [Finset.prod_const] at h2
      have h3 : Nf i₀ w ^ S.card ≤ Nf i₀ w ^ 32 := pow_le_pow_right₀ (h1 i₀ hi₀ w) hc
      have h4 : Nf i₀ w ^ 32 ≤ ∑ i ∈ S, Nf i w ^ 32 :=
        Finset.single_le_sum (f := fun i => Nf i w ^ 32) (fun i hi => pow_nonneg (by linarith [h1 i hi w]) _) hi₀
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  have hg : Integrable (fun w => 1 + ∑ i ∈ S, Nf i w ^ 32) μ :=
    (integrable_const 1).add (integrable_finsetSum _ hI)
  have hpos : ∀ w, 0 ≤ ∏ i ∈ S, Nf i w := fun w => by
    classical
    by_cases hne : S.Nonempty
    · exact Finset.prod_nonneg fun i hi => by linarith [h1 i hi w]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  have hP : Integrable (fun w => ∏ i ∈ S, Nf i w) μ := by
    refine hg.mono' (Finset.aestronglyMeasurable_fun_prod _ hm) (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hpos w)]
    exact hpt w
  refine ⟨hP, (integral_mono hP hg hpt).trans ?_⟩
  rw [integral_add (integrable_const 1) (integrable_finsetSum _ hI), integral_finsetSum _ hI]
  have h5 : ∑ i ∈ S, ∫ w, Nf i w ^ 32 ∂μ ≤ ∑ _i ∈ S, M := Finset.sum_le_sum hb
  rw [Finset.sum_const, nsmul_eq_mul] at h5
  have h6 : (S.card : ℝ) * M ≤ 32 * M := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hM
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  linarith
end Moments
private theorem centered_products_compare {Ω : Type} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hle : m ≤ mΩ)
    {p : ℕ} (hp : p ≤ 32) (Mk R Nf : Fin p → Ω → ℝ) (κ : Fin p → ℝ) (hMm : ∀ i, Measurable (Mk i))
    (hMb : ∀ i, ∃ C : ℝ, ∀ w, |Mk i w| ≤ C)
    (hresp : ∀ i, ∀ᵐ w ∂μ, R i w - κ i = (μ[fun w' => Mk i w' - κ i | m]) w)
    (hN1 : ∀ i w, 1 ≤ Nf i w) (hNm : ∀ i, AEStronglyMeasurable (Nf i) μ) (M Eb Xb : ℝ) (hM0 : 0 ≤ M) (hEb : 0 ≤ Eb)
    (hXb : 0 ≤ Xb)
    (hNI : ∀ i, Integrable (fun w => Nf i w ^ 32) μ) (hNb : ∀ i, ∫ w, Nf i w ^ 32 ∂μ ≤ M)
    (hprod : ∀ J : Finset (Fin p), ∀ᵐ w ∂μ, |(μ[fun w' => ∏ i ∈ J, (Mk i w' - κ i) | m]) w - ∏ i ∈ J, (R i w - κ i)| ≤
      Eb * ∏ i ∈ J, Nf i w)
    (hG : ∀ i, ∀ᵐ w ∂μ, |R i w - κ i| ≤ Xb * Nf i w) (I : Finset (Fin p)) :
    (∀ i, ∫ w, R i w ∂μ = ∫ w, Mk i w ∂μ) ∧
      |∫ w, ∏ i ∈ I, (Mk i w - ∫ w', R i w' ∂μ) ∂μ - ∫ w, ∏ i ∈ I, (R i w - ∫ w', R i w' ∂μ) ∂μ| ≤
        2 ^ 32 * ((1 + Xb * M) ^ 32 * (Eb * (1 + 32 * M))) := by
  have hsub : ∀ i, Integrable (fun w => Mk i w - κ i) μ := by
    intro i
    obtain ⟨C, hC⟩ := hMb i
    exact Integrable.of_bound ((hMm i).sub measurable_const).aestronglyMeasurable (|C| + |κ i|)
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]
        exact (abs_sub _ _).trans (add_le_add ((hC w).trans (le_abs_self C)) le_rfl))
  have hIm : ∀ i, Integrable (Mk i) μ := fun i =>
    ((hsub i).add (integrable_const (μ := μ) (κ i))).congr (Eventually.of_forall fun w => by
      show Mk i w - κ i + κ i = _
      ring)
  have hcI : ∀ i, Integrable (μ[fun w => Mk i w - κ i | m]) μ := fun i => integrable_condExp
  have hRκ : ∀ i, Integrable (fun w => R i w - κ i) μ := fun i => (hcI i).congr ((hresp i).mono fun w e => e.symm)
  have hR : ∀ i, Integrable (R i) μ := fun i =>
    ((hRκ i).add (integrable_const (μ := μ) (κ i))).congr (Eventually.of_forall fun w => by
      show R i w - κ i + κ i = _
      ring)
  have hmean : ∀ i, ∫ w, R i w ∂μ = ∫ w, Mk i w ∂μ := by
    intro i
    have e1 : ∫ w, (R i w - κ i) ∂μ = ∫ w, (Mk i w - κ i) ∂μ := by
      rw [integral_congr_ae (hresp i), integral_condExp hle]
    rw [integral_sub (hR i) (integrable_const _), integral_sub (hIm i) (integrable_const _)] at e1
    linarith
  refine ⟨hmean, ?_⟩
  set c : Fin p → ℝ := fun i => ∫ w', R i w' ∂μ with hc
  have hbdd : ∀ i, ∃ C : ℝ, ∀ᵐ w ∂μ, |R i w - κ i| ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := hMb i
    have hnn : 0 ≤ |C| + |κ i| := by positivity
    have h1 := ae_bdd_condExp_of_ae_bdd (m := m) (R := ⟨_, hnn⟩) (f := fun w => Mk i w - κ i) (μ := μ)
      (Eventually.of_forall fun w => (abs_sub _ _).trans (add_le_add ((hC w).trans (le_abs_self C)) le_rfl))
    refine ⟨|C| + |κ i|, ?_⟩
    filter_upwards [h1, hresp i] with w h2 h3
    rw [h3]
    exact h2
  have hgi : ∀ i, |κ i - c i| ≤ 1 + Xb * M := by
    intro i
    have h1 : κ i - c i = -∫ w, (R i w - κ i) ∂μ := by
      rw [integral_sub (hR i) (integrable_const _)]
      simp [hc]
    have hle' : ∀ w, Nf i w ≤ Nf i w ^ 32 := fun w => le_self_pow₀ (hN1 i w) (by norm_num)
    have h2 : ∀ᵐ w ∂μ, ‖R i w - κ i‖ ≤ Xb * Nf i w ^ 32 := by
      filter_upwards [hG i] with w hw
      rw [Real.norm_eq_abs]
      exact hw.trans (mul_le_mul_of_nonneg_left (hle' w) hXb)
    have h3 := norm_integral_le_of_norm_le ((hNI i).const_mul Xb) h2
    rw [Real.norm_eq_abs, integral_const_mul] at h3
    rw [h1, abs_neg]
    have h4 := mul_le_mul_of_nonneg_left (hNb i) hXb
    linarith
  have hab : ∀ J ∈ I.powerset, Integrable (fun w => ∏ i ∈ J, (Mk i w - κ i)) μ := fun J _ =>
    integrable_prod_of_bounded _ _ (fun i _ => (hsub i).aestronglyMeasurable) (fun i _ => by
      obtain ⟨C, hC⟩ := hMb i
      exact ⟨|C| + |κ i|, Eventually.of_forall fun w =>
        (abs_sub _ _).trans (add_le_add ((hC w).trans (le_abs_self C)) le_rfl)⟩)
  have hbb : ∀ J ∈ I.powerset, Integrable (fun w => ∏ i ∈ J, (R i w - κ i)) μ := fun J _ =>
    integrable_prod_of_bounded _ _ (fun i _ => (hRκ i).aestronglyMeasurable) (fun i _ => hbdd i)
  have hcardI : I.card ≤ 32 := (Finset.card_le_univ I).trans (by simpa using hp)
  have hE : ∀ J ∈ I.powerset, |∫ w, ∏ i ∈ J, (Mk i w - κ i) ∂μ - ∫ w, ∏ i ∈ J, (R i w - κ i) ∂μ| ≤
      Eb * (1 + 32 * M) := by
    intro J hJ
    have hJc : J.card ≤ 32 := (Finset.card_le_card (Finset.mem_powerset.mp hJ)).trans hcardI
    obtain ⟨hP, hPb⟩ := integral_prod_le_of_moments (μ := μ) J Nf (fun i _ => hNm i) (fun i _ w => hN1 i w) hJc M hM0
      (fun i _ => hNI i) (fun i _ => hNb i)
    rw [← integral_condExp hle (f := fun w => ∏ i ∈ J, (Mk i w - κ i)), ← integral_sub integrable_condExp (hbb J hJ)]
    have hbound : ∀ᵐ w ∂μ, ‖(μ[fun w' => ∏ i ∈ J, (Mk i w' - κ i) | m]) w - ∏ i ∈ J, (R i w - κ i)‖ ≤
        Eb * ∏ i ∈ J, Nf i w := by
      filter_upwards [hprod J] with w hw
      rwa [Real.norm_eq_abs]
    have h3 := norm_integral_le_of_norm_le (hP.const_mul Eb) hbound
    rw [Real.norm_eq_abs, integral_const_mul] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left hPb hEb)
  have hcmp := integral_prod_add_sub_le (μ := μ) I (fun i w => Mk i w - κ i) (fun i w => R i w - κ i)
    (fun i => κ i - c i) (fun _ => Eb * (1 + 32 * M)) hab hbb hE
  have e1 : ∀ (f : Fin p → Ω → ℝ), ∫ w, ∏ i ∈ I, (f i w - κ i + (κ i - c i)) ∂μ = ∫ w, ∏ i ∈ I, (f i w - c i) ∂μ :=
    fun f => integral_congr_ae (Eventually.of_forall fun w => Finset.prod_congr rfl fun i _ => by ring)
  rw [e1 Mk, e1 R] at hcmp
  refine hcmp.trans ?_
  have hY : (1 : ℝ) ≤ 1 + Xb * M := by nlinarith [mul_nonneg hXb hM0]
  have hEE : 0 ≤ Eb * (1 + 32 * M) := by positivity
  have hterm : ∀ J ∈ I.powerset, (∏ i ∈ I \ J, |κ i - c i|) * (Eb * (1 + 32 * M)) ≤
      (1 + Xb * M) ^ 32 * (Eb * (1 + 32 * M)) := by
    intro J _
    refine mul_le_mul_of_nonneg_right ?_ hEE
    have h1 : ∏ i ∈ I \ J, |κ i - c i| ≤ ∏ _i ∈ I \ J, (1 + Xb * M) :=
      Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => hgi i
    rw [Finset.prod_const] at h1
    exact h1.trans (pow_le_pow_right₀ hY ((Finset.card_le_card Finset.sdiff_subset).trans hcardI))
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hcardI
section Errors
variable {ℓ : StepParameters}
private def SupportsCountedBelow (ℓ : StepParameters) (A : ℕ → ℝ) {p : ℕ} : (s n : ℕ) → [NeZero n] →
    (Fin p → PlaquetteWeight (fineSide ℓ.side s n)) → Prop
  | 0, _, _, _ => True
  | s + 1, n, _, h => (∀ i, ((weightSupportSites ℓ.side s (n * ℓ.side) (h i)).card : ℝ) ≤ A s) ∧
      SupportsCountedBelow ℓ A s (n * ℓ.side) h
private theorem supportsCountedBelow_comp (A : ℕ → ℝ) {m m' : ℕ} (idx : Fin m' → Fin m) :
    (s n : ℕ) → [NeZero n] → (h : Fin m → PlaquetteWeight (fineSide ℓ.side s n)) →
    SupportsCountedBelow ℓ A s n h → SupportsCountedBelow ℓ A s n (fun j => h (idx j))
  | 0, _, _, _, _ => trivial
  | s + 1, n, _, h, ⟨h0, hrest⟩ => ⟨fun j => h0 (idx j), supportsCountedBelow_comp A idx s (n * ℓ.side) h hrest⟩
private theorem separationError_le_sum (Cp C₀ : ℝ) (hCp : 0 ≤ Cp) (hC₀ : 0 ≤ C₀) (A D : ℕ → ℝ) {p : ℕ} :
    (s n : ℕ) → [NeZero n] → (h : Fin p → PlaquetteWeight (fineSide ℓ.side s n)) → SupportsCountedBelow ℓ A s n h →
    separationError ℓ Cp C₀ D s n h ≤ ∑ u ∈ Finset.range s,
      Cp * ((p : ℝ) * A u) ^ 2 * Real.exp (-(ℓ.rt * D u / 2 ^ 8)) * (4 * C₀ * A u) ^ p
  | 0, _, _, _, _ => by simp [separationError]
  | s + 1, n, _, h, ⟨hc, hrest⟩ => by
    have ih := separationError_le_sum Cp C₀ hCp hC₀ A D s (n * ℓ.side) h hrest
    rw [Finset.sum_range_succ]
    show separationError ℓ Cp C₀ D s (n * ℓ.side) h +
      Cp * (∑ i, ((weightSupportSites ℓ.side s (n * ℓ.side) (h i)).card : ℝ)) ^ 2 *
        Real.exp (-(ℓ.rt * D s / 2 ^ 8)) *
      ∏ i, (4 * C₀ * ((weightSupportSites ℓ.side s (n * ℓ.side) (h i)).card : ℝ)) ≤ _
    refine add_le_add ih ?_
    have h0 : 0 ≤ ∑ i, ((weightSupportSites ℓ.side s (n * ℓ.side) (h i)).card : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have h1 : ∑ i, ((weightSupportSites ℓ.side s (n * ℓ.side) (h i)).card : ℝ) ≤ (p : ℝ) * A s := by
      have := Finset.sum_le_card_nsmul Finset.univ
        (fun i => ((weightSupportSites ℓ.side s (n * ℓ.side) (h i)).card : ℝ)) (A s) fun i _ => hc i
      simpa using this
    have h2 : ∏ i, (4 * C₀ * ((weightSupportSites ℓ.side s (n * ℓ.side) (h i)).card : ℝ)) ≤ (4 * C₀ * A s) ^ p := by
      have := Finset.prod_le_prod (s := Finset.univ)
        (f := fun i => 4 * C₀ * ((weightSupportSites ℓ.side s (n * ℓ.side) (h i)).card : ℝ))
        (g := fun _ : Fin p => 4 * C₀ * A s) (fun i _ => by positivity)
        fun i _ => mul_le_mul_of_nonneg_left (hc i) (by positivity)
      simpa using this
    have h3 : (∑ i, ((weightSupportSites ℓ.side s (n * ℓ.side) (h i)).card : ℝ)) ^ 2 ≤ ((p : ℝ) * A s) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    have h4 : 0 ≤ ∏ i, (4 * C₀ * ((weightSupportSites ℓ.side s (n * ℓ.side) (h i)).card : ℝ)) :=
      Finset.prod_nonneg fun _ _ => by positivity
    have he := Real.exp_pos (-(ℓ.rt * D s / 2 ^ 8))
    calc Cp * (∑ i, ((weightSupportSites ℓ.side s (n * ℓ.side) (h i)).card : ℝ)) ^ 2 *
          Real.exp (-(ℓ.rt * D s / 2 ^ 8)) *
          ∏ i, (4 * C₀ * ((weightSupportSites ℓ.side s (n * ℓ.side) (h i)).card : ℝ))
        ≤ Cp * ((p : ℝ) * A s) ^ 2 * Real.exp (-(ℓ.rt * D s / 2 ^ 8)) *
          ∏ i, (4 * C₀ * ((weightSupportSites ℓ.side s (n * ℓ.side) (h i)).card : ℝ)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h3 hCp) he.le) h4
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
private theorem level_term_le {rt Cq C₀ Lr v r : ℝ} (hrt : 0 < rt) (hCq : 0 ≤ Cq) (hC₀ : 1 ≤ C₀) (hL : 2 ≤ Lr)
    (hv : 2 ^ 12 * r ≤ v) (hr : 1 ≤ r) {q : ℕ} (hq : q ≤ 32) :
    Cq * ((q : ℝ) * (4 * v * Lr) ^ 4) ^ 2 * Real.exp (-(rt * (v / 2 - 5) / 2 ^ 8)) * (4 * C₀ * (4 * v * Lr) ^ 4) ^ q ≤
      Cq * 1024 * (4 * C₀) ^ 32 * (4 * Lr) ^ 136 * ((138).factorial / (rt / 2 ^ 11) ^ 138) *
        Real.exp (-(4 * rt * r)) / v ^ 2 := by
  have hvpos : 0 < v := by nlinarith
  set c : ℝ := rt / 2 ^ 11 with hc
  set A : ℝ := (4 * v * Lr) ^ 4 with hA
  have hA1 : 1 ≤ A := by
    rw [hA]
    exact one_le_pow₀ (by nlinarith)
  have h1 : ((q : ℝ) * A) ^ 2 ≤ 1024 * A ^ 2 := by
    have hq' : (q : ℝ) ≤ 32 := by exact_mod_cast hq
    have : (q : ℝ) * A ≤ 32 * A := mul_le_mul_of_nonneg_right hq' (by linarith)
    calc ((q : ℝ) * A) ^ 2 ≤ (32 * A) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
      _ = 1024 * A ^ 2 := by ring
  have h2 : (4 * C₀ * A) ^ q ≤ (4 * C₀ * A) ^ 32 :=
    pow_le_pow_right₀ (by nlinarith) hq
  have h3 : Real.exp (-(rt * (v / 2 - 5) / 2 ^ 8)) ≤ Real.exp (-(4 * rt * r)) * Real.exp (-(c * v)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [hc]
    have h4 : 2 ^ 10 * r + 5 ≤ 3 * v / 8 := by nlinarith
    have h5 : 0 ≤ rt * (3 * v / 8 - (2 ^ 10 * r + 5)) := mul_nonneg hrt.le (by linarith)
    have e : -(4 * rt * r) + -(rt / 2 ^ 11 * v) - -(rt * (v / 2 - 5) / 2 ^ 8) =
        rt * (3 * v / 8 - (2 ^ 10 * r + 5)) / 2 ^ 8 := by ring
    linarith
  have h7 : v ^ 138 * Real.exp (-(c * v)) ≤ (138).factorial / c ^ 138 := by
    have h8 := Real.pow_div_factorial_le_exp (c * v) (by positivity) 138
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    rw [div_le_iff₀ (by positivity)] at h8
    linarith
  have hexp3 := Real.exp_pos (-(rt * (v / 2 - 5) / 2 ^ 8))
  have hApow : A ^ 34 = (4 * Lr) ^ 136 * v ^ 136 := by
    rw [hA]
    ring
  have hmain : Cq * ((q : ℝ) * A) ^ 2 * Real.exp (-(rt * (v / 2 - 5) / 2 ^ 8)) * (4 * C₀ * A) ^ q ≤
      Cq * (1024 * A ^ 2) * (Real.exp (-(4 * rt * r)) * Real.exp (-(c * v))) * (4 * C₀ * A) ^ 32 := by
    have hq0 : 0 ≤ (4 * C₀ * A) ^ q := by positivity
    calc Cq * ((q : ℝ) * A) ^ 2 * Real.exp (-(rt * (v / 2 - 5) / 2 ^ 8)) * (4 * C₀ * A) ^ q
        ≤ Cq * (1024 * A ^ 2) * Real.exp (-(rt * (v / 2 - 5) / 2 ^ 8)) * (4 * C₀ * A) ^ q := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h1 hCq) hexp3.le) hq0
      _ ≤ Cq * (1024 * A ^ 2) * (Real.exp (-(4 * rt * r)) * Real.exp (-(c * v))) * (4 * C₀ * A) ^ q := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by positivity)) hq0
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  refine hmain.trans ?_
  rw [le_div_iff₀ (by positivity)]
  have e : Cq * (1024 * A ^ 2) * (Real.exp (-(4 * rt * r)) * Real.exp (-(c * v))) * (4 * C₀ * A) ^ 32 * v ^ 2 =
      Cq * 1024 * (4 * C₀) ^ 32 * (4 * Lr) ^ 136 * Real.exp (-(4 * rt * r)) * (v ^ 138 * Real.exp (-(c * v))) := by
    rw [mul_pow (4 * C₀) A 32]
    have : A ^ 2 * A ^ 32 = (4 * Lr) ^ 136 * v ^ 136 := by
      rw [← pow_add]
      exact hApow
    calc _ = Cq * 1024 * (4 * C₀) ^ 32 * (A ^ 2 * A ^ 32) * Real.exp (-(4 * rt * r)) * Real.exp (-(c * v)) * v ^ 2 := by
          ring
      _ = _ := by rw [this]; ring
  rw [e]
  have hpre : 0 ≤ Cq * 1024 * (4 * C₀) ^ 32 * (4 * Lr) ^ 136 * Real.exp (-(4 * rt * r)) := by positivity
  calc Cq * 1024 * (4 * C₀) ^ 32 * (4 * Lr) ^ 136 * Real.exp (-(4 * rt * r)) * (v ^ 138 * Real.exp (-(c * v)))
      ≤ Cq * 1024 * (4 * C₀) ^ 32 * (4 * Lr) ^ 136 * Real.exp (-(4 * rt * r)) * ((138).factorial / c ^ 138) :=
        mul_le_mul_of_nonneg_left h7 hpre
    _ = _ := by ring
end Errors
section Family
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
variable {ℓ : StepParameters}
private theorem euclidNormVec_le_two_mul {v : Fin 4 → ℝ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ a, |v a| ≤ B) :
    euclidNormVec v ≤ 2 * B := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.euclidNormVec_le <;> assumption
private theorem isBoundedBorelCompactlySupported_of_bump {d vt : ℝ} (hd : 0 < d) (hv : 0 < vt) {p : ℕ}
    {φ : Fin p → AmbientSpace → ℝ} (hφ : IsSeparatedBumpFamily d vt φ) (i : Fin p) :
    InfiniteLattice.IsBoundedBorelCompactlySupported (φ i) := by
  have hlip : LipschitzWith (Real.toNNReal (2 / (vt * d))) (φ i) := by
    refine LipschitzWith.of_dist_le' fun x x' => ?_
    rw [Real.dist_eq]
    refine (hφ.lipschitz i x x').trans ?_
    have h1 : euclidNormVec (x - x') ≤ 2 * dist x x' :=
      euclidNormVec_le_two_mul dist_nonneg fun a => by
        have := dist_le_pi_dist x x' a
        rwa [Real.dist_eq] at this
    calc euclidNormVec (x - x') / (vt * d) ≤ 2 * dist x x' / (vt * d) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = 2 / (vt * d) * dist x x' := by ring
  refine ⟨hlip.continuous.measurable, ⟨1, fun x => ?_⟩, ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (hφ.nonneg i x)]
    exact hφ.le_one i x
  · obtain ⟨c, hc⟩ := hφ.support_in_ball i
    have hsub : tsupport (φ i) ⊆ Metric.closedBall c d := by
      intro y hy
      have h1 : euclidNormVec (y - c) ≤ d := hc hy
      refine Metric.mem_closedBall.mpr ((dist_pi_le_iff hd.le).mpr fun a => ?_)
      rw [Real.dist_eq]
      refine le_trans ?_ h1
      unfold euclidNormVec
      exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun μ => (y - c) μ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ a))
    exact (isCompact_closedBall c d).of_isClosed_subset (isClosed_tsupport _) hsub
private theorem separated_and_counted (hWt : markWeightsOnUnitTorusStatement) (hodd : Odd ℓ.side) {d vt : ℝ}
    (hd0 : 0 < d) (hd : d ≤ 1 / 4) (hv : 0 < vt) {p : ℕ} {φ : Fin p → AmbientSpace → ℝ}
    (hφ : IsSeparatedBumpFamily d vt φ) (K : ℕ) (x D A : ℕ → ℝ) :
    ∀ (s n : ℕ) [NeZero n], s ≤ K → n = 2 * ℓ.side ^ (K - s) →
      (∀ u < s, 2 ^ 10 * (clusterRange (x u) : ℝ) ≤ D u ∧ 8 < D u ∧
        D u + 5 ≤ d / 2 * (ℓ.side : ℝ) ^ (K - (u + 1)) ∧
        (2 * (d * (ℓ.side : ℝ) ^ (K - u)) + 2) ^ 4 ≤ A u) →
      SeparatedAlongTower ℓ x D s n (fun i => torusWeightAtBarycentres ℓ.side K (fineSide ℓ.side s n) (φ i)) ∧
        SupportsCountedBelow ℓ A s n (fun i => torusWeightAtBarycentres ℓ.side K (fineSide ℓ.side s n) (φ i)) := by
  intro s
  induction s with
  | zero => exact fun _ _ _ _ _ => ⟨trivial, trivial⟩
  | succ s ih =>
    intro n _ hsK hn hc
    have hK : K - s = (K - (s + 1)) + 1 := by omega
    have hn' : n * ℓ.side = 2 * ℓ.side ^ (K - s) := by
      rw [hn, hK, pow_succ]
      ring
    obtain ⟨a, b⟩ := ih (n * ℓ.side) (by omega) hn' fun u hu => hc u (by omega)
    obtain ⟨h1, h2, h3, h4⟩ := hc s (by omega)
    have wt := hWt ℓ.side hodd K d vt hd0 hd hv p φ hφ (s + 1) n hsK hn
    have wt' := hWt ℓ.side hodd K d vt hd0 hd hv p φ hφ s (n * ℓ.side) (by omega) hn'
    refine ⟨⟨⟨h1, h2, fun i j hij y hy y' hy' => ?_⟩, a⟩, ⟨fun i => ?_, b⟩⟩
    · have := wt.2.2.2.1 i j hij y hy y' hy'
      linarith
    · exact (wt'.2.2.1 i).trans h4
end Family
section Tie
open InfiniteLattice (AmbientSpace)
variable {ℓ : StepParameters}
private theorem integral_prod_add_expand {Ω ι : Type} [MeasurableSpace Ω] {μ : Measure Ω} [DecidableEq ι]
    (I : Finset ι) (c : ι → Ω → ℝ) (g : ι → ℝ) (hc : ∀ J ∈ I.powerset, Integrable (fun w => ∏ i ∈ J, c i w) μ) :
    ∫ w, ∏ i ∈ I, (c i w + g i) ∂μ = ∑ J ∈ I.powerset, (∏ i ∈ I \ J, g i) * ∫ w, ∏ i ∈ J, c i w ∂μ := by
  have h1 : ∀ w, ∏ i ∈ I, (c i w + g i) = ∑ J ∈ I.powerset, (∏ i ∈ I \ J, g i) * ∏ i ∈ J, c i w := by
    intro w
    rw [Finset.prod_add]
    exact Finset.sum_congr rfl fun J _ => mul_comm _ _
  simp only [h1]
  rw [integral_finsetSum _ fun J hJ => (hc J hJ).const_mul _]
  exact Finset.sum_congr rfl fun J _ => integral_const_mul _ _
private theorem measurable_bottomField (s n : ℕ) : Measurable (bottomField ℓ s n) := by
  have h : bottomField ℓ s n = initialField ℓ s n ∘ forgetMarks ℓ s n :=
    funext fun u => (initialField_forgetMarks ℓ s n u).symm
  rw [h]
  exact (measurable_initialField ℓ s n).comp (measurable_forgetMarks s n)
abbrev _root_.YangMills.SharedProofs.p4086 := @measurable_bottomField
private theorem integral_prod_smeared_eq_bottom (hW : LawInAState.unitTorusMomentsViaWeightsStatement)
    (hI : unitTorusObservablesIntegrableStatement) (hodd : Odd ℓ.side) (h3 : 3 ≤ ℓ.side) {K k : ℕ} (hK : 1 ≤ K)
    (hk : k ≤ K) (T : WeightedResponses.StageTower ℓ) (β : ℝ)
    [IsFiniteMeasure (markedSampleLaw T β k (boxSide ℓ.side K k))]
    (hbot : Measure.map (bottomField ℓ k (boxSide ℓ.side K k)) (markedSampleLaw T β k (boxSide ℓ.side K k)) =
      wilsonLaw β (fineSide ℓ.side k (boxSide ℓ.side K k)))
    {p : ℕ} (φ : Fin p → AmbientSpace → ℝ) (hb : ∀ i, InfiniteLattice.IsBoundedBorelCompactlySupported (φ i))
    (c : Fin p → ℝ) (I : Finset (Fin p)) :
    ∫ U, ∏ i ∈ I, (smearedObservable ℓ.side K (φ i) U - c i) ∂unitTorusMeasure ℓ.side K β =
      ∫ u, ∏ i ∈ I, (curvatureObservable (unitTorusWeight ℓ.side K k (φ i))
          (bottomField ℓ k (boxSide ℓ.side K k) u) - c i)
        ∂(markedSampleLaw T β k (boxSide ℓ.side K k)) := by
  have hreidx : ∀ (J : Finset (Fin p)), ∃ (idx : Fin J.card → Fin p), ∀ g : Fin p → ℝ,
      ∏ i ∈ J, g i = ∏ j, g (idx j) := by
    intro J
    let e : Fin J.card ≃ {i // i ∈ J} := J.equivFin.symm
    refine ⟨fun j => (e j).1, fun g => ?_⟩
    rw [← Finset.prod_coe_sort J g]
    exact (Equiv.prod_comp e fun i : {i // i ∈ J} => g i.1).symm
  have hIa : ∀ J ∈ I.powerset, Integrable (fun U => ∏ i ∈ J, smearedObservable ℓ.side K (φ i) U)
      (unitTorusMeasure ℓ.side K β) := by
    intro J _
    obtain ⟨idx, hidx⟩ := hreidx J
    refine (hI ℓ.side K hodd h3 hK β J.card (fun j => φ (idx j)) fun j => hb _).congr
      (Eventually.of_forall fun U => ?_)
    exact (hidx fun i => smearedObservable ℓ.side K (φ i) U).symm
  have hIb : ∀ J ∈ I.powerset, Integrable (fun u => ∏ i ∈ J, curvatureObservable (unitTorusWeight ℓ.side K k (φ i))
      (bottomField ℓ k (boxSide ℓ.side K k) u)) (markedSampleLaw T β k (boxSide ℓ.side K k)) := by
    intro J _
    refine integrable_prod_of_bounded _ _ (fun i _ => ?_) (fun i _ => ?_)
    · exact ((continuous_curvatureObservable _).measurable.comp (measurable_bottomField k _)).aestronglyMeasurable
    · obtain ⟨C, hC⟩ := bounded_curvatureObservable (unitTorusWeight ℓ.side K k (φ i))
      exact ⟨C, Eventually.of_forall fun u => hC _⟩
  have e1 : ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Fin p → Ω → ℝ),
      ∫ w, ∏ i ∈ I, (f i w - c i) ∂μ = ∫ w, ∏ i ∈ I, (f i w + -c i) ∂μ := by
    intro Ω _ μ f
    simp only [sub_eq_add_neg]
  rw [e1 _ fun i U => smearedObservable ℓ.side K (φ i) U, e1 _ fun i u =>
      curvatureObservable (unitTorusWeight ℓ.side K k (φ i)) (bottomField ℓ k (boxSide ℓ.side K k) u),
    integral_prod_add_expand I _ _ hIa, integral_prod_add_expand I _ _ hIb]
  refine Finset.sum_congr rfl fun J _ => ?_
  congr 1
  obtain ⟨idx, hidx⟩ := hreidx J
  have hm : Measurable fun W : TorusField (fineSide ℓ.side k (boxSide ℓ.side K k)) =>
      ∏ j, curvatureObservable (unitTorusWeight ℓ.side K k (φ (idx j))) W :=
    Finset.measurable_fun_prod _ fun j _ => (continuous_curvatureObservable _).measurable
  calc ∫ U, ∏ i ∈ J, smearedObservable ℓ.side K (φ i) U ∂unitTorusMeasure ℓ.side K β
      = ∫ U, ∏ j, smearedObservable ℓ.side K (φ (idx j)) U ∂unitTorusMeasure ℓ.side K β :=
        integral_congr_ae (Eventually.of_forall fun U => hidx fun i => smearedObservable ℓ.side K (φ i) U)
    _ = ∫ W, ∏ j, curvatureObservable (unitTorusWeight ℓ.side K k (φ (idx j))) W
          ∂wilsonLaw β (fineSide ℓ.side k (boxSide ℓ.side K k)) :=
        hW ℓ.side K k hodd h3 hK hk β J.card (fun j => φ (idx j)) fun j => hb _
    _ = ∫ u, ∏ j, curvatureObservable (unitTorusWeight ℓ.side K k (φ (idx j)))
            (bottomField ℓ k (boxSide ℓ.side K k) u)
          ∂(markedSampleLaw T β k (boxSide ℓ.side K k)) := by
        rw [← hbot, integral_map (measurable_bottomField k _).aemeasurable hm.aestronglyMeasurable]
    _ = _ := integral_congr_ae (Eventually.of_forall fun u =>
        (hidx fun i => curvatureObservable (unitTorusWeight ℓ.side K k (φ i))
          (bottomField ℓ k (boxSide ℓ.side K k) u)).symm)
end Tie
section Tower
open InfiniteLattice (AmbientSpace)
variable {ℓ : StepParameters}
private theorem clusterRange_le_add (x : ℕ → ℝ) (k : ℕ)
    (hstep : ∀ u < k, clusterRange (x u) ≤ clusterRange (x (u + 1)) + 1) :
    ∀ j u, u + j = k → clusterRange (x u) ≤ clusterRange (x k) + j := by
  intro j
  induction j with
  | zero =>
    intro u hu
    have : u = k := by omega
    subst this
    simp
  | succ j ih =>
    intro u hu
    have h1 := ih (u + 1) (by omega)
    have h2 := hstep u (by omega)
    omega
private theorem level_scale_bounds {n₀ r Lr : ℝ} (hn : 2 ^ 12 * r ≤ n₀) (hr : 2 ≤ r) (hL : 2 ≤ Lr) (j : ℕ) :
    2 ^ 10 * (r + ((j : ℝ) + 1)) ≤ n₀ * Lr ^ j / 2 - 5 ∧ 8 < n₀ * Lr ^ j / 2 - 5 ∧ 2 ^ 12 * r ≤ n₀ * Lr ^ j ∧
      (2 : ℝ) ^ j ≤ n₀ * Lr ^ j := by
  have hw0 : (2 : ℝ) ^ j ≤ Lr ^ j := pow_le_pow_left₀ (by norm_num) hL j
  have hw1 : (j : ℝ) + 1 ≤ 2 ^ j := by
    have := one_add_mul_le_pow (a := (1 : ℝ)) (by norm_num) j
    norm_num at this
    linarith
  set w : ℝ := Lr ^ j with hwdef
  have h1 : 2 ^ 12 * r * w ≤ n₀ * w := mul_le_mul_of_nonneg_right hn (by linarith)
  have h2 : r ≤ r * w := by nlinarith
  have h3 : 2 * ((j : ℝ) + 1) ≤ r * w := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
private theorem centered_products_at_stage (hS : ScoresPreserveCorrelations) (hT : TwoPointByTotalCovarianceStatement)
    (hSc : BondScoreProperties) (hWt : markWeightsOnUnitTorusStatement)
    (hW : LawInAState.unitTorusMomentsViaWeightsStatement) (hI : unitTorusObservablesIntegrableStatement)
    (hMk : ResponseIsConditionalExpectation)
    (hf : ℓ.Admissible) (T : WeightedResponses.StageTower ℓ) (S : ScoredStageTower T)
    (hcut : ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (hcoin : T.MarksMeasurable) (β : ℝ)
    (x : ℕ → ℝ) (K k : ℕ) (hkK : k < K)
    (hstep : ∀ u < k, clusterRange (x u) ≤ clusterRange (x (u + 1)) + 1) {d vt : ℝ} (hd0 : 0 < d) (hd : d ≤ 1 / 4)
    (hv : 0 < vt) (hr : 2 ≤ (clusterRange (x k) : ℝ))
    (hfar : 2 ^ 12 * (clusterRange (x k) : ℝ) ≤ lengthInSites ℓ.side K k d)
    (hvt : 2 ≤ vt * lengthInSites ℓ.side K k d) {p : ℕ} (hp : p ≤ 32) {φ : Fin p → AmbientSpace → ℝ}
    (hφ : IsSeparatedBumpFamily d vt φ)
    {Cp : ℕ → ℝ} {C₀ Cx Cm M : ℝ} (hC₀ : 1 ≤ C₀) (hCx : 0 ≤ Cx) (hCm : ∀ q ≤ 32, 0 ≤ Cp q ∧ Cp q ≤ Cm) (hM0 : 0 ≤ M)
    (hfitted : ∀ f : FinePlaquetteFunction, ∀ᵐ a ∂(markedSampleLaw T β k (boxSide ℓ.side K k)),
      fittedResponse S f k (boxSide ℓ.side K k) (stageState T k (boxSide ℓ.side K k) a) =
        ((markedSampleLaw T β k (boxSide ℓ.side K k))[completedCentered S f k (boxSide ℓ.side K k) |
          stageSigma T k (boxSide ℓ.side K k)]) a)
    (hbound : ∀ f : FinePlaquetteFunction,
      weightNorm ℓ.side k (fineWeight f (fineSide ℓ.side k (boxSide ℓ.side K k))) ≤ 1 →
      ∀ᵐ a ∂(markedSampleLaw T β k (boxSide ℓ.side K k)),
        |fittedResponse S f k (boxSide ℓ.side K k) (stageState T k (boxSide ℓ.side K k) a)| ≤
        Cx * ((functionSites ℓ.side f k (boxSide ℓ.side K k)).card : ℝ) *
          scoreMeanOver S f k (boxSide ℓ.side K k) (stageState T k (boxSide ℓ.side K k) a))
    (hmany : ∀ (q : ℕ) (g : Fin q → FinePlaquetteFunction) (D : ℕ → ℝ),
      (∀ i, weightNorm ℓ.side k (fineWeight (g i) (fineSide ℓ.side k (boxSide ℓ.side K k))) ≤ 1) →
      SeparatedAlongTower ℓ x D k (boxSide ℓ.side K k)
        (fun i => fineWeight (g i) (fineSide ℓ.side k (boxSide ℓ.side K k))) →
      ∀ᵐ u ∂(markedSampleLaw T β k (boxSide ℓ.side K k)),
        |conditionalProduct S β g Finset.univ k (boxSide ℓ.side K k) u -
            ∏ i, fittedResponse S (g i) k (boxSide ℓ.side K k) (stageState T k (boxSide ℓ.side K k) u)| ≤
          separationError ℓ (Cp q) C₀ D k (boxSide ℓ.side K k)
              (fun i => fineWeight (g i) (fineSide ℓ.side k (boxSide ℓ.side K k))) *
            ∏ i, scoreMeanOver S (g i) k (boxSide ℓ.side K k) (stageState T k (boxSide ℓ.side K k) u))
    (hone : ∀ (f : FinePlaquetteFunction) (u),
      1 ≤ scoreMeanOver S f k (boxSide ℓ.side K k) (stageState T k (boxSide ℓ.side K k) u))
    (hNm : ∀ f : FinePlaquetteFunction,
      AEStronglyMeasurable (fun u => scoreMeanOver S f k (boxSide ℓ.side K k) (stageState T k (boxSide ℓ.side K k) u))
        (markedSampleLaw T β k (boxSide ℓ.side K k)))
    (hNq : ∀ f : FinePlaquetteFunction,
      Integrable (fun u => scoreMeanOver S f k (boxSide ℓ.side K k) (stageState T k (boxSide ℓ.side K k) u) ^ 32)
        (markedSampleLaw T β k (boxSide ℓ.side K k)) ∧
      ∫ u, scoreMeanOver S f k (boxSide ℓ.side K k) (stageState T k (boxSide ℓ.side K k) u) ^ 32
        ∂(markedSampleLaw T β k (boxSide ℓ.side K k)) ≤ M)
    (I : Finset (Fin p)) :
    |∫ U, ∏ i ∈ I, (smearedObservable ℓ.side K (φ i) U - unitTorusMean ℓ.side K β (φ i)) ∂unitTorusMeasure ℓ.side K β -
        ∫ u, ∏ i ∈ I, centeredBoxResponse T β S.coeffs K k (φ i) u ∂stageLaw T β K k| ≤
      2 ^ 32 * ((1 + Cx * (4 * lengthInSites ℓ.side K k d) ^ 4 * M) ^ 32 *
        (2 * (Cm * 1024 * (4 * C₀) ^ 32 * (4 * (ℓ.side : ℝ)) ^ 136 *
        ((138).factorial / (ℓ.rt / 2 ^ 11) ^ 138) * Real.exp (-(4 * ℓ.rt * (clusterRange (x k) : ℝ)))) *
          (1 + 32 * M))) := by
  have hodd : Odd ℓ.side := hf.L_odd
  have hL16 : 2 ^ 16 ≤ ℓ.side := hf.L_ge
  have hLr : (2 : ℝ) ≤ (ℓ.side : ℝ) := by
    have : (2 : ℕ) ≤ ℓ.side := by omega
    exact_mod_cast this
  have hL3 : 3 ≤ ℓ.side := by omega
  have hfl := hf.depth_lt
  have hkle : k ≤ K := hkK.le
  obtain ⟨hprob, hle, hbot, -, -, -⟩ := hT ℓ hf hfl T hcut hcoin β S.coeffs k (boxSide ℓ.side K k)
  set n₀ : ℝ := lengthInSites ℓ.side K k d with hn₀
  set r : ℝ := (clusterRange (x k) : ℝ) with hrdef
  have hn₀1 : 1 ≤ n₀ := by nlinarith
  let v : ℕ → ℝ := fun u => n₀ * (ℓ.side : ℝ) ^ (k - 1 - u)
  let D : ℕ → ℝ := fun u => v u / 2 - 5
  let A : ℕ → ℝ := fun u => (4 * v u * (ℓ.side : ℝ)) ^ 4
  have hvnum : ∀ u, 2 ^ 10 * (r + (((k - 1 - u : ℕ) : ℝ) + 1)) ≤ D u ∧ 8 < D u ∧ 2 ^ 12 * r ≤ v u ∧
      (2 : ℝ) ^ (k - 1 - u) ≤ v u := fun u => level_scale_bounds hfar hr hLr (k - 1 - u)
  have hcond : ∀ u < k, 2 ^ 10 * (clusterRange (x u) : ℝ) ≤ D u ∧ 8 < D u ∧
      D u + 5 ≤ d / 2 * (ℓ.side : ℝ) ^ (K - (u + 1)) ∧ (2 * (d * (ℓ.side : ℝ) ^ (K - u)) + 2) ^ 4 ≤ A u := by
    intro u hu
    obtain ⟨h1, h2, h3, -⟩ := hvnum u
    have hK1 : K - (u + 1) = (K - k) + (k - 1 - u) := by omega
    have hK2 : K - u = (K - k) + (k - 1 - u) + 1 := by omega
    have hvu : d * (ℓ.side : ℝ) ^ (K - (u + 1)) = v u := by
      show _ = lengthInSites ℓ.side K k d * (ℓ.side : ℝ) ^ (k - 1 - u)
      unfold lengthInSites
      rw [hK1, pow_add]
      ring
    have hvL : d * (ℓ.side : ℝ) ^ (K - u) = v u * (ℓ.side : ℝ) := by
      rw [hK2, pow_succ, ← hK1, ← mul_assoc, hvu]
    have hrange := clusterRange_le_add x k hstep (k - u) u (by omega)
    have hrr : (clusterRange (x u) : ℝ) ≤ r + (((k - 1 - u : ℕ) : ℝ) + 1) := by
      have e : k - u = (k - 1 - u) + 1 := by omega
      rw [e] at hrange
      have h9 : ((clusterRange (x u) : ℕ) : ℝ) ≤ ((clusterRange (x k) + ((k - 1 - u) + 1) : ℕ) : ℝ) :=
        Nat.cast_le.mpr hrange
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_one] at h9
      exact h9
    refine ⟨?_, h2, ?_, ?_⟩
    · have : 2 ^ 10 * (clusterRange (x u) : ℝ) ≤ 2 ^ 10 * (r + (((k - 1 - u : ℕ) : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hrr (by positivity)
      linarith
    · have e : d / 2 * (ℓ.side : ℝ) ^ (K - (u + 1)) = v u / 2 := by
        rw [← hvu]
        ring
      rw [e]
      show v u / 2 - 5 + 5 ≤ _
      linarith
    · rw [hvL]
      have hvp : 1 ≤ v u := by nlinarith
      have hvL1 : 1 ≤ v u * (ℓ.side : ℝ) := by nlinarith
      show _ ≤ (4 * v u * (ℓ.side : ℝ)) ^ 4
      exact pow_le_pow_left₀ (by nlinarith) (by nlinarith) 4
  obtain ⟨hap, hcnt⟩ := separated_and_counted hWt hodd hd0 hd hv hφ K x D A k (boxSide ℓ.side K k) hkle rfl hcond
  have wt := hWt ℓ.side hodd K d vt hd0 hd hv p φ hφ k (boxSide ℓ.side K k) hkle rfl
  let f : Fin p → FinePlaquetteFunction := fun i b => periodizeUnitTorus (φ i) fun a => b a / (ℓ.side : ℝ) ^ K
  let h : Fin p → PlaquetteWeight (fineSide ℓ.side k (boxSide ℓ.side K k)) := fun i => unitTorusWeight ℓ.side K k (φ i)
  have hbw : ∀ i, fineWeight (f i) (fineSide ℓ.side k (boxSide ℓ.side K k)) = h i := fun i => (wt.2.2.2.2 i).symm
  have hs : ∀ i, weightNorm ℓ.side k (h i) ≤ 1 := by
    intro i
    refine max_le (wt.1 i) ((wt.2.1 i).trans ?_)
    have : vt * (d * (ℓ.side : ℝ) ^ (K - k)) = vt * n₀ := rfl
    rw [this, div_le_one (by nlinarith)]
    exact hvt
  have hs' : ∀ i, weightNorm ℓ.side k (fineWeight (f i) (fineSide ℓ.side k (boxSide ℓ.side K k))) ≤ 1 := fun i => by
    rw [hbw i]
    exact hs i
  set Bc : ℝ := Cm * 1024 * (4 * C₀) ^ 32 * (4 * (ℓ.side : ℝ)) ^ 136 * ((138).factorial / (ℓ.rt / 2 ^ 11) ^ 138) *
    Real.exp (-(4 * ℓ.rt * r)) with hBc
  have hCm0 : 0 ≤ Cm := (hCm 0 (by norm_num)).1.trans (hCm 0 (by norm_num)).2
  have hrt := hf.rt_pos
  have hBc0 : 0 ≤ Bc := by positivity
  have hErr : ∀ (q : ℕ) (idx : Fin q → Fin p), q ≤ 32 →
      separationError ℓ (Cp q) C₀ D k (boxSide ℓ.side K k) (fun j => h (idx j)) ≤ 2 * Bc := by
    intro q idx hq
    have hc1 := separationError_le_sum (Cp q) C₀ (hCm q hq).1 (by linarith) A D k (boxSide ℓ.side K k)
      (fun j => h (idx j)) (supportsCountedBelow_comp A idx k _ h hcnt)
    refine hc1.trans ?_
    have hterm : ∀ u ∈ Finset.range k, Cp q * ((q : ℝ) * A u) ^ 2 * Real.exp (-(ℓ.rt * D u / 2 ^ 8)) *
        (4 * C₀ * A u) ^ q ≤ Bc * (1 / 2 : ℝ) ^ (k - 1 - u) := by
      intro u _
      obtain ⟨-, -, h3, h4⟩ := hvnum u
      have h5 := level_term_le (rt := ℓ.rt) (Cq := Cp q) (C₀ := C₀) (Lr := (ℓ.side : ℝ)) (v := v u) (r := r) hrt
        (hCm q hq).1 hC₀ hLr h3 (by linarith) hq
      refine h5.trans ?_
      have hvp : 0 < v u := lt_of_lt_of_le (by positivity) h4
      have hv1 : 1 ≤ v u := by
        have : (1 : ℝ) ≤ 2 ^ (k - 1 - u) := one_le_pow₀ (by norm_num)
        linarith
      have hinv : 1 / v u ^ 2 ≤ (1 / 2 : ℝ) ^ (k - 1 - u) := by
        rw [one_div_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
        nlinarith
      have hB1 : Cp q * 1024 * (4 * C₀) ^ 32 * (4 * (ℓ.side : ℝ)) ^ 136 * ((138).factorial / (ℓ.rt / 2 ^ 11) ^ 138) *
          Real.exp (-(4 * ℓ.rt * r)) ≤ Bc := by
        rw [hBc]
        have hz : 0 ≤ 1024 * (4 * C₀) ^ 32 * (4 * (ℓ.side : ℝ)) ^ 136 * ((138).factorial / (ℓ.rt / 2 ^ 11) ^ 138) *
            Real.exp (-(4 * ℓ.rt * r)) := by positivity
        have := mul_le_mul_of_nonneg_right (hCm q hq).2 hz
        calc _ = Cp q * (1024 * (4 * C₀) ^ 32 * (4 * (ℓ.side : ℝ)) ^ 136 *
              ((138).factorial / (ℓ.rt / 2 ^ 11) ^ 138) * Real.exp (-(4 * ℓ.rt * r))) := by ring
          _ ≤ _ := this
          _ = _ := by ring
      calc _ = (Cp q * 1024 * (4 * C₀) ^ 32 * (4 * (ℓ.side : ℝ)) ^ 136 * ((138).factorial / (ℓ.rt / 2 ^ 11) ^ 138) *
            Real.exp (-(4 * ℓ.rt * r))) * (1 / v u ^ 2) := by ring
        _ ≤ Bc * (1 / v u ^ 2) := mul_le_mul_of_nonneg_right hB1 (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hinv hBc0
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, Finset.sum_range_reflect (fun j => (1 / 2 : ℝ) ^ j) k, mul_comm]
    exact mul_le_mul_of_nonneg_right (sum_geometric_two_le k) hBc0
  let Mk : Fin p → MarkedSample ℓ k (boxSide ℓ.side K k) → ℝ := fun i u =>
    chainMark ℓ (fun j => (T.stage j).coupling) S.coeffs k (boxSide ℓ.side K k) (h i)
      (forgetMarks ℓ k (boxSide ℓ.side K k) u)
  let R : Fin p → MarkedSample ℓ k (boxSide ℓ.side K k) → ℝ := fun i =>
    WeightedResponses.response T β S.coeffs k (boxSide ℓ.side K k) (h i)
  let Nf : Fin p → MarkedSample ℓ k (boxSide ℓ.side K k) → ℝ := fun i u =>
    scoreMeanOver S (f i) k (boxSide ℓ.side K k) (stageState T k (boxSide ℓ.side K k) u)
  let κ : Fin p → ℝ := fun i => centering S (f i) k (boxSide ℓ.side K k)
  have hcompl : ∀ i u, completedCentered S (f i) k (boxSide ℓ.side K k) u = Mk i u - κ i := by
    intro i u
    show completedObservable T S.coeffs k (boxSide ℓ.side K k)
      (fineWeight (f i) (fineSide ℓ.side k (boxSide ℓ.side K k))) u - _ = _
    rw [hbw i, completedObservable_eq_chainMark]
  have hMm : ∀ i, Measurable (Mk i) := fun i => (chainMark_measurable_bounded hSc hf _ S.coeffs k _ (h i)).1
  have hMb : ∀ i, ∃ C : ℝ, ∀ w, |Mk i w| ≤ C := fun i => (chainMark_measurable_bounded hSc hf _ S.coeffs k _ (h i)).2
  have hMI : ∀ i, Integrable (Mk i) (markedSampleLaw T β k (boxSide ℓ.side K k)) := by
    intro i
    obtain ⟨C, hC⟩ := hMb i
    exact Integrable.of_bound (hMm i).aestronglyMeasurable C (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs]
      exact hC w)
  have hresp : ∀ i, ∀ᵐ w ∂(markedSampleLaw T β k (boxSide ℓ.side K k)), R i w - κ i =
      ((markedSampleLaw T β k (boxSide ℓ.side K k))[fun w' => Mk i w' - κ i | stageSigma T k (boxSide ℓ.side K k)]) w := by
    intro i
    have h1 := hMk ℓ hf hfl T hcut hcoin β S.coeffs k (boxSide ℓ.side K k) (h i)
    have h2 := condExp_sub (m := stageSigma T k (boxSide ℓ.side K k)) (hMI i) (integrable_const (κ i))
    have h3 : (markedSampleLaw T β k (boxSide ℓ.side K k))[fun _ => κ i | stageSigma T k (boxSide ℓ.side K k)] =
        fun _ => κ i :=
      condExp_const hle (κ i)
    filter_upwards [h1, h2] with w e1 e2
    have e3 : ((markedSampleLaw T β k (boxSide ℓ.side K k))[fun w' => Mk i w' - κ i |
          stageSigma T k (boxSide ℓ.side K k)]) w =
        ((markedSampleLaw T β k (boxSide ℓ.side K k))[Mk i | stageSigma T k (boxSide ℓ.side K k)]) w - κ i := by
      have e4 : (fun w' => Mk i w' - κ i) = Mk i - fun _ => κ i := rfl
      rw [e4, e2, Pi.sub_apply, h3]
    rw [e3]
    show WeightedResponses.response T β S.coeffs k (boxSide ℓ.side K k) (h i) w - κ i = _
    rw [e1]
  have hfitR : ∀ᵐ a ∂(markedSampleLaw T β k (boxSide ℓ.side K k)), ∀ i,
      fittedResponse S (f i) k (boxSide ℓ.side K k) (stageState T k (boxSide ℓ.side K k) a) = R i a - κ i := by
    refine ae_all_iff.mpr fun i => ?_
    filter_upwards [hfitted (f i), hresp i] with a e1 e2
    rw [e1, e2]
    have e3 : completedCentered S (f i) k (boxSide ℓ.side K k) = fun w' => Mk i w' - κ i := funext (hcompl i)
    rw [e3]
  have hprod : ∀ J : Finset (Fin p), ∀ᵐ w ∂(markedSampleLaw T β k (boxSide ℓ.side K k)),
      |((markedSampleLaw T β k (boxSide ℓ.side K k))[fun w' => ∏ i ∈ J, (Mk i w' - κ i) |
          stageSigma T k (boxSide ℓ.side K k)]) w -
        ∏ i ∈ J, (R i w - κ i)| ≤ (2 * Bc) * ∏ i ∈ J, Nf i w := by
    intro J
    let e : Fin J.card ≃ {i // i ∈ J} := J.equivFin.symm
    let idx : Fin J.card → Fin p := fun j => (e j).1
    have hidx : Function.Injective idx := fun a b h => e.injective (Subtype.ext h)
    have hre : ∀ g : Fin p → ℝ, ∏ i ∈ J, g i = ∏ j : Fin J.card, g (idx j) := by
      intro g
      rw [← Finset.prod_coe_sort J g]
      exact (Equiv.prod_comp e fun i : {i // i ∈ J} => g i.1).symm
    have hJc : J.card ≤ 32 := (Finset.card_le_univ J).trans (by simpa using hp)
    have hfam : (fun j => fineWeight (f (idx j)) (fineSide ℓ.side k (boxSide ℓ.side K k))) = fun j => h (idx j) :=
      funext fun j => hbw (idx j)
    have hapJ : SeparatedAlongTower ℓ x D k (boxSide ℓ.side K k)
        (fun j => fineWeight (f (idx j)) (fineSide ℓ.side k (boxSide ℓ.side K k))) := by
      rw [hfam]
      exact separated_comp x D idx hidx k _ h hap
    have hm := hmany J.card (fun j => f (idx j)) D (fun j => hs' _) hapJ
    filter_upwards [hm, hfitR] with u hu hfu
    have e1 : conditionalProduct S β (fun j => f (idx j)) Finset.univ k (boxSide ℓ.side K k) u =
        ((markedSampleLaw T β k (boxSide ℓ.side K k))[fun w' => ∏ i ∈ J, (Mk i w' - κ i) |
          stageSigma T k (boxSide ℓ.side K k)]) u := by
      have e4 : (fun w' => ∏ j ∈ Finset.univ, completedCentered S (f (idx j)) k (boxSide ℓ.side K k) w') =
          fun w' => ∏ i ∈ J, (Mk i w' - κ i) := by
        funext w'
        rw [hre fun i => Mk i w' - κ i]
        exact Finset.prod_congr rfl fun j _ => hcompl (idx j) w'
      unfold conditionalProduct
      rw [e4]
    have e2 : ∏ j, fittedResponse S (f (idx j)) k (boxSide ℓ.side K k) (stageState T k (boxSide ℓ.side K k) u) =
        ∏ i ∈ J, (R i u - κ i) := by
      rw [hre fun i => R i u - κ i]
      exact Finset.prod_congr rfl fun j _ => hfu (idx j)
    have e3 : ∏ j, scoreMeanOver S (f (idx j)) k (boxSide ℓ.side K k) (stageState T k (boxSide ℓ.side K k) u) =
        ∏ i ∈ J, Nf i u :=
      (hre fun i => Nf i u).symm
    rw [e1, e2, e3, hfam] at hu
    refine hu.trans (mul_le_mul_of_nonneg_right (hErr J.card idx hJc) (Finset.prod_nonneg fun i _ => ?_))
    linarith [hone (f i) u]
  have hG : ∀ i, ∀ᵐ u ∂(markedSampleLaw T β k (boxSide ℓ.side K k)), |R i u - κ i| ≤ (Cx * (4 * n₀) ^ 4) * Nf i u := by
    intro i
    filter_upwards [hbound (f i) (hs' i), hfitR] with u hu hfu
    rw [← hfu i]
    refine hu.trans (mul_le_mul_of_nonneg_right ?_ (by linarith [hone (f i) u]))
    refine mul_le_mul_of_nonneg_left ?_ hCx
    have h1 : ((functionSites ℓ.side (f i) k (boxSide ℓ.side K k)).card : ℝ) =
        ((weightSupportSites ℓ.side k (boxSide ℓ.side K k) (h i)).card : ℝ) := by
      show ((weightSupportSites ℓ.side k (boxSide ℓ.side K k)
        (fineWeight (f i) (fineSide ℓ.side k (boxSide ℓ.side K k)))).card : ℝ) = _
      rw [hbw i]
    rw [h1]
    refine (wt.2.2.1 i).trans ?_
    exact pow_le_pow_left₀ (by positivity) (by
      have : d * (ℓ.side : ℝ) ^ (K - k) = n₀ := rfl
      rw [this]
      nlinarith) 4
  obtain ⟨hmeans, hcore⟩ := centered_products_compare hle hp Mk R Nf κ hMm hMb hresp (fun i u => hone (f i) u)
    (fun i => hNm (f i)) M (2 * Bc) (Cx * (4 * n₀) ^ 4) hM0 (by positivity) (by positivity) (fun i => (hNq (f i)).1)
    (fun i => (hNq (f i)).2) hprod hG I
  have hb := isBoundedBorelCompactlySupported_of_bump hd0 hv hφ
  have hmean : ∀ i, unitTorusMean ℓ.side K β (φ i) =
      ∫ u, R i u ∂(markedSampleLaw T β k (boxSide ℓ.side K k)) := by
    intro i
    have h1 := integral_prod_smeared_eq_bottom hW hI hodd hL3 (by omega) hkle T β hbot φ hb (fun _ => 0) {i}
    have h2 := integral_prod_curvature_eq_chainMark hS hT hSc hf T hcut hcoin β S.coeffs x D k (boxSide ℓ.side K k)
      h hap (fun _ => 0) {i}
    simp only [Finset.prod_singleton, sub_zero] at h1 h2
    rw [hmeans i]
    exact h1.trans h2
  have e1 : ∫ U, ∏ i ∈ I, (smearedObservable ℓ.side K (φ i) U - unitTorusMean ℓ.side K β (φ i))
        ∂unitTorusMeasure ℓ.side K β =
      ∫ u, ∏ i ∈ I, (Mk i u - ∫ u', R i u' ∂(markedSampleLaw T β k (boxSide ℓ.side K k)))
        ∂(markedSampleLaw T β k (boxSide ℓ.side K k)) := by
    simp only [hmean]
    exact (integral_prod_smeared_eq_bottom hW hI hodd hL3 (by omega) hkle T β hbot φ hb _ I).trans
      (integral_prod_curvature_eq_chainMark hS hT hSc hf T hcut hcoin β S.coeffs x D k (boxSide ℓ.side K k) h hap _ I)
  rw [e1]
  exact hcore
end Tower
section Scores
private theorem siteScore_nonneg {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) {n : ℕ} (Y : Finset (TorusSite n))
    (ω : Y → Ω) (y : TorusSite n) : 0 ≤ siteScore s Y ω y := by apply _root_.YangMills.SharedProofs.p22275 <;> assumption
end Scores
section Final
open InfiniteLattice (AmbientSpace)
private theorem le_clusterRange {x A : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (h : A ^ 100 ≤ x) : A ≤ (clusterRange x : ℝ) := by
  have h1 : (A ^ 100) ^ ((1 : ℝ) / 100) ≤ x ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow (by positivity) h (by norm_num)
  have h2 : (A ^ 100) ^ ((1 : ℝ) / 100) = A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
    norm_num
  rw [h2] at h1
  exact h1.trans (Nat.le_ceil _)
private theorem clusterRange_le_two_mul {x : ℝ} (hx : 1 ≤ x) : (clusterRange x : ℝ) ≤ 2 * x := by
  have h1 : x ^ ((1 : ℝ) / 100) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  rw [Real.rpow_one] at h1
  have h2 : (clusterRange x : ℝ) < x ^ ((1 : ℝ) / 100) + 1 := Nat.ceil_lt_add_one (by positivity)
  linarith
abbrev _root_.YangMills.SharedProofs.p24708 := @clusterRange_le_two_mul
private def finalConstant (L Cx C₀ M Cm rt : ℝ) : ℝ :=
  2 ^ 32 * ((1 + Cx * (2 ^ 16 * L) ^ 4 * M) ^ 32 * (2 * (Cm * 1024 * (4 * C₀) ^ 32 * (4 * L) ^ 136 *
    ((138).factorial / (rt / 2 ^ 11) ^ 138)) * (1 + 32 * M)))
private theorem final_bound_le {L Cx C₀ M Cm rt x n₀ r E : ℝ} (hL : 1 ≤ L) (hCx : 0 ≤ Cx) (hC₀ : 0 ≤ C₀) (hM : 0 ≤ M)
    (hCm : 0 ≤ Cm) (hrt : 0 < rt)
    (hx : 1 ≤ x) (hxn : finalConstant L Cx C₀ M Cm rt ≤ x) (hn0 : 0 ≤ n₀) (hn : n₀ ≤ 2 ^ 13 * L * r) (hr : r ≤ 2 * x)
    (hE : 0 ≤ E) :
    2 ^ 32 * ((1 + Cx * (4 * n₀) ^ 4 * M) ^ 32 * (2 * (Cm * 1024 * (4 * C₀) ^ 32 * (4 * L) ^ 136 *
        ((138).factorial / (rt / 2 ^ 11) ^ 138) * E) * (1 + 32 * M))) ≤ x ^ 129 * E := by
  set Z : ℝ := 1 + Cx * (2 ^ 16 * L) ^ 4 * M with hZ
  set W : ℝ := Cm * 1024 * (4 * C₀) ^ 32 * (4 * L) ^ 136 * ((138).factorial / (rt / 2 ^ 11) ^ 138) with hW
  have h4 : 4 * n₀ ≤ 2 ^ 16 * L * x := by nlinarith
  have h5 : (4 * n₀) ^ 4 ≤ (2 ^ 16 * L) ^ 4 * x ^ 4 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h4 4
  have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx
  have h6 : 1 + Cx * (4 * n₀) ^ 4 * M ≤ Z * x ^ 4 := by
    have h7 : Cx * (4 * n₀) ^ 4 * M ≤ Cx * ((2 ^ 16 * L) ^ 4 * x ^ 4) * M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hCx) hM
    rw [hZ]
    nlinarith
  have h9 : (1 + Cx * (4 * n₀) ^ 4 * M) ^ 32 ≤ Z ^ 32 * x ^ 128 := by
    have := pow_le_pow_left₀ (by positivity) h6 32
    calc _ ≤ (Z * x ^ 4) ^ 32 := this
      _ = _ := by ring
  have hnum : 2 ^ 32 * (Z ^ 32 * (2 * W * (1 + 32 * M))) ≤ x := hxn
  have hnn : 0 ≤ 2 * W * (1 + 32 * M) * E := by positivity
  calc 2 ^ 32 * ((1 + Cx * (4 * n₀) ^ 4 * M) ^ 32 * (2 * (W * E) * (1 + 32 * M)))
      = 2 ^ 32 * ((1 + Cx * (4 * n₀) ^ 4 * M) ^ 32 * (2 * W * (1 + 32 * M) * E)) := by ring
    _ ≤ 2 ^ 32 * ((Z ^ 32 * x ^ 128) * (2 * W * (1 + 32 * M) * E)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h9 hnn) (by positivity)
    _ = (2 ^ 32 * (Z ^ 32 * (2 * W * (1 + 32 * M)))) * (x ^ 128 * E) := by ring
    _ ≤ x * (x ^ 128 * E) := mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = x ^ 129 * E := by ring
end Final
section Statement
open InfiniteLattice (AmbientSpace)
private theorem followsFlow_mono {Tb : ParameterAssignment} {y : ℝ} {T : WeightedResponses.StageTower (Tb.stepParameters y)}
    {S : ScoredStageTower T} {β : ℝ} {tp tq : ℕ}
    (h : S.FollowsFlow β tp) (hle : tq ≤ tp) : S.FollowsFlow β tq := by apply _root_.YangMills.SharedProofs.p16981 <;> assumption
private theorem sideBelow_eq_mul_pow (L : ℕ) : ∀ k n, sideBelow L k n = n * L ^ k := by apply _root_.YangMills.SharedProofs.p47689 <;> assumption
private theorem abs_fittedResponse_le {ℓ : StepParameters} {T : WeightedResponses.StageTower ℓ} (S : ScoredStageTower T)
    (F : FinePlaquetteFunction) (k n : ℕ) [NeZero n] {C₀ : ℝ}
    (hC : 0 ≤ C₀) (hs0 : ∀ w, 0 ≤ (S.setup k).score w) (q : StageState T k n)
    (hh : ∀ z, |centeredHullResponse (S.setup k).cold (S.setup k).hull n z q.1 q.2.1 q.2.2 (fineWeight F _)| ≤
      C₀ + siteScore (S.setup k).score q.2.1 q.2.2 z) :
    |fittedResponse S F k n q| ≤ (C₀ + 1) * ((functionSites ℓ.side F k n).card : ℝ) * scoreMeanOver S F k n q := by apply _root_.YangMills.DeltaSharedProofs.p501280 <;> assumption
set_option maxHeartbeats 3200000 in
theorem centeredProductsAtLevelStatement_holds (hS : ScoresPreserveCorrelations)
    (hT : TwoPointByTotalCovarianceStatement)
    (hSc : BondScoreProperties) (hWt : markWeightsOnUnitTorusStatement)
    (hW : LawInAState.unitTorusMomentsViaWeightsStatement) (hI : unitTorusObservablesIntegrableStatement)
    (hMk : ResponseIsConditionalExpectation) (hM : separatedProductsStatement)
    (hF : fittedResponseIsConditionalMeanStatement) (hSt : flowStatesAreGroundsStatement)
    (hMj : WeightedObservables.majorantMomentsStatement) (hLv : separationLevelStatement)
    (hGr : couplingAtSeparation_tendsto_statement) : centeredProductsAtLevelStatement := by
  unfold separatedProductsStatement at hM
  unfold fittedResponseIsConditionalMeanStatement at hF
  unfold flowStatesAreGroundsStatement at hSt
  unfold WeightedObservables.majorantMomentsStatement at hMj
  unfold separationLevelStatement at hLv
  unfold couplingAtSeparation_tendsto_statement at hGr
  unfold centeredProductsAtLevelStatement
  refine HoldsForShapes.mono (HoldsForShapes.params.and ((HoldsForShapes.of_response hM).and
    ((HoldsForShapes.of_response hF).and ((HoldsForShapes.of_response hSt).and
      ((HoldsForShapes.of_response hMj).and ((HoldsForShapes.of_holdsOnParameters hLv).and
        (HoldsForShapes.of_holdsOnParameters hGr))))))) ?_
  rintro Tb y Kr Xi vt ⟨⟨hD, hy, hRow, hKr, hXi, hv, hv1⟩, hMy, hFy, hSy, hMo, hLy, hGy⟩
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y hy
  choose Cp hCp0 hCp using hMy
  obtain ⟨C32, hC32, hM32⟩ := hMo 32
  obtain ⟨C1, hC1, hM1⟩ := hMo 1
  have hXi1 : 1 ≤ Xi := by
    have h1 := hfit.y₁_ge
    have h2 := hfit.B_pos
    linarith
  have hLnat : 2 ≤ (Tb.stepParameters y).side := by
    have := hfit.L_ge
    omega
  have hLr : (1 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) := by
    have : 1 ≤ (Tb.stepParameters y).side := by omega
    exact_mod_cast this
  obtain ⟨Nm, hNmdef⟩ : ∃ v : ℕ, v = (Tb.stepParameters y).n₀ + 1 := ⟨_, rfl⟩
  have hC₀ : 1 ≤ Kr.C₀ := by
    have h1 := hKr.C₀_eq
    have h2 := hfit.a_ge
    have h3 := hKr.N₀_nonneg
    have h4 := hKr.Kc_ge
    linarith
  set Mb : ℝ := C32 * Real.exp (C32 * (1 + Real.log (2 ^ Nm * Xi)) *
    ((2 * (Tb.stepParameters y).side ^ Nm : ℕ) : ℝ) ^ 4) with hMb
  set Nn : ℝ := finalConstant ((Tb.stepParameters y).side : ℝ) (Kr.C₀ + 1) Kr.C₀ (max Mb 1)
    (∑ q ∈ Finset.range 33, Cp q) (Tb.stepParameters y).rt with hNn
  set Af : ℝ := max (1 / vt) (max (((Tb.stepParameters y).side : ℝ) ^ Nm)
    (max (((Tb.stepParameters y).side : ℝ) * ((Tb.stepParameters y).n₀ : ℝ)) 2)) with hAf
  obtain ⟨d₁, hd₁, hgrow⟩ := hGy Xi hXi (max (max 1 Nn) (Af ^ 100))
  refine ⟨129, min d₁ (1 / 4), lt_min hd₁ (by norm_num), ?_⟩
  intro d hd0 hd K β al T hC p φ hp hφ I
  have hd1 : d ≤ d₁ := hd.trans (min_le_left _ _)
  have hd4 : d ≤ 1 / 4 := hd.trans (min_le_right _ _)
  have hX := hgrow d hd0 hd1 K β hC.isFlowDatum hC.minimalCutoff_le
  obtain ⟨hfar, hlt, hn⟩ := hLy Xi hXi d hd0 (by linarith) K β hC.isFlowDatum hC.minimalCutoff_le
  obtain ⟨S, hSK, hrun, rfl⟩ := hC.scored
  suffices H : ∀ k : ℕ, IsSeparatedAt (Tb.stepParameters y) β K d k → k < K →
      lengthInSites (Tb.stepParameters y).side K k d ≤
        2 ^ 13 * ((Tb.stepParameters y).side : ℝ) * (clusterRange (flowCouplings (Tb.stepParameters y) β k) : ℝ) →
      max (max 1 Nn) (Af ^ 100) ≤ flowCouplings (Tb.stepParameters y) β k →
      |∫ U, ∏ i ∈ I, (smearedObservable (Tb.stepParameters y).side K (φ i) U -
              unitTorusMean (Tb.stepParameters y).side K β (φ i)) ∂unitTorusMeasure (Tb.stepParameters y).side K β -
          ∫ u, ∏ i ∈ I, centeredBoxResponse T β S.coeffs K k (φ i) u ∂stageLaw T β K k| ≤
        markError (Tb.stepParameters y) 129 (flowCouplings (Tb.stepParameters y) β k) from
    H _ hfar hlt hn hX
  intro k hfar hlt hn hX
  have hx1 : 1 ≤ flowCouplings (Tb.stepParameters y) β k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hxn : Nn ≤ flowCouplings (Tb.stepParameters y) β k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hx3 : Af ^ 100 ≤ flowCouplings (Tb.stepParameters y) β k := le_trans (le_max_right _ _) hX
  have hx0 : 0 ≤ flowCouplings (Tb.stepParameters y) β k := by linarith
  have hAf0 : 0 ≤ Af := le_trans (by positivity) (le_max_left _ _)
  have hrA : Af ≤ (clusterRange (flowCouplings (Tb.stepParameters y) β k) : ℝ) := le_clusterRange hx0 hAf0 hx3
  have hrv : 1 / vt ≤ (clusterRange (flowCouplings (Tb.stepParameters y) β k) : ℝ) := le_trans (le_max_left _ _) hrA
  have hrP : ((Tb.stepParameters y).side : ℝ) ^ Nm ≤ (clusterRange (flowCouplings (Tb.stepParameters y) β k) : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hrA
  have hrL : ((Tb.stepParameters y).side : ℝ) * ((Tb.stepParameters y).n₀ : ℝ) ≤
      (clusterRange (flowCouplings (Tb.stepParameters y) β k) : ℝ) :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hrA
  have hr2 : (2 : ℝ) ≤ (clusterRange (flowCouplings (Tb.stepParameters y) β k) : ℝ) :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hrA
  have hfar' : 2 ^ 12 * (clusterRange (flowCouplings (Tb.stepParameters y) β k) : ℝ) ≤
      lengthInSites (Tb.stepParameters y).side K k d := hfar
  have hLp : (0 : ℝ) < (Tb.stepParameters y).side := by linarith
  have hpowP : (0 : ℝ) < ((Tb.stepParameters y).side : ℝ) ^ (K - k) := by positivity
  have hpow : 2 ^ 14 * (clusterRange (flowCouplings (Tb.stepParameters y) β k) : ℝ) ≤
      ((Tb.stepParameters y).side : ℝ) ^ (K - k) := by
    have h1 : lengthInSites (Tb.stepParameters y).side K k d = d * ((Tb.stepParameters y).side : ℝ) ^ (K - k) := rfl
    have h2 : d * ((Tb.stepParameters y).side : ℝ) ^ (K - k) ≤ 1 / 4 * ((Tb.stepParameters y).side : ℝ) ^ (K - k) :=
      mul_le_mul_of_nonneg_right hd4 hpowP.le
    nlinarith
  have hNmK : Nm < K - k := by
    by_contra hcon
    have h1 : ((Tb.stepParameters y).side : ℝ) ^ (K - k) ≤ ((Tb.stepParameters y).side : ℝ) ^ Nm :=
      pow_le_pow_right₀ hLr (by omega)
    have h2 : (0 : ℝ) < ((Tb.stepParameters y).side : ℝ) ^ Nm := by positivity
    nlinarith
  have hblock : IsBlockTorusSide (Tb.stepParameters y) (boxSide (Tb.stepParameters y).side K k) := by
    refine ⟨?_, ?_⟩
    · have h1 : K - k = (K - k - 1) + 1 := by omega
      show (Tb.stepParameters y).side ∣ 2 * (Tb.stepParameters y).side ^ (K - k)
      rw [h1, pow_succ]
      exact ⟨2 * (Tb.stepParameters y).side ^ (K - k - 1), by ring⟩
    · have h1 : (((Tb.stepParameters y).side * (Tb.stepParameters y).n₀ : ℕ) : ℝ) ≤
          ((2 * (Tb.stepParameters y).side ^ (K - k) : ℕ) : ℝ) := by
        push_cast
        nlinarith
      exact_mod_cast h1
  have hrunk : S.FollowsFlow β k := followsFlow_mono hrun (by omega)
  have hreach : ∀ t ≤ K, CouplingsAboveFloor (Tb.stepParameters y) β t := fun t ht j hj =>
    hC.isFlowDatum.le_coupling j (by omega)
  have hreachk := hreach k hlt.le
  have hhull := hSy β T S k hSK hrunk hreachk
  have hlive := (hhull.2 (boxSide (Tb.stepParameters y).side K k) hblock).1 k le_rfl
  have hresp := hrunk.isAdmissible k le_rfl
  have hKK : (S.setup k).responseParams = Kr := (hrunk.params_eq k).trans hSK
  have hs0 : ∀ w, 0 ≤ (S.setup k).score w := hresp.price.nonneg
  have ht : (T.stage k).toStepSetup.depth = k := (hrunk.isFlowStep k le_rfl).depth_eq
  obtain ⟨hprob, hle, -, -, -, -⟩ := hT (Tb.stepParameters y) hfit hfit.depth_lt T hC.isCutoff_bottom hC.marksMeasurable
    β S.coeffs k (boxSide (Tb.stepParameters y).side K k)
  have hbound : ∀ f : FinePlaquetteFunction,
      weightNorm (Tb.stepParameters y).side k
        (fineWeight f (fineSide (Tb.stepParameters y).side k (boxSide (Tb.stepParameters y).side K k))) ≤ 1 →
      ∀ᵐ a ∂(markedSampleLaw T β k (boxSide (Tb.stepParameters y).side K k)),
        |fittedResponse S f k (boxSide (Tb.stepParameters y).side K k)
            (stageState T k (boxSide (Tb.stepParameters y).side K k) a)| ≤
          (Kr.C₀ + 1) * ((functionSites (Tb.stepParameters y).side f k (boxSide (Tb.stepParameters y).side K k)).card : ℝ) *
            scoreMeanOver S f k (boxSide (Tb.stepParameters y).side K k)
              (stageState T k (boxSide (Tb.stepParameters y).side K k) a) := by
    intro f hsz
    have hsz' : weightNorm (Tb.stepParameters y).side (T.stage k).toStepSetup.depth
        (fineWeight f (fineSide (Tb.stepParameters y).side (T.stage k).toStepSetup.depth
          (boxSide (Tb.stepParameters y).side K k))) ≤ 1 := by
      rw [ht]
      exact hsz
    filter_upwards [hlive] with a ha
    refine abs_fittedResponse_le S f k _ (by linarith) hs0 _ fun z => ?_
    have h1 := hresp.bounds.size_hull (boxSide (Tb.stepParameters y).side K k) hblock z _ _ _ ha (fineWeight f _)
    rw [hKK] at h1
    refine h1.trans ?_
    have h2 : 0 ≤ Kr.C₀ + siteScore (S.setup k).score (stageState T k (boxSide (Tb.stepParameters y).side K k) a).2.1
        (stageState T k (boxSide (Tb.stepParameters y).side K k) a).2.2 z := by
      have := siteScore_nonneg hs0 (stageState T k (boxSide (Tb.stepParameters y).side K k) a).2.1
        (stageState T k (boxSide (Tb.stepParameters y).side K k) a).2.2 z
      linarith
    calc _ ≤ (Kr.C₀ + siteScore (S.setup k).score (stageState T k (boxSide (Tb.stepParameters y).side K k) a).2.1
          (stageState T k (boxSide (Tb.stepParameters y).side K k) a).2.2 z) * 1 := mul_le_mul_of_nonneg_left hsz' h2
      _ = _ := mul_one _
  have hone : ∀ (f : FinePlaquetteFunction) (u), 1 ≤ scoreMeanOver S f k (boxSide (Tb.stepParameters y).side K k)
      (stageState T k (boxSide (Tb.stepParameters y).side K k) u) := by
    intro f u
    show 1 ≤ 1 + _ * _
    have h1 : 0 ≤ ∑ z ∈ functionSites (Tb.stepParameters y).side f k (boxSide (Tb.stepParameters y).side K k),
        siteScore (S.setup k).score (stageState T k (boxSide (Tb.stepParameters y).side K k) u).2.1
          (stageState T k (boxSide (Tb.stepParameters y).side K k) u).2.2 z :=
      Finset.sum_nonneg fun z _ => siteScore_nonneg hs0 _ _ _
    have h2 : 0 ≤ (((functionSites (Tb.stepParameters y).side f k
        (boxSide (Tb.stepParameters y).side K k)).card : ℝ))⁻¹ := by positivity
    have := mul_nonneg h2 h1
    linarith
  obtain ⟨k', hk'⟩ : ∃ v : ℕ, v = K - Nm - k := ⟨_, rfl⟩
  have hkk : k + k' = K - Nm := by omega
  have hrunT : S.FollowsFlow β (k + k') := followsFlow_mono hrun (by omega)
  have hreachT : CouplingsAboveFloor (Tb.stepParameters y) β (k + k') := hreach _ (by omega)
  have hblockT : IsBlockTorusSide (Tb.stepParameters y) (2 * (Tb.stepParameters y).side ^ Nm) := by
    refine ⟨Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) 2, ?_⟩
    have h1 : (Tb.stepParameters y).n₀ < (Tb.stepParameters y).side ^ (Tb.stepParameters y).n₀ :=
      Nat.lt_pow_self (by omega)
    have h2 : (Tb.stepParameters y).side ^ Nm =
        (Tb.stepParameters y).side * (Tb.stepParameters y).side ^ (Tb.stepParameters y).n₀ := by
      rw [hNmdef, pow_succ]
      ring
    rw [h2]
    nlinarith
  have hdown : ∀ i, i ≤ K → flowCouplings (Tb.stepParameters y) β (K - i) ≤ 2 ^ i * Xi := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa using hC.isFlowDatum.coupling_le_top
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have hj : K - (i + 1) + 1 = K - i := by omega
      have hst := hrun.isFlowStep (K - (i + 1)) (by omega)
      have h2 := hst.onFamily.isStep.2.1
      have e1 : (T.stage (K - (i + 1))).toStepSetup.coupling = flowCouplings (Tb.stepParameters y) β (K - (i + 1)) :=
        hst.coupling_eq
      have e2 : (T.stage (K - (i + 1))).toStepSetup.nextCoupling = flowCouplings (Tb.stepParameters y) β (K - i) := by
        rw [← hj]
        exact hst.nextCoupling_eq
      rw [e1, e2] at h2
      have h3 : 0 ≤ flowCouplings (Tb.stepParameters y) β (K - i) := by
        have := hC.isFlowDatum.le_coupling (K - i) (by omega)
        have := hfit.y₁_ge
        linarith
      rw [pow_succ]
      nlinarith
  have hxtop : flowCouplings (Tb.stepParameters y) β (k + k') ≤ 2 ^ Nm * Xi := by
    rw [hkk]
    exact hdown Nm (by omega)
  have hxtop1 : 1 ≤ flowCouplings (Tb.stepParameters y) β (k + k') := by
    have h1 := hC.isFlowDatum.le_coupling (k + k') (by omega)
    have h2 := hfit.y₁_ge
    linarith
  have hMbound : C32 * Real.exp (C32 * (1 + Real.log (flowCoupling (Tb.stepParameters y) β (k + k'))) *
      ((2 * (Tb.stepParameters y).side ^ Nm : ℕ) : ℝ) ^ 4) ≤ Mb := by
    have hlog : Real.log (flowCoupling (Tb.stepParameters y) β (k + k')) ≤ Real.log (2 ^ Nm * Xi) :=
      Real.log_le_log (lt_of_lt_of_le one_pos hxtop1) hxtop
    have hn4 : 0 ≤ ((2 * (Tb.stepParameters y).side ^ Nm : ℕ) : ℝ) ^ 4 := by positivity
    have h1 : C32 * (1 + Real.log (flowCoupling (Tb.stepParameters y) β (k + k'))) *
          ((2 * (Tb.stepParameters y).side ^ Nm : ℕ) : ℝ) ^ 4 ≤
        C32 * (1 + Real.log (2 ^ Nm * Xi)) * ((2 * (Tb.stepParameters y).side ^ Nm : ℕ) : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) hn4
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) (by linarith)
  have hbase : ∀ B : Finset (TorusSite (sideBelow (Tb.stepParameters y).side k' (2 * (Tb.stepParameters y).side ^ Nm))),
      B.Nonempty →
      (Integrable (fun u => meanSiteScore (S.setup k).score B (stageState T k _ u).2.1 (stageState T k _ u).2.2 ^ 32)
          (markedSampleLaw T β k (sideBelow (Tb.stepParameters y).side k' (2 * (Tb.stepParameters y).side ^ Nm))) ∧
        ∫ u, meanSiteScore (S.setup k).score B (stageState T k _ u).2.1 (stageState T k _ u).2.2 ^ 32
          ∂(markedSampleLaw T β k (sideBelow (Tb.stepParameters y).side k' (2 * (Tb.stepParameters y).side ^ Nm))) ≤
            max Mb 1) ∧
      AEStronglyMeasurable (fun u => meanSiteScore (S.setup k).score B (stageState T k _ u).2.1
          (stageState T k _ u).2.2)
        (markedSampleLaw T β k (sideBelow (Tb.stepParameters y).side k' (2 * (Tb.stepParameters y).side ^ Nm))) := by
    intro B hB
    obtain ⟨h1, h2⟩ := hM32 β T S k k' (2 * (Tb.stepParameters y).side ^ Nm) (fun _ => B) hSK hrunT hreachT hblockT
      (fun _ => hB)
    obtain ⟨h3, -⟩ := hM1 β T S k k' (2 * (Tb.stepParameters y).side ^ Nm) (fun _ => B) hSK hrunT hreachT hblockT
      (fun _ => hB)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one] at h1 h2 h3
    exact ⟨⟨h1, (h2.trans hMbound).trans (le_max_left _ _)⟩, h3.aestronglyMeasurable⟩
  have hside : sideBelow (Tb.stepParameters y).side k' (2 * (Tb.stepParameters y).side ^ Nm) =
      boxSide (Tb.stepParameters y).side K k := by
    rw [sideBelow_eq_mul_pow]
    show 2 * (Tb.stepParameters y).side ^ Nm * (Tb.stepParameters y).side ^ k' =
      2 * (Tb.stepParameters y).side ^ (K - k)
    have : K - k = Nm + k' := by omega
    rw [this, pow_add, mul_assoc]
  have tr : ∀ (N : ℕ) [NeZero N], N = boxSide (Tb.stepParameters y).side K k →
      (∀ B : Finset (TorusSite N), B.Nonempty →
        (Integrable (fun u => meanSiteScore (S.setup k).score B (stageState T k N u).2.1 (stageState T k N u).2.2 ^ 32)
            (markedSampleLaw T β k N) ∧
          ∫ u, meanSiteScore (S.setup k).score B (stageState T k N u).2.1 (stageState T k N u).2.2 ^ 32
            ∂(markedSampleLaw T β k N) ≤ max Mb 1) ∧
        AEStronglyMeasurable (fun u => meanSiteScore (S.setup k).score B (stageState T k N u).2.1
            (stageState T k N u).2.2)
          (markedSampleLaw T β k N)) →
      ∀ B : Finset (TorusSite (boxSide (Tb.stepParameters y).side K k)), B.Nonempty →
        (Integrable (fun u => meanSiteScore (S.setup k).score B (stageState T k _ u).2.1 (stageState T k _ u).2.2 ^ 32)
            (markedSampleLaw T β k (boxSide (Tb.stepParameters y).side K k)) ∧
          ∫ u, meanSiteScore (S.setup k).score B (stageState T k _ u).2.1 (stageState T k _ u).2.2 ^ 32
            ∂(markedSampleLaw T β k (boxSide (Tb.stepParameters y).side K k)) ≤ max Mb 1) ∧
        AEStronglyMeasurable (fun u => meanSiteScore (S.setup k).score B (stageState T k _ u).2.1
            (stageState T k _ u).2.2)
          (markedSampleLaw T β k (boxSide (Tb.stepParameters y).side K k)) := by
    intro N _ hN hh
    subst hN
    exact hh
  have hall := tr _ hside hbase
  have hM1' : (1 : ℝ) ≤ max Mb 1 := le_max_right _ _
  have hempty : ∀ (f : FinePlaquetteFunction),
      ¬ (functionSites (Tb.stepParameters y).side f k (boxSide (Tb.stepParameters y).side K k)).Nonempty →
      ∀ u, scoreMeanOver S f k (boxSide (Tb.stepParameters y).side K k)
        (stageState T k (boxSide (Tb.stepParameters y).side K k) u) = 1 := by
    intro f hne u
    show meanSiteScore _ _ _ _ = 1
    unfold meanSiteScore
    rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp
  have hNm : ∀ f : FinePlaquetteFunction, AEStronglyMeasurable
      (fun u => scoreMeanOver S f k (boxSide (Tb.stepParameters y).side K k)
        (stageState T k (boxSide (Tb.stepParameters y).side K k) u))
      (markedSampleLaw T β k (boxSide (Tb.stepParameters y).side K k)) := by
    intro f
    by_cases hne : (functionSites (Tb.stepParameters y).side f k (boxSide (Tb.stepParameters y).side K k)).Nonempty
    · exact (hall _ hne).2
    · simp only [hempty f hne]
      exact aestronglyMeasurable_const
  have hNq : ∀ f : FinePlaquetteFunction,
      Integrable (fun u => scoreMeanOver S f k (boxSide (Tb.stepParameters y).side K k)
          (stageState T k (boxSide (Tb.stepParameters y).side K k) u) ^ 32)
        (markedSampleLaw T β k (boxSide (Tb.stepParameters y).side K k)) ∧
      ∫ u, scoreMeanOver S f k (boxSide (Tb.stepParameters y).side K k)
          (stageState T k (boxSide (Tb.stepParameters y).side K k) u) ^ 32
        ∂(markedSampleLaw T β k (boxSide (Tb.stepParameters y).side K k)) ≤ max Mb 1 := by
    intro f
    by_cases hne : (functionSites (Tb.stepParameters y).side f k (boxSide (Tb.stepParameters y).side K k)).Nonempty
    · exact (hall _ hne).1
    · simp only [hempty f hne, one_pow]
      refine ⟨integrable_const _, ?_⟩
      simpa using hM1'
  have hCm : ∀ q ≤ 32, 0 ≤ Cp q ∧ Cp q ≤ ∑ q ∈ Finset.range 33, Cp q := fun q hq =>
    ⟨hCp0 q, Finset.single_le_sum (f := Cp) (fun i _ => hCp0 i) (Finset.mem_range.mpr (by omega))⟩
  have hstep : ∀ u < k, clusterRange (flowCouplings (Tb.stepParameters y) β u) ≤
      clusterRange (flowCouplings (Tb.stepParameters y) β (u + 1)) + 1 := by
    intro u hu
    have hst := hrun.isFlowStep u (by omega)
    have h1 := hst.onFamily.isStep.2.2
    have e1 : (T.stage u).toStepSetup.coupling = flowCouplings (Tb.stepParameters y) β u := hst.coupling_eq
    have e2 : (T.stage u).toStepSetup.nextCoupling = flowCouplings (Tb.stepParameters y) β (u + 1) :=
      hst.nextCoupling_eq
    rw [← e1, ← e2]
    exact h1
  have hvt2 : 2 ≤ vt * lengthInSites (Tb.stepParameters y).side K k d := by
    have h1 : vt * (2 ^ 12 * (clusterRange (flowCouplings (Tb.stepParameters y) β k) : ℝ)) ≤
        vt * lengthInSites (Tb.stepParameters y).side K k d :=
      mul_le_mul_of_nonneg_left hfar' hv.le
    have h2 : vt * (1 / vt) ≤ vt * (clusterRange (flowCouplings (Tb.stepParameters y) β k) : ℝ) :=
      mul_le_mul_of_nonneg_left hrv hv.le
    rw [mul_one_div_cancel hv.ne'] at h2
    nlinarith
  have hb := centered_products_at_stage hS hT hSc hWt hW hI hMk hfit T S hC.isCutoff_bottom hC.marksMeasurable β
    (flowCouplings (Tb.stepParameters y) β) K k hlt hstep hd0 hd4 hv
    hr2 hfar' hvt2 hp hφ (Cp := Cp) (C₀ := Kr.C₀) (Cx := Kr.C₀ + 1) (Cm := ∑ q ∈ Finset.range 33, Cp q)
    (M := max Mb 1) hC₀ (by linarith) hCm (by linarith)
    (fun f => (hFy β T S k hSK hrunk hreachk f k le_rfl (boxSide (Tb.stepParameters y).side K k) hblock).2.1) hbound
    (fun q g D hsz hap =>
      ((hCp q) T S β k (boxSide (Tb.stepParameters y).side K k) D g hSK hrunk hreachk hblock hsz hap).2)
    hone hNm hNq I
  refine hb.trans ?_
  have hl := final_bound_le (L := ((Tb.stepParameters y).side : ℝ)) (Cx := Kr.C₀ + 1) (C₀ := Kr.C₀) (M := max Mb 1)
    (Cm := ∑ q ∈ Finset.range 33, Cp q) (rt := (Tb.stepParameters y).rt)
    (x := flowCouplings (Tb.stepParameters y) β k)
    (n₀ := lengthInSites (Tb.stepParameters y).side K k d)
    (r := (clusterRange (flowCouplings (Tb.stepParameters y) β k) : ℝ))
    (E := Real.exp (-(4 * (Tb.stepParameters y).rt * (clusterRange (flowCouplings (Tb.stepParameters y) β k) : ℝ))))
    hLr (by linarith) (by linarith) (by linarith) (Finset.sum_nonneg fun i _ => hCp0 i) hfit.rt_pos hx1 hxn
    (by linarith) hn (clusterRange_le_two_mul hx1) (Real.exp_pos _).le
  unfold markError
  rw [show (129 : ℝ) = ((129 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact hl
end Statement
end YangMills.Construction.StateLaws
end
