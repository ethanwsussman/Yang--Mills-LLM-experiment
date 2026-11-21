import YangMills.Construction.CellOfTheFlow.TheChanceOfACellHasItsValueProof
import YangMills.Construction.ClusterExpansionOfAStep.BaseLawIsAProduct
import YangMills.Construction.FreeEnergiesOfTheFlow.ThePastIsFreeGivenTheStateProof
import YangMills.Construction.ResponseInTheExpansion.MeanOverAStepOfTheStatesProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal Quaternion
namespace YangMills.Construction.CellWindows
open StepSettings StepCosts RenormalizationStepParameters TorusFields TorusLumps TorusContours TopLevelSites WeightedResponses
  BlockAverages LumpContours ColdStepAtMirrorFrames
namespace SampleChainLaw
section Abstract
private theorem map_prod_eq_withDensity {A B C E D : Type} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace E] [MeasurableSpace D] (μ : Measure A) (N : Measure B) (St : Measure C)
    (ρ : Measure E) [SFinite μ] [SFinite N] [SFinite St] [SFinite ρ]
    (g : A × B → D) (dr : D → C → E) (w : D × E → ℝ≥0∞) (hg : Measurable g)
    (hf : Measurable fun p : A × B × C => ((g (p.1, p.2.1), dr (g (p.1, p.2.1)) p.2.2) : D × E))
    (hw : Measurable w)
    (hstep : ∀ (a : D) (F : E → ℝ≥0∞), Measurable F → ∫⁻ c, F (dr a c) ∂St = ∫⁻ e, F e * w (a, e) ∂ρ) :
    (μ.prod (N.prod St)).map (fun p : A × B × C => ((g (p.1, p.2.1), dr (g (p.1, p.2.1)) p.2.2) : D × E)) =
      (((μ.prod N).map g).prod ρ).withDensity w := by
  ext Q hQ
  have hI : Measurable (Q.indicator (1 : D × E → ℝ≥0∞)) := measurable_one.indicator hQ
  have hm2 : Measurable fun z : D × E => Q.indicator (1 : D × E → ℝ≥0∞) z * w z := hI.mul hw
  have hPhim : Measurable fun a => ∫⁻ e, Q.indicator (1 : D × E → ℝ≥0∞) (a, e) * w (a, e) ∂ρ :=
    hm2.lintegral_prod_right'
  have hPhi : ∀ a, ∫⁻ c, Q.indicator (1 : D × E → ℝ≥0∞) (a, dr a c) ∂St =
      ∫⁻ e, Q.indicator (1 : D × E → ℝ≥0∞) (a, e) * w (a, e) ∂ρ := fun a =>
    hstep a (fun e => Q.indicator (1 : D × E → ℝ≥0∞) (a, e)) (hI.comp measurable_prodMk_left)
  have hL : (μ.prod (N.prod St)) ((fun p : A × B × C => ((g (p.1, p.2.1), dr (g (p.1, p.2.1)) p.2.2) : D × E)) ⁻¹' Q) =
      ∫⁻ p : A × B × C, Q.indicator (1 : D × E → ℝ≥0∞) (g (p.1, p.2.1), dr (g (p.1, p.2.1)) p.2.2)
        ∂(μ.prod (N.prod St)) := by
    rw [← lintegral_indicator_one (hf hQ)]
    refine lintegral_congr fun p => ?_
    by_cases h : (g (p.1, p.2.1), dr (g (p.1, p.2.1)) p.2.2) ∈ Q
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  have hR : ∫⁻ z in Q, w z ∂(((μ.prod N).map g).prod ρ) =
      ∫⁻ z, Q.indicator (1 : D × E → ℝ≥0∞) z * w z ∂(((μ.prod N).map g).prod ρ) := by
    rw [← lintegral_indicator hQ]
    refine lintegral_congr fun z => ?_
    by_cases h : z ∈ Q
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have hmf : Measurable fun p : A × B × C =>
      Q.indicator (1 : D × E → ℝ≥0∞) (g (p.1, p.2.1), dr (g (p.1, p.2.1)) p.2.2) := hI.comp hf
  have hcomp : Measurable fun q : A × B =>
      ∫⁻ e, Q.indicator (1 : D × E → ℝ≥0∞) (g q, e) * w (g q, e) ∂ρ := hPhim.comp hg
  rw [Measure.map_apply hf hQ, withDensity_apply _ hQ, hL, hR, lintegral_prod _ hmf.aemeasurable,
    lintegral_prod _ hm2.aemeasurable, lintegral_map hPhim hg, lintegral_prod _ hcomp.aemeasurable]
  refine lintegral_congr fun x => ?_
  have hmx : Measurable fun q : B × C =>
      Q.indicator (1 : D × E → ℝ≥0∞) (g (x, q.1), dr (g (x, q.1)) q.2) := hmf.comp measurable_prodMk_left
  refine (lintegral_prod _ hmx.aemeasurable).trans (lintegral_congr fun y => ?_)
  exact hPhi (g (x, y))
abbrev _root_.YangMills.SharedProofs.p2276 := @map_prod_eq_withDensity
private theorem lintegral_count_eq_sum {α : Type} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (f : α → ℝ≥0∞) : ∫⁻ a, f a ∂(Measure.count : Measure α) = ∑ a, f a := by
  rw [lintegral_count, tsum_fintype]
private theorem lintegral_three_stages {U V₀ W₀ Bc Fl Bd : Type} [MeasurableSpace U] [MeasurableSpace V₀]
    [MeasurableSpace W₀] [MeasurableSpace Bc] [MeasurableSpace Fl] [MeasurableSpace Bd] [Fintype Bc] [Fintype Bd]
    [MeasurableSingletonClass Bc] [MeasurableSingletonClass Bd]
    (P₁ : Measure U) (P₂ : Measure V₀) (P₃ : Measure W₀) (H : Measure Fl) [SFinite P₂] [SFinite P₃] [SFinite H]
    (B : U → Bc) (Fd : Bc → V₀ → Fl) (C : Fl → W₀ → Bd)
    (pb : Bc → ℝ≥0∞) (k : Bc → Fl → ℝ≥0∞) (c : Fl → Bd → ℝ≥0∞)
    (hdraw : Measurable fun ξ : U × V₀ × W₀ => ((B ξ.1, Fd (B ξ.1) ξ.2.1, C (Fd (B ξ.1) ξ.2.1) ξ.2.2) : Bc × Fl × Bd))
    (hk : ∀ b, Measurable (k b)) (hc : ∀ bad, Measurable fun x => c x bad)
    (hB : ∀ G : Bc → ℝ≥0∞, ∫⁻ u, G (B u) ∂P₁ = ∑ b, G b * pb b)
    (hFd : ∀ b (G : Fl → ℝ≥0∞), Measurable G → ∫⁻ v, G (Fd b v) ∂P₂ = ∫⁻ x, G x * k b x ∂H)
    (hC : ∀ x (G : Bd → ℝ≥0∞), ∫⁻ w, G (C x w) ∂P₃ = ∑ bad, G bad * c x bad)
    (F : Bc × Fl × Bd → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ξ, F (B ξ.1, Fd (B ξ.1) ξ.2.1, C (Fd (B ξ.1) ξ.2.1) ξ.2.2) ∂(P₁.prod (P₂.prod P₃)) =
      ∫⁻ d, F d * (pb d.1 * k d.1 d.2.1 * c d.2.1 d.2.2)
        ∂((Measure.count : Measure Bc).prod (H.prod (Measure.count : Measure Bd))) := by
  have hm : Measurable fun ξ : U × V₀ × W₀ => F (B ξ.1, Fd (B ξ.1) ξ.2.1, C (Fd (B ξ.1) ξ.2.1) ξ.2.2) :=
    hF.comp hdraw
  have hsl : ∀ (b : Bc) (bad : Bd), Measurable fun x : Fl => F (b, x, bad) := fun b bad =>
    hF.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  let Gv : Bc → Fl → ℝ≥0∞ := fun b x => ∑ bad, F (b, x, bad) * c x bad
  have hGv : ∀ b, Measurable (Gv b) := fun b => Finset.measurable_sum _ fun bad _ => (hsl b bad).mul (hc bad)
  let Gb : Bc → ℝ≥0∞ := fun b => ∫⁻ x, Gv b x * k b x ∂H
  have inner : ∀ u, ∫⁻ q : V₀ × W₀, F (B u, Fd (B u) q.1, C (Fd (B u) q.1) q.2) ∂(P₂.prod P₃) = Gb (B u) := by
    intro u
    have hm1 : Measurable fun q : V₀ × W₀ => F (B u, Fd (B u) q.1, C (Fd (B u) q.1) q.2) :=
      hm.comp measurable_prodMk_left
    rw [lintegral_prod _ hm1.aemeasurable]
    have e : ∀ v, ∫⁻ w, F (B u, Fd (B u) v, C (Fd (B u) v) w) ∂P₃ = Gv (B u) (Fd (B u) v) := fun v =>
      hC (Fd (B u) v) fun bad => F (B u, Fd (B u) v, bad)
    refine (lintegral_congr e).trans ?_
    exact hFd (B u) (Gv (B u)) (hGv _)
  have hden : Measurable fun d : Bc × Fl × Bd => pb d.1 * k d.1 d.2.1 * c d.2.1 d.2.2 := by
    have hA : ∀ x : Bc × Bd, Measurable fun y : Fl => pb x.1 * k x.1 y * c y x.2 := fun x =>
      ((hk x.1).const_mul (pb x.1)).mul (hc x.2)
    have h1 : Measurable fun z : (Bc × Bd) × Fl => pb z.1.1 * k z.1.1 z.2 * c z.2 z.1.2 :=
      measurable_from_prod_countable_right hA
    have h2 : Measurable fun d : Bc × Fl × Bd => (((d.1, d.2.2), d.2.1) : (Bc × Bd) × Fl) :=
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk (measurable_fst.comp measurable_snd)
    exact h1.comp h2
  have hall : Measurable fun d : Bc × Fl × Bd => F d * (pb d.1 * k d.1 d.2.1 * c d.2.1 d.2.2) := hF.mul hden
  rw [lintegral_prod _ hm.aemeasurable, lintegral_prod _ hall.aemeasurable, lintegral_count_eq_sum]
  refine (lintegral_congr fun u => inner u).trans ?_
  rw [hB Gb]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hmb : Measurable fun y : Fl × Bd => F (b, y) * (pb b * k b y.1 * c y.1 y.2) :=
    hall.comp measurable_prodMk_left
  rw [lintegral_prod _ hmb.aemeasurable]
  have e : ∀ x, ∫⁻ bad, F (b, x, bad) * (pb b * k b x * c x bad) ∂(Measure.count : Measure Bd) =
      Gv b x * k b x * pb b := by
    intro x
    rw [lintegral_count_eq_sum]
    simp only [Gv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun bad _ => ?_
    ring
  refine Eq.trans ?_ (lintegral_congr e).symm
  have hGk : Measurable fun x => Gv b x * k b x := (hGv b).mul (hk b)
  rw [lintegral_mul_const _ hGk]
abbrev _root_.YangMills.SharedProofs.p99551 := @lintegral_three_stages
private theorem lintegral_comp_of_fintype {Ω α : Type} [MeasurableSpace Ω] [MeasurableSpace α] [Fintype α]
    [MeasurableSingletonClass α] (P : Measure Ω) (f : Ω → α) (hf : Measurable f) (p : α → ℝ≥0∞)
    (hp : ∀ a, P (f ⁻¹' {a}) = p a) (G : α → ℝ≥0∞) : ∫⁻ ω, G (f ω) ∂P = ∑ a, G a * p a := by
  have hG : Measurable G := measurable_of_countable G
  rw [← lintegral_map hG hf, lintegral_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Measure.map_apply hf (measurableSet_singleton a), hp]
abbrev _root_.YangMills.SharedProofs.p60989 := @lintegral_comp_of_fintype
private theorem pi_withDensity_eq {ι X : Type} [Fintype ι] [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (k : ι → X → ℝ≥0∞) (hk : ∀ i, Measurable (k i))
    [∀ i, SigmaFinite (ν.withDensity (k i))] :
    Measure.pi (fun i => ν.withDensity (k i)) =
      (Measure.pi fun _ : ι => ν).withDensity fun x => ∏ i, k i (x i) := by
  classical
  refine Measure.pi_eq (μ := fun i => ν.withDensity (k i)) fun s hs => ?_
  have hQ : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hQ, ← lintegral_indicator hQ]
  have e : (Set.univ.pi s).indicator (fun x : ι → X => ∏ i, k i (x i)) =
      fun x => ∏ i, (s i).indicator (k i) (x i) := by
    funext x
    by_cases h : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem h]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (h i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem h]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by
        by_contra hc
        push Not at hc
        exact h fun i _ => hc i
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [e]
  have hm : ∀ i, Measurable ((s i).indicator (k i)) := fun i => (hk i).indicator (hs i)
  have hind : iIndepFun (fun i (x : ι → X) => (s i).indicator (k i) (x i)) (Measure.pi fun _ : ι => ν) :=
    iIndepFun_pi (X := fun i => (s i).indicator (k i)) fun i => (hm i).aemeasurable
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    fun i => (hm i).comp (measurable_pi_apply i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
  exact (measurePreserving_eval (fun _ : ι => ν) i).lintegral_comp (hm i)
abbrev _root_.YangMills.SharedProofs.p56082 := @pi_withDensity_eq
private theorem measurableSet_preimage_finset {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (f : Ω → Finset ι)
    (h : ∀ i, MeasurableSet {ω | i ∈ f ω}) (bad : Finset ι) : MeasurableSet (f ⁻¹' {bad}) := by
  classical
  have e : f ⁻¹' {bad} = ⋂ i, {ω | i ∈ f ω ↔ i ∈ bad} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact Finset.ext_iff
  rw [e]
  refine MeasurableSet.iInter fun i => ?_
  by_cases hb : i ∈ bad
  · have e' : {ω | i ∈ f ω ↔ i ∈ bad} = {ω | i ∈ f ω} := by
      ext ω
      simp [hb]
    rw [e']
    exact h i
  · have e' : {ω | i ∈ f ω ↔ i ∈ bad} = {ω | i ∈ f ω}ᶜ := by
      ext ω
      simp [hb]
    rw [e']
    exact (h i).compl
abbrev _root_.YangMills.SharedProofs.p29435 := @measurableSet_preimage_finset
end Abstract
section Cutoff
private theorem cutoffFactor_mem_unit {ρ : ℝ} {p : ℝ → ℝ} (h : IsCutoff ρ p) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ cutoffFactor ρ p u ∧ cutoffFactor ρ p u ≤ 1 := by apply _root_.YangMills.SharedProofs.p2957 <;> assumption
end Cutoff
private instance (L n : ℕ) : DiscreteMeasurableSpace (BaseChoice L n) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) : DiscreteMeasurableSpace (BondSet m) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) [NeZero m] : Fintype (BondSet m) := inferInstanceAs (Fintype (Finset (TorusBond m)))
section Marks
variable (R : StepSetup) {n : ℕ} [NeZero n]
private theorem bondMark_mem_unit (hc : IsCutoff R.ballRadius R.barrierFn) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (b : TorusBond (n * R.params.side)) :
    0 ≤ bondMark R V W b ∧ bondMark R V W b ≤ 1 :=
  cutoffFactor_mem_unit hc (norm_nonneg _)
open Classical in
private def markedLinks (W : TorusField (n * R.params.side)) (V : TorusField n)
    (w : TorusBond (n * R.params.side) → I) : Finset (TorusBond (n * R.params.side)) :=
  (markedBonds R (hotCoreSites R V)).filter fun b => bondMark R V W b < ((w b : I) : ℝ)
private def markedLinkSet (W : TorusField (n * R.params.side)) (V : TorusField n)
    (w : TorusBond (n * R.params.side) → I) : BondSet (n * R.params.side) :=
  markedLinks R W V w
private theorem mem_markedLinks (W : TorusField (n * R.params.side)) (V : TorusField n)
    (w : TorusBond (n * R.params.side) → I) (b : TorusBond (n * R.params.side)) :
    b ∈ markedLinks R W V w ↔
      b ∈ markedBonds R (hotCoreSites R V) ∧ bondMark R V W b < ((w b : I) : ℝ) := by
  classical
  unfold markedLinks
  exact Finset.mem_filter
private theorem sum_powerset_prod_ite_eq {ι : Type} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ) :
    ∑ t ∈ s.powerset, ∏ i ∈ s, (if i ∈ t then f i else g i) = ∏ i ∈ s, (f i + g i) := by apply _root_.YangMills.SharedProofs.p12670 <;> assumption
open Classical in
private def goodMass (W : TorusField (n * R.params.side)) (V : TorusField n) (b : TorusBond (n * R.params.side)) :
    ℝ :=
  ∑ bad : Finset (TorusBond (n * R.params.side)), if b ∈ bad then 0 else markLaw R W V bad
private theorem markLaw_eq_ite (hg : R.params.side ∣ n ∧ 64 ≤ n) (W : TorusField (n * R.params.side))
    (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side))) :
    markLaw R W V bad = open Classical in if bad ∈ (markedBonds R (hotCoreSites R V)).powerset then
      ∏ b ∈ markedBonds R (hotCoreSites R V), (if b ∈ bad then 1 - bondMark R V W b else bondMark R V W b)
      else 0 := by
  classical
  simp only [markLaw, markProduct, Finset.mem_powerset, if_pos hg]
private theorem goodMass_eq (hg : R.params.side ∣ n ∧ 64 ≤ n) (W : TorusField (n * R.params.side))
    (V : TorusField n) (b : TorusBond (n * R.params.side)) :
    goodMass R W V b = open Classical in
      if b ∈ markedBonds R (hotCoreSites R V) then bondMark R V W b else 1 := by
  classical
  set Mk := markedBonds R (hotCoreSites R V) with hMk
  set f : TorusBond (n * R.params.side) → ℝ := fun i => if i = b then 0 else 1 - bondMark R V W i with hf
  have h1 : goodMass R W V b = ∑ t ∈ Mk.powerset, if b ∈ t then 0 else
      ∏ i ∈ Mk, (if i ∈ t then 1 - bondMark R V W i else bondMark R V W i) := by
    unfold goodMass
    have e : ∀ bad : Finset (TorusBond (n * R.params.side)),
        (if b ∈ bad then (0 : ℝ) else markLaw R W V bad) =
        if bad ∈ Mk.powerset then (if b ∈ bad then 0 else
          ∏ i ∈ Mk, (if i ∈ bad then 1 - bondMark R V W i else bondMark R V W i)) else 0 := by
      intro bad
      rw [markLaw_eq_ite R hg]
      by_cases h1 : bad ∈ Mk.powerset <;> by_cases h2 : b ∈ bad <;> simp [h1, h2, hMk]
    simp only [e]
    rw [Finset.sum_ite_mem Finset.univ, Finset.univ_inter]
  by_cases hb : b ∈ Mk
  · rw [if_pos hb, h1]
    have h2 : ∀ t ∈ Mk.powerset, (if b ∈ t then (0 : ℝ) else
        ∏ i ∈ Mk, (if i ∈ t then 1 - bondMark R V W i else bondMark R V W i)) =
        ∏ i ∈ Mk, (if i ∈ t then f i else bondMark R V W i) := by
      intro t _
      by_cases hbt : b ∈ t
      · rw [if_pos hbt]
        refine (Finset.prod_eq_zero hb ?_).symm
        simp [hbt, hf]
      · rw [if_neg hbt]
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases hit : i ∈ t
        · have hne : i ≠ b := fun h => hbt (h ▸ hit)
          simp [hit, hf, hne]
        · simp [hit]
    rw [Finset.sum_congr rfl h2, sum_powerset_prod_ite_eq]
    rw [Finset.prod_eq_single b]
    · simp [hf]
    · intro i _ hne
      simp [hf, hne]
    · exact fun h => absurd hb h
  · rw [if_neg hb, h1]
    have h2 : ∀ t ∈ Mk.powerset, (if b ∈ t then (0 : ℝ) else
        ∏ i ∈ Mk, (if i ∈ t then 1 - bondMark R V W i else bondMark R V W i)) =
        ∏ i ∈ Mk, (if i ∈ t then 1 - bondMark R V W i else bondMark R V W i) := by
      intro t ht
      rw [if_neg fun h => hb (Finset.mem_powerset.1 ht h)]
    rw [Finset.sum_congr rfl h2, sum_powerset_prod_ite_eq]
    simp
private theorem mem_markedLinks_iff (hc : IsCutoff R.ballRadius R.barrierFn) (hg : R.params.side ∣ n ∧ 64 ≤ n)
    (W : TorusField (n * R.params.side)) (V : TorusField n) (w : TorusBond (n * R.params.side) → I)
    (b : TorusBond (n * R.params.side)) :
    b ∈ markedLinks R W V w ↔ goodMass R W V b < ((w b : I) : ℝ) := by
  classical
  rw [mem_markedLinks, goodMass_eq R hg]
  by_cases hb : b ∈ markedBonds R (hotCoreSites R V)
  · simp [hb]
  · simp only [hb, if_false, false_and, false_iff, not_lt]
    exact (w b).2.2
private theorem measurable_markedLinkSet (hc : IsCutoff R.ballRadius R.barrierFn)
    (hg : R.params.side ∣ n ∧ 64 ≤ n)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad) :
    Measurable fun p : TorusField (n * R.params.side) × TorusField n × (TorusBond (n * R.params.side) → I) =>
      markedLinkSet R p.1 p.2.1 p.2.2 := by
  classical
  have hm : ∀ b, Measurable fun p : TorusField (n * R.params.side) × TorusField n => goodMass R p.1 p.2 b := by
    intro b
    unfold goodMass
    refine Finset.measurable_sum _ fun bad _ => ?_
    by_cases hb : b ∈ bad
    · simp only [hb, if_true]
      exact measurable_const
    · simp only [hb, if_false]
      exact hB bad
  have hlt : ∀ b, MeasurableSet {p : TorusField (n * R.params.side) × TorusField n ×
      (TorusBond (n * R.params.side) → I) | b ∈ markedLinks R p.1 p.2.1 p.2.2} := by
    intro b
    have e : {p : TorusField (n * R.params.side) × TorusField n × (TorusBond (n * R.params.side) → I) |
        b ∈ markedLinks R p.1 p.2.1 p.2.2} = {p | goodMass R p.1 p.2.1 b < ((p.2.2 b : I) : ℝ)} := by
      ext p
      exact mem_markedLinks_iff R hc hg _ _ _ b
    rw [e]
    have hp : Measurable fun p : TorusField (n * R.params.side) × TorusField n ×
        (TorusBond (n * R.params.side) → I) => ((p.1, p.2.1) : TorusField (n * R.params.side) × TorusField n) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have h1 := (hm b).comp hp
    have hq : Measurable fun p : TorusField (n * R.params.side) × TorusField n ×
        (TorusBond (n * R.params.side) → I) => p.2.2 :=
      measurable_snd.comp measurable_snd
    have h2 : Measurable fun p : TorusField (n * R.params.side) × TorusField n ×
        (TorusBond (n * R.params.side) → I) => ((p.2.2 b : I) : ℝ) :=
      measurable_subtype_coe.comp ((measurable_pi_apply b).comp hq)
    exact measurableSet_lt h1 h2
  exact measurable_to_countable' fun bad =>
    measurableSet_preimage_finset (ι := TorusBond (n * R.params.side)) _ hlt bad
private theorem measurable_markedLinkSet_uniform (W : TorusField (n * R.params.side)) (V : TorusField n) :
    Measurable (markedLinkSet R W V) := by
  have hlt : ∀ b, MeasurableSet {w : TorusBond (n * R.params.side) → I | b ∈ markedLinks R W V w} := by
    intro b
    by_cases hb : b ∈ markedBonds R (hotCoreSites R V)
    · have e : {w : TorusBond (n * R.params.side) → I | b ∈ markedLinks R W V w} =
          {w | bondMark R V W b < ((w b : I) : ℝ)} := by
        ext w
        simpa [hb] using mem_markedLinks R W V w b
      rw [e]
      exact measurableSet_lt measurable_const (measurable_subtype_coe.comp (measurable_pi_apply b))
    · have e : {w : TorusBond (n * R.params.side) → I | b ∈ markedLinks R W V w} = ∅ := by
        ext w
        simpa [hb] using mem_markedLinks R W V w b
      rw [e]
      exact MeasurableSet.empty
  exact measurable_to_countable' fun bad =>
    measurableSet_preimage_finset (ι := TorusBond (n * R.params.side)) _ hlt bad
private theorem markedLinks_mass (hc : IsCutoff R.ballRadius R.barrierFn) (hg : R.params.side ∣ n ∧ 64 ≤ n)
    (W : TorusField (n * R.params.side)) (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side))) :
    (Measure.pi fun _ : TorusBond (n * R.params.side) => (volume : Measure I)) (markedLinks R W V ⁻¹' {bad}) =
      ENNReal.ofReal (markLaw R W V bad) := by
  classical
  set Mk := markedBonds R (hotCoreSites R V) with hMk
  have hbd := fun b => bondMark_mem_unit R hc V W b
  let mI : TorusBond (n * R.params.side) → I := fun b => ⟨bondMark R V W b, (hbd b).1, (hbd b).2⟩
  by_cases hsub : bad ⊆ Mk
  · let A : TorusBond (n * R.params.side) → Set I := fun b =>
      if b ∈ Mk then (if b ∈ bad then Set.Ioi (mI b) else Set.Iic (mI b))
      else Set.univ
    have e : markedLinks R W V ⁻¹' {bad} = Set.univ.pi A := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_imp_iff]
      constructor
      · intro h b
        have hm := mem_markedLinks R W V w b
        rw [h] at hm
        simp only [A]
        by_cases hb : b ∈ Mk
        · rw [if_pos hb]
          by_cases hbb : b ∈ bad
          · rw [if_pos hbb]
            exact (hm.1 hbb).2
          · rw [if_neg hbb]
            by_contra hcn
            exact hbb (hm.2 ⟨hb, not_le.1 hcn⟩)
        · rw [if_neg hb]
          exact Set.mem_univ _
      · intro h
        refine Finset.ext fun b => ?_
        refine (mem_markedLinks R W V w b).trans ?_
        have hb' := h b
        simp only [A] at hb'
        constructor
        · rintro ⟨h1, h2⟩
          rw [if_pos h1] at hb'
          by_contra hbb
          rw [if_neg hbb] at hb'
          exact absurd h2 (not_lt.2 hb')
        · intro hbb
          have h1 := hsub hbb
          rw [if_pos h1, if_pos hbb] at hb'
          exact ⟨h1, hb'⟩
    rw [e, Measure.pi_pi, markLaw_eq_ite R hg, if_pos (Finset.mem_powerset.2 hsub),
      ENNReal.ofReal_prod_of_nonneg]
    · have h1 : ∀ b : TorusBond (n * R.params.side), (volume : Measure I) (A b) =
          if b ∈ Mk then ENNReal.ofReal
            (if b ∈ bad then 1 - bondMark R V W b else bondMark R V W b) else 1 := by
        intro b
        simp only [A]
        by_cases hb : b ∈ Mk
        · by_cases hbb : b ∈ bad
          · simp only [if_pos hb, if_pos hbb]
            exact unitInterval.volume_Ioi (mI b)
          · simp only [if_pos hb, if_neg hbb]
            exact unitInterval.volume_Iic (mI b)
        · simp only [if_neg hb]
          exact measure_univ
      simp only [h1]
      rw [Finset.prod_ite_mem Finset.univ, Finset.univ_inter]
    · intro b _
      have := hbd b
      split_ifs <;> linarith [this.1, this.2]
  · have hempty : markedLinks R W V ⁻¹' {bad} = ∅ := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      apply hsub
      intro b hb
      have := (mem_markedLinks R W V w b).1 (by rw [h]; exact hb)
      exact this.1
    rw [hempty, measure_empty, markLaw_eq_ite R hg, if_neg (fun h => hsub (Finset.mem_powerset.1 h)),
      ENNReal.ofReal_zero]
end Marks
section Step
variable {R : StepSetup} {n : ℕ} [NeZero n]
private def cellEquivTorusSite (L n : ℕ) [NeZero L] [NeZero n] : (stepBlockFrame L n).Cell ≃ TorusSite n where
  toFun := toTorusSite (F := stepBlockFrame L n) (j := 1) n
  invFun := torusSiteInFrame (stepBlockFrame L n) 1
  left_inv := torusSiteInFrame_toTorusSite _root_.YangMills.Construction.TorusContours.stepBlockFrame_period_one
  right_inv := toTorusSite_torusSiteInFrame _root_.YangMills.Construction.TorusContours.stepBlockFrame_period_one
private def sampledBaseChoice (S : StepSampler R) (W : TorusField (n * R.params.side)) (u : TorusSite n → I) :
    BaseChoice R.params.side n :=
  fun y => S.sampleBase n W (toTorusSite n y) (u (toTorusSite n y))
private theorem blockBaseWeight_nonneg (ℓ : TorusLumps.StepParameters)
    (h : Finset (Finset ((stepBlockFrame ℓ.side n).Site 0)))
    (y : (stepBlockFrame ℓ.side n).Cell) (z : (stepBlockFrame ℓ.side n).Site 0) :
    0 ≤ blockBaseWeight ℓ h y z := by
  unfold blockBaseWeight
  split_ifs
  · positivity
  · exact le_rfl
abbrev _root_.YangMills.SharedProofs.p16398 := @blockBaseWeight_nonneg
private theorem baseLaw_nonneg (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    0 ≤ baseLaw (R := R) W b := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SmoothOffHull.baseLaw_nonneg_of_field <;> assumption
private theorem baseChoice_mass (S : StepSampler R) (hD : S.IsFaithful) (hBL : ClusterExpansionOfAStep.BaseLawIsProduct)
    (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    (Measure.pi fun _ : TorusSite n => (volume : Measure I)) (sampledBaseChoice S W ⁻¹' {b}) =
      ENNReal.ofReal (baseLaw (R := R) W b) := by
  classical
  have hset : sampledBaseChoice S W ⁻¹' {b} =
      Set.univ.pi fun x : TorusSite n =>
        {v : I | S.sampleBase n W x v = b ((cellEquivTorusSite R.params.side n).symm x)} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_imp_iff,
      Set.mem_setOf_eq]
    constructor
    · intro h x
      have h1 := congrFun h ((cellEquivTorusSite R.params.side n).symm x)
      have hx : toTorusSite (F := stepBlockFrame R.params.side n) (j := (stepBlockFrame R.params.side n).top) n
          ((cellEquivTorusSite R.params.side n).symm x) = x :=
        (cellEquivTorusSite R.params.side n).apply_symm_apply x
      simp only [sampledBaseChoice] at h1
      rw [hx] at h1
      exact h1
    · intro h
      funext y
      have h1 := h (cellEquivTorusSite R.params.side n y)
      rw [Equiv.symm_apply_apply] at h1
      exact h1
  rw [hset, Measure.pi_pi]
  have e : ∀ x : TorusSite n, (volume : Measure I)
      {v : I | S.sampleBase n W x v = b ((cellEquivTorusSite R.params.side n).symm x)} =
      ENNReal.ofReal (blockBaseWeight R.params (stepHotLumps R.params W)
        ((cellEquivTorusSite R.params.side n).symm x) (b ((cellEquivTorusSite R.params.side n).symm x))) :=
    fun x => hD.base_distribution n W x _
  simp only [e]
  rw [← ENNReal.ofReal_prod_of_nonneg fun x _ => blockBaseWeight_nonneg _ _ _ _, hBL R n W b]
  congr 1
  exact Equiv.prod_comp (cellEquivTorusSite R.params.side n).symm fun y =>
    blockBaseWeight R.params (stepHotLumps R.params W) y (b y)
private theorem measurable_sampledBaseChoice (S : StepSampler R) (hD : S.IsFaithful) :
    Measurable fun p : TorusField (n * R.params.side) × (TorusSite n → I) => sampledBaseChoice S p.1 p.2 := by
  refine measurable_to_countable' fun b => ?_
  have e : (fun p : TorusField (n * R.params.side) × (TorusSite n → I) => sampledBaseChoice S p.1 p.2) ⁻¹' {b} =
      ⋂ y, {p | S.sampleBase n p.1 (toTorusSite n y) (p.2 (toTorusSite n y)) = b y} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact funext_iff
  rw [e]
  refine MeasurableSet.iInter fun y => ?_
  have hm := (hD.measurable_base n (toTorusSite n y)).comp
    (measurable_fst.prodMk ((measurable_pi_apply (toTorusSite n y)).comp measurable_snd) :
      Measurable fun p : TorusField (n * R.params.side) × (TorusSite n → I) => (p.1, p.2 (toTorusSite n y)))
  exact hm (measurableSet_singleton (b y))
private def sampledLinkField (S : StepSampler R) (W : TorusField (n * R.params.side))
    (b : BaseChoice R.params.side n) (v : TorusBond n → I) : TorusField n :=
  fun x i => S.sampleLink n W b (x, i) (v (x, i))
private def linkKernel (R : StepSetup) (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n)
    (c : TorusBond n) (g : UnitQuaternion) : ℝ :=
  bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
    (readAtLevel (stepBlockFrame R.params.side n) 1 (fun _ _ => g : TorusField n)) b
    (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2)
private theorem bondKernel_nonneg (ℓ : TorusLumps.StepParameters) (x : ℝ)
    (W : (stepBlockFrame ℓ.side n).GaugeField 0) (V : (stepBlockFrame ℓ.side n).GaugeField 1)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) : 0 ≤ bondKernel ℓ x W V b c := by
  unfold bondKernel
  exact div_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)
private theorem measurable_heatKernel (C Z : ℝ) (Wb : ℍ[ℝ]) :
    Measurable fun g : UnitQuaternion => Real.exp (C * (Wb * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) / Z := by
  have h1 : Continuous fun g : UnitQuaternion => ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) :=
    continuous_subtype_val.comp continuous_inv
  have h2 : Continuous fun g : UnitQuaternion => (Wb * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re :=
    Quaternion.continuous_re.comp (continuous_const.mul h1)
  exact ((Real.continuous_exp.comp (continuous_const.mul h2)).div_const Z).measurable
abbrev _root_.YangMills.SharedProofs.p22068 := @measurable_heatKernel
private theorem measurable_linkKernel (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n)
    (c : TorusBond n) : Measurable (linkKernel R W b c) :=
  measurable_heatKernel (R.params.coupling * R.coupling)
    (partitionFn (R.params.coupling * R.coupling * ‖contourMean R.params.baseDepth
      (hotLumps R.params.grid R.params.threshold (levelSites (stepBlockFrame R.params.side n) 0)
      (readAtLevel (stepBlockFrame R.params.side n) 0 W)) b (readAtLevel (stepBlockFrame R.params.side n) 0 W)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2)‖))
    (contourMean R.params.baseDepth (hotLumps R.params.grid R.params.threshold
      (levelSites (stepBlockFrame R.params.side n) 0)
      (readAtLevel (stepBlockFrame R.params.side n) 0 W)) b (readAtLevel (stepBlockFrame R.params.side n) 0 W)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2))
abbrev _root_.YangMills.DeltaSharedProofs.p3729 := @measurable_linkKernel
private theorem prod_bondKernel_eq (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n)
    (V : TorusField n) :
    ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
      bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c =
    ∏ c : TorusBond n, linkKernel R W b c (V c.1 c.2) := by
  refine Fintype.prod_equiv ((cellEquivTorusSite R.params.side n).prodCongr (Equiv.refl _)) _ _ fun c => ?_
  have hy : torusSiteInFrame (stepBlockFrame R.params.side n) 1
      (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c.1) = c.1 :=
    (cellEquivTorusSite R.params.side n).symm_apply_apply c.1
  show _ = bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
    (readAtLevel (stepBlockFrame R.params.side n) 1
      (fun _ _ => V (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c.1) c.2 : TorusField n)) b
    (torusSiteInFrame (stepBlockFrame R.params.side n) 1
      (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c.1), c.2)
  rw [hy]
  rfl
abbrev _root_.YangMills.DeltaSharedProofs.p500894 := @prod_bondKernel_eq
private theorem map_curry_pi_haarUnit (n : ℕ) [NeZero n] :
    (Measure.pi fun _ : TorusBond n => haarUnit).map (MeasurableEquiv.curry (TorusSite n) (Fin 4) UnitQuaternion) =
      fieldHaar n := by
  have h := Measure.infinitePi_map_curry (ι := TorusSite n) (κ := Fin 4) (X := UnitQuaternion)
    (fun _ _ => haarUnit)
  simp only [Measure.infinitePi_eq_pi] at h
  exact h
abbrev _root_.YangMills.SharedProofs.p84299 := @map_curry_pi_haarUnit
private theorem lintegral_sampledLinkField (S : StepSampler R) (hD : S.IsFaithful)
    (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n)
    (G : TorusField n → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ v, G (sampledLinkField S W b v) ∂(Measure.pi fun _ : TorusBond n => (volume : Measure I)) =
      ∫⁻ V, G V * ∏ c : TorusBond n, ENNReal.ofReal (linkKernel R W b c (V c.1 c.2)) ∂(fieldHaar n) := by
  let k : TorusBond n → UnitQuaternion → ℝ≥0∞ := fun c g => ENNReal.ofReal (linkKernel R W b c g)
  have hk : ∀ c, Measurable (k c) := fun c => (measurable_linkKernel W b c).ennreal_ofReal
  have hb : ∀ c, Measurable (S.sampleLink n W b c) := fun c =>
    (hD.measurable_link n c).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hmap : ∀ c, (volume : Measure I).map (S.sampleLink n W b c) = haarUnit.withDensity (k c) := by
    intro c
    ext A hA
    rw [Measure.map_apply (hb c) hA, withDensity_apply _ hA]
    exact hD.link_distribution n W b c A hA
  haveI : ∀ c, IsProbabilityMeasure ((volume : Measure I).map (S.sampleLink n W b c)) := fun c =>
    Measure.isProbabilityMeasure_map (hb c).aemeasurable
  haveI : ∀ c, IsProbabilityMeasure (haarUnit.withDensity (k c)) := fun c => by
    rw [← hmap c]
    infer_instance
  have h1 : (Measure.pi fun _ : TorusBond n => (volume : Measure I)).map
      (fun v c => S.sampleLink n W b c (v c)) =
      (Measure.pi fun _ : TorusBond n => haarUnit).withDensity fun f => ∏ c, k c (f c) := by
    rw [Measure.pi_map_pi (fun c => (hb c).aemeasurable)]
    simp only [hmap]
    exact pi_withDensity_eq haarUnit k hk
  have hφ : Measurable fun (v : TorusBond n → I) (c : TorusBond n) => S.sampleLink n W b c (v c) :=
    measurable_pi_lambda _ fun c => (hb c).comp (measurable_pi_apply c)
  have hcur := (MeasurableEquiv.curry (TorusSite n) (Fin 4) UnitQuaternion).measurable
  have hPi : Measurable fun f : TorusBond n → UnitQuaternion => ∏ c, k c (f c) :=
    Finset.measurable_prod _ fun c _ => (hk c).comp (measurable_pi_apply c)
  have hGc : Measurable fun f : TorusBond n → UnitQuaternion =>
      G (MeasurableEquiv.curry (TorusSite n) (Fin 4) UnitQuaternion f) := hG.comp hcur
  have hL : ∫⁻ v, G (sampledLinkField S W b v) ∂(Measure.pi fun _ : TorusBond n => (volume : Measure I)) =
      ∫⁻ f, G (MeasurableEquiv.curry (TorusSite n) (Fin 4) UnitQuaternion f)
        ∂((Measure.pi fun _ : TorusBond n => (volume : Measure I)).map
          (fun v c => S.sampleLink n W b c (v c))) := by
    rw [lintegral_map hGc hφ]
    rfl
  have hRm : Measurable fun V : TorusField n =>
      G V * ∏ c : TorusBond n, ENNReal.ofReal (linkKernel R W b c (V c.1 c.2)) :=
    hG.mul (Finset.measurable_prod _ fun c _ =>
      (hk c).comp ((measurable_pi_apply c.2).comp (measurable_pi_apply c.1)))
  rw [hL, h1, lintegral_withDensity_eq_lintegral_mul _ hPi hGc, ← map_curry_pi_haarUnit n,
    lintegral_map hRm hcur]
  refine lintegral_congr fun f => ?_
  rw [Pi.mul_apply, mul_comm]
  rfl
private theorem stepTransitionDensity_eq_mul (W : TorusField (n * R.params.side))
    (b : BaseChoice R.params.side n) (V : TorusField n) :
    stepTransitionDensity R.params R.coupling W b V = baseLaw (R := R) W b *
      ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c := by apply _root_.YangMills.SharedProofs.p31947 <;> assumption
private theorem measurable_sample (S : StepSampler R) (hD : S.IsFaithful) (hc : IsCutoff R.ballRadius R.barrierFn)
    (hg : R.params.side ∣ n ∧ 64 ≤ n)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad) :
    Measurable fun p : TorusField (n * R.params.side) × StepNoise R.params n => S.sample p.1 p.2 := by
  have h1 : Measurable fun p : TorusField (n * R.params.side) × StepNoise R.params n =>
      sampledBaseChoice S p.1 p.2.1 :=
    (measurable_sampledBaseChoice S hD).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h2 : Measurable fun p : TorusField (n * R.params.side) × StepNoise R.params n =>
      sampledLinkField S p.1 (sampledBaseChoice S p.1 p.2.1) p.2.2.1 := by
    refine measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun i => ?_
    exact (hD.measurable_link n (x, i)).comp (measurable_fst.prodMk (h1.prodMk
      ((measurable_pi_apply (x, i)).comp (measurable_fst.comp (measurable_snd.comp measurable_snd)))))
  have h3 := (measurable_markedLinkSet R hc hg hB).comp (measurable_fst.prodMk (h2.prodMk
    (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  exact h1.prodMk (h2.prodMk h3)
abbrev _root_.YangMills.SharedProofs.p94641 := @measurable_sample
private theorem lintegral_sample (S : StepSampler R) (hD : S.IsFaithful) (hBL : ClusterExpansionOfAStep.BaseLawIsProduct)
    (hc : IsCutoff R.ballRadius R.barrierFn) (hg : R.params.side ∣ n ∧ 64 ≤ n)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (W : TorusField (n * R.params.side)) (F : StepOutcome R.params n → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ξ, F (S.sample W ξ) ∂(stepNoiseMeasure R.params n) =
      ∫⁻ e, F e * ENNReal.ofReal (stepOutcomeDensity R W e) ∂(stepReferenceMeasure R.params n) := by
  have hmeas := measurable_sample S hD hc hg hB
  have hbases : Measurable (sampledBaseChoice S W) :=
    (measurable_sampledBaseChoice S hD).comp measurable_prodMk_left
  have h := lintegral_three_stages (Measure.pi fun _ : TorusSite n => (volume : Measure I))
    (Measure.pi fun _ : TorusBond n => (volume : Measure I))
    (Measure.pi fun _ : TorusBond (n * R.params.side) => (volume : Measure I)) (fieldHaar n)
    (sampledBaseChoice S W) (sampledLinkField S W) (markedLinkSet R W)
    (fun b => ENNReal.ofReal (baseLaw (R := R) W b))
    (fun b V => ∏ c : TorusBond n, ENNReal.ofReal (linkKernel R W b c (V c.1 c.2)))
    (fun V bad => ENNReal.ofReal (markLaw R W V bad))
    (hmeas.comp measurable_prodMk_left)
    (fun b => Finset.measurable_prod _ fun c _ => (measurable_linkKernel W b c).ennreal_ofReal.comp
      ((measurable_pi_apply c.2).comp (measurable_pi_apply c.1)))
    (fun bad => ((hB bad).comp measurable_prodMk_left).ennreal_ofReal)
    (fun G => lintegral_comp_of_fintype _ _ hbases _ (baseChoice_mass S hD hBL W) G)
    (fun b G hG => lintegral_sampledLinkField S hD W b G hG)
    (fun V G => lintegral_comp_of_fintype (α := BondSet (n * R.params.side)) _ _
      (measurable_markedLinkSet_uniform R W V) _ (markedLinks_mass R hc hg W V) G)
    F hF
  unfold stepNoiseMeasure stepReferenceMeasure
  refine h.trans (lintegral_congr fun e => ?_)
  congr 1
  show _ = ENNReal.ofReal (stepTransitionDensity R.params R.coupling W e.1 e.2.1 * markLaw R W e.2.1 e.2.2)
  have hcn : 0 ≤ ∏ c : TorusBond n, linkKernel R W e.1 c (e.2.1 c.1 c.2) :=
    Finset.prod_nonneg fun c _ => bondKernel_nonneg _ _ _ _ _ _
  have hprod : ∏ c : TorusBond n, ENNReal.ofReal (linkKernel R W e.1 c (e.2.1 c.1 c.2)) =
      ENNReal.ofReal (∏ c : TorusBond n, linkKernel R W e.1 c (e.2.1 c.1 c.2)) :=
    (ENNReal.ofReal_prod_of_nonneg fun c _ => bondKernel_nonneg _ _ _ _ _ _).symm
  rw [stepTransitionDensity_eq_mul, prod_bondKernel_eq, ENNReal.ofReal_mul (mul_nonneg (baseLaw_nonneg _ _) hcn),
    ENNReal.ofReal_mul (baseLaw_nonneg _ _), hprod]
abbrev _root_.YangMills.SharedProofs.p65995 := @lintegral_sample
private theorem measurable_of_discrete_parts {X : Type} [MeasurableSpace X] {f : X × StepOutcome R.params n → ℝ}
    (h : ∀ (b : BaseChoice R.params.side n) (bad : BondSet (n * R.params.side)),
      Measurable fun p : X × TorusField n => f (p.1, (b, p.2, bad))) : Measurable f := by
  have h1 : Measurable fun z : (BaseChoice R.params.side n × BondSet (n * R.params.side)) × (X × TorusField n) =>
      f (z.2.1, (z.1.1, z.2.2, z.1.2)) :=
    measurable_from_prod_countable_right fun x => h x.1 x.2
  have h2 : Measurable fun u : X × StepOutcome R.params n =>
      (((u.2.1, u.2.2.2), (u.1, u.2.2.1)) :
        (BaseChoice R.params.side n × BondSet (n * R.params.side)) × (X × TorusField n)) :=
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
      (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  exact h1.comp h2
abbrev _root_.YangMills.SharedProofs.p30209 := @measurable_of_discrete_parts
private theorem measurable_stepOutcomeDensity (hS : StepTransitionDensityBounds)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad) :
    Measurable fun p : TorusField (n * R.params.side) × StepOutcome R.params n => stepOutcomeDensity R p.1 p.2 :=
  measurable_of_discrete_parts fun b bad => ((hS R.params R.coupling n).1 b).mul (hB bad)
end Step
section Chain
variable {ℓ : TorusLumps.StepParameters}
private theorem measurable_topField (s n : ℕ) : Measurable (topField ℓ s n) := by apply _root_.YangMills.SharedProofs.p12845 <;> assumption
private theorem stage_isCutoff (T : StageTower ℓ) (h : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (t : ℕ) :
    IsCutoff (T.stage t).toStepSetup.ballRadius (T.stage t).toStepSetup.barrierFn := by apply _root_.YangMills.SharedProofs.p16 <;> assumption
private theorem refine_side_dvd_and_le {n : ℕ} (h64 : 64 ≤ n) : ℓ.side ∣ n * ℓ.side ∧ 64 ≤ n * ℓ.side :=
  ⟨Dvd.intro_left n rfl, h64.trans (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero (NeZero.ne ℓ.side)))⟩
private theorem measurable_compose_pair {A B C D E : Type} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E] (g : A × B → D) (dr : D → C → E)
    (hg : Measurable g) (hdr : Measurable fun q : D × C => dr q.1 q.2) :
    Measurable fun p : A × B × C => ((g (p.1, p.2.1), dr (g (p.1, p.2.1)) p.2.2) : D × E) := by
  have h : Measurable fun p : A × B × C => g (p.1, p.2.1) :=
    hg.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  exact h.prodMk (hdr.comp (h.prodMk (measurable_snd.comp measurable_snd)))
private theorem chainNoiseMeasure_isProbability (s : ℕ) :
    ∀ (n : ℕ) [NeZero n], IsProbabilityMeasure (chainNoiseMeasure ℓ s n) := by apply _root_.YangMills.SharedProofs.p9681 <;> assumption
variable (hS : StepTransitionDensityBounds) (hBL : ClusterExpansionOfAStep.BaseLawIsProduct) (T : StageTower ℓ)
  (S : ChainSampler T) (hcut : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (hcoin : T.MarksMeasurable)
  (hD : ∀ s, (S s).IsFaithful) (β : ℝ)
include hcut hcoin hD in
private theorem measurable_sampleChain (s : ℕ) : ∀ (n : ℕ) [NeZero n], ℓ.side ∣ n → 64 ≤ n →
    Measurable (fun p : TorusField (fineSide ℓ.side s n) × ChainNoise ℓ s n => sampleChain T S s n p.1 p.2) := by
  induction s with
  | zero =>
    intro n _ _ _
    exact measurable_fst
  | succ s ih =>
    intro n _ hL h64
    have hg := refine_side_dvd_and_le (ℓ := ℓ) h64
    have ih' := ih (n * ℓ.side) hg.1 hg.2
    have hdr : Measurable fun q : MarkedSample ℓ s (n * ℓ.side) × StepNoise ℓ n =>
        (S s).sample (topField ℓ s (n * ℓ.side) q.1) q.2 :=
      (measurable_sample (S s) (hD s) (stage_isCutoff T hcut s) ⟨hL, h64⟩ (fun bad => hcoin s n bad)).comp
        (((measurable_topField s (n * ℓ.side)).comp measurable_fst).prodMk measurable_snd)
    exact measurable_compose_pair (fun q : TorusField (fineSide ℓ.side s (n * ℓ.side)) ×
      ChainNoise ℓ s (n * ℓ.side) => sampleChain T S s (n * ℓ.side) q.1 q.2)
      (fun a c => (S s).sample (topField ℓ s (n * ℓ.side) a) c) ih' hdr
include hS hBL hcut hcoin hD in
private theorem map_sampleChain (s : ℕ) : ∀ (n : ℕ) [NeZero n], ℓ.side ∣ n → 64 ≤ n →
    Measure.map (fun p : TorusField (fineSide ℓ.side s n) × ChainNoise ℓ s n => sampleChain T S s n p.1 p.2)
      ((wilsonLaw β (fineSide ℓ.side s n)).prod (chainNoiseMeasure ℓ s n)) = markedSampleLaw T β s n := by
  induction s with
  | zero =>
    intro n _ _ _
    haveI : SFinite (wilsonLaw β n) := by
      unfold wilsonLaw
      infer_instance
    haveI := chainNoiseMeasure_isProbability (ℓ := ℓ) 0 n
    have e := Measure.map_fst_prod (μ := wilsonLaw β n) (ν := chainNoiseMeasure ℓ 0 n)
    rw [measure_univ, one_smul] at e
    exact e
  | succ s ih =>
    intro n _ hL h64
    have hg := refine_side_dvd_and_le (ℓ := ℓ) h64
    have ih' := ih (n * ℓ.side) hg.1 hg.2
    haveI := chainNoiseMeasure_isProbability (ℓ := ℓ) s (n * ℓ.side)
    haveI : IsProbabilityMeasure (stepNoiseMeasure ℓ n) := by
      unfold stepNoiseMeasure
      infer_instance
    haveI : SFinite (wilsonLaw β (fineSide ℓ.side s (n * ℓ.side))) := by
      unfold wilsonLaw
      infer_instance
    haveI : SFinite (stepReferenceMeasure ℓ n) := by
      unfold stepReferenceMeasure
      infer_instance
    have hdr : Measurable fun q : MarkedSample ℓ s (n * ℓ.side) × StepNoise ℓ n =>
        (S s).sample (topField ℓ s (n * ℓ.side) q.1) q.2 :=
      (measurable_sample (S s) (hD s) (stage_isCutoff T hcut s) ⟨hL, h64⟩ (fun bad => hcoin s n bad)).comp
        (((measurable_topField s (n * ℓ.side)).comp measurable_fst).prodMk measurable_snd)
    have hmg := measurable_sampleChain T S hcut hcoin hD s (n * ℓ.side) hg.1 hg.2
    have hw : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
        ENNReal.ofReal (stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2) :=
      ((measurable_stepOutcomeDensity (R := (T.stage s).toStepSetup) (n := n) hS (fun bad => hcoin s n bad)).comp
        (((measurable_topField s (n * ℓ.side)).comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal
    have key := map_prod_eq_withDensity (wilsonLaw β (fineSide ℓ.side s (n * ℓ.side)))
      (chainNoiseMeasure ℓ s (n * ℓ.side)) (stepNoiseMeasure ℓ n) (stepReferenceMeasure ℓ n)
      (fun q : TorusField (fineSide ℓ.side s (n * ℓ.side)) × ChainNoise ℓ s (n * ℓ.side) =>
        sampleChain T S s (n * ℓ.side) q.1 q.2) (fun a c => (S s).sample (topField ℓ s (n * ℓ.side) a) c)
      (fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
        ENNReal.ofReal (stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2))
      hmg (measurable_compose_pair (fun q : TorusField (fineSide ℓ.side s (n * ℓ.side)) ×
        ChainNoise ℓ s (n * ℓ.side) => sampleChain T S s (n * ℓ.side) q.1 q.2)
        (fun a c => (S s).sample (topField ℓ s (n * ℓ.side) a) c) hmg hdr) hw
      (fun a F hF => lintegral_sample (S s) (hD s) hBL (stage_isCutoff T hcut s) ⟨hL, h64⟩
        (fun bad => hcoin s n bad) (topField ℓ s (n * ℓ.side) a) F hF)
    rw [ih'] at key
    exact key
end Chain
end SampleChainLaw
open SampleChainLaw in
theorem sampleChainLawStatement_holds (hBL : ClusterExpansionOfAStep.BaseLawIsProduct) (hS : StepTransitionDensityBounds) :
    sampleChainLawStatement :=
  fun _ _ T S β _ hcut hcoin hD s n _ hL h64 =>
    ⟨measurable_sampleChain T S hcut hcoin hD s n hL h64, map_sampleChain hS hBL T S hcut hcoin hD β s n hL h64⟩
end YangMills.Construction.CellWindows
end
