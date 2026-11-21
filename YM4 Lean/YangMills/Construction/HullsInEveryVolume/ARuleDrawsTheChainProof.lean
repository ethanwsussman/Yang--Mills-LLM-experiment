import YangMills.Construction.CellOfTheFlow.TheNoiseDrawsTheChainProof
import YangMills.Construction.LawByMomentsOfTheFlow.HullsInALimitFieldProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal Quaternion
namespace YangMills.Construction.ChainNoise
open TorusFields TorusLumps StepSettings StepCosts WeightedResponses BlockAverages LumpContours
section Abstract
theorem map_prod_draw_eq_withDensity {A B C E D : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSpace E] [MeasurableSpace D] (μ : Measure A) (N : Measure B) (St : Measure C) (ρ : Measure E)
    [SFinite μ] [SFinite N] [SFinite St] [SFinite ρ]
    (g : A × B → D) (dr : D → C → E) (w : D × E → ℝ≥0∞) (hg : Measurable g)
    (hf : Measurable fun p : A × B × C => ((g (p.1, p.2.1), dr (g (p.1, p.2.1)) p.2.2) : D × E))
    (hw : Measurable w)
    (hstep : ∀ (a : D) (F : E → ℝ≥0∞), Measurable F → ∫⁻ c, F (dr a c) ∂St = ∫⁻ e, F e * w (a, e) ∂ρ) :
    (μ.prod (N.prod St)).map (fun p : A × B × C => ((g (p.1, p.2.1), dr (g (p.1, p.2.1)) p.2.2) : D × E)) =
      (((μ.prod N).map g).prod ρ).withDensity w := by apply _root_.YangMills.SharedProofs.p2276 <;> assumption
theorem lintegral_three_draws {U V₀ W₀ Bc Fl Bd : Type} [MeasurableSpace U] [MeasurableSpace V₀] [MeasurableSpace W₀]
    [MeasurableSpace Bc] [MeasurableSpace Fl] [MeasurableSpace Bd] [Fintype Bc] [Fintype Bd]
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
        ∂((Measure.count : Measure Bc).prod (H.prod (Measure.count : Measure Bd))) := by apply _root_.YangMills.SharedProofs.p99551 <;> assumption
theorem lintegral_comp_of_finite {Ω α : Type} [MeasurableSpace Ω] [MeasurableSpace α] [Fintype α]
    [MeasurableSingletonClass α] (P : Measure Ω) (f : Ω → α) (hf : Measurable f) (p : α → ℝ≥0∞)
    (hp : ∀ a, P (f ⁻¹' {a}) = p a) (G : α → ℝ≥0∞) : ∫⁻ ω, G (f ω) ∂P = ∑ a, G a * p a := by apply _root_.YangMills.SharedProofs.p60989 <;> assumption
theorem pi_withDensity_eq {ι X : Type} [Fintype ι] [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (k : ι → X → ℝ≥0∞) (hk : ∀ i, Measurable (k i)) [∀ i, SigmaFinite (ν.withDensity (k i))] :
    Measure.pi (fun i => ν.withDensity (k i)) =
      (Measure.pi fun _ : ι => ν).withDensity fun x => ∏ i, k i (x i) := by apply _root_.YangMills.SharedProofs.p56082 <;> assumption
theorem measurableSet_preimage_finset {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (f : Ω → Finset ι)
    (h : ∀ i, MeasurableSet {ω | i ∈ f ω}) (bad : Finset ι) : MeasurableSet (f ⁻¹' {bad}) := by apply _root_.YangMills.SharedProofs.p29435 <;> assumption
end Abstract
section Cutoff
theorem cutoffFactor_mem_unit {ρ : ℝ} {p : ℝ → ℝ} (h : ColdStepAtMirrorFrames.IsCutoff ρ p) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ ColdStepAtMirrorFrames.cutoffFactor ρ p u ∧ ColdStepAtMirrorFrames.cutoffFactor ρ p u ≤ 1 := by apply _root_.YangMills.SharedProofs.p2957 <;> assumption
end Cutoff
instance (L n : ℕ) : DiscreteMeasurableSpace (BaseChoice L n) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
instance (m : ℕ) : DiscreteMeasurableSpace (BondSet m) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
instance (m : ℕ) [NeZero m] : Fintype (BondSet m) := inferInstanceAs (Fintype (Finset (TorusBond m)))
section Marks
variable (R : StepSetup) {n : ℕ} [NeZero n]
theorem bondMark_mem_unit (hc : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (b : TorusBond (n * R.params.side)) :
    0 ≤ bondMark R V W b ∧ bondMark R V W b ≤ 1 :=
  cutoffFactor_mem_unit hc (norm_nonneg _)
open Classical in
def markedBadBonds (W : TorusField (n * R.params.side)) (V : TorusField n) (w : TorusBond (n * R.params.side) → I) :
    Finset (TorusBond (n * R.params.side)) :=
  (markedBonds R (hotCoreSites R V)).filter fun b => ¬ (((w b : I) : ℝ) < bondMark R V W b)
def markedBadBondSet (W : TorusField (n * R.params.side)) (V : TorusField n)
    (w : TorusBond (n * R.params.side) → I) : BondSet (n * R.params.side) :=
  markedBadBonds R W V w
theorem mem_markedBadBonds (W : TorusField (n * R.params.side)) (V : TorusField n)
    (w : TorusBond (n * R.params.side) → I) (b : TorusBond (n * R.params.side)) :
    b ∈ markedBadBonds R W V w ↔
      b ∈ markedBonds R (hotCoreSites R V) ∧ bondMark R V W b ≤ ((w b : I) : ℝ) := by
  classical
  unfold markedBadBonds
  rw [Finset.mem_filter, not_lt]
theorem sum_powerset_prod_ite_eq {ι : Type} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ) :
    ∑ t ∈ s.powerset, ∏ i ∈ s, (if i ∈ t then f i else g i) = ∏ i ∈ s, (f i + g i) := by apply _root_.YangMills.SharedProofs.p12670 <;> assumption
open Classical in
def goodMargin (W : TorusField (n * R.params.side)) (V : TorusField n) (b : TorusBond (n * R.params.side)) : ℝ :=
  ∑ bad : Finset (TorusBond (n * R.params.side)), if b ∈ bad then 0 else markLaw R W V bad
theorem markLaw_eq_ite (hg : R.params.side ∣ n ∧ 64 ≤ n) (W : TorusField (n * R.params.side)) (V : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side))) :
    markLaw R W V bad = open Classical in if bad ∈ (markedBonds R (hotCoreSites R V)).powerset then
      ∏ b ∈ markedBonds R (hotCoreSites R V), (if b ∈ bad then 1 - bondMark R V W b else bondMark R V W b) else 0 := by
  classical
  simp only [markLaw, markProduct, Finset.mem_powerset, if_pos hg]
theorem goodMargin_eq (hg : R.params.side ∣ n ∧ 64 ≤ n) (W : TorusField (n * R.params.side)) (V : TorusField n)
    (b : TorusBond (n * R.params.side))
    (hb : b ∈ markedBonds R (hotCoreSites R V)) : goodMargin R W V b = bondMark R V W b := by
  classical
  set Mk := markedBonds R (hotCoreSites R V) with hMk
  set f : TorusBond (n * R.params.side) → ℝ := fun i => if i = b then 0 else 1 - bondMark R V W i with hf
  have h1 : goodMargin R W V b = ∑ t ∈ Mk.powerset, if b ∈ t then 0 else
      ∏ i ∈ Mk, (if i ∈ t then 1 - bondMark R V W i else bondMark R V W i) := by
    unfold goodMargin
    have e : ∀ bad : Finset (TorusBond (n * R.params.side)), (if b ∈ bad then (0 : ℝ) else markLaw R W V bad) =
        if bad ∈ Mk.powerset then (if b ∈ bad then 0 else
          ∏ i ∈ Mk, (if i ∈ bad then 1 - bondMark R V W i else bondMark R V W i)) else 0 := by
      intro bad
      rw [markLaw_eq_ite R hg]
      by_cases h1 : bad ∈ Mk.powerset <;> by_cases h2 : b ∈ bad <;> simp [h1, h2, hMk]
    simp only [e]
    rw [Finset.sum_ite_mem Finset.univ, Finset.univ_inter]
  rw [h1]
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
theorem measurable_markedBadBondSet
    (hH : ∀ a : Finset (TorusSite n), MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (hg : R.params.side ∣ n ∧ 64 ≤ n)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad) :
    Measurable fun p : TorusField (n * R.params.side) × TorusField n × (TorusBond (n * R.params.side) → I) =>
      markedBadBondSet R p.1 p.2.1 p.2.2 := by
  classical
  have hm : ∀ b, Measurable fun p : TorusField (n * R.params.side) × TorusField n => goodMargin R p.1 p.2 b := by
    intro b
    unfold goodMargin
    refine Finset.measurable_sum _ fun bad _ => ?_
    by_cases hb : b ∈ bad
    · simp only [hb, if_true]
      exact measurable_const
    · simp only [hb, if_false]
      exact hB bad
  have hmk : ∀ b, MeasurableSet {V : TorusField n | b ∈ markedBonds R (hotCoreSites R V)} := by
    intro b
    have e : {V : TorusField n | b ∈ markedBonds R (hotCoreSites R V)} =
        ⋃ a ∈ (Finset.univ.filter fun a : Finset (TorusSite n) => b ∈ markedBonds R a),
          {V : TorusField n | hotCoreSites R V = a} := by
      ext V
      simp
    rw [e]
    exact Finset.measurableSet_biUnion _ fun a _ => hH a
  have hlt : ∀ b, MeasurableSet {p : TorusField (n * R.params.side) × TorusField n × (TorusBond (n * R.params.side) → I) |
      b ∈ markedBadBonds R p.1 p.2.1 p.2.2} := by
    intro b
    have e : {p : TorusField (n * R.params.side) × TorusField n × (TorusBond (n * R.params.side) → I) |
        b ∈ markedBadBonds R p.1 p.2.1 p.2.2} =
        {p | p.2.1 ∈ {V : TorusField n | b ∈ markedBonds R (hotCoreSites R V)}} ∩
          {p | goodMargin R p.1 p.2.1 b ≤ ((p.2.2 b : I) : ℝ)} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      rw [mem_markedBadBonds]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [goodMargin_eq R hg _ _ _ h1]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [goodMargin_eq R hg _ _ _ h1] at h2; exact h2⟩
    rw [e]
    have hp : Measurable fun p : TorusField (n * R.params.side) × TorusField n × (TorusBond (n * R.params.side) → I) =>
        ((p.1, p.2.1) : TorusField (n * R.params.side) × TorusField n) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have h1 := (hm b).comp hp
    have hq : Measurable fun p : TorusField (n * R.params.side) × TorusField n × (TorusBond (n * R.params.side) → I) =>
        p.2.2 := measurable_snd.comp measurable_snd
    have h2 : Measurable fun p : TorusField (n * R.params.side) × TorusField n × (TorusBond (n * R.params.side) → I) =>
        ((p.2.2 b : I) : ℝ) :=
      measurable_subtype_coe.comp ((measurable_pi_apply b).comp hq)
    exact ((measurable_fst.comp measurable_snd) (hmk b)).inter (measurableSet_le h1 h2)
  exact measurable_to_countable' fun bad =>
    measurableSet_preimage_finset (ι := TorusBond (n * R.params.side)) _ hlt bad
theorem measurable_markedBadBondSet_uniform (W : TorusField (n * R.params.side)) (V : TorusField n) :
    Measurable (markedBadBondSet R W V) := by
  have hlt : ∀ b, MeasurableSet {w : TorusBond (n * R.params.side) → I | b ∈ markedBadBonds R W V w} := by
    intro b
    by_cases hb : b ∈ markedBonds R (hotCoreSites R V)
    · have e : {w : TorusBond (n * R.params.side) → I | b ∈ markedBadBonds R W V w} =
          {w | bondMark R V W b ≤ ((w b : I) : ℝ)} := by
        ext w
        simpa [hb] using mem_markedBadBonds R W V w b
      rw [e]
      exact measurableSet_le measurable_const (measurable_subtype_coe.comp (measurable_pi_apply b))
    · have e : {w : TorusBond (n * R.params.side) → I | b ∈ markedBadBonds R W V w} = ∅ := by
        ext w
        simpa [hb] using mem_markedBadBonds R W V w b
      rw [e]
      exact MeasurableSet.empty
  exact measurable_to_countable' fun bad =>
    measurableSet_preimage_finset (ι := TorusBond (n * R.params.side)) _ hlt bad
theorem pi_preimage_markedBadBonds (hc : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn)
    (hg : R.params.side ∣ n ∧ 64 ≤ n) (W : TorusField (n * R.params.side)) (V : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side))) :
    (Measure.pi fun _ : TorusBond (n * R.params.side) => (volume : Measure I)) (markedBadBonds R W V ⁻¹' {bad}) =
      ENNReal.ofReal (markLaw R W V bad) := by
  classical
  set Mk := markedBonds R (hotCoreSites R V) with hMk
  have hbd := fun b => bondMark_mem_unit R hc V W b
  let mI : TorusBond (n * R.params.side) → I := fun b => ⟨bondMark R V W b, (hbd b).1, (hbd b).2⟩
  by_cases hsub : bad ⊆ Mk
  · let A : TorusBond (n * R.params.side) → Set I := fun b =>
      if b ∈ Mk then (if b ∈ bad then Set.Ici (mI b) else Set.Iio (mI b))
      else Set.univ
    have e : markedBadBonds R W V ⁻¹' {bad} = Set.univ.pi A := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_imp_iff]
      constructor
      · intro h b
        have hm := mem_markedBadBonds R W V w b
        rw [h] at hm
        simp only [A]
        by_cases hb : b ∈ Mk
        · rw [if_pos hb]
          by_cases hbb : b ∈ bad
          · rw [if_pos hbb]
            exact (hm.1 hbb).2
          · rw [if_neg hbb]
            by_contra hcn
            exact hbb (hm.2 ⟨hb, not_lt.1 hcn⟩)
        · rw [if_neg hb]
          exact Set.mem_univ _
      · intro h
        refine Finset.ext fun b => ?_
        refine (mem_markedBadBonds R W V w b).trans ?_
        have hb' := h b
        simp only [A] at hb'
        constructor
        · rintro ⟨h1, h2⟩
          rw [if_pos h1] at hb'
          by_contra hbb
          rw [if_neg hbb] at hb'
          exact absurd h2 (not_le.2 hb')
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
            exact unitInterval.volume_Ici (mI b)
          · simp only [if_pos hb, if_neg hbb]
            exact unitInterval.volume_Iio (mI b)
        · simp only [if_neg hb]
          exact measure_univ
      simp only [h1]
      rw [Finset.prod_ite_mem Finset.univ, Finset.univ_inter]
    · intro b _
      have := hbd b
      split_ifs <;> linarith [this.1, this.2]
  · have hempty : markedBadBonds R W V ⁻¹' {bad} = ∅ := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      apply hsub
      intro b hb
      have := (mem_markedBadBonds R W V w b).1 (by rw [h]; exact hb)
      exact this.1
    rw [hempty, measure_empty, markLaw_eq_ite R hg, if_neg (fun h => hsub (Finset.mem_powerset.1 h)),
      ENNReal.ofReal_zero]
end Marks
section Offsets
variable (ℓ : StepParameters) {n : ℕ} [NeZero n]
def centredOffset (L : ℕ) (o : BlockOffset L) : Fin 4 → ℤ := fun i => ((o i : ℕ) : ℤ) - ((L : ℤ) - 1) / 2
theorem centredOffset_injective (L : ℕ) : Function.Injective (centredOffset L) := by
  intro o o' h
  funext i
  have h1 := congrFun h i
  simp only [centredOffset] at h1
  exact Fin.ext (by omega)
theorem centredOffset_mem {L : ℕ} (hodd : Odd L) (o : BlockOffset L) : centredOffset L o ∈ centredCube L := by
  rw [TorusContours.mem_centredCube_iff]
  intro i
  obtain ⟨H, hH⟩ := hodd
  have h1 := (o i).2
  have hL : ((L : ℤ) - 1) / 2 = (H : ℤ) := by
    subst hH
    push_cast
    omega
  simp only [centredOffset]
  rw [hL]
  constructor <;> omega
theorem baseChoiceOfOffsets_apply (o : TorusSite n → BlockOffset ℓ.side) (x : TorusSite n) :
    baseChoiceOfOffsets o (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x) =
      siteAtOffset (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x) (centredOffset ℓ.side (o x)) := by
  have hx : toTorusSite n (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x) = x :=
    TopLevelSites.toTorusSite_torusSiteInFrame TorusContours.stepBlockFrame_period_one x
  show torusSiteInFrame (stepBlockFrame ℓ.side n) 0 (blockSite (toTorusSite n (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x))
    (o (toTorusSite n (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x)))) = _
  rw [hx]
  unfold blockSite
  rw [BlockOffsets.torusSiteInFrame_siteOfInt]
  have hc : (cellCentre (stepBlockFrame ℓ.side n).depth (siteOfCoords 1 fun i => ((x i).cast : ℤ)) :
      (stepBlockFrame ℓ.side n).Site 0) =
      siteOfCoords 0 fun i => (ℓ.side : ℤ) * ((x i).cast : ℤ) := TorusContours.cellCentre_siteOfCoords _
  have hs : (siteOfCoords 0 (fun i => (ℓ.side : ℤ) * ((x i).cast : ℤ) + (((o x i : ℕ) : ℤ) - ((ℓ.side : ℤ) - 1) / 2)) :
      (stepBlockFrame ℓ.side n).Site 0) =
      siteOfCoords 0 (fun i => (ℓ.side : ℤ) * ((x i).cast : ℤ)) + siteOfCoords 0 (centredOffset ℓ.side (o x)) :=
    BlockOffsets.siteOfCoords_add 0 _ _
  exact hs.trans (congrArg (· + (siteOfCoords 0 (centredOffset ℓ.side (o x)) : (stepBlockFrame ℓ.side n).Site 0))
    hc.symm)
theorem centredOffset_siteOffset (hodd : Odd ℓ.side) (y : (stepBlockFrame ℓ.side n).Cell) {z : Fin 4 → ℤ}
    (hz : z ∈ centredCube ℓ.side) :
    centredOffset ℓ.side (siteOffset (toTorusSite (n * ℓ.side) (siteAtOffset y z : (stepBlockFrame ℓ.side n).Site 0))) = z := by
  funext i
  obtain ⟨H, hH⟩ := hodd
  have hLz : ((ℓ.side : ℤ) - 1) / 2 = (H : ℤ) := by
    rw [hH]
    push_cast
    omega
  have hb := (TorusContours.mem_centredCube_iff.mp hz) i
  rw [hLz] at hb
  have e1 : (toTorusSite (n * ℓ.side) (siteAtOffset y z : (stepBlockFrame ℓ.side n).Site 0) : TorusSite (n * ℓ.side)) =
      siteOfInt fun i => (ℓ.side : ℤ) * siteCoords y i + z i := by
    rw [TorusContours.siteAtOffset_eq]
    exact TorusContours.toTorusSite_siteOfCoords TorusContours.stepBlockFrame_period_zero _
  rw [e1]
  simp only [centredOffset, siteOffset, siteOfInt]
  rw [TorusBlocks.cast_intCast_eq_sub_mul_ediv, hLz]
  have e2 : ((ℓ.side : ℤ) * siteCoords y i + z i - ((n * ℓ.side : ℕ) : ℤ) *
      (((ℓ.side : ℤ) * siteCoords y i + z i) / ((n * ℓ.side : ℕ) : ℤ)) + (H : ℤ)) % (ℓ.side : ℤ) =
      z i + H := by
    have : (ℓ.side : ℤ) * siteCoords y i + z i - ((n * ℓ.side : ℕ) : ℤ) *
        (((ℓ.side : ℤ) * siteCoords y i + z i) / ((n * ℓ.side : ℕ) : ℤ)) + (H : ℤ) =
        (z i + H) + (ℓ.side : ℤ) * (siteCoords y i - (n : ℤ) *
          (((ℓ.side : ℤ) * siteCoords y i + z i) / ((n * ℓ.side : ℕ) : ℤ))) := by
      push_cast
      ring
    rw [this, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [e2]
  have e3 : ((Fin.ofNat ℓ.side (z i + H).toNat : Fin ℓ.side) : ℕ) = (z i + H).toNat := by
    rw [Fin.val_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [e3]
  omega
def offsetsOfBaseChoice (b : BaseChoice ℓ.side n) : TorusSite n → BlockOffset ℓ.side :=
  fun y => siteOffset (toTorusSite (n * ℓ.side) (b (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 y)))
theorem offsets_baseChoice (hodd : Odd ℓ.side) (o : TorusSite n → BlockOffset ℓ.side) :
    offsetsOfBaseChoice ℓ (baseChoiceOfOffsets o) = o := by
  funext y
  apply centredOffset_injective ℓ.side
  have h := centredOffset_siteOffset ℓ hodd (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 y)
    (centredOffset_mem hodd (o y))
  exact (congrArg (fun q : (stepBlockFrame ℓ.side n).Site 0 =>
    centredOffset ℓ.side (siteOffset (toTorusSite (n * ℓ.side) q)))
    (baseChoiceOfOffsets_apply ℓ o y)).trans h
theorem baseChoice_offsets (hodd : Odd ℓ.side) (b : BaseChoice ℓ.side n)
    (hb : ∀ y, ∃ z ∈ centredCube ℓ.side, b y = siteAtOffset y z) :
    baseChoiceOfOffsets (offsetsOfBaseChoice ℓ b) = b := by
  funext y
  obtain ⟨x, rfl⟩ : ∃ x : TorusSite n, torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x = y :=
    ⟨toTorusSite n y, TopLevelSites.torusSiteInFrame_toTorusSite TorusContours.stepBlockFrame_period_one y⟩
  obtain ⟨z, hz, e⟩ := hb (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x)
  have h2 : centredOffset ℓ.side (offsetsOfBaseChoice ℓ b x) = z :=
    (congrArg (fun q : (stepBlockFrame ℓ.side n).Site 0 =>
      centredOffset ℓ.side (siteOffset (toTorusSite (n * ℓ.side) q))) e).trans
      (centredOffset_siteOffset ℓ hodd _ hz)
  exact (baseChoiceOfOffsets_apply ℓ (offsetsOfBaseChoice ℓ b) x).trans ((congrArg _ h2).trans e.symm)
theorem baseChoice_offsets_of_mem (hodd : Odd ℓ.side) {w : (stepBlockFrame ℓ.side n).GaugeField 0}
    {b : BaseChoice ℓ.side n} (hb : b ∈ baseChoices ℓ w) :
    baseChoiceOfOffsets (offsetsOfBaseChoice ℓ b) = b := by
  classical
  have h := (Finset.mem_filter.mp hb).2
  have hL : 1 ≤ (stepBlockFrame ℓ.side n).blockSide := Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
  exact baseChoice_offsets ℓ hodd b fun y => TorusContours.exists_centredCube_of_isBaseChoice hL h y
end Offsets
section Step
variable {R : StepSetup} {n : ℕ} [NeZero n]
structure UniformStepRule (R : StepSetup) (n : ℕ) [NeZero n]
    (bF : TorusField (n * R.params.side) → TorusSite n → I → BlockOffset R.params.side)
    (vF : TorusField (n * R.params.side) → (TorusSite n → BlockOffset R.params.side) → TorusBond n → I →
      UnitQuaternion) : Prop where
  base_measurable : ∀ y : TorusSite n, Measurable fun p : TorusField (n * R.params.side) × I => bF p.1 y p.2
  value_measurable : ∀ (o : TorusSite n → BlockOffset R.params.side) (c : TorusBond n),
    Measurable fun p : TorusField (n * R.params.side) × I => vF p.1 o c p.2
  base_law : ∀ (W : TorusField (n * R.params.side)) (o : TorusSite n → BlockOffset R.params.side),
    (Measure.pi fun _ : TorusSite n => (volume : Measure I)).real {U | ∀ y, bF W y (U y) = o y} =
      baseLaw (R := R) W (baseChoiceOfOffsets o)
  value_law : ∀ (W : TorusField (n * R.params.side)) (o : TorusSite n → BlockOffset R.params.side) (c : TorusBond n),
    (volume : Measure I).map (vF W o c) =
      haarUnit.withDensity fun h => ENNReal.ofReal
        (bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
          (readAtLevel (stepBlockFrame R.params.side n) 1 (fun _ _ => h : TorusField n)) (baseChoiceOfOffsets o)
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2))
variable {bF : TorusField (n * R.params.side) → TorusSite n → I → BlockOffset R.params.side}
  {vF : TorusField (n * R.params.side) → (TorusSite n → BlockOffset R.params.side) → TorusBond n → I → UnitQuaternion}
def drawnOffsets (bF : TorusField (n * R.params.side) → TorusSite n → I → BlockOffset R.params.side)
    (W : TorusField (n * R.params.side)) (u : TorusSite n → I) :
    TorusSite n → BlockOffset R.params.side := fun y => bF W y (u y)
def drawnField
    (vF : TorusField (n * R.params.side) → (TorusSite n → BlockOffset R.params.side) → TorusBond n → I → UnitQuaternion)
    (W : TorusField (n * R.params.side))
    (o : TorusSite n → BlockOffset R.params.side) (v : TorusBond n → I) : TorusField n :=
  fun x i => vF W o (x, i) (v (x, i))
def drawnOutcome (bF : TorusField (n * R.params.side) → TorusSite n → I → BlockOffset R.params.side)
    (vF : TorusField (n * R.params.side) → (TorusSite n → BlockOffset R.params.side) → TorusBond n → I → UnitQuaternion)
    (W : TorusField (n * R.params.side))
    (U : StepNoise R.params n) : StepOutcome R.params n :=
  (baseChoiceOfOffsets (drawnOffsets bF W U.1), drawnField vF W (drawnOffsets bF W U.1) U.2.1,
    markedBadBondSet R W (drawnField vF W (drawnOffsets bF W U.1) U.2.1) U.2.2)
def cellEquivTorusSite (L n : ℕ) [NeZero L] [NeZero n] : (stepBlockFrame L n).Cell ≃ TorusSite n where
  toFun := toTorusSite (F := stepBlockFrame L n) (j := 1) n
  invFun := torusSiteInFrame (stepBlockFrame L n) 1
  left_inv := TopLevelSites.torusSiteInFrame_toTorusSite TorusContours.stepBlockFrame_period_one
  right_inv := TopLevelSites.toTorusSite_torusSiteInFrame TorusContours.stepBlockFrame_period_one
theorem measurable_drawnOffsets (h : UniformStepRule R n bF vF) :
    Measurable fun p : TorusField (n * R.params.side) × (TorusSite n → I) => drawnOffsets bF p.1 p.2 :=
  measurable_pi_lambda _ fun y =>
    (h.base_measurable y).comp (measurable_fst.prodMk ((measurable_pi_apply y).comp measurable_snd))
theorem measurable_drawnField (h : UniformStepRule R n bF vF) :
    Measurable fun p : TorusField (n * R.params.side) × (TorusSite n → BlockOffset R.params.side) × (TorusBond n → I) =>
      drawnField vF p.1 p.2.1 p.2.2 := by
  refine measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun i => ?_
  have h1 : Measurable fun z : (TorusSite n → BlockOffset R.params.side) × (TorusField (n * R.params.side) × I) =>
      vF z.2.1 z.1 (x, i) z.2.2 :=
    measurable_from_prod_countable_right fun o => h.value_measurable o (x, i)
  have h2 : Measurable fun p : TorusField (n * R.params.side) × (TorusSite n → BlockOffset R.params.side) ×
      (TorusBond n → I) =>
      ((p.2.1, (p.1, p.2.2 (x, i))) : (TorusSite n → BlockOffset R.params.side) × (TorusField (n * R.params.side) × I)) :=
    (measurable_fst.comp measurable_snd).prodMk (measurable_fst.prodMk
      ((measurable_pi_apply (x, i)).comp (measurable_snd.comp measurable_snd)))
  exact h1.comp h2
theorem measurable_baseChoiceOfOffsets :
    Measurable (baseChoiceOfOffsets : (TorusSite n → BlockOffset R.params.side) → BaseChoice R.params.side n) :=
  Measurable.of_discrete
theorem measurable_drawnOutcome (h : UniformStepRule R n bF vF)
    (hH : ∀ a : Finset (TorusSite n), MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (hg : R.params.side ∣ n ∧ 64 ≤ n)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad) :
    Measurable fun p : TorusField (n * R.params.side) × StepNoise R.params n => drawnOutcome bF vF p.1 p.2 := by
  have h1 : Measurable fun p : TorusField (n * R.params.side) × StepNoise R.params n => drawnOffsets bF p.1 p.2.1 :=
    (measurable_drawnOffsets h).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h2 : Measurable fun p : TorusField (n * R.params.side) × StepNoise R.params n =>
      drawnField vF p.1 (drawnOffsets bF p.1 p.2.1) p.2.2.1 :=
    (measurable_drawnField h).comp (measurable_fst.prodMk (h1.prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd))))
  have h3 := (measurable_markedBadBondSet R hH hg hB).comp (measurable_fst.prodMk (h2.prodMk
    (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  exact (measurable_baseChoiceOfOffsets.comp h1).prodMk (h2.prodMk h3)
theorem pi_preimage_baseChoice (hodd : Odd R.params.side) (h : UniformStepRule R n bF vF)
    (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    (Measure.pi fun _ : TorusSite n => (volume : Measure I))
      ((fun u => baseChoiceOfOffsets (drawnOffsets bF W u)) ⁻¹' {b}) =
      ENNReal.ofReal (baseLaw (R := R) W b) := by
  classical
  by_cases hb : ∃ o : TorusSite n → BlockOffset R.params.side, baseChoiceOfOffsets o = b
  · obtain ⟨o, rfl⟩ := hb
    have e : (fun u => baseChoiceOfOffsets (drawnOffsets bF W u)) ⁻¹' {baseChoiceOfOffsets o} =
        {U | ∀ y, bF W y (U y) = o y} := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h1 y
        have h2 := congrArg (offsetsOfBaseChoice R.params) h1
        rw [offsets_baseChoice _ hodd, offsets_baseChoice _ hodd] at h2
        exact congrFun h2 y
      · intro h1
        exact congrArg baseChoiceOfOffsets (funext h1)
    rw [e, ← h.base_law W o, ofReal_measureReal]
  · have e : (fun u => baseChoiceOfOffsets (drawnOffsets bF W u)) ⁻¹' {b} = ∅ := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun h1 => hb ⟨_, h1⟩
    have e2 : baseLaw (R := R) W b = 0 := by
      unfold baseLaw
      rw [if_neg]
      intro h1
      exact hb ⟨_, baseChoice_offsets_of_mem R.params hodd h1⟩
    rw [e, e2, measure_empty, ENNReal.ofReal_zero]
def bondKernelAt (R : StepSetup) (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n)
    (c : TorusBond n) (g : UnitQuaternion) : ℝ :=
  bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
    (readAtLevel (stepBlockFrame R.params.side n) 1 (fun _ _ => g : TorusField n)) b
    (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2)
theorem zero_le_bondKernel (ℓ : StepParameters) (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (V : (stepBlockFrame ℓ.side n).GaugeField 1)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) : 0 ≤ bondKernel ℓ x W V b c := by
  unfold bondKernel
  exact div_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)
theorem measurable_bondKernelAt (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n)
    (c : TorusBond n) : Measurable (bondKernelAt R W b c) := by apply _root_.YangMills.DeltaSharedProofs.p3729 <;> assumption
theorem prod_bondKernel_eq (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) (V : TorusField n) :
    ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
      bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c =
    ∏ c : TorusBond n, bondKernelAt R W b c (V c.1 c.2) := by apply _root_.YangMills.DeltaSharedProofs.p500894 <;> assumption
theorem map_curry_pi_haarUnit (n : ℕ) [NeZero n] :
    (Measure.pi fun _ : TorusBond n => haarUnit).map (MeasurableEquiv.curry (TorusSite n) (Fin 4) UnitQuaternion) =
      fieldHaar n := by apply _root_.YangMills.SharedProofs.p84299 <;> assumption
theorem lintegral_drawnField (h : UniformStepRule R n bF vF) (W : TorusField (n * R.params.side))
    (o : TorusSite n → BlockOffset R.params.side) (G : TorusField n → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ v, G (drawnField vF W o v) ∂(Measure.pi fun _ : TorusBond n => (volume : Measure I)) =
      ∫⁻ V, G V * ∏ c : TorusBond n, ENNReal.ofReal (bondKernelAt R W (baseChoiceOfOffsets o) c (V c.1 c.2))
        ∂(fieldHaar n) := by
  let k : TorusBond n → UnitQuaternion → ℝ≥0∞ := fun c g => ENNReal.ofReal (bondKernelAt R W (baseChoiceOfOffsets o) c g)
  have hk : ∀ c, Measurable (k c) := fun c => (measurable_bondKernelAt W (baseChoiceOfOffsets o) c).ennreal_ofReal
  have hb : ∀ c, Measurable (vF W o c) := fun c => (h.value_measurable o c).comp measurable_prodMk_left
  have hmap : ∀ c, (volume : Measure I).map (vF W o c) = haarUnit.withDensity (k c) := fun c => h.value_law W o c
  haveI : ∀ c, IsProbabilityMeasure ((volume : Measure I).map (vF W o c)) := fun c =>
    Measure.isProbabilityMeasure_map (hb c).aemeasurable
  haveI : ∀ c, IsProbabilityMeasure (haarUnit.withDensity (k c)) := fun c => by
    rw [← hmap c]
    infer_instance
  have h1 : (Measure.pi fun _ : TorusBond n => (volume : Measure I)).map (fun v c => vF W o c (v c)) =
      (Measure.pi fun _ : TorusBond n => haarUnit).withDensity fun f => ∏ c, k c (f c) := by
    rw [Measure.pi_map_pi (fun c => (hb c).aemeasurable)]
    simp only [hmap]
    exact pi_withDensity_eq haarUnit k hk
  have hφ : Measurable fun (v : TorusBond n → I) (c : TorusBond n) => vF W o c (v c) :=
    measurable_pi_lambda _ fun c => (hb c).comp (measurable_pi_apply c)
  have hcur := (MeasurableEquiv.curry (TorusSite n) (Fin 4) UnitQuaternion).measurable
  have hPi : Measurable fun f : TorusBond n → UnitQuaternion => ∏ c, k c (f c) :=
    Finset.measurable_prod _ fun c _ => (hk c).comp (measurable_pi_apply c)
  have hGc : Measurable fun f : TorusBond n → UnitQuaternion =>
      G (MeasurableEquiv.curry (TorusSite n) (Fin 4) UnitQuaternion f) := hG.comp hcur
  have hL : ∫⁻ v, G (drawnField vF W o v) ∂(Measure.pi fun _ : TorusBond n => (volume : Measure I)) =
      ∫⁻ f, G (MeasurableEquiv.curry (TorusSite n) (Fin 4) UnitQuaternion f)
        ∂((Measure.pi fun _ : TorusBond n => (volume : Measure I)).map (fun v c => vF W o c (v c))) := by
    rw [lintegral_map hGc hφ]
    rfl
  have hRm : Measurable fun V : TorusField n =>
      G V * ∏ c : TorusBond n, ENNReal.ofReal (bondKernelAt R W (baseChoiceOfOffsets o) c (V c.1 c.2)) :=
    hG.mul (Finset.measurable_prod _ fun c _ =>
      (hk c).comp ((measurable_pi_apply c.2).comp (measurable_pi_apply c.1)))
  rw [hL, h1, lintegral_withDensity_eq_lintegral_mul _ hPi hGc, ← map_curry_pi_haarUnit n, lintegral_map hRm hcur]
  refine lintegral_congr fun f => ?_
  rw [Pi.mul_apply, mul_comm]
  rfl
theorem stepTransitionDensity_eq (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n)
    (V : TorusField n) :
    stepTransitionDensity R.params R.coupling W b V = baseLaw (R := R) W b *
      ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c := by apply _root_.YangMills.SharedProofs.p31947 <;> assumption
theorem zero_le_baseLaw (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    0 ≤ baseLaw (R := R) W b := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SmoothOffHull.baseLaw_nonneg_of_field <;> assumption
theorem lintegral_drawnOutcome (hodd : Odd R.params.side) (h : UniformStepRule R n bF vF)
    (hH : ∀ a : Finset (TorusSite n), MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (hc : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn)
    (hg : R.params.side ∣ n ∧ 64 ≤ n)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (W : TorusField (n * R.params.side)) (F : StepOutcome R.params n → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ξ, F (drawnOutcome bF vF W ξ) ∂(stepNoiseLaw R.params n) =
      ∫⁻ e, F e * ENNReal.ofReal (stepOutcomeDensity R W e) ∂(stepReferenceMeasure R.params n) := by
  have hmeas := measurable_drawnOutcome h hH hg hB
  have hbases : Measurable fun u : TorusSite n → I => baseChoiceOfOffsets (drawnOffsets bF W u) :=
    measurable_baseChoiceOfOffsets.comp ((measurable_drawnOffsets h).comp measurable_prodMk_left)
  have hoc : ∀ u : TorusSite n → I,
      offsetsOfBaseChoice R.params (baseChoiceOfOffsets (drawnOffsets bF W u)) = drawnOffsets bF W u :=
    fun u => offsets_baseChoice _ hodd _
  have hd : (fun ξ : (TorusSite n → I) × (TorusBond n → I) × (TorusBond (n * R.params.side) → I) =>
      ((baseChoiceOfOffsets (drawnOffsets bF W ξ.1),
        drawnField vF W (offsetsOfBaseChoice R.params (baseChoiceOfOffsets (drawnOffsets bF W ξ.1))) ξ.2.1,
        markedBadBondSet R W (drawnField vF W
          (offsetsOfBaseChoice R.params (baseChoiceOfOffsets (drawnOffsets bF W ξ.1))) ξ.2.1) ξ.2.2) :
        StepOutcome R.params n)) =
      fun ξ => drawnOutcome bF vF W ξ := by
    funext ξ
    simp only [hoc]
    rfl
  have hdm : Measurable fun ξ : (TorusSite n → I) × (TorusBond n → I) × (TorusBond (n * R.params.side) → I) =>
      ((baseChoiceOfOffsets (drawnOffsets bF W ξ.1),
        drawnField vF W (offsetsOfBaseChoice R.params (baseChoiceOfOffsets (drawnOffsets bF W ξ.1))) ξ.2.1,
        markedBadBondSet R W (drawnField vF W
          (offsetsOfBaseChoice R.params (baseChoiceOfOffsets (drawnOffsets bF W ξ.1))) ξ.2.1) ξ.2.2) :
        StepOutcome R.params n) := by
    have h0 : Measurable fun ξ : StepNoise R.params n =>
        ((W, ξ) : TorusField (n * R.params.side) × StepNoise R.params n) :=
      measurable_prodMk_left
    have h1 := hmeas.comp h0
    rw [hd]
    exact h1
  have hh := lintegral_three_draws (Measure.pi fun _ : TorusSite n => (volume : Measure I))
    (Measure.pi fun _ : TorusBond n => (volume : Measure I))
    (Measure.pi fun _ : TorusBond (n * R.params.side) => (volume : Measure I)) (fieldHaar n)
    (fun u => baseChoiceOfOffsets (drawnOffsets bF W u)) (fun b => drawnField vF W (offsetsOfBaseChoice R.params b))
    (markedBadBondSet R W)
    (fun b => ENNReal.ofReal (baseLaw (R := R) W b))
    (fun b V => ∏ c : TorusBond n,
      ENNReal.ofReal (bondKernelAt R W (baseChoiceOfOffsets (offsetsOfBaseChoice R.params b)) c (V c.1 c.2)))
    (fun V bad => ENNReal.ofReal (markLaw R W V bad))
    hdm
    (fun b => Finset.measurable_prod _ fun c _ => (measurable_bondKernelAt W _ c).ennreal_ofReal.comp
      ((measurable_pi_apply c.2).comp (measurable_pi_apply c.1)))
    (fun bad => ((hB bad).comp measurable_prodMk_left).ennreal_ofReal)
    (fun G => lintegral_comp_of_finite _ _ hbases _ (pi_preimage_baseChoice hodd h W) G)
    (fun b G hG => lintegral_drawnField h W (offsetsOfBaseChoice R.params b) G hG)
    (fun V G => lintegral_comp_of_finite (α := BondSet (n * R.params.side)) _ _
      (measurable_markedBadBondSet_uniform R W V) _
      (pi_preimage_markedBadBonds R hc hg W V) G)
    F hF
  have hL : ∫⁻ ξ, F (drawnOutcome bF vF W ξ) ∂(stepNoiseLaw R.params n) =
      ∫⁻ ξ, F (baseChoiceOfOffsets (drawnOffsets bF W ξ.1),
        drawnField vF W (offsetsOfBaseChoice R.params (baseChoiceOfOffsets (drawnOffsets bF W ξ.1))) ξ.2.1,
        markedBadBondSet R W (drawnField vF W
          (offsetsOfBaseChoice R.params (baseChoiceOfOffsets (drawnOffsets bF W ξ.1))) ξ.2.1) ξ.2.2)
        ∂(stepNoiseLaw R.params n) :=
    lintegral_congr fun ξ => congrArg F (congrFun hd ξ).symm
  refine hL.trans (Eq.trans hh ?_)
  unfold stepReferenceMeasure
  refine lintegral_congr fun e => ?_
  congr 1
  show ENNReal.ofReal (baseLaw (R := R) W e.1) *
      (∏ c : TorusBond n,
        ENNReal.ofReal (bondKernelAt R W (baseChoiceOfOffsets (offsetsOfBaseChoice R.params e.1)) c (e.2.1 c.1 c.2))) *
      ENNReal.ofReal (markLaw R W e.2.1 e.2.2) =
    ENNReal.ofReal (stepTransitionDensity R.params R.coupling W e.1 e.2.1 * markLaw R W e.2.1 e.2.2)
  by_cases hb : e.1 ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)
  · rw [baseChoice_offsets_of_mem R.params hodd hb]
    have hcn : 0 ≤ ∏ c : TorusBond n, bondKernelAt R W e.1 c (e.2.1 c.1 c.2) :=
      Finset.prod_nonneg fun c _ => zero_le_bondKernel _ _ _ _ _ _
    have hprod : ∏ c : TorusBond n, ENNReal.ofReal (bondKernelAt R W e.1 c (e.2.1 c.1 c.2)) =
        ENNReal.ofReal (∏ c : TorusBond n, bondKernelAt R W e.1 c (e.2.1 c.1 c.2)) :=
      (ENNReal.ofReal_prod_of_nonneg fun c _ => zero_le_bondKernel _ _ _ _ _ _).symm
    rw [stepTransitionDensity_eq, prod_bondKernel_eq,
      ENNReal.ofReal_mul (mul_nonneg (zero_le_baseLaw _ _) hcn),
      ENNReal.ofReal_mul (zero_le_baseLaw _ _), hprod]
  · have h0 : baseLaw (R := R) W e.1 = 0 := by
      unfold baseLaw
      exact if_neg hb
    have h1 : stepTransitionDensity R.params R.coupling W e.1 e.2.1 = 0 := by
      unfold stepTransitionDensity
      exact if_neg hb
    rw [h0, h1]
    simp
theorem measurable_of_discrete_slices {X : Type} [MeasurableSpace X] {f : X × StepOutcome R.params n → ℝ}
    (h : ∀ (b : BaseChoice R.params.side n) (bad : BondSet (n * R.params.side)),
      Measurable fun p : X × TorusField n => f (p.1, (b, p.2, bad))) : Measurable f := by apply _root_.YangMills.SharedProofs.p30209 <;> assumption
theorem measurable_stepOutcomeDensity (hS : StepTransitionDensityBounds)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad) :
    Measurable fun p : TorusField (n * R.params.side) × StepOutcome R.params n => stepOutcomeDensity R p.1 p.2 :=
  measurable_of_discrete_slices fun b bad => ((hS R.params R.coupling n).1 b).mul (hB bad)
end Step
section Chain
variable {ℓ : StepParameters}
theorem measurable_topField (s n : ℕ) : Measurable (topField ℓ s n) := by apply _root_.YangMills.SharedProofs.p12845 <;> assumption
theorem stage_isCutoff (T : StageTower ℓ)
    (h : ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (t : ℕ) :
    ColdStepAtMirrorFrames.IsCutoff (T.stage t).toStepSetup.ballRadius (T.stage t).toStepSetup.barrierFn := by apply _root_.YangMills.SharedProofs.p16 <;> assumption
theorem dvd_and_le_mul_side {n : ℕ} (h64 : 64 ≤ n) : ℓ.side ∣ n * ℓ.side ∧ 64 ≤ n * ℓ.side :=
  ⟨Dvd.intro_left n rfl, h64.trans (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero (NeZero.ne ℓ.side)))⟩
theorem measurable_draw_pair {A B C D E : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSpace D] [MeasurableSpace E] (g : A × B → D) (dr : D → C → E) (hg : Measurable g)
    (hdr : Measurable fun q : D × C => dr q.1 q.2) :
    Measurable fun p : A × B × C => ((g (p.1, p.2.1), dr (g (p.1, p.2.1)) p.2.2) : D × E) := by
  have h : Measurable fun p : A × B × C => g (p.1, p.2.1) :=
    hg.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  exact h.prodMk (hdr.comp (h.prodMk (measurable_snd.comp measurable_snd)))
theorem isProbabilityMeasure_chainNoiseLaw (s : ℕ) :
    ∀ (n : ℕ) [NeZero n], IsProbabilityMeasure (chainNoiseLaw ℓ s n) := by apply _root_.YangMills.SharedProofs.p2413 <;> assumption
variable (hS : StepTransitionDensityBounds) (hW : ResponseInTheExpansion.chainMeasurabilityStatement)
  (T : StageTower ℓ) (rule : NoiseRule ℓ)
  (hodd : Odd ℓ.side) (hcut : ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn)
  (hcoin : T.MarksMeasurable) (hr : rule.IsAdmissible T) (β : ℝ)
include hr in
theorem uniformStepRule_stage (s n : ℕ) [NeZero n] :
    UniformStepRule (T.stage s).toStepSetup n (rule.base s n) (rule.value s n) :=
  ⟨hr.base_measurable s n, hr.value_measurable s n, hr.base_law s n, hr.value_law s n⟩
theorem stepOutcome_eq_drawnOutcome (s n : ℕ) [NeZero n] (W : TorusField (n * ℓ.side)) (U : StepNoise ℓ n) :
    rule.stepOutcome T s n W U =
      drawnOutcome (R := (T.stage s).toStepSetup) (rule.base s n) (rule.value s n) W U := rfl
include hW hcoin hr in
theorem measurable_stepOutcome (s n : ℕ) [NeZero n] (hL : ℓ.side ∣ n) (h64 : 64 ≤ n) :
    Measurable fun p : TorusField (n * ℓ.side) × StepNoise ℓ n => rule.stepOutcome T s n p.1 p.2 := by
  have h := measurable_drawnOutcome (R := (T.stage s).toStepSetup) (uniformStepRule_stage T rule hr s n)
    (fun a => hW.1 (T.stage s).toStepSetup n a) ⟨hL, h64⟩ (fun bad => hcoin s n bad)
  have e : (fun p : TorusField (n * ℓ.side) × StepNoise ℓ n => rule.stepOutcome T s n p.1 p.2) =
      fun p => drawnOutcome (R := (T.stage s).toStepSetup) (rule.base s n) (rule.value s n) p.1 p.2 :=
    funext fun p => stepOutcome_eq_drawnOutcome T rule s n p.1 p.2
  rw [e]
  exact h
include hW hcut hcoin hr in
theorem measurable_chain (s : ℕ) : ∀ (n : ℕ) [NeZero n], ℓ.side ∣ n → 64 ≤ n →
    Measurable (fun p : TorusField (fineSide ℓ.side s n) × ChainNoise ℓ s n => rule.chain T s n p.1 p.2) := by
  induction s with
  | zero =>
    intro n _ _ _
    exact measurable_fst
  | succ s ih =>
    intro n _ hL h64
    have hg := dvd_and_le_mul_side (ℓ := ℓ) h64
    have ih' := ih (n * ℓ.side) hg.1 hg.2
    have hdr : Measurable fun q : MarkedSample ℓ s (n * ℓ.side) × StepNoise ℓ n =>
        rule.stepOutcome T s n (topField ℓ s (n * ℓ.side) q.1) q.2 := by
      have h := (measurable_stepOutcome hW T rule hcoin hr s n hL h64).comp
        (((measurable_topField s (n * ℓ.side)).comp measurable_fst).prodMk measurable_snd :
          Measurable fun q : MarkedSample ℓ s (n * ℓ.side) × StepNoise ℓ n =>
            ((topField ℓ s (n * ℓ.side) q.1, q.2) : TorusField (n * ℓ.side) × StepNoise ℓ n))
      exact h
    exact measurable_draw_pair (fun q : TorusField (fineSide ℓ.side s (n * ℓ.side)) × ChainNoise ℓ s (n * ℓ.side) =>
      rule.chain T s (n * ℓ.side) q.1 q.2)
      (fun a c => rule.stepOutcome T s n (topField ℓ s (n * ℓ.side) a) c) ih' hdr
include hS hW hodd hcut hcoin hr in
theorem map_chain_eq_markedSampleLaw (s : ℕ) : ∀ (n : ℕ) [NeZero n], ℓ.side ∣ n → 64 ≤ n →
    Measure.map (fun p : TorusField (fineSide ℓ.side s n) × ChainNoise ℓ s n => rule.chain T s n p.1 p.2)
      ((wilsonLaw β (fineSide ℓ.side s n)).prod (chainNoiseLaw ℓ s n)) = markedSampleLaw T β s n := by
  induction s with
  | zero =>
    intro n _ _ _
    haveI : SFinite (wilsonLaw β n) := by
      unfold wilsonLaw
      infer_instance
    haveI := isProbabilityMeasure_chainNoiseLaw (ℓ := ℓ) 0 n
    have e := Measure.map_fst_prod (μ := wilsonLaw β n) (ν := chainNoiseLaw ℓ 0 n)
    rw [measure_univ, one_smul] at e
    exact e
  | succ s ih =>
    intro n _ hL h64
    have hg := dvd_and_le_mul_side (ℓ := ℓ) h64
    have ih' := ih (n * ℓ.side) hg.1 hg.2
    haveI := isProbabilityMeasure_chainNoiseLaw (ℓ := ℓ) s (n * ℓ.side)
    haveI : IsProbabilityMeasure (stepNoiseLaw ℓ n) := by
      unfold stepNoiseLaw
      infer_instance
    haveI : SFinite (wilsonLaw β (fineSide ℓ.side s (n * ℓ.side))) := by
      unfold wilsonLaw
      infer_instance
    haveI : SFinite (stepReferenceMeasure ℓ n) := by
      unfold stepReferenceMeasure
      infer_instance
    have hdr : Measurable fun q : MarkedSample ℓ s (n * ℓ.side) × StepNoise ℓ n =>
        rule.stepOutcome T s n (topField ℓ s (n * ℓ.side) q.1) q.2 := by
      have h := (measurable_stepOutcome hW T rule hcoin hr s n hL h64).comp
        (((measurable_topField s (n * ℓ.side)).comp measurable_fst).prodMk measurable_snd :
          Measurable fun q : MarkedSample ℓ s (n * ℓ.side) × StepNoise ℓ n =>
            ((topField ℓ s (n * ℓ.side) q.1, q.2) : TorusField (n * ℓ.side) × StepNoise ℓ n))
      exact h
    have hmg := measurable_chain hW T rule hcut hcoin hr s (n * ℓ.side) hg.1 hg.2
    have hw : Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
        ENNReal.ofReal (stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2) :=
      ((measurable_stepOutcomeDensity (R := (T.stage s).toStepSetup) (n := n) hS (fun bad => hcoin s n bad)).comp
        (((measurable_topField s (n * ℓ.side)).comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal
    have key := map_prod_draw_eq_withDensity (wilsonLaw β (fineSide ℓ.side s (n * ℓ.side)))
      (chainNoiseLaw ℓ s (n * ℓ.side)) (stepNoiseLaw ℓ n)
      (stepReferenceMeasure ℓ n) (fun q : TorusField (fineSide ℓ.side s (n * ℓ.side)) × ChainNoise ℓ s (n * ℓ.side) =>
        rule.chain T s (n * ℓ.side) q.1 q.2) (fun a c => rule.stepOutcome T s n (topField ℓ s (n * ℓ.side) a) c)
      (fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n =>
        ENNReal.ofReal (stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2))
      hmg (measurable_draw_pair (fun q : TorusField (fineSide ℓ.side s (n * ℓ.side)) × ChainNoise ℓ s (n * ℓ.side) =>
        rule.chain T s (n * ℓ.side) q.1 q.2)
        (fun a c => rule.stepOutcome T s n (topField ℓ s (n * ℓ.side) a) c) hmg hdr) hw
      (fun a F hF => lintegral_drawnOutcome hodd (uniformStepRule_stage T rule hr s n)
        (fun a => hW.1 (T.stage s).toStepSetup n a)
        (stage_isCutoff T hcut s) ⟨hL, h64⟩ (fun bad => hcoin s n bad) (topField ℓ s (n * ℓ.side) a) F hF)
    rw [ih'] at key
    exact key
end Chain
theorem ruleDrawsChainStatement_holds (hS : StepTransitionDensityBounds)
    (hW : ResponseInTheExpansion.chainMeasurabilityStatement) :
    ruleDrawsChainStatement :=
  fun _ hfit T rule β hcut hcoin hr s n _ hL h64 =>
    ⟨measurable_chain hW T rule hcut hcoin hr s n hL h64,
      map_chain_eq_markedSampleLaw hS hW T rule hfit.L_odd hcut hcoin hr β s n hL h64⟩
end YangMills.Construction.ChainNoise
end
