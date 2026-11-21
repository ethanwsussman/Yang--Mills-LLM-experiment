import YangMills.Construction.FreeEnergiesOfTheFlow.StateOfAStepIsBorelProof
import YangMills.Construction.ResponseInTheExpansion.CaseMassesAreBorelInAParameter
import YangMills.Construction.ResponseInTheExpansion.MeanGivenTheStateOfAStep
import YangMills.Construction.SixteenPointsOnASmallTorus.CentringIsTheSumOfTheShiftsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open StepSettings TorusLumps TorusFields StepCosts StepGas ResponseInTheExpansion ClusterExpansionOfAStep BlockPlaces
  BlockAverages ColdStepAtMirrorFrames
namespace ConditionalMean
section SigmaSpaces
variable {X : Type} [MeasurableSpace X]
private theorem measurable_sigmaMk {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    Measurable (Sigma.mk a : β a → Sigma β) :=
  measurable_iff_le_map.2 (iInf_le _ a)
private theorem measurableEmbedding_sigmaMk {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableEmbedding (Sigma.mk a : β a → Sigma β) := by
  classical
  refine ⟨sigma_mk_injective, measurable_sigmaMk a, fun s hs => MeasurableSpace.measurableSet_iInf.2 fun a' => ?_⟩
  show MeasurableSet ((Sigma.mk a' : β a' → Sigma β) ⁻¹' (Sigma.mk a '' s))
  by_cases h : a' = a
  · subst h
    rwa [Set.preimage_image_eq _ sigma_mk_injective]
  · have e : (Sigma.mk a' : β a' → Sigma β) ⁻¹' (Sigma.mk a '' s) = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro x _ hx
      exact h (congrArg Sigma.fst hx).symm
    rw [e]
    exact MeasurableSet.empty
abbrev _root_.YangMills.SharedProofs.p4862 := @measurableEmbedding_sigmaMk
private theorem measurable_prod_sigma {A : Type} [Countable A] {β : A → Type} [∀ a, MeasurableSpace (β a)] {γ : Type}
    [MeasurableSpace γ] {f : X × Sigma β → γ} (h : ∀ a, Measurable fun p : X × β a => f (p.1, ⟨a, p.2⟩)) :
    Measurable f := by
  intro s hs
  have e : f ⁻¹' s = ⋃ a, Prod.map (id : X → X) (Sigma.mk a : β a → Sigma β) ''
      ((fun p : X × β a => f (p.1, ⟨a, p.2⟩)) ⁻¹' s) := by
    ext ⟨x, a, y⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image, Prod.exists, Prod.map_apply, id_eq]
    constructor
    · intro hx
      exact ⟨a, x, y, hx, rfl⟩
    · rintro ⟨a', x', y', hx, he⟩
      have h1 : x' = x := congrArg Prod.fst he
      have h2 : (⟨a', y'⟩ : Sigma β) = ⟨a, y⟩ := congrArg Prod.snd he
      rw [← h1, ← h2]
      exact hx
  rw [e]
  exact MeasurableSet.iUnion fun a =>
    (MeasurableEmbedding.id.prodMap (measurableEmbedding_sigmaMk a)).measurableSet_image.2 (h a hs)
private theorem measurable_of_countable_fibres {D Z : Type} [Countable D] [MeasurableSpace Z] (f : X → D)
    (hf : ∀ d, MeasurableSet {x | f x = d}) (G : D → X → Z) (hG : ∀ d, Measurable (G d)) :
    Measurable fun x => G (f x) x := by apply _root_.YangMills.SharedProofs.p23008 <;> assumption
private theorem integrable_of_posNeg_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Measurable f) (hp : ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≠ ⊤) (hm : ∫⁻ a, ENNReal.ofReal (-f a) ∂μ ≠ ⊤) :
    Integrable f μ := by apply _root_.YangMills.SharedProofs.p18814 <;> assumption
end SigmaSpaces
section Outcomes
variable {ℓ : TorusLumps.StepParameters}
private instance (L n : ℕ) : DiscreteMeasurableSpace (BaseChoice L n) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) : DiscreteMeasurableSpace (BondSet m) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) [NeZero m] : Fintype (BondSet m) := inferInstanceAs (Fintype (Finset (TorusBond m)))
private instance (ℓ : TorusLumps.StepParameters) (n : ℕ) [NeZero n] : SFinite (stepReferenceMeasure ℓ n) := by
  unfold stepReferenceMeasure
  infer_instance
private theorem measurable_of_outcome {X γ : Type} [MeasurableSpace X] [MeasurableSpace γ] {n : ℕ} [NeZero n]
    {f : X × StepOutcome ℓ n → γ}
    (h : ∀ (b : BaseChoice ℓ.side n) (bad : BondSet (n * ℓ.side)),
      Measurable fun p : X × TorusField n => f (p.1, (b, p.2, bad))) : Measurable f := by
  have h1 : Measurable fun z : (BaseChoice ℓ.side n × BondSet (n * ℓ.side)) × (X × TorusField n) =>
      f (z.2.1, (z.1.1, z.2.2, z.1.2)) :=
    measurable_from_prod_countable_right fun x => h x.1 x.2
  have h2 : Measurable fun u : X × StepOutcome ℓ n =>
      (((u.2.1, u.2.2.2), (u.1, u.2.2.1)) : (BaseChoice ℓ.side n × BondSet (n * ℓ.side)) × (X × TorusField n)) :=
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
      (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  exact h1.comp h2
private theorem lintegral_stepReference {n : ℕ} [NeZero n] {f : StepOutcome ℓ n → ENNReal} (hf : Measurable f) :
    ∫⁻ d, f d ∂(stepReferenceMeasure ℓ n) =
      ∑ b : BaseChoice ℓ.side n, ∫⁻ V, ∑ bad : BondSet (n * ℓ.side), f (b, V, bad) ∂(fieldHaar n) := by
  unfold stepReferenceMeasure
  rw [lintegral_prod _ hf.aemeasurable, lintegral_count, tsum_fintype]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hb : Measurable fun y : TorusField n × BondSet (n * ℓ.side) => f (b, y) := hf.comp measurable_prodMk_left
  rw [lintegral_prod _ hb.aemeasurable]
  refine lintegral_congr fun V => ?_
  rw [lintegral_count, tsum_fintype]
end Outcomes
section Marks
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem stepWeight_eq_mul (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    stepWeight R C V W Yt ωt bad b =
      R.labelWeight (n * R.params.side) W Yt ωt *
        (stepTransitionDensity R.params R.coupling W b V * markProduct R C V W bad) := by
  classical
  unfold stepWeight
  have : baseLaw (R := R) W b * (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
      bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) =
      stepTransitionDensity R.params R.coupling W b V := by
    by_cases hb : b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)
    · simp [baseLaw, stepTransitionDensity, hb]
    · simp [baseLaw, stepTransitionDensity, hb]
  rw [mul_assoc (R.labelWeight (n * R.params.side) W Yt ωt), this, mul_assoc]
private theorem isBlockTorusSide_mul (hn : R.params.n₀ ≤ n) : IsBlockTorusSide R.params (n * R.params.side) :=
  ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
private theorem sixtyFour_le (hR : R.IsWellPosed) (hn : R.params.n₀ ≤ n) : 64 ≤ n :=
  le_trans (le_trans (by norm_num) hR.admissible.n₀_ge) hn
private theorem labelWeight_nonneg (hR : R.IsWellPosed) (hn : R.params.n₀ ≤ n) {W : TorusField (n * R.params.side)}
    {Yt : Finset (TorusSite (n * R.params.side))} (ωt : Yt → R.labels.Ω) (hh : IsHullState R.params R.range W Yt) :
    0 ≤ R.labelWeight (n * R.params.side) W Yt ωt :=
  hR.hasExpansions.2.nonneg _ (isBlockTorusSide_mul hn) W Yt ωt hh
open Classical in
private def labelDensity (Yt : Finset (TorusSite (n * R.params.side)))
    (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : ENNReal :=
  if IsHullState R.params R.range p.1 Yt then ENNReal.ofReal (R.labelWeight (n * R.params.side) p.1 Yt p.2) else 0
private theorem labelDensity_measurable (hR : R.IsWellPosed) (hn : R.params.n₀ ≤ n)
    (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable (labelDensity (R := R) (n := n) Yt) := by
  classical
  have h := (hR.hasExpansions.2.borel (n * R.params.side) (isBlockTorusSide_mul hn) Yt).1
  have e : labelDensity (R := R) (n := n) Yt = fun p => ENNReal.ofReal
      (if IsHullState R.params (clusterRange R.coupling) p.1 Yt then R.labelWeight (n * R.params.side) p.1 Yt p.2
        else 0) := by
    funext p
    unfold labelDensity
    by_cases hh : IsHullState R.params (clusterRange R.coupling) p.1 Yt
    · rw [if_pos hh, if_pos (show IsHullState R.params R.range p.1 Yt from hh)]
    · rw [if_neg hh, if_neg (show ¬ IsHullState R.params R.range p.1 Yt from hh)]
      simp
  rw [e]
  exact h.ennreal_ofReal
private def caseDensity (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n)
    (p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : ENNReal :=
  labelDensity Yt p.2 * ENNReal.ofReal (stepTransitionDensity R.params R.coupling p.2.1 b p.1 * markLaw R p.2.1 p.1 bad)
private theorem caseDensity_measurable (hS : StepTransitionDensityBounds) (hR : R.IsWellPosed)
    (hn : R.params.n₀ ≤ n)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    Measurable (caseDensity (R := R) (n := n) bad Yt b) := by
  have h0 : Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      ((p.2.1, p.1) : TorusField (n * R.params.side) × TorusField n) :=
    (measurable_fst.comp measurable_snd).prodMk measurable_fst
  have h1 := ((hS R.params R.coupling n).1 b).comp h0
  have h2 := (hB bad).comp h0
  exact ((labelDensity_measurable hR hn Yt).comp measurable_snd).mul (h1.mul h2).ennreal_ofReal
open Classical in
private theorem caseDensity_eq (hR : R.IsWellPosed) (hn : R.params.n₀ ≤ n) (hd : R.params.side ∣ n)
    {V : TorusField n} {bad : Finset (TorusBond (n * R.params.side))}
    (hbad : bad ∈ (markedBonds R (hotCoreSites R V)).powerset) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side)) (ωt : Yt → R.labels.Ω) :
    caseDensity bad Yt b (V, W, ωt) = configurationWeight R (hotCoreSites R V) V bad Yt b W ωt := by
  unfold caseDensity labelDensity configurationWeight
  by_cases hh : IsHullState R.params R.range W Yt
  · simp only [if_pos hh]
    rw [← ENNReal.ofReal_mul (labelWeight_nonneg hR hn ωt hh), stepWeight_eq_mul]
    unfold markLaw
    rw [if_pos ⟨hd, sixtyFour_le hR hn⟩, if_pos (Finset.mem_powerset.mp hbad)]
  · simp only [if_neg hh, zero_mul]
open Classical in
private theorem caseDensity_of_not_marked (hR : R.IsWellPosed) (hn : R.params.n₀ ≤ n) (hd : R.params.side ∣ n)
    {V : TorusField n} {bad : Finset (TorusBond (n * R.params.side))}
    (hbad : bad ∉ (markedBonds R (hotCoreSites R V)).powerset) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side)) (ωt : Yt → R.labels.Ω) :
    caseDensity bad Yt b (V, W, ωt) = 0 := by
  unfold caseDensity markLaw
  rw [if_pos ⟨hd, sixtyFour_le hR hn⟩, if_neg fun h => hbad (Finset.mem_powerset.mpr h)]
  simp
end Marks
section Mass
variable {R : StepSetup} {n : ℕ} [NeZero n]
private abbrev CaseIntegrand (R : StepSetup) (n : ℕ) [NeZero n] : Type :=
  (bad : Finset (TorusBond (n * R.params.side))) → (Yt : Finset (TorusSite (n * R.params.side))) →
    BaseChoice R.params.side n → TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ENNReal
private def weighted (H : CaseIntegrand R n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : ENNReal :=
  caseDensity bad Yt b p * H bad Yt b p
private def stateMass (H : CaseIntegrand R n) (x : TorusField n × CoarseState R n) : ENNReal :=
  ∑ bad : Finset (TorusBond (n * R.params.side)), ∑ Yt : Finset (TorusSite (n * R.params.side)),
    ∑ b : BaseChoice R.params.side n,
      configurationMassOf R (hotCoreSites R x.1) bad Yt b (fun W ωt => weighted H bad Yt b (x.1, W, ωt)) x.2
private theorem configurationMassOf_of_ne {C : Finset (TorusSite n)} {bad : Finset (TorusBond (n * R.params.side))}
    {Yt : Finset (TorusSite (n * R.params.side))} {b : BaseChoice R.params.side n}
    (G : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal) {q : CoarseState R n}
    (hq : q.1 ≠ coarseHull R.params.side R.range R.nextRange bad Yt C) : configurationMassOf R C bad Yt b G q = 0 := by
  classical
  unfold configurationMassOf
  refine Eq.trans (lintegral_congr (g := fun _ => 0) fun W => ?_) (by simp)
  refine Eq.trans (lintegral_congr (g := fun _ => 0) fun ν => if_neg fun h => hq ?_) (by simp)
  rw [← h.2]
  rfl
private theorem weighted_of_not_hull (H : CaseIntegrand R n) {bad : Finset (TorusBond (n * R.params.side))}
    {Yt : Finset (TorusSite (n * R.params.side))} {b : BaseChoice R.params.side n}
    {W : TorusField (n * R.params.side)} (hh : ¬ IsHullState R.params R.range W Yt) (V : TorusField n)
    (ωt : Yt → R.labels.Ω) : weighted H bad Yt b (V, W, ωt) = 0 := by
  classical
  unfold weighted caseDensity labelDensity
  simp only [if_neg hh, zero_mul]
private structure Hyps (R : StepSetup) (n : ℕ) [NeZero n] : Prop where
  withFunction : ConfigurationMassWithFunction
  massMeasurable : ConfigurationMassMeasurable
  density : StepTransitionDensityBounds
  weightMeasurable : ConfigurationWeightMeasurable
  wellPosed : R.IsWellPosed
  n₀_le : R.params.n₀ ≤ n
  markLaw_measurable : ∀ bad : Finset (TorusBond (n * R.params.side)),
    Measurable fun p : TorusField (n * R.params.side) × TorusField n => markLaw R p.1 p.2 bad
  hotCore_measurable : ∀ a : Finset (TorusSite n), MeasurableSet {V : TorusField n | hotCoreSites R V = a}
  labelShapes : CoarseLabelMeasureByShapes
  side_dvd : R.params.side ∣ n
variable {H : CaseIntegrand R n}
private theorem weighted_measurable (f : Hyps R n) (hH : ∀ bad Yt b, Measurable (H bad Yt b))
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    Measurable (weighted H bad Yt b) :=
  (caseDensity_measurable f.density f.wellPosed f.n₀_le f.markLaw_measurable bad Yt b).mul (hH bad Yt b)
private theorem stateMass_measurable (f : Hyps R n) (hH : ∀ bad Yt b, Measurable (H bad Yt b)) :
    Measurable (stateMass H) := by
  classical
  refine measurable_prod_sigma fun Y => ?_
  unfold stateMass
  refine Finset.measurable_sum _ fun bad _ => Finset.measurable_sum _ fun Yt _ =>
    Finset.measurable_sum _ fun b _ => ?_
  refine measurable_of_countable_fibres (X := TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side))
    (fun p => hotCoreSites R p.1) (fun a => measurable_fst (f.hotCore_measurable a))
    (fun C p => configurationMassOf R C bad Yt b (fun W ωt => weighted H bad Yt b (p.1, W, ωt)) ⟨Y, p.2⟩)
    fun C => ?_
  by_cases hY : Y = coarseHull R.params.side R.range R.nextRange bad Yt C
  · subst hY
    exact f.massMeasurable R n C bad Yt b (TorusField n) (fun V W ωt => weighted H bad Yt b (V, W, ωt))
      (weighted_measurable f hH bad Yt b) fun V W ωt hh => weighted_of_not_hull H hh V ωt
  · have e : (fun p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) =>
        configurationMassOf R C bad Yt b (fun W ωt => weighted H bad Yt b (p.1, W, ωt)) ⟨Y, p.2⟩) = fun _ => 0 :=
      funext fun p => configurationMassOf_of_ne _ hY
    rw [e]
    exact measurable_const
private theorem configurationMassOf_measurable (f : Hyps R n) (hH : ∀ bad Yt b, Measurable (H bad Yt b))
    (V : TorusField n) (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (Y : Finset (TorusSite n)) :
    Measurable fun ω : Y → CoarseLabel R.labels.Ω R.params.side =>
      configurationMassOf R C bad Yt b (fun W ωt => weighted H bad Yt b (V, W, ωt)) ⟨Y, ω⟩ := by
  classical
  by_cases hY : Y = coarseHull R.params.side R.range R.nextRange bad Yt C
  · subst hY
    have h := f.massMeasurable R n C bad Yt b (TorusField n) (fun V W ωt => weighted H bad Yt b (V, W, ωt))
      (weighted_measurable f hH bad Yt b) fun V W ωt hh => weighted_of_not_hull H hh V ωt
    have h0 : Measurable fun ω : coarseHull R.params.side R.range R.nextRange bad Yt C →
        CoarseLabel R.labels.Ω R.params.side =>
        ((V, ω) : TorusField n × (coarseHull R.params.side R.range R.nextRange bad Yt C →
          CoarseLabel R.labels.Ω R.params.side)) :=
      measurable_const.prodMk measurable_id
    have h1 := h.comp h0
    exact h1
  · have e : (fun ω : Y → CoarseLabel R.labels.Ω R.params.side =>
        configurationMassOf R C bad Yt b (fun W ωt => weighted H bad Yt b (V, W, ωt)) ⟨Y, ω⟩) = fun _ => 0 :=
      funext fun ω => configurationMassOf_of_ne _ hY
    rw [e]
    exact measurable_const
open Classical in
private theorem configurationMassOf_eq_with (f : Hyps R n) {V : TorusField n}
    {bad : Finset (TorusBond (n * R.params.side))}
    (hbad : bad ∈ (markedBonds R (hotCoreSites R V)).powerset) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (q : CoarseState R n) :
    configurationMassOf R (hotCoreSites R V) bad Yt b (fun W ωt => weighted H bad Yt b (V, W, ωt)) q =
      configurationMassWith R (hotCoreSites R V) V bad Yt b (fun W ωt => H bad Yt b (V, W, ωt)) q := by
  unfold configurationMassOf configurationMassWith
  refine lintegral_congr fun W => lintegral_congr fun ν => ?_
  by_cases h : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
      coarseStateOf R (hotCoreSites R V) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q
  · rw [if_pos h, if_pos h]
    beta_reduce
    unfold weighted
    rw [caseDensity_eq f.wellPosed f.n₀_le f.side_dvd hbad]
    unfold configurationWeight
    rw [if_pos h.1]
  · rw [if_neg h, if_neg h]
open Classical in
private theorem configurationMassOf_of_not_marked (f : Hyps R n) {V : TorusField n}
    {bad : Finset (TorusBond (n * R.params.side))}
    (hbad : bad ∉ (markedBonds R (hotCoreSites R V)).powerset) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (C : Finset (TorusSite n)) (q : CoarseState R n) :
    configurationMassOf R C bad Yt b (fun W ωt => weighted H bad Yt b (V, W, ωt)) q = 0 := by
  unfold configurationMassOf weighted
  simp only [caseDensity_of_not_marked f.wellPosed f.n₀_le f.side_dvd hbad, zero_mul, ite_self, lintegral_zero]
open Classical in
private theorem lintegral_weighted_eq_sum (f : Hyps R n) (hH : ∀ bad Yt b, Measurable (H bad Yt b))
    (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, weighted H bad Yt b (V, W, ωt) ∂(Measure.pi fun _ => R.labels.μ)
        ∂(fieldHaar (n * R.params.side)) =
      ∑ Y : Finset (TorusSite n), ∫⁻ ω, configurationMassOf R (hotCoreSites R V) bad Yt b
          (fun W ωt => weighted H bad Yt b (V, W, ωt)) ⟨Y, ω⟩
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) := by
  by_cases hbad : bad ∈ (markedBonds R (hotCoreSites R V)).powerset
  · have hg : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => H bad Yt b (V, p.1, p.2) :=
      (hH bad Yt b).comp (measurable_const.prodMk measurable_id)
    obtain ⟨z1, -, -, i⟩ := f.withFunction R f.wellPosed n f.n₀_le (hotCoreSites R V) V bad Yt b
      (fun W ωt => H bad Yt b (V, W, ωt)) hg
    rw [Finset.sum_eq_single_of_mem (coarseHull R.params.side R.range R.nextRange bad Yt (hotCoreSites R V))
      (Finset.mem_univ _) fun Y _ hY => by simp [configurationMassOf_of_ne _ (q := ⟨Y, _⟩) hY]]
    simp_rw [configurationMassOf_eq_with f hbad Yt b]
    rw [i]
    refine lintegral_congr fun W => lintegral_congr fun ωt => ?_
    unfold weighted
    rw [caseDensity_eq f.wellPosed f.n₀_le f.side_dvd hbad]
  · have h0 : ∀ (W : TorusField (n * R.params.side)) (ωt : Yt → R.labels.Ω),
        weighted H bad Yt b (V, W, ωt) = 0 := fun W ωt => by
      unfold weighted
      rw [caseDensity_of_not_marked f.wellPosed f.n₀_le f.side_dvd hbad, zero_mul]
    rw [Finset.sum_eq_zero fun Y _ => by
      rw [lintegral_congr fun ω => configurationMassOf_of_not_marked (H := H) f hbad Yt b (hotCoreSites R V) ⟨Y, ω⟩]
      simp]
    simp [h0]
private def outcomeIntegrand (H : CaseIntegrand R n) (q : StepCaseState R (n * R.params.side))
    (d : StepOutcome R.params n) : ENNReal :=
  H d.2.2 q.2.1 d.1 (d.2.1, q.1, q.2.2)
private theorem outcomeIntegrand_measurable (hH : ∀ bad Yt b, Measurable (H bad Yt b)) :
    Measurable fun x : StepCaseState R (n * R.params.side) × StepOutcome R.params n =>
      outcomeIntegrand H x.1 x.2 := by
  have hg : Measurable fun z : (TorusField (n * R.params.side) × StepOutcome R.params n) ×
      (Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω)) =>
      outcomeIntegrand H (z.1.1, z.2) z.1.2 := by
    refine measurable_prod_sigma fun Y => ?_
    have hf : Measurable fun z : (TorusField (n * R.params.side) × (Y → R.labels.Ω)) × StepOutcome R.params n =>
        H z.2.2.2 Y z.2.1 (z.2.2.1, z.1.1, z.1.2) :=
      measurable_of_outcome fun b bad => (hH bad Y b).comp
        (measurable_snd.prodMk ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst)))
    exact hf.comp (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst))
  exact hg.comp (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
    (measurable_snd.comp measurable_fst))
private theorem outcomeDensity_measurable (f : Hyps R n) :
    Measurable fun x : StepCaseState R (n * R.params.side) × StepOutcome R.params n =>
      stepOutcomeDensity R x.1.1 x.2 := by
  have h : Measurable fun p : TorusField (n * R.params.side) × StepOutcome R.params n =>
      stepOutcomeDensity R p.1 p.2 := by
    refine measurable_of_outcome (ℓ := R.params) (X := TorusField (n * R.params.side))
      (f := fun p => stepOutcomeDensity R p.1 p.2) fun b bad => ?_
    exact ((f.density R.params R.coupling n).1 b).mul (f.markLaw_measurable bad)
  have h0 : Measurable fun x : StepCaseState R (n * R.params.side) × StepOutcome R.params n =>
      ((x.1.1, x.2) : TorusField (n * R.params.side) × StepOutcome R.params n) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have h1 := h.comp h0
  exact h1
private def outcomeMean (H : CaseIntegrand R n) (q : StepCaseState R (n * R.params.side)) : ENNReal :=
  ∫⁻ d, outcomeIntegrand H q d * ENNReal.ofReal (stepOutcomeDensity R q.1 d) ∂(stepReferenceMeasure R.params n)
private theorem outcomeMean_measurable (f : Hyps R n) (hH : ∀ bad Yt b, Measurable (H bad Yt b)) :
    Measurable (outcomeMean H) :=
  Measurable.lintegral_prod_right' (ν := stepReferenceMeasure R.params n)
    ((outcomeIntegrand_measurable hH).mul (outcomeDensity_measurable f).ennreal_ofReal)
private theorem lintegral_stepJointLaw (f : Hyps R n) (hH : ∀ bad Yt b, Measurable (H bad Yt b)) {A : Type}
    [MeasurableSpace A] (μ : Measure A) [SFinite μ] {st : A → StepCaseState R (n * R.params.side)}
    (hst : Measurable st) :
    ∫⁻ u, outcomeIntegrand H (st u.1) u.2 ∂(stepJointLaw R n μ st) = ∫⁻ a, outcomeMean H (st a) ∂μ := by
  unfold stepJointLaw
  have h0 : Measurable fun u : A × StepOutcome R.params n =>
      ((st u.1, u.2) : StepCaseState R (n * R.params.side) × StepOutcome R.params n) :=
    (hst.comp measurable_fst).prodMk measurable_snd
  have m1 : Measurable fun u : A × StepOutcome R.params n => ENNReal.ofReal (stepOutcomeDensity R (st u.1).1 u.2) :=
    ((outcomeDensity_measurable f).comp h0).ennreal_ofReal
  have m2 : Measurable fun u : A × StepOutcome R.params n => outcomeIntegrand H (st u.1) u.2 :=
    (outcomeIntegrand_measurable hH).comp h0
  rw [lintegral_withDensity_eq_lintegral_mul _ m1 m2]
  have e : ((fun u : A × StepOutcome R.params n => ENNReal.ofReal (stepOutcomeDensity R (st u.1).1 u.2)) *
      fun u => outcomeIntegrand H (st u.1) u.2) =
      fun u => outcomeIntegrand H (st u.1) u.2 * ENNReal.ofReal (stepOutcomeDensity R (st u.1).1 u.2) := by
    funext u
    exact mul_comm _ _
  have m3 : Measurable fun u : A × StepOutcome R.params n =>
      outcomeIntegrand H (st u.1) u.2 * ENNReal.ofReal (stepOutcomeDensity R (st u.1).1 u.2) :=
    m2.mul m1
  rw [e, lintegral_prod _ m3.aemeasurable]
  rfl
private theorem outcomeMean_eq (f : Hyps R n) (hH : ∀ bad Yt b, Measurable (H bad Yt b))
    (q : StepCaseState R (n * R.params.side)) :
    outcomeMean H q = ∑ b : BaseChoice R.params.side n, ∫⁻ V, ∑ bad : Finset (TorusBond (n * R.params.side)),
      H bad q.2.1 b (V, q.1, q.2.2) *
        ENNReal.ofReal (stepTransitionDensity R.params R.coupling q.1 b V * markLaw R q.1 V bad)
        ∂(fieldHaar n) := by
  unfold outcomeMean
  have hm : Measurable fun d : StepOutcome R.params n =>
      outcomeIntegrand H q d * ENNReal.ofReal (stepOutcomeDensity R q.1 d) :=
    ((outcomeIntegrand_measurable hH).mul (outcomeDensity_measurable f).ennreal_ofReal).comp
      (measurable_const.prodMk measurable_id)
  rw [lintegral_stepReference hm]
  rfl
private theorem outcomeMean_mul_labelWeight (f : Hyps R n) (hH : ∀ bad Yt b, Measurable (H bad Yt b))
    {W : TorusField (n * R.params.side)} {Y : Finset (TorusSite (n * R.params.side))} (ω : Y → R.labels.Ω)
    (hh : IsHullState R.params R.range W Y) :
    outcomeMean H (W, ⟨Y, ω⟩) * ENNReal.ofReal (R.labelWeight (n * R.params.side) W Y ω) =
      ∑ b : BaseChoice R.params.side n, ∫⁻ V, ∑ bad : Finset (TorusBond (n * R.params.side)),
        weighted H bad Y b (V, W, ω) ∂(fieldHaar n) := by
  classical
  rw [outcomeMean_eq f hH, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun V => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun bad _ => ?_
  unfold weighted caseDensity labelDensity
  simp only [if_pos hh]
  ring
private theorem lintegral_swap_three {Yt : Finset (TorusSite (n * R.params.side))}
    {K : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ENNReal} (hK : Measurable K) :
    ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, ∫⁻ V, K (V, W, ωt) ∂(fieldHaar n) ∂(Measure.pi fun _ => R.labels.μ)
        ∂(fieldHaar (n * R.params.side)) =
      ∫⁻ V, ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, K (V, W, ωt) ∂(Measure.pi fun _ => R.labels.μ)
        ∂(fieldHaar (n * R.params.side)) ∂(fieldHaar n) := by
  have s1 : ∀ W : TorusField (n * R.params.side),
      ∫⁻ ωt : Yt → R.labels.Ω, ∫⁻ V, K (V, W, ωt) ∂(fieldHaar n) ∂(Measure.pi fun _ => R.labels.μ) =
      ∫⁻ V, ∫⁻ ωt : Yt → R.labels.Ω, K (V, W, ωt) ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar n) := fun W =>
    lintegral_lintegral_swap (hK.comp (measurable_snd.prodMk (measurable_const.prodMk measurable_fst))).aemeasurable
  simp_rw [s1]
  have h2 : Measurable fun p : TorusField (n * R.params.side) × TorusField n =>
      ∫⁻ ωt : Yt → R.labels.Ω, K (p.2, p.1, ωt) ∂(Measure.pi fun _ => R.labels.μ) :=
    Measurable.lintegral_prod_right' (ν := Measure.pi fun _ : Yt => R.labels.μ)
      (hK.comp ((measurable_snd.comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  exact lintegral_lintegral_swap h2.aemeasurable
private theorem sum_stateMass_eq (f : Hyps R n) (hH : ∀ bad Yt b, Measurable (H bad Yt b)) (V : TorusField n) :
    ∑ Y : Finset (TorusSite n), ∫⁻ ω, stateMass H (V, ⟨Y, ω⟩)
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
        ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω,
        ∑ bad : Finset (TorusBond (n * R.params.side)), weighted H bad Yt b (V, W, ωt)
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  classical
  have e1 : ∀ Y : Finset (TorusSite n), ∫⁻ ω, stateMass H (V, ⟨Y, ω⟩)
      ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ∑ bad : Finset (TorusBond (n * R.params.side)), ∑ Yt : Finset (TorusSite (n * R.params.side)),
        ∑ b : BaseChoice R.params.side n,
        ∫⁻ ω, configurationMassOf R (hotCoreSites R V) bad Yt b (fun W ωt => weighted H bad Yt b (V, W, ωt)) ⟨Y, ω⟩
          ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) := by
    intro Y
    show ∫⁻ ω, ∑ bad : Finset (TorusBond (n * R.params.side)), ∑ Yt : Finset (TorusSite (n * R.params.side)),
      ∑ b : BaseChoice R.params.side n,
      configurationMassOf R (hotCoreSites R V) bad Yt b (fun W ωt => weighted H bad Yt b (V, W, ωt)) ⟨Y, ω⟩
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) = _
    rw [lintegral_finsetSum _ fun bad _ => Finset.measurable_sum _ fun Yt _ => Finset.measurable_sum _ fun b _ =>
      configurationMassOf_measurable f hH V _ bad Yt b Y]
    refine Finset.sum_congr rfl fun bad _ => ?_
    rw [lintegral_finsetSum _ fun Yt _ => Finset.measurable_sum _ fun b _ =>
      configurationMassOf_measurable f hH V _ bad Yt b Y]
    refine Finset.sum_congr rfl fun Yt _ => ?_
    rw [lintegral_finsetSum _ fun b _ => configurationMassOf_measurable f hH V _ bad Yt b Y]
  have e2 : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω,
      ∑ bad : Finset (TorusBond (n * R.params.side)), weighted H bad Yt b (V, W, ωt)
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∑ bad : Finset (TorusBond (n * R.params.side)), ∑ Y : Finset (TorusSite n),
        ∫⁻ ω, configurationMassOf R (hotCoreSites R V) bad Yt b (fun W ωt => weighted H bad Yt b (V, W, ωt)) ⟨Y, ω⟩
          ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) := by
    intro Yt b
    have hm : ∀ bad, Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        weighted H bad Yt b (V, p.1, p.2) := fun bad => by
      have h0 : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
          ((V, p.1, p.2) : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω)) :=
        measurable_const.prodMk measurable_id
      have h1 := (weighted_measurable f hH bad Yt b).comp h0
      exact h1
    have hm1 : ∀ (W : TorusField (n * R.params.side)) bad, Measurable fun ωt : Yt → R.labels.Ω =>
        weighted H bad Yt b (V, W, ωt) := fun W bad => by
      have h0 : Measurable fun ωt : Yt → R.labels.Ω =>
          ((W, ωt) : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) :=
        measurable_const.prodMk measurable_id
      have h1 := (hm bad).comp h0
      exact h1
    have hm2 : ∀ bad, Measurable fun W : TorusField (n * R.params.side) =>
        ∫⁻ ωt : Yt → R.labels.Ω, weighted H bad Yt b (V, W, ωt) ∂(Measure.pi fun _ => R.labels.μ) := fun bad =>
      Measurable.lintegral_prod_right' (ν := Measure.pi fun _ : Yt => R.labels.μ) (hm bad)
    simp_rw [lintegral_finsetSum _ fun bad _ => hm1 _ bad]
    rw [lintegral_finsetSum _ fun bad _ => hm2 bad]
    exact Finset.sum_congr rfl fun bad _ => lintegral_weighted_eq_sum f hH V bad Yt b
  simp_rw [e1, e2]
  rw [Finset.sum_comm]
  have e3 : ∀ bad : Finset (TorusBond (n * R.params.side)), ∑ Y : Finset (TorusSite n),
      ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
        ∫⁻ ω, configurationMassOf R (hotCoreSites R V) bad Yt b (fun W ωt => weighted H bad Yt b (V, W, ωt)) ⟨Y, ω⟩
          ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n, ∑ Y : Finset (TorusSite n),
        ∫⁻ ω, configurationMassOf R (hotCoreSites R V) bad Yt b (fun W ωt => weighted H bad Yt b (V, W, ωt)) ⟨Y, ω⟩
          ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) := by
    intro bad
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun Yt _ => Finset.sum_comm
  simp_rw [e3]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Yt _ => ?_
  exact Finset.sum_comm
end Mass
section Law
variable {R : StepSetup} {n : ℕ} [NeZero n] {H : CaseIntegrand R n}
private theorem lintegral_hull_eq (f : Hyps R n) (hH : ∀ bad Yt b, Measurable (H bad Yt b)) :
    ∫⁻ W, (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.range W),
      ∫⁻ ω, outcomeMean H (W, ⟨Y, ω⟩) * ENNReal.ofReal (R.labelWeight (n * R.params.side) W Y ω)
        ∂(Measure.pi fun _ : Y => R.labels.μ))
      ∂(fieldHaar (n * R.params.side)) =
    ∫⁻ V, ∑ Y : Finset (TorusSite n), ∫⁻ ω, stateMass H (V, ⟨Y, ω⟩)
      ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) ∂(fieldHaar n) := by
  classical
  have hS : ∀ (Y : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Y → R.labels.Ω) =>
        ∑ bad : Finset (TorusBond (n * R.params.side)), weighted H bad Y b p :=
    fun Y b => Finset.measurable_sum _ fun bad _ => weighted_measurable f hH bad Y b
  have hB : ∀ (Y : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
      Measurable fun x : TorusField (n * R.params.side) × (Y → R.labels.Ω) =>
        ∫⁻ V, ∑ bad : Finset (TorusBond (n * R.params.side)), weighted H bad Y b (V, x.1, x.2) ∂(fieldHaar n) :=
    fun Y b => by
    have h0 : Measurable fun z : (TorusField (n * R.params.side) × (Y → R.labels.Ω)) × TorusField n =>
        ((z.2, z.1.1, z.1.2) : TorusField n × TorusField (n * R.params.side) × (Y → R.labels.Ω)) :=
      measurable_snd.prodMk ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))
    have h1 := (hS Y b).comp h0
    exact Measurable.lintegral_prod_right' (ν := fieldHaar n) h1
  have hB1 : ∀ (Y : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
      (W : TorusField (n * R.params.side)),
      Measurable fun ω : Y → R.labels.Ω =>
        ∫⁻ V, ∑ bad : Finset (TorusBond (n * R.params.side)), weighted H bad Y b (V, W, ω) ∂(fieldHaar n) :=
    fun Y b W => by
    have h0 : Measurable fun ω : Y → R.labels.Ω => ((W, ω) : TorusField (n * R.params.side) × (Y → R.labels.Ω)) :=
      measurable_const.prodMk measurable_id
    have h1 := (hB Y b).comp h0
    exact h1
  have hW : ∀ (Y : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
      Measurable fun W : TorusField (n * R.params.side) => ∫⁻ ω : Y → R.labels.Ω,
        ∫⁻ V, ∑ bad : Finset (TorusBond (n * R.params.side)), weighted H bad Y b (V, W, ω) ∂(fieldHaar n)
          ∂(Measure.pi fun _ => R.labels.μ) := fun Y b =>
    Measurable.lintegral_prod_right' (ν := Measure.pi fun _ : Y => R.labels.μ) (hB Y b)
  have hV : ∀ (Y : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
      Measurable fun V : TorusField n => ∫⁻ W, ∫⁻ ω : Y → R.labels.Ω,
        ∑ bad : Finset (TorusBond (n * R.params.side)), weighted H bad Y b (V, W, ω)
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := fun Y b => by
    have h0 : Measurable fun z : (TorusField n × TorusField (n * R.params.side)) × (Y → R.labels.Ω) =>
        ((z.1.1, z.1.2, z.2) : TorusField n × TorusField (n * R.params.side) × (Y → R.labels.Ω)) :=
      (measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have h1 := (hS Y b).comp h0
    have h2 := Measurable.lintegral_prod_right' (ν := Measure.pi fun _ : Y => R.labels.μ) h1
    exact Measurable.lintegral_prod_right' (ν := fieldHaar (n * R.params.side)) h2
  have e1 : ∀ W : TorusField (n * R.params.side), (∑ Y ∈ Finset.univ.filter (IsHullState R.params R.range W),
      ∫⁻ ω, outcomeMean H (W, ⟨Y, ω⟩) * ENNReal.ofReal (R.labelWeight (n * R.params.side) W Y ω)
        ∂(Measure.pi fun _ : Y => R.labels.μ)) =
      ∑ Y : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n, ∫⁻ ω : Y → R.labels.Ω,
        ∫⁻ V, ∑ bad : Finset (TorusBond (n * R.params.side)), weighted H bad Y b (V, W, ω) ∂(fieldHaar n)
          ∂(Measure.pi fun _ => R.labels.μ) := by
    intro W
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [← lintegral_finsetSum _ fun b _ => hB1 Y b W]
    by_cases hh : IsHullState R.params R.range W Y
    · rw [if_pos hh]
      exact lintegral_congr fun ω => outcomeMean_mul_labelWeight f hH ω hh
    · rw [if_neg hh]
      symm
      have hz : ∀ (ω : Y → R.labels.Ω), ∑ b : BaseChoice R.params.side n,
          ∫⁻ V, ∑ bad : Finset (TorusBond (n * R.params.side)), weighted H bad Y b (V, W, ω) ∂(fieldHaar n) = 0 :=
        fun ω => by
        simp [weighted_of_not_hull H hh]
      simp [hz]
  rw [lintegral_congr e1, lintegral_finsetSum _ fun Y _ => Finset.measurable_sum _ fun b _ => hW Y b,
    lintegral_congr (sum_stateMass_eq f hH),
    lintegral_finsetSum _ fun Y _ => Finset.measurable_sum _ fun b _ => hV Y b]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [lintegral_finsetSum _ fun b _ => hW Y b, lintegral_finsetSum _ fun b _ => hV Y b]
  exact Finset.sum_congr rfl fun b _ => lintegral_swap_three (hS Y b)
private theorem mul_lintegral_eq (f : Hyps R n) (hH : ∀ bad Yt b, Measurable (H bad Yt b)) {A : Type}
    [MeasurableSpace A] (μ : Measure A) [SFinite μ] {st : A → StepCaseState R (n * R.params.side)}
    (hst : Measurable st) {Z : ENNReal} (hD : HasStateDensity R n Z μ st) :
    Z * ∫⁻ u, outcomeIntegrand H (st u.1) u.2 ∂(stepJointLaw R n μ st) =
      ∫⁻ V, ∑ Y : Finset (TorusSite n), ∫⁻ ω, stateMass H (V, ⟨Y, ω⟩)
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) ∂(fieldHaar n) := by
  rw [lintegral_stepJointLaw f hH μ hst, hD _ (outcomeMean_measurable f hH)]
  exact lintegral_hull_eq f hH
variable (R n) in
private def imageMeasure : Measure (TorusField n × CoarseState R n) :=
  (fieldHaar n).prod (Measure.sum fun Y : Finset (TorusSite n) =>
    (Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side).map (Sigma.mk Y))
private theorem lintegral_imageMeasure (f : Hyps R n) {g : TorusField n × CoarseState R n → ENNReal}
    (hg : Measurable g) :
    ∫⁻ x, g x ∂(imageMeasure R n) =
      ∫⁻ V, ∑ Y : Finset (TorusSite n), ∫⁻ ω, g (V, ⟨Y, ω⟩)
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) ∂(fieldHaar n) := by
  classical
  have : SigmaFinite (coarseLabelMeasure R.labels.μ R.params.side) :=
    (f.labelShapes R.labels.Ω R.labels.μ R.params.side).1
  unfold imageMeasure
  rw [lintegral_prod _ hg.aemeasurable]
  refine lintegral_congr fun V => ?_
  rw [lintegral_sum_measure, tsum_fintype]
  refine Finset.sum_congr rfl fun Y _ => ?_
  have h0 : Measurable fun q : CoarseState R n => ((V, q) : TorusField n × CoarseState R n) :=
    measurable_const.prodMk measurable_id
  have h1 := hg.comp h0
  exact lintegral_map h1 (measurable_sigmaMk Y)
private theorem blockConfigAt_measurable (C Z : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (y : TorusSite n) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => blockConfigAt R C Z p.1 Yt p.2 bad b y := by
  classical
  refine measurable_comap_iff.2 ?_
  refine measurable_const.prodMk (measurable_const.prodMk
    ((measurable_pi_lambda _ fun o => ?_).prodMk (measurable_const.prodMk (measurable_pi_lambda _ fun c => ?_))))
  · show Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      (blockConfigAt R C Z p.1 Yt p.2 bad b y).siteLabel o
    unfold blockConfigAt
    by_cases h : blockSite y o ∈ Yt
    · simp only [dif_pos h]
      exact measurable_inr.comp ((measurable_pi_apply _).comp measurable_snd)
    · simp only [dif_neg h]
      exact measurable_const
  · show Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      (blockConfigAt R C Z p.1 Yt p.2 bad b y).linkValue c
    unfold blockConfigAt
    by_cases h : parentBlock R.params.side
        (blockSite (L := R.params.side) y c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈ Z
    · simp only [if_pos h]
      exact measurable_inr.comp measurable_fst.eval.eval
    · simp only [if_neg h]
      exact measurable_const
private theorem coarseStateOf_measurable (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => coarseStateOf R C p.1 Yt p.2 bad b := by
  classical
  unfold coarseStateOf
  refine (measurable_sigmaMk (β := fun Y : Finset (TorusSite n) => Y → CoarseLabel R.labels.Ω R.params.side)
    (coarseHull R.params.side R.range R.nextRange bad Yt C)).comp (measurable_pi_lambda _ fun y => ?_)
  by_cases hy : (y : TorusSite n) ∈ storedBlocks R.params.side R.range bad Yt C
  · simp only [if_pos hy]
    exact measurable_inr.comp (blockConfigAt_measurable _ _ _ _ _ _)
  · simp only [if_neg hy]
    exact measurable_const
private theorem image_measurable_fixed (f : Hyps R n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      ((p.1, coarseStateOf R (hotCoreSites R p.1) p.2.1 Yt p.2.2 bad b) : TorusField n × CoarseState R n) := by
  refine measurable_fst.prodMk ?_
  refine measurable_of_countable_fibres (X := TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω))
    (fun p => hotCoreSites R p.1) (fun a => measurable_fst (f.hotCore_measurable a))
    (fun C p => coarseStateOf R C p.2.1 Yt p.2.2 bad b) fun C => ?_
  have h0 : Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) => p.2 :=
    measurable_snd
  have h1 := (coarseStateOf_measurable C bad Yt b).comp h0
  exact h1
private theorem stepImage_measurable (f : Hyps R n) :
    Measurable fun x : StepCaseState R (n * R.params.side) × StepOutcome R.params n => stepImage R x.1 x.2 := by
  have hg : Measurable fun z : (TorusField (n * R.params.side) × StepOutcome R.params n) ×
      (Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω)) =>
      stepImage R (z.1.1, z.2) z.1.2 := by
    refine measurable_prod_sigma fun Y => ?_
    have hf : Measurable fun z : (TorusField (n * R.params.side) × (Y → R.labels.Ω)) × StepOutcome R.params n =>
        stepImage R (z.1.1, ⟨Y, z.1.2⟩) z.2 := by
      refine measurable_of_outcome fun b bad => ?_
      have h0 : Measurable fun p : (TorusField (n * R.params.side) × (Y → R.labels.Ω)) × TorusField n =>
          ((p.2, p.1.1, p.1.2) : TorusField n × TorusField (n * R.params.side) × (Y → R.labels.Ω)) :=
        measurable_snd.prodMk ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))
      have h1 := (image_measurable_fixed f bad Y b).comp h0
      exact h1
    have h0 : Measurable fun p : (TorusField (n * R.params.side) × StepOutcome R.params n) × (Y → R.labels.Ω) =>
        (((p.1.1, p.2), p.1.2) : (TorusField (n * R.params.side) × (Y → R.labels.Ω)) × StepOutcome R.params n) :=
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk (measurable_snd.comp measurable_fst)
    have h1 := hf.comp h0
    exact h1
  have h0 : Measurable fun x : StepCaseState R (n * R.params.side) × StepOutcome R.params n =>
      (((x.1.1, x.2), x.1.2) : (TorusField (n * R.params.side) × StepOutcome R.params n) ×
        (Σ Y : Finset (TorusSite (n * R.params.side)), (Y → R.labels.Ω))) :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk (measurable_snd.comp measurable_fst)
  have h1 := hg.comp h0
  exact h1
private def withImage (ψ : TorusField n × CoarseState R n → ENNReal) (H : CaseIntegrand R n) : CaseIntegrand R n :=
  fun bad Yt b p => ψ (p.1, coarseStateOf R (hotCoreSites R p.1) p.2.1 Yt p.2.2 bad b) * H bad Yt b p
private theorem withImage_measurable (f : Hyps R n) {ψ : TorusField n × CoarseState R n → ENNReal}
    (hψ : Measurable ψ) (hH : ∀ bad Yt b, Measurable (H bad Yt b)) :
    ∀ bad Yt b, Measurable (withImage ψ H bad Yt b) := fun bad Yt b => by
  have h1 := hψ.comp (image_measurable_fixed f bad Yt b)
  exact h1.mul (hH bad Yt b)
open Classical in
private theorem stateMass_withImage {ψ : TorusField n × CoarseState R n → ENNReal} (hψ : ∀ x, ψ x ≠ ⊤)
    (x : TorusField n × CoarseState R n) :
    stateMass (withImage ψ H) x = ψ x * stateMass H x := by
  unfold stateMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun bad _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun Yt _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold configurationMassOf
  rw [← lintegral_const_mul' _ _ (hψ x)]
  refine lintegral_congr fun W => ?_
  rw [← lintegral_const_mul' _ _ (hψ x)]
  refine lintegral_congr fun ν => ?_
  by_cases h : IsHullState R.params R.range (x.2.fieldWithStoredLinks W) Yt ∧
      coarseStateOf R (hotCoreSites R x.1) (x.2.fieldWithStoredLinks W) Yt (x.2.fillLabels Yt ν) bad b = x.2
  · rw [if_pos h, if_pos h]
    unfold weighted withImage
    beta_reduce
    rw [h.2]
    have e : ((x.1, x.2) : TorusField n × CoarseState R n) = x := rfl
    rw [e]
    ring
  · rw [if_neg h, if_neg h, mul_zero]
private theorem mul_lintegral_image_eq (f : Hyps R n) (hH : ∀ bad Yt b, Measurable (H bad Yt b)) {A : Type}
    [MeasurableSpace A] (μ : Measure A) [SFinite μ] {st : A → StepCaseState R (n * R.params.side)}
    (hst : Measurable st) {Z : ENNReal} (hD : HasStateDensity R n Z μ st)
    {ψ : TorusField n × CoarseState R n → ENNReal} (hψ : Measurable ψ) (hψt : ∀ x, ψ x ≠ ⊤) :
    Z * ∫⁻ u, ψ (stepImage R (st u.1) u.2) * outcomeIntegrand H (st u.1) u.2 ∂(stepJointLaw R n μ st) =
      ∫⁻ x, ψ x * stateMass H x ∂(imageMeasure R n) := by
  have h1 := mul_lintegral_eq f (withImage_measurable f hψ hH) μ hst hD
  have e : ∀ u : A × StepOutcome R.params n, outcomeIntegrand (withImage ψ H) (st u.1) u.2 =
      ψ (stepImage R (st u.1) u.2) * outcomeIntegrand H (st u.1) u.2 :=
    fun u => rfl
  simp_rw [e, stateMass_withImage hψt] at h1
  have hm : Measurable fun x => ψ x * stateMass H x := hψ.mul (stateMass_measurable f hH)
  rw [h1]
  exact (lintegral_imageMeasure f hm).symm
end Law
section Means
variable {R : StepSetup} {n : ℕ} [NeZero n] {H : CaseIntegrand R n}
private def unitIntegrand : CaseIntegrand R n := fun _ _ _ _ => 1
private theorem unitIntegrand_measurable : ∀ bad Yt b, Measurable (unitIntegrand (R := R) (n := n) bad Yt b) :=
  fun _ _ _ => measurable_const
open Classical in
private theorem stateMass_le {c : ENNReal} (hc : c ≠ ⊤) (h : ∀ bad Yt b p, H bad Yt b p ≤ c)
    (x : TorusField n × CoarseState R n) :
    stateMass H x ≤ c * stateMass unitIntegrand x := by
  unfold stateMass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun bad _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun Yt _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  unfold configurationMassOf
  rw [← lintegral_const_mul' _ _ hc]
  refine lintegral_mono fun W => ?_
  rw [← lintegral_const_mul' _ _ hc]
  refine lintegral_mono fun ν => ?_
  by_cases ht : IsHullState R.params R.range (x.2.fieldWithStoredLinks W) Yt ∧
      coarseStateOf R (hotCoreSites R x.1) (x.2.fieldWithStoredLinks W) Yt (x.2.fillLabels Yt ν) bad b = x.2
  · rw [if_pos ht, if_pos ht]
    unfold weighted unitIntegrand
    calc _ ≤ caseDensity bad Yt b (x.1, x.2.fieldWithStoredLinks W, x.2.fillLabels Yt ν) * c :=
          mul_le_mul' le_rfl (h _ _ _ _)
      _ = _ := by ring
  · rw [if_neg ht, if_neg ht, mul_zero]
private def massRatio (H : CaseIntegrand R n) (x : TorusField n × CoarseState R n) : ENNReal :=
  stateMass H x / stateMass unitIntegrand x
private theorem massRatio_measurable (f : Hyps R n) (hH : ∀ bad Yt b, Measurable (H bad Yt b)) :
    Measurable (massRatio H) :=
  (stateMass_measurable f hH).div (stateMass_measurable f unitIntegrand_measurable)
private theorem massRatio_le {c : ENNReal} (hc : c ≠ ⊤) (h : ∀ bad Yt b p, H bad Yt b p ≤ c)
    (x : TorusField n × CoarseState R n) : massRatio H x ≤ c :=
  ENNReal.div_le_of_le_mul (stateMass_le hc h x)
private theorem stateMass_eq_massRatio_mul {c : ENNReal} (hc : c ≠ ⊤) (h : ∀ bad Yt b p, H bad Yt b p ≤ c)
    {x : TorusField n × CoarseState R n} (hx : stateMass unitIntegrand x ≠ ⊤) :
    stateMass H x = massRatio H x * stateMass unitIntegrand x := by
  by_cases h0 : stateMass unitIntegrand x = 0
  · have h1 := stateMass_le hc h x
    rw [h0, mul_zero] at h1
    rw [h0, mul_zero]
    exact le_antisymm h1 zero_le
  · exact (ENNReal.div_mul_cancel h0 hx).symm
section Outcome
variable {A : Type} [MeasurableSpace A] (μ : Measure A) [SFinite μ] {st : A → StepCaseState R (n * R.params.side)}
  {Z : ENNReal}
private theorem stepImage_outcome_measurable (f : Hyps R n) (hst : Measurable st) :
    Measurable fun u : A × StepOutcome R.params n => stepImage R (st u.1) u.2 := by
  have h0 : Measurable fun u : A × StepOutcome R.params n =>
      ((st u.1, u.2) : StepCaseState R (n * R.params.side) × StepOutcome R.params n) :=
    (hst.comp measurable_fst).prodMk measurable_snd
  have h1 := (stepImage_measurable f).comp h0
  exact h1
private theorem lintegral_stateMass_unit_ne_top (f : Hyps R n) (hst : Measurable st) (hZt : Z ≠ ⊤)
    (hD : HasStateDensity R n Z μ st) [IsFiniteMeasure (stepJointLaw R n μ st)] :
    ∫⁻ x, stateMass unitIntegrand x ∂(imageMeasure R n) ≠ ⊤ := by
  have h := mul_lintegral_image_eq f unitIntegrand_measurable μ hst hD (ψ := fun _ => 1) measurable_const
    fun _ => ENNReal.one_ne_top
  simp only [one_mul] at h
  rw [← h]
  have e : ∀ u : A × StepOutcome R.params n, outcomeIntegrand (unitIntegrand (R := R) (n := n)) (st u.1) u.2 = 1 :=
    fun u => rfl
  simp only [e, lintegral_one]
  exact ENNReal.mul_ne_top hZt (measure_ne_top _ _)
private theorem ae_stateMass_unit_ne_top (f : Hyps R n) (hst : Measurable st) (hZt : Z ≠ ⊤)
    (hD : HasStateDensity R n Z μ st) [IsFiniteMeasure (stepJointLaw R n μ st)] :
    ∀ᵐ x ∂(imageMeasure R n), stateMass unitIntegrand x ≠ ⊤ := by
  filter_upwards [ae_lt_top (stateMass_measurable f unitIntegrand_measurable)
    (lintegral_stateMass_unit_ne_top μ f hst hZt hD)] with x hx
  exact hx.ne
private theorem setLIntegral_preimage_eq {α : Type} [MeasurableSpace α] {ν : Measure α}
    {t : α → TorusField n × CoarseState R n} (ht : Measurable t) {S : Set (TorusField n × CoarseState R n)}
    (hS : MeasurableSet S) (g : α → ENNReal) :
    ∫⁻ u in t ⁻¹' S, g u ∂ν = ∫⁻ u, S.indicator (fun _ => 1) (t u) * g u ∂ν := by
  rw [← lintegral_indicator (ht hS)]
  refine lintegral_congr fun u => ?_
  by_cases h : t u ∈ S
  · rw [Set.indicator_of_mem (show u ∈ t ⁻¹' S from h), Set.indicator_of_mem h, one_mul]
  · rw [Set.indicator_of_notMem (show u ∉ t ⁻¹' S from h), Set.indicator_of_notMem h, zero_mul]
private theorem setLIntegral_eq_massRatio (f : Hyps R n) (hH : ∀ bad Yt b, Measurable (H bad Yt b)) {c : ENNReal}
    (hc : c ≠ ⊤) (hle : ∀ bad Yt b p, H bad Yt b p ≤ c) (hst : Measurable st) (hZ0 : Z ≠ 0) (hZt : Z ≠ ⊤)
    (hD : HasStateDensity R n Z μ st) [IsFiniteMeasure (stepJointLaw R n μ st)]
    {S : Set (TorusField n × CoarseState R n)} (hS : MeasurableSet S) :
    ∫⁻ u in (fun u : A × StepOutcome R.params n => stepImage R (st u.1) u.2) ⁻¹' S,
        outcomeIntegrand H (st u.1) u.2 ∂(stepJointLaw R n μ st) =
      ∫⁻ u in (fun u : A × StepOutcome R.params n => stepImage R (st u.1) u.2) ⁻¹' S,
        massRatio H (stepImage R (st u.1) u.2) ∂(stepJointLaw R n μ st) := by
  have ht := stepImage_outcome_measurable (A := A) (st := st) f hst
  rw [setLIntegral_preimage_eq ht hS, setLIntegral_preimage_eq ht hS]
  refine (ENNReal.mul_right_inj hZ0 hZt).1 ?_
  have hψ : Measurable (S.indicator fun _ => (1 : ENNReal)) := measurable_const.indicator hS
  have hψt : ∀ x, S.indicator (fun _ => (1 : ENNReal)) x ≠ ⊤ := fun x => by
    by_cases h : x ∈ S
    · rw [Set.indicator_of_mem h]
      exact ENNReal.one_ne_top
    · rw [Set.indicator_of_notMem h]
      exact ENNReal.zero_ne_top
  have hψ' : Measurable fun x => S.indicator (fun _ => (1 : ENNReal)) x * massRatio H x :=
    hψ.mul (massRatio_measurable f hH)
  have hψ't : ∀ x, S.indicator (fun _ => (1 : ENNReal)) x * massRatio H x ≠ ⊤ := fun x =>
    ENNReal.mul_ne_top (hψt x) (ne_top_of_le_ne_top hc (massRatio_le hc hle x))
  have h1 := mul_lintegral_image_eq f hH μ hst hD hψ hψt
  have h2 := mul_lintegral_image_eq f unitIntegrand_measurable μ hst hD hψ' hψ't
  have e : ∀ u : A × StepOutcome R.params n, outcomeIntegrand (unitIntegrand (R := R) (n := n)) (st u.1) u.2 = 1 :=
    fun u => rfl
  simp only [e, mul_one] at h2
  rw [h1, h2]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_stateMass_unit_ne_top μ f hst hZt hD] with x hx
  rw [stateMass_eq_massRatio_mul hc hle hx, mul_assoc]
private theorem ae_stateMass_unit_image_ne_top (f : Hyps R n) (hst : Measurable st) (hZ0 : Z ≠ 0) (hZt : Z ≠ ⊤)
    (hD : HasStateDensity R n Z μ st) [IsFiniteMeasure (stepJointLaw R n μ st)] :
    ∀ᵐ u ∂(stepJointLaw R n μ st), stateMass unitIntegrand (stepImage R (st u.1) u.2) ≠ ⊤ := by
  have hB : MeasurableSet {x : TorusField n × CoarseState R n | stateMass unitIntegrand x = ⊤} :=
    stateMass_measurable f unitIntegrand_measurable (measurableSet_singleton ⊤)
  have ht := stepImage_outcome_measurable (A := A) (st := st) f hst
  have hψ : Measurable ({x : TorusField n × CoarseState R n | stateMass unitIntegrand x = ⊤}.indicator
      fun _ => (1 : ENNReal)) :=
    measurable_const.indicator hB
  have hψt : ∀ x, {x : TorusField n × CoarseState R n | stateMass unitIntegrand x = ⊤}.indicator
      (fun _ => (1 : ENNReal)) x ≠ ⊤ := fun x => by
    by_cases h : x ∈ {x : TorusField n × CoarseState R n | stateMass unitIntegrand x = ⊤}
    · rw [Set.indicator_of_mem h]
      exact ENNReal.one_ne_top
    · rw [Set.indicator_of_notMem h]
      exact ENNReal.zero_ne_top
  have h1 := mul_lintegral_image_eq f unitIntegrand_measurable μ hst hD hψ hψt
  have h2 : ∫⁻ x, {x : TorusField n × CoarseState R n | stateMass unitIntegrand x = ⊤}.indicator
      (fun _ => (1 : ENNReal)) x * stateMass unitIntegrand x ∂(imageMeasure R n) = 0 := by
    refine Eq.trans (lintegral_congr_ae (g := fun _ => 0) ?_) (by simp)
    filter_upwards [ae_stateMass_unit_ne_top μ f hst hZt hD] with x hx
    rw [Set.indicator_of_notMem
      (show x ∉ {x : TorusField n × CoarseState R n | stateMass unitIntegrand x = ⊤} from hx), zero_mul]
  rw [h2, ← setLIntegral_preimage_eq ht hB] at h1
  have h3 : ∫⁻ u in (fun u : A × StepOutcome R.params n => stepImage R (st u.1) u.2) ⁻¹'
      {x : TorusField n × CoarseState R n | stateMass unitIntegrand x = ⊤},
        outcomeIntegrand (unitIntegrand (R := R) (n := n)) (st u.1) u.2 ∂(stepJointLaw R n μ st) = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hZ0
    · exact h
  have e : ∀ u : A × StepOutcome R.params n, outcomeIntegrand (unitIntegrand (R := R) (n := n)) (st u.1) u.2 = 1 :=
    fun u => rfl
  simp only [e, lintegral_one, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at h3
  exact measure_eq_zero_iff_ae_notMem.mp h3
end Outcome
end Means
section Terms
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem markProduct_nonneg (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (bad : Finset (TorusBond (n * R.params.side))) :
    0 ≤ markProduct R C V W bad := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.markProduct_nonneg <;> assumption
private theorem measurable_fieldWithStoredLinks (q : CoarseState R n) : Measurable q.fieldWithStoredLinks := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fieldWithStoredLinks <;> assumption
private theorem measurable_fillLabels (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable (q.fillLabels Yt) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fillLabels <;> assumption
private theorem coarseStateOf_eq_of_eq (q : CoarseState R n) (C : Finset (TorusSite n))
    (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) {W W' : TorusField (n * R.params.side)} {ν ν' : q.unlabelled Yt → R.labels.Ω}
    (h : coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) :
    coarseStateOf R C (q.fieldWithStoredLinks W') Yt (q.fillLabels Yt ν') bad b = q := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.coarseStateOf_fill <;> assumption
variable {C : Finset (TorusSite n)} {V : TorusField n} {bad : Finset (TorusBond (n * R.params.side))}
  {Yt : Finset (TorusSite (n * R.params.side))} {b : BaseChoice R.params.side n}
private def weightedValue (C : Finset (TorusSite n)) (V : TorusField n) (G : CaseFunction R n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : ℝ :=
  (configurationWeight R C V bad Yt b p.1 p.2).toReal * G p.1 Yt p.2 bad b
private theorem configurationWeight_ne_top (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) :
    configurationWeight R C V bad Yt b W ω ≠ ⊤ := by apply _root_.YangMills.SharedProofs.p21773 <;> assumption
private theorem configurationWeight_mul_pos (G : CaseFunction R n) (W : TorusField (n * R.params.side))
    (ω : Yt → R.labels.Ω) :
    configurationWeight R C V bad Yt b W ω * ENNReal.ofReal (G W Yt ω bad b) =
      ENNReal.ofReal (weightedValue C V G bad Yt b (W, ω)) := by
  unfold weightedValue
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (configurationWeight_ne_top _ _)]
private theorem configurationWeight_mul_neg (G : CaseFunction R n) (W : TorusField (n * R.params.side))
    (ω : Yt → R.labels.Ω) :
    configurationWeight R C V bad Yt b W ω * ENNReal.ofReal (-G W Yt ω bad b) =
      ENNReal.ofReal (-weightedValue C V G bad Yt b (W, ω)) := by
  unfold weightedValue
  rw [← mul_neg, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (configurationWeight_ne_top _ _)]
private theorem stepWeight_nonneg (f : Hyps R n) {W : TorusField (n * R.params.side)} (ω : Yt → R.labels.Ω)
    (hh : IsHullState R.params R.range W Yt) :
    0 ≤ stepWeight R C V W Yt ω bad b := by
  rw [stepWeight_eq_mul]
  obtain ⟨Cd, hC⟩ := (f.density R.params R.coupling n).2
  exact mul_nonneg (labelWeight_nonneg f.wellPosed f.n₀_le ω hh)
    (mul_nonneg (hC W b V).1 (markProduct_nonneg f.wellPosed C V W bad))
open Classical in
private theorem caseTerm_eq_weightedValue (f : Hyps R n) (G : CaseFunction R n) (q : CoarseState R n)
    {W : TorusField (n * R.params.side)} {ν : q.unlabelled Yt → R.labels.Ω}
    (hq : coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) :
    caseTerm R C V q G bad Yt b W ν = weightedValue C V G bad Yt b (q.fieldWithStoredLinks W, q.fillLabels Yt ν) := by
  unfold caseTerm weightedValue configurationWeight
  by_cases hh : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt
  · simp only [if_pos hh]
    rw [if_pos ⟨hh, hq⟩, ENNReal.toReal_ofReal (stepWeight_nonneg f _ hh), mul_comm]
  · simp only [if_neg hh]
    rw [if_neg fun x => hh x.1]
    simp
private theorem integral_caseTerm_eq (f : Hyps R n) {G : CaseFunction R n}
    (hG : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => G p.1 Yt p.2 bad b)
    (q : CoarseState R n)
    (hp : configurationMassWith R C V bad Yt b (fun W ω => ENNReal.ofReal (G W Yt ω bad b)) q ≠ ⊤)
    (hm : configurationMassWith R C V bad Yt b (fun W ω => ENNReal.ofReal (-G W Yt ω bad b)) q ≠ ⊤) :
    ∫ W, ∫ ν, caseTerm R C V q G bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      (configurationMassWith R C V bad Yt b (fun W ω => ENNReal.ofReal (G W Yt ω bad b)) q).toReal -
        (configurationMassWith R C V bad Yt b (fun W ω => ENNReal.ofReal (-G W Yt ω bad b)) q).toReal := by
  classical
  by_cases hS : ∃ (W₀ : TorusField (n * R.params.side)) (ν₀ : q.unlabelled Yt → R.labels.Ω),
      coarseStateOf R C (q.fieldWithStoredLinks W₀) Yt (q.fillLabels Yt ν₀) bad b = q
  · obtain ⟨W₀, ν₀, h0⟩ := hS
    have hq : ∀ (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω),
        coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q := fun W ν =>
      coarseStateOf_eq_of_eq q C Yt bad b h0
    have hprod : Measurable (weightedValue C V G bad Yt b) :=
      (f.weightMeasurable R f.wellPosed n f.n₀_le C V bad Yt b).ennreal_toReal.mul hG
    set v : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) → ℝ :=
      fun p => weightedValue C V G bad Yt b (q.fieldWithStoredLinks p.1, q.fillLabels Yt p.2) with hv
    have hvm : Measurable v := hprod.comp
      (((measurable_fieldWithStoredLinks q).comp measurable_fst).prodMk
        ((measurable_fillLabels q Yt).comp measurable_snd))
    have e1 : configurationMassWith R C V bad Yt b (fun W ω => ENNReal.ofReal (G W Yt ω bad b)) q =
        ∫⁻ p, ENNReal.ofReal (v p)
          ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : q.unlabelled Yt => R.labels.μ)) := by
      rw [lintegral_prod _ hvm.ennreal_ofReal.aemeasurable]
      unfold configurationMassWith
      refine lintegral_congr fun W => lintegral_congr fun ν => ?_
      rw [hv]
      beta_reduce
      rw [← configurationWeight_mul_pos]
      unfold configurationWeight
      by_cases hh : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt
      · rw [if_pos ⟨hh, hq W ν⟩, if_pos hh]
      · rw [if_neg fun x => hh x.1, if_neg hh, zero_mul]
    have e2 : configurationMassWith R C V bad Yt b (fun W ω => ENNReal.ofReal (-G W Yt ω bad b)) q =
        ∫⁻ p, ENNReal.ofReal (-v p)
          ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : q.unlabelled Yt => R.labels.μ)) := by
      have hneg : Measurable fun p => ENNReal.ofReal (-v p) := hvm.neg.ennreal_ofReal
      rw [lintegral_prod (fun p => ENNReal.ofReal (-v p)) hneg.aemeasurable]
      unfold configurationMassWith
      refine lintegral_congr fun W => lintegral_congr fun ν => ?_
      rw [hv]
      beta_reduce
      rw [← configurationWeight_mul_neg]
      unfold configurationWeight
      by_cases hh : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt
      · rw [if_pos ⟨hh, hq W ν⟩, if_pos hh]
      · rw [if_neg fun x => hh x.1, if_neg hh, zero_mul]
    have hi : Integrable v ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : q.unlabelled Yt => R.labels.μ)) :=
      integrable_of_posNeg_lintegral hvm (e1 ▸ hp) (e2 ▸ hm)
    have e3 : ∫ W, ∫ ν, caseTerm R C V q G bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ)
        ∂(fieldHaar (n * R.params.side)) =
        ∫ p, v p ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : q.unlabelled Yt => R.labels.μ)) := by
      rw [integral_prod _ hi]
      refine integral_congr_ae (ae_of_all _ fun W => integral_congr_ae (ae_of_all _ fun ν => ?_))
      exact caseTerm_eq_weightedValue f G q (hq W ν)
    rw [e3, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi, e1, e2]
  · push Not at hS
    have h0 : ∀ (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω),
        caseTerm R C V q G bad Yt b W ν = 0 := fun W ν => by
      unfold caseTerm
      rw [if_neg fun x => hS W ν x.2]
    have z : ∀ g : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal,
        configurationMassWith R C V bad Yt b g q = 0 := fun g => by
      unfold configurationMassWith
      refine Eq.trans (lintegral_congr (g := fun _ => 0) fun W => ?_) (by simp)
      exact Eq.trans (lintegral_congr (g := fun _ => 0) fun ν => if_neg fun x => hS W ν x.2) (by simp)
    simp [h0, z]
end Terms
section Final
variable {R : StepSetup} {n : ℕ} [NeZero n]
private def posIntegrand (F : TorusField n → CaseFunction R n) : CaseIntegrand R n :=
  fun bad Yt b p => ENNReal.ofReal (F p.1 p.2.1 Yt p.2.2 bad b)
private def negIntegrand (F : TorusField n → CaseFunction R n) : CaseIntegrand R n :=
  fun bad Yt b p => ENNReal.ofReal (-F p.1 p.2.1 Yt p.2.2 bad b)
private theorem stateMass_eq_sum_marked (f : Hyps R n) (H : CaseIntegrand R n) (x : TorusField n × CoarseState R n) :
    stateMass H x = ∑ bad ∈ (markedBonds R (hotCoreSites R x.1)).powerset,
      ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
        configurationMassWith R (hotCoreSites R x.1) x.1 bad Yt b (fun W ωt => H bad Yt b (x.1, W, ωt)) x.2 := by
  classical
  unfold stateMass
  rw [← Finset.sum_subset (Finset.subset_univ (markedBonds R (hotCoreSites R x.1)).powerset) fun bad _ hbad =>
    Finset.sum_eq_zero fun Yt _ => Finset.sum_eq_zero fun b _ => configurationMassOf_of_not_marked f hbad Yt b _ _]
  refine Finset.sum_congr rfl fun bad hbad => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ => ?_
  exact configurationMassOf_eq_with f hbad Yt b x.2
private theorem stateMass_unit_eq (f : Hyps R n) (x : TorusField n × CoarseState R n) :
    stateMass unitIntegrand x = coarseStateMass R (hotCoreSites R x.1) x.1 x.2 := by
  classical
  rw [stateMass_eq_sum_marked f]
  unfold coarseStateMass configurationMassWith unitIntegrand
  simp only [mul_one]
private theorem massRatio_sub_eq_caseMean (f : Hyps R n) {F : TorusField n → CaseFunction R n} {B : ℝ}
    (hF : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        F p.1 p.2.1 Yt p.2.2 bad b)
    (hB : ∀ V W Yt ωt bad b, |F V W Yt ωt bad b| ≤ B) {x : TorusField n × CoarseState R n}
    (hx : stateMass unitIntegrand x ≠ ⊤) :
    (massRatio (posIntegrand F) x).toReal - (massRatio (negIntegrand F) x).toReal =
      caseMean R (hotCoreSites R x.1) x.1 x.2 (F x.1) := by
  classical
  have hcp : ∀ bad Yt b p, posIntegrand F bad Yt b p ≤ ENNReal.ofReal B := fun bad Yt b p =>
    ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) (hB _ _ _ _ _ _))
  have hcm : ∀ bad Yt b p, negIntegrand F bad Yt b p ≤ ENNReal.ofReal B := fun bad Yt b p =>
    ENNReal.ofReal_le_ofReal (le_trans (neg_le_abs _) (hB _ _ _ _ _ _))
  have hP : stateMass (posIntegrand F) x ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx)
    (stateMass_le ENNReal.ofReal_ne_top hcp x)
  have hM : stateMass (negIntegrand F) x ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx)
    (stateMass_le ENNReal.ofReal_ne_top hcm x)
  have hP' := hP
  have hM' := hM
  rw [stateMass_eq_sum_marked f] at hP' hM'
  have hfp := ENNReal.sum_ne_top.1 hP'
  have hfm := ENNReal.sum_ne_top.1 hM'
  have eP := stateMass_eq_sum_marked f (posIntegrand F) x
  have eM := stateMass_eq_sum_marked f (negIntegrand F) x
  have hI : caseIntegral R (hotCoreSites R x.1) x.1 x.2 (F x.1) =
      (stateMass (posIntegrand F) x).toReal - (stateMass (negIntegrand F) x).toReal := by
    rw [eP, eM, ENNReal.toReal_sum hfp, ENNReal.toReal_sum hfm, ← Finset.sum_sub_distrib]
    unfold caseIntegral
    refine Finset.sum_congr rfl fun bad hbad => ?_
    have h1 := ENNReal.sum_ne_top.1 (hfp bad hbad)
    have h2 := ENNReal.sum_ne_top.1 (hfm bad hbad)
    rw [ENNReal.toReal_sum h1, ENNReal.toReal_sum h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun Yt hYt => ?_
    have h3 := ENNReal.sum_ne_top.1 (h1 Yt hYt)
    have h4 := ENNReal.sum_ne_top.1 (h2 Yt hYt)
    rw [ENNReal.toReal_sum h3, ENNReal.toReal_sum h4, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hG : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => F x.1 p.1 Yt p.2 bad b := by
      have h0 : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
          ((x.1, p.1, p.2) : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω)) :=
        measurable_const.prodMk measurable_id
      have h5 := (hF Yt bad b).comp h0
      exact h5
    exact integral_caseTerm_eq f hG x.2 (h3 b hb) (h4 b hb)
  unfold caseMean coarseStateWeight massRatio
  rw [hI, stateMass_unit_eq f, ENNReal.toReal_div, ENNReal.toReal_div, sub_div]
private theorem caseValueAt_eq_sub (F : TorusField n → CaseFunction R n) (q : StepCaseState R (n * R.params.side))
    (d : StepOutcome R.params n) :
    caseValueAt F q d = (outcomeIntegrand (posIntegrand F) q d).toReal -
      (outcomeIntegrand (negIntegrand F) q d).toReal := by
  unfold caseValueAt outcomeIntegrand posIntegrand negIntegrand
  rcases le_total 0 (F d.2.1 q.1 q.2.1 q.2.2 d.2.2 d.1) with h | h
  · rw [ENNReal.toReal_ofReal h, ENNReal.ofReal_of_nonpos (by linarith)]
    simp
  · rw [ENNReal.ofReal_of_nonpos h, ENNReal.toReal_ofReal (by linarith)]
    simp
private theorem integral_toReal_sub {α : Type} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {a a' : α → ENNReal} (ha : Measurable a) (ha' : Measurable a') {c : ENNReal} (hc : c ≠ ⊤)
    (h1 : ∀ x, a x ≤ c) (h2 : ∀ x, a' x ≤ c) :
    ∫ x, ((a x).toReal - (a' x).toReal) ∂ν = (∫⁻ x, a x ∂ν).toReal - (∫⁻ x, a' x ∂ν).toReal := by
  have hb : ∀ {g : α → ENNReal}, (∀ x, g x ≤ c) → ∫⁻ x, g x ∂ν ≠ ⊤ := fun {g} hg =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hc (measure_ne_top ν Set.univ))
      ((lintegral_mono hg).trans (by simp))
  have i1 := integrable_toReal_of_lintegral_ne_top ha.aemeasurable (hb h1)
  have i2 := integrable_toReal_of_lintegral_ne_top ha'.aemeasurable (hb h2)
  rw [integral_sub i1 i2,
    integral_toReal ha.aemeasurable (ae_of_all _ fun x => lt_of_le_of_lt (h1 x) (lt_top_iff_ne_top.mpr hc)),
    integral_toReal ha'.aemeasurable (ae_of_all _ fun x => lt_of_le_of_lt (h2 x) (lt_top_iff_ne_top.mpr hc))]
end Final
end ConditionalMean
open ConditionalMean in
theorem conditionalMeanGivenCoarseState_holds (hc : ConfigurationMassWithFunction)
    (hp : ConfigurationMassMeasurable) (hs' : StepTransitionDensityBounds)
    (hw : ConfigurationWeightMeasurable) (hl : CoarseLabelMeasureByShapes) :
    conditionalMeanGivenCoarseState := by
  classical
  intro R hR n _ hn hd hcoin hhull A _ μ _ st hst Z hZ0 hZt hD hfin F B hF hB
  have f : Hyps R n := ⟨hc, hp, hs', hw, hR, hn, hcoin, hhull, hl, hd⟩
  set img : A × StepOutcome R.params n → TorusField n × CoarseState R n := fun u => stepImage R (st u.1) u.2
    with himg
  have htm : Measurable img := stepImage_outcome_measurable f hst
  have hHp : ∀ bad Yt b, Measurable (posIntegrand F bad Yt b) := fun bad Yt b => (hF Yt bad b).ennreal_ofReal
  have hHm : ∀ bad Yt b, Measurable (negIntegrand F bad Yt b) := fun bad Yt b => (hF Yt bad b).neg.ennreal_ofReal
  have hcp : ∀ bad Yt b p, posIntegrand F bad Yt b p ≤ ENNReal.ofReal B := fun bad Yt b p =>
    ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) (hB _ _ _ _ _ _))
  have hcm : ∀ bad Yt b p, negIntegrand F bad Yt b p ≤ ENNReal.ofReal B := fun bad Yt b p =>
    ENNReal.ofReal_le_ofReal (le_trans (neg_le_abs _) (hB _ _ _ _ _ _))
  have hcB : ENNReal.ofReal B ≠ ⊤ := ENNReal.ofReal_ne_top
  have h0 : Measurable fun u : A × StepOutcome R.params n =>
      ((st u.1, u.2) : StepCaseState R (n * R.params.side) × StepOutcome R.params n) :=
    (hst.comp measurable_fst).prodMk measurable_snd
  have hsp : Measurable fun u : A × StepOutcome R.params n => outcomeIntegrand (posIntegrand F) (st u.1) u.2 := by
    have h1 := (outcomeIntegrand_measurable hHp).comp h0
    exact h1
  have hsm : Measurable fun u : A × StepOutcome R.params n => outcomeIntegrand (negIntegrand F) (st u.1) u.2 := by
    have h1 := (outcomeIntegrand_measurable hHm).comp h0
    exact h1
  have hrp : Measurable fun u => massRatio (posIntegrand F) (img u) := (massRatio_measurable f hHp).comp htm
  have hrm : Measurable fun u => massRatio (negIntegrand F) (img u) := (massRatio_measurable f hHm).comp htm
  have eΦ : (fun u : A × StepOutcome R.params n => caseValueAt F (st u.1) u.2) =
      fun u => (outcomeIntegrand (posIntegrand F) (st u.1) u.2).toReal -
        (outcomeIntegrand (negIntegrand F) (st u.1) u.2).toReal :=
    funext fun u => caseValueAt_eq_sub F _ _
  have hΦm : Measurable fun u : A × StepOutcome R.params n => caseValueAt F (st u.1) u.2 := by
    rw [eΦ]
    exact hsp.ennreal_toReal.sub hsm.ennreal_toReal
  have hΦi : Integrable (fun u : A × StepOutcome R.params n => caseValueAt F (st u.1) u.2) (stepJointLaw R n μ st) :=
    Integrable.of_bound hΦm.aestronglyMeasurable B (ae_of_all _ fun u => hB _ _ _ _ _ _)
  set g : TorusField n × CoarseState R n → ℝ :=
    fun x => (massRatio (posIntegrand F) x).toReal - (massRatio (negIntegrand F) x).toReal with hg
  have hgm : Measurable g :=
    (massRatio_measurable f hHp).ennreal_toReal.sub (massRatio_measurable f hHm).ennreal_toReal
  have hgb : ∀ x, ‖g x‖ ≤ 2 * (ENNReal.ofReal B).toReal := fun x => by
    have h1 := ENNReal.toReal_mono hcB (massRatio_le hcB hcp x)
    have h2 := ENNReal.toReal_mono hcB (massRatio_le hcB hcm x)
    have h3 : (0 : ℝ) ≤ (massRatio (posIntegrand F) x).toReal := ENNReal.toReal_nonneg
    have h4 : (0 : ℝ) ≤ (massRatio (negIntegrand F) x).toReal := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> simp only [hg] <;> linarith
  have hgi : Integrable (g ∘ img) (stepJointLaw R n μ st) :=
    Integrable.of_bound (hgm.comp htm).aestronglyMeasurable _ (ae_of_all _ fun u => hgb _)
  have hle : MeasurableSpace.comap img inferInstance ≤
      (inferInstance : MeasurableSpace (A × StepOutcome R.params n)) :=
    htm.comap_le
  have hmain : (g ∘ img) =ᵐ[stepJointLaw R n μ st] (stepJointLaw R n μ st)[fun u => caseValueAt F (st u.1) u.2 |
      MeasurableSpace.comap img inferInstance] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hle hΦi (fun s _ _ => hgi.integrableOn) ?_ ?_
    · rintro _ ⟨S, hS, rfl⟩ -
      have s1 := setLIntegral_eq_massRatio μ f hHp hcB hcp hst hZ0 hZt hD hS
      have s2 := setLIntegral_eq_massRatio μ f hHm hcB hcm hst hZ0 hZt hD hS
      have e1 := integral_toReal_sub (ν := (stepJointLaw R n μ st).restrict (img ⁻¹' S)) hrp hrm hcB
        (fun u => massRatio_le hcB hcp _) (fun u => massRatio_le hcB hcm _)
      have e2 := integral_toReal_sub (ν := (stepJointLaw R n μ st).restrict (img ⁻¹' S)) hsp hsm hcB
        (fun u => hcp _ _ _ _) (fun u => hcm _ _ _ _)
      show ∫ u in img ⁻¹' S, g (img u) ∂(stepJointLaw R n μ st) = _
      simp only [hg]
      rw [e1, eΦ, e2, s1, s2]
    · exact ((hgm.comp (comap_measurable img)).stronglyMeasurable).aestronglyMeasurable
  filter_upwards [hmain, ae_stateMass_unit_image_ne_top μ f hst hZ0 hZt hD] with u h1 h2
  rw [← h1]
  exact massRatio_sub_eq_caseMean f hF hB h2
end YangMills.Construction.WeightedResponses
end
