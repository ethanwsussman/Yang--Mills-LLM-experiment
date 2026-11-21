import YangMills.Construction.ResponseInTheExpansion.MassAlongTheLevelsProof
import YangMills.Construction.ResponseInTheExpansion.NumbersOfAScoredTowerAreTheChain
import YangMills.Construction.SixteenPointsOnASmallTorus.CentringIsTheSumOfTheShiftsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open ClusterExpansionOfAStep TorusFields TorusLumps StepSettings StepGas RenormalizationStepParameters StepCosts StepReturn StepFloors WeightedResponses
  FreeEnergies LevelTestFunctions
namespace ScoredTowerChainProof
section Marks
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem markProduct_nonneg (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (bad : Finset (TorusBond (n * R.params.side))) :
    0 ≤ markProduct R C V W bad := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.markProduct_nonneg <;> assumption
private theorem markProduct_le_one (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (bad : Finset (TorusBond (n * R.params.side))) :
    markProduct R C V W bad ≤ 1 := by apply _root_.YangMills.SharedProofs.p3258 <;> assumption
private theorem sum_markProduct (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side)) :
    ∑ bad ∈ (markedBonds R C).powerset, markProduct R C V W bad = 1 := by apply _root_.YangMills.SharedProofs.p20431 <;> assumption
private theorem stepWeight_eq_mul (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    stepWeight R C V W Yt ωt bad b =
      R.labelWeight (n * R.params.side) W Yt ωt * stepTransitionDensity R.params R.coupling W b V *
        markProduct R C V W bad := by apply _root_.YangMills.SharedProofs.p15525 <;> assumption
end Marks
section States
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem measurable_fieldWithStoredLinks (q : CoarseState R n) : Measurable q.fieldWithStoredLinks := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fieldWithStoredLinks <;> assumption
private theorem measurable_fillLabels (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable (q.fillLabels Yt) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fillLabels <;> assumption
private theorem coarseStateOf_indep (q : CoarseState R n) (C : Finset (TorusSite n))
    (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) {W W' : TorusField (n * R.params.side)} {ν ν' : q.unlabelled Yt → R.labels.Ω}
    (h : coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) :
    coarseStateOf R C (q.fieldWithStoredLinks W') Yt (q.fillLabels Yt ν') bad b = q := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.coarseStateOf_fill <;> assumption
end States
private structure Inputs : Prop where
  massWith : ConfigurationMassWithFunction
  support : ConfigurationSupportedOnCoarseHull
  measurable : ConfigurationWeightMeasurable
  weightsSum : ConfigurationWeightsSum
  coarseHull : CoarseHullIsHullState
  coldState : coldFieldStateStatement
  scoredMass : ScoredMassStatement
  scoreBounds : BondScoreProperties
  transitionBounds : StepTransitionDensityBounds
private structure LevelInputs (R : StepSetup) (A : ResponseSetup R) : Prop where
  inputs : Inputs
  wellPosed : R.IsWellPosed
  response : A.IsAdmissible
private theorem integrable_of_lintegral_pos_neg_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Measurable f) (hp : ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≠ ⊤) (hm : ∫⁻ a, ENNReal.ofReal (-f a) ∂μ ≠ ⊤) :
    Integrable f μ := by apply _root_.YangMills.SharedProofs.p18814 <;> assumption
section Majorant
variable {R : StepSetup} (A : ResponseSetup R)
open Classical in
private def scoredDensity (m : ℕ) [NeZero m] (Yt : Finset (TorusSite m)) (p : TorusField m × (Yt → R.labels.Ω)) : ℝ :=
  (if IsHullState R.params (clusterRange R.coupling) p.1 Yt then R.labelWeight m p.1 Yt p.2 else 0) *
    Real.exp (∑ y : Yt, A.score (p.2 y))
variable {A} {m : ℕ} [NeZero m]
private theorem scoredDensity_measurable (h : LevelInputs R A) (hb : IsBlockTorusSide R.params m)
    (Yt : Finset (TorusSite m)) : Measurable (scoredDensity A m Yt) := by
  classical
  refine Measurable.mul (h.wellPosed.hasExpansions.2.borel m hb Yt).1 ?_
  exact (Finset.measurable_sum _ fun y _ => h.response.price.borel.comp
    ((measurable_pi_apply y).comp measurable_snd)).exp
private theorem scoredDensity_nonneg (h : LevelInputs R A) (hb : IsBlockTorusSide R.params m) (Yt : Finset (TorusSite m))
    (p : TorusField m × (Yt → R.labels.Ω)) : 0 ≤ scoredDensity A m Yt p := by
  classical
  unfold scoredDensity
  refine mul_nonneg ?_ (Real.exp_pos _).le
  split_ifs with hh
  · exact h.wellPosed.hasExpansions.2.nonneg m hb p.1 Yt p.2 hh
  · exact le_rfl
private def scoredMassBound (R : StepSetup) (m : ℕ) [NeZero m] : ℝ :=
  R.functional m (trivialField m) * 2 ^ Fintype.card (TorusSite m) *
    Real.exp (2 * R.params.E * Fintype.card (TorusSite m))
private theorem lintegral_scoredDensity_le (h : LevelInputs R A) (hb : IsBlockTorusSide R.params m)
    (Yt : Finset (TorusSite m)) (W : TorusField m) :
    ∫⁻ ω, ENNReal.ofReal (scoredDensity A m Yt (W, ω)) ∂(Measure.pi fun _ : Yt => R.labels.μ) ≤
      ENNReal.ofReal (scoredMassBound R m) := by
  classical
  by_cases hh : IsHullState R.params (clusterRange R.coupling) W Yt
  · have hs := h.inputs.scoredMass R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
      R.clusterFactor R.siteDensity A.score h.wellPosed.admissible h.wellPosed.admissible.E_ge h.wellPosed.coupling_pos
      h.wellPosed.range_ge_base h.wellPosed.hasExpansions.1 h.wellPosed.hasExpansions.2 h.response.price m hb W
    refine le_trans (le_of_eq ?_) (le_trans (Finset.single_le_sum (f := fun Y : Finset (TorusSite m) =>
      ∫⁻ ω, ENNReal.ofReal (R.labelWeight m W Y ω * Real.exp (∑ y : Y, A.score (ω y)))
        ∂(Measure.pi fun _ : Y => R.labels.μ))
      (fun _ _ => zero_le) (Finset.mem_filter.mpr ⟨Finset.mem_univ Yt, hh⟩)) hs)
    refine lintegral_congr fun ω => ?_
    simp only [scoredDensity, if_pos hh]
  · have : ∀ ω, scoredDensity A m Yt (W, ω) = 0 := fun ω => by simp [scoredDensity, hh]
    simp [this]
private theorem scoredDensity_integrable (h : LevelInputs R A) (hb : IsBlockTorusSide R.params m)
    (Yt : Finset (TorusSite m)) :
    Integrable (scoredDensity A m Yt) ((fieldHaar m).prod (Measure.pi fun _ : Yt => R.labels.μ)) := by
  have hm := scoredDensity_measurable h hb Yt
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (scoredDensity_nonneg h hb Yt))]
  rw [lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
  calc _ ≤ ∫⁻ _ : TorusField m, ENNReal.ofReal (scoredMassBound R m) ∂(fieldHaar m) :=
        lintegral_mono fun W => lintegral_scoredDensity_le h hb Yt W
    _ = ENNReal.ofReal (scoredMassBound R m) := by simp
    _ < ⊤ := ENNReal.ofReal_lt_top
private theorem scoredDensity_integrable_section (h : LevelInputs R A) (hb : IsBlockTorusSide R.params m)
    (Yt : Finset (TorusSite m)) (W : TorusField m) :
    Integrable (fun ω => scoredDensity A m Yt (W, ω)) (Measure.pi fun _ : Yt => R.labels.μ) := by
  have hm : Measurable fun ω => scoredDensity A m Yt (W, ω) :=
    (scoredDensity_measurable h hb Yt).comp measurable_prodMk_left
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => scoredDensity_nonneg h hb Yt _)]
  exact lt_of_le_of_lt (lintegral_scoredDensity_le h hb Yt W) ENNReal.ofReal_lt_top
end Majorant
section Cases
variable {R : StepSetup} (A : ResponseSetup R) {n : ℕ} [NeZero n]
open Classical in
private def liveRestriction (H : CaseFunction R n) (Yt : Finset (TorusSite (n * R.params.side)))
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : ℝ :=
  if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then H p.1 Yt p.2 bad b else 0
private structure IsTame (H : CaseFunction R n) : Prop where
  measurable_live : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n), Measurable (liveRestriction H Yt bad b)
  bound : ∃ M : ℝ, ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
    (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
    IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
    |H W Yt ωt bad b| ≤ M * Real.exp (∑ y : Yt, A.score (ωt y))
variable (C : Finset (TorusSite n)) (V : TorusField n)
private def weightedCase (H : CaseFunction R n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : ℝ :=
  (configurationWeight R C V bad Yt b p.1 p.2).toReal * liveRestriction H Yt bad b p
private def posPart (H : CaseFunction R n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) : ENNReal :=
  ENNReal.ofReal (liveRestriction H Yt bad b (W, ω))
private def negPart (H : CaseFunction R n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) : ENNReal :=
  ENNReal.ofReal (-liveRestriction H Yt bad b (W, ω))
variable {A C V} {H : CaseFunction R n} {bad : Finset (TorusBond (n * R.params.side))}
  {Yt : Finset (TorusSite (n * R.params.side))} {b : BaseChoice R.params.side n}
private theorem configurationWeight_ne_top (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) :
    configurationWeight R C V bad Yt b W ω ≠ ⊤ := by apply _root_.YangMills.SharedProofs.p21773 <;> assumption
private theorem configurationWeight_mul_posPart (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) :
    configurationWeight R C V bad Yt b W ω * posPart H bad Yt b W ω =
      ENNReal.ofReal (weightedCase C V H bad Yt b (W, ω)) := by
  unfold weightedCase posPart
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (configurationWeight_ne_top W ω)]
private theorem configurationWeight_mul_negPart (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) :
    configurationWeight R C V bad Yt b W ω * negPart H bad Yt b W ω =
      ENNReal.ofReal (-weightedCase C V H bad Yt b (W, ω)) := by
  unfold weightedCase negPart
  rw [← mul_neg, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (configurationWeight_ne_top W ω)]
private theorem transitionDensity_bounded (h : LevelInputs R A) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) (V : TorusField n),
      0 ≤ stepTransitionDensity R.params R.coupling W b V ∧ stepTransitionDensity R.params R.coupling W b V ≤ Cd := by
  obtain ⟨Cd, hC⟩ := (h.inputs.transitionBounds R.params R.coupling n).2
  exact ⟨|Cd|, abs_nonneg _, fun W b V => ⟨(hC W b V).1, (hC W b V).2.trans (le_abs_self _)⟩⟩
private theorem isBlockTorusSide_mul (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) :
    IsBlockTorusSide R.params (n * R.params.side) :=
  ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
private theorem stepWeight_nonneg (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (W : TorusField (n * R.params.side))
    (ω : Yt → R.labels.Ω) (hh : IsHullState R.params R.range W Yt) : 0 ≤ stepWeight R C V W Yt ω bad b := by
  obtain ⟨Cd, -, hC⟩ := transitionDensity_bounded (n := n) h
  rw [stepWeight_eq_mul]
  exact mul_nonneg (mul_nonneg (h.wellPosed.hasExpansions.2.nonneg _ (isBlockTorusSide_mul h hn) W Yt ω hh)
    (hC W b V).1) (markProduct_nonneg h.wellPosed C V W bad)
private theorem stepWeight_eq_zero_of_not_live (h : LevelInputs R A) (hn : R.params.n₀ ≤ n)
    (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) (hh : IsHullState R.params R.range W Yt)
    (hl : ¬ IsLiveState R.params R.coupling R.labelWeight W Yt ω) : stepWeight R C V W Yt ω bad b = 0 := by
  have h0 : R.labelWeight (n * R.params.side) W Yt ω = 0 :=
    le_antisymm (not_lt.mp fun hp => hl ⟨hh, hp⟩)
      (h.wellPosed.hasExpansions.2.nonneg _ (isBlockTorusSide_mul h hn) W Yt ω hh)
  rw [stepWeight_eq_mul, h0, zero_mul, zero_mul]
private theorem weightedCase_measurable (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (hT : IsTame A H) :
    Measurable (weightedCase C V H bad Yt b) :=
  ((h.inputs.measurable R h.wellPosed n hn C V bad Yt b).ennreal_toReal).mul (hT.measurable_live Yt bad b)
private theorem weightedCase_abs_le (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (hT : IsTame A H) :
    ∃ B : ℝ, ∀ p, |weightedCase C V H bad Yt b p| ≤ B * scoredDensity A (n * R.params.side) Yt p := by
  classical
  obtain ⟨M, hM⟩ := hT.bound
  obtain ⟨Cd, hCd, hC⟩ := transitionDensity_bounded (n := n) h
  have hb := isBlockTorusSide_mul h hn
  refine ⟨Cd * |M|, fun p => ?_⟩
  have hs := scoredDensity_nonneg h hb Yt p
  have hB : 0 ≤ Cd * |M| * scoredDensity A (n * R.params.side) Yt p := mul_nonneg (mul_nonneg hCd (abs_nonneg _)) hs
  unfold weightedCase liveRestriction configurationWeight
  by_cases hh : IsHullState R.params R.range p.1 Yt
  · by_cases hl : IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2
    · rw [if_pos hh, if_pos hl, ENNReal.toReal_ofReal (stepWeight_nonneg h hn p.1 p.2 hh), abs_mul,
        abs_of_nonneg (stepWeight_nonneg h hn p.1 p.2 hh)]
      have hd := h.wellPosed.hasExpansions.2.nonneg _ hb p.1 Yt p.2 hh
      have hw : stepWeight R C V p.1 Yt p.2 bad b ≤ R.labelWeight (n * R.params.side) p.1 Yt p.2 * Cd := by
        rw [stepWeight_eq_mul]
        have hm := markProduct_le_one h.wellPosed C V p.1 bad
        have hm0 := markProduct_nonneg h.wellPosed C V p.1 bad
        calc _ ≤ R.labelWeight (n * R.params.side) p.1 Yt p.2 * stepTransitionDensity R.params R.coupling p.1 b V * 1 :=
              mul_le_mul_of_nonneg_left hm (mul_nonneg hd (hC p.1 b V).1)
          _ ≤ _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left (hC p.1 b V).2 hd
      have hH : |H p.1 Yt p.2 bad b| ≤ |M| * Real.exp (∑ y : Yt, A.score (p.2 y)) :=
        (hM p.1 Yt p.2 bad b hl).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
      have e : scoredDensity A (n * R.params.side) Yt p =
          R.labelWeight (n * R.params.side) p.1 Yt p.2 * Real.exp (∑ y : Yt, A.score (p.2 y)) := by
        unfold scoredDensity
        rw [if_pos (show IsHullState R.params (clusterRange R.coupling) p.1 Yt from hh)]
      rw [e]
      calc _ ≤ (R.labelWeight (n * R.params.side) p.1 Yt p.2 * Cd) * (|M| * Real.exp (∑ y : Yt, A.score (p.2 y))) :=
            mul_le_mul hw hH (abs_nonneg _) (mul_nonneg hd hCd)
        _ = _ := by ring
    · rw [if_neg hl, mul_zero, abs_zero]
      exact hB
  · rw [if_neg hh]
    simpa using hB
private theorem weightedCase_integrable (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (hT : IsTame A H) :
    Integrable (weightedCase C V H bad Yt b)
      ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) := by
  obtain ⟨B, hB⟩ := weightedCase_abs_le (C := C) (V := V) (bad := bad) (Yt := Yt) (b := b) h hn hT
  exact ((scoredDensity_integrable h (isBlockTorusSide_mul h hn) Yt).const_mul B).mono'
    (weightedCase_measurable h hn hT).aestronglyMeasurable
    (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hB p)
private theorem posPart_measurable (hT : IsTame A H) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => posPart H bad Yt b p.1 p.2 :=
  (hT.measurable_live Yt bad b).ennreal_ofReal
private theorem negPart_measurable (hT : IsTame A H) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => negPart H bad Yt b p.1 p.2 :=
  (hT.measurable_live Yt bad b).neg.ennreal_ofReal
open Classical in
private theorem caseTerm_eq_weightedCase (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (q : CoarseState R n)
    {W : TorusField (n * R.params.side)} {ν : q.unlabelled Yt → R.labels.Ω}
    (hq : coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) :
    caseTerm R C V q H bad Yt b W ν = weightedCase C V H bad Yt b (q.fieldWithStoredLinks W, q.fillLabels Yt ν) := by
  unfold caseTerm weightedCase liveRestriction configurationWeight
  by_cases hh : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt
  · rw [if_pos ⟨hh, hq⟩, if_pos hh, ENNReal.toReal_ofReal (stepWeight_nonneg h hn _ _ hh)]
    by_cases hl : IsLiveState R.params R.coupling R.labelWeight (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν)
    · rw [if_pos hl, mul_comm]
    · rw [if_neg hl, stepWeight_eq_zero_of_not_live h hn _ _ hh hl]
      simp
  · rw [if_neg fun x => hh x.1, if_neg hh]
    simp
open Classical in
private theorem massWith_posPart_eq (q : CoarseState R n)
    (hq : ∀ (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω),
      coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) :
    configurationMassWith R C V bad Yt b (posPart H bad Yt b) q =
      ∫⁻ W, ∫⁻ ν, ENNReal.ofReal (weightedCase C V H bad Yt b (q.fieldWithStoredLinks W, q.fillLabels Yt ν))
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  unfold configurationMassWith
  refine lintegral_congr fun W => lintegral_congr fun ν => ?_
  rw [← configurationWeight_mul_posPart]
  unfold configurationWeight
  by_cases hh : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt
  · rw [if_pos ⟨hh, hq W ν⟩, if_pos hh]
  · rw [if_neg fun x => hh x.1, if_neg hh, zero_mul]
open Classical in
private theorem massWith_negPart_eq (q : CoarseState R n)
    (hq : ∀ (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω),
      coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) :
    configurationMassWith R C V bad Yt b (negPart H bad Yt b) q =
      ∫⁻ W, ∫⁻ ν, ENNReal.ofReal (-weightedCase C V H bad Yt b (q.fieldWithStoredLinks W, q.fillLabels Yt ν))
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  unfold configurationMassWith
  refine lintegral_congr fun W => lintegral_congr fun ν => ?_
  rw [← configurationWeight_mul_negPart]
  unfold configurationWeight
  by_cases hh : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt
  · rw [if_pos ⟨hh, hq W ν⟩, if_pos hh]
  · rw [if_neg fun x => hh x.1, if_neg hh, zero_mul]
private theorem integral_caseTerm_eq (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (hT : IsTame A H)
    (q : CoarseState R n)
    (hp : configurationMassWith R C V bad Yt b (posPart H bad Yt b) q ≠ ⊤)
    (hm : configurationMassWith R C V bad Yt b (negPart H bad Yt b) q ≠ ⊤) :
    ∫ W, ∫ ν, caseTerm R C V q H bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      (configurationMassWith R C V bad Yt b (posPart H bad Yt b) q).toReal -
        (configurationMassWith R C V bad Yt b (negPart H bad Yt b) q).toReal := by
  classical
  by_cases hS : ∃ (W₀ : TorusField (n * R.params.side)) (ν₀ : q.unlabelled Yt → R.labels.Ω),
      coarseStateOf R C (q.fieldWithStoredLinks W₀) Yt (q.fillLabels Yt ν₀) bad b = q
  · obtain ⟨W₀, ν₀, h0⟩ := hS
    have hq : ∀ (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω),
        coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q :=
      fun W ν => coarseStateOf_indep q C Yt bad b h0
    set v : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) → ℝ :=
      fun p => weightedCase C V H bad Yt b (q.fieldWithStoredLinks p.1, q.fillLabels Yt p.2) with hv
    have hvm : Measurable v := (weightedCase_measurable h hn hT).comp
      (((measurable_fieldWithStoredLinks q).comp measurable_fst).prodMk
        ((measurable_fillLabels q Yt).comp measurable_snd))
    have e1 : configurationMassWith R C V bad Yt b (posPart H bad Yt b) q = ∫⁻ p, ENNReal.ofReal (v p)
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : q.unlabelled Yt => R.labels.μ)) := by
      rw [lintegral_prod _ hvm.ennreal_ofReal.aemeasurable]
      exact massWith_posPart_eq q hq
    have e2 : configurationMassWith R C V bad Yt b (negPart H bad Yt b) q = ∫⁻ p, ENNReal.ofReal (-v p)
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : q.unlabelled Yt => R.labels.μ)) := by
      have hneg : Measurable fun p => ENNReal.ofReal (-v p) := hvm.neg.ennreal_ofReal
      rw [lintegral_prod (fun p => ENNReal.ofReal (-v p)) hneg.aemeasurable]
      exact massWith_negPart_eq q hq
    have hi : Integrable v
        ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : q.unlabelled Yt => R.labels.μ)) :=
      integrable_of_lintegral_pos_neg_ne_top hvm (e1 ▸ hp) (e2 ▸ hm)
    have e3 : ∫ W, ∫ ν, caseTerm R C V q H bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ)
          ∂(fieldHaar (n * R.params.side)) =
        ∫ p, v p ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : q.unlabelled Yt => R.labels.μ)) := by
      rw [integral_prod _ hi]
      refine integral_congr_ae (ae_of_all _ fun W => integral_congr_ae (ae_of_all _ fun ν => ?_))
      exact caseTerm_eq_weightedCase h hn q (hq W ν)
    rw [e3, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi, e1, e2]
  · push Not at hS
    have h0 : ∀ (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω),
        caseTerm R C V q H bad Yt b W ν = 0 := fun W ν => by
      unfold caseTerm
      rw [if_neg fun x => hS W ν x.2]
    have z : ∀ g : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal,
        configurationMassWith R C V bad Yt b g q = 0 := fun g => by
      unfold configurationMassWith
      refine Eq.trans (lintegral_congr (g := fun _ => 0) fun W => ?_) (by simp)
      exact Eq.trans (lintegral_congr (g := fun _ => 0) fun ν => if_neg fun x => hS W ν x.2) (by simp)
    simp [h0, z]
variable (C V H bad Yt b) in
private def stateIntegral (q : CoarseState R n) : ℝ :=
  ∫ W, ∫ ν, caseTerm R C V q H bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
variable (C V H) in
private def totalCaseIntegral : ℝ :=
  ∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
    ∫ p, weightedCase C V H bad Yt b p ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ))
private theorem lintegral_posPart_eq (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (hT : IsTame A H) :
    ∫⁻ W, ∫⁻ ω : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ω * posPart H bad Yt b W ω
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∫⁻ p, ENNReal.ofReal (weightedCase C V H bad Yt b p)
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) := by
  rw [lintegral_prod _ (weightedCase_measurable h hn hT).ennreal_ofReal.aemeasurable]
  exact lintegral_congr fun W => lintegral_congr fun ω => configurationWeight_mul_posPart W ω
private theorem lintegral_negPart_eq (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (hT : IsTame A H) :
    ∫⁻ W, ∫⁻ ω : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ω * negPart H bad Yt b W ω
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∫⁻ p, ENNReal.ofReal (-weightedCase C V H bad Yt b p)
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) := by
  have hm : Measurable fun p => ENNReal.ofReal (-weightedCase C V H bad Yt b p) :=
    (weightedCase_measurable h hn hT).neg.ennreal_ofReal
  rw [lintegral_prod (fun p => ENNReal.ofReal (-weightedCase C V H bad Yt b p)) hm.aemeasurable]
  exact lintegral_congr fun W => lintegral_congr fun ω => configurationWeight_mul_negPart W ω
private theorem lintegral_pos_weightedCase_ne_top (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (hT : IsTame A H) :
    ∫⁻ p, ENNReal.ofReal (weightedCase C V H bad Yt b p)
      ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) ≠ ⊤ :=
  (weightedCase_integrable h hn hT).lintegral_lt_top.ne
private theorem lintegral_neg_weightedCase_ne_top (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (hT : IsTame A H) :
    ∫⁻ p, ENNReal.ofReal (-weightedCase C V H bad Yt b p)
      ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) ≠ ⊤ :=
  (weightedCase_integrable h hn hT).neg.lintegral_lt_top.ne
private theorem lintegral_configurationWeight_ne_top (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) :
    ∫⁻ W, ∫⁻ ω : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ω
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) ≠ ⊤ := by
  classical
  obtain ⟨Cd, hCd, hC⟩ := transitionDensity_bounded (n := n) h
  have hb := isBlockTorusSide_mul h hn
  have hm := h.inputs.measurable R h.wellPosed n hn C V bad Yt b
  rw [← lintegral_prod (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
    configurationWeight R C V bad Yt b p.1 p.2) hm.aemeasurable]
  refine ne_top_of_le_ne_top
    (((scoredDensity_integrable (A := A) h hb Yt).const_mul Cd).lintegral_lt_top.ne) (lintegral_mono fun p => ?_)
  unfold configurationWeight
  by_cases hh : IsHullState R.params R.range p.1 Yt
  · rw [if_pos hh]
    refine ENNReal.ofReal_le_ofReal ?_
    have hd := h.wellPosed.hasExpansions.2.nonneg _ hb p.1 Yt p.2 hh
    have e : scoredDensity A (n * R.params.side) Yt p =
        R.labelWeight (n * R.params.side) p.1 Yt p.2 * Real.exp (∑ y : Yt, A.score (p.2 y)) := by
      unfold scoredDensity
      rw [if_pos (show IsHullState R.params (clusterRange R.coupling) p.1 Yt from hh)]
    have hE : 1 ≤ Real.exp (∑ y : Yt, A.score (p.2 y)) :=
      Real.one_le_exp (Finset.sum_nonneg fun y _ => h.response.price.nonneg _)
    rw [e, stepWeight_eq_mul]
    have hm1 := markProduct_le_one h.wellPosed C V p.1 bad
    calc _ ≤ R.labelWeight (n * R.params.side) p.1 Yt p.2 * stepTransitionDensity R.params R.coupling p.1 b V * 1 :=
          mul_le_mul_of_nonneg_left hm1 (mul_nonneg hd (hC p.1 b V).1)
      _ ≤ R.labelWeight (n * R.params.side) p.1 Yt p.2 * Cd * 1 := by
          rw [mul_one, mul_one]
          exact mul_le_mul_of_nonneg_left (hC p.1 b V).2 hd
      _ ≤ R.labelWeight (n * R.params.side) p.1 Yt p.2 * Cd * Real.exp (∑ y : Yt, A.score (p.2 y)) :=
          mul_le_mul_of_nonneg_left hE (mul_nonneg hd hCd)
      _ = _ := by ring
  · rw [if_neg hh]
    exact zero_le
private theorem stateIntegral_integrable_and_eq (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (hT : IsTame A H) :
    Integrable (fun ω => stateIntegral C V H bad Yt b ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩)
        (Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side) ∧
      ∫ ω, stateIntegral C V H bad Yt b ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩
          ∂(Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side) =
        ∫ p, weightedCase C V H bad Yt b p
          ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) := by
  obtain ⟨-, -, mp, ip⟩ := h.inputs.massWith R h.wellPosed n hn C V bad Yt b _
    (posPart_measurable (bad := bad) (b := b) hT)
  obtain ⟨-, -, mm, im⟩ := h.inputs.massWith R h.wellPosed n hn C V bad Yt b _
    (negPart_measurable (bad := bad) (b := b) hT)
  rw [lintegral_posPart_eq h hn hT] at ip
  rw [lintegral_negPart_eq h hn hT] at im
  have fp := lintegral_pos_weightedCase_ne_top (C := C) (V := V) (bad := bad) (Yt := Yt) (b := b) h hn hT
  have fm := lintegral_neg_weightedCase_ne_top (C := C) (V := V) (bad := bad) (Yt := Yt) (b := b) h hn hT
  rw [← ip] at fp
  rw [← im] at fm
  have ap := ae_lt_top mp fp
  have am := ae_lt_top mm fm
  have aeq : (fun ω => stateIntegral C V H bad Yt b ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩)
      =ᵐ[Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side]
      fun ω => (configurationMassWith R C V bad Yt b (posPart H bad Yt b)
          ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩).toReal -
        (configurationMassWith R C V bad Yt b (negPart H bad Yt b)
          ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩).toReal := by
    filter_upwards [ap, am] with ω a1 a2
    exact integral_caseTerm_eq h hn hT _ a1.ne a2.ne
  have i1 := integrable_toReal_of_lintegral_ne_top mp.aemeasurable fp
  have i2 := integrable_toReal_of_lintegral_ne_top mm.aemeasurable fm
  refine ⟨(i1.sub i2).congr aeq.symm, ?_⟩
  rw [integral_congr_ae aeq, integral_sub i1 i2, integral_toReal mp.aemeasurable ap,
    integral_toReal mm.aemeasurable am, ip, im,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (weightedCase_integrable h hn hT)]
private theorem stateIntegral_eq_zero_of_ne {q : CoarseState R n}
    (hY : q.1 ≠ coarseHull R.params.side R.range R.nextRange bad Yt C) :
    stateIntegral C V H bad Yt b q = 0 := by
  classical
  have h0 : ∀ (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω),
      caseTerm R C V q H bad Yt b W ν = 0 := fun W ν => by
    unfold caseTerm
    rw [if_neg fun x => hY (congrArg Sigma.fst x.2).symm]
  unfold stateIntegral
  simp [h0]
private theorem stateIntegral_integrable (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (hT : IsTame A H)
    (Y : Finset (TorusSite n)) :
    Integrable (fun ω : Y → CoarseLabel R.labels.Ω R.params.side => stateIntegral C V H bad Yt b ⟨Y, ω⟩)
      (Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side) := by
  by_cases hY : Y = coarseHull R.params.side R.range R.nextRange bad Yt C
  · subst hY
    exact (stateIntegral_integrable_and_eq h hn hT).1
  · have e : (fun ω : Y → CoarseLabel R.labels.Ω R.params.side => stateIntegral C V H bad Yt b ⟨Y, ω⟩) = fun _ => 0 :=
      funext fun ω => stateIntegral_eq_zero_of_ne (q := ⟨Y, ω⟩) hY
    rw [e]
    exact integrable_zero _ _ _
private theorem sum_integral_stateIntegral (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (hT : IsTame A H)
    (hs : IsBlockTorusSide R.params n) :
    (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
      ∫ ω, stateIntegral (hotCoreSites R V) V H bad Yt b ⟨Y, ω⟩
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)) =
      ∫ p, weightedCase (hotCoreSites R V) V H bad Yt b p
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) := by
  classical
  have hmem : coarseHull R.params.side R.range R.nextRange bad Yt (hotCoreSites R V) ∈
      Finset.univ.filter (IsHullState R.params R.nextRange V) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      h.inputs.coarseHull R.params h.wellPosed.admissible R.range R.nextRange h.wellPosed.range_le
        h.wellPosed.nextRange_ge n hs.1 V bad Yt⟩
  rw [Finset.sum_eq_single_of_mem _ hmem]
  · exact (stateIntegral_integrable_and_eq h hn hT).2
  · intro Y _ hY
    have e : ∀ ω : Y → CoarseLabel R.labels.Ω R.params.side,
        stateIntegral (hotCoreSites R V) V H bad Yt b ⟨Y, ω⟩ = 0 :=
      fun ω => stateIntegral_eq_zero_of_ne (q := ⟨Y, ω⟩) hY
    simp [e]
private theorem ae_masses_ne_top (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (hT : IsTame A H)
    (Y : Finset (TorusSite n)) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side),
      configurationMassWith R C V bad Yt b (posPart H bad Yt b) ⟨Y, ω⟩ ≠ ⊤ ∧
      configurationMassWith R C V bad Yt b (negPart H bad Yt b) ⟨Y, ω⟩ ≠ ⊤ ∧
      configurationMass R C V bad Yt b ⟨Y, ω⟩ ≠ ⊤ := by
  obtain ⟨zp, -, mp, ip⟩ := h.inputs.massWith R h.wellPosed n hn C V bad Yt b _
    (posPart_measurable (bad := bad) (b := b) hT)
  obtain ⟨zm, -, mm, im⟩ := h.inputs.massWith R h.wellPosed n hn C V bad Yt b _
    (negPart_measurable (bad := bad) (b := b) hT)
  obtain ⟨zo, mo, io⟩ := h.inputs.support R h.wellPosed n hn C V bad Yt b
  by_cases hY : Y = coarseHull R.params.side R.range R.nextRange bad Yt C
  · subst hY
    rw [lintegral_posPart_eq h hn hT] at ip
    rw [lintegral_negPart_eq h hn hT] at im
    have fp := lintegral_pos_weightedCase_ne_top (C := C) (V := V) (bad := bad) (Yt := Yt) (b := b) h hn hT
    have fm := lintegral_neg_weightedCase_ne_top (C := C) (V := V) (bad := bad) (Yt := Yt) (b := b) h hn hT
    rw [← ip] at fp
    rw [← im] at fm
    have fo := lintegral_configurationWeight_ne_top (C := C) (V := V) (bad := bad) (Yt := Yt) (b := b) h hn
    rw [← io] at fo
    filter_upwards [ae_lt_top mp fp, ae_lt_top mm fm, ae_lt_top mo fo] with ω a1 a2 a3
    exact ⟨a1.ne, a2.ne, a3.ne⟩
  · refine ae_of_all _ fun ω => ?_
    rw [zp ⟨Y, ω⟩ hY, zm ⟨Y, ω⟩ hY, zo ⟨Y, ω⟩ hY]
    simp
private theorem ae_caseMean_mul (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (hT : IsTame A H)
    (Y : Finset (TorusSite n)) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side),
      caseMean R C V ⟨Y, ω⟩ H * coarseStateWeight R C V ⟨Y, ω⟩ = caseIntegral R C V ⟨Y, ω⟩ H := by
  classical
  have hall : ∀ᵐ ω ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side),
      ∀ bad ∈ (markedBonds R C).powerset, ∀ (Yt : Finset (TorusSite (n * R.params.side)))
        (b : BaseChoice R.params.side n),
        configurationMassWith R C V bad Yt b (posPart H bad Yt b) ⟨Y, ω⟩ ≠ ⊤ ∧
        configurationMassWith R C V bad Yt b (negPart H bad Yt b) ⟨Y, ω⟩ ≠ ⊤ ∧
        configurationMass R C V bad Yt b ⟨Y, ω⟩ ≠ ⊤ :=
    (Filter.eventually_all_finset _).2 fun bad _ => Filter.eventually_all.2 fun Yt => Filter.eventually_all.2 fun b =>
      ae_masses_ne_top h hn hT Y
  filter_upwards [hall] with ω hω
  by_cases h0 : coarseStateWeight R C V ⟨Y, ω⟩ = 0
  · rw [h0, mul_zero]
    have hfin : coarseStateMass R C V ⟨Y, ω⟩ ≠ ⊤ :=
      ENNReal.sum_ne_top.2 fun bad hbad => ENNReal.sum_ne_top.2 fun Yt _ => ENNReal.sum_ne_top.2 fun b _ =>
        (hω bad hbad Yt b).2.2
    have hz : coarseStateMass R C V ⟨Y, ω⟩ = 0 := by
      unfold coarseStateWeight at h0
      exact (ENNReal.toReal_eq_zero_iff _).mp h0 |>.resolve_right hfin
    have hcase : ∀ bad ∈ (markedBonds R C).powerset, ∀ (Yt : Finset (TorusSite (n * R.params.side)))
        (b : BaseChoice R.params.side n), configurationMass R C V bad Yt b ⟨Y, ω⟩ = 0 := by
      intro bad hbad Yt b
      have h1 := (Finset.sum_eq_zero_iff.mp hz) bad hbad
      have h2 := (Finset.sum_eq_zero_iff.mp h1) Yt (Finset.mem_univ _)
      exact (Finset.sum_eq_zero_iff.mp h2) b (Finset.mem_univ _)
    symm
    unfold caseIntegral
    refine Finset.sum_eq_zero fun bad hbad => Finset.sum_eq_zero fun Yt _ => Finset.sum_eq_zero fun b _ => ?_
    have z1 := (h.inputs.massWith R h.wellPosed n hn C V bad Yt b _
      (posPart_measurable (bad := bad) (b := b) hT)).2.1 _ (hcase bad hbad Yt b)
    have z2 := (h.inputs.massWith R h.wellPosed n hn C V bad Yt b _
      (negPart_measurable (bad := bad) (b := b) hT)).2.1 _ (hcase bad hbad Yt b)
    rw [integral_caseTerm_eq h hn hT _ (hω bad hbad Yt b).1 (hω bad hbad Yt b).2.1, z1, z2]
    simp
  · unfold caseMean
    exact div_mul_cancel₀ _ h0
private theorem sum_integral_caseMean (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (hT : IsTame A H)
    (hs : IsBlockTorusSide R.params n) :
    (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
      ∫ ω, caseMean R (hotCoreSites R V) V ⟨Y, ω⟩ H * coarseStateWeight R (hotCoreSites R V) V ⟨Y, ω⟩
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)) =
      totalCaseIntegral (hotCoreSites R V) V H := by
  classical
  have e : ∀ Y : Finset (TorusSite n), ∫ ω, caseMean R (hotCoreSites R V) V ⟨Y, ω⟩ H *
        coarseStateWeight R (hotCoreSites R V) V ⟨Y, ω⟩
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
        ∑ b : BaseChoice R.params.side n,
        ∫ ω, stateIntegral (hotCoreSites R V) V H bad Yt b ⟨Y, ω⟩
          ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) := by
    intro Y
    rw [integral_congr_ae (ae_caseMean_mul h hn hT Y)]
    show ∫ ω, (∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
        ∑ b : BaseChoice R.params.side n, stateIntegral (hotCoreSites R V) V H bad Yt b ⟨Y, ω⟩)
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) = _
    rw [integral_finsetSum _ fun bad _ => integrable_finsetSum _ fun Yt _ => integrable_finsetSum _ fun b _ =>
      stateIntegral_integrable h hn hT Y]
    refine Finset.sum_congr rfl fun bad _ => ?_
    rw [integral_finsetSum _ fun Yt _ => integrable_finsetSum _ fun b _ => stateIntegral_integrable h hn hT Y]
    refine Finset.sum_congr rfl fun Yt _ => ?_
    rw [integral_finsetSum _ fun b _ => stateIntegral_integrable h hn hT Y]
  simp_rw [e]
  unfold totalCaseIntegral
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun bad _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Yt _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => sum_integral_stateIntegral h hn hT hs
private theorem coarseHull_empty (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) :
    coarseHull R.params.side R.range R.nextRange bad Yt (∅ : Finset (TorusSite n)) = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coarseHull_empty <;> assumption
private theorem massWith_at_empty (h : LevelInputs R A) (hn : R.params.n₀ ≤ n)
    (g : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal)
    (hg : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => g p.1 p.2)
    (Y : Finset (TorusSite n))
    (hY : Y = coarseHull R.params.side R.range R.nextRange bad Yt (∅ : Finset (TorusSite n)))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) :
    configurationMassWith R ∅ V bad Yt b g ⟨Y, ω⟩ =
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R ∅ V bad Yt b W ωt * g W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  subst hY
  obtain ⟨-, -, hm, hi⟩ := h.inputs.massWith R h.wellPosed n hn ∅ V bad Yt b g hg
  rw [← hi]
  have he : IsEmpty (coarseHull R.params.side R.range R.nextRange bad Yt (∅ : Finset (TorusSite n))) :=
    ⟨fun x => by
      obtain ⟨z, hz⟩ := x
      rw [coarseHull_empty] at hz
      simp at hz⟩
  rw [Measure.pi_of_empty _ ω, lintegral_dirac' _ hm]
private theorem caseIntegral_empty (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (hT : IsTame A H) :
    caseIntegral R ∅ V (emptyCoarseState R) H = totalCaseIntegral ∅ V H := by
  classical
  unfold caseIntegral totalCaseIntegral
  refine Finset.sum_congr rfl fun bad _ => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ => ?_
  have ep : configurationMassWith R ∅ V bad Yt b (posPart H bad Yt b) (emptyCoarseState R) = _ :=
    massWith_at_empty h hn _ (posPart_measurable hT) ∅ (coarseHull_empty bad Yt).symm (emptyCoarseState R).2
  have em : configurationMassWith R ∅ V bad Yt b (negPart H bad Yt b) (emptyCoarseState R) = _ :=
    massWith_at_empty h hn _ (negPart_measurable hT) ∅ (coarseHull_empty bad Yt).symm (emptyCoarseState R).2
  rw [lintegral_posPart_eq h hn hT] at ep
  rw [lintegral_negPart_eq h hn hT] at em
  have fp := lintegral_pos_weightedCase_ne_top (C := ∅) (V := V) (bad := bad) (Yt := Yt) (b := b) h hn hT
  have fm := lintegral_neg_weightedCase_ne_top (C := ∅) (V := V) (bad := bad) (Yt := Yt) (b := b) h hn hT
  rw [← ep] at fp
  rw [← em] at fm
  rw [integral_caseTerm_eq h hn hT _ fp fm, ep, em,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (weightedCase_integrable h hn hT)]
private theorem totalCaseIntegral_eq_zero (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (hT : IsTame A H)
    (hD : kernelImage R.params R.coupling R.functional n V = 0) : totalCaseIntegral C V H = 0 := by
  classical
  have hz := h.inputs.weightsSum R h.wellPosed n hn C V
  rw [hD, ENNReal.ofReal_zero] at hz
  unfold totalCaseIntegral
  refine Finset.sum_eq_zero fun bad hbad => Finset.sum_eq_zero fun Yt _ => Finset.sum_eq_zero fun b _ => ?_
  have h1 := (Finset.sum_eq_zero_iff.mp hz) bad hbad
  have h2 := (Finset.sum_eq_zero_iff.mp h1) Yt (Finset.mem_univ _)
  have h3 := (Finset.sum_eq_zero_iff.mp h2) b (Finset.mem_univ _)
  have hm := h.inputs.measurable R h.wellPosed n hn C V bad Yt b
  rw [← lintegral_prod (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
    configurationWeight R C V bad Yt b p.1 p.2) hm.aemeasurable] at h3
  have h4 := (lintegral_eq_zero_iff hm).mp h3
  refine integral_eq_zero_of_ae ?_
  filter_upwards [h4] with p hp
  have hp' : configurationWeight R C V bad Yt b p.1 p.2 = 0 := hp
  unfold weightedCase
  rw [hp']
  simp
end Cases
private def CarriesResponse (R : StepSetup) (A : ResponseSetup R) (rO : ColdResponse R.params.side R.depth) : Prop :=
  ∀ (m : ℕ) [NeZero m], IsBlockTorusSide R.params m → ∀ (y : TorusSite m) (W : TorusField m)
    (hw : PlaquetteWeight (fineSide R.params.side R.depth m)),
    R.functional m W * rO m y W hw = open Classical in
      ∑ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
      ∫ ω, A.hull m y W Yt ω hw * R.labelWeight m W Yt ω ∂(Measure.pi fun _ : Yt => R.labels.μ)
section Sections
variable {R : StepSetup} {A : ResponseSetup R} {m : ℕ} [NeZero m]
private theorem measurableSet_live (h : LevelInputs R A) (hb : IsBlockTorusSide R.params m) (Yt : Finset (TorusSite m)) :
    MeasurableSet {p : TorusField m × (Yt → R.labels.Ω) | IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} := by
  classical
  have hm := (h.wellPosed.hasExpansions.2.borel m hb Yt).1
  have e : {p : TorusField m × (Yt → R.labels.Ω) | IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} =
      (fun p : TorusField m × (Yt → R.labels.Ω) =>
        if IsHullState R.params (clusterRange R.coupling) p.1 Yt then R.labelWeight m p.1 Yt p.2 else 0) ⁻¹'
        Set.Ioi 0 := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi, IsLiveState]
    split_ifs with hh
    · simp [hh]
    · simp [hh]
  rw [e]
  convert hm measurableSet_Ioi using 3
private theorem siteScore_le_exp (h : LevelInputs R A) {Y : Finset (TorusSite m)} (ω : Y → R.labels.Ω) (y : TorusSite m) :
    siteScore A.score Y ω y ≤ Real.exp (∑ z : Y, A.score (ω z)) := by
  classical
  unfold siteScore
  split_ifs with hy
  · have h1 : A.score (ω ⟨y, hy⟩) ≤ ∑ z : Y, A.score (ω z) :=
      Finset.single_le_sum (f := fun z : Y => A.score (ω z)) (fun z _ => h.response.price.nonneg _)
        (Finset.mem_univ (⟨y, hy⟩ : Y))
    linarith [Real.add_one_le_exp (∑ z : Y, A.score (ω z))]
  · exact (Real.exp_pos _).le
private theorem one_le_exp_score (h : LevelInputs R A) {Y : Finset (TorusSite m)} (ω : Y → R.labels.Ω) :
    1 ≤ Real.exp (∑ z : Y, A.score (ω z)) :=
  Real.one_le_exp (Finset.sum_nonneg fun y _ => h.response.price.nonneg _)
private theorem hull_abs_le (h : LevelInputs R A) (hb : IsBlockTorusSide R.params m) (y : TorusSite m)
    (W : TorusField m) (Yt : Finset (TorusSite m)) (ω : Yt → R.labels.Ω)
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ω)
    (hw : PlaquetteWeight (fineSide R.params.side R.depth m)) :
    |A.hull m y W Yt ω hw| ≤ (|A.cold m y (trivialField m) hw| +
      (|A.responseParams.C₀| + 1) * |weightNorm R.params.side R.depth hw|) *
      Real.exp (∑ z : Yt, A.score (ω z)) := by
  classical
  have hs := h.response.bounds.size_hull m hb y W Yt ω hl hw
  unfold centeredHullResponse at hs
  have hE := one_le_exp_score h ω
  have hsc := siteScore_le_exp h ω y
  have hsc0 : 0 ≤ siteScore A.score Yt ω y := by
    unfold siteScore
    split_ifs
    · exact h.response.price.nonneg _
    · exact le_rfl
  set E := Real.exp (∑ z : Yt, A.score (ω z))
  set Z := weightNorm R.params.side R.depth hw
  set Pf := A.cold m y (trivialField m) hw
  have h1 : |A.hull m y W Yt ω hw| ≤ |Pf| + (|A.responseParams.C₀| + siteScore A.score Yt ω y) * |Z| := by
    have e : A.hull m y W Yt ω hw = (A.hull m y W Yt ω hw - Pf) + Pf := by ring
    have h2 : |(A.responseParams.C₀ + siteScore A.score Yt ω y) * Z| ≤
        (|A.responseParams.C₀| + siteScore A.score Yt ω y) * |Z| := by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg hsc0]
    calc |A.hull m y W Yt ω hw| = |(A.hull m y W Yt ω hw - Pf) + Pf| := by rw [← e]
      _ ≤ |A.hull m y W Yt ω hw - Pf| + |Pf| := abs_add_le _ _
      _ ≤ (|A.responseParams.C₀| + siteScore A.score Yt ω y) * |Z| + |Pf| := by
          linarith [hs.trans (le_abs_self _)]
      _ = _ := by ring
  have a1 : |Pf| ≤ |Pf| * E := le_mul_of_one_le_right (abs_nonneg _) hE
  have a2 : |A.responseParams.C₀| + siteScore A.score Yt ω y ≤ (|A.responseParams.C₀| + 1) * E := by
    nlinarith [abs_nonneg A.responseParams.C₀]
  have a3 := mul_le_mul_of_nonneg_right a2 (abs_nonneg Z)
  have e2 : (|Pf| + (|A.responseParams.C₀| + 1) * |Z|) * E = |Pf| * E + (|A.responseParams.C₀| + 1) * E * |Z| := by
    ring
  rw [e2]
  linarith
private theorem labelWeight_measurable (h : LevelInputs R A) (hb : IsBlockTorusSide R.params m)
    {Yt : Finset (TorusSite m)} {W : TorusField m} (hh : IsHullState R.params (clusterRange R.coupling) W Yt) :
    Measurable fun ω => R.labelWeight m W Yt ω := by
  classical
  have hm := (h.wellPosed.hasExpansions.2.borel m hb Yt).1.comp (measurable_prodMk_left (x := W))
  have e : (fun ω => R.labelWeight m W Yt ω) =
      (fun p : TorusField m × (Yt → R.labels.Ω) =>
        if IsHullState R.params (clusterRange R.coupling) p.1 Yt then R.labelWeight m p.1 Yt p.2 else 0) ∘
        Prod.mk W := by
    funext ω
    simp [hh]
  rw [e]
  exact hm
private theorem scoredDensity_of_hull (A : ResponseSetup R) {Yt : Finset (TorusSite m)} {W : TorusField m}
    (hh : IsHullState R.params (clusterRange R.coupling) W Yt) (ω : Yt → R.labels.Ω) :
    scoredDensity A m Yt (W, ω) = R.labelWeight m W Yt ω * Real.exp (∑ y : Yt, A.score (ω y)) := by
  classical
  unfold scoredDensity
  rw [if_pos hh]
private theorem labelWeight_integrable (h : LevelInputs R A) (hb : IsBlockTorusSide R.params m)
    {Yt : Finset (TorusSite m)} {W : TorusField m} (hh : IsHullState R.params (clusterRange R.coupling) W Yt) :
    Integrable (fun ω => R.labelWeight m W Yt ω) (Measure.pi fun _ : Yt => R.labels.μ) := by
  refine (scoredDensity_integrable_section h hb Yt W).mono' (labelWeight_measurable h hb hh).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  have hd := h.wellPosed.hasExpansions.2.nonneg m hb W Yt ω hh
  rw [scoredDensity_of_hull A hh, Real.norm_eq_abs, abs_of_nonneg hd]
  exact le_mul_of_one_le_right hd (one_le_exp_score h ω)
open Classical in
private def liveHull (A : ResponseSetup R) (m : ℕ) [NeZero m] (y : TorusSite m)
    (hw : PlaquetteWeight (fineSide R.params.side R.depth m)) (Yt : Finset (TorusSite m))
    (p : TorusField m × (Yt → R.labels.Ω)) : ℝ :=
  if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then A.hull m y p.1 Yt p.2 hw else 0
private theorem liveHull_measurable (h : LevelInputs R A) (hb : IsBlockTorusSide R.params m) (y : TorusSite m)
    (hw : PlaquetteWeight (fineSide R.params.side R.depth m)) (Yt : Finset (TorusSite m)) :
    Measurable (liveHull A m y hw Yt) :=
  h.response.bounds.hull_borel m hb y Yt hw
private theorem hull_mul_labelWeight_integrable (h : LevelInputs R A) (hb : IsBlockTorusSide R.params m)
    {Yt : Finset (TorusSite m)} {W : TorusField m} (hh : IsHullState R.params (clusterRange R.coupling) W Yt)
    (y : TorusSite m) (hw : PlaquetteWeight (fineSide R.params.side R.depth m)) :
    Integrable (fun ω => A.hull m y W Yt ω hw * R.labelWeight m W Yt ω) (Measure.pi fun _ : Yt => R.labels.μ) := by
  classical
  have hqm : Measurable fun ω : Yt → R.labels.Ω => liveHull A m y hw Yt (W, ω) :=
    (liveHull_measurable h hb y hw Yt).comp measurable_prodMk_left
  have e : (fun ω => A.hull m y W Yt ω hw * R.labelWeight m W Yt ω) =
      fun ω => liveHull A m y hw Yt (W, ω) * R.labelWeight m W Yt ω := by
    funext ω
    by_cases hl : IsLiveState R.params R.coupling R.labelWeight W Yt ω
    · unfold liveHull
      rw [if_pos hl]
    · have h0 : R.labelWeight m W Yt ω = 0 :=
        le_antisymm (not_lt.mp fun hp => hl ⟨hh, hp⟩) (h.wellPosed.hasExpansions.2.nonneg m hb W Yt ω hh)
      rw [h0, mul_zero, mul_zero]
  rw [e]
  have hM : 0 ≤ |A.cold m y (trivialField m) hw| + (|A.responseParams.C₀| + 1) * |weightNorm R.params.side R.depth hw| :=
    add_nonneg (abs_nonneg _) (mul_nonneg (add_nonneg (abs_nonneg _) zero_le_one) (abs_nonneg _))
  refine ((scoredDensity_integrable_section (A := A) h hb Yt W).const_mul (|A.cold m y (trivialField m) hw| +
      (|A.responseParams.C₀| + 1) * |weightNorm R.params.side R.depth hw|)).mono'
    (hqm.mul (labelWeight_measurable h hb hh)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  have hd := h.wellPosed.hasExpansions.2.nonneg m hb W Yt ω hh
  show ‖liveHull A m y hw Yt (W, ω) * R.labelWeight m W Yt ω‖ ≤ _
  rw [scoredDensity_of_hull A hh, Real.norm_eq_abs, abs_mul, abs_of_nonneg hd]
  by_cases hl : IsLiveState R.params R.coupling R.labelWeight W Yt ω
  · have hq := hull_abs_le h hb y W Yt ω hl hw
    have e2 : liveHull A m y hw Yt (W, ω) = A.hull m y W Yt ω hw := by
      unfold liveHull
      rw [if_pos hl]
    rw [e2]
    calc _ ≤ (|A.cold m y (trivialField m) hw| + (|A.responseParams.C₀| + 1) * |weightNorm R.params.side R.depth hw|) *
          Real.exp (∑ z : Yt, A.score (ω z)) * R.labelWeight m W Yt ω := mul_le_mul_of_nonneg_right hq hd
      _ = _ := by ring
  · have e2 : liveHull A m y hw Yt (W, ω) = 0 := by
      unfold liveHull
      rw [if_neg hl]
    rw [e2, abs_zero, zero_mul]
    exact mul_nonneg hM (mul_nonneg hd (Real.exp_pos _).le)
private theorem sum_integral_labelWeight (h : LevelInputs R A) (hb : IsBlockTorusSide R.params m) (W : TorusField m) :
    (open Classical in ∑ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
      ∫ ω, R.labelWeight m W Yt ω ∂(Measure.pi fun _ : Yt => R.labels.μ)) = R.functional m W := by
  classical
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn : R.params.n₀ ≤ m := le_trans (Nat.le_mul_of_pos_left _ hLpos) hb.2
  have hs := h.wellPosed.hasExpansions.2.sum m hb W
  have hD : 0 ≤ R.functional m W := (h.wellPosed.functional_spec m hn).2.1 W
  have hfin : ∀ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
      ∫⁻ ω, ENNReal.ofReal (R.labelWeight m W Yt ω) ∂(Measure.pi fun _ : Yt => R.labels.μ) ≠ ⊤ := fun Yt hY =>
    (labelWeight_integrable h hb (Finset.mem_filter.mp hY).2).lintegral_lt_top.ne
  have e : ∀ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
      ∫ ω, R.labelWeight m W Yt ω ∂(Measure.pi fun _ : Yt => R.labels.μ) =
      (∫⁻ ω, ENNReal.ofReal (R.labelWeight m W Yt ω) ∂(Measure.pi fun _ : Yt => R.labels.μ)).toReal := fun Yt hY => by
    have hh := (Finset.mem_filter.mp hY).2
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => h.wellPosed.hasExpansions.2.nonneg m hb W Yt ω hh)
      (labelWeight_measurable h hb hh).aestronglyMeasurable
  rw [Finset.sum_congr rfl e, ← ENNReal.toReal_sum hfin, hs, ENNReal.toReal_ofReal hD]
end Sections
section Value
variable {R : StepSetup} {A : ResponseSetup R} {n : ℕ} [NeZero n]
private theorem blockBondScores_abs_le (h : LevelInputs R A) (W : TorusField (n * R.params.side)) (V : TorusField n)
    (b : BaseChoice R.params.side n) (Y : TorusSite n) : |blockBondScores (R := R) W V b Y| ≤ 16 := by
  unfold blockBondScores
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hc : ∀ c : TorusBond n, |bondScore R.params R.coupling W V b c| ≤ 2 := fun c =>
    (h.inputs.scoreBounds R.params h.wellPosed.admissible R.coupling n b c).2.2.1 W V
  have : ∀ i : Fin 4, |bondScore R.params R.coupling W V b (Y, i) +
      bondScore R.params R.coupling W V b (Y - unitStep n i, i)| ≤ 4 := fun i =>
    (abs_add_le _ _).trans (by linarith [hc (Y, i), hc (Y - unitStep n i, i)])
  calc _ ≤ ∑ _i : Fin 4, (4 : ℝ) := Finset.sum_le_sum fun i _ => this i
    _ = 16 := by norm_num
private theorem blockBondScores_measurable (h : LevelInputs R A) (V : TorusField n)
    (b : BaseChoice R.params.side n) (Y : TorusSite n) :
    Measurable fun W : TorusField (n * R.params.side) => blockBondScores (R := R) W V b Y := by
  unfold blockBondScores
  have hp : Measurable fun W : TorusField (n * R.params.side) => (W, V) := measurable_id.prodMk measurable_const
  have hc : ∀ c : TorusBond n, Measurable fun W : TorusField (n * R.params.side) =>
      bondScore R.params R.coupling W V b c := fun c => by
    have h0 := (h.inputs.scoreBounds R.params h.wellPosed.admissible R.coupling n b c).2.2.2.2
    exact Measurable.comp (g := fun p : TorusField (n * R.params.side) × TorusField n =>
        bondScore R.params R.coupling p.1 p.2 b c)
      (f := fun W : TorusField (n * R.params.side) => (W, V)) h0 hp
  have h1 : ∀ i : Fin 4, Measurable fun W : TorusField (n * R.params.side) =>
      bondScore R.params R.coupling W V b (Y, i) + bondScore R.params R.coupling W V b (Y - unitStep n i, i) :=
    fun i => (hc (Y, i)).add (hc (Y - unitStep n i, i))
  exact Finset.measurable_sum Finset.univ fun i _ => h1 i
private theorem isTame_caseResponse (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) (V : TorusField n) (Y : TorusSite n)
    (hw : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) : IsTame A (caseResponse A V Y hw) := by
  classical
  have hb := isBlockTorusSide_mul h hn
  set c : ℝ := R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y hw with hc
  refine ⟨fun Yt bad b => ?_, ?_⟩
  · have hl := measurableSet_live h hb Yt
    have e : liveRestriction (caseResponse A V Y hw) Yt bad b = fun p =>
        ∑ y ∈ sitesInBlocks R.params.side {Y},
          (if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then
            A.hull (n * R.params.side) y p.1 Yt p.2 hw else 0) +
          (if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then
            c * blockBondScores (R := R) p.1 V b Y else 0) := by
      funext p
      unfold liveRestriction caseResponse
      by_cases hp : IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2
      · simp [hp, hc]
      · simp [hp]
    rw [e]
    exact (Finset.measurable_sum _ fun y _ => h.response.bounds.hull_borel _ hb y Yt hw).add
      (Measurable.ite hl (((blockBondScores_measurable h V b Y).comp measurable_fst).const_mul c) measurable_const)
  · refine ⟨∑ y ∈ sitesInBlocks R.params.side {Y}, (|A.cold (n * R.params.side) y (trivialField _) hw| +
      (|A.responseParams.C₀| + 1) * |weightNorm R.params.side R.depth hw|) + |c| * 16,
      fun W Yt ωt bad b hl => ?_⟩
    show |∑ y ∈ sitesInBlocks R.params.side {Y}, A.hull (n * R.params.side) y W Yt ωt hw +
      c * blockBondScores (R := R) W V b Y| ≤ _
    have hE := one_le_exp_score h ωt
    have h1 : |∑ y ∈ sitesInBlocks R.params.side {Y}, A.hull (n * R.params.side) y W Yt ωt hw| ≤
        (∑ y ∈ sitesInBlocks R.params.side {Y}, (|A.cold (n * R.params.side) y (trivialField _) hw| +
          (|A.responseParams.C₀| + 1) * |weightNorm R.params.side R.depth hw|)) *
          Real.exp (∑ z : Yt, A.score (ωt z)) := by
      rw [Finset.sum_mul]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => hull_abs_le h hb y W Yt ωt hl hw)
    have h2 : |c * blockBondScores (R := R) W V b Y| ≤ |c| * 16 * Real.exp (∑ z : Yt, A.score (ωt z)) := by
      rw [abs_mul]
      calc _ ≤ |c| * 16 := mul_le_mul_of_nonneg_left (blockBondScores_abs_le h W V b Y) (abs_nonneg _)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hE
    rw [add_mul]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
open Classical in
private def markSummed (H : CaseFunction R n) (V : TorusField n) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : ℝ :=
  if IsHullState R.params (clusterRange R.coupling) p.1 Yt then
    R.labelWeight (n * R.params.side) p.1 Yt p.2 * stepTransitionDensity R.params R.coupling p.1 b V *
      liveRestriction H Yt ∅ b p else 0
private theorem sum_weightedCase_eq_markSummed (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) {H : CaseFunction R n}
    (hI : ∀ W Yt ω (bad bad' : Finset (TorusBond (n * R.params.side))) b, H W Yt ω bad b = H W Yt ω bad' b)
    (C : Finset (TorusSite n)) (V : TorusField n) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) :
    ∑ bad ∈ (markedBonds R C).powerset, weightedCase C V H bad Yt b p = markSummed H V Yt b p := by
  classical
  have hl : ∀ bad, liveRestriction H Yt bad b p = liveRestriction H Yt ∅ b p := fun bad => by
    unfold liveRestriction
    rw [hI p.1 Yt p.2 bad ∅ b]
  unfold markSummed
  by_cases hh : IsHullState R.params (clusterRange R.coupling) p.1 Yt
  · rw [if_pos hh]
    have e : ∀ bad, weightedCase C V H bad Yt b p =
        R.labelWeight (n * R.params.side) p.1 Yt p.2 * stepTransitionDensity R.params R.coupling p.1 b V *
          liveRestriction H Yt ∅ b p * markProduct R C V p.1 bad := fun bad => by
      unfold weightedCase configurationWeight
      rw [if_pos (show IsHullState R.params R.range p.1 Yt from hh),
        ENNReal.toReal_ofReal (stepWeight_nonneg h hn p.1 p.2 hh), stepWeight_eq_mul, hl bad]
      ring
    simp_rw [e]
    rw [← Finset.mul_sum, sum_markProduct, mul_one]
  · rw [if_neg hh]
    refine Finset.sum_eq_zero fun bad _ => ?_
    unfold weightedCase configurationWeight
    rw [if_neg (show ¬ IsHullState R.params R.range p.1 Yt from hh)]
    simp
private theorem markSummed_integrable (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) {H : CaseFunction R n}
    (hT : IsTame A H)
    (hI : ∀ W Yt ω (bad bad' : Finset (TorusBond (n * R.params.side))) b, H W Yt ω bad b = H W Yt ω bad' b)
    (C : Finset (TorusSite n)) (V : TorusField n) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    Integrable (markSummed H V Yt b) ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) := by
  have hi := integrable_finsetSum (μ := (fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ))
    (markedBonds R C).powerset (f := fun bad p => weightedCase C V H bad Yt b p)
    fun bad _ => weightedCase_integrable h hn hT
  exact hi.congr (ae_of_all _ fun p => sum_weightedCase_eq_markSummed h hn hI C V Yt b p)
private theorem sum_integral_weightedCase (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) {H : CaseFunction R n}
    (hT : IsTame A H)
    (hI : ∀ W Yt ω (bad bad' : Finset (TorusBond (n * R.params.side))) b, H W Yt ω bad b = H W Yt ω bad' b)
    (C : Finset (TorusSite n)) (V : TorusField n) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    ∑ bad ∈ (markedBonds R C).powerset,
      ∫ p, weightedCase C V H bad Yt b p
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) =
      ∫ p, markSummed H V Yt b p ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) := by
  rw [← integral_finsetSum _ fun bad _ => weightedCase_integrable h hn hT]
  exact integral_congr_ae (ae_of_all _ fun p => sum_weightedCase_eq_markSummed h hn hI C V Yt b p)
private theorem sum_integral_markSummed (h : LevelInputs R A) (hn : R.params.n₀ ≤ n)
    {rO : ColdResponse R.params.side R.depth} (tie : CarriesResponse R A rO)
    (V : TorusField n) (Y : TorusSite n) (hw : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (W : TorusField (n * R.params.side)) :
    ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
      ∫ ω, markSummed (caseResponse A V Y hw) V Yt b (W, ω) ∂(Measure.pi fun _ : Yt => R.labels.μ) =
    R.functional (n * R.params.side) W * ∑ b : BaseChoice R.params.side n,
      stepTransitionDensity R.params R.coupling W b V *
      (∑ z ∈ sitesInBlocks R.params.side {Y}, rO (n * R.params.side) z W hw +
        R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y hw *
          blockBondScores (R := R) W V b Y) := by
  classical
  have hb := isBlockTorusSide_mul h hn
  have hval : ∀ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
      ∀ b : BaseChoice R.params.side n,
      ∫ ω, markSummed (caseResponse A V Y hw) V Yt b (W, ω) ∂(Measure.pi fun _ : Yt => R.labels.μ) =
      stepTransitionDensity R.params R.coupling W b V * (∑ z ∈ sitesInBlocks R.params.side {Y},
          ∫ ω, A.hull (n * R.params.side) z W Yt ω hw * R.labelWeight (n * R.params.side) W Yt ω
            ∂(Measure.pi fun _ : Yt => R.labels.μ) +
        R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y hw *
          blockBondScores (R := R) W V b Y *
          ∫ ω, R.labelWeight (n * R.params.side) W Yt ω ∂(Measure.pi fun _ : Yt => R.labels.μ)) := by
    intro Yt hY b
    have hh := (Finset.mem_filter.mp hY).2
    have e : ∀ ω, markSummed (caseResponse A V Y hw) V Yt b (W, ω) = stepTransitionDensity R.params R.coupling W b V *
        (∑ z ∈ sitesInBlocks R.params.side {Y},
            A.hull (n * R.params.side) z W Yt ω hw * R.labelWeight (n * R.params.side) W Yt ω +
          R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y hw *
            blockBondScores (R := R) W V b Y * R.labelWeight (n * R.params.side) W Yt ω) := fun ω => by
      unfold markSummed
      rw [if_pos (show IsHullState R.params (clusterRange R.coupling) (W, ω).1 Yt from hh)]
      by_cases hl : IsLiveState R.params R.coupling R.labelWeight W Yt ω
      · have e2 : liveRestriction (caseResponse A V Y hw) Yt ∅ b (W, ω) =
            ∑ z ∈ sitesInBlocks R.params.side {Y}, A.hull (n * R.params.side) z W Yt ω hw +
            R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y hw *
              blockBondScores (R := R) W V b Y := by
          unfold liveRestriction
          rw [if_pos (show IsLiveState R.params R.coupling R.labelWeight (W, ω).1 Yt (W, ω).2 from hl)]
          rfl
        rw [e2, ← Finset.sum_mul]
        show R.labelWeight (n * R.params.side) W Yt ω * stepTransitionDensity R.params R.coupling W b V * _ = _
        ring
      · have h0 : R.labelWeight (n * R.params.side) W Yt ω = 0 :=
          le_antisymm (not_lt.mp fun hp => hl ⟨hh, hp⟩) (h.wellPosed.hasExpansions.2.nonneg _ hb W Yt ω hh)
        show R.labelWeight (n * R.params.side) W Yt ω * stepTransitionDensity R.params R.coupling W b V * _ = _
        rw [h0]
        simp
    rw [integral_congr_ae (ae_of_all _ e), integral_const_mul,
      integral_add (integrable_finsetSum _ fun z _ => hull_mul_labelWeight_integrable h hb hh z hw)
        ((labelWeight_integrable h hb hh).const_mul _),
      integral_finsetSum _ (fun z _ => hull_mul_labelWeight_integrable h hb hh z hw), integral_const_mul]
  have hoff : ∀ Yt ∉ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
      ∀ b : BaseChoice R.params.side n,
      ∫ ω, markSummed (caseResponse A V Y hw) V Yt b (W, ω) ∂(Measure.pi fun _ : Yt => R.labels.μ) = 0 := by
    intro Yt hY b
    have hh : ¬ IsHullState R.params (clusterRange R.coupling) W Yt :=
      fun x => hY (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x⟩)
    have e : ∀ ω, markSummed (caseResponse A V Y hw) V Yt b (W, ω) = 0 := fun ω => by
      unfold markSummed
      rw [if_neg (show ¬ IsHullState R.params (clusterRange R.coupling) (W, ω).1 Yt from hh)]
    simp [e]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W)))
    (fun Yt _ hY => Finset.sum_eq_zero fun b _ => hoff Yt hY b)]
  rw [Finset.sum_congr rfl fun Yt hY => Finset.sum_congr rfl fun b _ => hval Yt hY b, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum, sum_integral_labelWeight h hb W]
  have e3 : ∀ z ∈ sitesInBlocks R.params.side {Y},
      (∑ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
      ∫ ω, A.hull (n * R.params.side) z W Yt ω hw * R.labelWeight (n * R.params.side) W Yt ω
        ∂(Measure.pi fun _ : Yt => R.labels.μ)) =
      R.functional (n * R.params.side) W * rO (n * R.params.side) z W hw := fun z _ => (tie _ hb z W hw).symm
  rw [Finset.sum_congr rfl e3, ← Finset.mul_sum]
  ring
private theorem totalCaseIntegral_caseResponse (h : LevelInputs R A) (hn : R.params.n₀ ≤ n)
    {rO : ColdResponse R.params.side R.depth} (tie : CarriesResponse R A rO)
    (C : Finset (TorusSite n)) (V : TorusField n) (Y : TorusSite n)
    (hw : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    totalCaseIntegral C V (caseResponse A V Y hw) = ∫ W, R.functional (n * R.params.side) W *
      ∑ b : BaseChoice R.params.side n, stepTransitionDensity R.params R.coupling W b V *
      (∑ z ∈ sitesInBlocks R.params.side {Y}, rO (n * R.params.side) z W hw +
        R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y hw *
          blockBondScores (R := R) W V b Y) ∂(fieldHaar (n * R.params.side)) := by
  have hT := isTame_caseResponse h hn V Y hw
  have hI : ∀ W Yt ω (bad bad' : Finset (TorusBond (n * R.params.side))) b,
      caseResponse A V Y hw W Yt ω bad b = caseResponse A V Y hw W Yt ω bad' b := fun _ _ _ _ _ _ => rfl
  have hfi := fun (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) =>
    markSummed_integrable h hn hT hI C V Yt b
  unfold totalCaseIntegral
  rw [Finset.sum_comm]
  calc _ = ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n, ∫ W, ∫ ω,
        markSummed (caseResponse A V Y hw) V Yt b (W, ω) ∂(Measure.pi fun _ : Yt => R.labels.μ)
          ∂(fieldHaar (n * R.params.side)) := by
        refine Finset.sum_congr rfl fun Yt _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [sum_integral_weightedCase h hn hT hI C V Yt b, integral_prod _ (hfi Yt b)]
    _ = ∫ W, ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n, ∫ ω,
        markSummed (caseResponse A V Y hw) V Yt b (W, ω) ∂(Measure.pi fun _ : Yt => R.labels.μ)
          ∂(fieldHaar (n * R.params.side)) := by
        rw [integral_finsetSum _ fun Yt _ => integrable_finsetSum _ fun b _ => (hfi Yt b).integral_prod_left]
        refine Finset.sum_congr rfl fun Yt _ => ?_
        rw [integral_finsetSum _ fun b _ => (hfi Yt b).integral_prod_left]
    _ = _ := integral_congr_ae (ae_of_all _ fun W => sum_integral_markSummed h hn tie V Y hw W)
private theorem coldStep_eq (h : LevelInputs R A) (hn : R.params.n₀ ≤ n) {rO : ColdResponse R.params.side R.depth}
    (tie : CarriesResponse R A rO) (V : TorusField n) (Y : TorusSite n)
    (hw : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    A.coldStep n Y V hw = stepColdResponse R.params R.coupling A.coeff R.depth R.functional rO n Y V hw := by
  have hT := isTame_caseResponse h hn V Y hw
  have e : coarseStateWeight R ∅ V (emptyCoarseState R) = kernelImage R.params R.coupling R.functional n V :=
    (h.inputs.coldState R h.wellPosed n hn).1 V (emptyCoarseState R).2
  show caseMean R ∅ V (emptyCoarseState R) (caseResponse A V Y hw) = _
  unfold caseMean
  rw [caseIntegral_empty h hn hT, totalCaseIntegral_caseResponse h hn tie ∅ V Y hw, e]
  rfl
end Value
section Fine
private theorem directions_eq_of_parity : ∀ μ ν μ' ν' : Fin 4, μ < ν → μ' < ν' →
    (∀ a : Fin 4, ((if a = μ then 1 else 0) + (if a = ν then 1 else 0)) % 2 =
      ((if a = μ' then 1 else 0) + (if a = ν' then 1 else 0)) % 2) → μ = μ' ∧ ν = ν' := by
  decide
private theorem barycenterCoord_injective {m : ℕ} [NeZero m] (p p' : OrientedPlaquette m)
    (e : barycenterCoord p.1 = barycenterCoord p'.1) : p = p' := by
  obtain ⟨⟨z, μ, ν⟩, hp⟩ := p
  obtain ⟨⟨z', μ', ν'⟩, hp'⟩ := p'
  have key : ∀ a : Fin 4, 2 * (z a).val + (if a = μ then 1 else 0) + (if a = ν then 1 else 0) =
      2 * (z' a).val + (if a = μ' then 1 else 0) + (if a = ν' then 1 else 0) := fun a => by
    have h := congrFun e a
    simp only [barycenterCoord] at h
    have h2 : ((2 * (z a).val + (if a = μ then 1 else 0) + (if a = ν then 1 else 0) : ℕ) : ℝ) =
        ((2 * (z' a).val + (if a = μ' then 1 else 0) + (if a = ν' then 1 else 0) : ℕ) : ℝ) := by
      push_cast
      split_ifs at h ⊢ <;> linarith
    exact_mod_cast h2
  obtain ⟨rfl, rfl⟩ := directions_eq_of_parity μ ν μ' ν' hp hp' fun a => by
    have := key a
    omega
  have hz : z = z' := funext fun a => ZMod.val_injective m (by
    have := key a
    omega)
  subst hz
  rfl
abbrev _root_.YangMills.SharedProofs.p53598 := @barycenterCoord_injective
open Classical in
private def fineFunctionOf {m : ℕ} (h : PlaquetteWeight m) : FinePlaquetteFunction := fun b =>
  if hb : ∃ p : OrientedPlaquette m, barycenterCoord p.1 = b then h hb.choose.1 else 0
private theorem fineWeight_fineFunctionOf {m : ℕ} [NeZero m] (h : PlaquetteWeight m) (p : TorusPlaquette m)
    (hp : p.2.1 < p.2.2) : fineWeight (fineFunctionOf h) m p = h p := by
  classical
  have hb : ∃ q : OrientedPlaquette m, barycenterCoord q.1 = barycenterCoord p := ⟨⟨p, hp⟩, rfl⟩
  show fineFunctionOf h (barycenterCoord p) = h p
  unfold fineFunctionOf
  rw [dif_pos hb]
  have := barycenterCoord_injective hb.choose ⟨p, hp⟩ hb.choose_spec
  rw [this]
abbrev _root_.YangMills.DeltaSharedProofs.p501682 := @fineWeight_fineFunctionOf
private theorem siteResponse_congr {m : ℕ} [NeZero m] (z : TorusSite m) (W : TorusField m) (h h' : PlaquetteWeight m)
    (e : ∀ p : TorusPlaquette m, p.2.1 < p.2.2 → h p = h' p) : siteResponse z W h = siteResponse z W h' := by
  unfold siteResponse
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [e p (Finset.mem_filter.mp hp).2.1]
private theorem blockMean_congr {L : ℕ} [NeZero L] {m : ℕ} [NeZero m] (z : TorusSite m) (h h' : PlaquetteWeight m)
    (e : ∀ p : TorusPlaquette m, p.2.1 < p.2.2 → h p = h' p) : blockMean L 0 m z h = blockMean L 0 m z h' := by
  show (1 / 24) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity z p * h p =
    (1 / 24) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity z p * h' p
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [e p (Finset.mem_filter.mp hp).2.1]
private theorem weightLipschitz_congr {L t m : ℕ} (h h' : PlaquetteWeight m)
    (e : ∀ p : TorusPlaquette m, p.2.1 < p.2.2 → h p = h' p) :
    weightLipschitz L t h = weightLipschitz L t h' := by
  unfold weightLipschitz
  congr 1
  funext pp
  rw [e _ pp.1.2, e _ pp.2.2]
end Fine
section Levels
variable {ℓ : TorusLumps.StepParameters}
private theorem carriesResponse_next (c : ChainStage ℓ) (hf : CoarseLabelFacts c.toStepSetup) (x'' : ℝ)
    (f' : LocalDensity)
    (φ' : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) →
      (Y → CoarseLabel c.labels.Ω ℓ.side) → ℝ)
    (A : ResponseSetup c.toStepSetup) (h : LevelInputs c.toStepSetup A) (rO : ColdResponse ℓ.side c.depth)
    (tie : CarriesResponse c.toStepSetup A rO)
    (B : ResponseSetup (c.next hf x'' f' φ').toStepSetup) (hQ : B.hull = A.hullStep) :
    CarriesResponse (c.next hf x'' f' φ').toStepSetup B
      (stepColdResponse ℓ c.coupling A.coeff c.depth c.functional rO) := by
  classical
  obtain ⟨K', al', s', P', Q', Ra', Rb'⟩ := B
  dsimp only at hQ
  subst hQ
  intro m _ hm Y V hw
  have hLpos : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn : ℓ.n₀ ≤ m := le_trans (Nat.le_mul_of_pos_left _ hLpos) hm.2
  have hT := isTame_caseResponse (R := c.toStepSetup) (A := A) h hn V Y hw
  have hm' : IsBlockTorusSide c.toStepSetup.params m := hm
  have hrhs : (∑ Y' ∈ Finset.univ.filter (IsHullState ℓ (clusterRange c.nextCoupling) V),
      ∫ ω, A.hullStep m Y V Y' ω hw * coarseWeightExpansion c.toStepSetup m V Y' ω
        ∂(Measure.pi fun _ : Y' => coarseLabelMeasure c.labels.μ ℓ.side)) =
      totalCaseIntegral (hotCoreSites c.toStepSetup V) V (caseResponse A V Y hw) := by
    rw [← sum_integral_caseMean h hn hT hm']
    refine Finset.sum_congr rfl fun Y' _ => integral_congr_ae (ae_of_all _ fun ω => ?_)
    have e : coarseWeightExpansion c.toStepSetup m V Y' ω =
        coarseStateWeight c.toStepSetup (hotCoreSites c.toStepSetup V) V ⟨Y', ω⟩ := by
      simp [coarseWeightExpansion, NeZero.ne m]
    exact congrArg (fun u => caseMean c.toStepSetup (hotCoreSites c.toStepSetup V) V ⟨Y', ω⟩
      (caseResponse A V Y hw) * u) e
  show kernelImage ℓ c.coupling c.functional m V *
      stepColdResponse ℓ c.coupling A.coeff c.depth c.functional rO m Y V hw =
    ∑ Y' ∈ Finset.univ.filter (IsHullState ℓ (clusterRange c.nextCoupling) V),
      ∫ ω, A.hullStep m Y V Y' ω hw * coarseWeightExpansion c.toStepSetup m V Y' ω
        ∂(Measure.pi fun _ : Y' => coarseLabelMeasure c.labels.μ ℓ.side)
  rw [hrhs]
  by_cases hD : kernelImage ℓ c.coupling c.functional m V = 0
  · rw [hD, zero_mul, totalCaseIntegral_eq_zero h hn hT hD]
  · rw [totalCaseIntegral_caseResponse h hn tie _ V Y hw]
    show kernelImage ℓ c.coupling c.functional m V * (_ / kernelImage ℓ c.coupling c.functional m V) = _
    rw [mul_div_cancel₀ _ hD]
    rfl
private def castColdResponse {L t t' : ℕ} (e : t = t') (rO : ColdResponse L t) : ColdResponse L t' := e ▸ rO
private def Carries (c : ChainStage ℓ) (A : ResponseSetup c.toStepSetup) (t : ℕ) (rO : ColdResponse ℓ.side t) : Prop :=
  ∃ e : t = c.depth, CarriesResponse c.toStepSetup A (castColdResponse e rO)
private def ColdAgrees (c : ChainStage ℓ) (A : ResponseSetup c.toStepSetup) (t : ℕ) (rO : ColdResponse ℓ.side t) :
    Prop :=
  ∃ e : t = c.depth, ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n)
    (hw : PlaquetteWeight (fineSide ℓ.side c.depth n)),
    A.cold n y W hw = castColdResponse e rO n y W hw
private theorem carries_next (c : ChainStage ℓ) (hf : CoarseLabelFacts c.toStepSetup) (x'' : ℝ) (f' : LocalDensity)
    (φ' : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) →
      (Y → CoarseLabel c.labels.Ω ℓ.side) → ℝ)
    (A : ResponseSetup c.toStepSetup) (B : ResponseSetup (c.next hf x'' f' φ').toStepSetup)
    (hQ : B.hull = A.hullStep) (hP : B.cold = A.coldStep)
    (t : ℕ) (rO : ColdResponse ℓ.side t) (ht : Carries c A t rO) (h : LevelInputs c.toStepSetup A) :
    Carries (c.next hf x'' f' φ') B (t + 1) (stepColdResponse ℓ c.coupling A.coeff t c.functional rO) ∧
      ColdAgrees (c.next hf x'' f' φ') B (t + 1) (stepColdResponse ℓ c.coupling A.coeff t c.functional rO) := by
  obtain ⟨e, tie⟩ := ht
  subst e
  refine ⟨⟨rfl, carriesResponse_next c hf x'' f' φ' A h rO tie B hQ⟩, ⟨rfl, fun n _ hn Y V hw => ?_⟩⟩
  rw [hP]
  exact coldStep_eq h hn tie V Y hw
private theorem carries_zero (c : ChainStage ℓ) (e : c.depth = 0) (A : ResponseSetup c.toStepSetup)
    (h : LevelInputs c.toStepSetup A)
    (hQ : ∀ (n : ℕ) [NeZero n] (z : TorusSite n) (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → c.labels.Ω)
      (f : FinePlaquetteFunction), A.hull n z W Y ω (fineWeight f _) = siteResponse z W (fineWeight f n)) :
    Carries c A 0 (wilsonColdResponse ℓ.side) := by
  classical
  obtain ⟨t, x, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩ := c
  dsimp only at e
  subst e
  refine ⟨rfl, ?_⟩
  intro m _ hm y W hw
  have hrow := h.response.bounds
  have e₁ : ∀ Yt ∈ Finset.univ.filter (IsHullState ℓ (clusterRange x) W),
      ∫ ω, A.hull m y W Yt ω hw * Dq m W Yt ω ∂(Measure.pi fun _ : Yt => Λ.μ) =
        siteResponse y W hw * ∫ ω, Dq m W Yt ω ∂(Measure.pi fun _ : Yt => Λ.μ) := fun Yt hY => by
    have hh : IsHullState ℓ (clusterRange x) W Yt := (Finset.mem_filter.mp hY).2
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    have hnn : 0 ≤ Dq m W Yt ω := h.wellPosed.hasExpansions.2.nonneg m hm W Yt ω hh
    rcases hnn.eq_or_lt with h0 | hpos
    · simp only [← h0, mul_zero]
    · have hlive : IsLiveState ℓ x Dq W Yt ω := ⟨hh, hpos⟩
      have r₁ : A.hull m y W Yt ω hw = A.hull m y W Yt ω (fineWeight (fineFunctionOf hw) _) :=
        hrow.hull_reads m hm y W Yt ω hlive _ _ fun q hq => (fineWeight_fineFunctionOf hw q hq.1).symm
      have r₂ := hQ m y W Yt ω (fineFunctionOf hw)
      have r₃ : siteResponse y W (fineWeight (fineFunctionOf hw) m) = siteResponse y W hw :=
        siteResponse_congr y W _ _ fun q hq => fineWeight_fineFunctionOf hw q hq
      exact congrArg (fun u => u * Dq m W Yt ω) (r₁.trans (r₂.trans r₃))
  show D m W * siteResponse y W hw = _
  rw [Finset.sum_congr rfl e₁, ← Finset.mul_sum, sum_integral_labelWeight h hm W, mul_comm]
private theorem coldResponseBounds_of_agrees (c : ChainStage ℓ) (A : ResponseSetup c.toStepSetup) (t : ℕ)
    (rO : ColdResponse ℓ.side t) (ht : ColdAgrees c A t rO) (K : ResponseParameters) (x al : ℝ)
    (hK : A.responseParams = K) (hx : c.coupling = x) (hal : A.coeff = al) (hr : A.IsAdmissible) :
    ∃ Ra Rb : LocalDensity, ColdResponseBounds ℓ K t x al rO Ra Rb := by
  obtain ⟨e, hP⟩ := ht
  subst e
  subst hK
  subst hx
  subst hal
  have hP' : ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n)
      (hw : PlaquetteWeight (fineSide ℓ.side c.depth n)), A.cold n y W hw = rO n y W hw := hP
  have row := hr.bounds
  have hat : ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n)
      (hw : PlaquetteWeight (fineSide ℓ.side c.depth n)),
      centeredResponse rO n y W hw = centeredResponse A.cold n y W hw := fun n _ hn y W hw => by
    unfold centeredResponse
    rw [hP' n hn, hP' n hn]
  have rem : ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (hw : PlaquetteWeight (fineSide ℓ.side c.depth n)),
      responseRemainder rO n y hw = responseRemainder A.cold n y hw := fun n _ hn y hw => by
    funext W
    unfold responseRemainder
    rw [hP' n hn, hP' n hn]
  have hrem : ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n)
      (hw : PlaquetteWeight (fineSide ℓ.side c.depth n)),
      centeredRemainder rO n y hw = centeredRemainder A.cold n y hw := fun n _ hn y hw => by
    funext W
    unfold centeredRemainder
    rw [rem n hn]
  refine ⟨A.siteRemainder, A.totalRemainder, ?_⟩
  exact
    { share_site := fun n _ hn y W hW => by
        rw [hat n hn]
        exact row.share_site n hn y W hW
      share_total := fun n _ hn W hW => by
        simp_rw [hat n hn]
        exact row.share_total n hn W hW
      site_family := row.site_family
      total_family := row.total_family
      remainder :=
        { smooth := fun n _ hn y W hW hw => by
            rw [rem n hn]
            exact row.remainder_smooth n hn y W hW hw
          decay := fun n _ hn y W hW hw k c X h1 h2 hX => by
            rw [rem n hn]
            exact row.remainder_decay n hn y W hW hw k c X h1 h2 hX
          compare := fun n _ hn y W W' m hm hW hW' hA hw k b X hk hb hX => by
            rw [hrem n hn]
            exact row.remainder_local n hn y W W' m hm hW hW' hA hw k b X hk hb hX } }
private theorem coldResponseBounds_zero (c : ChainStage ℓ) (e : c.depth = 0) (A : ResponseSetup c.toStepSetup)
    (hP : ∀ (n : ℕ) [NeZero n] (z : TorusSite n) (W : TorusField n) (f : FinePlaquetteFunction),
      A.cold n z W (fineWeight f _) = siteResponse z W (fineWeight f n))
    (K : ResponseParameters) (x al : ℝ) (hK : A.responseParams = K) (hx : c.coupling = x) (hal : A.coeff = al)
    (hr : A.IsAdmissible) :
    ∃ Ra Rb : LocalDensity, ColdResponseBounds ℓ K 0 x al (wilsonColdResponse ℓ.side) Ra Rb := by
  obtain ⟨t, x₀, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩ := c
  dsimp only at e hx
  subst e
  subst hK
  subst hx
  subst hal
  have row := hr.bounds
  have hw₁ : ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (W : TorusField n),
      wilsonColdResponse ℓ.side n y W (constOneWeight _) = A.cold n y W (constOneWeight _) :=
    fun n _ y W => (hP n y W fun _ => 1).symm
  have hat₁ : ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (W : TorusField n),
      centeredResponse (wilsonColdResponse ℓ.side) n y W (constOneWeight _) =
        centeredResponse A.cold n y W (constOneWeight _) := fun n _ y W => by
    unfold centeredResponse
    rw [hw₁, hw₁]
  have rem : ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (hw : PlaquetteWeight (fineSide ℓ.side 0 n)),
      responseRemainder (wilsonColdResponse ℓ.side) n y hw =
        responseRemainder A.cold n y (fineWeight (fineFunctionOf hw) _) := fun n _ y hw => by
    funext W
    unfold responseRemainder
    rw [hw₁, hP n y W (fineFunctionOf hw)]
    have r₁ : siteResponse y W (fineWeight (fineFunctionOf hw) n) = siteResponse y W hw :=
      siteResponse_congr y W _ _ fun q hq => fineWeight_fineFunctionOf hw q hq
    have r₂ : blockMean ℓ.side 0 n y (fineWeight (fineFunctionOf hw) n) = blockMean ℓ.side 0 n y hw :=
      blockMean_congr y _ _ fun q hq => fineWeight_fineFunctionOf hw q hq
    rw [r₁]
    exact congrArg (fun u => wilsonColdResponse ℓ.side n y W hw - u * A.cold n y W (constOneWeight _)) r₂.symm
  have hrem : ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (hw : PlaquetteWeight (fineSide ℓ.side 0 n)),
      centeredRemainder (wilsonColdResponse ℓ.side) n y hw =
        centeredRemainder A.cold n y (fineWeight (fineFunctionOf hw) _) := fun n _ y hw => by
    funext W
    unfold centeredRemainder
    rw [rem n y hw]
  have hlip : ∀ (n : ℕ) [NeZero n] (hw : PlaquetteWeight (fineSide ℓ.side 0 n)),
      weightLipschitz ℓ.side 0 (fineWeight (fineFunctionOf hw) n) = weightLipschitz ℓ.side 0 hw := fun n _ hw =>
    weightLipschitz_congr _ _ fun q hq => fineWeight_fineFunctionOf hw q hq
  refine ⟨A.siteRemainder, A.totalRemainder, ?_⟩
  exact
    { share_site := fun n _ hn y W hW => by
        rw [hat₁]
        exact row.share_site n hn y W hW
      share_total := fun n _ hn W hW => by
        simp_rw [hat₁]
        exact row.share_total n hn W hW
      site_family := row.site_family
      total_family := row.total_family
      remainder :=
        { smooth := fun n _ hn y W hW hw => by
            rw [rem n y hw]
            exact row.remainder_smooth n hn y W hW _
          decay := fun n _ hn y W hW hw k c X h1 h2 hX => by
            rw [rem n y hw, ← hlip n hw]
            exact row.remainder_decay n hn y W hW _ k c X h1 h2 hX
          compare := fun n _ hn y W W' m hm hW hW' hA hw k b X hk hb hX => by
            rw [hrem n y hw, ← hlip n hw]
            exact row.remainder_local n hn y W W' m hm hW hW' hA _ k b X hk hb hX } }
variable {Tb : ParameterAssignment} {y β : ℝ}
private theorem tower_carries (inputs : Inputs) {T : StageTower (Tb.stepParameters y)} (S : ScoredStageTower T) (k : ℕ)
    (hS : S.FollowsFlow β k) (hF : ∀ t ≤ k, (T.stage t).toStepSetup.IsWellPosed) (t : ℕ) (ht : t ≤ k) :
    Carries (T.stage t) (S.setup t) t
        (coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) S.coeffs t) ∧
      (T.stage t).functional = chainFunctional (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) t := by
  induction t with
  | zero =>
    refine ⟨?_, hS.startsAtWilson.functional_eq⟩
    have h0 : LevelInputs (T.stage 0).toStepSetup (S.setup 0) := ⟨inputs, hF 0 ht, hS.isAdmissible 0 ht⟩
    exact carries_zero (T.stage 0) hS.startsAtWilson.depth_eq (S.setup 0) h0 fun n _ z W Y ω f => hS.hull_zero n z W Y ω f
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih (Nat.le_of_succ_le ht)
    have hlt : t < k := ht
    have h : LevelInputs (T.stage t).toStepSetup (S.setup t) := ⟨inputs, hF t hlt.le, hS.isAdmissible t hlt.le⟩
    have hx : flowCouplings (Tb.stepParameters y) β t = (T.stage t).coupling :=
      (hS.isFlowStep t hlt.le).coupling_eq.symm
    have hn := (carries_next (T.stage t) (T.labelFacts _ T.two_le_side) (T.couplings t) (T.densities t)
      (T.siteDensities (T.stage t).toStepSetup) (S.setup t) (S.setup (t + 1))
      (hS.hull_succ t hlt) (hS.cold_succ t hlt) t _ h1 h).1
    refine ⟨?_, ?_⟩
    · have e : coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) S.coeffs (t + 1) =
          stepColdResponse (Tb.stepParameters y) (T.stage t).coupling (S.setup t).coeff t (T.stage t).functional
            (coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) S.coeffs t) := by
        rw [← hx, h2]
        rfl
      rw [e]
      exact hn
    · show kernelImage (Tb.stepParameters y) (T.stage t).coupling (T.stage t).functional =
        kernelImage (Tb.stepParameters y) (flowCouplings (Tb.stepParameters y) β t)
          (chainFunctional (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) t)
      rw [← hx, h2]
private theorem tower_coldResponseBounds (inputs : Inputs) {T : StageTower (Tb.stepParameters y)}
    (S : ScoredStageTower T) (k : ℕ) (hS : S.FollowsFlow β k)
    (hF : ∀ t ≤ k, (T.stage t).toStepSetup.IsWellPosed) (t : ℕ) (ht : t + 1 ≤ k) :
    ∃ Ra Rb : LocalDensity, ColdResponseBounds (Tb.stepParameters y) S.params (t + 1)
      (flowCouplings (Tb.stepParameters y) β (t + 1)) (S.coeffs (t + 1))
      (coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) S.coeffs (t + 1)) Ra Rb := by
  have hlt : t < k := ht
  obtain ⟨h1, h2⟩ := tower_carries inputs S k hS hF t hlt.le
  have h : LevelInputs (T.stage t).toStepSetup (S.setup t) := ⟨inputs, hF t hlt.le, hS.isAdmissible t hlt.le⟩
  have hx : flowCouplings (Tb.stepParameters y) β t = (T.stage t).coupling :=
    (hS.isFlowStep t hlt.le).coupling_eq.symm
  have hn := (carries_next (T.stage t) (T.labelFacts _ T.two_le_side) (T.couplings t) (T.densities t)
    (T.siteDensities (T.stage t).toStepSetup) (S.setup t) (S.setup (t + 1))
    (hS.hull_succ t hlt) (hS.cold_succ t hlt) t _ h1 h).2
  have e : coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) S.coeffs (t + 1) =
      stepColdResponse (Tb.stepParameters y) (T.stage t).coupling (S.setup t).coeff t (T.stage t).functional
        (coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) S.coeffs t) := by
    rw [← hx, h2]
    rfl
  rw [e]
  exact coldResponseBounds_of_agrees (T.stage (t + 1)) (S.setup (t + 1)) (t + 1) _ hn S.params _ _ (hS.params_eq (t + 1))
    (hS.isFlowStep (t + 1) ht).coupling_eq rfl (hS.isAdmissible (t + 1) ht)
private theorem isWellPosed_of_onParameters {T : ParameterAssignment} (hT : T.Admissible) {y : ℝ} (hy₀ : T.floorMin ≤ y)
    (hy₁ : 1 ≤ y) {R : StepSetup} (hon : R.OnParameters T y) (hmoved : |R.nextCoupling - R.coupling| ≤ 2 * T.B)
    (hArr : R.IsSymmetricWeight)
    (hF : T.FloorConditions (2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17) 1 R.coupling) : R.IsWellPosed := by apply _root_.YangMills.SharedProofs.p3707 <;> assumption
private theorem flow_hasExpansion {ℓ : TorusLumps.StepParameters} (hret : ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) {K : ℕ}
    (hrun : ∀ j ≤ K, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) :
    ∀ s ≤ K, HasExpansion ℓ s (couplingFlow ℓ β s).1 (couplingFlow ℓ β s).2 ∧
      |(couplingFlow ℓ β (s + 1)).1 - (couplingFlow ℓ β s).1| ≤ 2 * ℓ.B := by
  have step : ∀ s ≤ K, HasExpansion ℓ s (couplingFlow ℓ β s).1 (couplingFlow ℓ β s).2 →
      HasExpansion ℓ (s + 1) (couplingFlow ℓ β (s + 1)).1 (couplingFlow ℓ β (s + 1)).2 ∧
        |(couplingFlow ℓ β (s + 1)).1 - (couplingFlow ℓ β s).1| ≤ 2 * ℓ.B := by
    intro s hs hrow
    obtain ⟨x', ⟨hx', hmv⟩, huniq⟩ := hret s _ _ (hrun s hs) hrow
    have hex : ∃ x'' : ℝ, HasExpansion ℓ (s + 1) x''
        (kernelImage ℓ (couplingFlow ℓ β s).1 (couplingFlow ℓ β s).2) := ⟨x', hx'⟩
    have hnext : (couplingFlow ℓ β (s + 1)).1 = hex.choose := by
      show expansionCoupling ℓ s (couplingFlow ℓ β s).1 (couplingFlow ℓ β s).2 = _
      unfold expansionCoupling
      rw [dif_pos hex]
    have hch := hex.choose_spec
    obtain ⟨-, f'', hc, -⟩ := hch
    have he : hex.choose = x' := huniq _ _ hc
    refine ⟨?_, ?_⟩
    · rw [hnext]
      exact hex.choose_spec
    · rw [hnext, he]
      exact hmv
  intro s
  induction s with
  | zero => exact fun h => ⟨h0, (step 0 h h0).2⟩
  | succ s ih =>
    intro h
    have hs := (ih (by omega)).1
    have h1 := (step s (by omega) hs).1
    exact ⟨h1, (step (s + 1) h h1).2⟩
abbrev _root_.YangMills.SharedProofs.p25177 := @flow_hasExpansion
end Levels
theorem scoredTowerCoeffsAreChain (hc : ConfigurationMassWithFunction) (ho : ConfigurationSupportedOnCoarseHull)
    (hb : ConfigurationWeightMeasurable) (ha : ConfigurationWeightsSum) (hh : CoarseHullIsHullState)
    (hC : coldFieldStateStatement) (hm : ScoredMassStatement) (hs : BondScoreProperties)
    (hd : StepTransitionDensityBounds) (hFl : EventuallyFloorConditions) : scoredTowerCoeffsAreChainStatement := by
  have inputs : Inputs := ⟨hc, ho, hb, ha, hh, hC, hm, hs, hd⟩
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L _ _ Tb _ _ hT _ _ _ _ => ?_⟩
  have hCpos : (0 : ℝ) < 2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 17 := by positivity
  obtain ⟨yF, hyF⟩ := hFl Tb hT _ 1 hCpos one_pos
  refine ⟨max (max Tb.floorMin yF) 1, fun y hy hret hW β k Tw S hS => ?_⟩
  have h₁ : Tb.floorMin ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have h₂ : yF ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have h₃ : (1 : ℝ) ≤ y := le_trans (le_max_right _ _) hy
  have hβ : y ≤ β := by
    have h := (hS.isFlowStep 0 (Nat.zero_le _)).onFamily.le_coupling
    rwa [show (Tw.stage 0).toStepSetup.coupling = β from hS.bottom_coupling] at h
  have hrun : ∀ j ≤ k, (Tb.stepParameters y).y₁ ≤ (couplingFlow (Tb.stepParameters y) β j).1 := fun j hj => by
    have h := (hS.isFlowStep j hj).onFamily.le_coupling
    rw [(hS.isFlowStep j hj).coupling_eq] at h
    exact h
  have hrow := flow_hasExpansion hret (hW β hβ) hrun
  have hF : ∀ t ≤ k, (Tw.stage t).toStepSetup.IsWellPosed := fun t ht => by
    have hst := hS.isFlowStep t ht
    have hon := hst.onFamily
    have hmv : |(Tw.stage t).nextCoupling - (Tw.stage t).coupling| ≤ 2 * Tb.B := by
      have e₁ : (Tw.stage t).nextCoupling = (couplingFlow (Tb.stepParameters y) β (t + 1)).1 := hst.nextCoupling_eq
      have e₂ : (Tw.stage t).coupling = (couplingFlow (Tb.stepParameters y) β t).1 := hst.coupling_eq
      rw [e₁, e₂]
      exact (hrow t ht).2
    have hArr : (Tw.stage t).toStepSetup.IsSymmetricWeight := by
      have h := (hrow t ht).1.1
      have hD : (Tw.stage t).functional = (couplingFlow (Tb.stepParameters y) β t).2 := hst.functional_eq
      show ∀ (m : ℕ) [NeZero m], (Tb.stepParameters y).n₀ ≤ m → Measurable ((Tw.stage t).functional m) ∧
        (∀ W, 0 ≤ (Tw.stage t).functional m W) ∧
        (∀ (g : TorusSite m → BlockAverages.UnitQuaternion) (W : TorusField m),
          (Tw.stage t).functional m (_root_.YangMills.Construction.TorusFields.gaugeTransform g W) = (Tw.stage t).functional m W) ∧
        ∀ (g : TorusIsometry) (W W' : TorusField m), g.Transports W W' →
          (Tw.stage t).functional m W' = (Tw.stage t).functional m W
      rw [hD]
      exact h
    exact isWellPosed_of_onParameters hT h₁ h₃ hon hmv hArr (hyF _ (h₂.trans hon.le_coupling))
  refine ⟨hS.coeff_zero, fun j hj => ?_⟩
  cases j with
  | zero =>
    exact coldResponseBounds_zero (Tw.stage 0) hS.startsAtWilson.depth_eq (S.setup 0) (fun n _ z W f => hS.cold_zero n z W f)
      S.params _ _ (hS.params_eq 0) (hS.isFlowStep 0 hj).coupling_eq rfl (hS.isAdmissible 0 hj)
  | succ t => exact tower_coldResponseBounds inputs S k hS hF t hj
end ScoredTowerChainProof
end YangMills.Construction.ResponseInTheExpansion
end
