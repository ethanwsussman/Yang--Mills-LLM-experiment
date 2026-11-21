import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfFourDensitiesProofForm
import YangMills.Construction.ClusterExpansionOfAStep.FormOfTheShares
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsAreTheGasProof
import YangMills.Construction.ClusterExpansionOfAStep.StateOverAColdFieldProof
import YangMills.Construction.ColdChainAtEveryLevel.FlatTopCostsNothing
import YangMills.Construction.ResponseInTheExpansion.ColdConditionsHaveOneConstant
import YangMills.Construction.ResponseInTheExpansion.ManyLevelsOfSeveralSupportsProof
import YangMills.Construction.ResponseInTheExpansion.MeanOverAStepOfTheStatesProof
import YangMills.Construction.ResponseInTheExpansion.ScoredMassOfAField
import YangMills.Construction.SixteenPointsOnASmallTorus.CentringIsTheSumOfTheShifts
import YangMills.Construction.SixteenPointsOnASmallTorus.ResponsesAreCarriedByAnIsometry
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
open YangMills.Construction.StepSettings YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.StepGas YangMills.Construction.RenormalizationStepParameters YangMills.Construction.WeightedResponses YangMills.Construction.ResponseInTheExpansion YangMills.Construction.ShareFamilies YangMills.Construction.ClusterExpansionOfAStep YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.BlockPlaces YangMills.Construction.StepCosts
namespace CentringProof
section Marks
private theorem marks_add {B : Type} [DecidableEq B] (M : Finset B) (m : B → ℝ) :
    ∑ bad ∈ M.powerset, ∏ b ∈ M, (if b ∈ bad then 1 - m b else m b) = 1 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdGasIdentity.sum_powerset_prod_complement_eq_one <;> assumption
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem mark_bounds (hR : R.IsWellPosed) (V : TorusField n) (W : TorusField (n * R.params.side)) (b : TorusBond (n * R.params.side)) :
    0 ≤ bondMark R V W b ∧ bondMark R V W b ≤ 1 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.bondMark_nonneg_le_one <;> assumption
private theorem marks_nonneg (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (bad : Finset (TorusBond (n * R.params.side))) : 0 ≤ markProduct R C V W bad := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.markProduct_nonneg <;> assumption
private theorem marks_le_one (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (bad : Finset (TorusBond (n * R.params.side))) : markProduct R C V W bad ≤ 1 := by
  classical
  unfold markProduct
  refine Finset.prod_le_one (fun b _ => ?_) fun b _ => ?_
  · have := mark_bounds hR V W b
    split_ifs
    · linarith [this.2]
    · exact this.1
  · have := mark_bounds hR V W b
    split_ifs
    · linarith [this.1]
    · exact this.2
abbrev _root_.YangMills.SharedProofs.p3258 := @marks_le_one
private theorem marks_sum (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side)) :
    ∑ bad ∈ (markedBonds R C).powerset, markProduct R C V W bad = 1 := by
  classical
  have := marks_add (markedBonds R C) (fun b => bondMark R V W b)
  unfold markProduct
  convert this using 2
abbrev _root_.YangMills.SharedProofs.p20431 := @marks_sum
private theorem stepWeight_eq (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    stepWeight R C V W Yt ωt bad b =
      R.labelWeight (n * R.params.side) W Yt ωt * stepTransitionDensity R.params R.coupling W b V * markProduct R C V W bad := by apply _root_.YangMills.SharedProofs.p15525 <;> assumption
end Marks
section States
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem measurable_fieldWithStoredLinks (q : CoarseState R n) : Measurable q.fieldWithStoredLinks := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fieldWithStoredLinks <;> assumption
private theorem measurable_fillLabels (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable (q.fillLabels Yt) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_fillLabels <;> assumption
private theorem state_const (q : CoarseState R n) (C : Finset (TorusSite n)) (Yt : Finset (TorusSite (n * R.params.side)))
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) {W W' : TorusField (n * R.params.side)}
    {ν ν' : q.unlabelled Yt → R.labels.Ω}
    (h : coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) :
    coarseStateOf R C (q.fieldWithStoredLinks W') Yt (q.fillLabels Yt ν') bad b = q := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.coarseStateOf_fill <;> assumption
end States
private structure Inputs : Prop where
  carry : ConfigurationMassWithFunction
  one : ConfigurationSupportedOnCoarseHull
  borel : ConfigurationWeightMeasurable
  addUp : ConfigurationWeightsSum
  hulls : CoarseHullIsHullState
  cold : coldFieldStateStatement
  scored : ScoredMassStatement
  score : BondScoreProperties
  density : StepTransitionDensityBounds
private structure Holds (R : StepSetup) (A : ResponseSetup R) : Prop where
  inputs : Inputs
  forms : R.IsWellPosed
  resp : A.IsAdmissible
private theorem integrable_of_parts {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} (hf : Measurable f)
    (hp : ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≠ ⊤) (hm : ∫⁻ a, ENNReal.ofReal (-f a) ∂μ ≠ ⊤) : Integrable f μ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have e : ∫⁻ a, ‖f a‖ₑ ∂μ = ∫⁻ a, ENNReal.ofReal (f a) ∂μ + ∫⁻ a, ENNReal.ofReal (-f a) ∂μ := by
    rw [← lintegral_add_left hf.ennreal_ofReal]
    refine lintegral_congr fun a => ?_
    rw [Real.enorm_eq_ofReal_abs]
    rcases le_total 0 (f a) with h | h
    · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (by linarith : -f a ≤ 0), add_zero]
    · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
  show ∫⁻ a, ‖f a‖ₑ ∂μ < ⊤
  rw [e]
  exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hp, lt_top_iff_ne_top.mpr hm⟩
abbrev _root_.YangMills.SharedProofs.p18814 := @integrable_of_parts
section Majorant
variable {R : StepSetup} (A : ResponseSetup R)
open Classical in
private def scored (m : ℕ) [NeZero m] (Yt : Finset (TorusSite m)) (p : TorusField m × (Yt → R.labels.Ω)) : ℝ :=
  (if IsHullState R.params (clusterRange R.coupling) p.1 Yt then R.labelWeight m p.1 Yt p.2 else 0) *
    Real.exp (∑ y : Yt, A.score (p.2 y))
variable {A} {m : ℕ} [NeZero m]
private theorem scored_measurable (h : Holds R A) (hb : IsBlockTorusSide R.params m) (Yt : Finset (TorusSite m)) :
    Measurable (scored A m Yt) := by
  classical
  refine Measurable.mul (h.forms.hasExpansions.2.borel m hb Yt).1 ?_
  exact (Finset.measurable_sum _ fun y _ => h.resp.price.borel.comp
    ((measurable_pi_apply y).comp measurable_snd)).exp
private theorem scored_nonneg (h : Holds R A) (hb : IsBlockTorusSide R.params m) (Yt : Finset (TorusSite m))
    (p : TorusField m × (Yt → R.labels.Ω)) : 0 ≤ scored A m Yt p := by
  classical
  unfold scored
  refine mul_nonneg ?_ (Real.exp_pos _).le
  split_ifs with hh
  · exact h.forms.hasExpansions.2.nonneg m hb p.1 Yt p.2 hh
  · exact le_rfl
private def massBound (R : StepSetup) (m : ℕ) [NeZero m] : ℝ :=
  R.functional m (trivialField m) * 2 ^ Fintype.card (TorusSite m) * Real.exp (2 * R.params.E * Fintype.card (TorusSite m))
private theorem scored_fibre (h : Holds R A) (hb : IsBlockTorusSide R.params m) (Yt : Finset (TorusSite m)) (W : TorusField m) :
    ∫⁻ ω, ENNReal.ofReal (scored A m Yt (W, ω)) ∂(Measure.pi fun _ : Yt => R.labels.μ) ≤ ENNReal.ofReal (massBound R m) := by
  classical
  by_cases hh : IsHullState R.params (clusterRange R.coupling) W Yt
  · have hs := h.inputs.scored R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity A.score h.forms.admissible h.forms.admissible.E_ge h.forms.coupling_pos
      h.forms.range_ge_base h.forms.hasExpansions.1 h.forms.hasExpansions.2 h.resp.price m hb W
    refine le_trans (le_of_eq ?_) (le_trans (Finset.single_le_sum (f := fun Y : Finset (TorusSite m) =>
      ∫⁻ ω, ENNReal.ofReal (R.labelWeight m W Y ω * Real.exp (∑ y : Y, A.score (ω y))) ∂(Measure.pi fun _ : Y => R.labels.μ))
      (fun _ _ => zero_le) (Finset.mem_filter.mpr ⟨Finset.mem_univ Yt, hh⟩)) hs)
    refine lintegral_congr fun ω => ?_
    simp only [scored, if_pos hh]
  · have : ∀ ω, scored A m Yt (W, ω) = 0 := fun ω => by simp [scored, hh]
    simp [this]
private theorem scored_integrable (h : Holds R A) (hb : IsBlockTorusSide R.params m) (Yt : Finset (TorusSite m)) :
    Integrable (scored A m Yt) ((fieldHaar m).prod (Measure.pi fun _ : Yt => R.labels.μ)) := by
  have hm := scored_measurable h hb Yt
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (scored_nonneg h hb Yt))]
  rw [lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
  calc _ ≤ ∫⁻ _ : TorusField m, ENNReal.ofReal (massBound R m) ∂(fieldHaar m) := lintegral_mono fun W => scored_fibre h hb Yt W
    _ = ENNReal.ofReal (massBound R m) := by simp
    _ < ⊤ := ENNReal.ofReal_lt_top
private theorem scored_section (h : Holds R A) (hb : IsBlockTorusSide R.params m) (Yt : Finset (TorusSite m)) (W : TorusField m) :
    Integrable (fun ω => scored A m Yt (W, ω)) (Measure.pi fun _ : Yt => R.labels.μ) := by
  have hm : Measurable fun ω => scored A m Yt (W, ω) := (scored_measurable h hb Yt).comp measurable_prodMk_left
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => scored_nonneg h hb Yt _)]
  exact lt_of_le_of_lt (scored_fibre h hb Yt W) ENNReal.ofReal_lt_top
end Majorant
section Cases
variable {R : StepSetup} (A : ResponseSetup R) {n : ℕ} [NeZero n]
open Classical in
private def live (H : CaseFunction R n) (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : ℝ :=
  if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then H p.1 Yt p.2 bad b else 0
private structure Tame (H : CaseFunction R n) : Prop where
  borel : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n), Measurable (live H Yt bad b)
  size : ∃ M : ℝ, ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
    IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
    |H W Yt ωt bad b| ≤ M * Real.exp (∑ y : Yt, A.score (ωt y))
variable (C : Finset (TorusSite n)) (V : TorusField n)
private def product (H : CaseFunction R n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : ℝ :=
  (configurationWeight R C V bad Yt b p.1 p.2).toReal * live H Yt bad b p
private def gPlus (H : CaseFunction R n) (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) : ENNReal :=
  ENNReal.ofReal (live H Yt bad b (W, ω))
private def gMinus (H : CaseFunction R n) (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) : ENNReal :=
  ENNReal.ofReal (-live H Yt bad b (W, ω))
variable {A C V} {H : CaseFunction R n} {bad : Finset (TorusBond (n * R.params.side))}
  {Yt : Finset (TorusSite (n * R.params.side))} {b : BaseChoice R.params.side n}
private theorem weight_ne_top (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) :
    configurationWeight R C V bad Yt b W ω ≠ ⊤ := by
  classical
  unfold configurationWeight
  split_ifs
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.zero_ne_top
abbrev _root_.YangMills.SharedProofs.p21773 := @weight_ne_top
private theorem weight_mul_plus (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) :
    configurationWeight R C V bad Yt b W ω * gPlus H bad Yt b W ω = ENNReal.ofReal (product C V H bad Yt b (W, ω)) := by
  unfold product gPlus
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (weight_ne_top W ω)]
private theorem weight_mul_minus (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω) :
    configurationWeight R C V bad Yt b W ω * gMinus H bad Yt b W ω = ENNReal.ofReal (-product C V H bad Yt b (W, ω)) := by
  unfold product gMinus
  rw [← mul_neg, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (weight_ne_top W ω)]
private theorem density_bound (h : Holds R A) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) (V : TorusField n),
      0 ≤ stepTransitionDensity R.params R.coupling W b V ∧ stepTransitionDensity R.params R.coupling W b V ≤ Cd := by
  obtain ⟨Cd, hC⟩ := (h.inputs.density R.params R.coupling n).2
  exact ⟨|Cd|, abs_nonneg _, fun W b V => ⟨(hC W b V).1, (hC W b V).2.trans (le_abs_self _)⟩⟩
private theorem block_side (h : Holds R A) (hn : R.params.n₀ ≤ n) : IsBlockTorusSide R.params (n * R.params.side) :=
  ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
private theorem weight_nonneg (h : Holds R A) (hn : R.params.n₀ ≤ n) (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω)
    (hh : IsHullState R.params R.range W Yt) : 0 ≤ stepWeight R C V W Yt ω bad b := by
  obtain ⟨Cd, -, hC⟩ := density_bound (n := n) h
  rw [stepWeight_eq]
  exact mul_nonneg (mul_nonneg (h.forms.hasExpansions.2.nonneg _ (block_side h hn) W Yt ω hh) (hC W b V).1)
    (marks_nonneg h.forms C V W bad)
private theorem weight_zero (h : Holds R A) (hn : R.params.n₀ ≤ n) (W : TorusField (n * R.params.side)) (ω : Yt → R.labels.Ω)
    (hh : IsHullState R.params R.range W Yt) (hl : ¬ IsLiveState R.params R.coupling R.labelWeight W Yt ω) :
    stepWeight R C V W Yt ω bad b = 0 := by
  have h0 : R.labelWeight (n * R.params.side) W Yt ω = 0 :=
    le_antisymm (not_lt.mp fun hp => hl ⟨hh, hp⟩) (h.forms.hasExpansions.2.nonneg _ (block_side h hn) W Yt ω hh)
  rw [stepWeight_eq, h0, zero_mul, zero_mul]
private theorem product_measurable (h : Holds R A) (hn : R.params.n₀ ≤ n) (hT : Tame A H) :
    Measurable (product C V H bad Yt b) :=
  ((h.inputs.borel R h.forms n hn C V bad Yt b).ennreal_toReal).mul (hT.borel Yt bad b)
private theorem product_bound (h : Holds R A) (hn : R.params.n₀ ≤ n) (hT : Tame A H) :
    ∃ B : ℝ, ∀ p, |product C V H bad Yt b p| ≤ B * scored A (n * R.params.side) Yt p := by
  classical
  obtain ⟨M, hM⟩ := hT.size
  obtain ⟨Cd, hCd, hC⟩ := density_bound (n := n) h
  have hb := block_side h hn
  refine ⟨Cd * |M|, fun p => ?_⟩
  have hs := scored_nonneg h hb Yt p
  have hB : 0 ≤ Cd * |M| * scored A (n * R.params.side) Yt p := mul_nonneg (mul_nonneg hCd (abs_nonneg _)) hs
  unfold product live configurationWeight
  by_cases hh : IsHullState R.params R.range p.1 Yt
  · by_cases hl : IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2
    · rw [if_pos hh, if_pos hl, ENNReal.toReal_ofReal (weight_nonneg h hn p.1 p.2 hh), abs_mul,
        abs_of_nonneg (weight_nonneg h hn p.1 p.2 hh)]
      have hd := h.forms.hasExpansions.2.nonneg _ hb p.1 Yt p.2 hh
      have hw : stepWeight R C V p.1 Yt p.2 bad b ≤ R.labelWeight (n * R.params.side) p.1 Yt p.2 * Cd := by
        rw [stepWeight_eq]
        have hm := marks_le_one h.forms C V p.1 bad
        have hm0 := marks_nonneg h.forms C V p.1 bad
        calc _ ≤ R.labelWeight (n * R.params.side) p.1 Yt p.2 * stepTransitionDensity R.params R.coupling p.1 b V * 1 :=
              mul_le_mul_of_nonneg_left hm (mul_nonneg hd (hC p.1 b V).1)
          _ ≤ _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left (hC p.1 b V).2 hd
      have hH : |H p.1 Yt p.2 bad b| ≤ |M| * Real.exp (∑ y : Yt, A.score (p.2 y)) :=
        (hM p.1 Yt p.2 bad b hl).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
      have e : scored A (n * R.params.side) Yt p =
          R.labelWeight (n * R.params.side) p.1 Yt p.2 * Real.exp (∑ y : Yt, A.score (p.2 y)) := by
        unfold scored
        rw [if_pos (show IsHullState R.params (clusterRange R.coupling) p.1 Yt from hh)]
      rw [e]
      calc _ ≤ (R.labelWeight (n * R.params.side) p.1 Yt p.2 * Cd) * (|M| * Real.exp (∑ y : Yt, A.score (p.2 y))) :=
            mul_le_mul hw hH (abs_nonneg _) (mul_nonneg hd hCd)
        _ = _ := by ring
    · rw [if_neg hl, mul_zero, abs_zero]
      exact hB
  · rw [if_neg hh]
    simpa using hB
private theorem product_integrable (h : Holds R A) (hn : R.params.n₀ ≤ n) (hT : Tame A H) :
    Integrable (product C V H bad Yt b) ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) := by
  obtain ⟨B, hB⟩ := product_bound (C := C) (V := V) (bad := bad) (Yt := Yt) (b := b) h hn hT
  exact ((scored_integrable h (block_side h hn) Yt).const_mul B).mono'
    (product_measurable h hn hT).aestronglyMeasurable (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hB p)
private theorem gPlus_measurable (hT : Tame A H) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => gPlus H bad Yt b p.1 p.2 :=
  (hT.borel Yt bad b).ennreal_ofReal
private theorem gMinus_measurable (hT : Tame A H) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => gMinus H bad Yt b p.1 p.2 :=
  (hT.borel Yt bad b).neg.ennreal_ofReal
open Classical in
private theorem term_of_state (h : Holds R A) (hn : R.params.n₀ ≤ n) (q : CoarseState R n) {W : TorusField (n * R.params.side)}
    {ν : q.unlabelled Yt → R.labels.Ω} (hq : coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) :
    caseTerm R C V q H bad Yt b W ν = product C V H bad Yt b (q.fieldWithStoredLinks W, q.fillLabels Yt ν) := by
  unfold caseTerm product live configurationWeight
  by_cases hh : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt
  · rw [if_pos ⟨hh, hq⟩, if_pos hh, ENNReal.toReal_ofReal (weight_nonneg h hn _ _ hh)]
    by_cases hl : IsLiveState R.params R.coupling R.labelWeight (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν)
    · rw [if_pos hl, mul_comm]
    · rw [if_neg hl, weight_zero h hn _ _ hh hl]
      simp
  · rw [if_neg fun x => hh x.1, if_neg hh]
    simp
open Classical in
private theorem mass_plus_of_state (q : CoarseState R n) (hq : ∀ (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω),
    coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) :
    configurationMassWith R C V bad Yt b (gPlus H bad Yt b) q =
      ∫⁻ W, ∫⁻ ν, ENNReal.ofReal (product C V H bad Yt b (q.fieldWithStoredLinks W, q.fillLabels Yt ν))
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  unfold configurationMassWith
  refine lintegral_congr fun W => lintegral_congr fun ν => ?_
  rw [← weight_mul_plus]
  unfold configurationWeight
  by_cases hh : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt
  · rw [if_pos ⟨hh, hq W ν⟩, if_pos hh]
  · rw [if_neg fun x => hh x.1, if_neg hh, zero_mul]
open Classical in
private theorem mass_minus_of_state (q : CoarseState R n) (hq : ∀ (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω),
    coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) :
    configurationMassWith R C V bad Yt b (gMinus H bad Yt b) q =
      ∫⁻ W, ∫⁻ ν, ENNReal.ofReal (-product C V H bad Yt b (q.fieldWithStoredLinks W, q.fillLabels Yt ν))
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  unfold configurationMassWith
  refine lintegral_congr fun W => lintegral_congr fun ν => ?_
  rw [← weight_mul_minus]
  unfold configurationWeight
  by_cases hh : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt
  · rw [if_pos ⟨hh, hq W ν⟩, if_pos hh]
  · rw [if_neg fun x => hh x.1, if_neg hh, zero_mul]
private theorem term_formula (h : Holds R A) (hn : R.params.n₀ ≤ n) (hT : Tame A H) (q : CoarseState R n)
    (hp : configurationMassWith R C V bad Yt b (gPlus H bad Yt b) q ≠ ⊤)
    (hm : configurationMassWith R C V bad Yt b (gMinus H bad Yt b) q ≠ ⊤) :
    ∫ W, ∫ ν, caseTerm R C V q H bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      (configurationMassWith R C V bad Yt b (gPlus H bad Yt b) q).toReal -
        (configurationMassWith R C V bad Yt b (gMinus H bad Yt b) q).toReal := by
  classical
  by_cases hS : ∃ (W₀ : TorusField (n * R.params.side)) (ν₀ : q.unlabelled Yt → R.labels.Ω),
      coarseStateOf R C (q.fieldWithStoredLinks W₀) Yt (q.fillLabels Yt ν₀) bad b = q
  · obtain ⟨W₀, ν₀, h0⟩ := hS
    have hq : ∀ (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω),
        coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q := fun W ν => state_const q C Yt bad b h0
    set v : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) → ℝ :=
      fun p => product C V H bad Yt b (q.fieldWithStoredLinks p.1, q.fillLabels Yt p.2) with hv
    have hvm : Measurable v := (product_measurable h hn hT).comp
      (((measurable_fieldWithStoredLinks q).comp measurable_fst).prodMk ((measurable_fillLabels q Yt).comp measurable_snd))
    have e1 : configurationMassWith R C V bad Yt b (gPlus H bad Yt b) q = ∫⁻ p, ENNReal.ofReal (v p)
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : q.unlabelled Yt => R.labels.μ)) := by
      rw [lintegral_prod _ hvm.ennreal_ofReal.aemeasurable]
      exact mass_plus_of_state q hq
    have e2 : configurationMassWith R C V bad Yt b (gMinus H bad Yt b) q = ∫⁻ p, ENNReal.ofReal (-v p)
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : q.unlabelled Yt => R.labels.μ)) := by
      have hneg : Measurable fun p => ENNReal.ofReal (-v p) := hvm.neg.ennreal_ofReal
      rw [lintegral_prod (fun p => ENNReal.ofReal (-v p)) hneg.aemeasurable]
      exact mass_minus_of_state q hq
    have hi : Integrable v ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : q.unlabelled Yt => R.labels.μ)) :=
      integrable_of_parts hvm (e1 ▸ hp) (e2 ▸ hm)
    have e3 : ∫ W, ∫ ν, caseTerm R C V q H bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
        ∫ p, v p ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : q.unlabelled Yt => R.labels.μ)) := by
      rw [integral_prod _ hi]
      refine integral_congr_ae (ae_of_all _ fun W => integral_congr_ae (ae_of_all _ fun ν => ?_))
      exact term_of_state h hn q (hq W ν)
    rw [e3, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi, e1, e2]
  · push Not at hS
    have h0 : ∀ (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω), caseTerm R C V q H bad Yt b W ν = 0 :=
      fun W ν => by
        unfold caseTerm
        rw [if_neg fun x => hS W ν x.2]
    have z : ∀ g : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal,
        configurationMassWith R C V bad Yt b g q = 0 := fun g => by
      unfold configurationMassWith
      refine Eq.trans (lintegral_congr (g := fun _ => 0) fun W => ?_) (by simp)
      exact Eq.trans (lintegral_congr (g := fun _ => 0) fun ν => if_neg fun x => hS W ν x.2) (by simp)
    simp [h0, z]
variable (C V H bad Yt b) in
private def term (q : CoarseState R n) : ℝ :=
  ∫ W, ∫ ν, caseTerm R C V q H bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
variable (C V H) in
private def caseSum : ℝ :=
  ∑ bad ∈ (markedBonds R C).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
    ∫ p, product C V H bad Yt b p ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ))
private theorem plus_total (h : Holds R A) (hn : R.params.n₀ ≤ n) (hT : Tame A H) :
    ∫⁻ W, ∫⁻ ω : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ω * gPlus H bad Yt b W ω
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∫⁻ p, ENNReal.ofReal (product C V H bad Yt b p)
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) := by
  rw [lintegral_prod _ (product_measurable h hn hT).ennreal_ofReal.aemeasurable]
  exact lintegral_congr fun W => lintegral_congr fun ω => weight_mul_plus W ω
private theorem minus_total (h : Holds R A) (hn : R.params.n₀ ≤ n) (hT : Tame A H) :
    ∫⁻ W, ∫⁻ ω : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ω * gMinus H bad Yt b W ω
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∫⁻ p, ENNReal.ofReal (-product C V H bad Yt b p)
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) := by
  have hm : Measurable fun p => ENNReal.ofReal (-product C V H bad Yt b p) :=
    (product_measurable h hn hT).neg.ennreal_ofReal
  rw [lintegral_prod (fun p => ENNReal.ofReal (-product C V H bad Yt b p)) hm.aemeasurable]
  exact lintegral_congr fun W => lintegral_congr fun ω => weight_mul_minus W ω
private theorem plus_ne_top (h : Holds R A) (hn : R.params.n₀ ≤ n) (hT : Tame A H) :
    ∫⁻ p, ENNReal.ofReal (product C V H bad Yt b p)
      ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) ≠ ⊤ :=
  (product_integrable h hn hT).lintegral_lt_top.ne
private theorem minus_ne_top (h : Holds R A) (hn : R.params.n₀ ≤ n) (hT : Tame A H) :
    ∫⁻ p, ENNReal.ofReal (-product C V H bad Yt b p)
      ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) ≠ ⊤ :=
  (product_integrable h hn hT).neg.lintegral_lt_top.ne
private theorem weight_finite (h : Holds R A) (hn : R.params.n₀ ≤ n) :
    ∫⁻ W, ∫⁻ ω : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ω
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) ≠ ⊤ := by
  classical
  obtain ⟨Cd, hCd, hC⟩ := density_bound (n := n) h
  have hb := block_side h hn
  have hm := h.inputs.borel R h.forms n hn C V bad Yt b
  rw [← lintegral_prod (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => configurationWeight R C V bad Yt b p.1 p.2)
    hm.aemeasurable]
  refine ne_top_of_le_ne_top
    (((scored_integrable (A := A) h hb Yt).const_mul Cd).lintegral_lt_top.ne) (lintegral_mono fun p => ?_)
  unfold configurationWeight
  by_cases hh : IsHullState R.params R.range p.1 Yt
  · rw [if_pos hh]
    refine ENNReal.ofReal_le_ofReal ?_
    have hd := h.forms.hasExpansions.2.nonneg _ hb p.1 Yt p.2 hh
    have e : scored A (n * R.params.side) Yt p =
        R.labelWeight (n * R.params.side) p.1 Yt p.2 * Real.exp (∑ y : Yt, A.score (p.2 y)) := by
      unfold scored
      rw [if_pos (show IsHullState R.params (clusterRange R.coupling) p.1 Yt from hh)]
    have hE : 1 ≤ Real.exp (∑ y : Yt, A.score (p.2 y)) :=
      Real.one_le_exp (Finset.sum_nonneg fun y _ => h.resp.price.nonneg _)
    rw [e, stepWeight_eq]
    have hm1 := marks_le_one h.forms C V p.1 bad
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
private theorem term_total (h : Holds R A) (hn : R.params.n₀ ≤ n) (hT : Tame A H) :
    Integrable (fun ω => term C V H bad Yt b ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩)
        (Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side) ∧
      ∫ ω, term C V H bad Yt b ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩
          ∂(Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side) =
        ∫ p, product C V H bad Yt b p ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) := by
  obtain ⟨-, -, mp, ip⟩ := h.inputs.carry R h.forms n hn C V bad Yt b _ (gPlus_measurable (bad := bad) (b := b) hT)
  obtain ⟨-, -, mm, im⟩ := h.inputs.carry R h.forms n hn C V bad Yt b _ (gMinus_measurable (bad := bad) (b := b) hT)
  rw [plus_total h hn hT] at ip
  rw [minus_total h hn hT] at im
  have fp := plus_ne_top (C := C) (V := V) (bad := bad) (Yt := Yt) (b := b) h hn hT
  have fm := minus_ne_top (C := C) (V := V) (bad := bad) (Yt := Yt) (b := b) h hn hT
  rw [← ip] at fp
  rw [← im] at fm
  have ap := ae_lt_top mp fp
  have am := ae_lt_top mm fm
  have aeq : (fun ω => term C V H bad Yt b ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩)
      =ᵐ[Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side]
      fun ω => (configurationMassWith R C V bad Yt b (gPlus H bad Yt b)
          ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩).toReal -
        (configurationMassWith R C V bad Yt b (gMinus H bad Yt b)
          ⟨coarseHull R.params.side R.range R.nextRange bad Yt C, ω⟩).toReal := by
    filter_upwards [ap, am] with ω a1 a2
    exact term_formula h hn hT _ a1.ne a2.ne
  have i1 := integrable_toReal_of_lintegral_ne_top mp.aemeasurable fp
  have i2 := integrable_toReal_of_lintegral_ne_top mm.aemeasurable fm
  refine ⟨(i1.sub i2).congr aeq.symm, ?_⟩
  rw [integral_congr_ae aeq, integral_sub i1 i2, integral_toReal mp.aemeasurable ap, integral_toReal mm.aemeasurable am,
    ip, im, integral_eq_lintegral_pos_part_sub_lintegral_neg_part (product_integrable h hn hT)]
private theorem term_off {q : CoarseState R n} (hY : q.1 ≠ coarseHull R.params.side R.range R.nextRange bad Yt C) :
    term C V H bad Yt b q = 0 := by
  classical
  have h0 : ∀ (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω), caseTerm R C V q H bad Yt b W ν = 0 :=
    fun W ν => by
      unfold caseTerm
      rw [if_neg fun x => hY (congrArg Sigma.fst x.2).symm]
  unfold term
  simp [h0]
private theorem term_integrable (h : Holds R A) (hn : R.params.n₀ ≤ n) (hT : Tame A H) (Y : Finset (TorusSite n)) :
    Integrable (fun ω : Y → CoarseLabel R.labels.Ω R.params.side => term C V H bad Yt b ⟨Y, ω⟩)
      (Measure.pi fun _ => coarseLabelMeasure R.labels.μ R.params.side) := by
  by_cases hY : Y = coarseHull R.params.side R.range R.nextRange bad Yt C
  · subst hY
    exact (term_total h hn hT).1
  · have e : (fun ω : Y → CoarseLabel R.labels.Ω R.params.side => term C V H bad Yt b ⟨Y, ω⟩) = fun _ => 0 :=
      funext fun ω => term_off (q := ⟨Y, ω⟩) hY
    rw [e]
    exact integrable_zero _ _ _
private theorem term_sum (h : Holds R A) (hn : R.params.n₀ ≤ n) (hT : Tame A H) (hs : IsBlockTorusSide R.params n) :
    (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
      ∫ ω, term (hotCoreSites R V) V H bad Yt b ⟨Y, ω⟩ ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)) =
      ∫ p, product (hotCoreSites R V) V H bad Yt b p
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) := by
  classical
  have hmem : coarseHull R.params.side R.range R.nextRange bad Yt (hotCoreSites R V) ∈
      Finset.univ.filter (IsHullState R.params R.nextRange V) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      h.inputs.hulls R.params h.forms.admissible R.range R.nextRange h.forms.range_le h.forms.nextRange_ge n hs.1 V bad Yt⟩
  rw [Finset.sum_eq_single_of_mem _ hmem]
  · exact (term_total h hn hT).2
  · intro Y _ hY
    have e : ∀ ω : Y → CoarseLabel R.labels.Ω R.params.side, term (hotCoreSites R V) V H bad Yt b ⟨Y, ω⟩ = 0 :=
      fun ω => term_off (q := ⟨Y, ω⟩) hY
    simp [e]
private theorem cases_finite (h : Holds R A) (hn : R.params.n₀ ≤ n) (hT : Tame A H) (Y : Finset (TorusSite n)) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side),
      configurationMassWith R C V bad Yt b (gPlus H bad Yt b) ⟨Y, ω⟩ ≠ ⊤ ∧
      configurationMassWith R C V bad Yt b (gMinus H bad Yt b) ⟨Y, ω⟩ ≠ ⊤ ∧
      configurationMass R C V bad Yt b ⟨Y, ω⟩ ≠ ⊤ := by
  obtain ⟨zp, -, mp, ip⟩ := h.inputs.carry R h.forms n hn C V bad Yt b _ (gPlus_measurable (bad := bad) (b := b) hT)
  obtain ⟨zm, -, mm, im⟩ := h.inputs.carry R h.forms n hn C V bad Yt b _ (gMinus_measurable (bad := bad) (b := b) hT)
  obtain ⟨zo, mo, io⟩ := h.inputs.one R h.forms n hn C V bad Yt b
  by_cases hY : Y = coarseHull R.params.side R.range R.nextRange bad Yt C
  · subst hY
    rw [plus_total h hn hT] at ip
    rw [minus_total h hn hT] at im
    have fp := plus_ne_top (C := C) (V := V) (bad := bad) (Yt := Yt) (b := b) h hn hT
    have fm := minus_ne_top (C := C) (V := V) (bad := bad) (Yt := Yt) (b := b) h hn hT
    rw [← ip] at fp
    rw [← im] at fm
    have fo := weight_finite (C := C) (V := V) (bad := bad) (Yt := Yt) (b := b) h hn
    rw [← io] at fo
    filter_upwards [ae_lt_top mp fp, ae_lt_top mm fm, ae_lt_top mo fo] with ω a1 a2 a3
    exact ⟨a1.ne, a2.ne, a3.ne⟩
  · refine ae_of_all _ fun ω => ?_
    rw [zp ⟨Y, ω⟩ hY, zm ⟨Y, ω⟩ hY, zo ⟨Y, ω⟩ hY]
    simp
private theorem mean_ae (h : Holds R A) (hn : R.params.n₀ ≤ n) (hT : Tame A H) (Y : Finset (TorusSite n)) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side),
      caseMean R C V ⟨Y, ω⟩ H * coarseStateWeight R C V ⟨Y, ω⟩ = caseIntegral R C V ⟨Y, ω⟩ H := by
  classical
  have hall : ∀ᵐ ω ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side),
      ∀ bad ∈ (markedBonds R C).powerset, ∀ (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
        configurationMassWith R C V bad Yt b (gPlus H bad Yt b) ⟨Y, ω⟩ ≠ ⊤ ∧
        configurationMassWith R C V bad Yt b (gMinus H bad Yt b) ⟨Y, ω⟩ ≠ ⊤ ∧
        configurationMass R C V bad Yt b ⟨Y, ω⟩ ≠ ⊤ :=
    (Filter.eventually_all_finset _).2 fun bad _ => Filter.eventually_all.2 fun Yt => Filter.eventually_all.2 fun b =>
      cases_finite h hn hT Y
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
    have z1 := (h.inputs.carry R h.forms n hn C V bad Yt b _ (gPlus_measurable (bad := bad) (b := b) hT)).2.1 _
      (hcase bad hbad Yt b)
    have z2 := (h.inputs.carry R h.forms n hn C V bad Yt b _ (gMinus_measurable (bad := bad) (b := b) hT)).2.1 _
      (hcase bad hbad Yt b)
    rw [term_formula h hn hT _ (hω bad hbad Yt b).1 (hω bad hbad Yt b).2.1, z1, z2]
    simp
  · unfold caseMean
    exact div_mul_cancel₀ _ h0
private theorem hull_total (h : Holds R A) (hn : R.params.n₀ ≤ n) (hT : Tame A H) (hs : IsBlockTorusSide R.params n) :
    (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState R.params R.nextRange V),
      ∫ ω, caseMean R (hotCoreSites R V) V ⟨Y, ω⟩ H * coarseStateWeight R (hotCoreSites R V) V ⟨Y, ω⟩
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side)) = caseSum (hotCoreSites R V) V H := by
  classical
  have e : ∀ Y : Finset (TorusSite n), ∫ ω, caseMean R (hotCoreSites R V) V ⟨Y, ω⟩ H *
        coarseStateWeight R (hotCoreSites R V) V ⟨Y, ω⟩ ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) =
      ∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
        ∑ b : BaseChoice R.params.side n,
        ∫ ω, term (hotCoreSites R V) V H bad Yt b ⟨Y, ω⟩ ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) := by
    intro Y
    rw [integral_congr_ae (mean_ae h hn hT Y)]
    show ∫ ω, (∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
        ∑ b : BaseChoice R.params.side n, term (hotCoreSites R V) V H bad Yt b ⟨Y, ω⟩)
        ∂(Measure.pi fun _ : Y => coarseLabelMeasure R.labels.μ R.params.side) = _
    rw [integral_finsetSum _ fun bad _ => integrable_finsetSum _ fun Yt _ => integrable_finsetSum _ fun b _ =>
      term_integrable h hn hT Y]
    refine Finset.sum_congr rfl fun bad _ => ?_
    rw [integral_finsetSum _ fun Yt _ => integrable_finsetSum _ fun b _ => term_integrable h hn hT Y]
    refine Finset.sum_congr rfl fun Yt _ => ?_
    rw [integral_finsetSum _ fun b _ => term_integrable h hn hT Y]
  simp_rw [e]
  unfold caseSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun bad _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Yt _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => term_sum h hn hT hs
private theorem coarseHull_empty (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))) :
    coarseHull R.params.side R.range R.nextRange bad Yt (∅ : Finset (TorusSite n)) = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coarseHull_empty <;> assumption
private theorem mass_at_empty (h : Holds R A) (hn : R.params.n₀ ≤ n)
    (g : TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ENNReal)
    (hg : Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => g p.1 p.2) (Y : Finset (TorusSite n))
    (hY : Y = coarseHull R.params.side R.range R.nextRange bad Yt (∅ : Finset (TorusSite n)))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) :
    configurationMassWith R ∅ V bad Yt b g ⟨Y, ω⟩ =
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R ∅ V bad Yt b W ωt * g W ωt
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  subst hY
  obtain ⟨-, -, hm, hi⟩ := h.inputs.carry R h.forms n hn ∅ V bad Yt b g hg
  rw [← hi]
  have he : IsEmpty (coarseHull R.params.side R.range R.nextRange bad Yt (∅ : Finset (TorusSite n))) :=
    ⟨fun x => by
      obtain ⟨z, hz⟩ := x
      rw [coarseHull_empty] at hz
      simp at hz⟩
  rw [Measure.pi_of_empty _ ω, lintegral_dirac' _ hm]
private theorem cold_total (h : Holds R A) (hn : R.params.n₀ ≤ n) (hT : Tame A H) :
    caseIntegral R ∅ V (emptyCoarseState R) H = caseSum ∅ V H := by
  classical
  unfold caseIntegral caseSum
  refine Finset.sum_congr rfl fun bad _ => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ => ?_
  have ep : configurationMassWith R ∅ V bad Yt b (gPlus H bad Yt b) (emptyCoarseState R) = _ :=
    mass_at_empty h hn _ (gPlus_measurable hT) ∅ (coarseHull_empty bad Yt).symm (emptyCoarseState R).2
  have em : configurationMassWith R ∅ V bad Yt b (gMinus H bad Yt b) (emptyCoarseState R) = _ :=
    mass_at_empty h hn _ (gMinus_measurable hT) ∅ (coarseHull_empty bad Yt).symm (emptyCoarseState R).2
  rw [plus_total h hn hT] at ep
  rw [minus_total h hn hT] at em
  have fp := plus_ne_top (C := ∅) (V := V) (bad := bad) (Yt := Yt) (b := b) h hn hT
  have fm := minus_ne_top (C := ∅) (V := V) (bad := bad) (Yt := Yt) (b := b) h hn hT
  rw [← ep] at fp
  rw [← em] at fm
  rw [term_formula h hn hT _ fp fm, ep, em,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (product_integrable h hn hT)]
private theorem sum_at_zero (h : Holds R A) (hn : R.params.n₀ ≤ n) (hT : Tame A H)
    (hD : kernelImage R.params R.coupling R.functional n V = 0) : caseSum C V H = 0 := by
  classical
  have hz := h.inputs.addUp R h.forms n hn C V
  rw [hD, ENNReal.ofReal_zero] at hz
  unfold caseSum
  refine Finset.sum_eq_zero fun bad hbad => Finset.sum_eq_zero fun Yt _ => Finset.sum_eq_zero fun b _ => ?_
  have h1 := (Finset.sum_eq_zero_iff.mp hz) bad hbad
  have h2 := (Finset.sum_eq_zero_iff.mp h1) Yt (Finset.mem_univ _)
  have h3 := (Finset.sum_eq_zero_iff.mp h2) b (Finset.mem_univ _)
  have hm := h.inputs.borel R h.forms n hn C V bad Yt b
  rw [← lintegral_prod (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => configurationWeight R C V bad Yt b p.1 p.2)
    hm.aemeasurable] at h3
  have h4 := (lintegral_eq_zero_iff hm).mp h3
  refine integral_eq_zero_of_ae ?_
  filter_upwards [h4] with p hp
  have hp' : configurationWeight R C V bad Yt b p.1 p.2 = 0 := hp
  unfold product
  rw [hp']
  simp
end Cases
private def Tie (R : StepSetup) (A : ResponseSetup R) (rO : ColdResponse R.params.side R.depth) : Prop :=
  ∀ (m : ℕ) [NeZero m], IsBlockTorusSide R.params m → ∀ (y : TorusSite m) (W : TorusField m)
    (hw : PlaquetteWeight (fineSide R.params.side R.depth m)),
    R.functional m W * rO m y W hw = open Classical in ∑ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
      ∫ ω, A.hull m y W Yt ω hw * R.labelWeight m W Yt ω ∂(Measure.pi fun _ : Yt => R.labels.μ)
section Sections
variable {R : StepSetup} {A : ResponseSetup R} {m : ℕ} [NeZero m]
private theorem live_measurable (h : Holds R A) (hb : IsBlockTorusSide R.params m) (Yt : Finset (TorusSite m)) :
    MeasurableSet {p : TorusField m × (Yt → R.labels.Ω) | IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} := by
  classical
  have hm := (h.forms.hasExpansions.2.borel m hb Yt).1
  have e : {p : TorusField m × (Yt → R.labels.Ω) | IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} =
      (fun p : TorusField m × (Yt → R.labels.Ω) =>
        if IsHullState R.params (clusterRange R.coupling) p.1 Yt then R.labelWeight m p.1 Yt p.2 else 0) ⁻¹' Set.Ioi 0 := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi, IsLiveState]
    split_ifs with hh
    · simp [hh]
    · simp [hh]
  rw [e]
  convert hm measurableSet_Ioi using 3
private theorem score_le_exp (h : Holds R A) {Y : Finset (TorusSite m)} (ω : Y → R.labels.Ω) (y : TorusSite m) :
    siteScore A.score Y ω y ≤ Real.exp (∑ z : Y, A.score (ω z)) := by
  classical
  unfold siteScore
  split_ifs with hy
  · have h1 : A.score (ω ⟨y, hy⟩) ≤ ∑ z : Y, A.score (ω z) :=
      Finset.single_le_sum (f := fun z : Y => A.score (ω z)) (fun z _ => h.resp.price.nonneg _)
        (Finset.mem_univ (⟨y, hy⟩ : Y))
    linarith [Real.add_one_le_exp (∑ z : Y, A.score (ω z))]
  · exact (Real.exp_pos _).le
private theorem exp_ge_one (h : Holds R A) {Y : Finset (TorusSite m)} (ω : Y → R.labels.Ω) :
    1 ≤ Real.exp (∑ z : Y, A.score (ω z)) :=
  Real.one_le_exp (Finset.sum_nonneg fun y _ => h.resp.price.nonneg _)
private theorem hull_bound (h : Holds R A) (hb : IsBlockTorusSide R.params m) (y : TorusSite m) (W : TorusField m)
    (Yt : Finset (TorusSite m)) (ω : Yt → R.labels.Ω)
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ω) (hw : PlaquetteWeight (fineSide R.params.side R.depth m)) :
    |A.hull m y W Yt ω hw| ≤ (|A.cold m y (trivialField m) hw| + (|A.responseParams.C₀| + 1) * |weightNorm R.params.side R.depth hw|) *
      Real.exp (∑ z : Yt, A.score (ω z)) := by
  classical
  have hs := h.resp.bounds.size_hull m hb y W Yt ω hl hw
  unfold centeredHullResponse at hs
  have hE := exp_ge_one h ω
  have hsc := score_le_exp h ω y
  have hsc0 : 0 ≤ siteScore A.score Yt ω y := by
    unfold siteScore
    split_ifs
    · exact h.resp.price.nonneg _
    · exact le_rfl
  set E := Real.exp (∑ z : Yt, A.score (ω z))
  set Z := weightNorm R.params.side R.depth hw
  set Pf := A.cold m y (trivialField m) hw
  have h1 : |A.hull m y W Yt ω hw| ≤ |Pf| + (|A.responseParams.C₀| + siteScore A.score Yt ω y) * |Z| := by
    have e : A.hull m y W Yt ω hw = (A.hull m y W Yt ω hw - Pf) + Pf := by ring
    have h2 : |(A.responseParams.C₀ + siteScore A.score Yt ω y) * Z| ≤ (|A.responseParams.C₀| + siteScore A.score Yt ω y) * |Z| := by
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
  have e2 : (|Pf| + (|A.responseParams.C₀| + 1) * |Z|) * E = |Pf| * E + (|A.responseParams.C₀| + 1) * E * |Z| := by ring
  rw [e2]
  linarith
private theorem labelWeight_measurable (h : Holds R A) (hb : IsBlockTorusSide R.params m) {Yt : Finset (TorusSite m)}
    {W : TorusField m} (hh : IsHullState R.params (clusterRange R.coupling) W Yt) :
    Measurable fun ω => R.labelWeight m W Yt ω := by
  classical
  have hm := (h.forms.hasExpansions.2.borel m hb Yt).1.comp (measurable_prodMk_left (x := W))
  have e : (fun ω => R.labelWeight m W Yt ω) =
      (fun p : TorusField m × (Yt → R.labels.Ω) =>
        if IsHullState R.params (clusterRange R.coupling) p.1 Yt then R.labelWeight m p.1 Yt p.2 else 0) ∘ Prod.mk W := by
    funext ω
    simp [hh]
  rw [e]
  exact hm
private theorem scored_at (A : ResponseSetup R) {Yt : Finset (TorusSite m)} {W : TorusField m}
    (hh : IsHullState R.params (clusterRange R.coupling) W Yt) (ω : Yt → R.labels.Ω) :
    scored A m Yt (W, ω) = R.labelWeight m W Yt ω * Real.exp (∑ y : Yt, A.score (ω y)) := by
  classical
  unfold scored
  rw [if_pos hh]
private theorem labelWeight_integrable (h : Holds R A) (hb : IsBlockTorusSide R.params m) {Yt : Finset (TorusSite m)}
    {W : TorusField m} (hh : IsHullState R.params (clusterRange R.coupling) W Yt) :
    Integrable (fun ω => R.labelWeight m W Yt ω) (Measure.pi fun _ : Yt => R.labels.μ) := by
  refine (scored_section h hb Yt W).mono' (labelWeight_measurable h hb hh).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  have hd := h.forms.hasExpansions.2.nonneg m hb W Yt ω hh
  rw [scored_at A hh, Real.norm_eq_abs, abs_of_nonneg hd]
  exact le_mul_of_one_le_right hd (exp_ge_one h ω)
open Classical in
private def hullLive (A : ResponseSetup R) (m : ℕ) [NeZero m] (y : TorusSite m)
    (hw : PlaquetteWeight (fineSide R.params.side R.depth m)) (Yt : Finset (TorusSite m))
    (p : TorusField m × (Yt → R.labels.Ω)) : ℝ :=
  if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then A.hull m y p.1 Yt p.2 hw else 0
private theorem hullLive_measurable (h : Holds R A) (hb : IsBlockTorusSide R.params m) (y : TorusSite m)
    (hw : PlaquetteWeight (fineSide R.params.side R.depth m)) (Yt : Finset (TorusSite m)) : Measurable (hullLive A m y hw Yt) :=
  h.resp.bounds.hull_borel m hb y Yt hw
private theorem hull_integrable (h : Holds R A) (hb : IsBlockTorusSide R.params m) {Yt : Finset (TorusSite m)}
    {W : TorusField m} (hh : IsHullState R.params (clusterRange R.coupling) W Yt) (y : TorusSite m)
    (hw : PlaquetteWeight (fineSide R.params.side R.depth m)) :
    Integrable (fun ω => A.hull m y W Yt ω hw * R.labelWeight m W Yt ω) (Measure.pi fun _ : Yt => R.labels.μ) := by
  classical
  have hqm : Measurable fun ω : Yt → R.labels.Ω => hullLive A m y hw Yt (W, ω) :=
    (hullLive_measurable h hb y hw Yt).comp measurable_prodMk_left
  have e : (fun ω => A.hull m y W Yt ω hw * R.labelWeight m W Yt ω) =
      fun ω => hullLive A m y hw Yt (W, ω) * R.labelWeight m W Yt ω := by
    funext ω
    by_cases hl : IsLiveState R.params R.coupling R.labelWeight W Yt ω
    · unfold hullLive
      rw [if_pos hl]
    · have h0 : R.labelWeight m W Yt ω = 0 :=
        le_antisymm (not_lt.mp fun hp => hl ⟨hh, hp⟩) (h.forms.hasExpansions.2.nonneg m hb W Yt ω hh)
      rw [h0, mul_zero, mul_zero]
  rw [e]
  have hM : 0 ≤ |A.cold m y (trivialField m) hw| + (|A.responseParams.C₀| + 1) * |weightNorm R.params.side R.depth hw| :=
    add_nonneg (abs_nonneg _) (mul_nonneg (add_nonneg (abs_nonneg _) zero_le_one) (abs_nonneg _))
  refine ((scored_section (A := A) h hb Yt W).const_mul
    (|A.cold m y (trivialField m) hw| + (|A.responseParams.C₀| + 1) * |weightNorm R.params.side R.depth hw|)).mono'
    (hqm.mul (labelWeight_measurable h hb hh)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  have hd := h.forms.hasExpansions.2.nonneg m hb W Yt ω hh
  show ‖hullLive A m y hw Yt (W, ω) * R.labelWeight m W Yt ω‖ ≤ _
  rw [scored_at A hh, Real.norm_eq_abs, abs_mul, abs_of_nonneg hd]
  by_cases hl : IsLiveState R.params R.coupling R.labelWeight W Yt ω
  · have hq := hull_bound h hb y W Yt ω hl hw
    have e2 : hullLive A m y hw Yt (W, ω) = A.hull m y W Yt ω hw := by
      unfold hullLive
      rw [if_pos hl]
    rw [e2]
    calc _ ≤ (|A.cold m y (trivialField m) hw| + (|A.responseParams.C₀| + 1) * |weightNorm R.params.side R.depth hw|) *
          Real.exp (∑ z : Yt, A.score (ω z)) * R.labelWeight m W Yt ω := mul_le_mul_of_nonneg_right hq hd
      _ = _ := by ring
  · have e2 : hullLive A m y hw Yt (W, ω) = 0 := by
      unfold hullLive
      rw [if_neg hl]
    rw [e2, abs_zero, zero_mul]
    exact mul_nonneg hM (mul_nonneg hd (Real.exp_pos _).le)
private theorem real_sum (h : Holds R A) (hb : IsBlockTorusSide R.params m) (W : TorusField m) :
    (open Classical in ∑ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
      ∫ ω, R.labelWeight m W Yt ω ∂(Measure.pi fun _ : Yt => R.labels.μ)) = R.functional m W := by
  classical
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn : R.params.n₀ ≤ m := le_trans (Nat.le_mul_of_pos_left _ hLpos) hb.2
  have hs := h.forms.hasExpansions.2.sum m hb W
  have hD : 0 ≤ R.functional m W := (h.forms.functional_spec m hn).2.1 W
  have hfin : ∀ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
      ∫⁻ ω, ENNReal.ofReal (R.labelWeight m W Yt ω) ∂(Measure.pi fun _ : Yt => R.labels.μ) ≠ ⊤ := fun Yt hY =>
    (labelWeight_integrable h hb (Finset.mem_filter.mp hY).2).lintegral_lt_top.ne
  have e : ∀ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
      ∫ ω, R.labelWeight m W Yt ω ∂(Measure.pi fun _ : Yt => R.labels.μ) =
      (∫⁻ ω, ENNReal.ofReal (R.labelWeight m W Yt ω) ∂(Measure.pi fun _ : Yt => R.labels.μ)).toReal := fun Yt hY => by
    have hh := (Finset.mem_filter.mp hY).2
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => h.forms.hasExpansions.2.nonneg m hb W Yt ω hh)
      (labelWeight_measurable h hb hh).aestronglyMeasurable
  rw [Finset.sum_congr rfl e, ← ENNReal.toReal_sum hfin, hs, ENNReal.toReal_ofReal hD]
end Sections
section Value
variable {R : StepSetup} {A : ResponseSetup R} {n : ℕ} [NeZero n]
private theorem blockBondScores_abs_le (h : Holds R A) (W : TorusField (n * R.params.side)) (V : TorusField n)
    (b : BaseChoice R.params.side n) (Y : TorusSite n) : |blockBondScores (R := R) W V b Y| ≤ 16 := by
  unfold blockBondScores
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hc : ∀ c : TorusBond n, |bondScore R.params R.coupling W V b c| ≤ 2 := fun c =>
    (h.inputs.score R.params h.forms.admissible R.coupling n b c).2.2.1 W V
  have : ∀ i : Fin 4, |bondScore R.params R.coupling W V b (Y, i) + bondScore R.params R.coupling W V b (Y - TorusFields.unitStep n i, i)| ≤ 4 :=
    fun i => (abs_add_le _ _).trans (by linarith [hc (Y, i), hc (Y - TorusFields.unitStep n i, i)])
  calc _ ≤ ∑ _i : Fin 4, (4 : ℝ) := Finset.sum_le_sum fun i _ => this i
    _ = 16 := by norm_num
private theorem blockBondScores_measurable (h : Holds R A) (V : TorusField n) (b : BaseChoice R.params.side n) (Y : TorusSite n) :
    Measurable fun W : TorusField (n * R.params.side) => blockBondScores (R := R) W V b Y := by
  unfold blockBondScores
  have hp : Measurable fun W : TorusField (n * R.params.side) => (W, V) := measurable_id.prodMk measurable_const
  have hc : ∀ c : TorusBond n, Measurable fun W : TorusField (n * R.params.side) => bondScore R.params R.coupling W V b c := fun c => by
    have h0 := (h.inputs.score R.params h.forms.admissible R.coupling n b c).2.2.2.2
    exact Measurable.comp (g := fun p : TorusField (n * R.params.side) × TorusField n => bondScore R.params R.coupling p.1 p.2 b c)
      (f := fun W : TorusField (n * R.params.side) => (W, V)) h0 hp
  have h1 : ∀ i : Fin 4, Measurable fun W : TorusField (n * R.params.side) =>
      bondScore R.params R.coupling W V b (Y, i) + bondScore R.params R.coupling W V b (Y - TorusFields.unitStep n i, i) :=
    fun i => (hc (Y, i)).add (hc (Y - TorusFields.unitStep n i, i))
  exact Finset.measurable_sum Finset.univ fun i _ => h1 i
private theorem tame_response (h : Holds R A) (hn : R.params.n₀ ≤ n) (V : TorusField n) (Y : TorusSite n)
    (hw : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) : Tame A (caseResponse A V Y hw) := by
  classical
  have hb := block_side h hn
  set c : ℝ := R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y hw with hc
  refine ⟨fun Yt bad b => ?_, ?_⟩
  · have hl := live_measurable h hb Yt
    have e : live (caseResponse A V Y hw) Yt bad b = fun p =>
        ∑ y ∈ sitesInBlocks R.params.side {Y}, (if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then
            A.hull (n * R.params.side) y p.1 Yt p.2 hw else 0) +
          (if IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2 then c * blockBondScores (R := R) p.1 V b Y else 0) := by
      funext p
      unfold live caseResponse
      by_cases hp : IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2
      · simp [hp, hc]
      · simp [hp]
    rw [e]
    exact (Finset.measurable_sum _ fun y _ => h.resp.bounds.hull_borel _ hb y Yt hw).add
      (Measurable.ite hl (((blockBondScores_measurable h V b Y).comp measurable_fst).const_mul c) measurable_const)
  · refine ⟨∑ y ∈ sitesInBlocks R.params.side {Y}, (|A.cold (n * R.params.side) y (trivialField _) hw| +
      (|A.responseParams.C₀| + 1) * |weightNorm R.params.side R.depth hw|) + |c| * 16, fun W Yt ωt bad b hl => ?_⟩
    show |∑ y ∈ sitesInBlocks R.params.side {Y}, A.hull (n * R.params.side) y W Yt ωt hw + c * blockBondScores (R := R) W V b Y| ≤ _
    have hE := exp_ge_one h ωt
    have h1 : |∑ y ∈ sitesInBlocks R.params.side {Y}, A.hull (n * R.params.side) y W Yt ωt hw| ≤
        (∑ y ∈ sitesInBlocks R.params.side {Y}, (|A.cold (n * R.params.side) y (trivialField _) hw| +
          (|A.responseParams.C₀| + 1) * |weightNorm R.params.side R.depth hw|)) * Real.exp (∑ z : Yt, A.score (ωt z)) := by
      rw [Finset.sum_mul]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => hull_bound h hb y W Yt ωt hl hw)
    have h2 : |c * blockBondScores (R := R) W V b Y| ≤ |c| * 16 * Real.exp (∑ z : Yt, A.score (ωt z)) := by
      rw [abs_mul]
      calc _ ≤ |c| * 16 := mul_le_mul_of_nonneg_left (blockBondScores_abs_le h W V b Y) (abs_nonneg _)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hE
    rw [add_mul]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
open Classical in
private def fullPart (H : CaseFunction R n) (V : TorusField n) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : ℝ :=
  if IsHullState R.params (clusterRange R.coupling) p.1 Yt then
    R.labelWeight (n * R.params.side) p.1 Yt p.2 * stepTransitionDensity R.params R.coupling p.1 b V * live H Yt ∅ b p else 0
private theorem sum_bad (h : Holds R A) (hn : R.params.n₀ ≤ n) {H : CaseFunction R n}
    (hI : ∀ W Yt ω (bad bad' : Finset (TorusBond (n * R.params.side))) b, H W Yt ω bad b = H W Yt ω bad' b)
    (C : Finset (TorusSite n)) (V : TorusField n) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) :
    ∑ bad ∈ (markedBonds R C).powerset, product C V H bad Yt b p = fullPart H V Yt b p := by
  classical
  have hl : ∀ bad, live H Yt bad b p = live H Yt ∅ b p := fun bad => by
    unfold live
    rw [hI p.1 Yt p.2 bad ∅ b]
  unfold fullPart
  by_cases hh : IsHullState R.params (clusterRange R.coupling) p.1 Yt
  · rw [if_pos hh]
    have e : ∀ bad, product C V H bad Yt b p =
        R.labelWeight (n * R.params.side) p.1 Yt p.2 * stepTransitionDensity R.params R.coupling p.1 b V * live H Yt ∅ b p *
          markProduct R C V p.1 bad := fun bad => by
      unfold product configurationWeight
      rw [if_pos (show IsHullState R.params R.range p.1 Yt from hh), ENNReal.toReal_ofReal (weight_nonneg h hn p.1 p.2 hh),
        stepWeight_eq, hl bad]
      ring
    simp_rw [e]
    rw [← Finset.mul_sum, marks_sum, mul_one]
  · rw [if_neg hh]
    refine Finset.sum_eq_zero fun bad _ => ?_
    unfold product configurationWeight
    rw [if_neg (show ¬ IsHullState R.params R.range p.1 Yt from hh)]
    simp
private theorem full_integrable (h : Holds R A) (hn : R.params.n₀ ≤ n) {H : CaseFunction R n} (hT : Tame A H)
    (hI : ∀ W Yt ω (bad bad' : Finset (TorusBond (n * R.params.side))) b, H W Yt ω bad b = H W Yt ω bad' b)
    (C : Finset (TorusSite n)) (V : TorusField n) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Integrable (fullPart H V Yt b) ((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) := by
  have hi := integrable_finsetSum (μ := (fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ))
    (markedBonds R C).powerset (f := fun bad p => product C V H bad Yt b p)
    fun bad _ => product_integrable h hn hT
  exact hi.congr (ae_of_all _ fun p => sum_bad h hn hI C V Yt b p)
private theorem sum_bad_integral (h : Holds R A) (hn : R.params.n₀ ≤ n) {H : CaseFunction R n} (hT : Tame A H)
    (hI : ∀ W Yt ω (bad bad' : Finset (TorusBond (n * R.params.side))) b, H W Yt ω bad b = H W Yt ω bad' b)
    (C : Finset (TorusSite n)) (V : TorusField n) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    ∑ bad ∈ (markedBonds R C).powerset,
      ∫ p, product C V H bad Yt b p ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) =
      ∫ p, fullPart H V Yt b p ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) := by
  rw [← integral_finsetSum _ fun bad _ => product_integrable h hn hT]
  exact integral_congr_ae (ae_of_all _ fun p => sum_bad h hn hI C V Yt b p)
private theorem section_value (h : Holds R A) (hn : R.params.n₀ ≤ n) {rO : ColdResponse R.params.side R.depth} (tie : Tie R A rO)
    (V : TorusField n) (Y : TorusSite n) (hw : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (W : TorusField (n * R.params.side)) :
    ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
      ∫ ω, fullPart (caseResponse A V Y hw) V Yt b (W, ω) ∂(Measure.pi fun _ : Yt => R.labels.μ) =
    R.functional (n * R.params.side) W * ∑ b : BaseChoice R.params.side n, stepTransitionDensity R.params R.coupling W b V *
      (∑ z ∈ sitesInBlocks R.params.side {Y}, rO (n * R.params.side) z W hw +
        R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y hw * blockBondScores (R := R) W V b Y) := by
  classical
  have hb := block_side h hn
  have hval : ∀ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W), ∀ b : BaseChoice R.params.side n,
      ∫ ω, fullPart (caseResponse A V Y hw) V Yt b (W, ω) ∂(Measure.pi fun _ : Yt => R.labels.μ) =
      stepTransitionDensity R.params R.coupling W b V * (∑ z ∈ sitesInBlocks R.params.side {Y},
          ∫ ω, A.hull (n * R.params.side) z W Yt ω hw * R.labelWeight (n * R.params.side) W Yt ω
            ∂(Measure.pi fun _ : Yt => R.labels.μ) +
        R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y hw * blockBondScores (R := R) W V b Y *
          ∫ ω, R.labelWeight (n * R.params.side) W Yt ω ∂(Measure.pi fun _ : Yt => R.labels.μ)) := by
    intro Yt hY b
    have hh := (Finset.mem_filter.mp hY).2
    have e : ∀ ω, fullPart (caseResponse A V Y hw) V Yt b (W, ω) = stepTransitionDensity R.params R.coupling W b V *
        (∑ z ∈ sitesInBlocks R.params.side {Y}, A.hull (n * R.params.side) z W Yt ω hw * R.labelWeight (n * R.params.side) W Yt ω +
          R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y hw * blockBondScores (R := R) W V b Y *
            R.labelWeight (n * R.params.side) W Yt ω) := fun ω => by
      unfold fullPart
      rw [if_pos (show IsHullState R.params (clusterRange R.coupling) (W, ω).1 Yt from hh)]
      by_cases hl : IsLiveState R.params R.coupling R.labelWeight W Yt ω
      · have e2 : live (caseResponse A V Y hw) Yt ∅ b (W, ω) =
            ∑ z ∈ sitesInBlocks R.params.side {Y}, A.hull (n * R.params.side) z W Yt ω hw +
            R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y hw * blockBondScores (R := R) W V b Y := by
          unfold live
          rw [if_pos (show IsLiveState R.params R.coupling R.labelWeight (W, ω).1 Yt (W, ω).2 from hl)]
          rfl
        rw [e2, ← Finset.sum_mul]
        show R.labelWeight (n * R.params.side) W Yt ω * stepTransitionDensity R.params R.coupling W b V * _ = _
        ring
      · have h0 : R.labelWeight (n * R.params.side) W Yt ω = 0 :=
          le_antisymm (not_lt.mp fun hp => hl ⟨hh, hp⟩) (h.forms.hasExpansions.2.nonneg _ hb W Yt ω hh)
        show R.labelWeight (n * R.params.side) W Yt ω * stepTransitionDensity R.params R.coupling W b V * _ = _
        rw [h0]
        simp
    rw [integral_congr_ae (ae_of_all _ e), integral_const_mul,
      integral_add (integrable_finsetSum _ fun z _ => hull_integrable h hb hh z hw) ((labelWeight_integrable h hb hh).const_mul _),
      integral_finsetSum _ (fun z _ => hull_integrable h hb hh z hw), integral_const_mul]
  have hoff : ∀ Yt ∉ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W), ∀ b : BaseChoice R.params.side n,
      ∫ ω, fullPart (caseResponse A V Y hw) V Yt b (W, ω) ∂(Measure.pi fun _ : Yt => R.labels.μ) = 0 := by
    intro Yt hY b
    have hh : ¬ IsHullState R.params (clusterRange R.coupling) W Yt := fun x => hY (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x⟩)
    have e : ∀ ω, fullPart (caseResponse A V Y hw) V Yt b (W, ω) = 0 := fun ω => by
      unfold fullPart
      rw [if_neg (show ¬ IsHullState R.params (clusterRange R.coupling) (W, ω).1 Yt from hh)]
    simp [e]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W)))
    (fun Yt _ hY => Finset.sum_eq_zero fun b _ => hoff Yt hY b)]
  rw [Finset.sum_congr rfl fun Yt hY => Finset.sum_congr rfl fun b _ => hval Yt hY b, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum, real_sum h hb W]
  have e3 : ∀ z ∈ sitesInBlocks R.params.side {Y}, (∑ Yt ∈ Finset.univ.filter (IsHullState R.params (clusterRange R.coupling) W),
      ∫ ω, A.hull (n * R.params.side) z W Yt ω hw * R.labelWeight (n * R.params.side) W Yt ω ∂(Measure.pi fun _ : Yt => R.labels.μ)) =
      R.functional (n * R.params.side) W * rO (n * R.params.side) z W hw := fun z _ => (tie _ hb z W hw).symm
  rw [Finset.sum_congr rfl e3, ← Finset.mul_sum]
  ring
private theorem case_sum_value (h : Holds R A) (hn : R.params.n₀ ≤ n) {rO : ColdResponse R.params.side R.depth} (tie : Tie R A rO)
    (C : Finset (TorusSite n)) (V : TorusField n) (Y : TorusSite n) (hw : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    caseSum C V (caseResponse A V Y hw) = ∫ W, R.functional (n * R.params.side) W * ∑ b : BaseChoice R.params.side n,
      stepTransitionDensity R.params R.coupling W b V *
      (∑ z ∈ sitesInBlocks R.params.side {Y}, rO (n * R.params.side) z W hw +
        R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y hw * blockBondScores (R := R) W V b Y)
      ∂(fieldHaar (n * R.params.side)) := by
  have hT := tame_response h hn V Y hw
  have hI : ∀ W Yt ω (bad bad' : Finset (TorusBond (n * R.params.side))) b,
      caseResponse A V Y hw W Yt ω bad b = caseResponse A V Y hw W Yt ω bad' b := fun _ _ _ _ _ _ => rfl
  have hfi := fun (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) =>
    full_integrable h hn hT hI C V Yt b
  unfold caseSum
  rw [Finset.sum_comm]
  calc _ = ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n, ∫ W, ∫ ω,
        fullPart (caseResponse A V Y hw) V Yt b (W, ω) ∂(Measure.pi fun _ : Yt => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
        refine Finset.sum_congr rfl fun Yt _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [sum_bad_integral h hn hT hI C V Yt b, integral_prod _ (hfi Yt b)]
    _ = ∫ W, ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n, ∫ ω,
        fullPart (caseResponse A V Y hw) V Yt b (W, ω) ∂(Measure.pi fun _ : Yt => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
        rw [integral_finsetSum _ fun Yt _ => integrable_finsetSum _ fun b _ => (hfi Yt b).integral_prod_left]
        refine Finset.sum_congr rfl fun Yt _ => ?_
        rw [integral_finsetSum _ fun b _ => (hfi Yt b).integral_prod_left]
    _ = _ := integral_congr_ae (ae_of_all _ fun W => section_value h hn tie V Y hw W)
private theorem cold_eq (h : Holds R A) (hn : R.params.n₀ ≤ n) {rO : ColdResponse R.params.side R.depth} (tie : Tie R A rO)
    (V : TorusField n) (Y : TorusSite n) (hw : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    A.coldStep n Y V hw = stepColdResponse R.params R.coupling A.coeff R.depth R.functional rO n Y V hw := by
  have hT := tame_response h hn V Y hw
  have e : coarseStateWeight R ∅ V (emptyCoarseState R) = kernelImage R.params R.coupling R.functional n V :=
    (h.inputs.cold R h.forms n hn).1 V (emptyCoarseState R).2
  show caseMean R ∅ V (emptyCoarseState R) (caseResponse A V Y hw) = _
  unfold caseMean
  rw [cold_total h hn hT, case_sum_value h hn tie ∅ V Y hw, e]
  rfl
end Value
section Levels
variable {ℓ : TorusLumps.StepParameters}
private theorem tie_step (hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup) (lam x'' : ℝ) (c : ChainStage ℓ)
    (A : ResponseSetup c.toStepSetup) (h : Holds c.toStepSetup A) (rO : ColdResponse ℓ.side c.depth) (tie : Tie c.toStepSetup A rO)
    (al' : ℝ) (Ra Rb : LocalDensity) :
    Tie (nextStage hL lam x'' c).toStepSetup (nextResponseSetup hL lam x'' A al' Ra Rb)
      (stepColdResponse ℓ c.coupling A.coeff c.depth c.functional rO) := by
  classical
  intro m _ hm Y V hw
  have hLpos : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn : ℓ.n₀ ≤ m := le_trans (Nat.le_mul_of_pos_left _ hLpos) hm.2
  have hT := tame_response (R := c.toStepSetup) (A := A) h hn V Y hw
  have hm' : IsBlockTorusSide c.toStepSetup.params m := hm
  have hrhs : (∑ Y' ∈ Finset.univ.filter (IsHullState ℓ (clusterRange c.nextCoupling) V),
      ∫ ω, A.hullStep m Y V Y' ω hw * coarseWeightExpansion c.toStepSetup m V Y' ω
        ∂(Measure.pi fun _ : Y' => coarseLabelMeasure c.labels.μ ℓ.side)) =
      caseSum (hotCoreSites c.toStepSetup V) V (caseResponse A V Y hw) := by
    rw [← hull_total h hn hT hm']
    refine Finset.sum_congr rfl fun Y' _ => integral_congr_ae (ae_of_all _ fun ω => ?_)
    have e : coarseWeightExpansion c.toStepSetup m V Y' ω = coarseStateWeight c.toStepSetup (hotCoreSites c.toStepSetup V) V ⟨Y', ω⟩ := by
      simp [coarseWeightExpansion, NeZero.ne m]
    exact congrArg (fun u => caseMean c.toStepSetup (hotCoreSites c.toStepSetup V) V ⟨Y', ω⟩ (caseResponse A V Y hw) * u) e
  show kernelImage ℓ c.coupling c.functional m V * stepColdResponse ℓ c.coupling A.coeff c.depth c.functional rO m Y V hw =
    ∑ Y' ∈ Finset.univ.filter (IsHullState ℓ (clusterRange c.nextCoupling) V),
      ∫ ω, A.hullStep m Y V Y' ω hw * coarseWeightExpansion c.toStepSetup m V Y' ω
        ∂(Measure.pi fun _ : Y' => coarseLabelMeasure c.labels.μ ℓ.side)
  rw [hrhs]
  by_cases hD : kernelImage ℓ c.coupling c.functional m V = 0
  · rw [hD, zero_mul, sum_at_zero h hn hT hD]
  · rw [case_sum_value h hn tie _ V Y hw]
    show kernelImage ℓ c.coupling c.functional m V * (_ / kernelImage ℓ c.coupling c.functional m V) = _
    rw [mul_div_cancel₀ _ hD]
    rfl
private theorem tie_first {R : StepSetup} {A : ResponseSetup R} (h : Holds R A) (rO : ColdResponse R.params.side R.depth)
    (hQ : ∀ (m : ℕ) [NeZero m] (y : TorusSite m) (W : TorusField m) (Yt : Finset (TorusSite m)) (ω : Yt → R.labels.Ω)
      (hw : PlaquetteWeight (fineSide R.params.side R.depth m)), A.hull m y W Yt ω hw = rO m y W hw) : Tie R A rO := by
  classical
  intro m _ hm y W hw
  have e : ∀ Yt : Finset (TorusSite m), ∫ ω, A.hull m y W Yt ω hw * R.labelWeight m W Yt ω ∂(Measure.pi fun _ : Yt => R.labels.μ) =
      rO m y W hw * ∫ ω, R.labelWeight m W Yt ω ∂(Measure.pi fun _ : Yt => R.labels.μ) := fun Yt => by
    simp_rw [hQ]
    exact integral_const_mul _ _
  simp_rw [e]
  rw [← Finset.mul_sum, real_sum h hm W, mul_comm]
private def castResponse {L t t' : ℕ} (e : t = t') (rO : ColdResponse L t) : ColdResponse L t' := e ▸ rO
private def Tied (z : StageWithResponse ℓ) (t : ℕ) (rO : ColdResponse ℓ.side t) : Prop :=
  ∃ e : t = z.1.depth, Tie z.1.toStepSetup z.2 (castResponse e rO) ∧
    ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n) (hw : PlaquetteWeight (fineSide ℓ.side z.1.depth n)),
      z.2.cold n y W hw = castResponse e rO n y W hw
private theorem tied_next (hL : ∀ c : ChainStage ℓ, CoarseLabelFacts c.toStepSetup) (lam x'' : ℝ) (z : StageWithResponse ℓ)
    (t : ℕ) (rO : ColdResponse ℓ.side t) (ht : Tied z t rO) (h : Holds z.1.toStepSetup z.2) :
    Tied (nextStageWithResponse hL lam x'' z) (t + 1) (stepColdResponse ℓ z.1.coupling z.2.coeff t z.1.functional rO) := by
  obtain ⟨e, tie, -⟩ := ht
  subst e
  exact ⟨rfl, tie_step hL lam x'' z.1 z.2 h rO tie _ _ _, fun n _ hn Y V hw => cold_eq h hn tie V Y hw⟩
private theorem bounds_of_tied (z : StageWithResponse ℓ) (t : ℕ) (rO : ColdResponse ℓ.side t) (ht : Tied z t rO)
    (K : ResponseParameters) (x al : ℝ) (hK : z.2.responseParams = K) (hx : z.1.coupling = x) (hal : z.2.coeff = al)
    (hr : z.2.IsAdmissible) :
    ∃ Ra Rb : LocalDensity, ColdResponseBounds ℓ K t x al rO Ra Rb := by
  obtain ⟨e, -, hP⟩ := ht
  subst e
  subst hK
  subst hx
  subst hal
  have hP' : ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n)
      (hw : PlaquetteWeight (fineSide ℓ.side z.1.depth n)), z.2.cold n y W hw = rO n y W hw := hP
  have row := hr.bounds
  have hat : ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n)
      (hw : PlaquetteWeight (fineSide ℓ.side z.1.depth n)),
      centeredResponse rO n y W hw = centeredResponse z.2.cold n y W hw := fun n _ hn y W hw => by
    unfold centeredResponse
    rw [hP' n hn, hP' n hn]
  have rem : ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (hw : PlaquetteWeight (fineSide ℓ.side z.1.depth n)),
      responseRemainder rO n y hw = responseRemainder z.2.cold n y hw := fun n _ hn y hw => by
    funext W
    unfold responseRemainder
    rw [hP' n hn, hP' n hn]
  have hrem : ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (hw : PlaquetteWeight (fineSide ℓ.side z.1.depth n)),
      centeredRemainder rO n y hw = centeredRemainder z.2.cold n y hw := fun n _ hn y hw => by
    funext W
    unfold centeredRemainder
    rw [rem n hn]
  refine ⟨z.2.siteRemainder, z.2.totalRemainder, ?_⟩
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
variable {T : RenormalizationStepParameters.ParameterAssignment} {y β : ℝ} {K : ResponseParameters}
private theorem flow_tied (inputs : Inputs) (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup)
    (z₀ : StageWithResponse (T.stepParameters y)) (s : ℕ) (hz : IsInitialStage T y β z₀)
    (hs : StagesOnFlowUpTo T K y β hL z₀ s)
    (hF : ∀ t ≤ s, (flowStages T y β hL z₀ t).1.toStepSetup.IsWellPosed) (t : ℕ) (ht : t ≤ s) :
    Tied (flowStages T y β hL z₀ t) t (coldResponseChain (T.stepParameters y) β (flowCouplings (T.stepParameters y) β)
        (fun j => (flowStages T y β hL z₀ j).2.coeff) t) ∧
      (flowStages T y β hL z₀ t).1.functional =
        chainFunctional (T.stepParameters y) β (flowCouplings (T.stepParameters y) β) t := by
  induction t with
  | zero =>
    refine ⟨?_, hz.functional_eq⟩
    have h0 : Holds z₀.1.toStepSetup z₀.2 := ⟨inputs, hF 0 ht, (hs 0 ht).onFamily.admissible⟩
    obtain ⟨K', f, Λ, Dq, Φ, φ, rfl⟩ := hz.isWilson
    exact ⟨rfl, tie_first h0 _ fun m _ y W Yt ω hw => rfl, fun n _ _ y W hw => rfl⟩
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih (Nat.le_of_succ_le ht)
    have hst := hs t (Nat.le_of_succ_le ht)
    have h : Holds (flowStages T y β hL z₀ t).1.toStepSetup (flowStages T y β hL z₀ t).2 :=
      ⟨inputs, hF t (Nat.le_of_succ_le ht), hst.onFamily.admissible⟩
    have hx : flowCouplings (T.stepParameters y) β t = (flowStages T y β hL z₀ t).1.coupling := hst.coupling_eq.symm
    have hn := tied_next hL T.lam (couplingsAlongFlow (T.stepParameters y) β (t + 2)) (flowStages T y β hL z₀ t) t _ h1 h
    refine ⟨?_, ?_⟩
    · have e : coldResponseChain (T.stepParameters y) β (flowCouplings (T.stepParameters y) β)
            (fun j => (flowStages T y β hL z₀ j).2.coeff) (t + 1) =
          stepColdResponse (T.stepParameters y) (flowStages T y β hL z₀ t).1.coupling (flowStages T y β hL z₀ t).2.coeff t
            (flowStages T y β hL z₀ t).1.functional
            (coldResponseChain (T.stepParameters y) β (flowCouplings (T.stepParameters y) β)
              (fun j => (flowStages T y β hL z₀ j).2.coeff) t) := by
        rw [← hx, h2]
        rfl
      rw [e]
      exact hn
    · show kernelImage (T.stepParameters y) (flowStages T y β hL z₀ t).1.coupling (flowStages T y β hL z₀ t).1.functional =
        kernelImage (T.stepParameters y) (flowCouplings (T.stepParameters y) β t)
          (chainFunctional (T.stepParameters y) β (flowCouplings (T.stepParameters y) β) t)
      rw [← hx, h2]
end Levels
section Shift
variable {R : StepSetup} {A : ResponseSetup R} {n : ℕ} [NeZero n]
private theorem cold_zero (hI : A.IsAdmissible) {m : ℕ} [NeZero m] (hm : R.params.n₀ ≤ m) (y : TorusSite m)
    (f : PlaquetteWeight (fineSide R.params.side R.depth m)) (hy : ∀ p, IsPlaquetteAt R.params.side R.depth y p → f p = 0)
    (W : TorusField m) (hW : IsCold R.params.threshold W) : A.cold m y W f = 0 := by
  have h1 := hI.bounds.cold_reads m hm y W hW f 0 (fun p hp => by simpa using hy p hp)
  have h2 := hI.bounds.cold_linear m hm y W hW 1 0 0
  simp only [one_smul, add_zero, one_mul] at h2
  rw [h1]
  linarith
open Classical in
private theorem supportResponseSum_eq (hI : A.IsAdmissible) (hb : IsBlockTorusSide R.params (n * R.params.side)) (V : TorusField n)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) :
    supportResponseSum A V f W Yt ωt bad b =
      ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f, caseResponse A V Y f W Yt ωt bad b -
        ∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f, A.cold (n * R.params.side) y (trivialField _) f := by apply _root_.YangMills.SharedProofs.p27295 <;> assumption
private theorem live_congr {F G : CaseFunction R n}
    (hFG : ∀ W Yt ωt bad b, IsLiveState R.params R.coupling R.labelWeight W Yt ωt → F W Yt ωt bad b = G W Yt ωt bad b)
    (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    live F Yt bad b = live G Yt bad b := by
  classical
  funext p
  unfold live
  by_cases hl : IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2
  · rw [if_pos hl, if_pos hl, hFG _ _ _ _ _ hl]
  · rw [if_neg hl, if_neg hl]
private theorem tame_congr {F G : CaseFunction R n}
    (hFG : ∀ W Yt ωt bad b, IsLiveState R.params R.coupling R.labelWeight W Yt ωt → F W Yt ωt bad b = G W Yt ωt bad b)
    (hG : Tame A G) : Tame A F := by
  refine ⟨fun Yt bad b => ?_, ?_⟩
  · rw [live_congr hFG]
    exact hG.borel Yt bad b
  · obtain ⟨M, hM⟩ := hG.size
    exact ⟨M, fun W Yt ωt bad b hl => by
      rw [hFG W Yt ωt bad b hl]
      exact hM W Yt ωt bad b hl⟩
private theorem tame_add {F G : CaseFunction R n} (hF : Tame A F) (hG : Tame A G) :
    Tame A (fun a c d e g => F a c d e g + G a c d e g) := by
  classical
  refine ⟨fun Yt bad b => ?_, ?_⟩
  · have e : live (fun a c d e g => F a c d e g + G a c d e g) Yt bad b =
        fun p => live F Yt bad b p + live G Yt bad b p := by
      funext p
      unfold live
      split_ifs <;> simp
    rw [e]
    exact (hF.borel Yt bad b).add (hG.borel Yt bad b)
  · obtain ⟨M, hM⟩ := hF.size
    obtain ⟨N, hN⟩ := hG.size
    refine ⟨M + N, fun W Yt ωt bad b hl => ?_⟩
    rw [add_mul]
    exact (abs_add_le _ _).trans (add_le_add (hM W Yt ωt bad b hl) (hN W Yt ωt bad b hl))
private theorem tame_const (h : Holds R A) (hb : IsBlockTorusSide R.params (n * R.params.side)) (c : ℝ) :
    Tame A (fun _ _ _ _ _ => c : CaseFunction R n) := by
  classical
  refine ⟨fun Yt bad b => ?_, |c|, fun W Yt ωt bad b hl => ?_⟩
  · exact Measurable.ite (live_measurable h hb Yt) measurable_const measurable_const
  · exact le_mul_of_one_le_right (abs_nonneg _) (exp_ge_one h ωt)
private theorem tame_sum {κ : Type} (S : Finset κ) {F : κ → CaseFunction R n} (h : Holds R A)
    (hb : IsBlockTorusSide R.params (n * R.params.side)) (hF : ∀ k ∈ S, Tame A (F k)) :
    Tame A (fun a c d e g => ∑ k ∈ S, F k a c d e g) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using tame_const h hb 0
  | insert k S hk ih =>
    have := tame_add (hF k (Finset.mem_insert_self _ _)) (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))
    refine tame_congr (fun W Yt ωt bad b _ => ?_) this
    rw [Finset.sum_insert hk]
private theorem product_add (F G : CaseFunction R n) (C : Finset (TorusSite n)) (V : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) :
    product C V (fun a c d e g => F a c d e g + G a c d e g) bad Yt b p =
      product C V F bad Yt b p + product C V G bad Yt b p := by
  classical
  unfold product live
  by_cases hl : IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2
  · simp only [if_pos hl]
    ring
  · simp only [if_neg hl]
    ring
private theorem sum_add (h : Holds R A) (hn : R.params.n₀ ≤ n) {F G : CaseFunction R n} (hF : Tame A F) (hG : Tame A G)
    (C : Finset (TorusSite n)) (V : TorusField n) :
    caseSum C V (fun a c d e g => F a c d e g + G a c d e g) = caseSum C V F + caseSum C V G := by
  unfold caseSum
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun bad _ => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← integral_add (product_integrable h hn hF) (product_integrable h hn hG)]
  exact integral_congr_ae (ae_of_all _ fun p => product_add F G C V bad Yt b p)
private theorem sum_congr_live {F G : CaseFunction R n}
    (hFG : ∀ W Yt ωt bad b, IsLiveState R.params R.coupling R.labelWeight W Yt ωt → F W Yt ωt bad b = G W Yt ωt bad b)
    (C : Finset (TorusSite n)) (V : TorusField n) : caseSum C V F = caseSum C V G := by
  unfold caseSum
  refine Finset.sum_congr rfl fun bad _ => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ => ?_
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  unfold product
  rw [live_congr hFG]
private theorem sum_zero (C : Finset (TorusSite n)) (V : TorusField n) :
    caseSum C V (fun _ _ _ _ _ => 0 : CaseFunction R n) = 0 := by
  classical
  unfold caseSum
  refine Finset.sum_eq_zero fun bad _ => Finset.sum_eq_zero fun Yt _ => Finset.sum_eq_zero fun b _ => ?_
  have e : ∀ p, product C V (fun _ _ _ _ _ => 0 : CaseFunction R n) bad Yt b p = 0 := fun p => by
    unfold product live
    split_ifs <;> simp
  simp [e]
private theorem sum_sum {κ : Type} (S : Finset κ) {F : κ → CaseFunction R n} (h : Holds R A) (hn : R.params.n₀ ≤ n)
    (hF : ∀ k ∈ S, Tame A (F k)) (C : Finset (TorusSite n)) (V : TorusField n) :
    caseSum C V (fun a c d e g => ∑ k ∈ S, F k a c d e g) = ∑ k ∈ S, caseSum C V (F k) := by
  classical
  have hb := block_side h hn
  induction S using Finset.induction_on with
  | empty => simpa using sum_zero C V
  | insert k S hk ih =>
    have hS : ∀ j ∈ S, Tame A (F j) := fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have e : caseSum C V (fun a c d e g => ∑ j ∈ insert k S, F j a c d e g) =
        caseSum C V (fun a c d e g => F k a c d e g + ∑ j ∈ S, F j a c d e g) :=
      sum_congr_live (fun W Yt ωt bad b _ => by rw [Finset.sum_insert hk]) C V
    rw [e, sum_add h hn (hF k (Finset.mem_insert_self _ _)) (tame_sum S h hb hS), ih hS, Finset.sum_insert hk]
private theorem product_const (h : Holds R A) (hn : R.params.n₀ ≤ n) (c : ℝ) (C : Finset (TorusSite n)) (V : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) :
    product C V (fun _ _ _ _ _ => c : CaseFunction R n) bad Yt b p = c * (configurationWeight R C V bad Yt b p.1 p.2).toReal := by
  classical
  unfold product live
  by_cases hl : IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2
  · rw [if_pos hl, mul_comm]
  · rw [if_neg hl, mul_zero]
    have e : configurationWeight R C V bad Yt b p.1 p.2 = 0 := by
      unfold configurationWeight
      by_cases hh : IsHullState R.params R.range p.1 Yt
      · rw [if_pos hh, weight_zero h hn p.1 p.2 hh hl]
        simp
      · rw [if_neg hh]
    rw [e]
    simp
private theorem sum_const (h : Holds R A) (hn : R.params.n₀ ≤ n) (c : ℝ) (C : Finset (TorusSite n)) (V : TorusField n)
    (hD : 0 ≤ kernelImage R.params R.coupling R.functional n V) :
    caseSum C V (fun _ _ _ _ _ => c : CaseFunction R n) = c * kernelImage R.params R.coupling R.functional n V := by
  classical
  have fin : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      ∫⁻ W, ∫⁻ ω : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ω
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) ≠ ⊤ :=
    fun bad Yt b => weight_finite h hn
  have e : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      ∫ p, product C V (fun _ _ _ _ _ => c : CaseFunction R n) bad Yt b p
        ∂((fieldHaar (n * R.params.side)).prod (Measure.pi fun _ : Yt => R.labels.μ)) =
      c * (∫⁻ W, ∫⁻ ω : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ω
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))).toReal := by
    intro bad Yt b
    have hm := h.inputs.borel R h.forms n hn C V bad Yt b
    have f1 := fin bad Yt b
    rw [← lintegral_prod (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      configurationWeight R C V bad Yt b p.1 p.2) hm.aemeasurable] at f1 ⊢
    rw [← integral_toReal hm.aemeasurable (ae_lt_top hm f1), ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun p => product_const h hn c C V bad Yt b p)
  have tot := congrArg ENNReal.toReal (h.inputs.addUp R h.forms n hn C V)
  rw [ENNReal.toReal_ofReal hD] at tot
  unfold caseSum
  rw [← tot, ENNReal.toReal_sum (fun bad _ => ENNReal.sum_ne_top.2 fun Yt _ => ENNReal.sum_ne_top.2 fun b _ => fin bad Yt b),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun bad _ => ?_
  rw [ENNReal.toReal_sum (fun Yt _ => ENNReal.sum_ne_top.2 fun b _ => fin bad Yt b), Finset.mul_sum]
  refine Finset.sum_congr rfl fun Yt _ => ?_
  rw [ENNReal.toReal_sum (fun b _ => fin bad Yt b), Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => e bad Yt b
private theorem mean_cold (h : Holds R A) (hn : R.params.n₀ ≤ n) {H : CaseFunction R n} (hT : Tame A H) (V : TorusField n) :
    caseMean R ∅ V (emptyCoarseState R) H = caseSum ∅ V H / kernelImage R.params R.coupling R.functional n V := by
  have e : coarseStateWeight R ∅ V (emptyCoarseState R) = kernelImage R.params R.coupling R.functional n V :=
    (h.inputs.cold R h.forms n hn).1 V (emptyCoarseState R).2
  unfold caseMean
  rw [cold_total h hn hT, e]
private theorem shift_eq (h : Holds R A) (hn : R.params.n₀ ≤ n)
    (hD : 0 < kernelImage R.params R.coupling R.functional n (trivialField n))
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    stepMeanShift A f = ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f, A.coldStep n Y (trivialField n) f -
      ∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f, A.cold (n * R.params.side) y (trivialField _) f := by
  classical
  have hb := block_side h hn
  set c := ∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f, A.cold (n * R.params.side) y (trivialField _) f
    with hc
  set S' := weightSupportSites R.params.side (R.depth + 1) n f with hS'
  have hT1 : ∀ Y ∈ S', Tame A (caseResponse A (trivialField n) Y f) := fun Y _ => tame_response h hn _ Y f
  have hTs := tame_sum S' h hb hT1
  have hTc := tame_const h hb (-c)
  have hFG : ∀ W Yt ωt bad b, IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
      supportResponseSum A (trivialField n) f W Yt ωt bad b =
        (fun a d e g k => (∑ Y ∈ S', caseResponse A (trivialField n) Y f a d e g k) + (-c)) W Yt ωt bad b :=
    fun W Yt ωt bad b hl => by
      rw [supportResponseSum_eq h.resp hb _ f W Yt ωt bad b hl]
      ring
  have hTF : Tame A (supportResponseSum A (trivialField n) f) := tame_congr hFG (tame_add hTs hTc)
  have hne : kernelImage R.params R.coupling R.functional n (trivialField n) ≠ 0 := hD.ne'
  show caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) = _
  rw [mean_cold h hn hTF, sum_congr_live hFG, sum_add h hn hTs hTc, sum_sum S' h hn hT1, sum_const h hn _ _ _ hD.le]
  have e : ∀ Y, A.coldStep n Y (trivialField n) f =
      caseSum ∅ (trivialField n) (caseResponse A (trivialField n) Y f) / kernelImage R.params R.coupling R.functional n (trivialField n) :=
    fun Y => mean_cold h hn (tame_response h hn _ Y f) _
  simp_rw [e]
  rw [← Finset.sum_div]
  field_simp
  ring
end Shift
section Tower
variable {T : RenormalizationStepParameters.ParameterAssignment} {y β : ℝ} {K : ResponseParameters}
private theorem trivial_cold {ℓ : TorusLumps.StepParameters} (hσ : 0 < ℓ.threshold) (n : ℕ) : IsCold ℓ.threshold (trivialField n) := by apply _root_.YangMills.Construction.TorusLumps.DensityExpansion.trivialField_isCold <;> assumption
private theorem shift_along (inputs : Inputs) (hσ : 0 < (T.stepParameters y).threshold)
    (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup)
    (z₀ : StageWithResponse (T.stepParameters y)) (s : ℕ) (hz : IsInitialStage T y β z₀) (hs : StagesOnFlowUpTo T K y β hL z₀ s)
    (hF : ∀ t ≤ s, (flowStages T y β hL z₀ t).1.toStepSetup.IsWellPosed) (t : ℕ) (ht : t ≤ s) :
    ∀ (n : ℕ) [NeZero n], (T.stepParameters y).n₀ ≤ n →
      ∀ f : StageWeight hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ t n,
      accumulatedShift hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ t n f =
        ∑ u ∈ weightSupportSites (T.stepParameters y).side (flowStages T y β hL z₀ t).1.toStepSetup.depth n f,
          (flowStages T y β hL z₀ t).2.cold n u (trivialField n) f := by
  induction t with
  | zero =>
    intro n _ hn f
    obtain ⟨K', f', Λ, Dq, Φ, φ, rfl⟩ := hz.isWilson
    refine (Finset.sum_eq_zero fun u _ => ?_).symm
    show siteResponse u (trivialField n) f = 0
    have he : ∀ p : TorusPlaquette n, plaquetteEnergyOf (trivialField n) p = 0 := fun p => by
      simp only [plaquetteEnergyOf, plaquetteEnergy, holonomy_trivialField]
      exact sub_self (1 : ℝ)
    simp [siteResponse, he]
  | succ t ih =>
    intro n _ hn f
    have ht' : t ≤ s := Nat.le_of_succ_le ht
    have hAt : Holds (flowStages T y β hL z₀ t).1.toStepSetup (flowStages T y β hL z₀ t).2 :=
      ⟨inputs, hF t ht', (hs t ht').onFamily.admissible⟩
    have hD : 0 < kernelImage (T.stepParameters y) (flowStages T y β hL z₀ t).1.coupling
        (flowStages T y β hL z₀ t).1.functional n (trivialField n) :=
      (hF (t + 1) ht).hasExpansions.1.positive n hn (trivialField n) (trivial_cold hσ n)
    have hLpos : 0 < (T.stepParameters y).side := Nat.pos_of_ne_zero (NeZero.ne _)
    have e1 := ih ht' (n * (T.stepParameters y).side) (le_trans hn (Nat.le_mul_of_pos_right _ hLpos)) f
    have e2 := shift_eq hAt hn hD f
    show accumulatedShift hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ t (n * (T.stepParameters y).side) f +
      stepMeanShift (stageResponse hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ t) f = _
    rw [e1]
    erw [e2]
    show _ = ∑ u ∈ weightSupportSites (T.stepParameters y).side ((flowStages T y β hL z₀ t).1.toStepSetup.depth + 1) n f,
      (flowStages T y β hL z₀ t).2.coldStep n u (trivialField n) f
    ring
private theorem cast_weight {L t t' : ℕ} (e : t = t') (rO : ColdResponse L t) (w : (m : ℕ) → PlaquetteWeight m) (n : ℕ) [NeZero n]
    (u : TorusSite n) (W : TorusField n) :
    castResponse e rO n u W (w (fineSide L t' n)) = rO n u W (w (fineSide L t n)) := by
  subst e
  rfl
private theorem mean_is_shift (inputs : Inputs) (hσ : 0 < (T.stepParameters y).threshold)
    (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup)
    (z₀ : StageWithResponse (T.stepParameters y)) (s : ℕ) (hz : IsInitialStage T y β z₀) (hs : StagesOnFlowUpTo T K y β hL z₀ s)
    (hF : ∀ t ≤ s, (flowStages T y β hL z₀ t).1.toStepSetup.IsWellPosed) (n : ℕ) [NeZero n] (w : (m : ℕ) → PlaquetteWeight m)
    (hb : IsBlockTorusSide (T.stepParameters y) n) :
    meanAtTrivial (T.stepParameters y) β (fun j => (flowStages T y β hL z₀ j).2.coeff) s n (w _) =
      accumulatedShift hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ s n (w _) := by
  classical
  have hLpos : 0 < (T.stepParameters y).side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn : (T.stepParameters y).n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hLpos) hb.2
  obtain ⟨⟨e, -, hP⟩, -⟩ := flow_tied inputs hL z₀ s hz hs hF s le_rfl
  rw [shift_along inputs hσ hL z₀ s hz hs hF s le_rfl n hn]
  have hI := (hs s le_rfl).onFamily.admissible
  rw [Finset.sum_subset (Finset.subset_univ _) fun u _ hu => cold_zero hI hn u _ (fun p hp => by
    by_contra hne
    exact hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, hp, hne⟩)) (trivialField n) (trivial_cold hσ n)]
  unfold meanAtTrivial
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hP n hn u (trivialField n) (w _)]
  exact (cast_weight e _ w n u (trivialField n)).symm
private theorem coldResponseChain_congr (ℓ : TorusLumps.StepParameters) (β : ℝ) (x : ℕ → ℝ) {al al' : ℕ → ℝ} :
    ∀ t : ℕ, (∀ i < t, al i = al' i) → coldResponseChain ℓ β x al t = coldResponseChain ℓ β x al' t
  | 0, _ => rfl
  | t + 1, h => by
    show stepColdResponse ℓ (x t) (al t) t (chainFunctional ℓ β x t) (coldResponseChain ℓ β x al t) =
      stepColdResponse ℓ (x t) (al' t) t (chainFunctional ℓ β x t) (coldResponseChain ℓ β x al' t)
    rw [h t (Nat.lt_succ_self t), coldResponseChain_congr ℓ β x t fun i hi => h i (Nat.lt_succ_of_lt hi)]
private theorem shares_of_stage (hT : T.Admissible) (hy : T.floorMin ≤ y) (t : ℕ)
    (hSh : LevelSharesFormCurvatureFamily)
    (hForm : HasCurvatureForm (levelShareFamily T.coupling T.side (t + 1)) 1) (hFlat : flatTopVanishingStatement) :
    LevelShareBounds (T.stepParameters y) t (weightGrowthSup T.rt T.n₁ * maxOfFirstFour T.N) := by
  obtain ⟨h₁, -, h₃⟩ := hSh T hT y hy t
  have hfit := hT.fits y hy
  refine ⟨h₁, hForm, h₃, fun n _ _ z => ?_⟩
  exact (hFlat (torusFrame T.side t n) T.coupling (cellsOfSites (torusFrame T.side t n) Finset.univ)
    (by have : (1 : ℝ) ≤ T.coupling := hfit.a_ge; linarith) hfit.L_odd).2.2 _
private theorem coeff_is_stage (inputs : Inputs) (hOne : ColdResponseCoeffUniqueStatement)
    (hSh : LevelSharesFormCurvatureFamily) (hFm : LevelSharesHaveUnitCurvatureForm) (hFlat : flatTopVanishingStatement)
    (hCar : responseIsometryInvariantStatement) (hT : T.Admissible) (hy : T.floorMin ≤ y)
    (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup)
    (z₀ : StageWithResponse (T.stepParameters y)) (s : ℕ) (hz : IsInitialStage T y β z₀) (hs : StagesOnFlowUpTo T K y β hL z₀ s)
    (hF : ∀ t ≤ s, (flowStages T y β hL z₀ t).1.toStepSetup.IsWellPosed) (al : ℕ → ℝ)
    (hal : IsChainResponseCoeff (T.stepParameters y) K β s al) (t : ℕ) :
    t ≤ s → al t = (flowStages T y β hL z₀ t).2.coeff := by
  have hfit := hT.fits y hy
  have hK : K.Admissible (T.stepParameters y) := by
    have h0 := (hs 0 (Nat.zero_le _)).onFamily.admissible.params_admissible
    rw [(hs 0 (Nat.zero_le _)).params_eq] at h0
    exact h0
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    cases t with
    | zero => rw [hal.zero_eq]; exact hz.coeff_eq.symm
    | succ j =>
      have hsame := coldResponseChain_congr (T.stepParameters y) β (flowCouplings (T.stepParameters y) β) (al := al)
        (al' := fun i => (flowStages T y β hL z₀ i).2.coeff) (j + 1) fun i hi => ih i hi (by omega)
      obtain ⟨Ra, Rb, c⟩ := hal.bounds (j + 1) ht
      obtain ⟨Ra', Rb', c'⟩ := bounds_of_tied _ (j + 1) _ (flow_tied inputs hL z₀ s hz hs hF (j + 1) ht).1 K
        (flowCouplings (T.stepParameters y) β (j + 1)) _ (hs (j + 1) ht).params_eq (hs (j + 1) ht).coupling_eq rfl
        (hs (j + 1) ht).onFamily.admissible
      rw [hsame] at c
      have hx : 0 < flowCouplings (T.stepParameters y) β (j + 1) := by
        have h1 := (hF (j + 1) ht).coupling_pos
        have h2 := (hs (j + 1) ht).coupling_eq
        show 0 < couplingsAlongFlow (T.stepParameters y) β (j + 1)
        rw [← h2]
        exact h1
      exact hOne T hT y hy K j _ _ _ _ _ Ra Rb Ra' Rb' hK.η₃_pos hK.η₃_le hK.Kb_nonneg hx
        (shares_of_stage hT hy j hSh (hFm T hT j) hFlat) (hSh T hT y hy j).2.1
        (fun n _ hn g y' W W' _ hc => hCar (T.stepParameters y) hfit β _ _ (j + 1) n hn g W W' _ _ y' hc fun _ _ _ => rfl) c c'
end Tower
end CentringProof
open CentringProof in
theorem centringEqSumShifts_holds (hc : ConfigurationMassWithFunction) (ho : ConfigurationSupportedOnCoarseHull)
    (hb : ConfigurationWeightMeasurable) (ha : ConfigurationWeightsSum) (hh : CoarseHullIsHullState)
    (hC : coldFieldStateStatement) (hm : ScoredMassStatement) (hs : BondScoreProperties)
    (hd : StepTransitionDensityBounds) (hf : StagesAreWellPosed) (hOne : ColdResponseCoeffUniqueStatement)
    (hSh : LevelSharesFormCurvatureFamily) (hFm : LevelSharesHaveUnitCurvatureForm) (hFlat : flatTopVanishingStatement)
    (hCar : responseIsometryInvariantStatement) : centringEqSumShiftsStatement := by
  have inputs : Inputs := ⟨hc, ho, hb, ha, hh, hC, hm, hs, hd⟩
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ Kr => ?_⟩
  obtain ⟨y₁, hy₁⟩ := hf T hT
  refine ⟨max y₁ T.floorMin, fun y hy β hL z₀ hz s hst => ?_⟩
  have hy₀ : T.floorMin ≤ y := (le_max_right _ _).trans hy
  have hF := hy₁ y ((le_max_left _ _).trans hy) Kr β hL z₀ hz s hst
  exact ⟨fun al hal t ht => coeff_is_stage inputs hOne hSh hFm hFlat hCar hT hy₀ hL z₀ s hz hst hF al hal t ht,
    fun n _ w hb' => mean_is_shift inputs (hT.fits y hy₀).σ_pos hL z₀ s hz hst hF n w hb'⟩
end YangMills.Construction.SmallTorusCopies
end
