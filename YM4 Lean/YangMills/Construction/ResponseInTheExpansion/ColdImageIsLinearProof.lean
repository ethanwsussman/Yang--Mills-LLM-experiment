import YangMills.Construction.ResponseInTheExpansion.ColdImageIsLinear
import YangMills.Construction.ResponseInTheExpansion.ImageResponseIsAMeanOfTheGas
import YangMills.Construction.ResponseInTheExpansion.MeansOfAWeight
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings StepCosts TorusFields TorusLumps StepGas RenormalizationStepParameters WeightedResponses BlockAverages
namespace ColdStepLinear
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem isBlockTorusSide_mul (hn : R.params.n₀ ≤ n) : IsBlockTorusSide R.params (n * R.params.side) :=
  ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
private theorem isLiveState_of_stepWeight_ne_zero (hexp : R.HasExpansions) (hn : R.params.n₀ ≤ n)
    {C : Finset (TorusSite n)} {V : TorusField n}
    {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω}
    {bad : Finset (TorusBond (n * R.params.side))}
    {b : BaseChoice R.params.side n} (hh : IsHullState R.params R.range W Yt)
    (hw : stepWeight R C V W Yt ωt bad b ≠ 0) :
    IsLiveState R.params R.coupling R.labelWeight W Yt ωt := by
  refine ⟨hh, lt_of_le_of_ne (hexp.2.nonneg (n * R.params.side) (isBlockTorusSide_mul hn) W Yt ωt hh) fun h0 => hw ?_⟩
  unfold stepWeight
  rw [← h0]
  ring
abbrev _root_.YangMills.SharedProofs.p23747 := @isLiveState_of_stepWeight_ne_zero
private theorem caseTerm_eq_smul_add {C : Finset (TorusSite n)} {V : TorusField n} {q : CoarseState R n}
    {F₁ F₂ F₃ : CaseFunction R n}
    (c : ℝ) (h : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
      (ωt : Yt → R.labels.Ω)
      (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
      IsHullState R.params R.range W Yt →
      stepWeight R C V W Yt ωt bad b ≠ 0 → F₃ W Yt ωt bad b = c * F₁ W Yt ωt bad b + F₂ W Yt ωt bad b)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n)
    (W : TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω) :
    caseTerm R C V q F₃ bad Yt b W ν =
      c * caseTerm R C V q F₁ bad Yt b W ν + caseTerm R C V q F₂ bad Yt b W ν := by
  classical
  unfold caseTerm
  by_cases hc : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
      coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q
  · rw [if_pos hc, if_pos hc, if_pos hc]
    by_cases hw : stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = 0
    · simp [hw]
    · rw [h _ _ _ _ _ hc.1 hw]
      ring
  · simp [if_neg hc]
private theorem caseIntegral_eq_smul_add {C : Finset (TorusSite n)} {V : TorusField n} {q : CoarseState R n}
    {F₁ F₂ F₃ : CaseFunction R n} (c : ℝ) (h₁ : CaseIntegrable R C V q F₁) (h₂ : CaseIntegrable R C V q F₂)
    (h : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
      (ωt : Yt → R.labels.Ω)
      (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
      IsHullState R.params R.range W Yt →
      stepWeight R C V W Yt ωt bad b ≠ 0 → F₃ W Yt ωt bad b = c * F₁ W Yt ωt bad b + F₂ W Yt ωt bad b) :
    caseIntegral R C V q F₃ = c * caseIntegral R C V q F₁ + caseIntegral R C V q F₂ := by
  unfold caseIntegral
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun bad hbad => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ => ?_
  have e₁ := integral_prod _ (h₁ bad hbad Yt b)
  have e₂ := integral_prod _ (h₂ bad hbad Yt b)
  simp only at e₁ e₂
  rw [← e₁, ← e₂, ← integral_const_mul, ← integral_add ((h₁ bad hbad Yt b).const_mul c) (h₂ bad hbad Yt b)]
  have e₃ : (fun W => ∫ ν : q.unlabelled Yt → R.labels.Ω, caseTerm R C V q F₃ bad Yt b W ν
        ∂(Measure.pi fun _ => R.labels.μ)) =
      fun W => ∫ ν : q.unlabelled Yt → R.labels.Ω, (c * caseTerm R C V q F₁ bad Yt b W ν +
        caseTerm R C V q F₂ bad Yt b W ν) ∂(Measure.pi fun _ => R.labels.μ) := by
    funext W
    exact integral_congr_ae (Filter.Eventually.of_forall fun ν => caseTerm_eq_smul_add c h bad Yt b W ν)
  rw [e₃]
  exact (integral_prod (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
    c * caseTerm R C V q F₁ bad Yt b p.1 p.2 + caseTerm R C V q F₂ bad Yt b p.1 p.2)
    (((h₁ bad hbad Yt b).const_mul c).add (h₂ bad hbad Yt b))).symm
abbrev _root_.YangMills.SharedProofs.p59149 := @caseIntegral_eq_smul_add
private theorem caseIntegral_congr_of_weight {C : Finset (TorusSite n)} {V : TorusField n} {q : CoarseState R n}
    {F₁ F₂ : CaseFunction R n}
    (h : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
      (ωt : Yt → R.labels.Ω)
      (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
      IsHullState R.params R.range W Yt →
      stepWeight R C V W Yt ωt bad b ≠ 0 → F₁ W Yt ωt bad b = F₂ W Yt ωt bad b) :
    caseIntegral R C V q F₁ = caseIntegral R C V q F₂ := by
  unfold caseIntegral
  refine Finset.sum_congr rfl fun bad _ => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun ν => ?_)
  have := caseTerm_eq_smul_add (F₁ := F₂) (F₂ := fun _ _ _ _ _ => 0) (F₃ := F₁) (C := C) (V := V) (q := q) 1
    (fun W Yt ωt bad b hh hw => by rw [h W Yt ωt bad b hh hw]; ring) bad Yt b W ν
  simpa [caseTerm] using this
abbrev _root_.YangMills.SharedProofs.p114415 := @caseIntegral_congr_of_weight
private theorem caseResponse_smul_add (hW : BlockMeanIsLinearAndLocal) (hodd : Odd R.params.side)
    {A : ResponseSetup R} (hA : A.IsAdmissible) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (V : TorusField n) (y : TorusSite n) (c : ℝ)
    (h h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side)))
    (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) :
    caseResponse A V y (c • h + h') W Yt ωt bad b =
      c * caseResponse A V y h W Yt ωt bad b + caseResponse A V y h' W Yt ωt bad b := by
  have e : blockMean R.params.side (R.depth + 1) n y (c • h + h') =
      c * blockMean R.params.side (R.depth + 1) n y h + blockMean R.params.side (R.depth + 1) n y h' := by
    have h1 := (hW R.params.side hodd (R.depth + 1) n y).2.1 c 1 h h'
    have h2 : (fun p => c * h p + 1 * h' p) = c • h + h' := by
      funext p
      simp
    rw [h2, one_mul] at h1
    exact h1
  have e' : ∀ z ∈ sitesInBlocks R.params.side {y}, A.hull (n * R.params.side) z W Yt ωt (c • h + h') =
      c * A.hull (n * R.params.side) z W Yt ωt h + A.hull (n * R.params.side) z W Yt ωt h' := fun z _ =>
    hA.bounds.hull_linear (n * R.params.side) hside z W Yt ωt hl c h h'
  show ∑ z ∈ sitesInBlocks R.params.side {y}, A.hull (n * R.params.side) z W Yt ωt (c • h + h') +
      R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n y (c • h + h') *
        blockBondScores W V b y =
    c * (∑ z ∈ sitesInBlocks R.params.side {y}, A.hull (n * R.params.side) z W Yt ωt h +
      R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n y h * blockBondScores W V b y) +
    (∑ z ∈ sitesInBlocks R.params.side {y}, A.hull (n * R.params.side) z W Yt ωt h' +
      R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n y h' * blockBondScores W V b y)
  rw [Finset.sum_congr rfl e', Finset.sum_add_distrib, ← Finset.mul_sum, e]
  ring
abbrev _root_.YangMills.SharedProofs.p3179 := @caseResponse_smul_add
private theorem caseResponse_congr_local (hW : BlockMeanIsLinearAndLocal) (hodd : Odd R.params.side)
    {A : ResponseSetup R} (hA : A.IsAdmissible) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (V : TorusField n) (y : TorusSite n)
    (h h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (hh : ∀ p, IsPlaquetteAt R.params.side (R.depth + 1) y p → h p = h' p)
    (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
    (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) :
    caseResponse A V y h W Yt ωt bad b = caseResponse A V y h' W Yt ωt bad b := by
  have e : blockMean R.params.side (R.depth + 1) n y h = blockMean R.params.side (R.depth + 1) n y h' :=
    (hW R.params.side hodd (R.depth + 1) n y).2.2 h h' hh
  have e' : ∀ z ∈ sitesInBlocks R.params.side {y},
      A.hull (n * R.params.side) z W Yt ωt h = A.hull (n * R.params.side) z W Yt ωt h' := fun z hz =>
    hA.bounds.hull_reads (n * R.params.side) hside z W Yt ωt hl h h' fun p hp => hh p ⟨hp.1, by
      obtain ⟨c, hc, hcz⟩ := hp.2
      exact ⟨c, hc, Finset.mem_biUnion.mpr ⟨z, hz, hcz⟩⟩⟩
  show ∑ z ∈ sitesInBlocks R.params.side {y}, A.hull (n * R.params.side) z W Yt ωt h +
      R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n y h * blockBondScores W V b y =
    ∑ z ∈ sitesInBlocks R.params.side {y}, A.hull (n * R.params.side) z W Yt ωt h' +
      R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n y h' * blockBondScores W V b y
  rw [Finset.sum_congr rfl e', e]
abbrev _root_.YangMills.SharedProofs.p104861 := @caseResponse_congr_local
private theorem coldCaseGround_admissible (hfit : R.params.Admissible) (hn : R.params.n₀ ≤ n) {V : TorusField n}
    (hc : IsCold R.params.threshold V) :
    (coldCaseGround R V).IsAdmissibleGround :=
  Or.inl ⟨hn, fun x μ ν h => (hc x μ ν h).trans (by linarith [hfit.σ_pos]), rfl, rfl, rfl⟩
end ColdStepLinear
open ColdStepLinear in
theorem coldStepLinearLocal_holds (hI : coldStepIntegralEqGasMean) (hW : BlockMeanIsLinearAndLocal) :
    coldStepLinearLocalStatement := by
  classical
  obtain ⟨rt₀, hrt, hP⟩ := hI
  refine ⟨rt₀, hrt, fun T hT hr K => ?_⟩
  obtain ⟨y₀, hy⟩ := hP T hT hr K
  refine ⟨max y₀ T.floorMin, fun y hy' R A hK hA n _ hn Y V hV => ?_⟩
  have hint := hy y ((le_max_left _ _).trans hy') R A hK hA
  have hparams : R.params = T.stepParameters y := hA.onFamily.params_eq
  have hfit : R.params.Admissible := by
    rw [hparams]
    exact hT.fits y ((le_max_right _ _).trans hy')
  have hodd : Odd R.params.side := by
    rw [hparams]
    exact hT.L_odd
  have hexp : R.HasExpansions := hA.onFamily.isStep.1
  have hG : (coldCaseGround R V).IsAdmissibleGround := coldCaseGround_admissible hfit hn hV
  have hI' : ∀ h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n),
      CaseIntegrable R ∅ V (emptyCoarseState R) (caseResponse A V Y h) :=
    fun h => (hint n (coldCaseGround R V) hG Y h).1
  have hside := isBlockTorusSide_mul (R := R) hn
  have hr := hA.admissible
  refine ⟨fun c h h' => ?_, fun h h' hh => ?_⟩
  · show caseMean R ∅ V (emptyCoarseState R) _ =
      c * caseMean R ∅ V (emptyCoarseState R) _ + caseMean R ∅ V (emptyCoarseState R) _
    unfold caseMean
    rw [caseIntegral_eq_smul_add c (hI' h) (hI' h') fun W Yt ωt bad b hh hw =>
      caseResponse_smul_add hW hodd hr hside V Y c h h' W Yt ωt bad b
        (isLiveState_of_stepWeight_ne_zero hexp hn hh hw)]
    ring
  · show caseMean R ∅ V (emptyCoarseState R) _ = caseMean R ∅ V (emptyCoarseState R) _
    unfold caseMean
    rw [caseIntegral_congr_of_weight fun W Yt ωt bad b hs hw =>
      caseResponse_congr_local hW hodd hr hside V Y h h' hh W Yt ωt bad b
        (isLiveState_of_stepWeight_ne_zero hexp hn hs hw)]
end YangMills.Construction.ResponseInTheExpansion
end
