import YangMills.Construction.FreeEnergiesOfTheFlow.MeanOfTheVariableOfAStepProof
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStepIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepSettings StepGas ClusterExpansionOfAStep
def caseResponse_integrable : Prop :=
  HoldsAtEveryStep fun _ R A => R.IsWellPosed → ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ (y : TorusSite n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)),
      CaseIntegrable R G.cut G.coarse G.state (caseResponse A G.coarse y f)
end YangMills.Construction.WeightedResponses
end

set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings StepGas TorusFields TorusLumps WeightedResponses FreeEnergies RenormalizationStepParameters StepCosts
namespace CaseResponseIntegrable
private theorem holdsAtEveryStep_and {P Q : ParameterAssignment → ∀ R : StepSetup, ResponseSetup R → Prop}
    (hP : HoldsAtEveryStep P) (hQ : HoldsAtEveryStep Q) : HoldsAtEveryStep fun T R A => P T R A ∧ Q T R A := by apply _root_.YangMills.SharedProofs.p19358 <;> assumption
private theorem holdsAtEveryStep_mono {P Q : ParameterAssignment → ∀ R : StepSetup, ResponseSetup R → Prop}
    (hP : HoldsAtEveryStep P) (h : ∀ (T : ParameterAssignment) (y : ℝ) (R : StepSetup) (A : ResponseSetup R),
      OnStepParameters T y A → P T R A → Q T R A) : HoldsAtEveryStep Q := by
  obtain ⟨r, hr, hP⟩ := hP
  refine ⟨r, hr, fun T hT hrt K => ?_⟩
  obtain ⟨y₀, hy⟩ := hP T hT hrt K
  exact ⟨y₀, fun y hy' R A hK hA => h T y R A hA (hy y hy' R A hK hA)⟩
abbrev _root_.YangMills.SharedProofs.p66024 := @holdsAtEveryStep_mono
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem isBlockTorusSide_mul (hn : R.params.n₀ ≤ n) : IsBlockTorusSide R.params (n * R.params.side) :=
  ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
private theorem abs_blockBondScores_le (hsc : BondScoreProperties) (hfit : R.params.Admissible)
    (W : TorusField (n * R.params.side)) (V : TorusField n) (b : BaseChoice R.params.side n) (y : TorusSite n) :
    |blockBondScores (R := R) W V b y| ≤ 16 := by apply _root_.YangMills.SharedProofs.p16371 <;> assumption
private theorem siteScore_nonneg_of_admissible {A : ResponseSetup R} (hA : A.IsAdmissible)
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω) (z : TorusSite (n * R.params.side)) :
    0 ≤ siteScore A.score Yt ωt z := by
  classical
  unfold siteScore
  split_ifs
  · exact hA.price.nonneg _
  · exact le_rfl
private theorem abs_caseResponse_le (hsc : BondScoreProperties) (hfit : R.params.Admissible)
    {A : ResponseSetup R} (hA : A.IsAdmissible) (hn : R.params.n₀ ≤ n) (V : TorusField n) (y : TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
      (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
      IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
      |caseResponse A V y h W Yt ωt bad b| ≤
        K * Real.exp (scoreSumOn A (sitesInBlocks R.params.side {y}) Yt ωt) := by
  set sz : ℝ := weightNorm R.params.side R.depth
    (m := fineSide R.params.side R.depth (n * R.params.side)) h with hsz
  set c : ℝ := R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n y h with hc
  set P0 : TorusSite (n * R.params.side) → ℝ := fun z =>
    A.cold (n * R.params.side) z (trivialField (n * R.params.side)) h with hP0
  refine ⟨∑ z ∈ sitesInBlocks R.params.side {y}, (|P0 z| + |A.responseParams.C₀ * sz| + |sz|) + |c| * 16,
    add_nonneg (Finset.sum_nonneg fun z _ => by positivity) (by positivity), fun W Yt ωt bad b hl => ?_⟩
  set E : ℝ := Real.exp (scoreSumOn A (sitesInBlocks R.params.side {y}) Yt ωt) with hE
  have hsum0 : 0 ≤ scoreSumOn A (sitesInBlocks R.params.side {y}) Yt ωt :=
    Finset.sum_nonneg fun z _ => siteScore_nonneg_of_admissible hA Yt ωt z
  have hE1 : 1 ≤ E := Real.one_le_exp hsum0
  have hQ : ∀ z ∈ sitesInBlocks R.params.side {y}, |A.hull (n * R.params.side) z W Yt ωt h| ≤
      (|P0 z| + |A.responseParams.C₀ * sz| + |sz|) * E := by
    intro z hz
    have hs0 := siteScore_nonneg_of_admissible hA Yt ωt z
    have hsE : siteScore A.score Yt ωt z ≤ E := by
      have h1 : siteScore A.score Yt ωt z ≤ scoreSumOn A (sitesInBlocks R.params.side {y}) Yt ωt :=
        Finset.single_le_sum (f := fun z => siteScore A.score Yt ωt z)
          (fun z _ => siteScore_nonneg_of_admissible hA Yt ωt z) hz
      have h2 := Real.add_one_le_exp (scoreSumOn A (sitesInBlocks R.params.side {y}) Yt ωt)
      linarith
    have hb := hA.bounds.size_hull (n * R.params.side) (isBlockTorusSide_mul hn) z W Yt ωt hl h
    have e : A.hull (n * R.params.side) z W Yt ωt h =
        centeredHullResponse A.cold A.hull (n * R.params.side) z W Yt ωt h + P0 z := by
      simp [centeredHullResponse, hP0]
    have h3 : (A.responseParams.C₀ + siteScore A.score Yt ωt z) * sz ≤ |A.responseParams.C₀ * sz| + E * |sz| := by
      have h4 : A.responseParams.C₀ * sz ≤ |A.responseParams.C₀ * sz| := le_abs_self _
      have h5 : siteScore A.score Yt ωt z * sz ≤ E * |sz| :=
        (mul_le_mul_of_nonneg_left (le_abs_self sz) hs0).trans
          (mul_le_mul_of_nonneg_right hsE (abs_nonneg _))
      nlinarith
    have h6 := abs_add_le (centeredHullResponse A.cold A.hull (n * R.params.side) z W Yt ωt h) (P0 z)
    rw [← e] at h6
    have h7 : 0 ≤ |P0 z| := abs_nonneg _
    have h8 : 0 ≤ |A.responseParams.C₀ * sz| := abs_nonneg _
    nlinarith
  show |∑ z ∈ sitesInBlocks R.params.side {y}, A.hull (n * R.params.side) z W Yt ωt h +
    c * blockBondScores W V b y| ≤ _
  refine (abs_add_le _ _).trans ?_
  have h1 : |∑ z ∈ sitesInBlocks R.params.side {y}, A.hull (n * R.params.side) z W Yt ωt h| ≤
      (∑ z ∈ sitesInBlocks R.params.side {y}, (|P0 z| + |A.responseParams.C₀ * sz| + |sz|)) * E := by
    rw [Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hQ)
  have h2 : |c * blockBondScores W V b y| ≤ |c| * 16 * E := by
    rw [abs_mul]
    have h3 := mul_le_mul_of_nonneg_left (abs_blockBondScores_le hsc hfit W V b y) (abs_nonneg c)
    have h4 : 0 ≤ |c| * 16 := by positivity
    nlinarith
  rw [add_mul]
  exact add_le_add h1 h2
end CaseResponseIntegrable
open CaseResponseIntegrable in
theorem caseResponse_integrable_holds (hB : StepResponseMeasurable)
    (hF : labelFunctionsIntegrableStatement) (hsc : BondScoreProperties)
    (hlab : ClusterExpansionOfAStep.CoarseLabelsStandard) : caseResponse_integrable := by
  classical
  refine holdsAtEveryStep_mono (holdsAtEveryStep_and hB hF) fun T y R A hA ⟨hb, f⟩ hR n _ G hG y' h => ?_
  have hfit := hR.admissible
  have hresp := hA.admissible
  have hL := hlab R (by have := hfit.L_ge; omega)
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn : R.params.n₀ ≤ n := by
    rcases hG with hcold | hhot
    · exact hcold.n₀_le
    · exact le_trans (Nat.le_mul_of_pos_left _ hL0) hhot.isBlockSide.2
  obtain ⟨K, hK0, hK⟩ := abs_caseResponse_le hsc hfit hresp hn G.coarse y' h
  set S := sitesInBlocks R.params.side {y'} with hS
  have hmeas : ∀ Yt : Finset (TorusSite (n * R.params.side)), Measurable fun ωt : Yt → R.labels.Ω =>
      Real.exp (scoreSumOn A S Yt ωt) := by
    intro Yt
    refine Real.measurable_exp.comp (Finset.measurable_sum _ fun z _ => ?_)
    unfold siteScore
    by_cases hz : z ∈ Yt
    · simp only [dif_pos hz]
      exact hresp.price.borel.comp (measurable_pi_apply _)
    · simp only [dif_neg hz]
      exact measurable_const
  have hI := f n G hG S (fun Yt ωt => Real.exp (scoreSumOn A S Yt ωt)) hmeas
    fun Yt ωt => (abs_of_pos (Real.exp_pos _)).le
  intro bad hbad Yt b
  refine Integrable.mono' ((hI bad hbad Yt b).norm.const_mul K)
    ((hb hR hL).1 n hn G.cut G.coarse G.state y' h bad Yt b).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  show ‖caseTerm R G.cut G.coarse G.state (caseResponse A G.coarse y' h) bad Yt b p.1 p.2‖ ≤
    K * ‖caseTerm R G.cut G.coarse G.state (fun _ Yt ωt _ _ => Real.exp (scoreSumOn A S Yt ωt)) bad Yt b p.1 p.2‖
  unfold caseTerm
  by_cases hc : IsHullState R.params R.range (G.state.fieldWithStoredLinks p.1) Yt ∧
      coarseStateOf R G.cut (G.state.fieldWithStoredLinks p.1) Yt (G.state.fillLabels Yt p.2) bad b = G.state
  · rw [if_pos hc, if_pos hc]
    by_cases hw : stepWeight R G.cut G.coarse (G.state.fieldWithStoredLinks p.1) Yt
        (G.state.fillLabels Yt p.2) bad b = 0
    · simp [hw]
    · have hl : IsLiveState R.params R.coupling R.labelWeight (G.state.fieldWithStoredLinks p.1) Yt
          (G.state.fillLabels Yt p.2) := by
        refine ⟨hc.1, lt_of_le_of_ne
          (hR.hasExpansions.2.nonneg _ (isBlockTorusSide_mul hn) _ _ _ hc.1) fun h0 => hw ?_⟩
        unfold stepWeight
        rw [← h0]
        ring
      have h1 := hK _ Yt _ bad b hl
      rw [norm_mul, norm_mul, ← mul_assoc, Real.norm_eq_abs (caseResponse A G.coarse y' h _ _ _ _ _),
        Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  · rw [if_neg hc, if_neg hc]
    simp
end YangMills.Construction.ResponseInTheExpansion
end
