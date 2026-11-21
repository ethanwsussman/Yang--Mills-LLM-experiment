import YangMills.Construction.FreeEnergiesOfTheFlow.MeanOfTheVariableOfAStepProof
import YangMills.Construction.LawByMomentsOfTheFlow.ResponsesAtTheFieldOneAddUp
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace YangMills.Construction.MomentLaw
open StepSettings StepGas TorusFields TorusLumps RenormalizationStepParameters StepCosts WeightedResponses ResponseInTheExpansion
  BlockAverages ColdStepAtMirrorFrames FreeEnergies
section Conjunction
private theorem HoldsAtEveryStep.and {P Q : ParameterAssignment → ∀ R : StepSetup, ResponseSetup R → Prop}
    (hP : HoldsAtEveryStep P) (hQ : HoldsAtEveryStep Q) :
    HoldsAtEveryStep fun T R A => P T R A ∧ Q T R A := by apply _root_.YangMills.SharedProofs.p19358 <;> assumption
end Conjunction
section FiniteSums
variable {R : StepSetup} {n : ℕ} [NeZero n] {C : Finset (TorusSite n)} {V : TorusField n} {q : CoarseState R n}
private theorem caseMean_finset_sum
    (hadd : ∀ F F' : CaseFunction R n, CaseIntegrable R C V q F → CaseIntegrable R C V q F' →
      CaseIntegrable R C V q (fun W Yt ωt bad b => F W Yt ωt bad b + F' W Yt ωt bad b) ∧
      caseMean R C V q (fun W Yt ωt bad b => F W Yt ωt bad b + F' W Yt ωt bad b) =
        caseMean R C V q F + caseMean R C V q F')
    (h0 : CaseIntegrable R C V q (fun _ _ _ _ _ => 0) ∧ caseMean R C V q (fun _ _ _ _ _ => 0) = 0)
    {ι : Type} (s : Finset ι) (F : ι → CaseFunction R n) (hF : ∀ i ∈ s, CaseIntegrable R C V q (F i)) :
    CaseIntegrable R C V q (fun W Yt ωt bad b => ∑ i ∈ s, F i W Yt ωt bad b) ∧
      caseMean R C V q (fun W Yt ωt bad b => ∑ i ∈ s, F i W Yt ωt bad b) =
        ∑ i ∈ s, caseMean R C V q (F i) := by apply _root_.YangMills.SharedProofs.p34211 <;> assumption
end FiniteSums
section OneStep
variable {R : StepSetup} {A : ResponseSetup R} {n : ℕ} [NeZero n]
private theorem supportResponseSum_eq_sum_caseResponse
    (hrow : ResponseBounds R.params A.responseParams R.depth R.coupling A.coeff R.labels R.labelWeight A.score
      A.cold A.hull A.siteRemainder A.totalRemainder)
    (hbs : IsBlockTorusSide R.params (n * R.params.side))
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (V : TorusField n)
    {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω}
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) :
    ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f, caseResponse A V Y f W Yt ωt bad b +
        -(∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
          A.cold (n * R.params.side) y (trivialField (n * R.params.side)) f) * 1 =
      supportResponseSum A V f W Yt ωt bad b := by apply _root_.YangMills.SharedProofs.p48742 <;> assumption
end OneStep
section StepWeights
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem stepWeight_nonneg_and_live (hrow : R.HasExpansions) (hK : BondKernelProperties)
    (hcut : IsCutoff R.ballRadius R.barrierFn) (hbs : IsBlockTorusSide R.params (n * R.params.side))
    (C : Finset (TorusSite n)) (V : TorusField n) {W : TorusField (n * R.params.side)}
    {Yt : Finset (TorusSite (n * R.params.side))} (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hh : IsHullState R.params R.range W Yt) :
    0 ≤ stepWeight R C V W Yt ωt bad b ∧
      (0 < stepWeight R C V W Yt ωt bad b → IsLiveState R.params R.coupling R.labelWeight W Yt ωt) := by apply _root_.YangMills.SharedProofs.p15922 <;> assumption
end StepWeights
theorem responsesAtTrivialFieldSum (hC : caseMeanProperties)
    (hFL : labelFunctionsIntegrableStatement)
    (hMass : FreeEnergiesOfTheFlow.CoarseStateWeightNeZeroOnGround)
    (hIR : coldStepIntegralEqGasMean) (hK : BondKernelProperties) :
    responsesAtTrivialFieldSumStatement := by
  classical
  obtain ⟨rt₀, hrt₀, H⟩ := HoldsAtEveryStep.and hFL (HoldsAtEveryStep.and hMass hIR)
  refine ⟨rt₀, hrt₀, fun T hT hr K => ?_⟩
  obtain ⟨y₀, Y₀⟩ := H T hT hr K
  refine ⟨max y₀ T.floorMin, fun y hy R A hKA hA n _ hn f => ?_⟩
  obtain ⟨fl, mass, ir⟩ := Y₀ y ((le_max_left _ _).trans hy) R A hKA hA
  have hy' : T.floorMin ≤ y := (le_max_right _ _).trans hy
  have hparams := hA.onFamily.params_eq
  have hadm : R.params.Admissible := hparams ▸ hT.fits y hy'
  have hrow := hA.onFamily.isStep.1
  have hresp := hA.admissible.bounds
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    have hρ : R.ballRadius = T.ballRadius := by
      unfold StepSetup.ballRadius
      rw [hparams]
      rfl
    rw [hρ, hA.onFamily.barrierFn_eq]
    exact hT.cut
  have hbs : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hG : (coldCaseGround R (trivialField n)).IsAdmissibleGround :=
    coldCaseGround_trivialField_isAdmissible R n hn hadm
  have hp := hC R n (coldCaseGround R (trivialField n)).cut (coldCaseGround R (trivialField n)).coarse
    (coldCaseGround R (trivialField n)).state
    (fun W Yt ωt bad b hh => (stepWeight_nonneg_and_live hrow hK hcut hbs _ _ ωt bad b hh).1)
  have h1 : CaseIntegrable R (coldCaseGround R (trivialField n)).cut (coldCaseGround R (trivialField n)).coarse
      (coldCaseGround R (trivialField n)).state (fun _ _ _ _ _ => 1) :=
    fl n _ hG ∅ (fun _ _ => 1) (fun _ => measurable_const) (fun Yt ωt => by simp [scoreSumOn])
  have hone := hp.2.2.2.2.1 h1 (mass n _ hG)
  have h0 : CaseIntegrable R (coldCaseGround R (trivialField n)).cut (coldCaseGround R (trivialField n)).coarse
      (coldCaseGround R (trivialField n)).state (fun _ _ _ _ _ => 0) ∧
      caseMean R (coldCaseGround R (trivialField n)).cut (coldCaseGround R (trivialField n)).coarse
        (coldCaseGround R (trivialField n)).state (fun _ _ _ _ _ => 0) = 0 := by
    have h := hp.2.2.1 0 _ h1
    simpa only [zero_mul] using h
  have hs := caseMean_finset_sum hp.2.1 h0 (weightSupportSites R.params.side (R.depth + 1) n f)
    (fun Y => caseResponse A (trivialField n) Y f) (fun Y _ => (ir n _ hG Y f).1)
  have hc := hp.2.2.1 (-(∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
    A.cold (n * R.params.side) y (trivialField (n * R.params.side)) f)) _ h1
  have ha := hp.2.1 _ _ hs.1 hc.1
  have he := hp.1 _ (supportResponseSum A (trivialField n) f) (fun W Yt ωt bad b hh hw =>
    supportResponseSum_eq_sum_caseResponse hresp hbs f (trivialField n) bad b
      ((stepWeight_nonneg_and_live hrow hK hcut hbs _ _ ωt bad b hh).2 hw))
  have hmean : caseMean R (coldCaseGround R (trivialField n)).cut (coldCaseGround R (trivialField n)).coarse
      (coldCaseGround R (trivialField n)).state (supportResponseSum A (trivialField n) f) =
      ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
          caseMean R (coldCaseGround R (trivialField n)).cut (coldCaseGround R (trivialField n)).coarse
            (coldCaseGround R (trivialField n)).state (caseResponse A (trivialField n) Y f) -
        ∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
          A.cold (n * R.params.side) y (trivialField (n * R.params.side)) f := by
    rw [← he.2, ha.2, hs.2, hc.2, hone]
    ring
  have hmean' : caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) =
      ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
          caseMean R ∅ (trivialField n) (emptyCoarseState R) (caseResponse A (trivialField n) Y f) -
        ∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
          A.cold (n * R.params.side) y (trivialField (n * R.params.side)) f := hmean
  show ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
    caseMean R ∅ (trivialField n) (emptyCoarseState R) (caseResponse A (trivialField n) Y f) = _
  rw [hmean']
  ring
end YangMills.Construction.MomentLaw
end
