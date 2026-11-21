import YangMills.Construction.ClusterExpansionOfAStep.AZeroFactorKillsTheState
import YangMills.Construction.ClusterExpansionOfAStep.GroundsOfAgreeingStates
import YangMills.Construction.ClusterExpansionOfAStep.HullStatesAreGrounds
import YangMills.Construction.ResponseInTheExpansion.ForgettingOfTheResponseReturns
import YangMills.Construction.ResponseInTheExpansion.HatsOfAgreeingGrounds
import YangMills.Construction.ResponseInTheExpansion.StoredScoresOfAGround
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses StepGas StepSettings TorusFields TorusLumps RenormalizationStepParameters
theorem stepDecayBoundsHold_of (hB : centredGasBlockAgreementStatement)
    (hI : coldStepIntegralEqGasMean) (hGr : GroundsAgreeNearOfStatesAgreeNear)
    (hHu : HullStateIsHotCase) (hZ : ClusterExpansionOfAStep.CoarseWeightZeroOfFactorZero) :
    StepDecayBoundsHold := by
  obtain ⟨r₁, p₁, g₁⟩ := hB
  obtain ⟨r₂, p₂, g₂⟩ := hI
  refine ⟨fun c => min (r₁ c) (r₂ c), fun c => lt_min (p₁ c) (p₂ c), fun T hD hrt K => ?_⟩
  obtain ⟨y₁, B₁⟩ := g₁ T hD (hrt.trans (min_le_left _ _)) K
  obtain ⟨y₂, I₁⟩ := g₂ T hD (hrt.trans (min_le_right _ _)) K
  obtain ⟨y₃, H₁⟩ := hHu T hD
  refine ⟨max (max y₁ y₂) (max y₃ (200 * T.B)), fun y hy R A hK hAt hFo hL => ?_⟩
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
  have hy2 : y₂ ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans hy)
  have hy3 : y₃ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hy5 : 200 * T.B ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans hy)
  have hR := hAt.onFamily
  have hxy := hR.le_coupling
  have hfit : R.params.Admissible := hFo.admissible
  have hodd := hfit.L_odd
  have hxx : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAt.abs_sub_le).2
    linarith
  have core := B₁ y hy1 R A hK hAt hFo
  have hIm := I₁ y hy2 R A hK hAt
  have hKf0 := hAt.admissible.params_admissible
  have hs₁ : 0 ≤ A.responseParams.s₁ := by
    have e := hKf0.C₀_eq
    have h1 := hKf0.N₀_nonneg
    have h2 := hKf0.Kc_ge
    have h3 := hfit.a_ge
    have h4 : 0 ≤ A.responseParams.C₀ + 2 := by
      rw [e]
      linarith only [h1, h2, h3]
    rw [hKf0.s₁_eq]
    exact add_nonneg (mul_nonneg (by positivity) h4) (by linarith only [h3])
  have hsnn := hAt.admissible.price.nonneg
  have hot : ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (W : TorusField n)
      (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel R.labels.Ω R.params.side),
      IsLiveState R.params R.nextCoupling (coarseWeightExpansion R) W Y ω →
      (∀ X ∈ chainComponents R.nextRange Y, coarseFactor W (⟨Y, ω⟩ : CoarseState R n) X ≠ 0) ∧
        (hotCaseGround R W ⟨Y, ω⟩).IsAdmissibleGround := by
    intro n _ bs W Y ω hl
    have hpos : 0 < coarseStateWeight R (hotCoreSites R W) W ⟨Y, ω⟩ := by
      have := hl.2
      unfold coarseWeightExpansion at this
      rwa [dif_neg (NeZero.ne n)] at this
    have hΦ : ∀ X ∈ chainComponents R.nextRange Y, coarseFactor W (⟨Y, ω⟩ : CoarseState R n) X ≠ 0 := by
      intro X hX h0
      have := hZ R hFo n bs W ⟨Y, ω⟩ hl.1 ⟨X, hX, h0⟩
      linarith
    exact ⟨hΦ, Or.inr (H₁ y hy3 R hR hFo n bs W ⟨Y, ω⟩ hl.1 hΦ)⟩
  have hatHot : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (W : TorusField n) (Y : Finset (TorusSite n))
      (ω : Y → CoarseLabel R.labels.Ω R.params.side) (y' : TorusSite n)
      (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)),
      (hotCaseGround R W ⟨Y, ω⟩).IsAdmissibleGround →
      centeredHullResponse A.coldStep A.hullStep n y' W Y ω h =
        gasBlockMean A (hotCaseGround R W ⟨Y, ω⟩) y' h -
          gasBlockMean A (coldCaseGround R (trivialField n)) y' h := by
    intro n _ hn W Y ω y' h hG
    have e1 : caseMean R (hotCoreSites R W) W ⟨Y, ω⟩ (caseResponse A W y' h) = _ := (hIm n _ hG y' h).2
    have e2 : caseMean R ∅ (trivialField n) (emptyCoarseState R) (caseResponse A (trivialField n) y' h) = _ :=
      (hIm n _ (coldCaseGround_trivialField_isAdmissible R n hn hfit) y' h).2
    show caseMean R (hotCoreSites R W) W ⟨Y, ω⟩ (caseResponse A W y' h) -
      caseMean R ∅ (trivialField n) (emptyCoarseState R) (caseResponse A (trivialField n) y' h) = _
    rw [e1, e2]
    ring
  have hatCold : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (W : TorusField n) (y' : TorusSite n)
      (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)), (coldCaseGround R W).IsAdmissibleGround →
      centeredResponse A.coldStep n y' W h =
        gasBlockMean A (coldCaseGround R W) y' h - gasBlockMean A (coldCaseGround R (trivialField n)) y' h := by
    intro n _ hn W y' h hG
    have e1 : caseMean R ∅ W (emptyCoarseState R) (caseResponse A W y' h) = _ := (hIm n _ hG y' h).2
    have e2 : caseMean R ∅ (trivialField n) (emptyCoarseState R) (caseResponse A (trivialField n) y' h) = _ :=
      (hIm n _ (coldCaseGround_trivialField_isAdmissible R n hn hfit) y' h).2
    show caseMean R ∅ W (emptyCoarseState R) (caseResponse A W y' h) -
      caseMean R ∅ (trivialField n) (emptyCoarseState R) (caseResponse A (trivialField n) y' h) = _
    rw [e1, e2]
    ring
  have hcold : ∀ (n : ℕ) [NeZero n] (W : TorusField n), R.params.n₀ ≤ n → IsCold R.params.threshold W →
      (coldCaseGround R W).IsAdmissibleGround := by
    intro n _ W hn hc
    refine Or.inl ⟨hn, fun x μ ν hlt => ?_, rfl, rfl, rfl⟩
    have h1 := hc x μ ν hlt
    have h2 := hfit.σ_pos
    exact show curvature W x μ ν < 9 / 8 * R.params.threshold from by linarith only [h1, h2]
  have hblock : ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → R.params.n₀ ≤ n := by
    intro n _ bs
    have h1 := bs.2
    have h2 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
    nlinarith
  have hr16 : 2 ^ 16 ≤ R.nextRange := hFo.nextRange_ge
  refine ⟨?_, ?_, ?_⟩
  · intro n n' _ _ bs bs' W W' Y Y' ω ω' y₀ y₀' m h h' hl hl' hm hst hw
    obtain ⟨hΦ, hG⟩ := hot n bs W Y ω hl
    obtain ⟨hΦ', hG'⟩ := hot n' bs' W' Y' ω' hl'
    have hag := (hGr R n n' W W' Y ω y₀ y₀' m hfit hr16 bs.1 hl.1 hΦ).1 Y' ω' bs'.1 hl'.1 hΦ' hst
    exact (le_of_eq (congrArg abs (congrArg₂ (· - ·) (hatHot n (hblock n bs) W Y ω y₀ h hG)
      (hatHot n' (hblock n' bs') W' Y' ω' y₀' h' hG')))).trans
      (core n n' _ _ y₀ y₀' m h h' _ hG hG' (hblock n bs) (hblock n' bs') hag hm hw
        (sum_recordedSiteScore_le A hs₁ hsnn hodd W ⟨Y, ω⟩ y₀).1)
  · intro n n' _ _ bs hn' W W' Y ω ω' y₀ y₀' m h h' hl hc' hm hst hw
    obtain ⟨hΦ, hG⟩ := hot n bs W Y ω hl
    have hG' := hcold n' W' hn' hc'
    have hag := (hGr R n n' W W' Y ω y₀ y₀' m hfit hr16 bs.1 hl.1 hΦ).2 ω' hst
    exact (le_of_eq (congrArg abs (congrArg₂ (· - ·) (hatHot n (hblock n bs) W Y ω y₀ h hG)
      (hatCold n' hn' W' y₀' h' hG')))).trans
      (core n n' _ _ y₀ y₀' m h h' _ hG hG' (hblock n bs) hn' hag hm hw
        (sum_recordedSiteScore_le A hs₁ hsnn hodd W ⟨Y, ω⟩ y₀).1)
  · intro n n' _ _ hn hn' W W' y₀ y₀' m h h' hc hc' hm hs hs' hfa hw
    have hG := hcold n W hn hc
    have hG' := hcold n' W' hn' hc'
    have hag : GroundsAgreeNear (coldCaseGround R W) (coldCaseGround R W') y₀ y₀' m :=
      ⟨hs, hs', hfa, fun v _ => by simp [coldCaseGround], fun v _ => by
        rw [coldCaseGround_labelAt_eq_none, coldCaseGround_labelAt_eq_none]⟩
    rw [hatCold n hn W y₀ h hG, hatCold n' hn' W' y₀' h' hG']
    have := core n n' _ _ y₀ y₀' m h h' 0 hG hG' hn hn' hag hm hw
      (le_of_eq (sum_recordedSiteScore_coldCaseGround A hodd W y₀))
    simpa using this
end YangMills.Construction.ResponseInTheExpansion
end
