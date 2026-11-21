import YangMills.Construction.ResponseInTheExpansion.ResponseAlongTheFlow
import YangMills.Construction.ResponseInTheExpansion.TheLevelsOfAFlowAreTheChain
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesAtTheLevelOfTheirRadius
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesHaveTheirSign
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadius
import YangMills.Construction.SixteenPointsOnASmallTorus.MeanOfTheCopiesAtNoLevel
import YangMills.Construction.SixteenPointsOnASmallTorus.MeanOfTheScoresOfTheCopies
import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenCopiesOnTheLeastTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
private theorem logPos_nonneg (t : ℝ) : 0 ≤ TorusBound.logPos t := le_max_right _ _
private theorem logPos_mono {s t : ℝ} (hs : 0 < s) (h : s ≤ t) : TorusBound.logPos s ≤ TorusBound.logPos t :=
  max_le_max (Real.log_le_log hs h) le_rfl
private theorem one_add_rpow_le_exp {w : ℝ} (hw : 0 ≤ w) : (1 + w) ^ ((1 : ℝ) / 25) ≤ Real.exp (w ^ ((1 : ℝ) / 20)) := by
  have h1 : (1 + w) ^ ((1 : ℝ) / 25) ≤ (1 + w) ^ ((1 : ℝ) / 20) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h2 : (1 + w) ^ ((1 : ℝ) / 20) ≤ (1 : ℝ) ^ ((1 : ℝ) / 20) + w ^ ((1 : ℝ) / 20) :=
    Real.rpow_add_le_add_rpow zero_le_one hw (by norm_num) (by norm_num)
  rw [Real.one_rpow] at h2
  have h3 := Real.add_one_le_exp (w ^ ((1 : ℝ) / 20))
  linarith
private theorem clusterRange_pow_four_le {x : ℝ} (hx : 1 ≤ x) :
    (TorusLumps.clusterRange x : ℝ) ^ 4 ≤ 16 * x ^ ((1 : ℝ) / 25) := by
  have hp : 1 ≤ x ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx (by norm_num)
  have h1 : (TorusLumps.clusterRange x : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 100) := by
    unfold TorusLumps.clusterRange
    have := Nat.ceil_lt_add_one (show 0 ≤ x ^ ((1 : ℝ) / 100) by positivity)
    linarith
  have h2 : (TorusLumps.clusterRange x : ℝ) ^ 4 ≤ (2 * x ^ ((1 : ℝ) / 100)) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
  refine h2.trans (le_of_eq ?_)
  rw [mul_pow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 100)), ← Real.rpow_mul (by linarith)]
  norm_num
private theorem copySize_bound_of_level {C₁ C₂ Cr Cm l4 W u N r4 ρ4 : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hCr : 0 ≤ Cr)
    (hCm : 0 ≤ Cm) (hl4 : 0 ≤ l4) (hW : 0 ≤ W) (hN : 0 ≤ N) (hr0 : 0 ≤ r4) (hρ0 : 0 ≤ ρ4) (hr : r4 ≤ Cr * Real.exp W)
    (hρ : ρ4 ≤ l4) (hu : u ≤ W) :
    (C₁ * (1 + r4 + ρ4) * N) ^ 16 * Real.exp (Cm * (1 + l4 + u)) ≤
      ((C₁ * (2 + Cr) * Real.exp (Cm / 16) + C₂) * Real.exp ((1 + Cm / 16) * l4 + (1 + Cm / 16) * W) * N) ^ 16 := by
  have hE1 : 1 ≤ Real.exp (l4 + W) := Real.one_le_exp (by linarith)
  have hEW : Real.exp W ≤ Real.exp (l4 + W) := Real.exp_le_exp.mpr (by linarith)
  have hEl : l4 ≤ Real.exp (l4 + W) := by
    have := Real.add_one_le_exp (l4 + W)
    linarith
  have hv : 1 + r4 + ρ4 ≤ (2 + Cr) * Real.exp (l4 + W) := by
    have h1 : Cr * Real.exp W ≤ Cr * Real.exp (l4 + W) := mul_le_mul_of_nonneg_left hEW hCr
    nlinarith
  have hb1 : (C₁ * (1 + r4 + ρ4) * N) ^ 16 ≤ (C₁ * ((2 + Cr) * Real.exp (l4 + W)) * N) ^ 16 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 16
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hC₁) hN
  have hb2 : Real.exp (Cm * (1 + l4 + u)) ≤ Real.exp (Cm / 16 + Cm / 16 * (l4 + W)) ^ 16 := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    push_cast
    nlinarith
  calc _ ≤ (C₁ * ((2 + Cr) * Real.exp (l4 + W)) * N) ^ 16 * Real.exp (Cm / 16 + Cm / 16 * (l4 + W)) ^ 16 :=
        mul_le_mul hb1 hb2 (Real.exp_pos _).le (by positivity)
    _ = (C₁ * (2 + Cr) * Real.exp (Cm / 16) * Real.exp ((1 + Cm / 16) * l4 + (1 + Cm / 16) * W) * N) ^ 16 := by
        rw [← mul_pow]
        congr 1
        have e : Real.exp (l4 + W) * Real.exp (Cm / 16 + Cm / 16 * (l4 + W)) =
            Real.exp (Cm / 16) * Real.exp ((1 + Cm / 16) * l4 + (1 + Cm / 16) * W) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        calc _ = C₁ * (2 + Cr) * (Real.exp (l4 + W) * Real.exp (Cm / 16 + Cm / 16 * (l4 + W))) * N := by ring
          _ = _ := by rw [e]; ring
    _ ≤ _ := by
        refine pow_le_pow_left₀ (by positivity) ?_ 16
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le) hN
        linarith
private theorem copySize_bound_without_level {C₂ A b l4 W w H N : ℝ} (hA : C₂ ≤ A) (hC₂ : 0 ≤ C₂) (hb : 1 ≤ b)
    (hl4 : 0 ≤ l4) (hW : 0 ≤ W) (hw : 0 ≤ w) (hWw : (1 + w) ^ ((1 : ℝ) / 25) ≤ Real.exp W) (hH : 0 ≤ H) (hHN : H ≤ N) :
    (C₂ * (1 + w) ^ ((1 : ℝ) / 25) * H) ^ 16 ≤ (A * Real.exp (b * l4 + b * W) * N) ^ 16 := by
  have hp : 0 ≤ (1 + w) ^ ((1 : ℝ) / 25) := by positivity
  refine pow_le_pow_left₀ (by positivity) ?_ 16
  have h1 : Real.exp W ≤ Real.exp (b * l4 + b * W) := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : C₂ * (1 + w) ^ ((1 : ℝ) / 25) ≤ A * Real.exp (b * l4 + b * W) :=
    mul_le_mul hA (hWw.trans h1) hp (hC₂.trans hA)
  exact mul_le_mul h2 hHN hH (by have := hC₂.trans hA; positivity)
private theorem radiusLevel_le {ℓ : TorusLumps.StepParameters} {β ρ : ℝ} {K s : ℕ}
    (h : radiusLevel ℓ β K ρ = some s) : s ≤ K := by
  classical
  unfold radiusLevel at h
  split_ifs at h with hex
  have e := Option.some.inj h
  rw [← e]
  exact Nat.findGreatest_le K
set_option maxHeartbeats 1000000 in
theorem reflectedMeanBoundOnTwoCellTorus_holds (hCor : ResponseInTheExpansion.responseAlongFlowStatement)
    (hLab : ClusterExpansionOfAStep.CoarseLabelsStandard) (hChain : ResponseInTheExpansion.flowStagesAreChainStatement)
    (hLevel : reflectedMeanAtRadiusLevelStatement) (hMean : scoreMeanBoundStatement)
    (hNone : reflectedMeanWithoutLevelStatement) (hCoup : couplingAtRadiusLevelStatement)
    (hSign : reflectedMeanNonnegStatement) :
    reflectedMeanBoundOnTwoCellTorus := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, gC⟩ := hCor a ha
  obtain ⟨L₂, r₂, C₂, hr₂, gH⟩ := hChain a ha
  obtain ⟨L₃, r₃, C₃, hr₃, gL⟩ := hLevel a ha
  obtain ⟨L₄, r₄, C₄, hr₄, gM⟩ := hMean a ha
  obtain ⟨L₅, r₅, C₅, hr₅, gN⟩ := hNone a ha
  obtain ⟨L₆, r₆, C₆, hr₆, gK⟩ := hCoup a ha
  refine ⟨max (max L₁ (max L₂ L₃)) (max L₄ (max (max L₅ L₆) 2)),
    fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (min (r₄ c) (min (r₅ c) (r₆ c))))),
    max (max C₁ (max C₂ C₃)) (max C₄ (max C₅ C₆)),
    fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (lt_min (hr₃ c) (lt_min (hr₄ c) (lt_min (hr₅ c) (hr₆ c))))),
    fun L hLo hLL T hTa hTL hT hCS hOn hrt hCd => ?_⟩
  have t₁ := hrt.trans (min_le_left _ _)
  have u₁ := hrt.trans (min_le_right _ _)
  have t₂ := u₁.trans (min_le_left _ _)
  have u₂ := u₁.trans (min_le_right _ _)
  have t₃ := u₂.trans (min_le_left _ _)
  have u₃ := u₂.trans (min_le_right _ _)
  have t₄ := u₃.trans (min_le_left _ _)
  have u₄ := u₃.trans (min_le_right _ _)
  have t₅ := u₄.trans (min_le_left _ _)
  have t₆ := u₄.trans (min_le_right _ _)
  have lA : max L₁ (max L₂ L₃) ≤ L := (le_max_left _ _).trans hLL
  have lB : max L₄ (max (max L₅ L₆) 2) ≤ L := (le_max_right _ _).trans hLL
  have l₁ : L₁ ≤ L := (le_max_left _ _).trans lA
  have l₂ : L₂ ≤ L := (le_trans (le_max_left _ _) (le_max_right _ _)).trans lA
  have l₃ : L₃ ≤ L := (le_trans (le_max_right _ _) (le_max_right _ _)).trans lA
  have l₄ : L₄ ≤ L := (le_max_left _ _).trans lB
  have lC : max (max L₅ L₆) 2 ≤ L := (le_max_right _ _).trans lB
  have l₅ : L₅ ≤ L := (le_trans (le_max_left _ _) (le_max_left _ _)).trans lC
  have l₆ : L₆ ≤ L := (le_trans (le_max_right _ _) (le_max_left _ _)).trans lC
  have l₇ : 2 ≤ L := (le_max_right _ _).trans lC
  have cA : max C₁ (max C₂ C₃) ≤ T.derivBound := (le_max_left _ _).trans hCd
  have cB : max C₄ (max C₅ C₆) ≤ T.derivBound := (le_max_right _ _).trans hCd
  have c₁ : C₁ ≤ T.derivBound := (le_max_left _ _).trans cA
  have c₂ : C₂ ≤ T.derivBound := (le_trans (le_max_left _ _) (le_max_right _ _)).trans cA
  have c₃ : C₃ ≤ T.derivBound := (le_trans (le_max_right _ _) (le_max_right _ _)).trans cA
  have c₄ : C₄ ≤ T.derivBound := (le_max_left _ _).trans cB
  have c₅ : C₅ ≤ T.derivBound := (le_trans (le_max_left _ _) (le_max_right _ _)).trans cB
  have c₆ : C₆ ≤ T.derivBound := (le_trans (le_max_right _ _) (le_max_right _ _)).trans cB
  obtain ⟨RK, -, -, -, hFit, y₁, gC⟩ := gC L hLo l₁ T hTa hTL hT hCS hOn t₁ c₁ 0
  obtain ⟨y₂, gH⟩ := gH L hLo l₂ T hTa hTL hT hCS hOn t₂ c₂
  obtain ⟨y₃, gL⟩ := gL L hLo l₃ T hTa hTL hT hCS hOn t₃ c₃ RK hFit
  obtain ⟨y₄, gM⟩ := gM L hLo l₄ T hTa hTL hT hCS hOn t₄ c₄ RK
  obtain ⟨y₅, gN⟩ := gN L hLo l₅ T hTa hTL hT hCS hOn t₅ c₅
  obtain ⟨y₆, gK⟩ := gK L hLo l₆ T hTa hTL hT hCS hOn t₆ c₆
  refine ⟨max (max y₁ (max y₂ y₃)) (max y₄ (max y₅ (max y₆ T.floorMin))), fun y hy hR hW => ?_⟩
  have eA : max y₁ (max y₂ y₃) ≤ y := (le_max_left _ _).trans hy
  have eB : max y₄ (max y₅ (max y₆ T.floorMin)) ≤ y := (le_max_right _ _).trans hy
  have e₁ : y₁ ≤ y := (le_max_left _ _).trans eA
  have e₂ : y₂ ≤ y := (le_trans (le_max_left _ _) (le_max_right _ _)).trans eA
  have e₃ : y₃ ≤ y := (le_trans (le_max_right _ _) (le_max_right _ _)).trans eA
  have e₄ : y₄ ≤ y := (le_max_left _ _).trans eB
  have eC : max y₅ (max y₆ T.floorMin) ≤ y := (le_max_right _ _).trans eB
  have e₅ : y₅ ≤ y := (le_max_left _ _).trans eC
  have e₆ : y₆ ≤ y := (le_trans (le_max_left _ _) (le_max_right _ _)).trans eC
  have hy0 : T.floorMin ≤ y := (le_trans (le_max_right _ _) (le_max_right _ _)).trans eC
  have hfit : (T.stepParameters y).Admissible := hT.fits y hy0
  have hy1 : 1 ≤ y := hfit.y₁_ge
  have hL2 : 2 ≤ (T.stepParameters y).side := by
    have := hfit.L_ge
    omega
  refine ⟨RK, hFit y, fun Ξ hΞ => ?_⟩
  obtain ⟨Cl, hCl, gL⟩ := gL y e₃ hR hW Ξ hΞ
  obtain ⟨Cm, hCm, gM⟩ := gM y e₄ hR hW Ξ hΞ
  obtain ⟨Cn, hCn, gN⟩ := gN y e₅ hR hW Ξ hΞ
  obtain ⟨Cx, hCx, gK⟩ := gK y e₆ hR hW Ξ hΞ
  have hCr : 0 ≤ 16 * Cx ^ ((1 : ℝ) / 25) := by positivity
  refine ⟨Cl * (2 + 16 * Cx ^ ((1 : ℝ) / 25)) * Real.exp (Cm / 16) + Cn, 1 + Cm / 16, by positivity, by positivity, ?_⟩
  intro β K hd
  have hβ : y ≤ β := hd.coupling_ge 0 (Nat.zero_le _)
  have hLf : ∀ c : WeightedResponses.ChainStage (T.stepParameters y), ClusterExpansionOfAStep.CoarseLabelFacts c.toStepSetup :=
    fun c => hLab c.toStepSetup hL2
  obtain ⟨z₀, hz, hs⟩ := gC y e₁ hR hW β hLf hβ
  have hst : ResponseInTheExpansion.StagesOnFlowUpTo T RK y β hLf z₀ K := fun t ht => hs t fun k hk => hd.coupling_ge k (by omega)
  refine ⟨fun j => (ResponseInTheExpansion.flowStages T y β hLf z₀ j).2.coeff, gH y e₂ hR hW RK (hFit y) β hLf z₀ K hz hst, ?_⟩
  intro κ hκ ρ H Λ h hρ hρl hsrc z
  have hH : 0 ≤ H := (abs_nonneg _).trans (hsrc.abs_le 0)
  have hHN : H ≤ sourceNorm ρ H Λ := le_max_left _ _
  have hN0 : 0 ≤ sourceNorm ρ H Λ := hH.trans hHN
  have hKpos : 0 < K := by
    have := hd.two_le
    omega
  refine ⟨hSign (T.stepParameters y) hfit β K κ ρ H Λ h _ z (by linarith) hKpos hκ hρ hρl hsrc, ?_⟩
  set w := TorusBound.logPos (1 / ρ) with hw
  have hw0 : 0 ≤ w := logPos_nonneg _
  set W := w ^ ((1 : ℝ) / 20) with hWdef
  have hW0 : 0 ≤ W := by positivity
  set l := cellLength (T.stepParameters y).side K κ with hl
  have hρl₂ : ρ ≤ l / 4 := hρl
  have hρl' : ρ ≤ l := by linarith
  have hl4 : 0 ≤ l ^ 4 := by positivity
  show _ ≤ (ReflectedCopies.copySize _ _ l ρ * sourceNorm ρ H Λ) ^ 16
  unfold ReflectedCopies.copySize
  rw [← hw, ← hWdef]
  rcases hlev : radiusLevel (T.stepParameters y) β K ρ with _ | s
  · have hc : centring (T.stepParameters y) β (fun j => (ResponseInTheExpansion.flowStages T y β hLf z₀ j).2.coeff) K κ ρ h = 0 := by
      unfold centring reflectedCentring
      rw [hlev]
    rw [hc]
    refine (gN β K κ ρ H Λ h hd hκ hρ hρl hsrc hlev z).trans ?_
    exact copySize_bound_without_level (le_add_of_nonneg_left (by positivity)) hCn
      (by linarith [div_nonneg hCm (by norm_num : (0 : ℝ) ≤ 16)]) hl4 hW0 hw0 (one_add_rpow_le_exp hw0) hH hHN
  · have hsK := radiusLevel_le hlev
    have hmaj := gM β hLf z₀ hz K κ s ρ H Λ h hd hκ hρ hρl hsrc hlev hst
    have hb := gL β hLf z₀ hz K κ s ρ H Λ h hd hκ hρ hρl hsrc hlev hst _ (Real.exp_pos _).le hmaj z
    refine hb.trans ?_
    have hx1 : 1 ≤ (TorusLumps.couplingFlow (T.stepParameters y) β s).1 := hy1.trans (hd.coupling_ge s hsK)
    have hxs := (gK β K ρ hd hρ).1 s hlev
    have hr : rangeAtLevel (T.stepParameters y) β s ^ 4 ≤ 16 * Cx ^ ((1 : ℝ) / 25) * Real.exp W := by
      have h1 := clusterRange_pow_four_le hx1
      have h2 : (TorusLumps.couplingFlow (T.stepParameters y) β s).1 ^ ((1 : ℝ) / 25) ≤ (Cx * (1 + w)) ^ ((1 : ℝ) / 25) :=
        Real.rpow_le_rpow (by linarith) hxs (by norm_num)
      rw [Real.mul_rpow hCx (by linarith)] at h2
      have h3 := one_add_rpow_le_exp hw0
      have h4 : Cx ^ ((1 : ℝ) / 25) * (1 + w) ^ ((1 : ℝ) / 25) ≤ Cx ^ ((1 : ℝ) / 25) * Real.exp W :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      unfold rangeAtLevel
      calc _ ≤ 16 * (TorusLumps.couplingFlow (T.stepParameters y) β s).1 ^ ((1 : ℝ) / 25) := h1
        _ ≤ 16 * (Cx ^ ((1 : ℝ) / 25) * (1 + w) ^ ((1 : ℝ) / 25)) := mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ ≤ 16 * (Cx ^ ((1 : ℝ) / 25) * Real.exp W) := mul_le_mul_of_nonneg_left h4 (by norm_num)
        _ = _ := by ring
    have hρ4 : ρ ^ 4 ≤ l ^ 4 := pow_le_pow_left₀ hρ.le hρl' 4
    have hu : TorusBound.logPos (1 / l) ^ ((1 : ℝ) / 20) ≤ W := by
      have h1 : 1 / l ≤ 1 / ρ := one_div_le_one_div_of_le hρ hρl'
      have h2 : 0 < 1 / l := by
        have : 0 < l := lt_of_lt_of_le hρ hρl'
        positivity
      exact Real.rpow_le_rpow (logPos_nonneg _) (logPos_mono h2 h1) (by norm_num)
    have hr0 : 0 ≤ rangeAtLevel (T.stepParameters y) β s ^ 4 := by positivity
    exact copySize_bound_of_level hCl hCn hCr hCm hl4 hW0 hN0 hr0 (by positivity) hr hρ4 hu
end YangMills.Construction.SmallTorusCopies
end
