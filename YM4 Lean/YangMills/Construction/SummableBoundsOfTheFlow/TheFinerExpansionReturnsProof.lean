import YangMills.Construction.ClusterExpansionOfAStep.ExpansionReturnsAtDrawnParameters
import YangMills.Construction.ColdStepAtMirrorFrames.DensitiesOfTheStep
import YangMills.Construction.SummableBoundsOfTheFlow.FinerExpansionFollowsFromTilts
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.SumsOfFamilies
import YangMills.Construction.SummableBoundsOfTheFlow.ThePiecesOfTheStep
import YangMills.Construction.SummableBoundsOfTheFlow.WilsonHasFinerExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.FamilyNorms
open TorusLumps
private theorem thirdOrderSize_mono {P : StepParameters} (hP : P.Admissible) {ε ε' : ℝ} (hε : ε ≤ ε') :
    thirdOrderSize P ε ≤ thirdOrderSize P ε' := by
  unfold thirdOrderSize
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hε hP.E₃_pos.le) hP.E_pos.le
abbrev _root_.YangMills.SharedProofs.p37405 := @thirdOrderSize_mono
theorem refinedExpansionReturns_holds (hPieces : stepPiecesStatement)
    (hReturn : StepReturn.ExpansionHoldsAtAdmissibleParameters)
    (hStepBounds : ColdStepAtMirrorFrames.stepDensityBoundsStatement)
    (hWilson : wilsonHasRefinedExpansionStatement) (hFollow : BlockMeans.refinedExpansionOfTilt)
    (hTilt : imageTiltStatement) (hSums : normBoundedFamilyClosureStatement) : RefinedExpansionReturns := by
  obtain ⟨Q, hQ, rt₀, hrt₀, hP'⟩ := hPieces
  obtain ⟨fL, cR, cS, fN, fC, hR0, hS0, hAll⟩ := hReturn
  obtain ⟨Cw, hWc⟩ := hWilson
  refine ⟨_, ColdStepAtMirrorFrames.EventuallyInParameters.and hStepBounds hQ, fL, fun c => min (cR c) (rt₀ c), cS, fN, fC, Cw,
    fun c => lt_min (hR0 c) (hrt₀ c), hS0, ?_⟩
  intro T hAdm hLf h1 h2 h3 h4 hCd hFrom
  obtain ⟨c₀, m, hTies, hBoth⟩ := hFrom
  have hCold : T.ColdStepHolds := ⟨c₀, m, hTies, fun y hy => (hBoth y hy).1⟩
  have hFromQ : T.HoldsFrom Q := ⟨c₀, m, hTies, fun y hy => (hBoth y hy).2⟩
  obtain ⟨yR, hRet⟩ := hAll T hAdm hLf (h1.trans (min_le_left _ _)) h2 h3 h4 hCold
  obtain ⟨C₀, M, y₀, hC₀, hNa, hM, hdM, hRef, hpieces⟩ := hP' T hAdm (h1.trans (min_le_right _ _)) hFromQ
  set C₁ : ℝ := imageTiltConstant C₀ (shareBound T) M + 1 with hC₁
  have hC₁t : imageTiltConstant C₀ (shareBound T) M ≤ C₁ := by rw [hC₁]; linarith
  have hC₁3 : 3 * C₀ ≤ C₁ := by
    rw [hC₁]
    unfold imageTiltConstant
    have : 0 ≤ shareBound T * M := mul_nonneg hNa hM
    have : 0 ≤ 3 * C₀ * shareBound T := by positivity
    linarith
  have hC₁0 : 0 < C₁ := by
    rw [hC₁]
    unfold imageTiltConstant
    have : 0 ≤ shareBound T * M := mul_nonneg hNa hM
    have : 0 ≤ 3 * C₀ * shareBound T := by positivity
    linarith
  have hadm₀ : (T.stepParameters T.floorMin).Admissible := hAdm.fits _ le_rfl
  have hE0 : 0 < T.E := hadm₀.E_pos
  have hev : ∀ᶠ y : ℝ in Filter.atTop, 2 * C₁ * y ^ (-(3 / 4 : ℝ)) ≤ T.E / 2 := by
    have t0 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4)).const_mul (2 * C₁)
    rw [mul_zero] at t0
    exact t0.eventually_le_const (by positivity)
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max y₀ yR) (max (max T.floorMin 1) (max (200 * T.B) Y₁)), C₁, M, fun y hy => ?_⟩
  have l0 : y₀ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have lR : yR ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have lT : T.floorMin ≤ y := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hy
  have l1 : 1 ≤ y := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hy
  have lB : 200 * T.B ≤ y := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hy
  have lY : Y₁ ≤ y := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hy
  have hadm : (T.stepParameters y).Admissible := hAdm.fits y lT
  have hret := hRet y lR
  have hmono : ∀ {t : ℕ} {x : ℝ} {D : TorusFunctional} {f h : LocalDensity} {ε ε' : ℝ}, ε ≤ ε' →
      IsCurvatureFreeTilt (T.stepParameters y) t x D f h ε →
        IsCurvatureFreeTilt (T.stepParameters y) t x D f h ε' := fun hε H =>
    ⟨(hSums (T.stepParameters y)).1 _ _ _ _ _ hε (thirdOrderSize_mono hadm hε) H.normBounded,
      H.curvatureForm_vanishes, H.log_density_eq⟩
  have htilts : TiltReturnsAt (T.stepParameters y) (ParameterAssignment.reference T) (ParameterAssignment.oneLoop T)
      (ParameterAssignment.secondStep T) y C₁ := by
    intro t x D ε h hx hε hrow hTi hθ
    have hx1 : 1 ≤ x := l1.trans hx
    have hx0 : 0 < x := by linarith
    obtain ⟨c, m, e, g, Pc⟩ := hpieces y l0 t x D ε h hx hε hrow hTi hθ
    obtain ⟨x₁, ⟨hr₁, -⟩, -⟩ := hret t x D hx hrow
    obtain ⟨T1, T2⟩ := hTilt _ _ _ x₁ _ _ _ _ _ _ _ _ _ _ _ _ _ Pc hr₁
    refine ⟨x₁, _, hr₁, hmono ?_ T1, T2.trans ?_⟩
    · have : 0 < x ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos hx0 _
      have := mul_le_mul_of_nonneg_right hC₁t this.le
      linarith
    · refine mul_le_mul_of_nonneg_right hC₁3 ?_
      have : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
      have : 0 < x ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
      positivity
  have href : ∀ t, IsNormBoundedFamily (T.stepParameters y) ((T.stepParameters y).E / 2)
      ((T.stepParameters y).E₃ / 2) (ParameterAssignment.reference T t) :=
    fun t => hRef y lT t
  refine ⟨hadm, hret, hC₁0, hdM, htilts, ?_, ?_⟩
  · exact hFollow _ _ _ _ _ _ hadm hret hC₁0 l1 lB le_rfl (hY₁ y lY) href htilts
  · exact hWc _ _ _ _ hadm hCd rfl le_rfl (by linarith) (by positivity)
end YangMills.Construction.FamilyNorms
end
