import YangMills.Construction.ResponseInTheExpansion.ColdFunctionsOnAMirror
import YangMills.Construction.ResponseInTheExpansion.ColdResponsesKeepTheGauge
import YangMills.Construction.ResponseInTheExpansion.FloorsOfTheLocalParameters
import YangMills.Construction.ResponseInTheExpansion.MeansOfAWeight
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAScoredTowerOnColdMirrors
import YangMills.Construction.ResponseInTheExpansion.SharesAtEveryLevel
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheLocalChain
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsTheDescendedForm
import YangMills.Construction.ResponseInTheExpansion.TheResponseIsAQuadraticFormOfTheCurvature
import YangMills.Construction.ResponseInTheExpansion.TheShareHasTheFormOfTheCurvature
import YangMills.Construction.ResponseInTheExpansion.WeightsExtendWithTheirSlope
import YangMills.Construction.ResponseInTheExpansion.WeightsNearTheirMeans
import YangMills.Construction.ResponseInTheExpansion.WeightsOnTwoTori
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps RenormalizationStepParameters StepCosts ShareFamilies ExponentialSums TorusMirror BlockAverages WeightedResponses
  ColdStepAtMirrorFrames
open Classical
open MirrorKernels ColdMirrorFunctionals LocalRadii
private theorem remainder_coeff_le {Cc Cs Ka Kc a b : ℝ} (hC : 0 ≤ Cc) (hCs : 0 ≤ Cs) (hKa : 0 ≤ Ka) (hKc : 0 ≤ Kc)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Cc * (Ka * a) + Cc * (Kc * (2 * b)) ≤ Cc * (Cs + Ka + 2 * Kc) * (a + b) := by
  have h : 0 ≤ Cc * (Cs * (a + b) + Ka * b + 2 * Kc * a) := by positivity
  nlinarith
private theorem cube_moment_exponent_le {x G C n4 : ℝ} (hx : 1 ≤ x) (hG : 0 ≤ G) (hC : 0 ≤ C) (hn : 0 ≤ n4) :
    2 * (n4 * G) * ((C * x ^ (-(1 / 2 : ℝ) + 2 / 1000)) ^ 3 + ((x ^ (-1 : ℝ)) ^ 3 + x ^ (-2 : ℝ))) ≤
      2 * G * (C ^ 3 + 2) * n4 * x ^ (-(3 / 2 : ℝ) + 6 / 1000) := by
  have hx0 : 0 < x := by linarith
  have e1 : (x ^ (-(1 / 2 : ℝ) + 2 / 1000)) ^ 3 = x ^ (-(3 / 2 : ℝ) + 6 / 1000) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have e2 : (x ^ (-1 : ℝ)) ^ 3 = x ^ (-3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have b1 : x ^ (-3 : ℝ) ≤ x ^ (-(3 / 2 : ℝ) + 6 / 1000) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have b2 : x ^ (-2 : ℝ) ≤ x ^ (-(3 / 2 : ℝ) + 6 / 1000) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  rw [mul_pow, e1, e2]
  have h0 : 0 ≤ 2 * (n4 * G) := by positivity
  have h1 := mul_le_mul_of_nonneg_left
    (show C ^ 3 * x ^ (-(3 / 2 : ℝ) + 6 / 1000) + (x ^ (-3 : ℝ) + x ^ (-2 : ℝ)) ≤ (C ^ 3 + 2) * x ^ (-(3 / 2 : ℝ) + 6 / 1000) by
      nlinarith) h0
  calc _ ≤ 2 * (n4 * G) * ((C ^ 3 + 2) * x ^ (-(3 / 2 : ℝ) + 6 / 1000)) := h1
    _ = _ := by ring
private theorem holdsOnParameters_and {P Q : ParameterAssignment → ℝ → Prop} (hP : HoldsOnParameterFamilies P)
    (hQ : HoldsOnParameterFamilies Q) :
    HoldsOnParameterFamilies fun T y => P T y ∧ Q T y := by apply _root_.YangMills.SharedProofs.p24215 <;> assumption
private theorem holdsOnParameters_admissible :
    HoldsOnParameterFamilies fun Tb y => (Tb.stepParameters y).Admissible := by
  intro a _
  exact ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L _ _ T _ _ hD _ _ _ _ => ⟨T.floorMin, fun y hy _ _ => hD.fits y hy⟩⟩
private theorem card_le_of_subset_supBall {n : ℕ} [NeZero n] {B : Finset (TorusSite n)} {o : TorusSite n} {nn : ℝ}
    (h1 : 1 ≤ nn) (hB : ∀ z ∈ B, z ∈ supBall o (12 * nn)) : (B.card : ℝ) ≤ 25 ^ 4 * nn ^ 4 := by
  have hsub : B ⊆ Finset.univ.filter fun y : TorusSite n => supDist y o ≤ ⌊12 * nn⌋₊ := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact Nat.le_floor (Finset.mem_filter.mp (hB z hz)).2
  have h2 := (Finset.card_le_card hsub).trans (card_supDist_ball_le o ⌊12 * nn⌋₊)
  have h3 : (B.card : ℝ) ≤ (2 * (⌊12 * nn⌋₊ : ℝ) + 1) ^ 4 := by exact_mod_cast h2
  have h4 : (⌊12 * nn⌋₊ : ℝ) ≤ 12 * nn := Nat.floor_le (by linarith)
  have h5 : 2 * (⌊12 * nn⌋₊ : ℝ) + 1 ≤ 25 * nn := by linarith
  calc (B.card : ℝ) ≤ (2 * (⌊12 * nn⌋₊ : ℝ) + 1) ^ 4 := h3
    _ ≤ (25 * nn) ^ 4 := pow_le_pow_left₀ (by positivity) h5 4
    _ = 25 ^ 4 * nn ^ 4 := by ring
private theorem quadraticResponseAt_of (Tb : ParameterAssignment) (y : ℝ) (hfit : (Tb.stepParameters y).Admissible)
    (hLoc : localFunctionalQuadraticStatement) (hFam : LevelSharesUniformAt Tb y)
    (hShare : shareCurvatureFormAt Tb y) (hDesc : curvatureNearDescendedFormAt Tb y)
    (hSize : localChainSizeAt Tb y) (hMir : scoredTowerColdMirrorResponseAt Tb y)
    (hGauge : coldResponseGaugeInvariantStatement) (hExt : weightExtensionLipschitzStatement)
    (hTwo : WeightsCompatibleAcrossTori) (hNear : WeightsCloseToBlockMeans) (hMean : BlockMeanIsLinearAndLocal) :
    quadraticResponseAt Tb y := by
  intro Kr hKr
  have hσ := hfit.σ_pos
  have hr := weightRate_pos hfit
  have hodd := hfit.L_odd
  obtain ⟨C₁, c₁, ρ₁, hc₁, hL⟩ := hLoc (Tb.stepParameters y).threshold (Tb.stepParameters y).weightRate
    ((Tb.stepParameters y).weightRate / 2) hσ hr (by positivity)
  have hL' : HasLocalKernels (Tb.stepParameters y).threshold (Tb.stepParameters y).weightRate C₁ c₁ ρ₁ := hL
  obtain ⟨Cs, hCs, hfam⟩ := hFam
  obtain ⟨C₃, c₃, ρ₃, hc₃, hS⟩ := hShare (C₁ * Cs) c₁ (|C₁| * Cs) ((Tb.stepParameters y).weightRate / 2) hc₁ (by positivity)
  obtain ⟨Cd, cd, xd, hcd, hD⟩ := hDesc
  obtain ⟨Cz, cz, hCz, hcz, hZ⟩ := hSize
  obtain ⟨Cm, cm, xm, hcm, hM⟩ := hMir Kr hKr
  choose Csz xsz hSq using hZ
  have hη := hKr.η₃_pos
  have hη1 := hKr.η₃_le
  have hKc := hKr.Kc_ge
  have hKa := hKr.Ka_nonneg
  have hKc0 : 0 ≤ Kr.Kc := by linarith
  obtain ⟨c₀, hc₀, hc₀1, hc₀d, hc₀m⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧ c₀ ≤ cd ∧ c₀ ≤ cm :=
    ⟨min c₁ (min cd cm), lt_min hc₁ (lt_min hcd hcm), min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  obtain ⟨A, hA1, hA3, hA2, hAn, hAC⟩ : ∃ A : ℝ, ρ₁ ≤ A ∧ ρ₃ ≤ A ∧ 2 ≤ A ∧ ((Tb.stepParameters y).n₀ : ℝ) ≤ A ∧ 2 * |C₃| / c₃ ≤ A :=
    ⟨max (max ρ₁ ρ₃) (max 2 (max ((Tb.stepParameters y).n₀ : ℝ) (2 * |C₃| / c₃))), (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), (le_max_left _ _).trans (le_max_right _ _),
      ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _),
      ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)⟩
  obtain ⟨x₁, hx₁, hfl⟩ := eventually_radii_ordered A (Tb.stepParameters y).threshold c₀ hσ hc₀
  obtain ⟨Ka', hKa'⟩ : ∃ v : ℝ, v = Kr.Ka / Kr.η₃ := ⟨_, rfl⟩
  obtain ⟨Kc', hKc'⟩ : ∃ v : ℝ, v = Kr.Kc / Kr.η₃ := ⟨_, rfl⟩
  have hKa'0 : 0 ≤ Ka' := by
    rw [hKa']
    positivity
  have hKc'0 : 0 ≤ Kc' := by
    rw [hKc']
    positivity
  obtain ⟨Λ, hΛ⟩ : ∃ v : ℝ, v = (16 * expLatticeSum ((Tb.stepParameters y).weightRate / 2 / 2)) ^ 2 := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛ]
    positivity
  obtain ⟨B₀, hB₀⟩ : ∃ v : ℝ, v = |C₁| * (64 + 9 / 2 * Λ * |Cd| * (8 + |Cd|)) := ⟨_, rfl⟩
  have hB₀0 : 0 ≤ B₀ := by
    rw [hB₀]
    positivity
  obtain ⟨G', hG'⟩ : ∃ v : ℝ, v = 4 * (25 ^ 4 * (2 * Cs + Ka' + Kc') * B₀) + |Cm| + 1 := ⟨_, rfl⟩
  have hG'0 : 0 ≤ G' := by
    rw [hG']
    positivity
  refine ⟨fun q => 2 * G' * (|Csz (6 * q)| ^ 3 + 2), fun q => max (xsz (6 * q)) (xsz 0), |C₁| * (Cs + Ka' + 2 * Kc'),
    (Tb.stepParameters y).weightRate / 2, c₃ / 2, max x₁ (max xd xm), by positivity, by positivity, ?_⟩
  intro T S β k tp N _ nn vt al o hLC hLN hNum hal hk hSK hSrun hSal hvt0 hvt1 hvnn
  have hxfl : max x₁ (max xd xm) ≤ (couplingFlow (Tb.stepParameters y) β k).1 := hLC.floor_le
  have hx1X : x₁ ≤ (couplingFlow (Tb.stepParameters y) β k).1 := (le_max_left _ _).trans hxfl
  have hxdX : xd ≤ (couplingFlow (Tb.stepParameters y) β k).1 := ((le_max_left _ _).trans (le_max_right _ _)).trans hxfl
  have hxmX : xm ≤ (couplingFlow (Tb.stepParameters y) β k).1 := ((le_max_right _ _).trans (le_max_right _ _)).trans hxfl
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hfl (couplingFlow (Tb.stepParameters y) β k).1 hx1X
  have hX1 : 1 ≤ (couplingFlow (Tb.stepParameters y) β k).1 := hx₁.trans hx1X
  have hXpos : 0 < (couplingFlow (Tb.stepParameters y) β k).1 := by linarith
  have hρ1 : ρ₁ ≤ (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) := hA1.trans f1
  have hρ3 : ρ₃ ≤ (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) := hA3.trans f1
  have hρ2 : 2 ≤ (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) := hA2.trans f1
  have hρn : ((Tb.stepParameters y).n₀ : ℝ) ≤ (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) := hAn.trans f1
  have hρC : 2 * |C₃| / c₃ ≤ (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) := hAC.trans f1
  have hρ0 : 0 ≤ (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) := by linarith
  have hH3 : (3 : ℝ) ≤ (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) := by linarith
  have hH2 : 2 ≤ (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) := by
    have : ((2 : ℕ) : ℝ) ≤ (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) := by
      push_cast
      linarith
    exact_mod_cast this
  have hNZ : NeZero (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) := ⟨by omega⟩
  have hMs : 2 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) + 2 <
      ((4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) : ℕ) : ℝ) := by
    push_cast
    linarith
  have hn0' : (Tb.stepParameters y).n₀ ≤ 4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) := by
    have : ((Tb.stepParameters y).n₀ : ℝ) ≤ ((4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  have hnn1 : 1 ≤ nn := hLC.one_le
  have hnnX : nn ≤ (couplingFlow (Tb.stepParameters y) β k).1 ^ ((1 : ℝ) / 90) := hLC.le_rpow
  have hHr : ((mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) : ℝ) ≤
      localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1 := by
    have : 0 ≤ (couplingFlow (Tb.stepParameters y) β k).1 ^ ((1 : ℝ) / 90) := by positivity
    linarith
  have hNside : (2 : ℝ) ^ 10 * localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1 ≤ (N : ℝ) := hLC.side_ge
  have hNT : N ≤ (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) := by
    rw [fineSide_eq, fineSide_eq]
    have h1 : 1 ≤ (Tb.stepParameters y).side ^ (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne _))
    calc N = N * 1 * 1 := by simp
      _ ≤ N * (Tb.stepParameters y).side ^ (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) * (Tb.stepParameters y).side ^ (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) := Nat.mul_le_mul (Nat.mul_le_mul le_rfl h1) h1
  have hNTr : (N : ℝ) ≤ ((fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) : ℕ) := by exact_mod_cast hNT
  have hRn : logCubeScale (couplingFlow (Tb.stepParameters y) β k).1 = ((⌊Real.log (couplingFlow (Tb.stepParameters y) β k).1 ^ 3⌋₊ : ℕ) : ℝ) := rfl
  have hN2 : 2 * ⌊Real.log (couplingFlow (Tb.stepParameters y) β k).1 ^ 3⌋₊ < (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) := by
    have : ((2 * ⌊Real.log (couplingFlow (Tb.stepParameters y) β k).1 ^ 3⌋₊ : ℕ) : ℝ) < (((fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) : ℕ) : ℝ) := by
      push_cast
      rw [← hRn]
      nlinarith
    exact_mod_cast this
  have h4NT : 4 ≤ (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) := by
    have : ((4 : ℕ) : ℝ) ≤ (((fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this
  have h4M : 4 ≤ 4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) := by omega
  obtain ⟨Ra, Rb, hcl⟩ := hNum.bounds k le_rfl
  obtain ⟨hfamk, hflat⟩ := hfam k
  obtain ⟨κ0, g0⟩ := exists_isMirrorKernel_share (m := (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) hfit hL' hCs k hfamk hρ1 hρ2 hMs hn0'
  have hE : 0 ≤ Kr.Ka * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2) : ℝ) := by positivity
  obtain ⟨κ1, g1⟩ := exists_isMirrorKernel_density (m := (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) hfit hL' hE hη hη1 hcl.site_family hρ1 hρ2 hMs hn0'
  have hd2 : 0 < (Tb.stepParameters y).weightRate / 2 := by positivity
  have hloc0 := isLocalKernel_translatedKernel (n := (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N))) (m := (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) hRn hN2 hd2.le (by positivity : 0 ≤ |C₁| * Cs) g0.bound
  have hCk : |C₁| * Cs ≤ |C₁| * (Cs + Ka' + 2 * Kc') :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have hshare_eq : centered (levelShareFamily (Tb.stepParameters y).coupling (Tb.stepParameters y).side k) (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) 0 = levelShare (Tb.stepParameters y).coupling (Tb.stepParameters y).side k Finset.univ 0 := by
    funext W
    have e0 : ∀ V : TorusField (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)), levelShareFamily (Tb.stepParameters y).coupling (Tb.stepParameters y).side k (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) 0 V = levelShare (Tb.stepParameters y).coupling (Tb.stepParameters y).side k Finset.univ 0 V := by
      intro V
      unfold levelShareFamily
      rw [dif_neg (NeZero.ne _)]
    unfold centered
    rw [e0, e0, hflat _ hn0' 0, sub_zero]
  refine ⟨fun z => translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1))) (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) z κ0,
    ⟨hloc0.support, fun z p p' => (hloc0.decay z p p').trans (mul_le_mul_of_nonneg_right hCk (Real.exp_pos _).le)⟩, ?_, ?_⟩
  · intro z μ ν ρ' τ hμ hρ'
    have hord : ∀ a ∈ (plaquettesIn (supBall (0 : TorusSite (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1))) (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))), a.2.1 < a.2.2 := fun a ha => (Finset.mem_filter.mp ha).2.1
    rw [sum_translatedKernel_orientation (plaquettesIn (supBall (0 : TorusSite (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1))) (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) z κ0 hord (μ, ν) (ρ', τ)]
    have hexp : IsQuadraticInCurvature (Tb.stepParameters y).threshold (C₁ * Cs) c₁ 1 (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) (levelShare Tb.coupling (Tb.stepParameters y).side k Finset.univ 0) 0 κ0 := by
      intro g W s a1 a2 a3 a4
      have := g0.quadratic g W s a1 a2 a3 a4
      rw [hshare_eq] at this
      rw [mul_one]
      exact this
    have hc := hS k (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) 0 κ0 hρ3 hn0' hMs g0.symm g0.eq_zero_of_far g0.bound hexp μ ν ρ' τ hμ hρ'
    have hsub : (plaquettesIn (supBall (0 : TorusSite (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1))) (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) ⊆ plaquettesIn (Finset.univ : Finset (TorusSite (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)))) := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.1, fun _ _ => Finset.mem_univ _⟩
    rw [sum_filter_eq_of_support hsub κ0 g0.eq_zero_of_not_mem] at hc
    refine hc.trans ?_
    have hexp1 : |C₃| ≤ Real.exp (c₃ / 2 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1)) := by
      have b1 := Real.add_one_le_exp (c₃ / 2 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))
      have b2 : |C₃| ≤ c₃ / 2 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) := by
        rw [div_le_iff₀ hc₃] at hρC
        linarith
      linarith
    have e1 : Real.exp (-(c₃ * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) = Real.exp (-(c₃ / 2 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) * Real.exp (-(c₃ / 2 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (c₃ / 2 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1)) * Real.exp (-(c₃ / 2 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) = 1 := by
      rw [← Real.exp_add]
      simp
    have e3 : 0 < Real.exp (-(c₃ / 2 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) := Real.exp_pos _
    rw [e1]
    have e4 : C₃ ≤ Real.exp (c₃ / 2 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1)) := (le_abs_self _).trans hexp1
    calc C₃ * (Real.exp (-(c₃ / 2 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) * Real.exp (-(c₃ / 2 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))))
        ≤ Real.exp (c₃ / 2 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1)) * (Real.exp (-(c₃ / 2 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) * Real.exp (-(c₃ / 2 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1)))) :=
          mul_le_mul_of_nonneg_right e4 (by positivity)
      _ = Real.exp (-(c₃ / 2 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) := by
          rw [← mul_assoc, e2, one_mul]
  · intro h hsup hlip hsupp
    have hB : ∀ z ∈ (weightSupportSites (Tb.stepParameters y).side k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) h), z ∈ supBall o (12 * nn) := by
      intro z hz
      by_contra hzb
      obtain ⟨p, hp, hne⟩ := (Finset.mem_filter.mp hz).2
      exact hne (hsupp z p hzb hp)
    have hvn : 0 < vt * nn := by positivity
    have hLh1 : 2 / (vt * nn) ≤ 1 := by
      rw [div_le_one hvn]
      exact hvnn
    have hLh0 : 0 ≤ 2 / (vt * nn) := by positivity
    have hsz : weightNorm (Tb.stepParameters y).side k h ≤ 1 := max_le hsup (hlip.trans hLh1)
    have hsz0 : 0 ≤ weightNorm (Tb.stepParameters y).side k h := (weightLipschitz_nonneg _ _ h).trans (le_max_right _ _)
    choose h' hag hsup' hlip' using fun z : TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) => hExt (Tb.stepParameters y).side hodd k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) h4NT h4M z 0 h
    have hlip2 : ∀ z, weightLipschitz (Tb.stepParameters y).side k (h' z) ≤ 2 / (vt * nn) := fun z => (hlip' z).trans hlip
    have hP : ∀ (n : ℕ) [NeZero n] (y' : TorusSite n) (g : TorusSite n → UnitQuaternion) (W : TorusField n) (f : PlaquetteWeight (fineSide (Tb.stepParameters y).side k n)),
        (coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) al k) n y' (TorusFields.gaugeTransform g W) f = (coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) al k) n y' W f :=
      fun n _ y' g W f => hGauge (Tb.stepParameters y) hfit β (flowCouplings (Tb.stepParameters y) β) al k n y' g W f
    choose κ2 g2 using fun z : TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) => exists_isMirrorKernel_remainder (m := (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) hfit hL' hη hη1 hKc hcl.remainder hP (h' z)
      (hlip2 z) (weightLipschitz_nonneg _ _ _) hρ1 hρ2 hMs hn0'
    have hLCm : IsLocalChainAbove Tb y T β k N nn xm := { hLC with floor_le := hxmX }
    have f4' : 12 * nn + (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) ≤ localBoxRadius (flowCouplings (Tb.stepParameters y) β k) := by
      have : 12 * nn + (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) ≤ 12 * (couplingFlow (Tb.stepParameters y) β k).1 ^ ((1 : ℝ) / 90) + (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) := by linarith
      exact this.trans f4
    obtain ⟨κ₀, hκ⟩ := hM T S β k tp N nn o (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) hLCm hLN hk hSK hSrun f3 f4' h hsupp
    rw [hSal] at hκ
    have hae := hκ h' fun z _ => hag z
    have hh1 : ∀ z : TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)), |blockMean (Tb.stepParameters y).side k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) z h| ≤ 1 := fun z =>
      ((hNear (Tb.stepParameters y).side hodd k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) z).1 h).trans hsup
    have hoff : ∀ z, z ∉ (weightSupportSites (Tb.stepParameters y).side k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) h) → blockMean (Tb.stepParameters y).side k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) z h = 0 := by
      intro z hz
      have hzero : ∀ p, IsPlaquetteAt (Tb.stepParameters y).side k z p → h p = 0 := by
        intro p hp
        by_contra hne
        exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, hp, hne⟩)
      obtain ⟨-, hlin, hread⟩ := hMean (Tb.stepParameters y).side hodd k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) z
      have e1 := hread h (fun p => 0 * h p + 0 * h p) fun p hp => by
        rw [hzero p hp]
        simp
      rw [e1, hlin]
      simp
    have hD1 : 0 ≤ |C₁| * (Kr.Ka * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2) : ℝ) / Kr.η₃) := by positivity
    have hD2 : 0 ≤ |C₁| * (Kr.Kc / Kr.η₃ * (2 / (vt * nn))) := by positivity
    have hsizeD : |C₁| * (Kr.Ka * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2) : ℝ) / Kr.η₃) + |C₁| * (Kr.Kc / Kr.η₃ * (2 / (vt * nn))) ≤
        |C₁| * (Cs + Ka' + 2 * Kc') * ((couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2 : ℝ)) + 1 / (vt * nn)) := by
      have e1 : Kr.Ka * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2) : ℝ) / Kr.η₃ = Ka' * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2 : ℝ)) := by
        rw [hKa']
        ring
      have e2 : Kr.Kc / Kr.η₃ * (2 / (vt * nn)) = Kc' * (2 * (1 / (vt * nn))) := by
        rw [hKc']
        ring
      rw [e1, e2]
      exact remainder_coeff_le (abs_nonneg _) hCs hKa'0 hKc'0 (by positivity) (by positivity)
    refine ⟨κ₀, fun z p p' => if z ∈ (weightSupportSites (Tb.stepParameters y).side k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) h) then blockMean (Tb.stepParameters y).side k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) z h * translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1))) (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) z κ1 p p' +
      translatedKernel (plaquettesIn (supBall (0 : TorusSite (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1))) (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) z (κ2 z) p p' else 0, ?_, fun z hz p p' => if_neg hz, ?_⟩
    · exact isLocalKernel_remainderPart (weightSupportSites (Tb.stepParameters y).side k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) h) (fun z => blockMean (Tb.stepParameters y).side k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) z h) κ1 κ2 hRn hN2 hd2.le hD1 hD2 hsizeD hh1 g1.bound
        (fun z => (g2 z).bound)
    · intro q hq hxq
      have hxs6 : xsz (6 * q) ≤ (couplingFlow (Tb.stepParameters y) β k).1 := (le_max_left _ _).trans hxq
      have hxs0 : xsz 0 ≤ (couplingFlow (Tb.stepParameters y) β k).1 := (le_max_right _ _).trans hxq
      have hLC6 : IsLocalChainAbove Tb y T β k N nn (xsz (6 * q)) := { hLC with floor_le := hxs6 }
      have hLC0 : IsLocalChainAbove Tb y T β k N nn (xsz 0) := { hLC with floor_le := hxs0 }
      have hLCd : IsLocalChainAbove Tb y T β k N nn xd := { hLC with floor_le := hxdX }
      obtain ⟨hsm6, ⟨hi6, hm6⟩, -⟩ := hSq (6 * q) T β k N nn k (localChainDepth (Tb.stepParameters y) β k) (localChainDepth (Tb.stepParameters y) β k) o hLC6 hLN le_rfl rfl rfl
      obtain ⟨-, ⟨hi0, hm0⟩, -⟩ := hSq 0 T β k N nn k (localChainDepth (Tb.stepParameters y) β k) (localChainDepth (Tb.stepParameters y) β k) o hLC0 hLN le_rfl rfl rfl
      have hnnk : nn / ((Tb.stepParameters y).side : ℝ) ^ (k - k) = nn := by simp
      simp only [hnnk] at hsm6 hi6 hm6 hi0 hm0
      have hx₄ : 0 < (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 4 : ℝ)) := by positivity
      have hx₄1 : (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1 (by norm_num)
      have hδ : 0 < (couplingFlow (Tb.stepParameters y) β k).1 ^ (-1 : ℝ) := by positivity
      have hε0 : 0 ≤ (couplingFlow (Tb.stepParameters y) β k).1 ^ (-2 : ℝ) := by positivity
      have hε1 : (couplingFlow (Tb.stepParameters y) β k).1 ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1 (by norm_num)
      have hnear := ae_exists_small_near_abs (μ := markedSampleLaw T β (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) N)
        (Loc := fun u => IsLocalEventFrom T k (localChainDepth (Tb.stepParameters y) β k) (localChainDepth (Tb.stepParameters y) β k) (localBlockSide (Tb.stepParameters y) β k) N u o)
        (Small := fun s u => IsGaugeSmallAlong T k nn (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) s (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) (sampleBelow (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u) o (axialGaugeAt (Tb.stepParameters y) (topField (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) (sampleBelow (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u)) (siteAbove (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) o)))
        (Desc := fun s u => ∀ p ∈ plaquettesIn (supBall o (ballRadius (Tb.stepParameters y).side nn (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) 0)),
          ‖((lieFormCurl (ballLog (gaugeDescent k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) (sampleBelow (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u) (axialGaugeAt (Tb.stepParameters y) (topField (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) (sampleBelow (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u)) (siteAbove (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) o))) (topField (Tb.stepParameters y) k _ (sampleBelow (Tb.stepParameters y) k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) _ (sampleBelow (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u))) o (ballRadius (Tb.stepParameters y).side nn (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) 0)) p - (sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) nn (couplingFlow (Tb.stepParameters y) β k).1 N u o) p : imaginaryQuaternions) : Quaternion ℝ)‖ ≤
            Cd * (s ^ 2 + Real.exp (-(cd * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1)))))
        (A := fun u => (widenedChainSize T Cz cz (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) k nn (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) (sampleBelow (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u) o)) hx₄ hx₄1 hδ hsm6 (fun s a b => hD T β k N nn s o hLCd hLN a b)
      have hY0 : 0 ≤ |Csz (6 * q)| * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2 : ℝ) + 2 / 1000) := by positivity
      refine le_trans (lintegral_indicator_pow_le_of_cube_bound (A := fun u => (widenedChainSize T Cz cz (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) k nn (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) (sampleBelow (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u) o)) (b := nn ^ 4 * G') (X₀ := ((couplingFlow (Tb.stepParameters y) β k).1 ^ (-1 : ℝ)) ^ 3 + (couplingFlow (Tb.stepParameters y) β k).1 ^ (-2 : ℝ))
        (Y := |Csz (6 * q)| * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2 : ℝ) + 2 / 1000)) q hq (by positivity) (by positivity) hY0 (fun u hu => hu.1) ?_ hi6 ?_ hi0 ?_)
        (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity)
          (cube_moment_exponent_le hX1 hG'0 (abs_nonneg (Csz (6 * q))) (by positivity : 0 ≤ nn ^ 4)) _))
      · filter_upwards [hnear, hae] with u a1 a2 hu
        obtain ⟨hloc, hsm⟩ := hu
        obtain ⟨hcold, hclose⟩ := a2 hloc
        obtain ⟨s, hs0, hs1, hsA, hsmall, hdesc⟩ := a1 hloc hsm
        have hsl := norm_minimalLog_gaugeDescent_le T k nn (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) s (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) (sampleBelow (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u) o (axialGaugeAt (Tb.stepParameters y) (topField (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) (sampleBelow (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u)) (siteAbove (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) o)) hsmall
        have hb : ∀ z ∈ (weightSupportSites (Tb.stepParameters y).side k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) h), ∀ y' : TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)), (supDist y' z : ℝ) ≤ (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) → y' ∈ supBall o (ballRadius (Tb.stepParameters y).side nn (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) 0) := by
          intro z hz y' hy'
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have t1 : (supDist y' o : ℝ) ≤ supDist y' z + supDist z o := by exact_mod_cast supDist_triangle y' z o
          have t2 : (supDist z o : ℝ) ≤ 12 * nn := (Finset.mem_filter.mp (hB z hz)).2
          have t3 : (ballRadius (Tb.stepParameters y).side nn (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) 0) = 20 * nn + 4 * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) := by simp [ballRadius]
          rw [t3]
          linarith
        have hexpρ : Real.exp (-(c₀ * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) ≤ (couplingFlow (Tb.stepParameters y) β k).1 ^ (-2 : ℝ) := f6
        have hexp1 : Real.exp (-(c₁ * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) ≤ (couplingFlow (Tb.stepParameters y) β k).1 ^ (-2 : ℝ) :=
          (Real.exp_le_exp.mpr (by nlinarith)).trans hexpρ
        have hexpd : Real.exp (-(cd * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) ≤ (couplingFlow (Tb.stepParameters y) β k).1 ^ (-2 : ℝ) :=
          (Real.exp_le_exp.mpr (by nlinarith)).trans hexpρ
        have hexpm : Real.exp (-(cm * ((mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) : ℝ))) ≤ (couplingFlow (Tb.stepParameters y) β k).1 ^ (-2 : ℝ) := by
          refine (Real.exp_le_exp.mpr ?_).trans hexpρ
          have u1 : c₀ * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) ≤ cm * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) := mul_le_mul_of_nonneg_right hc₀m hρ0
          have u2 : cm * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) ≤ cm * ((mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) : ℝ) := mul_le_mul_of_nonneg_left (by linarith) hcm.le
          linarith
        have hAd : 0 ≤ |Cd| := abs_nonneg _
        have he : ∀ p ∈ plaquettesIn (supBall o (ballRadius (Tb.stepParameters y).side nn (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) 0)),
            ‖((lieFormCurl (ballLog (gaugeDescent k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) (sampleBelow (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u) (axialGaugeAt (Tb.stepParameters y) (topField (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) (sampleBelow (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u)) (siteAbove (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) o))) (topField (Tb.stepParameters y) k _ (sampleBelow (Tb.stepParameters y) k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) _ (sampleBelow (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u))) o (ballRadius (Tb.stepParameters y).side nn (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1) 0)) p - (sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) nn (couplingFlow (Tb.stepParameters y) β k).1 N u o) p : imaginaryQuaternions) : Quaternion ℝ)‖ ≤
              |Cd| * (s ^ 2 + (couplingFlow (Tb.stepParameters y) β k).1 ^ (-2 : ℝ)) := by
          intro p hp
          refine (hdesc p hp).trans ?_
          have v1 : 0 ≤ s ^ 2 + Real.exp (-(cd * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1))) := by positivity
          calc Cd * (s ^ 2 + Real.exp (-(cd * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1)))) ≤ |Cd| * (s ^ 2 + Real.exp (-(cd * (logCubeScale (couplingFlow (Tb.stepParameters y) β k).1)))) :=
                mul_le_mul_of_nonneg_right (le_abs_self _) v1
            _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hAd
        have hK1 : 0 ≤ Kr.Ka * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2) : ℝ) / Kr.η₃ := by positivity
        have hK1a : Kr.Ka * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2) : ℝ) / Kr.η₃ ≤ Ka' := by
          rw [hKa']
          refine div_le_div_of_nonneg_right ?_ hη.le
          have : (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1 (by norm_num)
          nlinarith
        have hK2 : 0 ≤ Kr.Kc / Kr.η₃ * (2 / (vt * nn)) := by positivity
        have hK2c : Kr.Kc / Kr.η₃ * (2 / (vt * nn)) ≤ Kc' := by
          rw [hKc']
          have : 0 ≤ Kr.Kc / Kr.η₃ := by positivity
          nlinarith
        have hv : ∀ z ∈ (weightSupportSites (Tb.stepParameters y).side k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) h), centeredResponse (coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) al k) (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) 0 (mirrorField (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) z (sampledLevelField k (localChainDepth (Tb.stepParameters y) β k) N u)) (h' z) =
            blockMean (Tb.stepParameters y).side k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) z h * (al k * centered (levelShareFamily (Tb.stepParameters y).coupling (Tb.stepParameters y).side k) (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) 0
                (mirrorField (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) z (sampledLevelField k (localChainDepth (Tb.stepParameters y) β k) N u)) +
              centered Ra (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) 0 (mirrorField (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) z (sampledLevelField k (localChainDepth (Tb.stepParameters y) β k) N u))) +
            centeredRemainder (coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) al k) (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) 0 (h' z) (mirrorField (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) z (sampledLevelField k (localChainDepth (Tb.stepParameters y) β k) N u)) := by
          intro z hz
          have e1 : centeredResponse (coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) al k) (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) 0 (mirrorField (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) z (sampledLevelField k (localChainDepth (Tb.stepParameters y) β k) N u)) (constOneWeight _) =
              al k * levelShare (Tb.stepParameters y).coupling (Tb.stepParameters y).side k Finset.univ 0 (mirrorField (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) z (sampledLevelField k (localChainDepth (Tb.stepParameters y) β k) N u)) + centered Ra (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) 0 (mirrorField (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) z (sampledLevelField k (localChainDepth (Tb.stepParameters y) β k) N u)) :=
            hcl.share_site _ hn0' 0 _ (hcold z hz)
          have e2 : centered (levelShareFamily (Tb.stepParameters y).coupling (Tb.stepParameters y).side k) (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) 0 (mirrorField (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) z (sampledLevelField k (localChainDepth (Tb.stepParameters y) β k) N u)) = levelShare (Tb.stepParameters y).coupling (Tb.stepParameters y).side k Finset.univ 0 (mirrorField (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1) z (sampledLevelField k (localChainDepth (Tb.stepParameters y) β k) N u)) :=
            congrFun hshare_eq _
          have e3 : blockMean (Tb.stepParameters y).side k (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) 0 (h' z) = blockMean (Tb.stepParameters y).side k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) z h :=
            ((hTwo (Tb.stepParameters y).side hodd k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1))).2.1 z 0 h (h' z) (hag z)).symm
          rw [centeredResponse_eq, e1, e2, e3]
        have hpw := abs_response_sub_form_le (weightSupportSites (Tb.stepParameters y).side k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) h) (fun z => blockMean (Tb.stepParameters y).side k (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) z h) (al k) κ0 κ1 κ2 _ _
          (fun z W => centeredRemainder (coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) al k) (4 * (mirrorHalfSide (couplingFlow (Tb.stepParameters y) β k).1)) 0 (h' z) W) g0 g1 g2 hd2 hCs hK1 hK2 hK1a hK2c hoff (fun z _ => hh1 z) hal
          (sampledLevelField k (localChainDepth (Tb.stepParameters y) β k) N u) (gaugeDescent k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) (sampleBelow (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u) (axialGaugeAt (Tb.stepParameters y) (topField (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) (sampleBelow (Tb.stepParameters y) (k + (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)) (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N u)) (siteAbove (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) o))) o hH2 f2 hb hs0 (hs1.trans hx₄1) (by linarith) hsl hcold (sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) nn (couplingFlow (Tb.stepParameters y) β k).1 N u o) hAd hε0 hε1
          hexp1 he _ hv hclose (card_le_of_subset_supBall hnn1 hB) (Real.exp_pos _).le hexpm hsz0 hsz (by positivity) hsA (abs_nonneg _) hδ.le
        rw [hG', hB₀, hΛ]
        exact hpw
      · refine hm6.trans (le_of_eq ?_)
        have ht0 : 0 ≤ flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ) + 2 / 1000) := by positivity
        have hev : Even (6 * q) := ⟨3 * q, by ring⟩
        rw [← hev.pow_abs, abs_mul, abs_of_nonneg ht0]
        rfl
      · exact hm0.trans (le_of_eq (pow_zero _))
theorem quadraticResponseStatement_holds (hLoc : localFunctionalQuadraticStatement) (hFam : levelSharesUniformStatement)
    (hShare : shareCurvatureFormStatement) (hDesc : curvatureNearDescendedFormStatement)
    (hSize : localChainSizeStatement) (hMir : scoredTowerColdMirrorResponseStatement)
    (hGauge : coldResponseGaugeInvariantStatement) (hExt : weightExtensionLipschitzStatement)
    (hTwo : WeightsCompatibleAcrossTori) (hNear : WeightsCloseToBlockMeans) (hMean : BlockMeanIsLinearAndLocal) :
    quadraticResponseStatement := by
  have h := holdsOnParameters_and holdsOnParameters_admissible (holdsOnParameters_and hFam
    (holdsOnParameters_and hShare (holdsOnParameters_and hDesc (holdsOnParameters_and hSize hMir))))
  intro a ha
  obtain ⟨L₀, r, C₀, hr, hh⟩ := h a ha
  refine ⟨L₀, r, C₀, hr, fun L hodd hL T h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  obtain ⟨y₀, hy⟩ := hh L hodd hL T h1 h2 h3 h4 h5 h6 h7
  refine ⟨y₀, fun y b1 b2 b3 => ?_⟩
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hy y b1 b2 b3
  exact quadraticResponseAt_of T y c1 hLoc c2 c3 c4 c5 c6 hGauge hExt hTwo hNear hMean
end YangMills.Construction.ResponseInTheExpansion
end
