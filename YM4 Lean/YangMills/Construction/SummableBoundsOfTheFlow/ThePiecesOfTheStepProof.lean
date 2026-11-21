import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheColdStep
import YangMills.Construction.ClusterExpansionOfAStep.FormOfTheShares
import YangMills.Construction.ClusterExpansionOfAStep.TheHotHalf
import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasTheExpansionProof
import YangMills.Construction.ColdStepAtMirrorFrames.ColdExpansionIsAnExpansionBelow
import YangMills.Construction.ColdStepAtMirrorFrames.DensitiesOfTheStep
import YangMills.Construction.RunningCouplingSlope.HessianOfAStepIsPositiveProof
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepIsTheSumOfItsDensityProof
import YangMills.Construction.SummableBoundsOfTheFlow.DisplayAtTheLeastField
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesReadBelow
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongATilt
import YangMills.Construction.SummableBoundsOfTheFlow.NumberOfASmallFamily
import YangMills.Construction.SummableBoundsOfTheFlow.StepIntegralReadsTheTotal
import YangMills.Construction.SummableBoundsOfTheFlow.SumsOfFamilies
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreNearTheirLimits
import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessIsADensity
import YangMills.Construction.SummableBoundsOfTheFlow.TheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.TheLeastFieldHasNoExcess
import YangMills.Construction.SummableBoundsOfTheFlow.TheNumberOfTheStep
import YangMills.Construction.SummableBoundsOfTheFlow.ThePiecesOfTheStep
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceIsSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.TheStepIsRegularAtTheLeastField
import YangMills.Construction.SummableBoundsOfTheFlow.TiltsReadBelow
import YangMills.Construction.SummableBoundsOfTheFlow.TopFamilyHasANorm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.StepPieces
section Cells
variable {L t n : ℕ} [NeZero n]
private theorem sum_finiteCells_torusFrame (G : (TorusFields.torusFrame L t n).Cell → ℝ) :
    ∑ Y ∈ ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n), G Y =
      ∑ y : TorusFields.TorusSite n,
        G (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top y) := by apply _root_.YangMills.SharedProofs.p21825 <;> assumption
private theorem isSmallCurvature_readAtLevel {s : ℝ} {V : TorusFields.TorusField n}
    (hV : TorusFields.IsCold s V) :
    ColdStepAtMirrorFrames.IsSmallCurvature (F := TorusFields.torusFrame L t n) s
      (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V) := by apply _root_.YangMills.SharedProofs.p2155 <;> assumption
end Cells
private theorem weight_pos (ℓ : TorusLumps.StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
private theorem isCold_mono {n : ℕ} {s s' : ℝ} {V : TorusFields.TorusField n} (hs : s ≤ s')
    (hV : TorusFields.IsCold s V) : TorusFields.IsCold s' V :=
  fun x μ ν h => lt_of_lt_of_le (hV x μ ν h) hs
private theorem trivialField_isCold {s : ℝ} (hs : 0 < s) (n : ℕ) :
    TorusFields.IsCold s (TorusFields.trivialField n) := by apply _root_.YangMills.SharedProofs.p4747 <;> assumption
private theorem mixedDeriv_zero {n : ℕ} (G : TorusFields.TorusField n → ℝ) (W : TorusFields.TorusField n)
    (c : Fin 0 → TorusFields.TorusBond n) (X : Fin 0 → BlockAverages.imaginaryQuaternions) :
    TorusFields.mixedDeriv G W c X = G W := by apply _root_.YangMills.Construction.TorusLumps.mixedDeriv_of_fin_zero <;> assumption
private theorem mixedDeriv_sub_const {n k : ℕ} (hk : 1 ≤ k) (G : TorusFields.TorusField n → ℝ) (κ : ℝ)
    (W : TorusFields.TorusField n) (c : Fin k → TorusFields.TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions)
    (h : ContDiffAt ℝ k (fun σ : Fin k → ℝ => G (TorusFields.perturb c X σ W)) 0) :
    TorusFields.mixedDeriv (fun V => G V - κ) W c X = TorusFields.mixedDeriv G W c X := by apply _root_.YangMills.SharedProofs.p1322 <;> assumption
private theorem isNormBoundedFamily_of_isSmallDensity {ℓ : TorusLumps.StepParameters} {e : ℝ}
    {g : TorusLumps.LocalDensity} (hσ : 0 < ℓ.threshold) (he : 0 ≤ e)
    (H : TorusLumps.IsSmallDensity ℓ e g) : FamilyNorms.IsNormBoundedFamily ℓ (2 * e) (2 * e) g := by
  have hw := weight_pos ℓ
  refine ⟨⟨H.smooth, H.gauge, H.translation⟩, ?_, ?_⟩
  · intro n _ hn y W hW k c X k1 k3 hX
    refine (H.decay n hn y W hW k c X k1 k3 hX).trans ?_
    beta_reduce
    rw [if_congr Iff.rfl rfl rfl, ite_self]
    exact div_le_div_of_nonneg_right (by linarith) (hw _).le
  · intro n n' _ _ hn hn' y y' W W' m h1 h2 hW hW' hA k b X hk hb hX
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have a1 := H.local_density n n' hn hn' y y' W W' m h1 h2 hW hW' hA 0 b X hk hb hX
      have a2 := H.local_density n n' hn hn' y y' (TorusFields.trivialField n) (TorusFields.trivialField n') m h1 h2
        (trivialField_isCold hσ n) (trivialField_isCold hσ n') (fun _ _ => rfl) 0 b X hk hb hX
      simp only [mixedDeriv_zero] at a1 a2 ⊢
      simp only [TorusLumps.centeredFamily, TorusLumps.centered]
      have a3 : 2 * e / ℓ.weight m = e / ℓ.weight m + e / ℓ.weight m := by ring
      rw [a3]
      rw [abs_le] at a1 a2 ⊢
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
    · have a1 := H.local_density n n' hn hn' y y' W W' m h1 h2 hW hW' hA k b X hk hb hX
      have s1 := (H.smooth n hn y W hW k (fun l => TorusLumps.bondFrom y (b l)) X).of_le (m := k)
        (by exact_mod_cast (show k ≤ 3 by omega))
      have s2 := (H.smooth n' hn' y' W' hW' k (fun l => TorusLumps.bondFrom y' (b l)) X).of_le (m := k)
        (by exact_mod_cast (show k ≤ 3 by omega))
      have e1 : TorusFields.mixedDeriv (TorusLumps.centeredFamily g n y) W (fun l => TorusLumps.bondFrom y (b l)) X =
          TorusFields.mixedDeriv (g n y) W _ X :=
        mixedDeriv_sub_const hk1 (g n y) _ W _ X s1
      have e2 : TorusFields.mixedDeriv (TorusLumps.centeredFamily g n' y') W' (fun l => TorusLumps.bondFrom y' (b l)) X =
          TorusFields.mixedDeriv (g n' y') W' _ X :=
        mixedDeriv_sub_const hk1 (g n' y') _ W' _ X s2
      rw [e1, e2]
      refine a1.trans (div_le_div_of_nonneg_right (by linarith) (hw _).le)
private theorem isSmallCurvature_mono {F : BlockAverages.BlockFrame} {j : ℕ} {s s' : ℝ} {V : F.GaugeField j}
    (hs : s ≤ s') (hV : ColdStepAtMirrorFrames.IsSmallCurvature s V) :
    ColdStepAtMirrorFrames.IsSmallCurvature s' V := fun p h => lt_of_lt_of_le (hV p h) hs
private theorem exp_le_weightGrowthSup_div {ℓ : TorusLumps.StepParameters} (hf : ℓ.Admissible)
    (hG : ∀ m : ℕ, Real.exp (-(ℓ.rt / 2 ^ 9 * m)) ≤ TorusLumps.weightGrowthSup ℓ.rt ℓ.n₁ / ℓ.weight m) (m : ℕ) :
    Real.exp (-(ℓ.rt / 2 ^ 6 * m)) ≤ TorusLumps.weightGrowthSup ℓ.rt ℓ.n₁ / ℓ.weight m := by
  refine le_trans ?_ (hG m)
  apply Real.exp_le_exp.mpr
  have : (0 : ℝ) ≤ ℓ.rt * m := mul_nonneg hf.rt_pos.le (Nat.cast_nonneg m)
  nlinarith
private theorem minimizerDensity_sub_eq (S : ColdStepAtMirrorFrames.StepParameters) (t : ℕ) (x : ℝ) :
    S.minimizerDensity t x - S.referenceDensity (t + 1) -
        S.oneLoopCoeff t • ShareFamilies.levelShareFamily S.a S.L (t + 1) =
      ColdStepAtMirrorFrames.densityOfTopFamily S.L t (StepDensities.densityExcess S t x) := by
  funext n y V
  simp only [ColdStepAtMirrorFrames.StepParameters.minimizerDensity, ScaledVariables.minimizerDensities,
    ColdStepAtMirrorFrames.StepParameters.referenceDensity, ReferenceDensity.referenceFamily,
    ColdStepAtMirrorFrames.StepParameters.oneLoopCoeff, ReferenceDensity.stepDensityFamily,
    ReferenceDensity.familyAtMinimizer, StepDensities.densityExcess, ColdStepAtMirrorFrames.densityOfTopFamily,
    Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ColdStepAtMirrorFrames.StepParameters.localReference]
  ring
set_option maxHeartbeats 8000000 in
theorem stepPiecesStatement_holds
    (hCl : ColdStepAtMirrorFrames.stepDensityBoundsStatement) (hTM : BlockMeans.segmentMeanStatement)
    (hX7 : Interpolation.frameInterpolationStatement)
    (hFBs : Interpolation.interpolatedFramesStatement) (hEnds : Interpolation.interpolationAtEndpoints)
    (hRS : StepDensities.referenceSmoothStatement) (hEx : StepDensities.densitiesNearLimitsStatement)
    (hDn : StepDensities.densityExcessIsLocalDensity) (hNu : StepDensities.stepCurvatureValueStatement)
    (hLR : Interpolation.regularStepAtMinimizerStatement) (hHot : ClusterExpansionOfAStep.HotFactorization)
    (hCold : StepSettings.ColdImageFactorsThroughColdStep) (hSh : ShareFamilies.LevelSharesFormCurvatureFamily)
    (hFm : ShareFamilies.LevelSharesHaveUnitCurvatureForm) (hRB : FamilyNorms.vanishingFormLocalFamilyStatement)
    (hFBw : FamilyNorms.localFamilyNormStatement)
    (hCR : ColdStepAtMirrorFrames.ColdExpansionRegular)
    (hTot : ColdStepAtMirrorFrames.stepIntegralDependsOnlyOnFunctional)
    (hDisp : Interpolation.logIntegralAtMinimizerStatement) (hLog : Interpolation.logIntegralAlongSegmentStatement)
    (hNoX : Interpolation.minimizerExcessSumZero) (hTop : FamilyNorms.topFamilyNormStatement)
    (hSm : FamilyNorms.smallFamilyValueStatement) (hs : FamilyNorms.normBoundedFamilyClosureStatement)
    (hn : FamilyNorms.curvatureValueLinearityStatement)
    (hNT : TorusLumps.PotentialSumsFinite) : FamilyNorms.stepPiecesStatement := by
  obtain ⟨Cq, Cz, Cr, hFB⟩ := hFBs
  obtain ⟨rtH, hrtH, hHot'⟩ := hHot
  unfold StepDensities.referenceSmoothStatement ColdStepAtMirrorFrames.EventuallyOrdered at hRS
  unfold StepDensities.densitiesNearLimitsStatement ColdStepAtMirrorFrames.EventuallyOrdered at hEx
  unfold StepDensities.densityExcessIsLocalDensity ColdStepAtMirrorFrames.EventuallyOrdered at hDn
  unfold StepDensities.stepCurvatureValueStatement ColdStepAtMirrorFrames.EventuallyOrdered at hNu
  refine ⟨_, ((((((((hCl.and hTM).and hX7).and hFB).and hRS).and hEx).and hDn).and hNu).and hLR), rtH, hrtH, ?_⟩
  intro T hDr hrt hOn
  obtain ⟨c₀, nss, hTies, hOnAll⟩ := hOn
  obtain ⟨hδ₁, hlam, hρ, hσA, hcg, hNN, hδc, hHolds⟩ := id hTies
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨qCl, qMn⟩, qX7⟩, qFB⟩, qRS⟩, qEx⟩, qDn⟩, qNu⟩, qLR⟩ := hOnAll T.yC le_rfl
  set S : ColdStepAtMirrorFrames.StepParameters := T.stepParamsAt c₀ nss T.yC with hS
  have hE1 : 1 ≤ T.E := by
    have := hDr.B_ge
    show 1 ≤ 4 * T.B
    linarith
  have hSD : S.IsOrdered :=
    ⟨hDr.a_ge, hDr.L_odd, hHolds, hDr.rt_pos, hDr.η₃_pos, hDr.η₃_le, hDr.σ_pos, hDr.cut, hE1⟩
  have hn0 : 1 ≤ S.n₀ := by
    have := hDr.n₀_ge
    show 1 ≤ T.n₀
    omega
  have hMat : ∀ y, S.Compatible (T.stepParameters y) := fun y => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hfit₀ : (T.stepParameters T.floorMin).Admissible := hDr.fits _ le_rfl
  have hRoom : S.AdmitsReference := by
    refine ⟨?_, T.stepParameters T.floorMin, hMat _, hfit₀⟩
    show 4 * TorusLumps.expansionConstant T.Cs (TorusLumps.maxOfFirstFour c₀.N) T.rt ((T.side : ℝ) ^ (1 / 640 : ℝ)) ≤
      4 * T.B
    rw [hNN]
    exact le_rfl
  obtain ⟨Eh, hEh⟩ := qRS hSD hn0 hRoom
  obtain ⟨yE, CX, hyE, hCX, hEx'⟩ := qEx hSD hn0 hRoom
  obtain ⟨yD, -, hDn'⟩ := qDn hSD hn0 hRoom
  obtain ⟨yN, CN₁, -, -, hNu'⟩ := qNu hSD hn0 hRoom
  obtain ⟨CNs, hCNs, hX⟩ := qX7
  obtain ⟨yH, hH⟩ := hHot' T hDr hrt
  have hColdStep : T.ColdStepHolds := ⟨c₀, nss, hTies, fun y hy => (hOnAll y hy).1.1.1.1.1.1.1.1⟩
  obtain ⟨yC', hC⟩ := hCold T hDr hColdStep
  obtain ⟨hσ₀, hκ₀⟩ := And.intro hDr.σ_pos hDr.rt_pos
  have hNTf := hNT T.rt T.n₁ hDr.rt_pos hfit₀.n₁_pos
  obtain ⟨-, -, -, -, -, hG0, hG1⟩ := hNTf
  set G : ℝ := TorusLumps.weightGrowthSup T.rt T.n₁ with hGd
  set SG : ℝ := TorusLumps.potentialWeightSum T.rt T.n₁ with hSG
  have hCE : 0 < T.CE := hDr.CE_pos
  have hCN2 : 0 < CNs 2 := hCNs 2
  set M : ℝ := max CN₁ 0 with hMd
  have hM0 : 0 ≤ M := le_max_right _ _
  set C₀ : ℝ := 1 + CX * G + T.CE * G + T.CE + CNs 2 * G + CNs 2 + M + SG with hC₀d
  have hNa0 : 0 ≤ FamilyNorms.shareBound T := by
    unfold FamilyNorms.shareBound
    have hpos := hDr.chain.2.2.2.2.2.2.2.1 0
    have : 0 ≤ TorusLumps.maxOfFirstFour T.N := by
      unfold TorusLumps.maxOfFirstFour
      exact le_trans hpos.le (le_trans (le_max_left _ _) (le_max_left _ _))
    exact mul_nonneg (by linarith) this
  have hC₀1 : 1 ≤ C₀ := by
    have a1 : 0 ≤ CX * G := by positivity
    have a2 : 0 ≤ T.CE * G := by positivity
    have a3 : 0 ≤ CNs 2 * G := by positivity
    rw [hC₀d]
    linarith
  have hch : 0 < T.gasRate := by
    have hκ := hDr.κ_pos
    have hcE := hDr.cE_pos
    have hσ2 : 0 < T.threshold ^ 2 := by positivity
    have hκ₁ : 0 < T.κ₁ := lt_min (by positivity) (by positivity)
    unfold RenormalizationStepParameters.ParameterAssignment.gasRate
    have : 0 < min T.cE (min (T.κ * T.threshold ^ 2) (T.κ₁ * T.threshold ^ 2)) :=
      lt_min hcE (lt_min (by positivity) (by positivity))
    positivity
  have hev1 : ∀ᶠ x : ℝ in Filter.atTop,
      (C₀ + 3 * C₀ * FamilyNorms.shareBound T) * x ^ (-(1 / 2 : ℝ)) ≤ 1 / 16 := by
    have t0 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
      (C₀ + 3 * C₀ * FamilyNorms.shareBound T)
    rw [mul_zero] at t0
    exact t0.eventually_le_const (by norm_num)
  have hev2 : ∀ᶠ x : ℝ in Filter.atTop, 2 * Real.exp (-(T.gasRate * x / 2)) ≤ x ^ (-(2 : ℝ)) := by
    have t1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
      (Filter.tendsto_id.const_mul_atTop (by positivity : 0 < T.gasRate / 2))
    have hpos : 0 < (T.gasRate / 2) ^ 2 / 2 := by positivity
    filter_upwards [t1.eventually_le_const hpos, Filter.eventually_gt_atTop 0] with x hx hx0
    simp only [Function.comp, id] at hx
    have e1 : x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
      rw [Real.rpow_neg hx0.le]
      norm_num
    have e2 : -(T.gasRate * x / 2) = -(T.gasRate / 2 * x) := by ring
    rw [e1, e2]
    have hxx : 0 < x ^ 2 := by positivity
    set Ex := Real.exp (-(T.gasRate / 2 * x)) with hEx0
    have hc2 : 0 < (T.gasRate / 2) ^ 2 := by positivity
    have h1 : x ^ 2 * Ex ≤ 1 / 2 := by
      have h2 : (T.gasRate / 2) ^ 2 * (x ^ 2 * Ex) ≤ (T.gasRate / 2) ^ 2 * (1 / 2) := by
        have e3 : (T.gasRate / 2 * x) ^ 2 * Ex = (T.gasRate / 2) ^ 2 * (x ^ 2 * Ex) := by ring
        rw [← e3]
        linarith
      exact le_of_mul_le_mul_left h2 hc2
    rw [show (x ^ 2)⁻¹ = 1 / x ^ 2 by simp, le_div_iff₀ hxx]
    nlinarith
  have hev3 : ∀ᶠ x : ℝ in Filter.atTop, 2 ^ 40 * T.side ≤ TorusLumps.clusterRange x := by
    have t1 := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)
    filter_upwards [t1.eventually_ge_atTop ((2 ^ 40 * T.side : ℕ) : ℝ)] with x hx
    have := Nat.le_ceil (x ^ ((1 : ℝ) / 100))
    have h2 : ((2 ^ 40 * T.side : ℕ) : ℝ) ≤ (TorusLumps.clusterRange x : ℝ) := hx.trans this
    exact_mod_cast h2
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.mp (hev1.and (hev2.and hev3))
  set y₀ : ℝ := max (max (max T.floorMin T.yC) (max yE yD)) (max (max yN yH) (max yC' (max Y₁ 1))) with hy₀
  have b1 : T.floorMin ≤ y₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have b2 : T.yC ≤ y₀ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have b3 : yE ≤ y₀ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have b4 : yD ≤ y₀ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have b5 : yN ≤ y₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have b6 : yH ≤ y₀ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have b7 : yC' ≤ y₀ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have b8 : Y₁ ≤ y₀ := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
    (le_max_right _ _)
  have b9 : (1 : ℝ) ≤ y₀ := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
    (le_max_right _ _)
  have hrefEq : ∀ t, FamilyNorms.ParameterAssignment.reference T t = S.referenceDensity t := by
    intro t
    show ReferenceDensity.referenceFamily T.coupling T.ρA T.lam T.side t =
      ReferenceDensity.referenceFamily T.coupling c₀.ρA c₀.lam T.side t
    rw [hρ, hlam]
  have hfirst : ∀ t, FamilyNorms.ParameterAssignment.oneLoop T t = S.oneLoopCoeff t := by
    intro t
    show ReferenceDensity.oneLoopCoefficient T.coupling T.ρA T.lam T.side t =
      ReferenceDensity.oneLoopCoefficient T.coupling c₀.ρA c₀.lam T.side t
    rw [hρ, hlam]
  have hsec : ∀ t, FamilyNorms.ParameterAssignment.secondStep T t = S.secondCoeff t := by
    intro t
    show ScaledVariables.secondStepCoefficient T.coupling T.ρA T.lam T.side t =
      ScaledVariables.secondStepCoefficient T.coupling c₀.ρA c₀.lam T.side t
    rw [hρ, hlam]
  have hNuAll := hNu' (T.stepParameters T.floorMin) (hMat _) hfit₀
  refine ⟨C₀, M, y₀, by linarith, hNa0, hM0, ?_, ?_, ?_⟩
  · intro t
    rw [hsec]
    exact (hNuAll t).1.2.trans (le_max_left _ _)
  · intro y hy t
    rw [hrefEq]
    exact (hEh (T.stepParameters y) (hMat y) (hDr.fits y hy) t).family
  intro y hy t x D ε h hx hε hrow hTi hθ
  have hyT : T.floorMin ≤ y := b1.trans hy
  have hxy₀ : y₀ ≤ x := hy.trans hx
  have hx1 : 1 ≤ x := b9.trans hxy₀
  have hx0 : 0 < x := by linarith
  obtain ⟨ev1, ev2, ev3⟩ := hY₁ x (b8.trans hxy₀)
  have hfit : (T.stepParameters y).Admissible := hDr.fits y hyT
  have hxS : S.coupling ≤ x := b2.trans hxy₀
  rw [hrefEq t] at hTi hθ
  rw [hrefEq (t + 1), hfirst t, hsec t]
  obtain ⟨hArr, f₂, hcold, Λ, Dq, Φ, φl, hHull⟩ := hrow
  let R : StepSettings.StepSetup := ⟨T.stepParameters y, t, x, x, D, f₂, Λ, Dq, Φ, φl, c₀.ρA, T.cutoff⟩
  have hLge : 1 ≤ T.side := by
    have h2 : 2 ^ 16 ≤ T.side := (hDr.fits _ le_rfl).L_ge
    omega
  have hr16 : 2 ^ 16 ≤ TorusLumps.clusterRange x := by
    have : 2 ^ 16 * 1 ≤ 2 ^ 40 * T.side := Nat.mul_le_mul (by norm_num) hLge
    omega
  have hOnT : R.OnParameters T y :=
    ⟨rfl, hρ, rfl, hx, ⟨⟨hcold, hHull⟩, by show x ≤ 1.01 * x; linarith, Nat.le_succ _⟩⟩
  obtain ⟨hsmall, hhot⟩ := hH y (b6.trans hy) R hOnT hArr
  have hcoldI := hC y (b7.trans hy) R hOnT
  have hF1 := hθ 1 zero_le_one le_rfl
  rw [one_smul] at hF1
  have hη : 0 < T.η₃ := hDr.η₃_pos
  have hE0 : 0 < T.E := by linarith
  have h3 : FamilyNorms.thirdOrderSize (T.stepParameters y) ε = ε / T.η₃ := by
    show ε * T.E₃ / T.E = ε / T.η₃
    have : T.E₃ = T.E / T.η₃ := rfl
    rw [this]
    field_simp
  have hFamθ : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      FamilyNorms.IsNormBoundedLocalFamily S.L t S.n₀ S.σ S.decayRate S.E (S.E / S.η₃)
        (S.localReference t + θ • ColdStepAtMirrorFrames.localFamilyOfDensity h) :=
    fun θ a1 a2 => hFBw (T.stepParameters y) t _ _ _ hfit rfl (hθ θ a1 a2)
  have hrowh : ColdStepAtMirrorFrames.IsRegularFamily S.L t S.n₀ S.σ S.decayRate ε (ε / S.η₃)
      (ColdStepAtMirrorFrames.localFamilyOfDensity h) := by
    have := hRB (T.stepParameters y) t ε _ h hfit rfl hTi.normBounded hTi.curvatureForm_vanishes
    rw [h3] at this
    exact this
  have hMean := qMn t x (S.localReference t) (ColdStepAtMirrorFrames.localFamilyOfDensity h) ε hxS hε hFamθ hrowh
  have hFam1 : FamilyNorms.IsNormBoundedLocalFamily S.L t S.n₀ S.σ S.decayRate S.E (S.E / S.η₃)
      (ColdStepAtMirrorFrames.localFamilyOfDensity (S.referenceDensity t + h)) :=
    hFBw (T.stepParameters y) t _ _ _ hfit rfl hF1
  have fc := hX t x _ hxS hFam1
  have hRef0 := hEh (T.stepParameters y) (hMat y) hfit
  have hcold' : TorusLumps.ColdExpansion (T.stepParameters y) t x D (S.referenceDensity t + h) := by
    refine ⟨hcold.positive, hF1.admissible.smooth, hF1.admissible.gauge, hF1.admissible.translation,
      hTi.log_density_eq, hF1.decay, hF1.comparison, fun A A' hA hA' => ?_⟩
    have := ((hn (T.stepParameters y) hfit).2.2.1 _ _ _ _ (hRef0 t).family.admissible hTi.normBounded.admissible
      (hRef0 t).vanishing_curvatureForm hTi.curvatureForm_vanishes).2 A A' hA hA'
    simp only [add_zero, zero_mul] at this
    exact this
  have hGb := (hTop (T.stepParameters y) hfit).2.2
  have hGb6 := exp_le_weightGrowthSup_div hfit hGb
  have hw0 := weight_pos (T.stepParameters y)
  set u : ℝ := x ^ (-(3 / 4 : ℝ)) with hu
  set v : ℝ := x ^ (-(1 / 2 : ℝ)) with hv
  set z : ℝ := x ^ (-(2 : ℝ)) with hz
  have u0 : 0 < u := Real.rpow_pos_of_pos hx0 _
  have v0 : 0 < v := Real.rpow_pos_of_pos hx0 _
  have z0 : 0 < z := Real.rpow_pos_of_pos hx0 _
  have qu : x⁻¹ ≤ u := by
    have : x ^ (-(1 : ℝ)) ≤ u := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rwa [Real.rpow_neg_one] at this
  have zq : (x ^ 2)⁻¹ = z := by
    rw [hz, Real.rpow_neg hx0.le]
    norm_num
  have hσle : T.threshold ≤ 9 / 8 * T.threshold := by linarith
  have hσle' : T.threshold ≤ 5 / 4 * T.threshold := by linarith
  have h59 : 9 / 8 * T.threshold ≤ 5 / 4 * T.threshold := by linarith
  have hGdef : TorusLumps.weightGrowthSup (T.stepParameters y).rt (T.stepParameters y).n₁ = G := rfl
  rw [hGdef] at hGb hGb6
  have hC₀CX : CX * G ≤ C₀ := by
    have a2 : 0 ≤ T.CE * G := by positivity
    have a3 : 0 ≤ CNs 2 * G := by positivity
    have a4 : 0 ≤ SG := hG0
    rw [hC₀d]
    linarith
  have hC₀CE : T.CE * G ≤ C₀ := by
    have a2 : 0 ≤ CX * G := by positivity
    have a3 : 0 ≤ CNs 2 * G := by positivity
    have a4 : 0 ≤ SG := hG0
    rw [hC₀d]
    linarith
  have hC₀CE' : T.CE ≤ C₀ := by
    have a2 : 0 ≤ CX * G := by positivity
    have a2' : 0 ≤ T.CE * G := by positivity
    have a3 : 0 ≤ CNs 2 * G := by positivity
    have a4 : 0 ≤ SG := hG0
    rw [hC₀d]
    linarith
  have hC₀CN : CNs 2 * G ≤ C₀ := by
    have a2 : 0 ≤ CX * G := by positivity
    have a2' : 0 ≤ T.CE * G := by positivity
    have a4 : 0 ≤ SG := hG0
    rw [hC₀d]
    linarith
  have hC₀CN' : CNs 2 ≤ C₀ := by
    have a2 : 0 ≤ CX * G := by positivity
    have a2' : 0 ≤ T.CE * G := by positivity
    have a3 : 0 ≤ CNs 2 * G := by positivity
    have a4 : 0 ≤ SG := hG0
    rw [hC₀d]
    linarith
  have hC₀M : M ≤ C₀ := by
    have a2 : 0 ≤ CX * G := by positivity
    have a2' : 0 ≤ T.CE * G := by positivity
    have a3 : 0 ≤ CNs 2 * G := by positivity
    have a4 : 0 ≤ SG := hG0
    rw [hC₀d]
    linarith
  have hC₀SG : SG ≤ C₀ := by
    have a2 : 0 ≤ CX * G := by positivity
    have a2' : 0 ≤ T.CE * G := by positivity
    have a3 : 0 ≤ CNs 2 * G := by positivity
    rw [hC₀d]
    linarith
  have FX : FamilyNorms.IsNormBoundedFamily (T.stepParameters y) (C₀ * u) (C₀ * u)
      (ColdStepAtMirrorFrames.densityOfTopFamily T.side t (StepDensities.densityExcess S t x)) := by
    refine (hTop (T.stepParameters y) hfit).1 t (9 / 8 * T.threshold) (9 / 8 * T.threshold) _ _ _
      (fun _ m => CX * x⁻¹ * Real.exp (-(T.rt / 2 ^ 6 * m))) (fun r => CX * u * Real.exp (-(T.rt / 2 ^ 9 * r)))
      hσle hσle (hDn' t x (b4.trans hxy₀)) ?_ (hEx' t x (b3.trans hxy₀)).2 ?_ ?_
    · intro F hF Y V k c X hV k1 k3 hX
      exact (hEx' t x (b3.trans hxy₀)).1 F Y V k c X hF (isSmallCurvature_mono h59 hV) k3 hX
    · intro k m k1 k3
      rw [ite_self]
      have e1 := hGb6 m
      calc CX * x⁻¹ * Real.exp (-(T.rt / 2 ^ 6 * m)) ≤ CX * x⁻¹ * (G / (T.stepParameters y).weight m) :=
            mul_le_mul_of_nonneg_left e1 (by positivity)
        _ = (CX * G * x⁻¹) / (T.stepParameters y).weight m := by ring
        _ ≤ (C₀ * u) / (T.stepParameters y).weight m := by
            refine div_le_div_of_nonneg_right ?_ (hw0 m).le
            exact mul_le_mul hC₀CX qu (by positivity) (by linarith)
    · intro m
      have e1 := hGb m
      calc CX * u * Real.exp (-(T.rt / 2 ^ 9 * m)) ≤ CX * u * (G / (T.stepParameters y).weight m) :=
            mul_le_mul_of_nonneg_left e1 (by positivity)
        _ = (CX * G * u) / (T.stepParameters y).weight m := by ring
        _ ≤ (C₀ * u) / (T.stepParameters y).weight m := by
            refine div_le_div_of_nonneg_right ?_ (hw0 m).le
            exact mul_le_mul_of_nonneg_right hC₀CX u0.le
  have hbar : ∀ (k m : ℕ), (2⁻¹ : ℝ) ^ 6 * (if k = 3 then ε / T.η₃ else ε) /
        BlockAverages.torusDecayFactor T.side S.decayRate (m : ℝ) +
      T.CE * ε * v * Real.exp (-(T.rt / 2 ^ 6 * m)) ≤
      (if k = 3 then FamilyNorms.thirdOrderSize (T.stepParameters y) (ε / 16) + C₀ * ε * v
        else ε / 16 + C₀ * ε * v) / (T.stepParameters y).weight m := by
    intro k m
    have hdw : BlockAverages.torusDecayFactor T.side S.decayRate (m : ℝ) = (T.stepParameters y).weight m := rfl
    rw [hdw]
    have e1 := hGb6 m
    have e2 : T.CE * ε * v * Real.exp (-(T.rt / 2 ^ 6 * m)) ≤ (C₀ * ε * v) / (T.stepParameters y).weight m := by
      calc T.CE * ε * v * Real.exp (-(T.rt / 2 ^ 6 * m)) ≤ T.CE * ε * v * (G / (T.stepParameters y).weight m) :=
            mul_le_mul_of_nonneg_left e1 (by positivity)
        _ = (T.CE * G * ε * v) / (T.stepParameters y).weight m := by ring
        _ ≤ _ := by
            refine div_le_div_of_nonneg_right ?_ (hw0 m).le
            have := mul_le_mul_of_nonneg_right hC₀CE (by positivity : 0 ≤ ε * v)
            linarith
    split_ifs with hk
    · have e3 : FamilyNorms.thirdOrderSize (T.stepParameters y) (ε / 16) = ε / T.η₃ / 16 := by
        show ε / 16 * T.E₃ / T.E = ε / T.η₃ / 16
        have : T.E₃ = T.E / T.η₃ := rfl
        rw [this]
        field_simp
      rw [e3, add_div]
      have e4 : (2⁻¹ : ℝ) ^ 6 * (ε / T.η₃) / (T.stepParameters y).weight m ≤
          ε / T.η₃ / 16 / (T.stepParameters y).weight m := by
        refine div_le_div_of_nonneg_right ?_ (hw0 m).le
        have : 0 ≤ ε / T.η₃ := by positivity
        norm_num
        linarith
      linarith
    · rw [add_div]
      have e4 : (2⁻¹ : ℝ) ^ 6 * ε / (T.stepParameters y).weight m ≤ ε / 16 / (T.stepParameters y).weight m := by
        refine div_le_div_of_nonneg_right ?_ (hw0 m).le
        norm_num
        linarith
      linarith
  have FM : FamilyNorms.IsNormBoundedFamily (T.stepParameters y) (ε / 16 + C₀ * ε * v)
      (FamilyNorms.thirdOrderSize (T.stepParameters y) (ε / 16) + C₀ * ε * v)
      (ColdStepAtMirrorFrames.densityOfTopFamily T.side t
        (BlockMeans.segmentAveragedMean T.coupling c₀.ρA (T.threshold / 64) x (ColdStepAtMirrorFrames.frameRadius x) T.cutoff
          (S.localReference t) (ColdStepAtMirrorFrames.localFamilyOfDensity h))) := by
    refine (hTop (T.stepParameters y) hfit).1 t (5 / 4 * T.threshold) (9 / 8 * T.threshold) _ _ _ _ _ hσle' hσle
      hMean.density hMean.decay hMean.locality ?_ ?_
    · intro k m _ _
      exact hbar k m
    · intro m
      have hdw : BlockAverages.torusDecayFactor T.side S.decayRate (m : ℝ) = (T.stepParameters y).weight m := rfl
      show (2⁻¹ : ℝ) ^ 4 * ε / BlockAverages.torusDecayFactor T.side S.decayRate (m : ℝ) ≤ _
      rw [hdw]
      refine div_le_div_of_nonneg_right ?_ (hw0 m).le
      have : 0 ≤ C₀ * ε * v := by positivity
      norm_num
      linarith
  have hδ₂ : 0 < c₀.δ₂ := by rw [hδc]; exact hDr.δc_pos
  have hω : Real.exp (-(S.chainParams.δ₂ / 4 * ColdStepAtMirrorFrames.frameRadius x)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ S.chainParams.δ₂ / 4 * (ColdStepAtMirrorFrames.frameRadius x : ℝ) := by
      have h1 : 0 < S.chainParams.δ₂ := hδ₂
      positivity
    linarith
  set gapTop : ColdStepAtMirrorFrames.TopLevelFamily :=
    Interpolation.blockGapDensity T.coupling c₀.ρA (T.threshold / 64) x (ColdStepAtMirrorFrames.frameRadius x) T.cutoff
      (ColdStepAtMirrorFrames.localFamilyOfDensity (S.referenceDensity t + h)) with hgap
  have hcent : ColdStepAtMirrorFrames.IsLocalOnTori T.side t T.n₀ (9 / 8 * T.threshold)
      (ColdStepAtMirrorFrames.centredFamily gapTop)
      fun r => CNs 2 * (x ^ 2)⁻¹ / BlockAverages.torusDecayFactor T.side S.decayRate (r : ℝ) := by
    intro F F' hF hF' Y Y' V V' r k hh X hV hV' hAg hk hb hX
    have e1 : ColdStepAtMirrorFrames.centredFamily gapTop F Y = gapTop F Y := by
      funext W
      exact sub_eq_self.mpr (fc.eq_zero_at_uniform F hF Y)
    have e2 : ColdStepAtMirrorFrames.centredFamily gapTop F' Y' = gapTop F' Y' := by
      funext W
      exact sub_eq_self.mpr (fc.eq_zero_at_uniform F' hF' Y')
    rw [e1, e2]
    exact fc.locality 2 F F' hF hF' Y Y' V V' r k hh X hV hV' hAg hk hb hX
  have FE : FamilyNorms.IsNormBoundedFamily (T.stepParameters y) (C₀ * z) (C₀ * z)
      (ColdStepAtMirrorFrames.densityOfTopFamily T.side t gapTop) := by
    refine (hTop (T.stepParameters y) hfit).1 t (5 / 4 * T.threshold) (9 / 8 * T.threshold) _ _ _
      (fun _ m => CNs 2 * (x ^ 2)⁻¹ * Real.exp (-(S.chainParams.δ₂ / 4 * ColdStepAtMirrorFrames.frameRadius x)) *
        Real.exp (-(T.rt / 2 ^ 6 * m)))
      _ hσle' hσle fc.isLocalDensity ?_ hcent ?_ ?_
    · intro F hF Y V k c X hV k1 k3 hX
      exact fc.decay 2 F hF Y V k c X hV k3 hX
    · intro k m _ _
      rw [ite_self]
      have e1 := hGb6 m
      have hz0 : 0 < CNs 2 * z := by positivity
      calc CNs 2 * (x ^ 2)⁻¹ * Real.exp (-(S.chainParams.δ₂ / 4 * ColdStepAtMirrorFrames.frameRadius x)) *
            Real.exp (-(T.rt / 2 ^ 6 * m))
          ≤ CNs 2 * z * 1 * (G / (T.stepParameters y).weight m) := by
            rw [zq]
            refine mul_le_mul (mul_le_mul_of_nonneg_left hω hz0.le) e1 (Real.exp_pos _).le (by positivity)
        _ = (CNs 2 * G * z) / (T.stepParameters y).weight m := by ring
        _ ≤ _ := by
            refine div_le_div_of_nonneg_right ?_ (hw0 m).le
            exact mul_le_mul_of_nonneg_right hC₀CN z0.le
    · intro m
      have hdw : BlockAverages.torusDecayFactor T.side S.decayRate (m : ℝ) = (T.stepParameters y).weight m := rfl
      show CNs 2 * (x ^ 2)⁻¹ / BlockAverages.torusDecayFactor T.side S.decayRate (m : ℝ) ≤ _
      rw [hdw, zq]
      refine div_le_div_of_nonneg_right ?_ (hw0 m).le
      exact mul_le_mul_of_nonneg_right hC₀CN' z0.le
  have he₀ : 0 ≤ Real.exp (-(T.gasRate * x / 2)) := (Real.exp_pos _).le
  have hgas₀ := isNormBoundedFamily_of_isSmallDensity hDr.σ_pos he₀ hsmall
  have hzC : z ≤ C₀ * z := by nlinarith
  have FG : FamilyNorms.IsNormBoundedFamily (T.stepParameters y) (C₀ * z) (C₀ * z) R.blockDensity :=
    (hs (T.stepParameters y)).1 _ _ _ _ _ (ev2.trans hzC) (ev2.trans hzC) hgas₀
  have hcurv : TorusLumps.IsCurvatureFamily (T.stepParameters y) (2 * Real.exp (-(T.gasRate * x / 2)))
      R.blockDensity := by
    refine ⟨hgas₀.admissible.smooth, hgas₀.admissible.gauge, hgas₀.admissible.translation, ?_, ?_⟩
    · intro n _ hn y' W hW k c X k1 k3 hX
      have := hgas₀.decay n hn y' W hW k c X k1 k3 hX
      simpa using this
    · intro n n' _ _ hn hn' y' y'' W W' m h1 h2 hW hW' hA k b X hk hb hX
      exact hgas₀.comparison n n' hn hn' y' y'' W W' m h1 h2 hW hW' hA k b X hk hb hX
  obtain ⟨sh1, sh2, sh3⟩ := hSh T hDr y hyT t
  have hform := hFm T hDr t
  have hnumc := (hNuAll t).2 x (b5.trans hxy₀)
  obtain ⟨vm, nm, bm⟩ := (hTop (T.stepParameters y) hfit).2.1 t _ _ hMean.flat_form
  obtain ⟨qe, hqe, hqe2⟩ := fc.flat_limit
  obtain ⟨ve, ne, be⟩ := (hTop (T.stepParameters y) hfit).2.1 t gapTop (CNs 2 * (x ^ 2)⁻¹)
    ⟨qe, hqe, fun X μ ν B h1 h2 h3 => by
      obtain ⟨v', a1, a2⟩ := hqe2 X μ ν B h1 h2 h3
      exact ⟨v', a1, a2 2⟩⟩
  obtain ⟨vg, ng, bg⟩ := hSm (T.stepParameters y) _ _ hfit (by positivity) hcurv
  have hrow₂ : S.IsRegularExpansion t (ColdStepAtMirrorFrames.localFamilyOfDensity f₂) :=
    hCR (T.stepParameters y) t x D f₂ hfit rfl hcold
  have hreg₀ := qCl t x hxS (ColdStepAtMirrorFrames.localFamilyOfDensity f₂) hrow₂
  have ha0 : 0 ≤ T.coupling := by linarith [hDr.a_ge]
  have hlowT : ∀ (n : ℕ), T.n₀ ≤ n →
      ColdStepAtMirrorFrames.IsCubicTorusAbove (T.stepParameters y).side t (T.stepParameters y).n₀
        (TorusFields.torusFrame T.side t n) := by
    intro n hn
    refine ⟨rfl, rfl, n, fun _ => rfl, hn.trans ?_⟩
    exact Nat.le_mul_of_pos_right n (by show 0 < T.side; omega)
  set cP : TorusLumps.LocalDensity := S.minimizerDensity t x with hcP
  set mP : TorusLumps.LocalDensity := ColdStepAtMirrorFrames.densityOfTopFamily T.side t
    (BlockMeans.segmentAveragedMean T.coupling c₀.ρA (T.threshold / 64) x (ColdStepAtMirrorFrames.frameRadius x) T.cutoff
      (S.localReference t) (ColdStepAtMirrorFrames.localFamilyOfDensity h)) with hmP
  set eP : TorusLumps.LocalDensity := ColdStepAtMirrorFrames.densityOfTopFamily T.side t gapTop with heP
  set gP : TorusLumps.LocalDensity := R.blockDensity with hgP
  have hdisp : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusFields.TorusField n, TorusFields.IsCold T.threshold V →
      Real.log (TorusLumps.kernelImage (T.stepParameters y) x D n V) =
        (Real.log (D (n * T.side) (TorusFields.trivialField _)) +
          (∑ _c ∈ BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame T.side t n))
              (TorusFields.torusFrame T.side t n).top, ColdStepAtMirrorFrames.haarGap (T.coupling * x)) +
          (∑ _b : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame T.side t n))),
            Real.log (ColdStepAtMirrorFrames.haarRadialDensity 0)) +
          Real.log (ColdStepAtMirrorFrames.gaussianMass (T.threshold / 64) S.chainParams.lam x T.cutoff
            (TorusFields.torusFrame T.side t n))) -
        x * TorusFields.actionAtLevel T.coupling T.side (t + 1) Finset.univ V + ∑ y', (cP + mP + eP + gP) n y' V := by
    intro n _ hn V hV
    have hnpos : 4096 ≤ n := hDr.n₀_ge.trans hn
    have hTopF : ColdStepAtMirrorFrames.IsCubicTopTorus T.side t T.n₀ (TorusFields.torusFrame T.side t n) :=
      ⟨rfl, rfl, n, fun _ => rfl, hn⟩
    have hV98 : ColdStepAtMirrorFrames.IsSmallCurvature (9 / 8 * T.threshold)
        (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top V) :=
      isSmallCurvature_readAtLevel (isCold_mono hσle hV)
    have hV54 := isSmallCurvature_mono h59 hV98
    obtain ⟨p1, -, p3⟩ := hhot n hn V hV
    have a2 := (hcoldI n hn V (isCold_mono hσle hV)).1
    have hside2 : ∀ i, 2 ≤ (TorusFields.torusFrame T.side t n).extent i := fun _ => by show 2 ≤ n; omega
    have hside0 : ∀ i, 0 < (TorusFields.torusFrame T.side t n).extent i := fun _ => by show 0 < n; omega
    have hodd : Odd (TorusFields.torusFrame T.side t n).blockSide := hDr.L_odd
    have hframeM := ((hreg₀.regular (TorusFields.torusFrame T.side t n) hTopF _ hV98).1)
    have hcoldAb : ∀ η : ColdStepAtMirrorFrames.StepVariable
          (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame T.side t n)),
        η ∈ ColdStepAtMirrorFrames.openBallProduct (TorusFields.torusFrame T.side t n) (T.threshold / 64) →
        ColdStepAtMirrorFrames.IsSmallCurvature T.threshold
          (ColdStepAtMirrorFrames.fieldAboveFrame false T.coupling c₀.ρA (ColdStepAtMirrorFrames.frameRadius x)
            (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top V) η) := by
      intro η hη
      have one := (qFB t x hxS).one_torus (TorusFields.torusFrame T.side t n) _ 1 hTopF hV54 zero_le_one le_rfl
      have c1 := one.small.small_curvature_nearby η (fun b => (hη b).le)
      have e1 := (hEnds (TorusFields.torusFrame T.side t n) false T.coupling c₀.ρA 0 x 0
        (ColdStepAtMirrorFrames.frameRadius x)
        (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top V)).2.2.1 η
      have e2 : Interpolation.segmentEnd false = 1 := by simp [Interpolation.segmentEnd]
      rw [e2] at e1
      rw [← e1]
      have h34 : 3 / 4 * T.threshold ≤ T.threshold := by linarith
      exact isSmallCurvature_mono h34 c1
    have a3 := hTot (T.stepParameters y) t x D f₂ (S.referenceDensity t + h) (TorusFields.torusFrame T.side t n) c₀.ρA
      (T.threshold / 64) (ColdStepAtMirrorFrames.frameRadius x) T.cutoff _ hfit hcold hcold' (hlowT n hn) hodd hside0
      hframeM hcoldAb
    have a4 := fc.log_eq (TorusFields.torusFrame T.side t n) hTopF _ hV54
    obtain ⟨r1, r2, ⟨M₁, r3⟩, ⟨M₂, r4⟩⟩ := qLR t x (S.localReference t)
      (ColdStepAtMirrorFrames.localFamilyOfDensity h) ε hxS hε hFamθ hrowh (TorusFields.torusFrame T.side t n) hTopF _ hV98
    have hm₁ : ¬ ∀ i, 4 * n + 5 < (TorusFields.torusFrame T.side t n).extent i := fun hh => by
      have h0 : 4 * n + 5 < n := hh 0
      omega
    have a5 := hLog (TorusFields.torusFrame T.side t n) T.coupling c₀.ρA (T.threshold / 64) x M₂
      (ColdStepAtMirrorFrames.frameRadius x) n T.cutoff (S.localReference t)
      (ColdStepAtMirrorFrames.localFamilyOfDensity h) _ hodd hside2 hm₁ r1 r4
    have a6 := hDisp (TorusFields.torusFrame T.side t n) T.coupling c₀.ρA (T.threshold / 64) S.chainParams.lam x M₁
      (ColdStepAtMirrorFrames.frameRadius x) 0 n T.cutoff (S.localReference t) _ ha0 hodd hside2 hm₁ r1 (r3 n hm₁)
    have a7 := hNoX (TorusFields.torusFrame T.side t n) T.coupling c₀.ρA x 0 _ ha0 hodd hside2 r2
    have hφ : ColdStepAtMirrorFrames.localFamilyOfDensity (S.referenceDensity t + h) =
        S.localReference t + ColdStepAtMirrorFrames.localFamilyOfDensity h := rfl
    have hNE : NeZero (n * T.side) := ⟨by have : 0 < n * T.side := Nat.mul_pos (by omega) (by omega); omega⟩
    have hDpos : 0 < D (n * T.side) (TorusFields.trivialField _) :=
      hcold.positive (n * T.side) (hn.trans (Nat.le_mul_of_pos_right n (by show 0 < T.side; omega))) _
        (trivialField_isCold hDr.σ_pos _)
    set I₁ : ℝ := ColdStepAtMirrorFrames.stepIntegral T.coupling c₀.ρA (T.threshold / 64) x
      (ColdStepAtMirrorFrames.frameRadius x) T.cutoff
      (ColdStepAtMirrorFrames.localFamilyOfDensity (S.referenceDensity t + h))
      (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame T.side t n))
      (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top V) with hI₁
    have a3' : StepSettings.coldStepIntegral R n V = I₁ := a3
    have a23 : StepSettings.coldImageIntegral R V = D (n * T.side) (TorusFields.trivialField _) * I₁ := by
      have a2' := a2
      rw [a3'] at a2'
      exact a2'
    have hI₁pos : 0 < I₁ := by
      have : 0 < D (n * T.side) (TorusFields.trivialField _) * I₁ := a23 ▸ p1
      exact (mul_pos_iff_of_pos_left hDpos).mp this
    have l1 : Real.log (StepSettings.coldImageIntegral R V) =
        Real.log (D (n * T.side) (TorusFields.trivialField _)) + Real.log I₁ := by
      rw [a23, Real.log_mul hDpos.ne' hI₁pos.ne']
    have s_e : ∑ Y ∈ ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame T.side t n),
        gapTop (TorusFields.torusFrame T.side t n) Y
          (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top V) =
        ∑ y', eP n y' V := sum_finiteCells_torusFrame _
    have s_m : ∑ Y ∈ ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame T.side t n),
        ∫ θ in (0 : ℝ)..1, Estimates.conditionalExpansionMean true T.coupling c₀.ρA (T.threshold / 64) x
          (ColdStepAtMirrorFrames.frameRadius x) T.cutoff
          (S.localReference t + θ • ColdStepAtMirrorFrames.localFamilyOfDensity h)
          (ColdStepAtMirrorFrames.localFamilyOfDensity h) (TorusFields.torusFrame T.side t n) Y
          (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top V) =
        ∑ y', mP n y' V := sum_finiteCells_torusFrame _
    have s_c : ∑ Y ∈ ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame T.side t n),
        (ColdStepAtMirrorFrames.interactionDensity true T.coupling c₀.ρA (T.threshold / 64) S.chainParams.lam x 0 T.cutoff
            (S.localReference t) Y
            (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top V) +
          ColdStepAtMirrorFrames.expansionDensity true T.coupling c₀.ρA (T.threshold / 64) x 0 T.cutoff (S.localReference t) Y
            (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top V)) =
        ∑ y', cP n y' V := sum_finiteCells_torusFrame _
    have hlA : BlockAverages.minimalAction T.coupling
        (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame T.side t n))
        (TorusFields.torusFrame T.side t n).top
        (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top V) =
        TorusFields.actionAtLevel T.coupling T.side (t + 1) Finset.univ V := by
      show _ = BlockAverages.minimalAction T.coupling
        (TorusFields.cellsOfSites (TorusFields.torusFrame T.side t n) Finset.univ) (t + 1)
        (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (t + 1) V)
      rw [TopLevelSites.cellsOfSites_univ (fun _ => rfl)]
      rfl
    rw [Finset.sum_add_distrib, hlA] at a6
    have a6' := a6
    rw [a7, add_zero, s_c] at a6'
    rw [s_m] at a5
    have a4t : Real.log I₁ = Real.log (Interpolation.interpolatedStepIntegral 0 T.coupling c₀.ρA (T.threshold / 64) x
        (ColdStepAtMirrorFrames.frameRadius x) T.cutoff
        (ColdStepAtMirrorFrames.localFamilyOfDensity (S.referenceDensity t + h))
        (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top V)) +
        ∑ Y ∈ ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame T.side t n),
          gapTop (TorusFields.torusFrame T.side t n) Y
            (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top V) := a4
    rw [s_e] at a4t
    have e5 : Real.log (Interpolation.interpolatedStepIntegral 0 T.coupling c₀.ρA (T.threshold / 64) x
        (ColdStepAtMirrorFrames.frameRadius x) T.cutoff
        (ColdStepAtMirrorFrames.localFamilyOfDensity (S.referenceDensity t + h))
        (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top V)) =
        Real.log (Interpolation.interpolatedStepIntegral 0 T.coupling c₀.ρA (T.threshold / 64) x
          (ColdStepAtMirrorFrames.frameRadius x) T.cutoff (S.localReference t)
          (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top V)) +
        ∑ y', mP n y' V := by
      rw [hφ]
      linarith
    have hsum : ∑ y', (cP + mP + eP + gP) n y' V =
        ∑ y', cP n y' V + ∑ y', mP n y' V + ∑ y', eP n y' V + ∑ y', gP n y' V := by
      simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [hsum]
    have p3' : Real.log (TorusLumps.kernelImage (T.stepParameters y) x D n V) =
        Real.log (StepSettings.coldImageIntegral R V) + ∑ Y, gP n Y V := p3
    rw [p3', l1, a4t, e5, a6']
    ring
  refine ⟨cP, mP, eP, gP, ?_⟩
  have hE₃ : T.E ≤ T.E₃ := by
    show T.E ≤ T.E / T.η₃
    rw [le_div_iff₀ hη]
    have := hDr.η₃_le
    nlinarith
  refine
    { admissible := hfit, E_le_E₃ := hE₃, one_le_x := hx1, ε_pos := hε, C₀_nonneg := by linarith,
      Na_nonneg := hNa0, small_constants := ev1, abs_d₀_le := (hNuAll t).1.2.trans (le_max_left _ _),
      log_density_eq := ?_, reference_norm := (hRef0 (t + 1)).family,
      reference_curvatureForm := (hRef0 (t + 1)).vanishing_curvatureForm, excess_norm := ?_,
      mean_norm := FM, frameChange_norm := FE, gas_norm := FG, share_curvatureFamily := sh1,
      share_invariant := sh2, share_sum := sh3, share_curvatureForm := hform,
      value_c := ?_, value_m := ?_, value_e := ?_, value_g := ?_ }
  · intro n _ hn V hV
    have d1 := hdisp n hn V hV
    have hfl : TorusFields.IsCold T.threshold (TorusFields.trivialField n) := trivialField_isCold hDr.σ_pos n
    have d2 := hdisp n hn (TorusFields.trivialField n) hfl
    have hA0 : TorusFields.actionAtLevel T.coupling T.side (t + 1) Finset.univ (TorusFields.trivialField n) = 0 := by
      rw [← sh3 n hn (TorusFields.trivialField n) hfl]
      exact Finset.sum_eq_zero fun z _ => by simp [TorusLumps.centered]
    have hh : ∑ y', TorusLumps.centered (cP + mP + eP + gP) n y' V =
        ∑ y', (cP + mP + eP + gP) n y' V - ∑ y', (cP + mP + eP + gP) n y' (TorusFields.trivialField n) := by
      simp only [TorusLumps.centered, Finset.sum_sub_distrib]
    rw [hh]
    rw [hA0] at d2
    show Real.log (TorusLumps.kernelImage (T.stepParameters y) x D n V) -
        Real.log (TorusLumps.kernelImage (T.stepParameters y) x D n (TorusFields.trivialField n)) +
      x * TorusFields.actionAtLevel T.coupling T.side (t + 1) Finset.univ V = _
    linarith
  · have e : cP - S.referenceDensity (t + 1) - S.oneLoopCoeff t • ShareFamilies.levelShareFamily T.coupling T.side (t + 1) =
        ColdStepAtMirrorFrames.densityOfTopFamily T.side t (StepDensities.densityExcess S t x) :=
      minimizerDensity_sub_eq S t x
    rw [e]
    exact FX
  · obtain ⟨v₁, n₁, b₁⟩ := hnumc
    refine ⟨v₁, n₁, ?_⟩
    have e : v₁ - (S.oneLoopCoeff t + S.secondCoeff t / x) = v₁ - S.oneLoopCoeff t - S.secondCoeff t / x := by ring
    rw [e]
    refine b₁.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos hx0 _).le)
    exact (le_max_left _ _).trans hC₀M
  · refine ⟨vm, nm, bm.trans ?_⟩
    have := mul_le_mul_of_nonneg_right hC₀CE' (by positivity : 0 ≤ ε * v)
    show T.CE * ε * v ≤ C₀ * ε * v
    linarith
  · refine ⟨ve, ne, be.trans ?_⟩
    rw [zq]
    exact mul_le_mul_of_nonneg_right hC₀CN' z0.le
  · refine ⟨vg, ng, bg.trans ?_⟩
    have e1 : 2 * Real.exp (-(T.gasRate * x / 2)) *
        TorusLumps.potentialWeightSum (T.stepParameters y).rt (T.stepParameters y).n₁ ≤ z * SG :=
      mul_le_mul_of_nonneg_right ev2 hG0
    have e2 : z * SG ≤ C₀ * z := by
      have := mul_le_mul_of_nonneg_right hC₀SG z0.le
      linarith
    exact e1.trans e2
end YangMills.Construction.StepPieces
end
