import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionHasOneCoupling
import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfTheImage
import YangMills.Construction.ClusterExpansionOfAStep.ExpansionReturnsAtDrawnParameters
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.LabelDataOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.PriceOfTheImage
import YangMills.Construction.ClusterExpansionOfAStep.RegularityOfTheImage
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfAStepFormAnExpansion
import YangMills.Construction.ClusterExpansionOfAStep.TheImageIsAnArray
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepReturn
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.StepSettings YangMills.Construction.RenormalizationStepParameters YangMills.Construction.TorusLumps YangMills.Construction.ClusterExpansionOfAStep YangMills.Construction.CouplingUniqueness YangMills.Construction.ImageColdExpansion YangMills.Construction.ImageDensities YangMills.Construction.StepFloors
theorem expansionReturnsAtAdmissibleParameters_of_parts (hS : CoarseStatesFormHullExpansion)
    (hC : ImageHasColdExpansion) (hOne : ColdExpansionCouplingUnique) (hLab : CoarseLabelsStandard)
    (hImg : KernelImageIsDensity) (hD : ImageHasHullExpansion) (hReg : ImageHasHullExpansionRegularity)
    (hP : ImageHasHullExpansionPrice) (hFl : EventuallyFloorConditions) :
    ExpansionHoldsAtAdmissibleParameters := by
  obtain ⟨rt₀, hrt₀, hC⟩ := hC
  obtain ⟨rt₁, hrt₁, hP⟩ := hP
  obtain ⟨rt₂, hrt₂, hD⟩ := hD
  refine ⟨fun _ => 0, fun c => min (min (rt₀ c) (rt₁ c)) (rt₂ c), fun _ _ => 1, fun _ _ _ => 0, fun _ _ _ => 0,
    fun c => lt_min (lt_min (hrt₀ c) (hrt₁ c)) (hrt₂ c), fun _ _ => one_pos, ?_⟩
  intro T hT _ hrt hσ1 _ _ hCold
  obtain ⟨yC, hyC⟩ := hC T hT hCold ((hrt.trans (min_le_left _ _)).trans (min_le_left _ _))
  obtain ⟨yD, hyD⟩ := hD T hT hCold (hrt.trans (min_le_right _ _))
  obtain ⟨yR, hyR⟩ := hReg T hT
  obtain ⟨yP, hyP⟩ := hP T hT ((hrt.trans (min_le_left _ _)).trans (min_le_right _ _))
  have hCpos : (0 : ℝ) < 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 := by positivity
  obtain ⟨yF, hyF⟩ := hFl T hT _ 1 hCpos one_pos
  refine ⟨max (max (max yC yD) (max yR yP)) (max yF T.floorMin), fun y hy t x D hx hrow => ?_⟩
  have h1 : yC ≤ y := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hy
  have h2 : yD ≤ y := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hy
  have h3 : yR ≤ y := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hy
  have h4 : yP ≤ y := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hy
  have h5 : yF ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have h6 : T.floorMin ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  have hfit : (T.stepParameters y).Admissible := hT.fits y h6
  have hxpos : 0 < x := lt_of_lt_of_le (lt_of_lt_of_le one_pos hfit.y₁_ge) hx
  have hF := hyF x (h5.trans hx)
  have hrow' := hrow
  obtain ⟨hA, f, hc, Λ, Dq, Φ, φ, hh⟩ := hrow
  let R₀ : StepSetup := ⟨T.stepParameters y, t, x, x, D, f, Λ, Dq, Φ, φ, T.ρA, T.cutoff⟩
  have hstep₀ : R₀.OnParameters T y := ⟨rfl, rfl, rfl, hx, ⟨⟨hc, hh⟩, by
    show x ≤ 1.01 * x
    nlinarith, by
    show clusterRange x ≤ clusterRange x + 1
    omega⟩⟩
  obtain ⟨hcold, hmove⟩ := hyC y h1 R₀ hstep₀ hA
  let R : StepSetup := ⟨T.stepParameters y, t, x, R₀.shiftedCoupling T.lam, D, f, Λ, Dq, Φ, φ, T.ρA, T.cutoff⟩
  have hnext : R.shiftedCoupling T.lam = R₀.shiftedCoupling T.lam := rfl
  have hnew : R.renormalizedDensity T.lam = R₀.renormalizedDensity T.lam := rfl
  have hB : |R₀.shiftedCoupling T.lam - x| ≤ 2 * T.B := hmove
  obtain ⟨_, hStable⟩ := hF.stable_nearby
  obtain ⟨hx1, _, hr1, hr2⟩ := hStable _ hB
  have hr : (2 : ℝ) ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 ≤ clusterRange x := hF.range_ge
  have hr' : 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 ≤ clusterRange x := by exact_mod_cast hr
  have hforms : R.IsWellPosed := by
    refine ⟨⟨hc, hh⟩, hfit, hT.cut, hr1, hr2, ?_, ?_, ?_, hxpos, hA⟩
    · show 2 ^ 16 ≤ clusterRange (R₀.shiftedCoupling T.lam)
      omega
    · show 2 ^ 40 * T.side ≤ clusterRange x
      omega
    · show 4 * T.n₀ + 2 ^ 16 ≤ clusterRange x
      omega
  have hL2 : 2 ≤ R.params.side := by
    have := hfit.L_ge
    show 2 ≤ (T.stepParameters y).side
    omega
  have hlab := hLab R hL2
  have hframes : R.ColdChainFits := ⟨T.δ₁, T.lam, T.σA, T.cg, T.N, hT.chain, hT.σ_le, hσ1⟩
  have hst := hS R hforms hframes hlab
  have hstep : R.OnParameters T y := ⟨rfl, rfl, rfl, hx, ⟨⟨hc, hh⟩, hx1, hr1⟩⟩
  have hdi := hyD y h2 R hstep hforms rfl hmove hlab
  have hre := hyR y h3 R rfl rfl rfl hx ⟨hc, hh⟩ hA rfl hmove hlab
  have hpr := hyP y h4 R hstep hforms rfl hmove hlab
  refine ⟨R₀.shiftedCoupling T.lam, ⟨⟨?_, R₀.renormalizedDensity T.lam, hcold, coarseLabelSpace R hlab, coarseWeightExpansion R,
    coarseFactorExpansion R, R.stateDensity T.lam, hullExpansion_of_parts hst hdi hre hpr⟩, hmove⟩, fun x'' f'' h'' => ?_⟩
  · intro n _ hn
    obtain ⟨_, hm, hnn, hg, hi⟩ := hImg (T.stepParameters y) hfit t x D hxpos (by
      show 4 * T.n₀ + 2 ^ 16 ≤ clusterRange x
      omega) hrow' n hn
    exact ⟨hm, hnn, hg, hi⟩
  · exact hOne T hT y h6 t _ _ _ _ _ h'' hcold
end YangMills.Construction.StepReturn
end
