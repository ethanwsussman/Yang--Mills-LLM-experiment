import YangMills.Construction.LimitsOfTwoKinds.WhatTheSettingNamesIsFormed
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import YangMills.Construction.Torus.ComponentsOfASeparatedTupleAreBoundedAndLipschitz
import YangMills.Construction.Torus.IsometriesPermutationsAndSubTuplesKeepTuplesSeparated
import YangMills.Construction.Torus.OneSpaceOneDistanceOneClassOfTestFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitsOfTwoKinds.SettingWellDefined
open ReflectionPositivity.AxisMirror (Ambient)
open ParameterChoice FlowConstants AmbientPoints
private theorem widthSharp_pos_of_chosen {T : DerivedConstants} {N : ExternalConstants}
    {c : ChoiceUpToCoupling} (hc : ChosenUpToCoupling T N c) :
    0 < widthSharp T c := by
  have hCβ := hc.ranges.Cβ_nonneg
  have hCp := hc.ranges.CPrime_pos
  have hγ := hc.ranges.γ_pos
  unfold widthSharp flowError
  positivity
private theorem highCoupling_lt_one {T : DerivedConstants} {N : ExternalConstants}
    {c : ChoiceUpToCoupling} (hc : ChosenUpToCoupling T N c) : c.γH < 1 := by
  have hCβ := hc.ranges.Cβ_nonneg
  have hfl : 2 * (T.Cβ c.toChoiceUpToRadii + 1) ≤ inverseSqAtHigh c :=
    (le_max_left _ _).trans hc.couplings.inverseSqAtHigh_floor
  by_contra hnot
  have hone : 1 ≤ c.γH := not_lt.mp hnot
  have hle : inverseSqAtHigh c ≤ 1 := by
    unfold inverseSqAtHigh
    rw [zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ hone (by norm_num))
  linarith
private theorem boundedReal_and_lipschitz_of_c1
    (hId : Identification.AllCoincide)
    (hEnt : SepTupleEntriesBoundedLipschitz)
    {s : Conventions.StandingParameters} {E : Ambient} {f : Pt s E → ℝ} (hf : IsC1Fn f)
    (hcpt : IsCompact (tsupport f)) :
    BoundedReal f ∧ TestFunctions.IsLipschitzFor (pointDist s E) f := by
  have hmem : (fun _ : Fin 1 => f) ∈ separatedTuples s E 1 :=
    ⟨fun _ => ⟨hf, hcpt⟩, fun a b hab => (hab (Subsingleton.elim a b)).elim⟩
  rw [← (hId s E).sepTuples_eq 1 le_rfl] at hmem
  obtain ⟨⟨C, hC⟩, hlip⟩ := hEnt s E 1 _ hmem 0
  exact ⟨⟨C, fun x => by simpa using hC x⟩, hlip⟩
theorem statement_holds
    (hTor : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (hId : Identification.AllCoincide)
    (hEnt : SepTupleEntriesBoundedLipschitz)
    (hStab : SeparatedTupleStability.holds) :
    Statement := by
  refine ⟨fun T N c ϱ γJ g hL hT hg hle => ?_, fun s E => ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · have hW := widthSharp_pos_of_chosen hL
    have hP : 0 < passageLevel T c g := passageLevel_pos hg hW
    exact
      ⟨⟨Real.rpow_pos_of_pos hP _, windowLowerEnd_lt hg hW, hle, hT.γJ_le_γH,
          highCoupling_lt_one hL, referenceTorusSide_mem_torusSides g,
          referenceTorusSide_mem_torusSides g, le_rfl⟩,
        ⟨hP, fun β hβ => hP.trans_le hβ, fun x D K β hβ => hP.trans_le hβ.1⟩⟩
  · exact fun f hf => boundedReal_and_lipschitz_of_c1 hId hEnt hf.1 hf.2.1
  · exact fun n X hX i =>
      boundedReal_and_lipschitz_of_c1 hId hEnt (hX.1 i).1 (hX.1 i).2
  · intro f hf
    obtain ⟨-, ⟨C, hC⟩, -⟩ :=
      (hTor { toStandingParameters := s, coupling := 1, coupling_pos := one_pos, dir := 0 }).2.1
        ℝ f hf
    exact ⟨C, fun x => by simpa using hC x⟩
  · intro n hn X hX J hJ
    exact ((hStab s E).2.2.1 n hn X hX).2.1 J hJ
end YangMills.Construction.LimitsOfTwoKinds.SettingWellDefined
end
