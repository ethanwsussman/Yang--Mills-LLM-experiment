import YangMills.Construction.ClusterExpansionOfAStep.PriceOfTheHotLumps
import YangMills.Construction.ResponseInTheExpansion.GroundOfAMirror
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps StepSettings StepGas TorusMirror BlockAverages
theorem mirrorGroundAgrees_holds : MirrorGroundAgrees := by
  classical
  intro R n _ _ V q y hF hot hy hne
  have hfit := hF.admissible
  have hr1 := hF.range_le
  have hr2 := hF.nextRange_ge
  obtain ⟨W₀, Yt, ωt, bad, b, hst, -⟩ := hot.exists_state
  have hst' : coarseStateOf R (hotCoreSites R V) W₀ Yt ωt bad b = q := hst
  subst hst'
  set Z := storedBlocks R.params.side R.range bad Yt (hotCoreSites R V) with hZ
  have hq1' : (coarseStateOf R (hotCoreSites R V) W₀ Yt ωt bad b).1 = thickening (R.nextRange / 2) Z := rfl
  have hfar : ∀ z ∈ Z, R.nextRange / 2 < supDist y z := by
    intro z hz
    by_contra hc
    apply hy
    rw [hq1']
    exact (mem_thickening _ _ _).mpr ⟨z, hz, not_lt.mp hc⟩
  have hCZ : hotCoreSites R V ⊆ Z := Finset.subset_union_left
  set m := R.nextRange / 4 - 2 with hm
  have hm3 : 2 ≤ m := by omega
  have hbox : ∀ v, OffsetInBox m v → supDist y (y + siteOfInt v) ≤ m := fun v hv =>
    supDist_add_siteOfInt_le y v m fun i => by
      have := hv i
      rw [abs_le] at this
      omega
  have hoff : ∀ v, OffsetInBox m v → y + siteOfInt v ∉ Z := by
    intro v hv hz
    have h1 := hfar _ hz
    have h2 := hbox v hv
    omega
  have hcold : IsCold R.params.threshold (mirrorField m y V) := by
    refine isCold_mirrorField (by omega) y V hfit.σ_pos fun a μ ν hlt hcorn => ?_
    by_contra hcon
    have h1 := mem_torusHotSites_of_mem_plaquetteVertices hfit hot.isBlockSide.1 hlt (not_lt.mp hcon)
      (base_mem_plaquetteVertices (y + siteOfInt a) μ ν)
    have h2 : y + siteOfInt a ∈ hotCoreSites R V := (mem_thickening _ _ _).mpr ⟨_, h1, by rw [supDist_self]; omega⟩
    have hbox0 := hcorn 0 (by simp [plaquetteOffsets])
    rw [add_zero] at hbox0
    exact hoff a hbox0 (hCZ h2)
  obtain ⟨z₀, hz₀⟩ : Z.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    rw [hq1', hc] at hne
    obtain ⟨u, hu⟩ := hne
    obtain ⟨z, hz, _⟩ := (mem_thickening _ _ _).mp hu
    simp at hz
  have hside : 2 * m + 2 < n := by
    have h1 := hfar z₀ hz₀
    have h2 : supDist y z₀ ≤ n / 2 := (supDist_le_iff y z₀ _).mpr fun _ => ZMod.natAbs_valMinAbs_le _
    omega
  refine ⟨hcold, hside, by omega, fun b' hb' => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · simp only [bondFrom, zero_add]
    exact (mirrorField_siteOfInt hm3 y V b' hb').symm
  · constructor
    · intro h
      exact absurd (hCZ h) (hoff v hv)
    · intro h
      exact absurd h (Finset.notMem_empty _)
  · have h2 : (coarseStateOf R (hotCoreSites R V) W₀ Yt ωt bad b).markAt (y + siteOfInt v) = none := by
      unfold CoarseState.markAt
      split_ifs with hmem
      · have e : (coarseStateOf R (hotCoreSites R V) W₀ Yt ωt bad b).2 ⟨y + siteOfInt v, hmem⟩ = Sum.inl () := by
          show (if (y + siteOfInt v) ∈ storedBlocks R.params.side R.range bad Yt (hotCoreSites R V) then _ else _) = _
          rw [if_neg (hoff v hv)]
        rw [e]
      · rfl
    show (coarseStateOf R (hotCoreSites R V) W₀ Yt ωt bad b).markAt _ = (emptyCoarseState R).markAt _
    rw [h2]
    unfold CoarseState.markAt
    rw [dif_neg]
    exact Finset.notMem_empty _
end YangMills.Construction.ResponseInTheExpansion
end
