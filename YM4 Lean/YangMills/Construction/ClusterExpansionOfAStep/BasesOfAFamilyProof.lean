import YangMills.Construction.ClusterExpansionOfAStep.BasesOfAFamily
import YangMills.Construction.ClusterExpansionOfAStep.CountFloorCanBeMet
import YangMills.Construction.ClusterExpansionOfAStep.EvaluationsOfAFamily
import YangMills.Construction.ClusterExpansionOfAStep.ZonesOfAFamily
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
namespace FamilyBases
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n] {G : StepGas.GasGround R n}
  {Γ : Finset G.GasSpin}
theorem nearbyLumps_trivialField_eq_empty
    (c : (TorusLumps.stepBlockFrame R.params.side n).Cell) (hσ : 0 < R.params.threshold) :
    LumpContours.nearbyLumps
      (StepCosts.stepHotLumps R.params (TorusFields.trivialField (n * R.params.side))) c = ∅ := by
  classical
  unfold LumpContours.nearbyLumps StepCosts.stepHotLumps LumpContours.hotLumps
  apply Finset.filter_eq_empty_iff.mpr
  intro l hl
  exfalso
  obtain ⟨p, hp, -⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨-, hhot⟩ := Finset.mem_filter.mp hp
  obtain ⟨p₀, μ, ν⟩ := p
  obtain ⟨p₁, rfl⟩ := BlockTrees.torusSiteInFrame_surjective
    (TorusLumps.stepBlockFrame R.params.side n) 0 BlockTrees.stepBlockFrame_period_zero p₀
  have h1 : R.params.threshold ≤
      TorusFields.curvature (TorusFields.trivialField (n * R.params.side)) p₁ μ ν :=
    le_of_le_of_eq hhot (FamilyRestrictions.plaquetteDefect_readAtLevel _ p₁ μ ν)
  have h2 : TorusFields.curvature (TorusFields.trivialField (n * R.params.side)) p₁ μ ν = 0 := by
    simp [TorusFields.curvature, TorusFields.holonomy_trivialField]
  linarith
end FamilyBases
open FamilyBases in
theorem nonzeroCaseBasesAreGroundOffsets_holds (hf1 : TorusLumps.CouplingFloorExists) :
    NonzeroCaseBasesAreGroundOffsets := by
  classical
  intro T hT
  obtain ⟨y₁, hf1⟩ := hf1 1 (64 * T.side) T.rt one_pos
  refine ⟨max y₁ T.floorMin, fun y hy R hR hx' n _ G hG F Γ hΓ b W ν hne => ?_⟩
  have b₁ : y₁ ≤ y := le_trans (by simp) hy
  have b₂ : T.floorMin ≤ y := le_trans (by simp) hy
  have hfit : R.params.Admissible := by rw [hR.params_eq]; exact hT.fits y b₂
  have eL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hfar : 64 * R.params.side ≤ R.range := by
    have := (hf1 R.coupling (b₁.trans hR.le_coupling)).1
    rw [eL]
    exact this
  have hL1 : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨Z, hZ⟩ := BlockZones.exists_isAdmissibleZone G hG
  have hn2 : 2 ≤ n := by
    have := hfit.n₀_ge
    have hn₀ : R.params.n₀ ≤ n := by
      rcases hG with g | g
      · exact g.n₀_le
      · exact (Nat.le_mul_of_pos_left _ hL1).trans g.isBlockSide.2
    omega
  unfold StepGas.GasGround.caseIntegrand at hne
  by_cases ht : TorusLumps.IsHullState R.params R.range (G.state.fieldWithStoredLinks W)
      (G.familySites Γ) ∧
      StepSettings.coarseStateOf R G.cut (G.state.fieldWithStoredLinks W) (G.familySites Γ)
        (G.state.fillLabels _ ν) (G.familyBadBonds Γ) b = G.state
  · rw [if_pos ht] at hne
    have hx := (mul_ne_zero_iff.mp hne).2
    have hw := (ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hx)).ne'
    unfold StepSettings.stepWeight at hw
    have hbl : StepSettings.baseLaw (R := R) (G.state.fieldWithStoredLinks W) b ≠ 0 :=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).1).2
    have hb := FamilyRestrictions.isBaseChoice_of_baseLaw_ne_zero hbl
    refine ⟨fun i y => StepSettings.baseOffset R b y.1, ?_⟩
    funext e
    have hcell := FamilyZones.enclosingCell_baseChoice hfit hnpos hb e
    have hsite := FamilyZones.eq_frameBlockSite_siteOffset hcell
    have hte : (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1
        (SpinFamilies.cellBlock R.params.side n e) :
          (TorusLumps.stepBlockFrame R.params.side n).Cell) = e :=
      TopLevelSites.torusSiteInFrame_toTorusSite (F := TorusLumps.stepBlockFrame R.params.side n)
        (j := 1) (fun k => BlockTrees.stepBlockFrame_period_one k) e
    have hoff : StepSettings.siteOffset (TorusLumps.toTorusSite
        (F := TorusLumps.stepBlockFrame R.params.side n) (j := 0) (n * R.params.side) (b e)) =
        StepSettings.baseOffset R b (SpinFamilies.cellBlock R.params.side n e) := by
      show _ = StepSettings.siteOffset (TorusLumps.toTorusSite (n * R.params.side)
        (b (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1
          (SpinFamilies.cellBlock R.params.side n e))))
      rw [hte]
    rw [hoff] at hsite
    unfold StepGas.GasGround.basesOfOffsets
    by_cases hc : ∃ i : Γ, SpinFamilies.cellBlock R.params.side n e ∈ i.1.1.core
    · rw [dif_pos hc]
      exact hsite
    · rw [dif_neg hc]
      have hstore := fun y =>
        (congrArg (fun q => StepSettings.CoarseState.markAt q y) ht.2).symm.trans
          (BlockZones.markAt_coarseStateOf G.cut (G.state.fieldWithStoredLinks W)
            (G.familySites Γ) (G.state.fillLabels _ ν) (G.familyBadBonds Γ) b y)
      show b e = (match G.state.markAt (SpinFamilies.cellBlock R.params.side n e) with
        | some s => StepGas.frameBlockSite R.params.side n
            (SpinFamilies.cellBlock R.params.side n e) s.basePoint
        | none => BlockAverages.cellCentre (F := TorusLumps.stepBlockFrame R.params.side n) 0 e)
      rcases hso : G.state.markAt (SpinFamilies.cellBlock R.params.side n e) with _ | s
      · have hnZ : SpinFamilies.cellBlock R.params.side n e ∉ Z := fun h => by
          have := (hZ.recorded_iff _).mpr h
          rw [hso] at this
          simp at this
        have hno : LumpContours.nearbyLumps
            (StepCosts.stepHotLumps R.params (G.state.fieldWithStoredLinks W)) e = ∅ := by
          have hsub := FamilyRestrictions.nearbyLumps_mono hfit.L_odd hn2
            (G.state.fieldWithStoredLinks W) (TorusFields.trivialField _)
            (SpinFamilies.cellBlock R.params.side n e)
            (fun x₁ p₁ μ ν hμν hc' hd hs => by
              exfalso
              have hl : TorusLumps.torusLumpOf R.params x₁ ∈
                  TorusLumps.torusHotLumps R.params (G.state.fieldWithStoredLinks W) :=
                (TorusLumps.mem_torusHotLumps_iff R.params hfit (Dvd.intro_left n rfl) _ _).mpr
                  ⟨p₁, μ, ν, hμν, hs, x₁, hc', rfl⟩
              have hs' : x₁ ∈ TorusLumps.torusHotSites R.params (G.state.fieldWithStoredLinks W) :=
                Finset.mem_biUnion.mpr ⟨_, hl, TorusLumps.mem_torusLumpOf_self x₁⟩
              have hY := ht.1.1 ((TorusFields.mem_thickening _ _ _).mpr
                ⟨x₁, hs', by rw [TorusFields.supDist_self]; omega⟩)
              obtain ⟨v, hv⟩ : ∃ v : TorusFields.TorusSite (n * R.params.side),
                  TorusLumps.parentBlock R.params.side v = SpinFamilies.cellBlock R.params.side n e :=
                ⟨StepSettings.blockSite _ (fun _ => 0), BlockPlaces.parentBlock_blockSite _ _⟩
              have h1 := FamilyRestrictions.supDist_le_four_mul hv hd
              have h2 : TorusFields.supDist v x₁ ≤ 4 * R.range := by
                rw [TorusFields.supDist_comm]
                omega
              rcases Finset.mem_union.mp hY with a | a
              · apply hnZ
                rw [hZ.zone_eq, ← hv]
                refine Finset.mem_union_right _ (BlockZones.parentBlock_mem_coreBlocks_of_near ?_ h2)
                unfold StepGas.GasGround.anchorSites
                exact Finset.mem_union_right _ a
              · obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp a
                apply hc
                refine ⟨⟨i, hi⟩, ?_⟩
                rw [← hv]
                exact BlockZones.parentBlock_mem_coreBlocks_of_near
                  (Finset.mem_union_right _ hzi) h2)
          rw [hte, nearbyLumps_trivialField_eq_empty e hfit.σ_pos] at hsub
          exact Finset.subset_empty.mp hsub
        exact (hb e).1 (Or.inl hno)
      · have h1 := hstore (SpinFamilies.cellBlock R.params.side n e)
        rw [hso] at h1
        by_cases hin : SpinFamilies.cellBlock R.params.side n e ∈
            TorusLumps.storedBlocks R.params.side R.range (G.familyBadBonds Γ) (G.familySites Γ) G.cut
        · rw [if_pos hin] at h1
          have := Option.some.inj h1
          subst this
          exact hsite
        · rw [if_neg hin] at h1
          cases h1
  · rw [if_neg ht] at hne
    exact absurd rfl hne
end YangMills.Construction.ClusterExpansionOfAStep
end
