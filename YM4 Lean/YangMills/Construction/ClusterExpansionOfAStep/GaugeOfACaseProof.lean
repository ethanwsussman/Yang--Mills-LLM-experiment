import YangMills.Construction.ClusterExpansionOfAStep.CountFloorCanBeMet
import YangMills.Construction.ClusterExpansionOfAStep.GaugeOfACase
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTheGaugeProof
import YangMills.Construction.ClusterExpansionOfAStep.ZonesOfAFamily
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusLumps StepSettings StepCosts LumpContours BlockZones SpinFamilies FamilyZones BlockPlaces TopLevelSites
namespace GaugeInvariance
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : StepGas.GasGround R n} {Γ : Finset G.GasSpin}
theorem readAtLevel_zero_gaugeTransform (g : TorusFields.TorusSite (n * R.params.side) → BlockAverages.UnitQuaternion)
    (W : TorusFields.TorusField (n * R.params.side)) :
    TorusFields.readAtLevel (stepBlockFrame R.params.side n) 0 (TorusFields.gaugeTransform g W) =
      BlockAverages.gaugeTransform (fun x => g (toTorusSite (n * R.params.side) x))
        (TorusFields.readAtLevel (stepBlockFrame R.params.side n) 0 W) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.readAtLevel_zero_gaugeTransform <;> assumption
theorem stepHotLumps_gaugeTransform (g : TorusFields.TorusSite (n * R.params.side) → BlockAverages.UnitQuaternion)
    (W : TorusFields.TorusField (n * R.params.side)) :
    stepHotLumps R.params (TorusFields.gaugeTransform g W) = stepHotLumps R.params W := by
  unfold stepHotLumps
  rw [_root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.readAtLevel_zero_gaugeTransform]
  simp only [hotLumps, TorusContours.plaquetteDefect_gaugeTransform]
theorem isHullState_gaugeTransform_iff (hadm : R.params.Admissible)
    (g : TorusFields.TorusSite (n * R.params.side) → BlockAverages.UnitQuaternion)
    (W : TorusFields.TorusField (n * R.params.side)) (r : ℕ)
    (Y : Finset (TorusFields.TorusSite (n * R.params.side))) :
    IsHullState R.params r (TorusFields.gaugeTransform g W) Y ↔ IsHullState R.params r W Y := by
  have h : torusHotLumps R.params (TorusFields.gaugeTransform g W) = torusHotLumps R.params W := by
    ext l
    simp only [mem_torusHotLumps_iff R.params hadm (Dvd.intro_left n rfl), TorusFields.curvature_gaugeTransform]
  unfold IsHullState torusHotSites
  rw [h]
theorem baseLaw_gaugeTransform (g : TorusFields.TorusSite (n * R.params.side) → BlockAverages.UnitQuaternion)
    (W : TorusFields.TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    baseLaw (R := R) (TorusFields.gaugeTransform g W) b = baseLaw (R := R) W b := by
  classical
  have h : baseChoices R.params (TorusFields.readAtLevel (stepBlockFrame R.params.side n) 0 (TorusFields.gaugeTransform g W)) =
      baseChoices R.params (TorusFields.readAtLevel (stepBlockFrame R.params.side n) 0 W) := by
    show (Finset.univ.filter fun b => IsBaseChoice R.params.baseDepth (stepHotLumps R.params (TorusFields.gaugeTransform g W)) b) =
      Finset.univ.filter fun b => IsBaseChoice R.params.baseDepth (stepHotLumps R.params W) b
    rw [_root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.stepHotLumps_gaugeTransform]
  unfold baseLaw
  rw [h]
theorem contourMean_gaugeTransform_of_eq_one {F : BlockAverages.BlockFrame} [∀ j i, NeZero (F.period j i)] (d : ℕ)
    (h : Finset (Finset (F.Site F.depth))) (γ : F.Site F.depth → BlockAverages.UnitQuaternion)
    (b : F.Cell → F.Site F.depth) (W : F.GaugeField F.depth) (c : F.Cell × Fin 4) (h1 : γ (b c.1) = 1)
    (h2 : γ (b (c.1 + BlockAverages.unitStep F.top c.2)) = 1) :
    contourMean d h b (BlockAverages.gaugeTransform γ W) c = contourMean d h b W c := by
  rw [TorusContours.contourMean_gaugeTransform, h1, h2]
  simp
theorem bondKernel_gaugeTransform {g : TorusFields.TorusSite (n * R.params.side) → BlockAverages.UnitQuaternion}
    (W : TorusFields.TorusField (n * R.params.side)) (V : (stepBlockFrame R.params.side n).GaugeField 1)
    {b : BaseChoice R.params.side n} (hb : ∀ e, g (toTorusSite (n * R.params.side) (b e)) = 1)
    (c : (stepBlockFrame R.params.side n).Cell × Fin 4) :
    bondKernel R.params R.coupling (TorusFields.readAtLevel (stepBlockFrame R.params.side n) 0 (TorusFields.gaugeTransform g W)) V b c =
      bondKernel R.params R.coupling (TorusFields.readAtLevel (stepBlockFrame R.params.side n) 0 W) V b c := by
  have hm : contourMean R.params.baseDepth (stepHotLumps R.params (TorusFields.gaugeTransform g W)) b
        (TorusFields.readAtLevel (stepBlockFrame R.params.side n) 0 (TorusFields.gaugeTransform g W)) c =
      contourMean R.params.baseDepth (stepHotLumps R.params W) b
        (TorusFields.readAtLevel (stepBlockFrame R.params.side n) 0 W) c := by
    rw [_root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.stepHotLumps_gaugeTransform, _root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.readAtLevel_zero_gaugeTransform]
    exact _root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.contourMean_gaugeTransform_of_eq_one (F := stepBlockFrame R.params.side n) _ _ _ _ _ _ (hb _) (hb _)
  show Real.exp (R.params.coupling * R.coupling * (contourMean R.params.baseDepth (stepHotLumps R.params (TorusFields.gaugeTransform g W)) b
      (TorusFields.readAtLevel (stepBlockFrame R.params.side n) 0 (TorusFields.gaugeTransform g W)) c *
        ((V c.1 c.2)⁻¹ : BlockAverages.UnitQuaternion)).re) /
      partitionFn (R.params.coupling * R.coupling * ‖contourMean R.params.baseDepth (stepHotLumps R.params (TorusFields.gaugeTransform g W)) b
        (TorusFields.readAtLevel (stepBlockFrame R.params.side n) 0 (TorusFields.gaugeTransform g W)) c‖) =
    Real.exp (R.params.coupling * R.coupling * (contourMean R.params.baseDepth (stepHotLumps R.params W) b
      (TorusFields.readAtLevel (stepBlockFrame R.params.side n) 0 W) c * ((V c.1 c.2)⁻¹ : BlockAverages.UnitQuaternion)).re) /
      partitionFn (R.params.coupling * R.coupling * ‖contourMean R.params.baseDepth (stepHotLumps R.params W) b
        (TorusFields.readAtLevel (stepBlockFrame R.params.side n) 0 W) c‖)
  rw [hm]
theorem bondMark_gaugeTransform (hL : Odd R.params.side) (hn : 2 ≤ n)
    {g : TorusFields.TorusSite (n * R.params.side) → BlockAverages.UnitQuaternion} (V : TorusFields.TorusField n)
    (W : TorusFields.TorusField (n * R.params.side)) {β : TorusFields.TorusBond (n * R.params.side)}
    (h1 : ∀ u, parentBlock R.params.side u = parentBlock R.params.side β.1 → g u = 1)
    (h2 : ∀ u, parentBlock R.params.side u = parentBlock R.params.side (β.1 + TorusFields.unitStep (n * R.params.side) β.2) → g u = 1) :
    bondMark R V (TorusFields.gaugeTransform g W) β = bondMark R V W β := by
  have key : ∀ x, (∀ u, parentBlock R.params.side u = parentBlock R.params.side x → g u = 1) →
      BlockTrees.blockGauge R.params.side (TorusFields.gaugeTransform g W) x = BlockTrees.blockGauge R.params.side W x := by
    intro x hx
    apply BlockTrees.blockGauge_congr hL hn
    intro z i hz ht
    unfold TorusFields.gaugeTransform
    rw [hx z hz, hx _ ((parentBlock_add_unitStep_of_isAxialTreeBond ht).trans hz)]
    simp
  have hW : TorusFields.gaugeTransform g W β.1 β.2 = W β.1 β.2 := by
    unfold TorusFields.gaugeTransform
    rw [h1 _ rfl, h2 _ rfl]
    simp
  unfold bondMark
  rw [BlockTrees.chartCoord_eq, BlockTrees.chartCoord_eq, key _ h1, key _ h2, hW]
theorem torusSiteInFrame_blockSite_centre (y : TorusFields.TorusSite n) :
    torusSiteInFrame (stepBlockFrame R.params.side n) 0 (blockSite (L := R.params.side) y fun _ => ⟨(R.params.side - 1) / 2, by
      have := NeZero.pos R.params.side
      omega⟩) =
      BlockAverages.cellCentre (F := stepBlockFrame R.params.side n) 0 (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) := by
  have hp0 : ∀ k, (stepBlockFrame R.params.side n).period 0 k = n * R.params.side := fun k => BlockTrees.stepBlockFrame_period_zero k
  have hp1 : ∀ k, (stepBlockFrame R.params.side n).period 1 k = n := fun k => BlockTrees.stepBlockFrame_period_one k
  apply toTorusSite_injective hp0
  rw [toTorusSite_torusSiteInFrame hp0]
  set e := torusSiteInFrame (stepBlockFrame R.params.side n) 1 y with he
  have hc : (BlockAverages.cellCentre (F := stepBlockFrame R.params.side n) 0 e : (stepBlockFrame R.params.side n).Site 0) =
      BlockAverages.siteOfCoords 0 fun i => (R.params.side : ℤ) * BlockAverages.siteCoords e i := by
    unfold BlockAverages.cellCentre
    congr 1
    funext i
    simp [stepBlockFrame, BlockAverages.BlockFrame.top]
  rw [hc, TorusContours.toTorusSite_siteOfCoords hp0]
  funext i
  simp only [blockSite, TorusFields.siteOfInt]
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2
  have h1 : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n e = y := toTorusSite_torusSiteInFrame hp1 y
  have h2 : ((BlockAverages.siteCoords e i : ℤ) : ZMod n) = (((y i).cast : ℤ) : ZMod n) := by
    rw [ZMod.intCast_zmod_cast]
    exact congrFun h1 i
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h2
  refine ⟨-k, ?_⟩
  have hm : (((⟨(R.params.side - 1) / 2, by
      have := NeZero.pos R.params.side
      omega⟩ : Fin R.params.side) : ℕ) : ℤ) = ((R.params.side : ℤ) - 1) / 2 := by
    have h3 : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
    simp only
    omega
  rw [hm]
  push_cast
  linear_combination (-(R.params.side : ℤ)) * hk
theorem cellOffset_cellCentre (hL : Odd R.params.side) (e : (stepBlockFrame R.params.side n).Cell) :
    BlockAverages.cellOffset (F := stepBlockFrame R.params.side n)
      (BlockAverages.cellCentre (F := stepBlockFrame R.params.side n) 0 e) = 0 := by
  have h0 : (0 : Fin 4 → ℤ) ∈ BlockAverages.centredCube
      ((stepBlockFrame R.params.side n).blockSide ^ ((stepBlockFrame R.params.side n).top - 0)) := by
    refine Fintype.mem_piFinset.2 fun i => ?_
    have hp : 1 ≤ (stepBlockFrame R.params.side n).blockSide ^ ((stepBlockFrame R.params.side n).top - 0) :=
      Nat.one_le_pow _ _ hL.pos
    generalize (stepBlockFrame R.params.side n).blockSide ^ ((stepBlockFrame R.params.side n).top - 0) = M at hp ⊢
    simp only [Pi.zero_apply, Finset.mem_Icc]
    omega
  have h1 := BlockTrees.enclosingCell_cellCentre_add (F := stepBlockFrame R.params.side n) hL (j := 0) e 0 h0
  have e0 : (BlockAverages.siteOfCoords 0 (0 : Fin 4 → ℤ) : (stepBlockFrame R.params.side n).Site 0) = 0 := by
    funext i
    simp [BlockAverages.siteOfCoords]
  rw [e0, add_zero] at h1
  funext i
  unfold BlockAverages.cellOffset
  show (((BlockAverages.cellCentre (F := stepBlockFrame R.params.side n) 0 e) -
    BlockAverages.cellCentre (F := stepBlockFrame R.params.side n) 0
      (BlockAverages.enclosingCell (BlockAverages.cellCentre (F := stepBlockFrame R.params.side n) 0 e))) i).valMinAbs = 0
  rw [h1, sub_self]
  simp
end GaugeInvariance
open GaugeInvariance in
theorem restIntegrandGaugeInvariant_of_couplingFloorExists (hfloor : CouplingFloorExists) :
    RestIntegrandGaugeInvariant := by
  classical
  intro T hT
  obtain ⟨y₁, hfloor⟩ := hfloor 1 (64 * T.side) T.rt one_pos
  refine ⟨max y₁ T.floorMin, fun y hy R hR hx' n _ G hG F hF Γ hΓ c ν g hg W => ?_⟩
  have b₁ : y₁ ≤ y := le_trans (by simp) hy
  have b₂ : T.floorMin ≤ y := le_trans (by simp) hy
  have hadm : R.params.Admissible := by rw [hR.params_eq]; exact hT.fits y b₂
  have eL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hfar : 64 * R.params.side ≤ R.range := by
    have := (hfloor R.coupling (b₁.trans hR.le_coupling)).1
    rw [eL]
    exact this
  have hL1 : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hn₀ : R.params.n₀ ≤ n := by
    rcases hG with h | h
    · exact h.n₀_le
    · exact (Nat.le_mul_of_pos_left _ hL1).trans h.isBlockSide.2
  have hn2 : 2 ≤ n := by
    have := hadm.n₀_ge
    omega
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
  obtain ⟨Z, hZ⟩ := exists_isAdmissibleZone G hG
  have hsep := coresDisjoint_familyData hΓ (by omega) c
  have g1 : ∀ u, parentBlock R.params.side u ∈ Z → g u = 1 := fun u h =>
    hg.1 u fun ho => ((mem_freeBlocks_iff hZ).mp ho).1 h
  have g2 : ∀ (i : Γ) u, parentBlock R.params.side u ∈ i.1.1.core → g u = 1 := fun i u h =>
    hg.1 u fun ho => ((mem_freeBlocks_iff hZ).mp ho).2 i h
  have hsame : ∀ W₁ W₂ : TorusFields.TorusField (n * R.params.side),
      (∀ x i, parentBlock R.params.side x ∈ Z →
        parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) ∈ Z → W₁ x i = W₂ x i) →
      coarseStateOf R G.cut W₁ (G.familySites Γ) (G.state.fillLabels _ ν) (G.familyBadBonds Γ) (G.familySetting c).bases = G.state →
      coarseStateOf R G.cut W₂ (G.familySites Γ) (G.state.fillLabels _ ν) (G.familyBadBonds Γ) (G.familySetting c).bases = G.state := by
    intro W₁ W₂ h hs
    have hrec := fun y => (congrArg (fun q => CoarseState.markAt q y) hs).symm.trans
      (markAt_coarseStateOf G.cut W₁ (G.familySites Γ) (G.state.fillLabels _ ν) (G.familyBadBonds Γ) (G.familySetting c).bases y)
    have hZZ : storedBlocks R.params.side R.range (G.familyBadBonds Γ) (G.familySites Γ) G.cut = Z := by
      ext y
      rw [← hZ.recorded_iff, hrec]
      by_cases h' : y ∈ storedBlocks R.params.side R.range (G.familyBadBonds Γ) (G.familySites Γ) G.cut
      · simp [h']
      · simp [h']
    refine Eq.trans (coarseStateOf_congr rfl fun y hy => ?_) hs
    refine blockConfig_ext rfl rfl rfl rfl ?_
    funext q
    have hbx : parentBlock R.params.side (blockSite (L := R.params.side) y q.1) = y := parentBlock_blockSite _ _
    show (if parentBlock R.params.side (blockSite (L := R.params.side) y q.1 + TorusFields.unitStep (n * R.params.side) q.2) ∈ _ then
        Sum.inr (W₂ (blockSite y q.1) q.2) else Sum.inl ()) =
      if parentBlock R.params.side (blockSite (L := R.params.side) y q.1 + TorusFields.unitStep (n * R.params.side) q.2) ∈ _ then
        Sum.inr (W₁ (blockSite y q.1) q.2) else Sum.inl ()
    by_cases hcond : parentBlock R.params.side (blockSite (L := R.params.side) y q.1 + TorusFields.unitStep (n * R.params.side) q.2) ∈
        storedBlocks R.params.side R.range (G.familyBadBonds Γ) (G.familySites Γ) G.cut
    · rw [if_pos hcond, if_pos hcond]
      congr 1
      exact (h _ _ (by rw [hbx, ← hZZ]; exact hy) (hZZ ▸ hcond)).symm
    · rw [if_neg hcond, if_neg hcond]
  have hWg : ∀ x i, parentBlock R.params.side x ∈ Z →
      parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) ∈ Z →
      TorusFields.gaugeTransform g W x i = W x i := by
    intro x i h1 h2
    unfold TorusFields.gaugeTransform
    rw [g1 _ h1, g1 _ h2]
    simp
  have hp0 : ∀ k, (stepBlockFrame R.params.side n).period 0 k = n * R.params.side := fun k => BlockTrees.stepBlockFrame_period_zero k
  have hcen : ∀ e : (stepBlockFrame R.params.side n).Cell,
      g (toTorusSite (n * R.params.side) (BlockAverages.cellCentre (F := stepBlockFrame R.params.side n) 0 e)) = 1 := by
    intro e
    refine hg.2 _ ?_
    rw [torusSiteInFrame_toTorusSite hp0]
    exact cellOffset_cellCentre hadm.L_odd e
  have hb : ∀ e, g (toTorusSite (n * R.params.side) ((G.familySetting c).bases e)) = 1 := by
    intro e
    rw [bases_familySetting hsep]
    unfold StepGas.GasGround.basesOfOffsets
    by_cases hcore : ∃ i : Γ, cellBlock R.params.side n e ∈ i.1.1.core
    · rw [dif_pos hcore]
      unfold StepGas.frameBlockSite
      rw [toTorusSite_torusSiteInFrame hp0]
      exact g2 hcore.choose _ (by rw [parentBlock_blockSite]; exact hcore.choose_spec)
    · rw [dif_neg hcore]
      show g (toTorusSite (n * R.params.side) (match G.state.markAt (cellBlock R.params.side n e) with
        | some s => StepGas.frameBlockSite R.params.side n (cellBlock R.params.side n e) s.basePoint
        | none => BlockAverages.cellCentre (F := stepBlockFrame R.params.side n) 0 e)) = 1
      rcases hso : G.state.markAt (cellBlock R.params.side n e) with _ | s
      · exact hcen e
      · have hinZ : cellBlock R.params.side n e ∈ Z := (hZ.recorded_iff _).mp (by rw [hso]; rfl)
        show g (toTorusSite (n * R.params.side) (StepGas.frameBlockSite R.params.side n (cellBlock R.params.side n e) s.basePoint)) = 1
        unfold StepGas.frameBlockSite
        rw [toTorusSite_torusSiteInFrame hp0]
        exact g1 _ (by rw [parentBlock_blockSite]; exact hinZ)
  have hc : ∀ y : TorusFields.TorusSite n, g (blockSite y fun _ => ⟨(R.params.side - 1) / 2, by
      have := NeZero.pos R.params.side
      omega⟩) = 1 := by
    intro y
    refine hg.2 _ ?_
    rw [torusSiteInFrame_blockSite_centre]
    exact cellOffset_cellCentre hadm.L_odd _
  have hact : R.labels.act (G.familySites Γ) g (G.state.fillLabels _ ν) = G.state.fillLabels _ ν := by
    funext z
    refine R.labels.act_free _ g _ z fun u hu => ?_
    have hd : TorusFields.supDist u z.1 ≤ 4 * R.range := by omega
    rcases Finset.mem_union.mp z.2 with a | a
    · refine g1 u ?_
      rw [hZ.zone_eq]
      refine Finset.mem_union_right _ (parentBlock_mem_coreBlocks_of_near ?_ hd)
      unfold StepGas.GasGround.anchorSites
      exact Finset.mem_union_right _ a
    · obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp a
      exact g2 ⟨i, hi⟩ u (parentBlock_mem_coreBlocks_of_near (Finset.mem_union_right _ hzi) hd)
  have hrm : G.remainingMarks (G.familySetting c).free (G.familyBadBonds Γ) (TorusFields.gaugeTransform g W) =
      G.remainingMarks (G.familySetting c).free (G.familyBadBonds Γ) W := by
    unfold StepGas.GasGround.remainingMarks
    refine Finset.prod_congr rfl fun β hβ => ?_
    obtain ⟨hm, hnf⟩ := Finset.mem_sdiff.mp hβ
    have key : bondMark R G.coarse (TorusFields.gaugeTransform g W) β = bondMark R G.coarse W β := by
      by_cases hst : G.IsRecorded β
      · obtain ⟨h1, h2⟩ := (hZ.bond_iff β).mp hst
        exact _root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.bondMark_gaugeTransform hadm.L_odd hn2 _ W (fun u hu => g1 u (hu ▸ h1)) (fun u hu => g1 u (hu ▸ h2))
      · by_cases hj : ∃ j : Γ, β ∈ j.1.1.coreBonds
        · obtain ⟨j, hj⟩ := hj
          obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hj
          exact _root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.bondMark_gaugeTransform hadm.L_odd hn2 _ W (fun u hu => g2 j u (hu ▸ h1)) (fun u hu => g2 j u (hu ▸ h2))
        · exact absurd ((mem_free_familySetting_iff c hsep).mpr ⟨hm, hst, fun j h => hj ⟨j, h⟩⟩) hnf
    rw [key]
  have hker : (∏ e : (stepBlockFrame R.params.side n).Cell × Fin 4, bondKernel R.params R.coupling
      (TorusFields.readAtLevel (stepBlockFrame R.params.side n) 0 (TorusFields.gaugeTransform g W))
      (TorusFields.readAtLevel (stepBlockFrame R.params.side n) 1 G.coarse) (G.familySetting c).bases e) =
      ∏ e : (stepBlockFrame R.params.side n).Cell × Fin 4, bondKernel R.params R.coupling
        (TorusFields.readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (TorusFields.readAtLevel (stepBlockFrame R.params.side n) 1 G.coarse) (G.familySetting c).bases e :=
    Finset.prod_congr rfl fun e _ => _root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.bondKernel_gaugeTransform W _ hb e
  unfold StepGas.GasGround.restIntegrand
  by_cases ht : IsHullState R.params R.range W (G.familySites Γ) ∧
      coarseStateOf R G.cut W (G.familySites Γ) (G.state.fillLabels _ ν) (G.familyBadBonds Γ) (G.familySetting c).bases = G.state
  · have ht' : IsHullState R.params R.range (TorusFields.gaugeTransform g W) (G.familySites Γ) ∧
        coarseStateOf R G.cut (TorusFields.gaugeTransform g W) (G.familySites Γ) (G.state.fillLabels _ ν) (G.familyBadBonds Γ)
          (G.familySetting c).bases = G.state :=
      ⟨(_root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.isHullState_gaugeTransform_iff hadm g W _ _).mpr ht.1, hsame _ _ (fun x i h1 h2 => (hWg x i h1 h2).symm) ht.2⟩
    rw [if_pos ht', if_pos ht]
    have hDq : R.labelWeight (n * R.params.side) (TorusFields.gaugeTransform g W) (G.familySites Γ) (G.state.fillLabels _ ν) =
        R.labelWeight (n * R.params.side) W (G.familySites Γ) (G.state.fillLabels _ ν) := by
      have := hR.isStep.1.2.gauge _ hside W (G.familySites Γ) (G.state.fillLabels _ ν) g ht.1
      rwa [hact] at this
    rw [hDq, hker, hrm, _root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.baseLaw_gaugeTransform]
    by_cases hpos : 0 < R.labelWeight (n * R.params.side) W (G.familySites Γ) (G.state.fillLabels _ ν)
    · have := hF.gauge_invariant W (G.familySites Γ) (G.state.fillLabels _ ν) (G.familyBadBonds Γ) (G.familySetting c).bases g ht.1 hpos hb hc
      rw [hact] at this
      rw [this]
    · have h0 : R.labelWeight (n * R.params.side) W (G.familySites Γ) (G.state.fillLabels _ ν) = 0 :=
        le_antisymm (not_lt.mp hpos) (hR.isStep.1.2.nonneg _ hside W _ _ ht.1)
      rw [h0]
      simp
  · have ht' : ¬ (IsHullState R.params R.range (TorusFields.gaugeTransform g W) (G.familySites Γ) ∧
        coarseStateOf R G.cut (TorusFields.gaugeTransform g W) (G.familySites Γ) (G.state.fillLabels _ ν) (G.familyBadBonds Γ)
          (G.familySetting c).bases = G.state) :=
      fun h => ht ⟨(_root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.isHullState_gaugeTransform_iff hadm g W _ _).mp h.1, hsame _ _ hWg h.2⟩
    rw [if_neg ht', if_neg ht]
end YangMills.Construction.ClusterExpansionOfAStep
end
