import YangMills.Construction.ClusterExpansionOfAStep.FitsOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.FrameAgainstTheLeastFieldOfTheCut
import YangMills.Construction.ClusterExpansionOfAStep.NearAFreeBond
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfPointsOfWeight
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsPlainFarFromLumps
import YangMills.Construction.ColdStepAtMirrorFrames.ContourOfAChartField
import YangMills.Construction.HoleBesideASecondHole.EnergyInTheChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages TorusFields TorusLumps StepSettings StepGas StepCosts RenormalizationStepParameters StepFrames
  FreeBondNeighborhood BlockTrees BlockZones LumpContours ColdStepAtMirrorFrames
namespace SettingOfWeight
variable {R : StepSetup} {n : ℕ} [NeZero n]
variable {δ lam σA cg : ℝ} {N : ℕ → ℝ} {G : GasGround R n} {γ : GasFamily R n} {Z S : Finset (TorusSite n)} {s₀ : ℝ}
section Requirements
variable (hS : StepHypotheses R δ lam σA cg N G γ Z S s₀) {η : FreeCoords (G.settingOf γ).free}
include hS
theorem inBalls_of_hasWeightAt (hw : G.HasWeightAt γ η) : (G.settingOf γ).InBalls η :=
  fun b => (hw.coordNorm_lt b).le
theorem bases_mem_baseChoices (hGood : coldPlaquette_of_small_frameDeviation) (hw : G.HasWeightAt γ η)
    (η' : FreeCoords (G.settingOf γ).free) (h' : (G.settingOf γ).InBalls η') :
    (G.settingOf γ).bases ∈ baseChoices R.params
      (readAtLevel (stepBlockFrame R.params.side n) 0 ((G.settingOf γ).field η')) := by
  classical
  have h1 : (G.settingOf γ).bases ∈ baseChoices R.params
      (readAtLevel (stepBlockFrame R.params.side n) 0 ((G.settingOf γ).field η)) := by
    by_contra hn
    apply hw.baseLaw_ne_zero
    unfold baseLaw
    rw [if_neg hn]
  have e : hotLumps R.params.grid R.params.threshold (levelSites (stepBlockFrame R.params.side n) 0)
      (readAtLevel (stepBlockFrame R.params.side n) 0 ((G.settingOf γ).field η')) =
      hotLumps R.params.grid R.params.threshold (levelSites (stepBlockFrame R.params.side n) 0)
        (readAtLevel (stepBlockFrame R.params.side n) 0 ((G.settingOf γ).field η)) :=
    stepHotLumps_field_eq hS hGood hw.bondMark_ne_zero η' η h' (inBalls_of_hasWeightAt hS hw)
  have hb := (Finset.mem_filter.mp h1).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact Eq.mpr (congrArg (fun H => IsBaseChoice (F := stepBlockFrame R.params.side n) R.params.baseDepth H
    (G.settingOf γ).bases) e) hb
theorem nearbyLumps_eq_empty (hGood : coldPlaquette_of_small_frameDeviation) (hw : G.HasWeightAt γ η)
    (η' : FreeCoords (G.settingOf γ).free) (h' : (G.settingOf γ).InBalls η')
    {b : TorusBond (n * R.params.side)} (hb : b ∈ (G.settingOf γ).free) (c₀ : TorusSite n)
    (hd : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1) c₀ ≤ 18) :
    nearbyLumps (stepHotLumps R.params ((G.settingOf γ).field η'))
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) = ∅ := by
  classical
  have hodd := side_odd hS
  have hs : ∀ i, 0 < (stepBlockFrame R.params.side n).extent i := fun _ => by
    have := hS.two_le
    show 0 < n
    omega
  have hfar := hS.side_le_range
  have hL1 := one_le_side hS
  unfold nearbyLumps
  apply Finset.eq_empty_of_forall_notMem
  intro l hlm
  have hodd' : Odd (stepBlockFrame R.params.side n).blockSide := hodd
  obtain ⟨p, hpc, hhot, x, hx, hu⟩ := exists_hot_corner_of_mem_nearbyLumps (F := stepBlockFrame R.params.side n)
    R.params.grid hodd hodd' hs R.params.threshold _ _ _ l hlm
  obtain ⟨h, hh, hcell⟩ := Finset.mem_image.mp hu
  obtain ⟨x₁, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 0 stepBlockFrame_period_zero x
  obtain ⟨p₀, μ, ν⟩ := p
  obtain ⟨p₁, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 0 stepBlockFrame_period_zero p₀
  have hμν : μ < ν := lt_of_mem_cutPlaquettes hpc
  have hhot' : R.params.threshold ≤ curvature ((G.settingOf γ).field η') p₁ μ ν :=
    le_of_le_of_eq hhot (plaquetteDefect_readAtLevel_zero _ p₁ μ ν)
  have hcorner : x₁ ∈ plaquetteVertices p₁ μ ν := mem_plaquetteVertices_of_mem_plaquetteCorners hx
  have hblock : parentBlock R.params.side x₁ = c₀ + siteOfInt h := by
    have h1 := hcell.trans (enclosingCell_torusSiteInFrame x₁)
    exact torusSiteInFrame_injective (stepBlockFrame R.params.side n) 1 stepBlockFrame_period_one
      (h1.symm.trans (torusSiteInFrame_one_add_siteOfCoords c₀ h))
  have hdist : _root_.YangMills.Construction.TorusFields.supDist c₀ (parentBlock R.params.side x₁) ≤ 2 := by
    rw [hblock]
    refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => ?_
    have := Fintype.mem_piFinset.1 hh i
    rw [Finset.mem_Icc] at this
    norm_num at this
    omega
  have d1 := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side b.1) c₀ (parentBlock R.params.side x₁)
  have d2 := _root_.YangMills.Construction.FreeBondNeighborhood.supDist_le_of_parentBlock b.1 x₁
  have d3 := _root_.YangMills.Construction.FreeBondNeighborhood.supDist_le_two_of_mem_plaquetteVertices hcorner
  have d4 := _root_.YangMills.Construction.TorusFields.supDist_triangle p₁ x₁ b.1
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm x₁ b.1] at d4
  have d5 : R.params.side * (_root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1) (parentBlock R.params.side x₁) + 2) ≤
      R.params.side * 22 :=
    Nat.mul_le_mul_left _ (by omega)
  have hc := curvature_lt_of_near_free hS hGood hw.bondMark_ne_zero η' h' hb p₁ μ ν hμν (by omega)
  have hσ := hS.admissible.σ_pos
  linarith
theorem norm_frameCoord_le (hFrame : FrameNearMinimizer) {b : TorusBond (n * R.params.side)}
    (hc : b ∈ chartBonds R.params.side n) (hC : parentBlock R.params.side b.1 ∉ G.cut) :
    ‖((frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse b : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
      N 0 * s₀ := by
  classical
  have hf := ((hFrame R.params δ lam R.anchorRadius σA cg N hS.admissible hS.chainConstants
    hS.two_threshold_le).2 R.depth R.range R.nextRange n G.coarse S G.cut s₀ hS.rangesAdmissible
    hS.situation b hc hC).1
  have hN : 0 ≤ N 0 * s₀ := by
    obtain ⟨_, _, _, _, _, _, _, h3, _⟩ := hS.chainConstants
    exact mul_nonneg (h3 0).le hS.s₀_pos.le
  have hρ' : 0 ≤ min R.anchorRadius (N 0 * s₀) := le_min (anchorRadius_le_one_and_pos hS).2.le hN
  have key : ∀ {F : BlockFrame} {a : ℝ} {Q : Finset F.Cell} {V : F.GaugeField F.top} {ρ' : ℝ}
      {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}, IsMinimizingChart a Q V ρ' w → 0 ≤ ρ' →
      ∀ c : F.Site F.depth × Fin 4, ‖((w c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ρ' := by
    intro F a Q V ρ' w hl h0 c
    by_cases hcb : c ∈ chordBonds Q
    · exact hl.2.1 c hcb
    · rw [hl.1 c hcb]
      simpa using h0
  by_cases h : 4 * (R.range / 2 ^ 11) + 5 < n
  · obtain ⟨w, hl, e⟩ := hf.1 h
    refine le_trans (le_of_eq (congrArg (fun v : imaginaryQuaternions => ‖(v : ℍ[ℝ])‖) e)) ?_
    exact (key hl hρ' _).trans (min_le_right _ _)
  · obtain ⟨w, hl, e⟩ := hf.2 h
    refine le_trans (le_of_eq (congrArg (fun v : imaginaryQuaternions => ‖(v : ℍ[ℝ])‖) e)) ?_
    exact (key hl hρ' (torusSiteInFrame (torusFrame R.params.side R.depth n)
      (torusFrame R.params.side R.depth n).depth b.1, b.2)).trans (min_le_right _ _)
omit hS in
theorem card_centredCube {L : ℕ} (hL : Odd L) : (centredCube L).card = L ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
omit hS in
theorem le_norm_contourAverage {F : BlockFrame} (hL : Odd F.blockSide) (W : F.GaugeField F.depth)
    (V : F.GaugeField F.top) (c : F.Site F.top × Fin 4) {ε : ℝ}
    (h : ∀ (u : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), u ∈ centredCube F.blockSide →
      ‖((pathHolonomy W (refineSite c.1) (bondContour F.blockSide u π c.2) * (V c.1 c.2)⁻¹ :
        UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε) :
    1 - ε ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c‖ := by
  classical
  set v : ℍ[ℝ] := ((V c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) with hv
  have hvn : ‖v‖ = 1 := norm_unitQuaternion _
  have hLpos : (0 : ℝ) < F.blockSide := by
    have : 0 < F.blockSide := hL.pos
    exact_mod_cast this
  set hol : (Fin 4 → ℤ) → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun u π =>
    ((pathHolonomy W (refineSite c.1) (bondContour F.blockSide u π c.2) : UnitQuaternion) : ℍ[ℝ]) with hhol
  have hne : ∀ u ∈ centredCube F.blockSide, ∀ π, ‖hol u π - v‖ ≤ ε := by
    intro u hu π
    have e : hol u π - v =
        (((pathHolonomy W (refineSite c.1) (bondContour F.blockSide u π c.2) * (V c.1 c.2)⁻¹ :
          UnitQuaternion) : ℍ[ℝ]) - 1) * v := by
      have e0 : ((pathHolonomy W (refineSite c.1) (bondContour F.blockSide u π c.2) * (V c.1 c.2)⁻¹ :
          UnitQuaternion) : ℍ[ℝ]) * v = hol u π := by
        rw [hv]
        rw [← Submonoid.coe_mul, inv_mul_cancel_right]
      rw [sub_mul, e0, one_mul]
    rw [e, norm_mul, hvn, mul_one]
    exact h u π hu
  have hcount : ∑ _u ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), v =
      ((24 * (F.blockSide : ℝ) ^ 4 : ℝ)) • v := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_perm, card_centredCube hL,
      ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    simp [Nat.factorial]
    ring
  have hD : (24 * (F.blockSide : ℝ) ^ 4) ≠ 0 := by positivity
  have e : _root_.YangMills.Construction.BlockAverages.contourAverage W c - v =
      (1 / (24 * (F.blockSide : ℝ) ^ 4)) •
        ∑ u ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (hol u π - v) := by
    simp only [Finset.sum_sub_distrib]
    rw [hcount, smul_sub, smul_smul, one_div, inv_mul_cancel₀ hD, one_smul]
    unfold _root_.YangMills.Construction.BlockAverages.contourAverage
    rw [one_div]
  have hb : ‖_root_.YangMills.Construction.BlockAverages.contourAverage W c - v‖ ≤ ε := by
    rw [e, norm_smul]
    have h1 : ‖∑ u ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (hol u π - v)‖ ≤
        ∑ _u ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), ε := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u hu => ?_)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => hne u hu π)
    have h2 : ∑ _u ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), ε =
        (24 * (F.blockSide : ℝ) ^ 4) * ε := by
      rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_perm, card_centredCube hL,
        nsmul_eq_mul, nsmul_eq_mul]
      simp [Nat.factorial]
      ring
    rw [h2] at h1
    have h3 : ‖(1 / (24 * (F.blockSide : ℝ) ^ 4))‖ = 1 / (24 * (F.blockSide : ℝ) ^ 4) := by
      rw [Real.norm_of_nonneg (by positivity)]
    rw [h3]
    calc 1 / (24 * (F.blockSide : ℝ) ^ 4) *
          ‖∑ u ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (hol u π - v)‖
        ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) * ((24 * (F.blockSide : ℝ) ^ 4) * ε) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ε := by field_simp
  have h4 := norm_sub_norm_le v (v - _root_.YangMills.Construction.BlockAverages.contourAverage W c)
  rw [sub_sub_cancel, hvn, norm_sub_rev] at h4
  linarith
omit hS in
theorem axialGauge_cellCentre {F : BlockFrame} (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (W : F.GaugeField F.depth) (z : F.Cell) :
    axialGauge 1 W (cellCentre F.depth z) = 1 := by apply _root_.YangMills.Construction.SettingFits.axialGauge_cellCentre <;> assumption
theorem half_le_meanNorm (hGood : coldPlaquette_of_small_frameDeviation) (hFrame : FrameNearMinimizer)
    (hContour : ChartedFieldContourBound) (hGC : gaugeCovarianceStatement)
    (hPlain : KernelPlainAwayFromLumps) (hw : G.HasWeightAt γ η)
    (η' : FreeCoords (G.settingOf γ).free) (h' : (G.settingOf γ).InBalls η') {b : TorusBond (n * R.params.side)}
    (hb : b ∈ (G.settingOf γ).free) (c : TorusBond n) (hd : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1) c.1 ≤ 16) :
    1 / 2 ≤ meanNorm R.params ((G.settingOf γ).field η') (G.settingOf γ).bases c := by
  classical
  have hodd := side_odd hS
  have hodd' : Odd (stepBlockFrame R.params.side n).blockSide := hodd
  have hs2 : ∀ i, 2 ≤ (stepBlockFrame R.params.side n).extent i := fun _ => hS.two_le
  have hs0 : ∀ i, 0 < (stepBlockFrame R.params.side n).extent i := fun i => by have := hs2 i; omega
  have hfar := hS.side_le_range
  have hL1 := one_le_side hS
  set Wr : (stepBlockFrame R.params.side n).GaugeField (stepBlockFrame R.params.side n).depth :=
    readAtLevel (stepBlockFrame R.params.side n) 0 ((G.settingOf γ).field η') with hWr
  set Vr : (stepBlockFrame R.params.side n).GaugeField (stepBlockFrame R.params.side n).top :=
    readAtLevel (stepBlockFrame R.params.side n) 1 G.coarse with hVr
  set y : (stepBlockFrame R.params.side n).Cell := torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1 with hy
  set i := c.2 with hi
  have hy' : y + BlockAverages.unitStep 1 i =
      torusSiteInFrame (stepBlockFrame R.params.side n) 1 (c.1 + TorusFields.unitStep n i) := by
    rw [torusSiteInFrame_one_add, torusSiteInFrame_one_unitStep]
    rfl
  have h1 := nearbyLumps_eq_empty hS hGood hw η' h' hb c.1 (by omega)
  have h2 : nearbyLumps (stepHotLumps R.params ((G.settingOf γ).field η')) (y + BlockAverages.unitStep 1 i) = ∅ := by
    have h3 := nearbyLumps_eq_empty hS hGood hw η' h' hb (c.1 + TorusFields.unitStep n i) (by
      have a := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side b.1) c.1 (c.1 + TorusFields.unitStep n i)
      have b' := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le c.1 i
      omega)
    exact Eq.mpr (congrArg (fun z => nearbyLumps (F := stepBlockFrame R.params.side n)
      (stepHotLumps R.params ((G.settingOf γ).field η')) z = ∅) hy') h3
  have hmean := ((hPlain R.params hS.admissible n Wr y i h1 h2).2 0 Vr (G.settingOf γ).bases
    (bases_mem_baseChoices hS hGood hw η' h')).1
  show (1 : ℝ) / 2 ≤ ‖contourMean R.params.baseDepth (stepHotLumps R.params ((G.settingOf γ).field η'))
    (G.settingOf γ).bases Wr (y, i)‖
  have hmean' : contourMean R.params.baseDepth (stepHotLumps R.params ((G.settingOf γ).field η'))
      (G.settingOf γ).bases Wr (y, i) = _root_.YangMills.Construction.BlockAverages.contourAverage Wr (y, i) := hmean
  rw [hmean']
  set τ := axialGauge 1 Wr with hτ
  have hcen : ∀ z : (stepBlockFrame R.params.side n).Cell, τ (refineSite z) = 1 := fun z => by
    rw [GaugeFixing.refineSite_eq_cellCentre]
    exact axialGauge_cellCentre hodd' hs2 Wr z
  have hg := (hGC (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth (Nat.lt_succ_self _)
    hodd'.pos).2.1 τ Wr (y, i)
  have hg' : _root_.YangMills.Construction.BlockAverages.contourAverage (gaugeTransform τ Wr) (y, i) = _root_.YangMills.Construction.BlockAverages.contourAverage Wr (y, i) := by
    rw [hg]
    simp [hcen]
  set S₂ : Finset (stepBlockFrame R.params.side n).Cell := {y, y + BlockAverages.unitStep 1 i} with hS₂
  set w := GaugeFixing.lexicographicChart S₂ Vr Wr with hw'
  have hbond : (y, i) ∈ innerBonds S₂ (stepBlockFrame R.params.side n).top := by
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨mem_sitesOfCells_top.2 (Finset.mem_insert_self _ _),
      mem_sitesOfCells_top.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
  have hcc := GaugeFixing.contourAverage_congr hs0 hodd' S₂ (gaugeTransform τ Wr) (chartedField w Vr)
    (fun b' hb' => (GaugeFixing.chartedField_lexicographicChart_eq hs2 hodd' S₂ Vr Wr b' hb').symm) (y, i) hbond
  set ε := N 0 * s₀ + R.ballRadius with hε
  have hN : 0 ≤ N 0 * s₀ := by
    obtain ⟨_, _, _, _, _, _, _, h3, _⟩ := hS.chainConstants
    exact mul_nonneg (h3 0).le hS.s₀_pos.le
  have hε0 : 0 ≤ ε := add_nonneg hN (ballRadius_pos hS).le
  have hbound : ∀ b' ∈ chordBonds (finiteCells (stepBlockFrame R.params.side n)), ‖w b'.1 b'.2‖ ≤ ε := by
    rintro ⟨x', i'⟩ _
    obtain ⟨x₁, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 0 stepBlockFrame_period_zero x'
    show ‖GaugeFixing.lexicographicChart S₂ Vr Wr (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x₁) i'‖ ≤ ε
    unfold GaugeFixing.lexicographicChart
    split_ifs with hm
    · have hm1 := Finset.mem_filter.mp hm
      have hbd := hm1.1
      have hnt := hm1.2
      have hsite : torusSiteInFrame (stepBlockFrame R.params.side n) 0 x₁ ∈
          sitesOfCells S₂ (stepBlockFrame R.params.side n).depth := by
        simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hbd
        exact hbd.1
      obtain ⟨y₀, hy₀, h₀, hh₀, hx₀⟩ := mem_sitesOfCells.mp hsite
      have hcell : enclosingCell (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x₁ :
          (stepBlockFrame R.params.side n).Site (stepBlockFrame R.params.side n).depth) = y₀ := by
        rw [hx₀]
        exact enclosingCell_cellCentre_add hodd' y₀ h₀ hh₀
      have hblk : torusSiteInFrame (stepBlockFrame R.params.side n) 1 (parentBlock R.params.side x₁) = y₀ :=
        (enclosingCell_torusSiteInFrame x₁).symm.trans hcell
      have hin := torusSiteInFrame_injective (m := n) (stepBlockFrame R.params.side n) 1 stepBlockFrame_period_one
      have hdb : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1) (parentBlock R.params.side x₁) ≤ 17 := by
        have e1 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le c.1 i
        have e2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side b.1) c.1 (c.1 + TorusFields.unitStep n i)
        simp only [hS₂, Finset.mem_insert, Finset.mem_singleton] at hy₀
        rcases hy₀ with rfl | rfl
        · rw [hin hblk]
          omega
        · rw [hin (hblk.trans hy')]
          omega
      have d2 := _root_.YangMills.Construction.FreeBondNeighborhood.supDist_le_of_parentBlock b.1 x₁
      have d5 : R.params.side * (_root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1) (parentBlock R.params.side x₁) + 2) ≤
          R.params.side * 19 :=
        Nat.mul_le_mul_left _ (by omega)
      have hc : (x₁, i') ∈ chartBonds R.params.side n := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnt⟩
      have hC : parentBlock R.params.side x₁ ∉ G.cut := fun hC => by
        have := far_of_parentBlock_mem_cut hS.markedZone hb hC
        omega
      have g1 := deviation_le_of_near_free hS hw.bondMark_ne_zero η' h' hb hc
        (show _root_.YangMills.Construction.TorusFields.supDist b.1 x₁ + R.params.side + 1 < 4 * R.range by omega)
      have g2 := norm_frameCoord_le hS hFrame hc hC
      have g3 := norm_sub_norm_le
        ((chartCoord R.params G.coarse ((G.settingOf γ).field η') (x₁, i') : imaginaryQuaternions) : ℍ[ℝ])
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse (x₁, i') : imaginaryQuaternions) : ℍ[ℝ])
      show ‖((chartCoord R.params G.coarse ((G.settingOf γ).field η') (x₁, i') : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ε
      rw [hε]
      linarith
    · simpa using hε0
  have hcon := hContour (stepBlockFrame R.params.side n) w Vr ε hodd' hs2 hε0 hbound (y, i)
  have hfin := le_norm_contourAverage hodd' (chartedField w Vr) Vr (y, i)
    (ε := 5 * ((stepBlockFrame R.params.side n).blockSide : ℝ) * ε) (fun u π hu => hcon u π hu)
  have hsz := hS.size_bound
  have hLe : ((stepBlockFrame R.params.side n).blockSide : ℝ) = R.params.side := rfl
  rw [hLe] at hfin
  rw [← hg', hcc]
  nlinarith
theorem isAdmissible_settingOf (hGood : coldPlaquette_of_small_frameDeviation) (hFrame : FrameNearMinimizer)
    (hContour : ChartedFieldContourBound) (hGC : gaugeCovarianceStatement)
    (hPlain : KernelPlainAwayFromLumps) (hw : G.HasWeightAt γ η)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) :
    (G.settingOf γ).IsAdmissible := by
  classical
  have hη := inBalls_of_hasWeightAt hS hw
  have h0 := inBalls_zero (G := G) (γ := γ) hS
  have hL := side_odd hS
  have hn := hS.two_le
  have hbase : (G.settingOf γ).fine = (G.settingOf γ).field 0 := fine_eq_field_zero hL hn
  have hh : ∀ η', (G.settingOf γ).InBalls η' →
      torusHotLumps R.params ((G.settingOf γ).field η') = torusHotLumps R.params ((G.settingOf γ).field η) :=
    fun η' h' => torusHotLumps_field_eq hS hGood hw.bondMark_ne_zero η' η h' hη
  have hsites : ∀ η', (G.settingOf γ).InBalls η' →
      torusHotSites R.params ((G.settingOf γ).field η') = torusHotSites R.params ((G.settingOf γ).field η) :=
    fun η' h' => by
      unfold torusHotSites
      rw [hh η' h']
  have hfar := hS.side_le_range
  have hL1 := one_le_side hS
  have hnb : ∀ {b b' : TorusBond (n * R.params.side)}, b ∈ (G.settingOf γ).free → _root_.YangMills.Construction.TorusFields.supDist b.1 b'.1 ≤ 3 * R.range →
      b' ∉ (G.settingOf γ).bad := fun hb hd hbad => by
    have := far_of_mem_bad hS.markedZone hb hbad
    omega
  have hco : ∀ {b : TorusBond (n * R.params.side)}, b ∉ (G.settingOf γ).free →
      chartCoord R.params G.coarse ((G.settingOf γ).field η) b =
        chartCoord R.params G.coarse (G.settingOf γ).fine b :=
    fun hb => chartCoord_field_of_not_mem_free (s := G.settingOf γ) free_subset_chartBonds hL hn η hb
  refine ⟨free_subset_chartBonds, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro η' h'
    unfold IsHullState
    rw [hsites η' h', hh η' h']
    exact hw.isHull
  · intro η' h'
    rw [hh η' h', hbase]
    exact (hh 0 h0).symm
  · intro η' h' X hX
    have e : R.clusterFactor (n * R.params.side) ((G.settingOf γ).field η') (G.settingOf γ).support
        (G.settingOf γ).labelling X =
        R.clusterFactor (n * R.params.side) ((G.settingOf γ).field η) (G.settingOf γ).support
          (G.settingOf γ).labelling X := by
      refine hS.hasExpansions.2.reads_class (n * R.params.side) hside _ _ _ _ _ _ X
        (subset_of_mem_chainComponents hX) (subset_of_mem_chainComponents hX) ?_ (fun _ _ _ _ => rfl)
      intro c hc _
      have hnf : c ∉ (G.settingOf γ).free := fun hf => by
        have := far_of_mem_support hS.markedZone hf (subset_of_mem_chainComponents hX hc)
        rw [_root_.YangMills.Construction.TorusFields.supDist_self] at this
        omega
      rw [field_of_not_mem_free hnf, field_of_not_mem_free hnf]
    rw [e]
    exact hw.factor_ne_zero X hX
  · intro b hb z hz
    rcases Finset.mem_union.mp hz with h | h
    · exact far_of_mem_support hS.markedZone hb h
    · rw [hbase, hsites 0 h0] at h
      refine far_of_mem_support hS.markedZone hb (hw.isHull.1 ?_)
      exact (mem_thickening _ _ _).mpr ⟨z, h, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; exact Nat.zero_le _⟩
  · exact fun η' h' b hb x μ ν hμ hd => curvature_lt_of_near_free hS hGood hw.bondMark_ne_zero η' h' hb x μ ν hμ hd
  · rcases hS.admissibleGround with hc | hc
    · exact Or.inl ⟨hc.region_eq, hc.coarse_cold⟩
    · refine Or.inr ⟨hc.isBlockSide, hc.region_eq, fun b hb z hz => far_of_parentBlock_mem_cut hS.markedZone hb ?_⟩
      rw [hc.cut_eq]
      exact hz
  · intro b hb b' hc hnf hd
    have h := deviation_lt_of_not_mem_free hS hw.bondMark_ne_zero η hc hnf (hnb hb hd)
    rw [hco hnf] at h
    exact h.le
  · have hb := (Finset.mem_filter.mp (bases_mem_baseChoices hS hGood hw 0 h0)).2
    exact Eq.mpr (congrArg (fun W => IsBaseChoice (F := stepBlockFrame R.params.side n) R.params.baseDepth
      (stepHotLumps R.params W) (G.settingOf γ).bases) hbase) hb
  · intro b hc hnf nb
    have h := hw.bondMark_ne_zero b hc hnf nb
    unfold bondMark at h
    rw [hco hnf] at h
    exact h
  · exact fun η' h' b hb c hd => half_le_meanNorm hS hGood hFrame hContour hGC hPlain hw η' h' hb c hd
end Requirements
end SettingOfWeight
open SettingOfWeight in
theorem settingAdmissibleOfHasWeight_holds (hGood : coldPlaquette_of_small_frameDeviation)
    (hFrame : FrameNearMinimizer) (hContour : ChartedFieldContourBound)
    (hGC : gaugeCovarianceStatement) (hPlain : KernelPlainAwayFromLumps) :
    SettingAdmissibleOfHasWeight := by
  intro T hT
  obtain ⟨y₀, h⟩ := exists_stepHypotheses_of_admissible T hT
  refine ⟨y₀, fun y hy R hOn _ n _ G hG γ hγ η hw => ?_⟩
  obtain ⟨Z, S, s₀, hS, hside⟩ := h y hy R hOn n G hG γ hγ
  exact isAdmissible_settingOf hS hGood hFrame hContour hGC hPlain hw hside
end YangMills.Construction.ClusterExpansionOfAStep
end
