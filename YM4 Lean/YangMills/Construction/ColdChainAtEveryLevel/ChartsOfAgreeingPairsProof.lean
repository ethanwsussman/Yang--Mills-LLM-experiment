import YangMills.Construction.ColdChainAtEveryLevel.ChartCoordinatesCompared
import YangMills.Construction.ColdChainAtEveryLevel.ChartsAtTheSameOffsets
import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfAgreeingPairs
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.BlockAverages.AgreeingCharts
open LatticePaths ComplexChart.BlockGeometry ComplexLineChart SameOffsets SameOffsetCharts ChartCoordinateComparison
  LatticeFractionalIntegration Analytic
variable {F : BlockFrame}
theorem localIteratedDeriv_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → E) (U : ChainChart F)
    (A : Fin 0 → ChainChart F) (v : Fin 0 → F.Site F.top → Fin 4 → imaginaryQuaternions) :
    localIteratedDeriv Φ U A v = Φ U (fun _ _ => 0) := by
  unfold localIteratedDeriv
  rw [iteratedFDeriv_zero_apply]
  have h1 : chartShiftAlong U A 0 = U := by
    obtain ⟨u, mu⟩ := U
    simp [chartShiftAlong]
  have h2 : topVariationAlong v 0 = fun _ _ => 0 := by
    funext y i
    simp [topVariationAlong]
  simp only [h1, h2]
theorem comparisonConstant_nonneg {c₀ : ℝ} (hc₀ : 0 < c₀) (k : ℕ) : 0 ≤ comparisonConstant c₀ k := by
  have hρ : 0 < comparisonRadius c₀ k := div_pos hc₀ (by positivity)
  exact add_nonneg (cauchyEstimateBound_nonneg zero_le_one hρ _) (cauchyEstimateBound_nonneg zero_le_one hρ _)
theorem norm_add_neg_one_smul_comm (x y : imaginaryQuaternions) :
    ‖x + (-1 : ℝ) • y‖ = ‖y + (-1 : ℝ) • x‖ := by
  rw [← norm_neg]
  congr 1
  module
theorem finsetLpNorm_norm_sub_le {β : Type} {p : ℝ} (hp : 1 ≤ p) (s : Finset β) (x y : β → imaginaryQuaternions) :
    finsetLpNorm p s (fun b => ‖x b + (-1 : ℝ) • y b‖) ≤
      finsetLpNorm p s (fun b => ‖x b‖) + finsetLpNorm p s (fun b => ‖y b‖) := by
  refine (finsetLpNorm_mono (by linarith) s fun b _ => ?_).trans (finsetLpNorm_add_le hp s _ _)
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul]
  simp
theorem sizedOnBondCells_chartGap {S : Finset F.Cell} {R : F.FieldChain} {b : F.Site F.depth × Fin 4}
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hb : b ∈ chordBonds S) (A B : ChainChart F) :
    SizedOnBondCells b (localNorm S R (chartMove A B (-1)) (oneSiteWeights F) (enclosingCell b.1))
      (chartMove B A (-1)) (fun _ _ => 0) := by
  classical
  have hnn : 0 ≤ localNorm S R (chartMove A B (-1)) (oneSiteWeights F) (enclosingCell b.1) := Real.sqrt_nonneg _
  refine ⟨?_, fun j hj => ?_, ?_⟩
  · refine le_trans (le_of_eq ?_)
      (finsetLpNorm_fine_le_localNorm S R (chartMove A B (-1)) _ (innerBonds_bondCells_subset_bondsOver hamb hodd hb 0))
    exact congrArg (finsetLpNorm 4 _) (funext fun c => norm_add_neg_one_smul_comm (B.fine c.1 c.2) (A.fine c.1 c.2))
  · refine le_trans (le_of_eq ?_)
      (finsetLpNorm_coarse_le_localNorm S R (chartMove A B (-1)) _ hj
        (innerBonds_bondCells_subset_bondsOver hamb hodd hb (j + 1)))
    exact congrArg (finsetLpNorm 2 _)
      (funext fun c => norm_add_neg_one_smul_comm (B.coarse j c.1 c.2) (A.coarse j c.1 c.2))
  · have h0 : crossingRotation b (fun _ _ => (0 : imaginaryQuaternions)) = 0 := by
      unfold crossingRotation
      split_ifs <;> rfl
    rw [h0, norm_zero]
    exact hnn
set_option maxHeartbeats 4000000 in
open Classical in
theorem agreeingChartsCompared (hB : referenceBoundsStatement) (hRf : referenceChordNearOneStatement)
    (hrec : UniformQuarticBoundAcrossLevels) (hLn : agreeingPairsLocalityStatement) :
    agreeingChartsComparedStatement := by
  obtain ⟨L₀, hfam⟩ := exists_bounded_extension_bondChartCoords hB hRf hrec
  obtain ⟨cl, hcl, hlines⟩ := hLn
  obtain ⟨P, hP⟩ := exists_leftInverse_imagToComplexCLM
  refine ⟨L₀, fun L hL hge => ?_⟩
  obtain ⟨c₀, hc₀, hc⟩ := hfam L hL hge
  refine ⟨min (c₀ / 16) cl, 110, comparisonConstant c₀, lt_min (by positivity) hcl,
    comparisonConstant_nonneg hc₀, ?_⟩
  intro F F' m S S' hFL hF'L ht hamb hamb' hm hreg hreg' s V V' Y Y' r hs hsc hcold hcold' hr hag U U' hU hU' b hb hbY
  obtain ⟨L', t', sd⟩ := F'
  have hLL : L' = F.blockSide := hF'L.trans hFL.symm
  have htt : t' = F.depth := ht
  subst hLL
  subst htt
  have hodd : Odd F.blockSide := hFL ▸ hL
  have hoddG : Odd (sameShapeFrame F sd).blockSide := hodd
  set c := min (c₀ / 16) cl with hcdef
  have hc16 : c ≤ c₀ / 16 := min_le_left _ _
  have hccl : c ≤ cl := min_le_right _ _
  have hcpos : 0 < c := lt_min (by positivity) hcl
  have hsc₀ : s ≤ c₀ := by linarith
  obtain ⟨-, hl2⟩ := hlines F (sameShapeFrame F sd) m S S' s V V' Y Y' r rfl rfl hodd hamb hamb' hm hreg hreg' hs
    (hsc.trans hccl) hcold hcold' hag
  obtain ⟨hs1, hs2, hSS, hVV⟩ := hag
  have hbS : b ∈ innerBonds S F.depth := (Finset.mem_filter.1 hb).1
  obtain ⟨x, i⟩ := b
  obtain ⟨hx, hx'⟩ := mem_innerBonds_iff.1 hbS
  simp only at hx hx' hbY
  obtain ⟨y, hyS, h, hh, rfl⟩ := exists_cellSite_eq hx
  rw [enclosingCell_cellSite hodd y hh] at hbY
  subst hbY
  set b : F.Site F.depth × Fin 4 := (cellSite y h, i) with hbd
  set D := bondCells b with hDd
  have hcell' : h + basisVector i ∉ centredCube F.blockSide →
      enclosingCell (cellSite y h + unitStep F.depth i) = y + siteOfCoords F.top (basisVector i) := fun hc' => by
    obtain ⟨-, h2, h3⟩ := isCrossingBond_of_add_basisVector_not_mem (y := y) hamb hodd hh hc'
    rw [h2, enclosingCell_cellSite hodd _ h3]
  have hcell : h + basisVector i ∈ centredCube F.blockSide →
      enclosingCell (cellSite y h + unitStep F.depth i) = y := fun hc' => by
    rw [cellSite_add_unitStep, enclosingCell_cellSite hodd y hc']
  have hunit : ∀ μ, |basisVector i μ| ≤ 1 := fun μ => by
    by_cases hμ : μ = i
    · subst hμ
      simp [basisVector]
    · simp [basisVector, hμ]
  have hyD : y ∈ D := mem_bondCells.2 (Or.inl (enclosingCell_cellSite hodd y hh).symm)
  have hD : IsNearCells y D := by
    intro u hu
    rcases mem_bondCells.1 hu with e | e
    · refine ⟨0, by simp, ?_⟩
      rw [e]
      simp only [hbd]
      rw [enclosingCell_cellSite hodd y hh, siteOfCoords_zero, add_zero]
    · by_cases hc' : h + basisVector i ∈ centredCube F.blockSide
      · refine ⟨0, by simp, ?_⟩
        rw [e]
        simp only [hbd]
        rw [hcell hc', siteOfCoords_zero, add_zero]
      · refine ⟨basisVector i, hunit, ?_⟩
        rw [e]
        simp only [hbd]
        exact hcell' hc'
  have hE : h + basisVector i ∉ centredCube F.blockSide → y + siteOfCoords F.top (basisVector i) ∈ D := fun hc' =>
    mem_bondCells.2 (Or.inr (hcell' hc').symm)
  have hDS : D ⊆ S := bondCells_subset hodd hbS
  have hr1 : 110 ≤ r := hr
  have hS' : ∀ a : Lattice4, (∀ i, |a i| ≤ 1) → y + siteOfCoords F.top a ∈ D →
      Y' + siteOfCoords (sameShapeFrame F sd).top a ∈ S' := by
    intro a ha hya
    refine (hSS a (fun μ => ?_)).1 (hDS hya)
    have : (1 : ℤ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
    exact (ha μ).trans this
  have hR := referenceFieldChain_agree (Y := y) (Y' := Y') (D := D) hamb hodd rfl hD (by omega) hDS hl2
  set R := referenceFieldChain S V with hRd
  set R' := referenceFieldChain S' V' with hR'd
  have hlow : depthSiteAtSameOffset y Y' (cellSite y h) =
      (cellSite Y' h : (sameShapeFrame F sd).Site (sameShapeFrame F sd).depth) := by
    have hsm : IsSmallOffset F F.depth h := fun μ => by
      have h2 := ((mem_centredCube_iff _ _).1 hh) μ
      have hL1 : (1 : ℤ) ≤ F.blockSide := by exact_mod_cast hodd.pos
      have e : (F.blockSide : ℤ) ^ (F.top - F.depth) = F.blockSide := by simp [BlockFrame.top]
      rw [e, abs_lt]
      constructor <;> omega
    exact siteAtSameOffset_siteAtOffset hamb hodd.pos y Y' hsm
  have hVy : V y i = V' Y' i := by
    have h1 := hVV ((0 : Lattice4), i) ⟨fun μ => by simp, fun μ => by
      have := hunit μ
      have h3 : (1 : ℤ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
      simp only [zero_add]
      exact this.trans h3⟩
    simpa [siteOfCoords_zero] using h1
  have htransfer : ∀ (U'' : ChainChart (sameShapeFrame F sd)) (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
      (v' : (sameShapeFrame F sd).Site (sameShapeFrame F sd).top → Fin 4 → imaginaryQuaternions),
      (h + basisVector i ∉ centredCube F.blockSide → v y i = v' Y' i) →
      bondChartCoord R' V' (depthSiteAtSameOffset y Y' (cellSite y h), i) U'' v' =
        bondChartCoord R V b (chartAtSameOffsets y Y' U'') v := by
    intro U'' v v' hvv
    rw [hlow]
    refine (bondChartCoord_chartAtSameOffsets hamb hamb' hodd hD R R' U'' hR V V' hh i hyD hE v v'
      fun hc' => ?_).symm
    show expUnit (v y i) * V y i = expUnit (v' Y' i) * V' Y' i
    rw [hvv hc', hVy]
  have hcy : enclosingCell b.1 = y := enclosingCell_cellSite hodd y hh
  have hnear : ∀ j, innerBonds D j ⊆ bondsOver S (cellBall S y 3) j := fun j => by
    have := innerBonds_bondCells_subset_bondsOver hamb hodd hb j
    rwa [hcy] at this
  have hUs4 : finsetLpNorm 4 (innerBonds D 0) (fun b => ‖U.fine b.1 b.2‖) ≤ c :=
    (finsetLpNorm_fine_le_localNorm S R U y (hnear 0)).trans (hU y hyS)
  have hUsm : ∀ j, j + 1 < F.top → finsetLpNorm 2 (innerBonds D (j + 1)) (fun b => ‖U.coarse j b.1 b.2‖) ≤ c :=
    fun j hj => (finsetLpNorm_coarse_le_localNorm S R U y hj (hnear (j + 1))).trans (hU y hyS)
  have hY'S : Y' ∈ S' := by
    have := hS' 0 (by simp) (by simpa [siteOfCoords_zero] using hyD)
    simpa [siteOfCoords_zero] using this
  have hT4 : finsetLpNorm 4 (innerBonds D 0) (fun b => ‖(chartAtSameOffsets y Y' U').fine b.1 b.2‖) ≤ c :=
    (finsetLpNorm_fine_chartAtSameOffsets_le hamb hamb' hodd hD hS' R' U').trans (hU' Y' hY'S)
  have hTm : ∀ j, j + 1 < F.top →
      finsetLpNorm 2 (innerBonds D (j + 1)) (fun b => ‖(chartAtSameOffsets y Y' U').coarse j b.1 b.2‖) ≤ c :=
    fun j hj => (finsetLpNorm_coarse_chartAtSameOffsets_le hamb hamb' hodd hD hS' R' U' hj).trans (hU' Y' hY'S)
  have hsmall : SmallOnBondCells b c₀ U :=
    ⟨hUs4.trans (by linarith), fun j hj => (hUsm j hj).trans (by linarith)⟩
  have hfam' := hc F m S hFL hamb hm hreg s V hs hsc₀ hcold b hb U hsmall
  have gen : ∀ (k : ℕ) (A : Fin k → ChainChart F) (A' : Fin k → ChainChart (sameShapeFrame F sd))
      (e : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions)
      (e' : Fin k → (sameShapeFrame F sd).Site (sameShapeFrame F sd).top → Fin 4 → imaginaryQuaternions),
      (h + basisVector i ∉ centredCube F.blockSide → ∀ l, e l y i = e' l Y' i) →
      ‖localIteratedDeriv (bondChartCoord R V b) U A e -
          localIteratedDeriv (bondChartCoord R' V' (depthSiteAtSameOffset y Y' (cellSite y h), i)) U' A' e'‖ ≤
        comparisonConstant c₀ k * (offsetChartGapNorm S R y y Y' U U' *
            ∏ l, localDirectionSize S R (topBondsAt b) y (A l) (e l) +
          ∑ l, offsetChartGapNorm S R y y Y' (A l) (A' l) * ∏ l' ∈ Finset.univ.erase l,
            (localDirectionSize S R (topBondsAt b) y (A l') (e l') + offsetChartGapNorm S R y y Y' (A l') (A' l'))) := by
    intro k A A' e e' he
    set Ã : Fin k → ChainChart F := fun l => chartAtSameOffsets y Y' (A' l) with hÃ
    have hrd : localIteratedDeriv (bondChartCoord R' V' (depthSiteAtSameOffset y Y' (cellSite y h), i)) U' A' e' =
        localIteratedDeriv (bondChartCoord R V b) (chartAtSameOffsets y Y' U') Ã e := by
      unfold localIteratedDeriv
      have hf : (fun t : Fin k → ℝ =>
          bondChartCoord R' V' (depthSiteAtSameOffset y Y' (cellSite y h), i) (chartShiftAlong U' A' t)
            (topVariationAlong e' t)) =
          fun t => bondChartCoord R V b (chartShiftAlong (chartAtSameOffsets y Y' U') Ã t) (topVariationAlong e t) := by
        funext t
        exact htransfer (chartShiftAlong U' A' t) (topVariationAlong e t) (topVariationAlong e' t) fun hc' => by
          simp only [topVariationAlong, he hc']
      rw [hf]
    rw [hrd]
    set gap₀ := offsetChartGapNorm S R y y Y' U U' with hgap₀
    have hg0 : SizedOnBondCells b gap₀ (chartMove (chartAtSameOffsets y Y' U') U (-1)) (fun _ _ => 0) := by
      have := sizedOnBondCells_chartGap (R := R) hamb hodd hb U (chartAtSameOffsets y Y' U')
      rwa [hcy] at this
    have hgap0 : 0 ≤ gap₀ := Real.sqrt_nonneg _
    set q₀ := min gap₀ (c₀ / 8) with hq₀
    have hc8 : 0 ≤ c₀ / 8 := by positivity
    have hq0 : 0 ≤ q₀ := le_min hgap0 hc8
    have hG : SizedOnBondCells b q₀ (chartMove (chartAtSameOffsets y Y' U') U (-1)) (fun _ _ => 0) := by
      refine ⟨le_min hg0.fine ?_, fun j hj => le_min (hg0.coarse j hj) ?_, le_min hg0.rearrangedPathCorner ?_⟩
      · have h1 := finsetLpNorm_norm_sub_le (p := 4) (by norm_num) (innerBonds D 0)
          (fun b => (chartAtSameOffsets y Y' U').fine b.1 b.2) (fun b => U.fine b.1 b.2)
        refine le_trans h1 ?_
        linarith
      · have h0 := finsetLpNorm_norm_sub_le (p := 2) (by norm_num) (innerBonds D (j + 1))
          (fun b => (chartAtSameOffsets y Y' U').coarse j b.1 b.2) (fun b => U.coarse j b.1 b.2)
        refine le_trans h0 ?_
        have h1 := hTm j hj
        have h2 := hUsm j hj
        linarith
      · have h0 : crossingRotation b (fun _ _ => (0 : imaginaryQuaternions)) = 0 := by
          unfold crossingRotation
          split_ifs <;> rfl
        rw [h0, norm_zero]
        exact hc8
    have hσ0 : ∀ l, 0 ≤ localDirectionSize S R (topBondsAt b) y (A l) (e l) := fun l =>
      add_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    have hγ0 : ∀ l, 0 ≤ offsetChartGapNorm S R y y Y' (A l) (A' l) := fun l => Real.sqrt_nonneg _
    have hσ : ∀ l, SizedOnBondCells b (localDirectionSize S R (topBondsAt b) y (A l) (e l)) (A l) (e l) :=
      fun l => by
        have := sizedOnBondCells_localDirectionSize (R := R) hamb hodd hb (A l) (e l)
        rwa [hcy] at this
    have hγ : ∀ l, SizedOnBondCells b (offsetChartGapNorm S R y y Y' (A l) (A' l))
        (chartMove (Ã l) (A l) (-1)) (fun _ _ => 0) := fun l => by
      have := sizedOnBondCells_chartGap (R := R) hamb hodd hb (A l) (Ã l)
      rwa [hcy] at this
    have hmain := norm_sliceIteratedDeriv_sub_le hc₀ hfam' P hP A Ã e _ _ hq0 (min_le_right _ _)
      hσ0 hγ0 hσ hγ hG
    refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (comparisonConstant_nonneg hc₀ k))
    have hp0 : 0 ≤ ∏ l, localDirectionSize S R (topBondsAt b) y (A l) (e l) :=
      Finset.prod_nonneg fun l _ => hσ0 l
    have := mul_le_mul_of_nonneg_right (min_le_left gap₀ (c₀ / 8)) hp0
    linarith
  have hmem : (depthSiteAtSameOffset y Y' (cellSite y h), i) ∈ chordBonds S' := by
    rw [hlow]
    have hnt : ¬ IsAxialTreeBond b := (Finset.mem_filter.1 hb).2
    have hb1 : ((cellSite Y' h : (sameShapeFrame F sd).Site (sameShapeFrame F sd).depth), i) ∈
        innerBonds S' (sameShapeFrame F sd).depth := by
      refine mem_innerBonds_iff.2 ⟨cellSite_mem_sitesOfCells hY'S hh, ?_⟩
      by_cases hc' : h + basisVector i ∈ centredCube F.blockSide
      · simp only
        rw [cellSite_add_unitStep]
        exact cellSite_mem_sitesOfCells hY'S hc'
      · obtain ⟨-, h2, h3⟩ :=
          isCrossingBond_of_add_basisVector_not_mem (F := sameShapeFrame F sd) (y := Y') hamb' hoddG hh hc'
        simp only
        rw [h2]
        exact cellSite_mem_sitesOfCells (hS' _ hunit (hE hc')) h3
    refine Finset.mem_filter.2 ⟨hb1, fun htree => hnt ?_⟩
    obtain ⟨hn1, hn2⟩ := htree
    have hc' : h + basisVector i ∈ centredCube F.blockSide := by
      by_contra hcn
      exact hn1 (isCrossingBond_of_add_basisVector_not_mem (F := sameShapeFrame F sd) (y := Y') hamb' hoddG hh hcn).1
    refine ⟨not_isCrossingBond_of_mem hodd hh hc', fun l hl => ?_⟩
    have h1 := hn2 l hl
    rw [cellOffset_cellSite (F := sameShapeFrame F sd) hamb' hoddG Y' hh] at h1
    show cellOffset (cellSite y h) l = 0
    rw [cellOffset_cellSite hamb hodd y hh]
    exact h1
  refine ⟨hmem, ?_, ?_⟩
  · have g0 := gen 0 (fun l => l.elim0) (fun l => l.elim0) (fun l => l.elim0) (fun l => l.elim0)
      (fun _ l => l.elim0)
    rw [localIteratedDeriv_zero, localIteratedDeriv_zero] at g0
    simpa using g0
  · intro k A A' e e' _ he
    refine gen k A A' e e' fun hc' l => ?_
    have hcr := (isCrossingBond_of_add_basisVector_not_mem (y := y) hamb hodd hh hc').1
    have hmemB : ((y, i) : F.Site F.top × Fin 4) ∈ topBondsAt b := by
      have hb' : IsCrossingBond b := hcr
      simp only [topBondsAt, if_pos hb', hcy]
      exact Finset.mem_singleton_self _
    have h1 := he l _ hmemB
    have htop : cellAtSameOffset y Y' y = Y' := by
      unfold cellAtSameOffset
      have e0 : (fun μ => ((y - y) μ).valMinAbs) = (0 : Lattice4) := by
        funext μ
        simp
      rw [e0, siteOfCoords_zero, add_zero]
    simpa [htop] using h1
end YangMills.Construction.BlockAverages.AgreeingCharts
end
