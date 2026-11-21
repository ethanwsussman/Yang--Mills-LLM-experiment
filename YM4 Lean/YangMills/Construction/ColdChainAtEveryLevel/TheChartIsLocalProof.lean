import YangMills.Construction.ColdChainAtEveryLevel.ChartOnComplexLines
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
open Metric
namespace YangMills.Construction.BlockAverages
open LatticePaths ComplexChart.BlockGeometry ComplexLineChart
variable {F : BlockFrame}
section Congr
theorem treeHolonomy_congr (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {S : Finset F.Cell}
    {X X' : F.GaugeField F.depth}
    (h : ChartCoordinates.GaugeAgreeOnBonds S F.depth X X') {x : F.Site F.depth} (hx : x ∈ sitesOfCells S F.depth) :
    treeHolonomy X x = treeHolonomy X' x := by
  obtain ⟨y, hy, g, hg, rfl⟩ := exists_cellSite_eq hx
  unfold treeHolonomy
  rw [enclosingCell_cellSite hodd y hg, cellOffset_cellSite hamb hodd y hg]
  have hp : AllAlong (fun v => cellCentre F.depth y + siteOfCoords F.depth v ∈
      (sitesOfCells S F.depth : Set (F.Site F.depth))) 0 (axisPath g 1) :=
    allAlong_mono (fun v hv => cellSite_mem_sitesOfCells hy
      (ComplexChainStep.mem_centredCube_of_between hg hodd.pos hv)) (axisPath_spec g 1).1
  have := ChartCoordinates.pathHolonomy_congr (D := (sitesOfCells S F.depth : Set (F.Site F.depth)))
    (fun x i hx hx' => h x i hx hx') (cellCentre F.depth y) _ 0 hp
  rwa [ChartCoordinates.add_siteOfCoords_zero] at this
theorem bondChartCoord_congr (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (R : F.FieldChain)
    (V : F.GaugeField F.top) {S : Finset F.Cell}
    {b : F.Site F.depth × Fin 4} (hb : b ∈ innerBonds S F.depth) {U U' : ChainChart F}
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (h : ChartEqOnBonds S U U') :
    bondChartCoord R V b U v = bondChartCoord R V b U' v := by
  obtain ⟨hx, hx'⟩ := mem_innerBonds_iff.1 hb
  have hf := ChartCoordinates.chartField_congr hodd R h F.depth (by simp [BlockFrame.top])
  have hk : ∀ x : F.Site F.depth, x ∈ sitesOfCells S F.depth → chartGauge R U F.top (enclosingCell x) =
      chartGauge R U' F.top (enclosingCell x) := fun x hx =>
    ChartCoordinates.balancingGauge_congr hodd (by simp [BlockFrame.top]) (R F.depth) hf
      (mem_sitesOfCells_top.2 (enclosingCell_mem_of_mem_sitesOfCells hodd hx))
  unfold bondChartCoord gaugedBondElement
  rw [hk _ hx, hk _ hx', treeHolonomy_congr hamb hodd hf hx, treeHolonomy_congr hamb hodd hf hx',
    hf b.1 b.2 hx hx']
end Congr
theorem div_succ_mul_le_of_le {c S K : ℝ} (hc : 0 ≤ c) (hK : 0 < K + 1) (hS : S ≤ K) :
    c / (K + 1) * S ≤ c := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hK]
  nlinarith
set_option maxHeartbeats 1000000 in
open Classical in
theorem chartLocality (hB : referenceBoundsStatement) (hRf : referenceChordNearOneStatement)
    (hrec : UniformQuarticBoundAcrossLevels) : chartLocalityStatement := by
  obtain ⟨L₀, hfam⟩ := exists_bounded_extension_bondChartCoords hB hRf hrec
  obtain ⟨P, hP⟩ := exists_leftInverse_imagToComplexCLM
  refine ⟨L₀, fun L hL hge => ?_⟩
  obtain ⟨c, hcpos, hc⟩ := hfam L hL hge
  refine ⟨c, fun k => Analytic.cauchyHalvingConstant k * 1 / (c / ((k : ℝ) + 1)) ^ k, hcpos, fun k => ?_, ?_⟩
  · have := Analytic.cauchyHalvingConstant_pos k
    positivity
  intro F m S hFL hamb hm hreg s V hs hsc hcold U hU b hb
  have hodd : Odd F.blockSide := hFL ▸ hL
  set R := referenceFieldChain S V with hRdef
  have hbS : b ∈ innerBonds S F.depth := (Finset.mem_filter.1 hb).1
  obtain ⟨hx, hx'⟩ := mem_innerBonds_iff.1 hbS
  set y := enclosingCell b.1 with hy
  have hyS : y ∈ S := enclosingCell_mem_of_mem_sitesOfCells hodd hx
  have hsmall : SmallOnBondCells b c U :=
    ⟨(finsetLpNorm_fine_le_localNorm S R U y (innerBonds_bondCells_subset_bondsOver hamb hodd hb 0)).trans
        (hU y hyS),
      fun j hj => (finsetLpNorm_coarse_le_localNorm S R U y hj
        (innerBonds_bondCells_subset_bondsOver hamb hodd hb (j + 1))).trans (hU y hyS)⟩
  have ext : ∀ (ι : Type) [Fintype ι] (A : ι → ChainChart F) (e : ι → F.Site F.top → Fin 4 → imaginaryQuaternions)
      (w : ι → ℝ) (ρ : ℝ), (∀ l, 0 ≤ w l) → 0 < ρ →
      ρ * ∑ l, w l * localDirectionSize S R (topBondsAt b) y (A l) (e l) ≤ c →
      ∃ g, Analytic.IsBoundedHolomorphicExtension imagToComplexCLM
        (fun t : ι → ℝ => bondChartCoord R V b (chartShiftAlong U A (fun l => w l * t l))
          (topVariationAlong e (fun l => w l * t l))) g ρ 1 := fun ι _ A e w ρ hw hρ hbud =>
    hc F m S hFL hamb hm hreg s V hs hsc hcold b hb U hsmall ι A e w _ ρ hw hρ hbud
      (fun l => sizedOnBondCells_localDirectionSize hamb hodd hb (A l) (e l))
  refine ⟨fun U' U'' v h => bondChartCoord_congr hamb hodd R V hbS v h, ?_, ?_⟩
  · intro ι _ A e
    set q : ι → ℝ := fun l => localDirectionSize S R (topBondsAt b) y (A l) (e l) with hq
    have hq0 : ∀ l, 0 ≤ q l := fun l => add_nonneg (Real.sqrt_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    have hsum : 0 ≤ ∑ l, q l := Finset.sum_nonneg fun l _ => hq0 l
    obtain ⟨g, hg⟩ := ext ι A e (fun _ => 1) (c / (∑ l, q l + 1)) (fun _ => zero_le_one) (by positivity) (by
      simp only [one_mul]
      exact div_succ_mul_le_of_le hcpos.le (by positivity) le_rfl)
    have h := hg.analyticAt_of_leftInverse P hP
    simpa only [one_mul] using h
  · intro k A e
    set q : Fin k → ℝ := fun l => localDirectionSize S R (topBondsAt b) y (A l) (e l) with hq
    have hq0 : ∀ l, 0 ≤ q l := fun l => add_nonneg (Real.sqrt_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    refine le_mul_prod_of_scaled q hq0 fun w hw hwq => ?_
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hbud : c / ((k : ℝ) + 1) * ∑ l, w l * q l ≤ c := by
      have h1 : ∑ l, w l * q l ≤ k := by
        refine (Finset.sum_le_sum fun l _ => hwq l).trans ?_
        simp
      exact div_succ_mul_le_of_le hcpos.le hk1 h1
    obtain ⟨g, hg⟩ := ext (Fin k) A e w (c / ((k : ℝ) + 1)) (fun l => (hw l).le) (by positivity) hbud
    have h1 := hg.norm_iteratedFDeriv_basis_le P hP norm_imagToComplexCLM
    have h2 := iteratedFDeriv_comp_diagonalScaling
      (fun t : Fin k → ℝ => bondChartCoord R V b (chartShiftAlong U A t) (topVariationAlong e t)) w
      (fun l => (hw l).ne')
    rw [h2, norm_smul, Real.norm_of_nonneg (Finset.prod_nonneg fun l _ => (hw l).le)] at h1
    exact h1
end YangMills.Construction.BlockAverages
end
