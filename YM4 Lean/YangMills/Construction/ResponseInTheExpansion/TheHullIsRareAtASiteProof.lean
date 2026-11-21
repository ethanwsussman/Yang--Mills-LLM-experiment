import YangMills.Construction.CellOfTheFlow.ACellIsRare
import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import YangMills.Construction.ResponseInTheExpansion.TheHullIsRareAtASite
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields CellWindows WeightedResponses RenormalizationStepParameters TorusLumps StepSettings
namespace HullRareAtSite
variable {n : ℕ} [NeZero n]
def gridCenteredAt (l : ℕ) (v : TorusSite n) : CellGrid :=
  ⟨l, fun i => (((v i).val : ℕ) : ℤ) - ((l : ℤ) - 1) / 2⟩
open Classical in
theorem mem_cell_zero_of_supDist_le {l d : ℕ} (hd : 2 * d + 2 ≤ l) (v w : TorusSite n) (h : supDist v w ≤ d) :
    w ∈ (gridCenteredAt l v).cell n 0 := by
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist v w
  have hb' : ∀ i, |e i| ≤ (d : ℤ) := fun i => by
    have := (hb i).trans h
    rw [Int.abs_eq_natAbs]
    exact_mod_cast this
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => ((l : ℤ) - 1) / 2 + e i, fun i => ?_, ?_⟩
  · have h1 := abs_le.mp (hb' i)
    constructor
    · show 0 ≤ ((l : ℤ) - 1) / 2 + e i
      omega
    · show ((l : ℤ) - 1) / 2 + e i < (l : ℤ)
      omega
  · rw [he]
    funext i
    simp [gridCenteredAt, siteOfInt]
    ring
open Classical in
theorem mem_interiorAtDepth_cell_zero {l d : ℕ} (hd : 2 * d + 2 ≤ l) (v : TorusSite n) :
    v ∈ interiorAtDepth d ((gridCenteredAt l v).cell n 0) := by
  refine Finset.mem_filter.mpr ⟨mem_cell_zero_of_supDist_le hd v v (by rw [supDist_self]; omega), fun w hw => ?_⟩
  by_contra hc
  exact hw (mem_cell_zero_of_supDist_le hd v w (by omega))
end HullRareAtSite
open HullRareAtSite in
open Classical in
theorem hullRareAtSiteStatement_of_cellEventsRare (hC : cellEventsRareStatement) : hullRareAtSiteStatement := by
  intro a ha
  obtain ⟨L₀, r₀, hr₀, hC₀⟩ := hC a ha
  refine ⟨max L₀ 2, r₀, hr₀, fun L hodd hL Tb h1 h2 hTb hrt => ?_⟩
  obtain ⟨y₀, hy₀⟩ := hC₀ L hodd ((le_max_left _ _).trans hL) Tb h1 h2 hTb hrt
  refine ⟨max y₀ Tb.floorMin, fun y hy hret hwil T β k e N _ hN hst hco hside v => ?_⟩
  have hcell := hy₀ y ((le_max_left _ _).trans hy) hret hwil T β k ⟨hst, hco⟩ e
  have hfit : (Tb.stepParameters y).Admissible := hTb.fits y ((le_max_right _ _).trans hy)
  subst hN
  set r := stageRange T k with hr
  set l := baseCellSide (Tb.stepParameters y).side r with hl
  have hL2 : 1 < (Tb.stepParameters y).side := by
    have := hfit.L_ge
    omega
  have hr1 : 1 ≤ r := by
    have h0 : (0 : ℝ) < (T.stage k).coupling :=
      lt_of_lt_of_le (lt_of_lt_of_le one_pos hfit.y₁_ge) (hst.onFamily k le_rfl).le_coupling
    exact Nat.ceil_pos.mpr (by positivity)
  have hl7 : 2 ^ 7 * r ≤ l := Nat.le_pow_clog hL2 _
  have hd : 2 * (8 * r) + 2 ≤ l := by omega
  have hl0 : 0 < l := by omega
  have hside' : 2 * l ≤ 2 * (Tb.stepParameters y).side ^ e := hside
  obtain ⟨-, -, h3, -⟩ := hcell (gridCenteredAt l v) {0} rfl hside' (by
    intro κ hκ
    rw [Finset.mem_singleton] at hκ
    subst hκ
    refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Ico.mpr ⟨le_rfl, ?_⟩
    have h4 : l ≤ 2 * (Tb.stepParameters y).side ^ e := by omega
    have h5 : 0 < 2 * (Tb.stepParameters y).side ^ e / l := Nat.div_pos h4 hl0
    show (0 : ℤ) < ((2 * (Tb.stepParameters y).side ^ e / l : ℕ) : ℤ)
    exact_mod_cast h5)
  have hsub : {u : MarkedSample (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ e) |
      v ∈ (stageState T k _ u).2.1} ⊆
      {u | ∀ κ ∈ ({0} : Finset (Fin 4 → ℤ)), (stageHull T k _ u ∩
        interiorAtDepth (8 * r) ((gridCenteredAt l v).cell (2 * (Tb.stepParameters y).side ^ e) κ)).Nonempty} := by
    intro u hu κ hκ
    rw [Finset.mem_singleton] at hκ
    subst hκ
    exact ⟨v, Finset.mem_inter.mpr ⟨hu, mem_interiorAtDepth_cell_zero hd v⟩⟩
  have hle := (measure_mono hsub).trans h3
  have hp : 0 ≤ cellEventBound Tb (T.stage k).coupling ^ ({0} : Finset (Fin 4 → ℤ)).card := by
    unfold cellEventBound
    positivity
  have h6 : (markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ e)).real {u | v ∈ (stageState T k _ u).2.1} ≤
      cellEventBound Tb (T.stage k).coupling ^ ({0} : Finset (Fin 4 → ℤ)).card :=
    ENNReal.toReal_le_of_le_ofReal hp hle
  rw [Finset.card_singleton, pow_one] at h6
  exact h6
end YangMills.Construction.ResponseInTheExpansion
end
