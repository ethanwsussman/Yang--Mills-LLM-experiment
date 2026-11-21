import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.ColdChainAtEveryLevel.SitesOfAPatch
import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeOfTheChartOnTwoTori
import YangMills.Construction.SummableBoundsOfTheFlow.FloorsOfTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenStayNear
import YangMills.Construction.SummableBoundsOfTheFlow.ShortMovesOfAChart
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeBetweenComparesOnTwoTori
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeMovesByItsKernels
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeOfTheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.SumOfTheWeightsAboutACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace SummableBoundsOfTheFlow
variable {F : BlockFrame}
private theorem chartedField_congr {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions} (V : F.GaugeField F.top)
    (h : ∀ z i, ¬ IsAxialTreeBond (z, i) → w z i = w' z i) : chartedField w V = chartedField w' V := by
  funext x i
  unfold chartedField
  by_cases hc : IsCrossingBond (x, i)
  · have hnt : ¬ IsAxialTreeBond (x, i) := fun ht => ht.1 hc
    simp only [hc, if_true, h x i hnt]
  · by_cases ht : IsAxialTreeBond (x, i)
    · simp only [hc, ht, if_true, if_false]
    · simp only [hc, ht, if_false, h x i ht]
abbrev _root_.YangMills.SharedProofs.p16263 := @chartedField_congr
private theorem chartedSlope_congr {a : ℝ} {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions} (V : F.GaugeField F.top)
    (h : ∀ z i, ¬ IsAxialTreeBond (z, i) → w z i = w' z i) (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions)
    (hb : ¬ IsAxialTreeBond b) : chartedSlope a w V b e = chartedSlope a w' V b e := by
  unfold chartedSlope chartedEnergy
  congr 1
  funext u
  have : chartedField (Function.update w b.1 (Function.update (w b.1) b.2 (w b.1 b.2 + u • e))) V =
      chartedField (Function.update w' b.1 (Function.update (w' b.1) b.2 (w' b.1 b.2 + u • e))) V := by
    apply chartedField_congr
    intro z i hz
    by_cases hx : z = b.1
    · subst hx
      by_cases hi : i = b.2
      · subst hi
        simp [h _ _ hb]
      · simp [Function.update_of_ne hi, h _ _ hz]
    · simp [Function.update_of_ne hx, h _ _ hz]
  rw [this]
private def zeroOnTree (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) : F.Site F.depth → Fin 4 → imaginaryQuaternions := by
  classical exact fun z i => if IsAxialTreeBond (z, i) then 0 else w z i
private theorem zeroOnTree_of_not_tree {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {z : F.Site F.depth} {i : Fin 4}
    (h : ¬ IsAxialTreeBond (z, i)) : zeroOnTree w z i = w z i := by simp [zeroOnTree, h]
private theorem zeroOnTree_of_tree {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {z : F.Site F.depth} {i : Fin 4}
    (h : IsAxialTreeBond (z, i)) : zeroOnTree w z i = 0 := by simp [zeroOnTree, h]
private theorem agreeOnBall_mono {F' : BlockFrame} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    {q r : ℕ} (h : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q) (hr : r ≤ q) :
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hbox : ∀ g, WithinRadius r g → WithinRadius q g := fun g hg i => (hg i).trans (by exact_mod_cast hr)
  refine ⟨fun i => ?_, fun i => ?_, fun g hg => h3 g (hbox g hg), fun b hb => h4 b ⟨hbox _ hb.1, hbox _ hb.2⟩⟩
  · rcases h1 i with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · rcases h2 i with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
abbrev _root_.YangMills.SharedProofs.p37458 := @agreeOnBall_mono
private def relOffset (Y y : F.Cell) : Fin 4 → ℤ := fun i => ((y - Y) i).valMinAbs
private theorem add_relOffset (Y y : F.Cell) : Y + siteOfCoords F.top (relOffset Y y) = y := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.add_siteOfCoords_cellDisplacement <;> assumption
private theorem abs_relOffset_le (Y y : F.Cell) (i : Fin 4) : |relOffset Y y i| ≤ cellSupDist Y y := by
  have h1 : (((Y - y) i).valMinAbs).natAbs ≤ cellSupDist Y y :=
    Finset.le_sup (f := fun i => ((Y i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
  have e : (y - Y) i = -((Y - y) i) := by simp
  have h2 : ((relOffset Y y i)).natAbs = (((Y - y) i).valMinAbs).natAbs := by
    unfold relOffset
    rw [e, ZMod.natAbs_valMinAbs_neg]
  have h3 : |relOffset Y y i| = ((relOffset Y y i).natAbs : ℤ) := Int.abs_eq_natAbs _
  rw [h3, h2]
  exact_mod_cast h1
abbrev _root_.YangMills.DeltaSharedProofs.p501586 := @abs_relOffset_le
private theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by simp [BlockFrame.period]
private theorem relOffset_add_siteOfCoords {Y : F.Cell} {h : Fin 4 → ℤ} (hh : ∀ i, 2 * |h i| < F.extent i) :
    relOffset Y (Y + siteOfCoords F.top h) = h := by
  funext i
  unfold relOffset
  have e : ((Y + siteOfCoords F.top h - Y : F.Cell) i) = ((h i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  rw [e]
  exact valMinAbs_intCast_of_small (Or.inr (by rw [period_top]; exact_mod_cast hh i))
private theorem mem_chordBonds_of_not_tree (hB : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 0 < F.extent i) (z : F.Site F.depth) (i : Fin 4) (h : ¬ IsAxialTreeBond (z, i)) :
    (z, i) ∈ chordBonds (finiteCells F) := by
  unfold chordBonds innerBonds
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨⟨hB F hL hs z, hB F hL hs _⟩, h⟩
abbrev _root_.YangMills.SharedProofs.p40832 := @mem_chordBonds_of_not_tree
private theorem not_tree_of_mem_chordBonds {b : F.Site F.depth × Fin 4} (hb : b ∈ chordBonds (finiteCells F)) :
    ¬ IsAxialTreeBond b := by
  simp only [chordBonds, Finset.mem_filter] at hb
  exact hb.2
private def transport {F' : BlockFrame} (Y : F.Cell) (Y' : F'.Cell) (z : F.Site F.depth) : F'.Site F'.depth :=
  cellCentre F'.depth (Y' + siteOfCoords F'.top (relOffset Y (enclosingCell z))) + siteOfCoords F'.depth (cellOffset z)
private theorem transport_fineBondAt {F' : BlockFrame} (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) (Y' : F'.Cell)
    {h o : Fin 4 → ℤ} (ho : o ∈ centredCube F.blockSide) (hh : ∀ i, 2 * |h i| < F.extent i) (i : Fin 4) :
    transport Y Y' (fineBondAt Y h o i).1 = (fineBondAt Y' h o i).1 := by
  unfold transport fineBondAt
  simp only
  rw [TopLevelSites.enclosingCell_centre_add hL hs _ o ho, TopLevelSites.cellOffset_centre_add hL hs _ o ho,
    relOffset_add_siteOfCoords hh]
private theorem site_eq_fineBondAt (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) (z : F.Site F.depth) (i : Fin 4) :
    cellOffset z ∈ centredCube F.blockSide ∧ (z, i) = fineBondAt Y (relOffset Y (enclosingCell z)) (cellOffset z) i := by
  obtain ⟨y, o, ho, hz⟩ := TopLevelSites.exists_centre_add hL hs z
  have h1 : enclosingCell z = y := by rw [hz]; exact TopLevelSites.enclosingCell_centre_add hL hs y o ho
  have h2 : cellOffset z = o := by rw [hz]; exact TopLevelSites.cellOffset_centre_add hL hs y o ho
  refine ⟨h2 ▸ ho, ?_⟩
  unfold fineBondAt
  rw [add_relOffset, h1, h2, ← hz]
private def spliced {F' : BlockFrame} (q : ℕ) (Y : F.Cell) (Y' : F'.Cell) (u : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (u' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) : F.Site F.depth → Fin 4 → imaginaryQuaternions := by
  classical exact fun z i => if IsAxialTreeBond (z, i) then 0 else
    if cellSupDist Y (enclosingCell z) ≤ q / 2 then u' (transport Y Y' z) i else u z i
private theorem cellSupDist_enclosingCell_add_unitStep_le (hL : Odd F.blockSide) (hs : ∀ i, 3 ≤ F.extent i) (x : F.Site F.depth) (i : Fin 4) :
    cellSupDist (enclosingCell x) (enclosingCell (x + unitStep F.depth i)) ≤ 1 := by
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by have := hs i; omega
  obtain ⟨z, h, hh, rfl⟩ := TopLevelSites.exists_centre_add hL hs2 x
  rw [TopLevelSites.enclosingCell_centre_add hL hs2 z h hh]
  by_cases he : h i = TopLevelSites.halfWidth F.blockSide
  · obtain ⟨h1, h2⟩ := TopLevelSites.centre_add_add_unitStep_of_edge hL hs2 z h hh i he
    rw [h2, TopLevelSites.enclosingCell_centre_add hL hs2 _ _ h1]
    refine Finset.sup_le fun l _ => ?_
    have e0 : ((z - (z + unitStep F.top i) : F.Cell) l) = -((unitStep F.top i : F.Cell) l) := by simp
    show (((z - (z + unitStep F.top i) : F.Cell) l).valMinAbs).natAbs ≤ 1
    rw [e0, ZMod.natAbs_valMinAbs_neg]
    have e1 : ((unitStep F.top i : F.Cell) l) = (((Pi.single i 1 : Fin 4 → ℤ) l : ℤ) : ZMod (F.period F.top l)) := rfl
    rw [e1, valMinAbs_intCast_of_small (Or.inr ?_)]
    · by_cases hl : l = i
      · subst hl; simp
      · simp [hl]
    · rw [period_top]
      have := hs l
      by_cases hl : l = i
      · subst hl
        simp
        omega
      · simp [hl]
        omega
  · have hin : h + Pi.single i 1 ∈ centredCube F.blockSide := by
      have hc := (TopLevelSites.mem_centredCube_iff h).mp hh
      rw [TopLevelSites.mem_centredCube_iff]
      intro l
      by_cases hl : l = i
      · subst hl
        have := hc l
        simp only [Pi.add_apply, Pi.single_eq_same]
        omega
      · simpa [hl] using hc l
    rw [TopLevelSites.centre_add_add_unitStep, TopLevelSites.enclosingCell_centre_add hL hs2 _ _ hin]
    unfold cellSupDist
    simp
private theorem card_fiber_le (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) :
    (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤
      (centredCube F.blockSide).card * 4 := by
  classical
  have := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z)
    (t := centredCube F.blockSide ×ˢ (Finset.univ : Finset (Fin 4)))
    (fun b => (cellOffset b.1.1, b.1.2)) ?_ ?_
  · simpa [Finset.card_product] using this
  · intro b _
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, and_true]
    exact (site_eq_fineBondAt hL hs z b.1.1 b.1.2).1
  · intro b hb b' hb' he
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb hb'
    simp only [Prod.mk.injEq] at he
    have h1 := (site_eq_fineBondAt hL hs z b.1.1 b.1.2).2
    have h2 := (site_eq_fineBondAt hL hs z b'.1.1 b'.1.2).2
    rw [hb] at h1
    rw [hb', ← he.1, ← he.2] at h2
    have h3 : ((b.1.1, b.1.2) : F.Site F.depth × Fin 4) = (b'.1.1, b.1.2) := h1.trans h2.symm
    have h4 : b.1.1 = b'.1.1 := (Prod.mk.inj h3).1
    exact Subtype.ext (Prod.ext h4 he.2)
private theorem chartedSlope_compare_far {L : ℕ} {a δ δ₁ C₂ C₃ E W σc : ℝ} {F' : BlockFrame} {V : F.GaugeField F.top}
    {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {q : ℕ}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    (hB : BlocksCoverLowerLevel)
    (hFL : F.blockSide = L) (hLodd : Odd L) (hs : ∀ i, 2 * q + 2 < F.extent i)
    (hq : 64 ≤ q) (hδ : 0 < δ) (hC₂ : 0 ≤ C₂) (hE : 0 ≤ E)
    (hkern : ∀ u₀ u₁ : F.Site F.depth → Fin 4 → imaginaryQuaternions,
      (∀ u : F.Site F.depth → Fin 4 → imaginaryQuaternions,
        (∀ z i, ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ u z i = u₀ z i + θ • (u₁ z i - u₀ z i)) →
        IsAdmissibleChartPoint L σc u V) →
      (∀ b, b ∉ chordBonds (finiteCells F) → u₁ b.1 b.2 = u₀ b.1 b.2) →
      ∀ (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions), ‖e‖ = 1 →
        |chartedSlope a u₁ V b e - chartedSlope a u₀ V b e| ≤
          ∑ b' ∈ chordBonds (finiteCells F),
            C₂ * Real.exp (-(δ₁ * cellSupDist (enclosingCell b.1) (enclosingCell b'.1))) * ‖u₁ b'.1 b'.2 - u₀ b'.1 b'.2‖)
    (hpts : ∀ u : F.Site F.depth → Fin 4 → imaginaryQuaternions,
      (∀ z i, ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ u z i = zeroOnTree (fun z i => w z i) z i +
        θ • (spliced q Y Y' (zeroOnTree w) (zeroOnTree w') z i - zeroOnTree w z i)) →
      IsAdmissibleChartPoint L σc u V)
    (htwo : ∀ (h o : Fin 4 → ℤ) (i : Fin 4) (e : imaginaryQuaternions), IsFineBondWithinRadius Y (q / 2 / 2) h o i → ‖e‖ = 1 →
      |chartedSlope a (spliced q Y Y' (zeroOnTree w) (zeroOnTree w')) V (fineBondAt Y h o i) e -
        chartedSlope a (zeroOnTree w') V' (fineBondAt Y' h o i) e| ≤
        C₃ * Real.exp (-(δ * ((L : ℝ) * (((q / 2 : ℕ) : ℝ) / 2) - 2 * L - 1))))
    (hmove : ∀ (z : F.Site F.depth) (i : Fin 4), (z, i) ∈ chordBonds (finiteCells F) →
      cellSupDist Y (enclosingCell z) ≤ q / 2 →
      ‖w' (transport Y Y' z) i - w z i‖ ≤ E * Real.exp (-(δ * ((q : ℝ) - cellSupDist Y (enclosingCell z)))))
    (hnt' : ∀ (z : F.Site F.depth) (i : Fin 4), ¬ IsAxialTreeBond (z, i) → ¬ IsAxialTreeBond (transport Y Y' z, i))
    (hsum : ∀ b : F.Site F.depth × Fin 4, ∑ b' ∈ chordBonds (finiteCells F),
      Real.exp (-((δ₁ - δ) * cellSupDist (enclosingCell b.1) (enclosingCell b'.1))) ≤ W)
    (h o : Fin 4 → ℤ) (i : Fin 4) (e : imaginaryQuaternions) (hb : IsFineBondWithinRadius Y (q / 4) h o i) (he : ‖e‖ = 1)
    (hb' : ¬ IsAxialTreeBond (fineBondAt Y' h o i)) :
    |chartedSlope a w V (fineBondAt Y h o i) e - chartedSlope a w' V' (fineBondAt Y' h o i) e| ≤
      C₂ * E * W * Real.exp (-(3 / 4 * δ * q)) +
        C₃ * Real.exp (-(δ * ((L : ℝ) * (((q / 2 : ℕ) : ℝ) / 2) - 2 * L - 1))) := by
  have hnt : ¬ IsAxialTreeBond (fineBondAt Y h o i) := not_tree_of_mem_chordBonds hb.2.1
  have hL : Odd F.blockSide := hFL ▸ hLodd
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by have := hs i; omega
  have hch : ∀ z i, ¬ IsAxialTreeBond (z, i) → (z, i) ∈ chordBonds (finiteCells F) := fun z i hz =>
    mem_chordBonds_of_not_tree hB hL (fun i => by have := hs2 i; omega) z i hz
  set u := zeroOnTree w with hu
  set u' := zeroOnTree w' with hu'
  set X := spliced q Y Y' u u' with hX
  have e1 : chartedSlope a w V (fineBondAt Y h o i) e = chartedSlope a u V (fineBondAt Y h o i) e :=
    chartedSlope_congr V (fun z i hz => (zeroOnTree_of_not_tree hz).symm) _ e hnt
  have e2 : chartedSlope a w' V' (fineBondAt Y' h o i) e = chartedSlope a u' V' (fineBondAt Y' h o i) e :=
    chartedSlope_congr V' (fun z i hz => (zeroOnTree_of_not_tree hz).symm) _ e hb'
  rw [e1, e2]
  have hoff : ∀ b, b ∉ chordBonds (finiteCells F) → X b.1 b.2 = u b.1 b.2 := by
    intro b hb0
    have ht : IsAxialTreeBond (b.1, b.2) := by
      by_contra hc
      exact hb0 (hch _ _ hc)
    simp [hX, spliced, hu, zeroOnTree_of_tree ht, ht]
  have hK := hkern u X hpts hoff (fineBondAt Y h o i) e he
  have hterm : ∀ b' ∈ chordBonds (finiteCells F),
      C₂ * Real.exp (-(δ₁ * cellSupDist (enclosingCell (fineBondAt Y h o i).1) (enclosingCell b'.1))) * ‖X b'.1 b'.2 - u b'.1 b'.2‖ ≤
      C₂ * E * Real.exp (-(3 / 4 * δ * q)) *
        Real.exp (-((δ₁ - δ) * cellSupDist (enclosingCell (fineBondAt Y h o i).1) (enclosingCell b'.1))) := by
    intro b' hb'c
    have hnb := not_tree_of_mem_chordBonds hb'c
    have hnb' : ¬ IsAxialTreeBond (b'.1, b'.2) := hnb
    by_cases hnear : cellSupDist Y (enclosingCell b'.1) ≤ q / 2
    · have hX1 : X b'.1 b'.2 = w' (transport Y Y' b'.1) b'.2 := by
        simp [hX, spliced, hnb', hnear, hu', zeroOnTree_of_not_tree (hnt' _ _ hnb')]
      have hu1 : u b'.1 b'.2 = w b'.1 b'.2 := zeroOnTree_of_not_tree hnb'
      rw [hX1, hu1]
      have hm := hmove b'.1 b'.2 hb'c hnear
      set d : ℝ := ((cellSupDist (enclosingCell (fineBondAt Y h o i).1) (enclosingCell b'.1) : ℕ) : ℝ) with hd
      set dY : ℝ := ((cellSupDist Y (enclosingCell b'.1) : ℕ) : ℝ) with hdY
      have hd1 : dY ≤ (q : ℝ) / 4 + d := by
        have h1 := PatchLocality.cellSupDist_triangle Y (enclosingCell (fineBondAt Y h o i).1) (enclosingCell b'.1)
        have h2 := hb.2.2.2.1
        have h3 : ((q / 4 : ℕ) : ℝ) ≤ (q : ℝ) / 4 := Nat.cast_div_le
        have h4 : (cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) : ℝ) ≤ ((q / 4 : ℕ) : ℝ) := by exact_mod_cast h2
        have h5 : (cellSupDist Y (enclosingCell b'.1) : ℝ) ≤ (cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) : ℝ) +
            (cellSupDist (enclosingCell (fineBondAt Y h o i).1) (enclosingCell b'.1) : ℝ) := by exact_mod_cast h1
        linarith
      have hexp : Real.exp (-(δ₁ * d)) * Real.exp (-(δ * ((q : ℝ) - dY))) ≤
          Real.exp (-(3 / 4 * δ * q)) * Real.exp (-((δ₁ - δ) * d)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left hd1 hδ.le
        nlinarith
      calc C₂ * Real.exp (-(δ₁ * d)) * ‖w' (transport Y Y' b'.1) b'.2 - w b'.1 b'.2‖
          ≤ C₂ * Real.exp (-(δ₁ * d)) * (E * Real.exp (-(δ * ((q : ℝ) - dY)))) := by gcongr
        _ = C₂ * E * (Real.exp (-(δ₁ * d)) * Real.exp (-(δ * ((q : ℝ) - dY)))) := by ring
        _ ≤ C₂ * E * (Real.exp (-(3 / 4 * δ * q)) * Real.exp (-((δ₁ - δ) * d))) := by gcongr
        _ = _ := by ring
    · have hX1 : X b'.1 b'.2 = u b'.1 b'.2 := by
        simp [hX, spliced, hnb', hnear]
      rw [hX1, sub_self, norm_zero, mul_zero]
      positivity
  have hS1 := (hK.trans (Finset.sum_le_sum hterm))
  have hS2 : ∑ b' ∈ chordBonds (finiteCells F), C₂ * E * Real.exp (-(3 / 4 * δ * q)) *
      Real.exp (-((δ₁ - δ) * cellSupDist (enclosingCell (fineBondAt Y h o i).1) (enclosingCell b'.1))) ≤
      C₂ * E * W * Real.exp (-(3 / 4 * δ * q)) := by
    rw [← Finset.mul_sum]
    calc _ ≤ C₂ * E * Real.exp (-(3 / 4 * δ * q)) * W := by
          gcongr
          exact hsum (fineBondAt Y h o i)
      _ = _ := by ring
  have h3 := htwo h o i e (by
    have : q / 2 / 2 = q / 4 := by omega
    rw [this]; exact hb) he
  calc |chartedSlope a u V (fineBondAt Y h o i) e - chartedSlope a u' V' (fineBondAt Y' h o i) e|
      ≤ |chartedSlope a u V (fineBondAt Y h o i) e - chartedSlope a X V (fineBondAt Y h o i) e| +
        |chartedSlope a X V (fineBondAt Y h o i) e - chartedSlope a u' V' (fineBondAt Y' h o i) e| :=
        abs_sub_le _ _ _
    _ ≤ _ := by
        rw [abs_sub_comm]
        exact add_le_add (hS1.trans hS2) h3
private theorem isAdmissibleChartPoint_spliced {L : ℕ} {σ σc ε B : ℝ} {F' : BlockFrame} {V : F.GaugeField F.top} {Y : F.Cell} {Y' : F'.Cell} {q : ℕ}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    (hS : ChartLipschitz.ChartedFieldLipschitz)
    (hwB : ∀ z i, ¬ IsAxialTreeBond (z, i) → ‖w z i‖ ≤ B)
    (hw'B : ∀ z i, ¬ IsAxialTreeBond (z, i) → ‖w' (transport Y Y' z) i‖ ≤ B)
    (hmv : ∀ z i, ¬ IsAxialTreeBond (z, i) → cellSupDist Y (enclosingCell z) ≤ q / 2 → ‖w' (transport Y Y' z) i - w z i‖ ≤ ε)
    (hnt' : ∀ (z : F.Site F.depth) (i : Fin 4), ¬ IsAxialTreeBond (z, i) → ¬ IsAxialTreeBond (transport Y Y' z, i))
    (hcold : IsSmallCurvature (41 / 64 * σ) (chartedField w V)) (h4 : 41 / 64 * σ + 4 * ε ≤ σc)
    (hB : B ≤ 1 / (64 * (L : ℝ))) (hε : 0 ≤ ε) (hB0 : 0 ≤ B)
    (u : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (hu : ∀ z i, ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ u z i = zeroOnTree w z i +
      θ • (spliced q Y Y' (zeroOnTree w) (zeroOnTree w') z i - zeroOnTree w z i)) :
    IsAdmissibleChartPoint L σc u V := by
  have hval : ∀ z i, ¬ IsAxialTreeBond (z, i) → (spliced q Y Y' (zeroOnTree w) (zeroOnTree w') z i = w z i ∧
      ¬ cellSupDist Y (enclosingCell z) ≤ q / 2) ∨ (spliced q Y Y' (zeroOnTree w) (zeroOnTree w') z i = w' (transport Y Y' z) i ∧
      cellSupDist Y (enclosingCell z) ≤ q / 2) := by
    intro z i hz
    by_cases hn : cellSupDist Y (enclosingCell z) ≤ q / 2
    · exact Or.inr ⟨by simp [spliced, hz, hn, zeroOnTree_of_not_tree (hnt' _ _ hz)], hn⟩
    · exact Or.inl ⟨by simp [spliced, hz, hn, zeroOnTree_of_not_tree hz], hn⟩
  have htree : ∀ z i, IsAxialTreeBond (z, i) → u z i = 0 := by
    intro z i hz
    obtain ⟨θ, -, -, e⟩ := hu z i
    rw [e]
    simp [spliced, hz, zeroOnTree_of_tree hz]
  have hclose : ∀ z i, ‖u z i - zeroOnTree w z i‖ ≤ ε := by
    intro z i
    by_cases hz : IsAxialTreeBond (z, i)
    · rw [htree z i hz, zeroOnTree_of_tree hz]; simpa using hε
    · obtain ⟨θ, h0, h1, e⟩ := hu z i
      rw [e, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg h0, zeroOnTree_of_not_tree hz]
      rcases hval z i hz with ⟨h2, -⟩ | ⟨h2, hn⟩
      · rw [h2]; simpa using hε
      · rw [h2]
        have := hmv z i hz hn
        have hn0 := norm_nonneg (w' (transport Y Y' z) i - w z i)
        calc θ * _ ≤ 1 * ‖w' (transport Y Y' z) i - w z i‖ := by gcongr
          _ ≤ ε := by linarith
  refine ⟨fun ⟨z, i⟩ _ => ?_, fun p hp => ?_⟩
  · by_cases hz : IsAxialTreeBond (z, i)
    · rw [htree z i hz, norm_zero]
      exact hB0.trans hB
    · obtain ⟨θ, h0, h1, e⟩ := hu z i
      have e2 : u z i = (1 - θ) • w z i + θ • spliced q Y Y' (zeroOnTree w) (zeroOnTree w') z i := by
        rw [e, zeroOnTree_of_not_tree hz]; module
      have hX : ‖spliced q Y Y' (zeroOnTree w) (zeroOnTree w') z i‖ ≤ B := by
        rcases hval z i hz with ⟨h2, -⟩ | ⟨h2, -⟩
        · rw [h2]; exact hwB z i hz
        · rw [h2]; exact hw'B z i hz
      refine le_trans ?_ hB
      rw [e2]
      calc ‖(1 - θ) • w z i + θ • spliced q Y Y' (zeroOnTree w) (zeroOnTree w') z i‖
          ≤ ‖(1 - θ) • w z i‖ + ‖θ • spliced q Y Y' (zeroOnTree w) (zeroOnTree w') z i‖ := norm_add_le _ _
        _ = (1 - θ) * ‖w z i‖ + θ * ‖spliced q Y Y' (zeroOnTree w) (zeroOnTree w') z i‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg h0]
        _ ≤ (1 - θ) * B + θ * B := by
            have := hwB z i hz
            have h1' : 0 ≤ 1 - θ := by linarith
            gcongr
        _ = B := by ring
  · have h1 := (hS.2 F u (zeroOnTree w) V ε hclose hε).2 p
    have h2 : chartedField (zeroOnTree w) V = chartedField w V :=
      chartedField_congr V fun z i hz => zeroOnTree_of_not_tree hz
    rw [h2] at h1
    have h3 := hcold p hp
    linarith
private theorem bondDeriv_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : F.GaugeField F.top → E)
    (V : F.GaugeField F.top) : bondDeriv G V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) = G V := by
  have h0 : expUnit (0 : imaginaryQuaternions) = 1 := by
    apply Subtype.ext
    simp [expUnit]
  have h1 : leftTranslate (ColdStepAtMirrorFrames.bondSpread (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) 0) V = V := by
    funext y i
    simp [leftTranslate, ColdStepAtMirrorFrames.bondSpread, h0]
  simp only [bondDeriv, iteratedFDeriv_zero_apply]
  rw [h1]
abbrev _root_.YangMills.SharedProofs.p27916 := @bondDeriv_zero
private theorem cellSupDist_add_le_of_withinRadius {Y : F.Cell} {h : Fin 4 → ℤ} {r : ℕ} (hh : WithinRadius r h)
    (hs : ∀ i, 2 * r + 2 < F.extent i) : cellSupDist Y (Y + siteOfCoords F.top h) ≤ r := by
  refine Finset.sup_le fun l _ => ?_
  have e0 : ((Y - (Y + siteOfCoords F.top h) : F.Cell) l) = -(((h l : ℤ) : ZMod (F.period F.top l))) := by
    simp [siteOfCoords]
  show (((Y - (Y + siteOfCoords F.top h) : F.Cell) l).valMinAbs).natAbs ≤ r
  rw [e0, ZMod.natAbs_valMinAbs_neg, valMinAbs_intCast_of_small (Or.inr ?_)]
  · have := hh l
    have e := Int.abs_eq_natAbs (h l)
    omega
  · rw [period_top]
    have := hh l
    have := hs l
    omega
private theorem compare_arith {x δ κ Cs A C₃ : ℝ} {L m q : ℕ} (hL : 2 ^ 40 ≤ L) (hq : 4 * m < q) (hq64 : 64 ≤ q)
    (hδ : 0 < δ) (hκ : κ ≤ δ / 2 ^ 14) (hκ0 : 0 < κ) (hx0 : 0 ≤ x)
    (hx : x * Real.exp (-(2 * δ * m)) ≤ 1) (hA : 0 ≤ A) (hC₃ : 0 ≤ C₃) (hCs : A + C₃ ≤ Cs) :
    x * (A * Real.exp (-(3 / 4 * δ * q)) +
        C₃ * Real.exp (-(δ * ((L : ℝ) * (((q / 2 : ℕ) : ℝ) / 2) - 2 * L - 1)))) ≤
      Cs * Real.exp (-(2 ^ 8 * κ * q)) := by
  have hqr : ((q : ℝ) - 1) / 2 ≤ ((q / 2 : ℕ) : ℝ) := by
    have h1 : q ≤ 2 * (q / 2) + 1 := by omega
    have h2 : (q : ℝ) ≤ 2 * ((q / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hLr : (2 : ℝ) ^ 40 ≤ L := by exact_mod_cast hL
  have hqr64 : (64 : ℝ) ≤ q := by exact_mod_cast hq64
  have hlong : 3 / 4 * (q : ℝ) ≤ (L : ℝ) * (((q / 2 : ℕ) : ℝ) / 2) - 2 * L - 1 := by
    have h1 : (L : ℝ) * (((q : ℝ) - 1) / 4) ≤ (L : ℝ) * (((q / 2 : ℕ) : ℝ) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have h2 : 0 ≤ ((L : ℝ) - 3) * ((q : ℝ) - 10) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have he2 : Real.exp (-(δ * ((L : ℝ) * (((q / 2 : ℕ) : ℝ) / 2) - 2 * L - 1))) ≤ Real.exp (-(3 / 4 * δ * q)) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hlong hδ.le
    linarith
  have hsplit : Real.exp (-(3 / 4 * δ * q)) ≤ Real.exp (-(2 * δ * m)) * Real.exp (-(2 ^ 8 * κ * q)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : 4 * (m : ℝ) ≤ q := by exact_mod_cast hq.le
    have h2 : 2 ^ 8 * κ ≤ δ / 4 := by
      have : κ * 2 ^ 14 ≤ δ := by rwa [le_div_iff₀ (by norm_num)] at hκ
      nlinarith
    have h3 := mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ q)
    have h4 := mul_le_mul_of_nonneg_left h1 hδ.le
    nlinarith
  set E := Real.exp (-(3 / 4 * δ * q)) with hE
  calc x * (A * E + C₃ * Real.exp (-(δ * ((L : ℝ) * (((q / 2 : ℕ) : ℝ) / 2) - 2 * L - 1))))
      ≤ x * (A * E + C₃ * E) := by gcongr
    _ = (A + C₃) * (x * E) := by ring
    _ ≤ Cs * (x * E) := by gcongr
    _ ≤ Cs * (x * (Real.exp (-(2 * δ * m)) * Real.exp (-(2 ^ 8 * κ * q)))) := by
        have hCs0 : 0 ≤ Cs := by linarith
        gcongr
    _ = Cs * ((x * Real.exp (-(2 * δ * m))) * Real.exp (-(2 ^ 8 * κ * q))) := by ring
    _ ≤ Cs * (1 * Real.exp (-(2 ^ 8 * κ * q))) := by
        have hCs0 : 0 ≤ Cs := by linarith
        gcongr
    _ = _ := by ring
private theorem radius_floor_bounds {Cs K δ x m : ℝ} (hCs : 0 < Cs) (hK : 0 < K) (hδ : 0 < δ) (hx1 : 1 ≤ x) (hm0 : 0 ≤ m)
    (hAm : (16 + 2 * K * 2 ^ 10 + 2 * Cs ^ 2 + 1) * x ^ 2 * Real.exp (-(3 * δ / 16 * m)) ≤ 1) :
    2 * K * Real.exp (-(δ * m)) ≤ 2⁻¹ ^ 10 ∧ x * Real.exp (-(2 * δ * m)) ≤ 1 ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ δ / 2 ^ 14 →
      2 * Cs ^ 2 * x * Real.exp (-(δ / 4 * m)) ≤ Real.exp (-(2 ^ 10 * κ * m)) := by
  set e₁ := Real.exp (-(3 * δ / 16 * m)) with he₁
  have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx1
  have hP1 : 0 < 2 * K * 2 ^ 10 := by positivity
  have hP2 : 0 < 2 * Cs ^ 2 := by positivity
  have hterm : ∀ B : ℝ, 0 ≤ B → B ≤ 16 + 2 * K * 2 ^ 10 + 2 * Cs ^ 2 + 1 → B * x ^ 2 * e₁ ≤ 1 := by
    intro B hB0 hB
    calc B * x ^ 2 * e₁ ≤ (16 + 2 * K * 2 ^ 10 + 2 * Cs ^ 2 + 1) * x ^ 2 * e₁ := by gcongr
      _ ≤ 1 := hAm
  have hone : ∀ B : ℝ, 0 ≤ B → B ≤ 16 + 2 * K * 2 ^ 10 + 2 * Cs ^ 2 + 1 → B * e₁ ≤ 1 := by
    intro B hB0 hB
    refine le_trans ?_ (hterm B hB0 hB)
    have : B * e₁ * 1 ≤ B * e₁ * x ^ 2 := by gcongr
    nlinarith
  refine ⟨?_, ?_, fun κ hκ0 hκ => ?_⟩
  · have h1 := hone (2 * K * 2 ^ 10) hP1.le (by linarith)
    have h2 : Real.exp (-(δ * m)) ≤ e₁ := by
      apply Real.exp_le_exp.2
      have : 3 * δ / 16 * m ≤ δ * m := mul_le_mul_of_nonneg_right (by linarith) hm0
      linarith
    have h3 : (2 : ℝ)⁻¹ ^ 10 = 1 / 2 ^ 10 := by norm_num
    rw [h3, le_div_iff₀ (by norm_num)]
    calc 2 * K * Real.exp (-(δ * m)) * 2 ^ 10 ≤ 2 * K * e₁ * 2 ^ 10 := by gcongr
      _ = 2 * K * 2 ^ 10 * e₁ := by ring
      _ ≤ 1 := h1
  · have h1 := hterm 1 zero_le_one (by linarith)
    have h2 : Real.exp (-(2 * δ * m)) ≤ e₁ := by
      apply Real.exp_le_exp.2
      have : 3 * δ / 16 * m ≤ 2 * δ * m := mul_le_mul_of_nonneg_right (by linarith) hm0
      linarith
    have hx3 : x ≤ x ^ 2 := by nlinarith
    calc x * Real.exp (-(2 * δ * m)) ≤ x ^ 2 * e₁ := by gcongr
      _ = 1 * x ^ 2 * e₁ := by ring
      _ ≤ 1 := h1
  · have h1 : Real.exp (-(δ / 4 * m)) = e₁ * Real.exp (-(δ / 16 * m)) := by
      rw [he₁, ← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-(δ / 16 * m)) ≤ Real.exp (-(2 ^ 10 * κ * m)) := by
      apply Real.exp_le_exp.2
      have h5 : 2 ^ 10 * κ ≤ δ / 16 := by
        have : κ * 2 ^ 14 ≤ δ := by rwa [le_div_iff₀ (by norm_num)] at hκ
        linarith
      have := mul_le_mul_of_nonneg_right h5 hm0
      linarith
    have h4 := hterm (2 * Cs ^ 2) hP2.le (by linarith)
    have hx3 : x ≤ x ^ 2 := by nlinarith
    calc 2 * Cs ^ 2 * x * Real.exp (-(δ / 4 * m))
        ≤ 2 * Cs ^ 2 * x ^ 2 * (e₁ * Real.exp (-(2 ^ 10 * κ * m))) := by
          rw [h1]; gcongr
      _ = (2 * Cs ^ 2 * x ^ 2 * e₁) * Real.exp (-(2 ^ 10 * κ * m)) := by ring
      _ ≤ 1 * Real.exp (-(2 ^ 10 * κ * m)) := by gcongr
      _ = _ := one_mul _
private theorem fineBondAt_not_tree {F' : BlockFrame} (hLL : F'.blockSide = F.blockSide) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (hs' : ∀ i, 2 ≤ F'.extent i) (Y : F.Cell) (Y' : F'.Cell) {h o : Fin 4 → ℤ} {i : Fin 4} (ho : o ∈ centredCube F.blockSide)
    (hnt : ¬ IsAxialTreeBond (fineBondAt Y h o i)) : ¬ IsAxialTreeBond (fineBondAt Y' h o i) := by
  have hL' : Odd F'.blockSide := hLL ▸ hL
  have ho' : o ∈ centredCube F'.blockSide := hLL ▸ ho
  have e1 := TopLevelSites.isAxialTreeBond_iff hL hs (Y + siteOfCoords F.top h) o ho i
  have e2 := TopLevelSites.isAxialTreeBond_iff hL' hs' (Y' + siteOfCoords F'.top h) o ho' i
  intro ht
  apply hnt
  have := e2.1 ht
  rw [hLL] at this
  exact e1.2 this
private theorem slopeLocal_of_frames {a : ℝ} {L : ℕ} {c : ColdChainParameters} {C σ κ x Cs C₂ C₃ W : ℝ} {t n₀ m : ℕ}
    (hB : BlocksCoverLowerLevel) (hS : ChartLipschitz.ChartedFieldLipschitz)
    (hc : c.Admissible a L) (hL : Odd L) (hL0 : 2 ^ 40 ≤ L) (hσ : 0 < σ) (hσs : σ ≤ c.s₀ / 2)
    (hCσ : C * σ ≤ 1 / (64 * (L : ℝ))) (hκ0 : 0 < κ) (hκ : κ ≤ c.δ₂ / 2 ^ 14) (hn64 : 64 ≤ n₀) (hx1 : 1 ≤ x)
    (hm16 : 16 ≤ m) (f1 : 2 * c.K * Real.exp (-(c.δ₂ * m)) ≤ 2⁻¹ ^ 10)
    (f2 : x * Real.exp (-(2 * c.δ₂ * m)) ≤ 1)
    (f3 : 2 * Cs ^ 2 * x * Real.exp (-(c.δ₂ / 4 * m)) ≤ Real.exp (-(2 ^ 10 * κ * m)))
    (hCs1 : 1 ≤ Cs) (hCs2 : C₂ * (2 * c.K * σ) * W + C₃ ≤ Cs) (hC₂ : 0 < C₂) (hC₃ : 0 < C₃) (hW0 : 0 ≤ W)
    (hMv : ∀ (F : BlockFrame) (w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top), IsBlockTorus L F →
        (∀ u : F.Site F.depth → Fin 4 → imaginaryQuaternions,
          (∀ z i, ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ u z i = w z i + θ • (w' z i - w z i)) →
          IsAdmissibleChartPoint L c.σA u V) →
        (∀ b, b ∉ chordBonds (finiteCells F) → w' b.1 b.2 = w b.1 b.2) →
        ∀ (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions), ‖e‖ = 1 →
          |chartedSlope a w' V b e - chartedSlope a w V b e| ≤
            ∑ b' ∈ chordBonds (finiteCells F),
              C₂ * Real.exp (-(c.δ₁ * cellSupDist (enclosingCell b.1) (enclosingCell b'.1))) * ‖w' b'.1 b'.2 - w b'.1 b'.2‖)
    (hTw : ∀ (F F' : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
        (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ), 1 ≤ r → IsBlockTorus L F → IsBlockTorus L F' →
        F'.depth = F.depth → IsAdmissibleChartPoint L c.s₀ w V → IsAdmissibleChartPoint L c.s₀ w' V' →
        AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
        (∀ (h o : Fin 4 → ℤ) (i : Fin 4), WithinRadius r h → o ∈ centredCube L →
          w (fineBondAt Y h o i).1 i = w' (fineBondAt Y' h o i).1 i) →
        ∀ (h o : Fin 4 → ℤ) (i : Fin 4) (e : imaginaryQuaternions), IsFineBondWithinRadius Y (r / 2) h o i → ‖e‖ = 1 →
          |chartedSlope a w V (fineBondAt Y h o i) e - chartedSlope a w' V' (fineBondAt Y' h o i) e| ≤
            C₃ * Real.exp (-(c.δ₂ * ((L : ℝ) * ((r : ℝ) / 2) - 2 * L - 1))))
    (hWs : ∀ (G : BlockFrame), G.blockSide = L → (∀ i, 2 ≤ G.extent i) → ∀ b : G.Site G.depth × Fin 4,
      ∑ b' ∈ chordBonds (finiteCells G),
        Real.exp (-((c.δ₁ - c.δ₂) * cellSupDist (enclosingCell b.1) (enclosingCell b'.1))) ≤ W)
    {F F' : BlockFrame} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ} {s : ℝ}
    (ht : IsCubicTopTorus L t n₀ F) (ht' : IsCubicTopTorus L t n₀ F')
    (hag : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hsz : ∀ b ∈ chordBonds (finiteCells F), ‖interpolatedFrame s a c.ρA m b V‖ ≤ C * σ)
    (hsz' : ∀ b ∈ chordBonds (finiteCells F'), ‖interpolatedFrame s a c.ρA m b V'‖ ≤ C * σ)
    (hcf : IsSmallCurvature (41 / 64 * σ) (chartedField (fun z i => interpolatedFrame s a c.ρA m (z, i) V) V))
    (hcf' : IsSmallCurvature (41 / 64 * σ) (chartedField (fun z i => interpolatedFrame s a c.ρA m (z, i) V') V'))
    (hloc : InterpolatedFrameLocal s a c.ρA c.δ₂ c.K Cs σ m V V' Y Y' r)
    (hst : InterpolatedSlopeSmall s a c.ρA c.δ₂ Cs (Cs * Real.exp (-(c.δ₂ / 4 * m))) x m V)
    (hst' : InterpolatedSlopeSmall s a c.ρA c.δ₂ Cs (Cs * Real.exp (-(c.δ₂ / 4 * m))) x m V') :
    InterpolatedSlopeLocal s a c.ρA κ Cs x m V V' Y Y' r := by
  obtain ⟨⟨hρ, hρ1, hs₀, hδ₂, hκ₂, hK, hC1, hKk⟩, -⟩ := hc.classical
  obtain ⟨hFL, hFt, nF, hnF, hnF0⟩ := ht
  obtain ⟨hFL', hFt', nF', hnF', hnF0'⟩ := ht'
  have hFtt : F'.depth = F.depth := hFt'.trans hFt.symm
  have hLL : F'.blockSide = F.blockSide := hFL'.trans hFL.symm
  have hLF : Odd F.blockSide := hFL ▸ hL
  have hLF' : Odd F'.blockSide := hFL' ▸ hL
  have hs64 : ∀ i, 64 ≤ F.extent i := fun i => by rw [hnF i]; omega
  have hs64' : ∀ i, 64 ≤ F'.extent i := fun i => by rw [hnF' i]; omega
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by have := hs64 i; omega
  have hs2' : ∀ i, 2 ≤ F'.extent i := fun i => by have := hs64' i; omega
  have hFc : IsBlockTorus L F := ⟨hFL, nF, by omega, hnF⟩
  have hFc' : IsBlockTorus L F' := ⟨hFL', nF', by omega, hnF'⟩
  have hch : ∀ z i, ¬ IsAxialTreeBond (z, i) → (z, i) ∈ chordBonds (finiteCells F) := fun z i hz =>
    mem_chordBonds_of_not_tree hB hLF (fun i => by have := hs2 i; omega) z i hz
  have hch' : ∀ z i, ¬ IsAxialTreeBond (z, i) → (z, i) ∈ chordBonds (finiteCells F') := fun z i hz =>
    mem_chordBonds_of_not_tree hB hLF' (fun i => by have := hs2' i; omega) z i hz
  intro h o i e hb he
  have hbc := hb.2.1
  have ho : o ∈ centredCube F.blockSide := hb.1
  have hbT : ¬ IsAxialTreeBond (fineBondAt Y h o i) := not_tree_of_mem_chordBonds hbc
  have hb'T : ¬ IsAxialTreeBond (fineBondAt Y' h o i) := fineBondAt_not_tree hLL hLF hs2 hs2' Y Y' ho hbT
  have hb'c : fineBondAt Y' h o i ∈ chordBonds (finiteCells F') := hch' _ _ hb'T
  by_cases hq : r ≤ 4 * m
  · have d1 := hst.deriv_decay _ hbc e he 0 Fin.elim0 Fin.elim0 (by omega) (fun l => l.elim0)
    have d2 := hst'.deriv_decay _ hb'c e he 0 Fin.elim0 Fin.elim0 (by omega) (fun l => l.elim0)
    rw [bondDeriv_zero] at d1 d2
    simp only [bondListDistance, Finset.univ_eq_empty, Finset.sup_empty, bot_eq_zero', Nat.cast_zero, mul_zero,
      neg_zero, Real.exp_zero, mul_one] at d1 d2
    have hE0 := Real.exp_pos (-(c.δ₂ / 4 * (m : ℝ)))
    have h1 : x * |interpolatedSlope s a c.ρA m (fineBondAt Y h o i) e V -
        interpolatedSlope s a c.ρA m (fineBondAt Y' h o i) e V'| ≤ 2 * Cs ^ 2 * x * Real.exp (-(c.δ₂ / 4 * m)) := by
      have h2 := abs_sub (interpolatedSlope s a c.ρA m (fineBondAt Y h o i) e V)
        (interpolatedSlope s a c.ρA m (fineBondAt Y' h o i) e V')
      have hx0 : 0 ≤ x := by linarith
      calc _ ≤ x * (Cs * (Cs * Real.exp (-(c.δ₂ / 4 * m))) + Cs * (Cs * Real.exp (-(c.δ₂ / 4 * m)))) := by
            gcongr
            exact h2.trans (add_le_add d1 d2)
        _ = _ := by ring
    have h3 : Real.exp (-(2 ^ 10 * κ * m)) ≤ Real.exp (-(2 ^ 8 * κ * r)) := by
      apply Real.exp_le_exp.2
      have h4 : (r : ℝ) ≤ 4 * m := by exact_mod_cast hq
      nlinarith
    have h5 := Real.exp_pos (-(2 ^ 8 * κ * (r : ℝ)))
    calc _ ≤ Real.exp (-(2 ^ 8 * κ * r)) := (h1.trans f3).trans h3
      _ = 1 * Real.exp (-(2 ^ 8 * κ * r)) := (one_mul _).symm
      _ ≤ _ := by gcongr
  · have hq' : 4 * m < r := by omega
    have hq64 : 64 ≤ r := by omega
    have hs : ∀ i, 2 * r + 2 < F.extent i := fun i => by
      rcases hag.1 i with h0 | h0
      · have := hs64 i; omega
      · exact h0
    have hs' : ∀ i, 2 * r + 2 < F'.extent i := fun i => by
      rcases hag.2.1 i with h0 | h0
      · have := hs64' i; omega
      · exact h0
    set w : F.Site F.depth → Fin 4 → imaginaryQuaternions := fun z i => interpolatedFrame s a c.ρA m (z, i) V with hw
    set w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions := fun z i => interpolatedFrame s a c.ρA m (z, i) V' with hw'
    have hnt' : ∀ (z : F.Site F.depth) (i : Fin 4), ¬ IsAxialTreeBond (z, i) → ¬ IsAxialTreeBond (transport Y Y' z, i) := by
      intro z i hz
      obtain ⟨ho', ez⟩ := site_eq_fineBondAt hLF hs2 Y z i
      have := fineBondAt_not_tree hLL hLF hs2 hs2' Y Y' ho' (ez ▸ hz)
      exact this
    have hmove : ∀ (z : F.Site F.depth) (i : Fin 4), (z, i) ∈ chordBonds (finiteCells F) →
        cellSupDist Y (enclosingCell z) ≤ r / 2 →
        ‖w' (transport Y Y' z) i - w z i‖ ≤ (2 * c.K * σ) * Real.exp (-(c.δ₂ * ((r : ℝ) - cellSupDist Y (enclosingCell z)))) := by
      intro z i hzc hn
      obtain ⟨ho', ez⟩ := site_eq_fineBondAt hLF hs2 Y z i
      have ed : (fineBondAt Y (relOffset Y (enclosingCell z)) (cellOffset z) i).1 = z :=
        (congrArg Prod.fst ez).symm
      have hbox : IsFineBondWithinRadius Y r (relOffset Y (enclosingCell z)) (cellOffset z) i := by
        refine ⟨ho', ez ▸ hzc, fun l => ?_, ?_, ?_⟩
        · have h1 := abs_relOffset_le Y (enclosingCell z) l
          have h2 : ((cellSupDist Y (enclosingCell z) : ℕ) : ℤ) ≤ (r : ℤ) := by
            have : cellSupDist Y (enclosingCell z) ≤ r := hn.trans (Nat.div_le_self _ _)
            exact_mod_cast this
          exact h1.trans h2
        · rw [ed]; exact hn.trans (Nat.div_le_self _ _)
        · rw [ed]
          have h1 := PatchLocality.cellSupDist_triangle Y (enclosingCell z) (enclosingCell (z + unitStep F.depth i))
          have h2 := cellSupDist_enclosingCell_add_unitStep_le hLF (fun i => by have := hs2 i; have := hs64 i; omega) z i
          omega
      have hm : (m : ℝ) < (r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y (relOffset Y (enclosingCell z)) (cellOffset z) i).1) := by
        rw [ed]
        have h1 : (cellSupDist Y (enclosingCell z) : ℝ) ≤ ((r / 2 : ℕ) : ℝ) := by exact_mod_cast hn
        have h2 : ((r / 2 : ℕ) : ℝ) ≤ (r : ℝ) / 2 := Nat.cast_div_le
        have h3 : 4 * (m : ℝ) < r := by exact_mod_cast hq'
        have h4 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
        linarith
      obtain ⟨f1', -, f3'⟩ := hloc.eq_far_inside (fun i => by have := hs i; omega) (fun i => by have := hs' i; omega)
        _ _ i hbox hm
      rw [ed] at f3'
      have e1 : w' (transport Y Y' z) i - w z i = -((1 - s) • (stepFrame true a c.ρA m (fineBondAt Y (relOffset Y (enclosingCell z)) (cellOffset z) i) V -
          stepFrame true a c.ρA m (fineBondAt Y' (relOffset Y (enclosingCell z)) (cellOffset z) i) V')) := by
        rw [← f1']
        simp only [hw, hw']
        rw [← ez]
        have e2 : (transport Y Y' z, i) = fineBondAt Y' (relOffset Y (enclosingCell z)) (cellOffset z) i := rfl
        rw [e2]
        abel
      rw [e1, norm_neg, norm_smul, Real.norm_of_nonneg (by linarith)]
      have hn0 := norm_nonneg (stepFrame true a c.ρA m (fineBondAt Y (relOffset Y (enclosingCell z)) (cellOffset z) i) V -
          stepFrame true a c.ρA m (fineBondAt Y' (relOffset Y (enclosingCell z)) (cellOffset z) i) V')
      calc (1 - s) * _ ≤ 1 * _ := by gcongr; linarith
        _ = _ := one_mul _
        _ ≤ _ := f3'
    have hε0 : (0 : ℝ) ≤ 2⁻¹ ^ 10 * σ := by positivity
    have hmv : ∀ z i, ¬ IsAxialTreeBond (z, i) → cellSupDist Y (enclosingCell z) ≤ r / 2 →
        ‖w' (transport Y Y' z) i - w z i‖ ≤ 2⁻¹ ^ 10 * σ := by
      intro z i hz hn
      refine (hmove z i (hch z i hz) hn).trans ?_
      have h1 : (cellSupDist Y (enclosingCell z) : ℝ) ≤ ((r / 2 : ℕ) : ℝ) := by exact_mod_cast hn
      have h2 : ((r / 2 : ℕ) : ℝ) ≤ (r : ℝ) / 2 := Nat.cast_div_le
      have h3 : 4 * (m : ℝ) < r := by exact_mod_cast hq'
      have h4 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      have h5 : Real.exp (-(c.δ₂ * ((r : ℝ) - cellSupDist Y (enclosingCell z)))) ≤ Real.exp (-(c.δ₂ * m)) := by
        apply Real.exp_le_exp.2
        have : (m : ℝ) ≤ (r : ℝ) - cellSupDist Y (enclosingCell z) := by linarith
        have := mul_le_mul_of_nonneg_left this hδ₂.le
        linarith
      calc (2 * c.K * σ) * Real.exp (-(c.δ₂ * ((r : ℝ) - cellSupDist Y (enclosingCell z))))
          ≤ (2 * c.K * σ) * Real.exp (-(c.δ₂ * m)) := by gcongr
        _ = (2 * c.K * Real.exp (-(c.δ₂ * m))) * σ := by ring
        _ ≤ 2⁻¹ ^ 10 * σ := by gcongr
    have hwB : ∀ z i, ¬ IsAxialTreeBond (z, i) → ‖w z i‖ ≤ C * σ := fun z i hz => hsz _ (hch z i hz)
    have hw'B : ∀ z i, ¬ IsAxialTreeBond (z, i) → ‖w' (transport Y Y' z) i‖ ≤ C * σ := fun z i hz =>
      hsz' _ (hch' _ i (hnt' z i hz))
    have hC0 : 0 ≤ C * σ := by
      have := norm_nonneg (interpolatedFrame s a c.ρA m (fineBondAt Y h o i) V)
      exact this.trans (hsz _ hbc)
    have hh10 : (2 : ℝ)⁻¹ ^ 10 = 1 / 1024 := by norm_num
    have hσA : σ ≤ c.σA := by
      have := hc.inequalities.2.2.1
      linarith
    have hpts : ∀ u : F.Site F.depth → Fin 4 → imaginaryQuaternions,
        (∀ z i, ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ u z i = zeroOnTree (fun z i => w z i) z i +
          θ • (spliced r Y Y' (zeroOnTree w) (zeroOnTree w') z i - zeroOnTree w z i)) →
        IsAdmissibleChartPoint L c.σA u V := fun u hu =>
      isAdmissibleChartPoint_spliced (σ := σ) (ε := 2⁻¹ ^ 10 * σ) (B := C * σ) hS hwB hw'B hmv hnt' hcf
        (by rw [hh10]; linarith) hCσ hε0 hC0 u hu
    have hXpt : IsAdmissibleChartPoint L c.s₀ (spliced r Y Y' (zeroOnTree w) (zeroOnTree w')) V :=
      isAdmissibleChartPoint_spliced (σ := σ) (ε := 2⁻¹ ^ 10 * σ) (B := C * σ) hS hwB hw'B hmv hnt' hcf
        (by rw [hh10]; linarith) hCσ hε0 hC0 _ (fun z i => ⟨1, zero_le_one, le_rfl, by simp⟩)
    have hUpt : IsAdmissibleChartPoint L c.s₀ (zeroOnTree w') V' := by
      refine ⟨fun ⟨z, i⟩ _ => ?_, fun p hp => ?_⟩
      · by_cases hz : IsAxialTreeBond (z, i)
        · rw [zeroOnTree_of_tree hz, norm_zero]
          exact hC0.trans hCσ
        · rw [zeroOnTree_of_not_tree hz]
          exact (hsz' _ (hch' z i hz)).trans hCσ
      · have h2 : chartedField (zeroOnTree w') V' = chartedField w' V' :=
          chartedField_congr V' fun z i hz => zeroOnTree_of_not_tree hz
        rw [h2]
        have := hcf' p hp
        linarith
    have heq : ∀ (h o : Fin 4 → ℤ) (i : Fin 4), WithinRadius (r / 2) h → o ∈ centredCube L →
        spliced r Y Y' (zeroOnTree w) (zeroOnTree w') (fineBondAt Y h o i).1 i = zeroOnTree w' (fineBondAt Y' h o i).1 i := by
      intro h o i hh ho
      have hoF : o ∈ centredCube F.blockSide := hFL ▸ ho
      by_cases hz : IsAxialTreeBond ((fineBondAt Y h o i).1, i)
      · have hz' : IsAxialTreeBond ((fineBondAt Y' h o i).1, i) := by
          by_contra hc'
          exact fineBondAt_not_tree hLL.symm hLF' hs2' hs2 Y' Y (hLL ▸ hoF) hc' hz
        rw [zeroOnTree_of_tree hz']
        simp [spliced, hz]
      · have hbox : ∀ l, 2 * |h l| < F.extent l := fun l => by
          have h1 := hh l
          have h2 := hs l
          omega
        have hcell : enclosingCell (fineBondAt Y h o i).1 = Y + siteOfCoords F.top h :=
          TopLevelSites.enclosingCell_centre_add hLF hs2 _ o hoF
        have hn : cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) ≤ r / 2 := by
          rw [hcell]
          exact cellSupDist_add_le_of_withinRadius hh (fun l => by have := hs l; omega)
        have := transport_fineBondAt hLF hs2 Y Y' hoF hbox i
        simp only [spliced, hz, hn, if_false, if_true, this]
    have hbound := chartedSlope_compare_far (L := L) (a := a) (δ := c.δ₂) (δ₁ := c.δ₁) (C₂ := C₂) (C₃ := C₃)
      (E := 2 * c.K * σ) (W := W) (σc := c.σA) (V := V) (V' := V') (Y := Y) (Y' := Y') (q := r) (w := w) (w' := w')
      hB hFL hL hs hq64 hδ₂ hC₂.le (by positivity)
      (fun u₀ u₁ h1 h2 b e he => hMv F u₀ u₁ V hFc h1 h2 b e he) hpts
      (fun h o i e hb he => hTw F F' _ _ V V' Y Y' (r / 2) (by omega) hFc hFc' hFtt hXpt hUpt
        (agreeOnBall_mono hag (Nat.div_le_self _ _)) heq h o i e hb he)
      hmove hnt' (hWs F hFL hs2) h o i e hb he hb'T
    have hx0 : 0 ≤ x := by linarith
    have hA0 : 0 ≤ C₂ * (2 * c.K * σ) * W := by positivity
    have := compare_arith (x := x) (δ := c.δ₂) (κ := κ) (Cs := Cs) (A := C₂ * (2 * c.K * σ) * W) (C₃ := C₃)
      (L := L) (m := m) (q := r) hL0 hq' hq64 hδ₂ hκ hκ0 hx0 f2 hA0 hC₃.le hCs2
    refine le_trans ?_ this
    gcongr
    exact hbound
theorem interpolatedSlopeLocalOnTwoTori_holds
    (hStay : interpolatedFramesControlled) (hOne : interpolatedSlopeSmallOnTorus)
    (hMv : ChartedSlopeKernelBound) (hTw : ChartedSlopeComparison)
    (hSum : CellCounting.ExpDecaySumBounded) (hB : BlocksCoverLowerLevel)
    (hS : ChartLipschitz.ChartedFieldLipschitz) (hF : Estimates.frameRadiusGrowthStatement)
    (hJ : EventuallyInParametersCombines) :
    interpolatedSlopeLocalOnTwoTori := by
  obtain ⟨hJ1, hJ2⟩ := hJ
  have hR : EventuallyInParameters (fun T => ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFramesControlledAt T t x →
      (∀ (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ), IsCubicTopTorus T.L t T.n₀ F →
        IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
        InterpolatedSlopeSmall s T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct (frameGapBound T (frameRadius x)) x
          (frameRadius x) V) →
      ∀ (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) (s : ℝ),
        IsCubicTopTorus T.L t T.n₀ F → IsCubicTopTorus T.L t T.n₀ F' → IsSmallCurvature (5 / 4 * T.σ) V →
        IsSmallCurvature (5 / 4 * T.σ) V' → AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r → 0 ≤ s →
        s ≤ 1 → InterpolatedSlopeLocal s T.a T.chainParams.ρA T.κ T.Ct x (frameRadius x) V V' Y Y' r) := by
    intro a ha
    refine ⟨2 ^ 40, fun L hL hL0 c hc => ?_⟩
    obtain ⟨C₂, hC₂, hMv'⟩ := hMv a L c ha hL hL0 hc
    obtain ⟨C₃, hC₃, hTw'⟩ := hTw a L c ha hL hL0 hc
    obtain ⟨⟨hρ, hρ1, hs₀, hδ₂, hκ₂, hK, hC1, hKk⟩, -⟩ := hc.classical
    have hδ₁ : c.δ₂ < c.δ₁ := by
      have := hc.inequalities.2.1
      nlinarith
    obtain ⟨W₀, hW0, hWs⟩ := hSum ((centredCube L).card * 4) (c.δ₁ - c.δ₂) (by linarith)
    have hWs' : ∀ G : BlockFrame, G.blockSide = L → (∀ i, 2 ≤ G.extent i) → ∀ b : G.Site G.depth × Fin 4,
        ∑ b' ∈ chordBonds (finiteCells G),
          Real.exp (-((c.δ₁ - c.δ₂) * cellSupDist (enclosingCell b.1) (enclosingCell b'.1))) ≤ W₀ := by
      intro G hG hs b
      have hLG : Odd G.blockSide := hG ▸ hL
      have h1 := hWs G ↥(chordBonds (finiteCells G)) (fun b => enclosingCell b.1.1)
        (fun z => by
          have := card_fiber_le hLG hs z
          rw [hG] at this
          convert this) (enclosingCell b.1)
      rw [← Finset.sum_coe_sort]
      refine le_trans (le_of_eq ?_) h1
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [PatchLocality.cellSupDist_comm]
    refine ⟨max (max 1 1) (C₂ * (2 * c.K * (c.s₀ / 2)) * W₀ + C₃ + 1), fun Ct hCt =>
      ⟨c.δ₂ / 2 ^ 14, by positivity, fun κ hκ0 hκ => ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun nss _ =>
      ⟨min (c.s₀ / 2) (1 / (64 * L * Ct)), ?_, fun σ hσ hσle p hp => ⟨0, fun Cs' _ E hE =>
      ⟨64, fun n₀ hn₀ => ⟨0, fun CE _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩
    · have h1 : 1 ≤ Ct := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCt
      have hLpos : (0 : ℝ) < L := by
        have : 0 < L := by have := hL.pos; omega
        exact_mod_cast this
      exact lt_min (by positivity) (by positivity)
    · have hCt1 : 1 ≤ Ct := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCt
      have hCt0 : 0 < Ct := by linarith
      have hCt2 : C₂ * (2 * c.K * (c.s₀ / 2)) * W₀ + C₃ ≤ Ct := by
        have := le_trans (le_max_right _ _) hCt
        linarith
      have hσs : σ ≤ c.s₀ / 2 := hσle.trans (min_le_left _ _)
      have hCs2 : C₂ * (2 * c.K * σ) * W₀ + C₃ ≤ Ct := by
        refine le_trans ?_ hCt2
        gcongr
      have hLpos : (0 : ℝ) < L := by
        have : 0 < L := by have := hL.pos; omega
        exact_mod_cast this
      have hCσ : Ct * σ ≤ 1 / (64 * (L : ℝ)) := by
        have h1 : σ ≤ 1 / (64 * L * Ct) := hσle.trans (min_le_right _ _)
        calc Ct * σ ≤ Ct * (1 / (64 * L * Ct)) := by gcongr
          _ = _ := by field_simp
      obtain ⟨y, hy1, hy⟩ := hF (16 + 2 * c.K * 2 ^ 10 + 2 * Ct ^ 2 + 1) (3 * c.δ₂ / 16) (by positivity)
        (by positivity)
      refine ⟨y, fun y₁ hy₁ t x hx hnear hone F F' V V' Y Y' r s ht ht' hcold hcold' hag hs0 hs1 => ?_⟩
      have hx' : y₁ ≤ x := hx
      have hyx : y ≤ x := hy₁.trans hx'
      have hx1 : 1 ≤ x := hy1.trans hyx
      obtain ⟨hAm, hmA⟩ := hy x hyx
      have hm0 : (0 : ℝ) ≤ (frameRadius x : ℝ) := Nat.cast_nonneg _
      obtain ⟨f1, f2, f3⟩ := radius_floor_bounds hCt0 hK hδ₂ hx1 hm0 hAm
      have hm16 : 16 ≤ frameRadius x := by
        have h0 : 0 ≤ 2 * c.K * 2 ^ 10 + 2 * Ct ^ 2 + 1 := by positivity
        have h1 : (16 : ℝ) ≤ (frameRadius x : ℝ) := by linarith
        exact_mod_cast h1
      obtain ⟨hnr, hsm⟩ := hnear.single F V s ht hcold hs0 hs1
      obtain ⟨hnr', hsm'⟩ := hnear.single F' V' s ht' hcold' hs0 hs1
      have hfield : ∀ (G : BlockFrame) (U : G.GaugeField G.top), interpolatedField s a c.ρA (frameRadius x) U 0 =
          chartedField (fun z i => interpolatedFrame s a c.ρA (frameRadius x) (z, i) U) U := by
        intro G U
        unfold interpolatedField
        congr 1
        funext z i
        have h0 : toImaginary (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by
          apply Subtype.ext
          ext <;> simp [toImaginary]
        have h1 : stepCoordinates (0 : StepVariable (finiteCells G)) z i = 0 := by
          unfold stepCoordinates
          split_ifs with hz
          · exact h0
          · rfl
        simp [interpolatedCoords, h1]
      have hcf := hsm.small_curvature
      have hcf' := hsm'.small_curvature
      rw [hfield] at hcf hcf'
      exact slopeLocal_of_frames (C := Ct) (Cs := Ct) (C₂ := C₂) (C₃ := C₃) (W := W₀) (κ := κ) (n₀ := n₀) (t := t)
        hB hS hc hL hL0 hσ hσs hCσ hκ0 hκ hn₀ hx1 hm16 f1 f2 (f3 κ hκ0 hκ) hCt1 hCs2 hC₂ hC₃ hW0
        (fun G w w' U => hMv' G w w' U) (fun G G' w w' U U' Y Y' r h1 h2 h3 h4 h5 h6 h7 h8 =>
          hTw' G G' w w' U U' Y Y' r h1 h2 h3 h4 h5 h6 h7 fun h o i hh ho _ => h8 h o i hh ho) hWs'
        ht ht' hag hs0 hs1 hsm.norm_le hsm'.norm_le hcf hcf' (hnear.pair F F' V V' Y Y' r s ht ht' hcold hcold' hag hs0 hs1)
        (hone F V s ht hcold hs0 hs1) (hone F' V' s ht' hcold' hs0 hs1)
  refine hJ2 _ _ ?_ (hJ1 _ _ (hJ1 _ _ hStay hOne) hR)
  intro T _ h t x hx
  exact h.2 t x hx (h.1.1 t x hx) (h.1.2 t x hx)
end SummableBoundsOfTheFlow
end YangMills.Construction
end
