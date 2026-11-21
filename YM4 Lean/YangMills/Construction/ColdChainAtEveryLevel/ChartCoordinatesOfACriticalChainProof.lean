import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.ColdChainAtEveryLevel.ChartCoordinatesOfACriticalChain
import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTop
import YangMills.Construction.ColdChainAtEveryLevel.CriticalValueIsTheLeastAction
import YangMills.Construction.ColdChainAtEveryLevel.LeastValuesOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.OneLeastFieldOfAColdTop
import YangMills.Construction.ColdChainAtEveryLevel.SharesOfTheCellsAtASite
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
open LatticeFractionalIntegration
namespace ChartRepresentation
open LocalPartition
variable {F : BlockFrame} {S : Finset F.Cell}
theorem unitLog_expUnit (u : imaginaryQuaternions) (hu : ‖u‖ ≤ 1) : unitLog (expUnit u) = u := by
  have hre : (u : ℍ[ℝ]).re = 0 := u.2
  set r : ℝ := ‖(u : ℍ[ℝ])‖ with hr
  have hr1 : r ≤ 1 := hu
  have hr0 : 0 ≤ r := norm_nonneg _
  have hexp : ((expUnit u : UnitQuaternion) : ℍ[ℝ]) = ((Real.cos r : ℝ) : ℍ[ℝ]) + (Real.sin r / r) • (u : ℍ[ℝ]) :=
    Quaternion.exp_of_re_eq_zero _ hre
  have hpu : pureComponent (u : ℍ[ℝ]) = u := by
    have := re_add_pureComponent (u : ℍ[ℝ])
    rw [hre] at this
    simpa using this
  have hp : pureComponent ((expUnit u : UnitQuaternion) : ℍ[ℝ]) = (Real.sin r / r) • (u : ℍ[ℝ]) := by
    rw [hexp, pureComponent_add, pureComponent_coe, zero_add, pureComponent_smul, hpu]
  by_cases h0 : r = 0
  · have hu0 : (u : ℍ[ℝ]) = 0 := norm_eq_zero.1 h0
    apply Subtype.ext
    simp only [unitLog, hp, hu0, smul_zero, norm_zero, div_zero, zero_smul]
    rfl
  · have hpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm h0)
    have hs : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [Real.pi_gt_three])
    have hn : ‖pureComponent ((expUnit u : UnitQuaternion) : ℍ[ℝ])‖ = Real.sin r := by
      rw [hp, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ← hr]
      field_simp
    apply Subtype.ext
    show (Real.arcsin ‖pureComponent ((expUnit u : UnitQuaternion) : ℍ[ℝ])‖ /
      ‖pureComponent ((expUnit u : UnitQuaternion) : ℍ[ℝ])‖) •
      pureComponent ((expUnit u : UnitQuaternion) : ℍ[ℝ]) = (u : ℍ[ℝ])
    rw [hn, Real.arcsin_sin (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]), hp, smul_smul]
    have : r / Real.sin r * (Real.sin r / r) = 1 := by
      field_simp
    rw [this, one_smul]
theorem valMinAbs_period_depth (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (i : Fin 4) {A : ℤ}
    (hA : 2 * |A| < (F.blockSide : ℤ)) : ((A : ZMod (F.period F.depth i))).valMinAbs = A := by
  apply valMinAbs_intCast_of_small
  have hp : F.period F.depth i = F.extent i * F.blockSide := by
    simp [BlockFrame.period, BlockFrame.top]
  rcases hamb with h | h
  · left
    rw [hp, h i, zero_mul]
  · right
    rw [hp]
    push_cast
    have h1 : (64 : ℤ) ≤ F.extent i := by exact_mod_cast h i
    nlinarith
def siteInBlock (y : F.Cell) (h : Lattice4) : F.Site F.depth := cellCentre F.depth y + siteOfCoords F.depth h
theorem top_sub_depth : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem enclosingCell_siteInBlock (hodd : Odd F.blockSide) (y : F.Cell) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) : enclosingCell (siteInBlock y h) = y := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.enclosingCell_blockPoint <;> assumption
theorem two_mul_abs_lt_of_mem_centredCube {L : ℕ} (hodd : Odd L) {h : Lattice4} (hh : h ∈ centredCube L) (i : Fin 4) :
    2 * |h i| < (L : ℤ) := by
  have h1 := abs_le.2 (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hh i))
  omega
theorem cellOffset_siteInBlock (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (y : F.Cell) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) (i : Fin 4) : cellOffset (siteInBlock y h) i = h i := by
  unfold cellOffset
  rw [enclosingCell_siteInBlock hodd y hh]
  have : (siteInBlock y h - cellCentre F.depth y) i = ((h i : ℤ) : ZMod (F.period F.depth i)) := by
    simp [siteInBlock, siteOfCoords]
  rw [this]
  exact valMinAbs_period_depth hamb hodd i (two_mul_abs_lt_of_mem_centredCube hodd hh i)
theorem siteInBlock_mem_sitesOfCells {y : F.Cell} (hy : y ∈ S) {h : Lattice4} (hh : h ∈ centredCube F.blockSide) :
    siteInBlock y h ∈ sitesOfCells S F.depth := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.blockPoint_mem <;> assumption
theorem gauge_eq_along_treeBond (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {V : F.GaugeField F.top}
    {u₁ u₀ : F.Site F.depth → Fin 4 → imaginaryQuaternions} {γ : F.Site F.depth → UnitQuaternion}
    (hs : AgreeOnBonds S F.depth (chartedField u₁ V) (gaugeTransform γ (chartedField u₀ V))) {y : F.Cell} (hy : y ∈ S)
    {h : Lattice4} {i : Fin 4} (hh : h ∈ centredCube F.blockSide) (hh' : h + basisVector i ∈ centredCube F.blockSide)
    (hl : ∀ l, i < l → h l = 0) : γ (siteInBlock y h) = γ (siteInBlock y (h + basisVector i)) := by
  classical
  have hnext : siteInBlock y h + unitStep F.depth i = siteInBlock y (h + basisVector i) := by
    rw [unitStep_eq]
    simp only [siteInBlock, siteOfCoords_add, add_assoc]
  have hb : (siteInBlock y h, i) ∈ innerBonds S F.depth := by
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨siteInBlock_mem_sitesOfCells hy hh, by rw [hnext]; exact siteInBlock_mem_sitesOfCells hy hh'⟩
  have hcross : ¬ IsCrossingBond (siteInBlock y h, i) := by
    unfold IsCrossingBond
    simp only [not_not]
    rw [hnext, enclosingCell_siteInBlock hodd y hh, enclosingCell_siteInBlock hodd y hh']
  have htree : IsAxialTreeBond (siteInBlock y h, i) :=
    ⟨hcross, fun l hl' => by
      simp only
      rw [cellOffset_siteInBlock hamb hodd y hh]
      exact hl l hl'⟩
  have h1 := hs _ hb
  simp only [chartedField, gaugeTransform, if_neg hcross, if_pos htree] at h1
  rw [hnext] at h1
  simp only [mul_one, one_mul] at h1
  exact (mul_inv_eq_one.1 h1.symm)
theorem sub_basisVector_mem_centredCube {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) {i : Fin 4} (hne : 0 < h i) :
    h - basisVector i ∈ centredCube L := by
  refine Fintype.mem_piFinset.2 fun l => ?_
  have h1 := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hh l)
  rw [Finset.mem_Icc]
  by_cases e : l = i
  · subst e
    simp only [Pi.sub_apply, basisVector, Pi.single_eq_same]
    omega
  · simp only [Pi.sub_apply, basisVector, Pi.single_eq_of_ne e]
    omega
theorem add_basisVector_mem_centredCube {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) {i : Fin 4} (hne : h i < 0) :
    h + basisVector i ∈ centredCube L := by
  refine Fintype.mem_piFinset.2 fun l => ?_
  have h1 := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hh l)
  rw [Finset.mem_Icc]
  by_cases e : l = i
  · subst e
    simp only [Pi.add_apply, basisVector, Pi.single_eq_same]
    omega
  · simp only [Pi.add_apply, basisVector, Pi.single_eq_of_ne e]
    omega
theorem gauge_eq_one_on_block (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {V : F.GaugeField F.top}
    {u₁ u₀ : F.Site F.depth → Fin 4 → imaginaryQuaternions} {γ : F.Site F.depth → UnitQuaternion}
    (hs : AgreeOnBonds S F.depth (chartedField u₁ V) (gaugeTransform γ (chartedField u₀ V)))
    (hc : ∀ z, γ (cellCentre F.depth z) = 1) {y : F.Cell} (hy : y ∈ S) :
    ∀ n : ℕ, n ≤ 4 → ∀ h ∈ centredCube F.blockSide, (∀ l : Fin 4, n ≤ l.val → h l = 0) →
      γ (siteInBlock y h) = 1 := by
  intro n
  induction n with
  | zero =>
    intro _ h _ h0
    have : h = 0 := funext fun l => h0 l (Nat.zero_le _)
    subst this
    simp only [siteInBlock, siteOfCoords_zero, add_zero]
    exact hc y
  | succ n ih =>
    intro hn h hh h0
    have hn4 : n < 4 := hn
    set i : Fin 4 := ⟨n, hn4⟩ with hi
    have hgt : ∀ (g : Lattice4), (∀ l : Fin 4, n + 1 ≤ l.val → g l = 0) → ∀ l, i < l → g l = 0 := by
      intro g hg l hl
      exact hg l hl
    have inner : ∀ (k : ℕ) (g : Lattice4), g ∈ centredCube F.blockSide → (∀ l : Fin 4, n + 1 ≤ l.val → g l = 0) →
        (g i).natAbs = k → γ (siteInBlock y g) = 1 := by
      intro k
      induction k with
      | zero =>
        intro g hg g0 hk
        refine ih (by omega) g hg fun l hl => ?_
        by_cases e : n = l.val
        · have : l = i := Fin.ext e.symm
          rw [this]
          exact Int.natAbs_eq_zero.1 hk
        · exact g0 l (by omega)
      | succ k ihk =>
        intro g hg g0 hk
        rcases lt_or_gt_of_ne (fun h' : g i = 0 => by rw [h'] at hk; simp at hk : g i ≠ 0) with hneg | hpos
        · have hg' := add_basisVector_mem_centredCube hg hneg
          have e1 := gauge_eq_along_treeBond hamb hodd hs hy hg hg' (hgt g g0)
          rw [e1]
          refine ihk _ hg' (fun l hl => ?_) ?_
          · have : l ≠ i := fun e => by
              rw [e] at hl
              simp [hi] at hl
            simp only [Pi.add_apply, basisVector, Pi.single_eq_of_ne this, add_zero]
            exact g0 l hl
          · simp only [Pi.add_apply, basisVector, Pi.single_eq_same]
            omega
        · have hg' := sub_basisVector_mem_centredCube hg hpos
          have e0 : g - basisVector i + basisVector i = g := by simp
          have e1 := gauge_eq_along_treeBond hamb hodd hs hy hg' (by rw [e0]; exact hg)
            (hgt _ fun l hl => by
              have : l ≠ i := fun e => by
                rw [e] at hl
                simp [hi] at hl
              simp only [Pi.sub_apply, basisVector, Pi.single_eq_of_ne this, sub_zero]
              exact g0 l hl)
          rw [e0] at e1
          rw [← e1]
          refine ihk _ hg' (fun l hl => ?_) ?_
          · have : l ≠ i := fun e => by
              rw [e] at hl
              simp [hi] at hl
            simp only [Pi.sub_apply, basisVector, Pi.single_eq_of_ne this, sub_zero]
            exact g0 l hl
          · simp only [Pi.sub_apply, basisVector, Pi.single_eq_same]
            omega
    exact inner _ h hh h0 rfl
theorem gauge_eq_one (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {V : F.GaugeField F.top}
    {u₁ u₀ : F.Site F.depth → Fin 4 → imaginaryQuaternions} {γ : F.Site F.depth → UnitQuaternion}
    (hs : AgreeOnBonds S F.depth (chartedField u₁ V) (gaugeTransform γ (chartedField u₀ V)))
    (hc : ∀ z, γ (cellCentre F.depth z) = 1) {x : F.Site F.depth} (hx : x ∈ sitesOfCells S F.depth) : γ x = 1 := by
  obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
  have hh' : h ∈ centredCube F.blockSide := by
    rw [top_sub_depth, pow_one] at hh
    exact hh
  exact gauge_eq_one_on_block hamb hodd hs hc hy 4 le_rfl h hh' fun l hl => absurd l.isLt (by omega)
theorem minimizingChart_unique (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {a N s : ℝ}
    {V : F.GaugeField F.top} (hone : HasColdMinimizer a 1 N s S V) {ρ : ℝ} (hρ : ρ ≤ 1)
    {u₁ u₂ : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (h₁ : IsMinimizingChart a S V ρ u₁) (h₂ : IsMinimizingChart a S V ρ u₂) :
    ∀ b ∈ chordBonds S, u₁ b.1 b.2 = u₂ b.1 b.2 := by
  classical
  obtain ⟨u₀, hu₀, -, huniq⟩ := hone
  have key : ∀ u, IsMinimizingChart a S V ρ u → ∀ b ∈ chordBonds S, u b.1 b.2 = u₀ b.1 b.2 := by
    intro u hu b hb
    obtain ⟨γ, hc, hs⟩ := huniq (chartedField u V) hu.2.2
    have hbs : b ∈ innerBonds S F.depth := (Finset.mem_filter.1 hb).1
    have hnt : ¬ IsAxialTreeBond b := (Finset.mem_filter.1 hb).2
    have h1 := hs b hbs
    have x1 : b.1 ∈ sitesOfCells S F.depth := (Finset.mem_product.1 (Finset.mem_filter.1 hbs).1).1
    have x2 : b.1 + unitStep F.depth b.2 ∈ sitesOfCells S F.depth := (Finset.mem_filter.1 hbs).2
    simp only [gaugeTransform, gauge_eq_one hamb hodd hs hc x1, gauge_eq_one hamb hodd hs hc x2, one_mul, inv_one,
      mul_one] at h1
    have hexp : expUnit (u b.1 b.2) = expUnit (u₀ b.1 b.2) := by
      simp only [chartedField] at h1
      by_cases hcr : IsCrossingBond (b.1, b.2)
      · rw [if_pos hcr, if_pos hcr] at h1
        exact mul_right_cancel h1
      · have hnt' : ¬ IsAxialTreeBond (b.1, b.2) := hnt
        rw [if_neg hcr, if_neg hcr, if_neg hnt', if_neg hnt'] at h1
        exact h1
    have n1 : ‖u b.1 b.2‖ ≤ 1 := (hu.2.1 b hb).trans hρ
    have n0 : ‖u₀ b.1 b.2‖ ≤ 1 := (hu₀.2.1 b hb).trans (min_le_left _ _)
    rw [← unitLog_expUnit _ n1, ← unitLog_expUnit _ n0, hexp]
  intro b hb
  rw [key u₁ h₁ b hb, key u₂ h₂ b hb]
end ChartRepresentation
theorem minimizerEqCriticalChainChart (hCh : criticalChainChartOverTopStatement)
    (hOne : uniqueMinimizerStatement) (hVal : criticalValueEqMinimalActionStatement)
    (hLV : minimalChainExistenceStatement) : minimizerEqCriticalChainChartStatement := by
  classical
  intro a θ δ Ca ha hθ hθ8 hd hd8 hCa
  obtain ⟨L₁, hC'⟩ := hCh a θ δ Ca ha hθ hθ8 hd hd8 hCa
  obtain ⟨L₂, hO'⟩ := hOne a ha
  obtain ⟨L₃, hV'⟩ := hVal a θ δ Ca ha hθ hθ8 hd hd8 hCa
  refine ⟨max L₁ (max L₂ L₃), fun L hL hge C₁ ρ hC₁ hρ hρ1 => ?_⟩
  have g1 : L₁ ≤ L := le_of_max_le_left hge
  have g2 : L₂ ≤ L := le_of_max_le_left (le_of_max_le_right hge)
  have g3 : L₃ ≤ L := le_of_max_le_right (le_of_max_le_right hge)
  obtain ⟨σ1, N0, hσ1, hN0, hc⟩ := hC' L hL g1 C₁ hC₁
  obtain ⟨σ2, N1, hσ2, hN1, ho⟩ := hO' L hL g2 1 one_pos
  obtain ⟨σ3, hσ3, hv⟩ := hV' L hL g3 C₁ hC₁
  refine ⟨min σ1 (min σ2 (min σ3 (ρ / N0))), N0, lt_min hσ1 (lt_min hσ2 (lt_min hσ3 (by positivity))), hN0, ?_⟩
  intro F m S hFL hamb hm hreg s V v hs hsσ hcold hvs hcold' U hU
  have e1 : s ≤ σ1 := hsσ.trans (min_le_left _ _)
  have e2 : s ≤ σ2 := hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e3 : s ≤ σ3 := hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have e4 : s ≤ ρ / N0 := hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hodd : Odd F.blockSide := hFL ▸ hL
  have hNs : N0 * s ≤ ρ := by
    rw [le_div_iff₀ hN0] at e4
    linarith
  obtain ⟨u, hu0, hub, hue, hen⟩ := hc F m S hFL hamb hm hreg s V (rotatedField v V) hs e1 hcold U hU
  have hleast := (hv F m S hFL hamb hm hreg s V v hs e3 hcold hvs U hU).1
  have hlc : IsMinimizingChart a S (rotatedField v V) ρ u := by
    refine ⟨hu0, fun b hb' => (hub b hb').trans hNs, fun W' => ?_⟩
    obtain ⟨W0, hW0, hmin⟩ := (hLV F a S ha.le).2.2.1 F.depth (rotatedField v V)
    have h1 : blockEnergy a S F.depth (chartedField u (rotatedField v V)) (rotatedField v V) ≤
        blockEnergy a S F.depth W0 (rotatedField v V) := by
      rw [hW0]
      exact hen.trans (le_of_eq hleast.symm)
    exact h1.trans (hmin W')
  have hone := ho F m S hFL hamb hm hreg s (rotatedField v V) hs e2 hcold'
  have hex : ∃ u', IsMinimizingChart a S (rotatedField v V) ρ u' := ⟨u, hlc⟩
  have hch : ∀ b ∈ chordBonds S, minimizingBondCoordinate a ρ S b (rotatedField v V) = u b.1 b.2 := by
    intro b hb
    unfold minimizingBondCoordinate minimizingCoordinates
    rw [dif_pos hex]
    exact ChartRepresentation.minimizingChart_unique hamb hodd hone hρ1 hex.choose_spec hlc b hb
  refine ⟨fun b hb => ⟨?_, by rw [hch b hb]; exact hub b hb⟩, fun b hb => ?_⟩
  · rw [hch b hb]
    unfold bondChartCoord
    rw [← hue b hb]
    exact (ChartRepresentation.unitLog_expUnit _ ((hub b hb).trans (hNs.trans hρ1))).symm
  · unfold minimizingBondCoordinate minimizingCoordinates
    rw [dif_pos hex]
    exact hex.choose_spec.1 b hb
end YangMills.Construction.BlockAverages
end
