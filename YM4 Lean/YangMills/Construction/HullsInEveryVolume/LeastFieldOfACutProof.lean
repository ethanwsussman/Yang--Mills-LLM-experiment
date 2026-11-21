import YangMills.Construction.ClusterExpansionOfAStep.EnergyNearAClassProof
import YangMills.Construction.HullsInEveryVolume.LeastFieldOfACut
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.HullsInEveryVolume
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.StepCosts YangMills.Construction.StepMarks YangMills.Construction.ClusterExpansionOfAStep YangMills.Construction.LumpContours YangMills.Construction.TopLevelSites
section Group
private theorem expUnit_zero_eq_one : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem minimalLog_expUnit_of_norm_lt {w : imaginaryQuaternions} (hw : ‖(w : ℍ[ℝ])‖ < Real.pi) :
    minimalLog (expUnit w) = w := by apply _root_.YangMills.Construction.GaugeFixing.minimalLog_expUnit <;> assumption
end Group
section Frames
variable {F : BlockFrame}
private theorem minimizingCoordinates_of_not_mem {a ρ : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top}
    {b : F.Site F.depth × Fin 4} (hb : b ∉ chordBonds S) : minimizingCoordinates a S V ρ b.1 b.2 = 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.minimizingCoordinates_of_not_mem <;> assumption
private theorem not_mem_chordBonds_of_axialTree {S : Finset F.Cell} {b : F.Site F.depth × Fin 4}
    (hb : IsAxialTreeBond b) : b ∉ chordBonds S := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.not_mem_chordBonds_of_tree <;> assumption
end Frames
section Torus
variable {n L : ℕ} [NeZero n] [NeZero L]
private instance : NeZero (n * (stepBlockFrame L n).blockSide) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
private theorem period_depth_stepFrame (i : Fin 4) : (stepBlockFrame L n).period 0 i = n * L :=
  period_depth_of_extent (F := stepBlockFrame L n) (fun _ => rfl) i
private theorem period_top_stepFrame (i : Fin 4) : (stepBlockFrame L n).period 1 i = n :=
  period_top_of_extent (F := stepBlockFrame L n) (fun _ => rfl) i
private theorem readAtLevel_minimizingField (a ρ : ℝ) (t : ℕ) (S : Finset (TorusSite n)) (V : TorusField n) :
    readAtLevel (torusFrame L t n) (torusFrame L t n).depth (minimizingField a ρ L t S V) =
      chartedField (minimizingCoordinates a (cellsOfSites (torusFrame L t n) S)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TorusMinimizer.readAtLevel_minimizingField <;> assumption
private theorem axialTree_torusFrame_iff_step (hL : Odd L) (h2 : 2 ≤ n) (t : ℕ) (x : TorusSite (n * L))
    (i : Fin 4) :
    IsAxialTreeBond (F := torusFrame L t n) (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth x, i) ↔
      IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 x, i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TorusMinimizer.isAxialTreeBond_frames_iff <;> assumption
open Classical in
private theorem minimizingField_apply (hL : Odd L) (h2 : 2 ≤ n) (a ρ : ℝ) (t : ℕ) (S : Finset (TorusSite n))
    (V : TorusField n) (x : TorusSite (n * L)) (i : Fin 4) :
    minimizingField a ρ L t S V x i =
      if IsCrossingBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 x, i)
      then expUnit (minimizerCoord a ρ L t S V (x, i)) * V (parentBlock L x) i
      else if IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 x, i) then 1
      else expUnit (minimizerCoord a ρ L t S V (x, i)) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TorusMinimizer.minimizingField_apply <;> assumption
private theorem torusSiteInFrame_add_unitStep (x : TorusSite (n * L)) (i : Fin 4) :
    torusSiteInFrame (stepBlockFrame L n) 0 x + BlockAverages.unitStep (F := stepBlockFrame L n) 0 i =
      torusSiteInFrame (stepBlockFrame L n) 0 (x + TorusFields.unitStep (n * L) i) := by
  apply toTorusSite_injective (F := stepBlockFrame L n) (j := 0) (N := n * L) period_depth_stepFrame
  rw [toTorusSite_add period_depth_stepFrame, toTorusSite_torusSiteInFrame period_depth_stepFrame,
    toTorusSite_torusSiteInFrame period_depth_stepFrame, toTorusSite_unitStep period_depth_stepFrame]
private theorem minimizerCoord_of_axialTree (hL : Odd L) (h2 : 2 ≤ n) {a ρ : ℝ} {t : ℕ}
    {S : Finset (TorusSite n)} {V : TorusField n} {b : TorusBond (n * L)}
    (ht : IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 b.1, b.2)) :
    minimizerCoord a ρ L t S V b = 0 :=
  minimizingCoordinates_of_not_mem
    (not_mem_chordBonds_of_axialTree ((axialTree_torusFrame_iff_step hL h2 t b.1 b.2).mpr ht))
private theorem axialGauge_eq_one_of_tree (hL : Odd L) (h2 : 2 ≤ n) (Wf : TorusField (n * L))
    (x : TorusSite (n * L))
    (hWf : ∀ b : TorusBond (n * L), parentBlock L b.1 = parentBlock L x →
      IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 b.1, b.2) →
        Wf b.1 b.2 = 1) :
    axialGauge 1 (readAtLevel (stepBlockFrame L n) 0 Wf) (torusSiteInFrame (stepBlockFrame L n) 0 x) = 1 := by
  classical
  set F := stepBlockFrame L n with hF
  have hs : ∀ i, 2 ≤ F.extent i := fun _ => h2
  have hL' : Odd F.blockSide := hL
  set W : F.GaugeField F.depth := readAtLevel F 0 Wf with hW
  set γ : F.Site F.depth → UnitQuaternion := axialGauge 1 W with hγ
  have hbl : torusSiteInFrame F F.top (parentBlock L x) = enclosingCell (torusSiteInFrame F F.depth x) :=
    (enclosingCell_torusSiteInFrame (F := F) (n := n) (fun _ => rfl) x).symm
  have h1 : ∀ z : F.Cell, γ (cellCentre F.depth z) = 1 := by
    intro z
    have hc : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := (mem_centredCube_iff _).mpr fun i => by
      have : (0 : ℤ) ≤ halfWidth F.blockSide := by
        unfold halfWidth
        have : 0 < F.blockSide := Nat.pos_of_ne_zero (NeZero.ne L)
        omega
      simpa using this
    have ho := cellOffset_centre_add hL' hs z 0 hc
    have e0 : (cellCentre F.depth z + siteOfCoords F.depth 0 : F.Site F.depth) = cellCentre F.depth z := by
      have : (siteOfCoords F.depth (0 : Fin 4 → ℤ) : F.Site F.depth) = 0 := by
        funext i
        simp [siteOfCoords]
      rw [this, add_zero]
    rw [e0] at ho
    have e1 : axisPath (0 : Fin 4 → ℤ) (1 : Equiv.Perm (Fin 4)) = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp [axisPath]
    simp only [hγ, axialGauge, ho, e1]
    rfl
  have hb : ∀ b ∈ innerBonds ({torusSiteInFrame F F.top (parentBlock L x)} : Finset F.Cell) F.depth,
      IsAxialTreeBond b → γ b.1 = γ (b.1 + BlockAverages.unitStep F.depth b.2) := by
    intro b hb ht
    have hb1 : b.1 ∈ sitesOfCells ({torusSiteInFrame F F.top (parentBlock L x)} : Finset F.Cell) F.depth :=
      (Finset.mem_product.mp (Finset.mem_filter.mp hb).1).1
    obtain ⟨y, hy, h, hh, e⟩ := mem_sitesOfCells.mp hb1
    rw [Finset.mem_singleton] at hy
    have hh' : h ∈ centredCube F.blockSide := by
      have : F.blockSide ^ (F.top - F.depth) = F.blockSide := by rw [_root_.YangMills.Construction.TopLevelSites.top_sub_depth, pow_one]
      rwa [this] at hh
    have hcell : enclosingCell b.1 = torusSiteInFrame F F.top (parentBlock L x) := by
      rw [e, enclosingCell_centre_add hL' hs y h hh', hy]
    set b' : TorusSite (n * L) := toTorusSite (n * L) b.1 with hb'
    have hof : torusSiteInFrame F F.depth b' = b.1 := torusSiteInFrame_toTorusSite period_depth_stepFrame b.1
    have hblock : parentBlock L b' = parentBlock L x := by
      have e1 : enclosingCell (torusSiteInFrame F F.depth b') = torusSiteInFrame F F.top (parentBlock L b') :=
        enclosingCell_torusSiteInFrame (F := F) (n := n) (fun _ => rfl) b'
      rw [hof, hcell] at e1
      have e3 := congrArg (toTorusSite n) e1
      have h3 : ∀ u : TorusSite n, toTorusSite n (torusSiteInFrame F F.top u) = u := fun u =>
        toTorusSite_torusSiteInFrame (F := F) (j := F.top) (period_top_of_extent (fun _ => rfl)) u
      rw [h3, h3] at e3
      exact e3.symm
    have ht' : IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 b', b.2) := by
      have : torusSiteInFrame (stepBlockFrame L n) 0 b' = b.1 := hof
      rw [this]
      exact ht
    have hone : Wf b' b.2 = 1 := hWf (b', b.2) hblock ht'
    have hv := axialGauge_treeBond hL' hs W b.1 b.2 ht
    have hWb : W b.1 b.2 = 1 := hone
    simp only [BlockAverages.gaugeTransform, hWb, mul_one] at hv
    exact mul_inv_eq_one.mp hv
  obtain ⟨ho, he⟩ := centre_cellOffset hL' hs (torusSiteInFrame F F.depth x)
  have key := gauge_eq_one_on_sites hL' hs γ h1 hb (torusSiteInFrame F F.top (parentBlock L x))
    (Finset.mem_singleton_self _) (cellOffset (torusSiteInFrame F F.depth x)) ho
  rw [hbl, he] at key
  exact key
private theorem chartCoord_minimizingField (ℓ : StepParameters) {n : ℕ} [NeZero n] (hL : Odd ℓ.side)
    (h2 : 2 ≤ n) (a ρ : ℝ) (t : ℕ) (S : Finset (TorusSite n)) (V : TorusField n)
    (hw : ∀ b : TorusBond (n * ℓ.side), ‖(minimizerCoord a ρ ℓ.side t S V b : ℍ[ℝ])‖ < Real.pi)
    (b : TorusBond (n * ℓ.side)) :
    chartCoord ℓ V (minimizingField a ρ ℓ.side t S V) b = minimizerCoord a ρ ℓ.side t S V b := by
  classical
  obtain ⟨x, i⟩ := b
  set F := stepBlockFrame ℓ.side n with hF
  set Wl := minimizingField a ρ ℓ.side t S V with hWl
  have htree : ∀ y : TorusSite (n * ℓ.side),
      axialGauge 1 (readAtLevel F 0 Wl) (torusSiteInFrame F 0 y) = 1 := fun y =>
    axialGauge_eq_one_of_tree hL h2 _ y fun b _ ht => by
      have hc : ¬ IsCrossingBond (F := stepBlockFrame ℓ.side n)
          (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1, b.2) := ht.1
      rw [hWl, minimizingField_apply hL h2, if_neg hc, if_pos ht]
  have g1 : axialGauge 1 (readAtLevel F F.depth Wl) (torusSiteInFrame F F.depth x) = 1 := htree x
  have g2 : axialGauge 1 (readAtLevel F F.depth Wl)
      (torusSiteInFrame F F.depth x + BlockAverages.unitStep F.depth i) = 1 := by
    have e : (torusSiteInFrame F F.depth x + BlockAverages.unitStep F.depth i : F.Site F.depth) =
        torusSiteInFrame F F.depth (x + TorusFields.unitStep (n * ℓ.side) i) :=
      torusSiteInFrame_add_unitStep x i
    rw [e]
    exact htree _
  have hread : readAtLevel F F.depth Wl (torusSiteInFrame F F.depth x) i = Wl x i :=
    readAtLevel_torusSiteInFrame period_depth_stepFrame _ x i
  have hg : BlockAverages.gaugeTransform (j := F.depth) (axialGauge 1 (readAtLevel F F.depth Wl)) (readAtLevel F F.depth Wl)
      (torusSiteInFrame F F.depth x) i = Wl x i := by
    unfold BlockAverages.gaugeTransform
    rw [g1, hread, g2]
    simp
  have hw' := hw (x, i)
  have hcell : readAtLevel F 1 V (enclosingCell (torusSiteInFrame F 0 x)) i = V (parentBlock ℓ.side x) i := by
    have e : enclosingCell (torusSiteInFrame F F.depth x) = torusSiteInFrame F F.top (parentBlock ℓ.side x) :=
      enclosingCell_torusSiteInFrame (F := F) (n := n) (fun _ => rfl) x
    have : enclosingCell (torusSiteInFrame F 0 x) = torusSiteInFrame F 1 (parentBlock ℓ.side x) := e
    rw [this]
    exact readAtLevel_torusSiteInFrame period_top_stepFrame V _ i
  unfold chartCoord LumpContours.bondCoordinate
  simp only
  have hg' : gaugeTransform (axialGauge 1 (readAtLevel F 0 Wl)) (readAtLevel F 0 Wl)
      (torusSiteInFrame F 0 x) i = Wl x i := hg
  by_cases h1 : IsCrossingBond (F := F) (torusSiteInFrame F 0 x, i)
  · rw [if_pos h1]
    have e1 : Wl x i = expUnit (minimizerCoord a ρ ℓ.side t S V (x, i)) * V (parentBlock ℓ.side x) i := by
      rw [hWl, minimizingField_apply hL h2, if_pos h1]
    have e3 : gaugeTransform (axialGauge 1 (readAtLevel F 0 Wl)) (readAtLevel F 0 Wl) (torusSiteInFrame F 0 x) i *
        (readAtLevel F 1 V (enclosingCell (torusSiteInFrame F 0 x)) i)⁻¹ =
          expUnit (minimizerCoord a ρ ℓ.side t S V (x, i)) := by
      rw [hg', hcell, e1]
      group
    have e4 := minimalLog_expUnit_of_norm_lt hw'
    rw [← e3] at e4
    exact e4
  · rw [if_neg h1]
    by_cases h3 : IsAxialTreeBond (F := F) (torusSiteInFrame F 0 x, i)
    · have e1 : Wl x i = 1 := by
        rw [hWl, minimizingField_apply hL h2, if_neg h1, if_pos h3]
      have e3 : minimizerCoord a ρ ℓ.side t S V (x, i) = 0 := minimizerCoord_of_axialTree hL h2 h3
      rw [hg', e1, e3]
      have e4 := minimalLog_expUnit_of_norm_lt (w := 0) (by simpa using Real.pi_pos)
      rw [expUnit_zero_eq_one] at e4
      exact e4
    · have e1 : Wl x i = expUnit (minimizerCoord a ρ ℓ.side t S V (x, i)) := by
        rw [hWl, minimizingField_apply hL h2, if_neg h1, if_neg h3]
      rw [hg', e1]
      exact minimalLog_expUnit_of_norm_lt hw'
end Torus
theorem minimizingFieldOfCutoff_holds (hc : ComplementOfThickenedLumpsRegular)
    (hC : WholeCellCostEqualsMinimalAction) : minimizingFieldOfCutoff := by
  intro ℓ δ lam ρA σA cg N hfit hchain hσ t r' n _ V S C sT hsit
  obtain ⟨hs0, hs2, h4096, hall⟩ := stepSituation_regular_and_cold hc hfit hsit
  set F := torusFrame ℓ.side t n with hF
  obtain ⟨hreg, hcold⟩ := hall F (fun _ => rfl)
  obtain ⟨_, _, _, hρ0, hρ1, _, _, _, hmain⟩ := hchain
  have hamb : IsAdmissibleAmbient F := TorusFrame.isAdmissibleAmbient_torusFrame (by omega)
  have hone := (hmain F 2047 _ rfl hamb (by norm_num) hreg sT _ hs0 (hs2.trans hσ) hcold).1
  have hL : Odd F.blockSide := hfit.L_odd
  have hs : ∀ i, 2 ≤ F.extent i := fun _ => by
    change 2 ≤ n
    omega
  have hπ : ρA < Real.pi := by linarith [Real.pi_gt_three]
  obtain ⟨w, hl, -, hw⟩ := minimizingCoordinates_eq hL hs hπ le_rfl hone
  have ha : 0 ≤ ℓ.coupling := by have := hfit.a_ge; linarith
  have hsmall : ∀ b : TorusBond (n * ℓ.side),
      ‖(minimizerCoord ℓ.coupling ρA ℓ.side t S V b : ℍ[ℝ])‖ < Real.pi := by
    classical
    intro b
    have hpi := Real.pi_gt_three
    have e : minimizerCoord ℓ.coupling ρA ℓ.side t S V b = w (torusSiteInFrame F F.depth b.1) b.2 := by
      unfold minimizerCoord BlockAverages.minimizingBondCoordinate
      rw [hw]
    rw [e]
    by_cases hb : (torusSiteInFrame F F.depth b.1, b.2) ∈ chordBonds (cellsOfSites F S)
    · have h1 := hl.2.1 _ hb
      have h2 : ‖w (torusSiteInFrame F F.depth b.1) b.2‖ ≤ 1 := h1.trans ((min_le_left _ _).trans hρ1)
      have h3 : ‖(w (torusSiteInFrame F F.depth b.1) b.2 : ℍ[ℝ])‖ ≤ 1 := h2
      linarith
    · have h1 := hl.1 _ hb
      have h2 : w (torusSiteInFrame F F.depth b.1) b.2 = 0 := h1
      rw [h2]
      simpa using Real.pi_pos
  refine ⟨?_, chartCoord_minimizingField ℓ hfit.L_odd (by omega) _ _ t S V hsmall⟩
  intro W'
  have hE := (hC F ℓ.coupling (cellsOfSites F S) hfit.L_odd ha).2.2
  rw [hE, hE, readAtLevel_minimizingField, hw]
  exact hl.2.2 W'
end YangMills.Construction.HullsInEveryVolume
end
