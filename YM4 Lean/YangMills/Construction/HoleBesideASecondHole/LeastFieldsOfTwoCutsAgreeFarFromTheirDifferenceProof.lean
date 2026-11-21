import YangMills.Construction.ColdChainAtEveryLevel.AnalyticCoordinatesOfAColdTop
import YangMills.Construction.ColdChainAtEveryLevel.OneLeastFieldOfAColdTop
import YangMills.Construction.HoleBesideASecondHole.CostOnWholeCellsIsTheLeastAction
import YangMills.Construction.HoleBesideASecondHole.EnergyInTheChart
import YangMills.Construction.HoleBesideASecondHole.LeastFieldsOfTwoCutsAgreeFarFromTheirDifference
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LumpContours
open YangMills.Construction.BlockAverages YangMills.Construction.GaugeFixing
variable {F : BlockFrame}
theorem minimalLog_one : minimalLog (1 : UnitQuaternion) = 0 := by
  have := minimalLog_expUnit (0 : imaginaryQuaternions) (by simpa using Real.pi_pos)
  rwa [expUnit_zero] at this
theorem lexBondCoordinate_eq_zero_of_isAxialTreeBond (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (V : F.GaugeField F.top) (W : F.GaugeField F.depth)
    (b : F.Site F.depth × Fin 4) (hb : IsAxialTreeBond b) : lexBondCoordinate V W b = 0 := by
  unfold lexBondCoordinate bondCoordinate
  rw [if_neg hb.1, gaugeTransform_axialGauge_of_isAxialTreeBond hs hL W b.1 b.2 hb, minimalLog_one]
theorem lexBondCoordinate_eq_minimizing (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (a ρ N0 s : ℝ) (hρ : ρ ≤ 1) (S : Finset F.Cell)
    (V : F.GaugeField F.top) (Wl : F.GaugeField F.depth) (hone : HasColdMinimizer a ρ N0 s S V)
    (hmin : ∀ W'', blockEnergy a S F.depth Wl V ≤ blockEnergy a S F.depth W'' V)
    (b : F.Site F.depth × Fin 4) (hb : b ∈ chordBonds S) :
    lexBondCoordinate V Wl b = minimizingBondCoordinate a ρ S b V ∧
      ‖(lexBondCoordinate V Wl b : ℍ[ℝ])‖ ≤ N0 * s := by
  obtain ⟨w, hLC, -, huniq⟩ := hone
  have hpi : (1 : ℝ) < Real.pi := by have := Real.pi_gt_three; linarith
  have hwle : ∀ b ∈ chordBonds S, ‖(w b.1 b.2 : ℍ[ℝ])‖ ≤ ρ :=
    fun b hb => (hLC.2.1 b hb).trans (min_le_left _ _)
  have hLC' : IsMinimizingChart a S V ρ w := ⟨hLC.1, hwle, hLC.2.2⟩
  have hex : ∃ w, IsMinimizingChart a S V ρ w := ⟨w, hLC'⟩
  have hch : minimizingCoordinates a S V ρ = hex.choose := dif_pos hex
  have hw2 : IsMinimizingChart a S V ρ (minimizingCoordinates a S V ρ) := by
    rw [hch]
    exact hex.choose_spec
  set w2 := minimizingCoordinates a S V ρ with hw2d
  obtain ⟨γ, hγ, hsame⟩ := huniq Wl hmin
  obtain ⟨γ2, hγ2, hsame2⟩ := huniq (chartedField w2 V) hw2.2.2
  have c1 := bondCoordinate_of_agreeOnBonds hs hL S V w γ Wl hγ hsame b hb
    ((hwle b hb).trans_lt (by linarith))
  have c2 := bondCoordinate_of_agreeOnBonds hs hL S V w γ2 _ hγ2 hsame2 b hb
    ((hwle b hb).trans_lt (by linarith))
  have hid : AgreeOnBonds S F.depth (chartedField w2 V)
      (gaugeTransform (fun _ => 1) (chartedField w2 V)) := by
    intro c _
    simp [gaugeTransform]
  have c3 := bondCoordinate_of_agreeOnBonds hs hL S V w2 (fun _ => 1) _ (fun _ => rfl) hid b hb
    ((hw2.2.1 b hb).trans_lt (by linarith))
  have e : lexBondCoordinate V Wl b = w b.1 b.2 := c1
  refine ⟨?_, ?_⟩
  · rw [e]
    show w b.1 b.2 = w2 b.1 b.2
    rw [← c2, c3]
  · rw [e]
    exact (hLC.2.1 b hb).trans (min_le_right _ _)
theorem natAbs_valMinAbs_le_cellSupDist (y z : F.Cell) (k : Fin 4) :
    ((z k - y k).valMinAbs).natAbs ≤ cellSupDist y z := by
  have h1 : ((y k - z k).valMinAbs).natAbs ≤ cellSupDist y z :=
    Finset.le_sup (f := fun i => ((y i - z i).valMinAbs).natAbs) (Finset.mem_univ k)
  have e : z k - y k = -(y k - z k) := by ring
  rw [e, ZMod.natAbs_valMinAbs_neg]
  exact h1
set_option maxHeartbeats 1000000 in
theorem minimizingFieldsLocalStatement_holds (hOne : uniqueMinimizerStatement)
    (hAC : analyticChartCoordsStatement) (hCost : WholeCellCostEqualsMinimalAction) :
    minimizingFieldsLocalStatement := by
  intro a ha
  have ha0 : 0 < a := by linarith
  obtain ⟨δ, hδ, h1⟩ := hAC a ha0
  obtain ⟨L1, h1⟩ := h1 δ hδ le_rfl
  obtain ⟨L2, h2⟩ := hOne a ha0
  refine ⟨δ, hδ, max L1 L2, fun L hodd hL => ?_⟩
  obtain ⟨σ1, Nk, hσ1, hNk, h1⟩ := h1 L hodd (le_of_max_le_left hL) (1 / 8) (by norm_num) (by norm_num)
  obtain ⟨σ2, N0, hσ2, hN0, h2⟩ := h2 L hodd (le_of_max_le_right hL) (1 / 8) (by norm_num)
  refine ⟨min σ1 σ2, N0 + Nk 0, lt_min hσ1 hσ2, add_pos hN0 (hNk 0), ?_⟩
  intro F m S S' hFL hcub hm hreg hreg' s V Wl Wl' hs0 hsσ hcold hcold' hleast hleast'
  subst hFL
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hcub.1 i]; have := hcub.2; omega
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hA : IsAdmissibleAmbient F := Or.inr fun i => by rw [hcub.1 i]; exact hcub.2
  have hplain : ∀ (T : Finset F.Cell) (W : F.GaugeField F.depth),
      plainBlockEnergy a T W V = blockEnergy a T F.depth W V :=
    fun T W => (hCost F a T hodd ha0.le).2.2 W V
  have hmin : ∀ W'', blockEnergy a S F.depth Wl V ≤ blockEnergy a S F.depth W'' V := fun W'' => by
    have := hleast W''
    rwa [hplain, hplain] at this
  have hmin' : ∀ W'', blockEnergy a S' F.depth Wl' V ≤ blockEnergy a S' F.depth W'' V := fun W'' => by
    have := hleast' W''
    rwa [hplain, hplain] at this
  have s1 : s ≤ σ1 := hsσ.trans (min_le_left _ _)
  have s2 : s ≤ σ2 := hsσ.trans (min_le_right _ _)
  have hone := h2 F m S rfl hA hm hreg s V hs0 s2 hcold
  have hone' := h2 F m S' rfl hA hm hreg' s V hs0 s2 hcold'
  have hNs : 0 < Nk 0 * s := mul_pos (hNk 0) hs0
  refine ⟨fun b hb => ?_, fun y r hr hside hagree b hb hb' h1b h2b => ?_⟩
  · by_cases ht : IsAxialTreeBond b
    · rw [lexBondCoordinate_eq_zero_of_isAxialTreeBond hs hodd V Wl b ht]
      simp only [ZeroMemClass.coe_zero, norm_zero]
      exact (mul_pos (add_pos hN0 (hNk 0)) hs0).le
    · have hc : b ∈ chordBonds S := by
        simp only [chordBonds, Finset.mem_filter]
        exact ⟨hb, ht⟩
      have := (lexBondCoordinate_eq_minimizing hs hodd a (1 / 8) N0 s (by norm_num) S V Wl hone hmin b hc).2
      nlinarith
  · by_cases ht : IsAxialTreeBond b
    · rw [lexBondCoordinate_eq_zero_of_isAxialTreeBond hs hodd V Wl b ht,
        lexBondCoordinate_eq_zero_of_isAxialTreeBond hs hodd V Wl' b ht]
      simp only [sub_self, norm_zero]
      have := Real.exp_pos (-δ * ((r : ℝ) - 1))
      have h3 : 0 < (N0 + Nk 0) * s := mul_pos (add_pos hN0 (hNk 0)) hs0
      exact (mul_pos h3 this).le
    have hc : b ∈ chordBonds S := by
      simp only [chordBonds, Finset.mem_filter]
      exact ⟨hb, ht⟩
    have hc' : b ∈ chordBonds S' := by
      simp only [chordBonds, Finset.mem_filter]
      exact ⟨hb', ht⟩
    rw [(lexBondCoordinate_eq_minimizing hs hodd a (1 / 8) N0 s (by norm_num) S V Wl hone hmin b hc).1,
      (lexBondCoordinate_eq_minimizing hs hodd a (1 / 8) N0 s (by norm_num) S' V Wl' hone' hmin' b hc').1]
    obtain ⟨x, i⟩ := b
    simp only at h1b h2b
    obtain ⟨ho, hx⟩ := cellOffset_mem_and_eq hs' hodd x
    set h : Fin 4 → ℤ := fun k => ((enclosingCell x - y) k).valMinAbs with hh
    have hcell : y + siteOfCoords F.top h = enclosingCell x := by
      funext k
      simp [hh, siteOfCoords]
    have hbond : fineBondAt y h (cellOffset x) i = (x, i) := by
      simp only [fineBondAt, hcell, hx]
    have hbox : WithinRadius r h := by
      intro k
      have h3 := natAbs_valMinAbs_le_cellSupDist y (enclosingCell x) k
      have h4 : |h k| = ((enclosingCell x - y) k).valMinAbs.natAbs := by
        rw [Int.abs_eq_natAbs]
      rw [h4]
      have : ((enclosingCell x - y) k).valMinAbs.natAbs ≤ r := by
        have h5 : ((enclosingCell x k - y k).valMinAbs).natAbs ≤ 1 := h3.trans h1b
        have h6 : (enclosingCell x - y) k = enclosingCell x k - y k := rfl
        rw [h6]
        omega
      exact_mod_cast this
    have hag : AgreeOnBall S V S' V y y r := by
      refine ⟨fun i => Or.inr ?_, fun i => Or.inr ?_, hagree, fun _ _ => rfl⟩
      · rw [hcub.1 i]; exact hside
      · rw [hcub.1 i]; exact hside
    have hloc := ((h1 F m S rfl hA hm hreg s V hs0 s1 hcold).2 F S' V y y r rfl rfl hA hreg' hcold' hag)
      h (cellOffset x) i ho (by rw [hbond]; exact hc) hbox (by rw [hbond]; exact h2b.trans hr)
    rw [hbond] at hloc
    refine hloc.1.trans ?_
    have hcd : (cellSupDist y (enclosingCell x) : ℝ) ≤ 1 := by exact_mod_cast h1b
    have hexp : Real.exp (-δ * ((r : ℝ) - cellSupDist y (enclosingCell x))) ≤
        Real.exp (-δ * ((r : ℝ) - 1)) := by
      apply Real.exp_le_exp.2
      nlinarith
    have h3 : Nk 0 * s ≤ (N0 + Nk 0) * s := by nlinarith
    calc Nk 0 * s * Real.exp (-δ * ((r : ℝ) - cellSupDist y (enclosingCell x)))
        ≤ Nk 0 * s * Real.exp (-δ * ((r : ℝ) - 1)) := mul_le_mul_of_nonneg_left hexp hNs.le
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
end YangMills.Construction.LumpContours
end
