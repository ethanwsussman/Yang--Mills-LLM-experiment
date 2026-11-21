import YangMills.Construction.ColdChainAtEveryLevel.AnalyticSharesOfAColdTopProof
import YangMills.Construction.ColdChainAtEveryLevel.ChartOfTheCriticalField
import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainOfAColdTop
import YangMills.Construction.ColdChainAtEveryLevel.FramingsOfNoEnergyAgreeProof
import YangMills.Construction.ColdChainAtEveryLevel.LeastFieldIsTheCriticalField
import YangMills.Construction.ColdChainAtEveryLevel.OneLeastFieldOfAColdTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.UniqueMinimizer
variable {F : BlockFrame}
theorem plaquetteDefect_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteDefect (gaugeTransform γ X) p = plaquetteDefect X p := by apply _root_.YangMills.Construction.GaugeFixing.plaquetteDefect_gaugeTransform <;> assumption
theorem enclosingCell_mem {S : Finset F.Cell} (hL : Odd F.blockSide) {j : ℕ} {x : F.Site j}
    (hx : x ∈ sitesOfCells S j) : enclosingCell x ∈ S := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_mem <;> assumption
theorem rotatedField_zero (V : F.GaugeField F.top) :
    rotatedField (fun _ _ => (0 : imaginaryQuaternions)) V = V := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.rotatedField_zero <;> assumption
theorem source_mem_sitesOfCells {S : Finset F.Cell} {j : ℕ} {b : F.Site j × Fin 4}
    (hb : b ∈ innerBonds S j) : b.1 ∈ sitesOfCells S j := by
  have := (Finset.mem_filter.1 hb).1
  exact (Finset.mem_product.1 this).1
theorem target_mem_sitesOfCells {S : Finset F.Cell} {j : ℕ} {b : F.Site j × Fin 4}
    (hb : b ∈ innerBonds S j) : b.1 + unitStep j b.2 ∈ sitesOfCells S j := (Finset.mem_filter.1 hb).2
theorem plaquetteHolonomy_congr (S : Finset F.Cell) {j : ℕ} (X X' : F.GaugeField j)
    (h : AgreeOnBonds S j X X') (p : F.Site j × Fin 4 × Fin 4) (hp : p ∈ innerPlaquettes S j) :
    plaquetteHolonomy X p = plaquetteHolonomy X' p := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.plaquetteHolonomy_congr <;> assumption
theorem enclosingCell_cellCentre (hL : Odd F.blockSide) (j : ℕ) (z : F.Cell) :
    enclosingCell (cellCentre j z : F.Site j) = z := by apply _root_.YangMills.Construction.BlockAverages.ZeroEnergyFramings.enclosingCell_cellCentre <;> assumption
theorem uniqueMinimizer (hC : coldTopCriticalChainStatement) (hVal : criticalValueEqMinimalActionStatement)
    (hCh : criticalFieldChartStatement) (hLF : minimalFieldIsCriticalStatement)
    (hLV : minimalChainExistenceStatement) : uniqueMinimizerStatement := by
  classical
  intro a ha
  obtain ⟨θ, del, Ca, hθ, hθ8, hd, hd8, hCa, L₁, hC'⟩ := hC a ha
  obtain ⟨L₂, hV'⟩ := hVal a θ del Ca ha hθ hθ8 hd hd8 hCa
  obtain ⟨L₃, hCh'⟩ := hCh a θ del Ca ha hθ hθ8 hd hd8 hCa
  obtain ⟨L₄, hLF'⟩ := hLF a θ del Ca ha hθ hθ8 hd hd8 hCa
  refine ⟨max L₁ (max L₂ (max L₃ L₄)), fun L hL hge ρ hρ => ?_⟩
  have g1 : L₁ ≤ L := le_of_max_le_left hge
  have g2 : L₂ ≤ L := le_of_max_le_left (le_of_max_le_right hge)
  have g3 : L₃ ≤ L := le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hge))
  have g4 : L₄ ≤ L := le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hge))
  obtain ⟨rL, sL, CL, hr, hsL, hCL, hc⟩ := hC' L hL g1
  obtain ⟨σ3, hσ3, hv⟩ := hV' L hL g2 CL hCL
  obtain ⟨σ4, N0, hσ4, hN0, hch⟩ := hCh' L hL g3 CL hCL
  obtain ⟨σ5, hσ5, hlf⟩ := hLF' L hL g4 CL hCL
  refine ⟨min (min sL σ3) (min σ4 (min σ5 (ρ / N0))), N0,
    lt_min (lt_min hsL hσ3) (lt_min hσ4 (lt_min hσ5 (by positivity))), hN0, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsσ hcold
  have e1 : s ≤ sL := hsσ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have e2 : s ≤ σ3 := hsσ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have e3 : s ≤ σ4 := hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e4 : s ≤ σ5 := hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have e5 : s ≤ ρ / N0 := hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hLF2 : Odd F.blockSide := hFL ▸ hL
  obtain ⟨U, -, -, hcrit, -, hsplit, -, hcold8, hq, hcm, hmis⟩ :=
    hc F m S hFL hamb hm hreg s V hs e1 hcold
  have hU : IsCriticalChainOverTop a θ del Ca CL s S V V U :=
    ⟨hcrit, hsplit, hq, hcm, fun j z hj => by rw [hFL]; exact hmis j z hj⟩
  have hU' : IsCriticalChainOverTop a θ del Ca CL s S V
      (rotatedField (fun _ _ => (0 : imaginaryQuaternions)) V) U := by
    rw [rotatedField_zero]
    exact hU
  have hv0 : ∀ (y : F.Site F.top) (i : Fin 4), ‖(0 : imaginaryQuaternions)‖ ≤ s := fun _ _ => by
    simpa using hs.le
  have hleast := (hv F m S hFL hamb hm hreg s V (fun _ _ => 0) hs e2 hcold hv0 U hU').1
  rw [rotatedField_zero] at hleast
  obtain ⟨w, γ, h0, hb, hsame, hen, hcent⟩ := hch F m S hFL hamb hm hreg s V hs e3 hcold U hU
  have hNs : N0 * s ≤ ρ := by
    rw [le_div_iff₀ hN0] at e5
    linarith
  refine ⟨w, ⟨h0, fun b hb' => (hb b hb').trans (le_min hNs le_rfl), fun W' => ?_⟩, ?_, ?_⟩
  · obtain ⟨W0, hW0, hmin⟩ := (hLV F a S ha.le).2.2.1 F.depth V
    have h1 : blockEnergy a S F.depth (chartedField w V) V ≤ blockEnergy a S F.depth W0 V := by
      rw [hW0]
      exact hen.trans (le_of_eq hleast.symm)
    exact h1.trans (hmin W')
  · intro p hp
    have h1 : plaquetteDefect (chartedField w V) p =
        plaquetteDefect (gaugeTransform γ (chartField (referenceFieldChain S V) U F.depth)) p := by
      unfold plaquetteDefect
      rw [plaquetteHolonomy_congr S _ _ hsame p hp]
    rw [h1, plaquetteDefect_gaugeTransform]
    exact hcold8 p hp
  · intro W' hW'
    obtain ⟨γ', hc', hs'⟩ := hlf F m S hFL hamb hm hreg s V hs e4 hcold U hU W' hW'
    refine ⟨fun x => if enclosingCell x ∈ S then γ' x * (γ x)⁻¹ else 1, fun z => ?_, fun b hb' => ?_⟩
    · by_cases hz : z ∈ S
      · simp only [enclosingCell_cellCentre hLF2, hz, if_true]
        rw [hc' z hz, hcent z hz, mul_inv_cancel]
      · simp only [enclosingCell_cellCentre hLF2, hz, if_false]
    · have m1 : enclosingCell b.1 ∈ S := enclosingCell_mem hLF2 (source_mem_sitesOfCells hb')
      have m2 : enclosingCell (b.1 + unitStep F.depth b.2) ∈ S :=
        enclosingCell_mem hLF2 (target_mem_sitesOfCells hb')
      have h1 := hs' b hb'
      have h2 := hsame b hb'
      unfold gaugeTransform at h1 h2 ⊢
      simp only [m1, m2, if_true]
      rw [h1, h2]
      group
end YangMills.Construction.BlockAverages.UniqueMinimizer
end
