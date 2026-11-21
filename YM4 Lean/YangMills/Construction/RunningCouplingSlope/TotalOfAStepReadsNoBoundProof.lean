import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.ColdStepAtMirrorFrames.OneLeastChart
import YangMills.Construction.RunningCouplingSlope.LeastFieldNearTheFlatField
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepReadsNoBound
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
open Filter
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.TorusFields YangMills.Construction.ReferenceDensity YangMills.Construction.SlopeCoefficient
namespace CutoffIndependence
variable {F : BlockFrame}
private theorem isMinimizingChart_one {a ρ : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (h : IsMinimizingChart a S V ρ w) (h1 : ρ ≤ 1) : IsMinimizingChart a S V 1 w :=
  ⟨h.1, fun b hb => (h.2.1 b hb).trans h1, h.2.2⟩
private theorem minimizingCoordinates_spec {a ρ : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top}
    (h : ∃ w, IsMinimizingChart a S V ρ w) : IsMinimizingChart a S V ρ (minimizingCoordinates a S V ρ) := by
  unfold minimizingCoordinates
  rw [dif_pos h]
  exact h.choose_spec
abbrev _root_.YangMills.SharedProofs.p13409 := @minimizingCoordinates_spec
private theorem isCold_everywhere (S : Finset F.Cell) (j : ℕ) (X : F.GaugeField j) : IsCold S j (24 / 8) X := by
  intro p _
  have h1 : ‖((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      ‖((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ])‖ + ‖(1 : ℍ[ℝ])‖ := norm_sub_le _ _
  rw [norm_coe_unitQuaternion, norm_one] at h1
  unfold plaquetteDefect
  norm_num at h1 ⊢
  linarith
abbrev _root_.YangMills.SharedProofs.p32772 := @isCold_everywhere
private theorem fieldAboveFrame_zero (a ρ : ℝ) (V : F.GaugeField F.top) :
    fieldAboveFrame true a ρ 0 V 0 = chartedField (minimizingCoordinates a (finiteCells F) V ρ) V := by
  have e0 : toImaginary (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by
    apply Subtype.ext
    ext <;> simp [toImaginary]
  unfold fieldAboveFrame
  congr 1
  funext x i
  simp [coordsAboveFrame, ColdStepAtMirrorFrames.stepFrame, minimizingBondCoordinate,
    ColdStepAtMirrorFrames.stepCoordinates, e0]
abbrev _root_.YangMills.DeltaSharedProofs.p501148 := @fieldAboveFrame_zero
abbrev _root_.YangMills.SharedProofs.p22006 := @fieldAboveFrame_zero
private theorem minimizingCoordinates_eq (hLC : MinimizingChartUnique) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i)
    {a ρ ρ' : ℝ} (h1 : ρ ≤ 1) (h1' : ρ' ≤ 1) {V : F.GaugeField F.top}
    (hex : ∃ w, IsMinimizingChart a (finiteCells F) V ρ w)
    (hex' : ∃ w, IsMinimizingChart a (finiteCells F) V ρ' w)
    (horb : ∀ W' : F.GaugeField F.depth,
      (∀ W'', blockEnergy a (finiteCells F) F.depth W' V ≤ blockEnergy a (finiteCells F) F.depth W'' V) →
      ∃ γ : F.Site F.depth → UnitQuaternion, (∀ z : F.Cell, γ (cellCentre _ z) = 1) ∧
        W' = BlockAverages.gaugeTransform γ (fieldAboveFrame true a ρ 0 V 0)) :
    minimizingCoordinates a (finiteCells F) V ρ = minimizingCoordinates a (finiteCells F) V ρ' := by
  have hw := isMinimizingChart_one (minimizingCoordinates_spec hex) h1
  have hw' := isMinimizingChart_one (minimizingCoordinates_spec hex') h1'
  have hOne : HasColdMinimizer a 1 1 24 (finiteCells F) V := by
    refine ⟨minimizingCoordinates a (finiteCells F) V ρ, ?_, isCold_everywhere _ _ _, ?_⟩
    · have e : min (1 : ℝ) (1 * 24) = 1 := by norm_num
      rw [e]
      exact hw
    · intro W' hW'
      obtain ⟨γ, hγ, e⟩ := horb W' hW'
      refine ⟨γ, hγ, fun b _ => ?_⟩
      rw [e, fieldAboveFrame_zero]
  exact ((hLC F a 1 1 24 V _ hL hs le_rfl hOne hw).1 _ hw').symm
private theorem stepLogAmplitude_congr {a ρ ρ' : ℝ} {V : F.GaugeField F.top}
    (h : minimizingCoordinates a (finiteCells F) V ρ = minimizingCoordinates a (finiteCells F) V ρ') :
    stepLogAmplitude a ρ V = stepLogAmplitude a ρ' V := by
  have e : coordsAboveFrame true a ρ 0 V = coordsAboveFrame true a ρ' 0 V := by
    funext η x i
    simp only [coordsAboveFrame, ColdStepAtMirrorFrames.stepFrame, if_true, minimizingBondCoordinate, h]
  have eH : chartedHessian a ρ V 0 = chartedHessian a ρ' V 0 := by
    have eE : chartedEnergyAtMinimizer a ρ V = chartedEnergyAtMinimizer a ρ' V := by
      funext η
      unfold chartedEnergyAtMinimizer
      rw [e]
    unfold chartedHessian
    rw [eE]
  have eS : fieldAboveFrame true a ρ 0 V 0 = fieldAboveFrame true a ρ' 0 V 0 := by
    unfold fieldAboveFrame
    rw [e]
  unfold stepLogAmplitude
  rw [eH, eS, e]
abbrev _root_.YangMills.SharedProofs.p40020 := @stepLogAmplitude_congr
end CutoffIndependence
open CutoffIndependence in
theorem stepGaugeTotal_independent_of_cutoff (hLC : MinimizingChartUnique)
    (hN : RunningCouplingSlope.MinimizerNearTrivialField) :
    StepGaugeTotalIndependentOfCutoff := by
  intro a ha L hL t ρ ρ' h0 h1 h0' h1'
  filter_upwards [eventually_ge_atTop (2 * L)] with n hn
  have hs : ∀ i, 2 ≤ (torusFrame L t n).extent i := fun _ => by
    have := hL.2
    show 2 ≤ n
    omega
  have key : ∀ᶠ V in 𝓝 (trivialField n),
      minimizingCoordinates a (finiteCells (torusFrame L t n))
          (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ =
        minimizingCoordinates a (finiteCells (torusFrame L t n))
          (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ' := by
    filter_upwards [(hN a ha L hL t n ρ hn h0 h1).2, (hN a ha L hL t n ρ' hn h0' h1').2] with V hV hV'
    exact minimizingCoordinates_eq hLC hL.1 hs h1 h1' hV.1 hV'.1 hV.2.1
  filter_upwards [key] with V hV
  unfold stepGaugeTotal
  rw [stepLogAmplitude_congr hV, stepLogAmplitude_congr key.self_of_nhds]
end YangMills.Construction.RunningCouplingSlope
end
