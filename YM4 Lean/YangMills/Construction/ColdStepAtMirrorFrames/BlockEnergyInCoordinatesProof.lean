import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyInCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.ChartEnergyInCoordinatesProof
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexAboveAChartPointProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
variable {F : BlockFrame}
namespace CellEnergyInCoordinates
theorem chartedField_congr (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs0 : ∀ i, 0 < F.extent i)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions} (V : F.GaugeField F.top)
    (h : ∀ b ∈ chordBonds (finiteCells F), w b.1 b.2 = w' b.1 b.2) : chartedField w V = chartedField w' V := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.chartedField_congr <;> assumption
theorem sum_chartCoordinates_smul_directionCoordinate (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (dv : F.Site F.top → Fin 4 → imaginaryQuaternions) (x : F.Site F.depth) (i : Fin 4)
    (hb : (x, i) ∈ chordBonds (finiteCells F)) :
    ∑ l, chartCoordinates dw dv l • directionCoordinate (chartDirections F l) x i = dw x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedEnergyCoordinates.sum_directionCoordinate_chartCoordinates <;> assumption
theorem sum_chartCoordinates_smul_directionMove (hs : ∀ i, 2 ≤ F.extent i)
    (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (dv : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    (fun y i => ∑ l, chartCoordinates dw dv l • directionMove (chartDirections F l) y i) = dv := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedEnergyCoordinates.sum_directionMove_chartCoordinates <;> assumption
theorem cellEnergyShare_congr (a : ℝ) (Y : F.Cell) {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top} (h : chartedField w V = chartedField w' V) :
    cellEnergyShare a Y w V = cellEnergyShare a Y w' V := by
  unfold cellEnergyShare
  rw [h]
end CellEnergyInCoordinates
open CellEnergyInCoordinates in
theorem cellEnergyInCoordinates_holds (hcover : BlocksCoverLowerLevel) : CellEnergyInCoordinates := by
  classical
  intro F a Y w dw V dv hL hs
  have hs0 : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  constructor
  · unfold cellEnergyAlong
    rw [sum_chartCoordinates_smul_directionMove hs]
    refine cellEnergyShare_congr a Y (chartedField_congr hcover hL hs0 _ fun b hb => ?_)
    rw [sum_chartCoordinates_smul_directionCoordinate dw dv b.1 b.2 hb]
  · intro σ
    unfold cellEnergyAlong
    have hm : (fun y i => ∑ l, (chartCoordinates dw (fun _ _ => 0) + σ) l • directionMove (chartDirections F l) y i) =
        fun y i => ∑ l, σ l • directionMove (chartDirections F l) y i := by
      funext y i
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      have := congrFun (congrFun (sum_chartCoordinates_smul_directionMove hs dw (fun _ _ => 0)) y) i
      rw [this, zero_add]
    rw [hm]
    refine cellEnergyShare_congr a Y (chartedField_congr hcover hL hs0 _ fun b hb => ?_)
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    rw [sum_chartCoordinates_smul_directionCoordinate dw _ b.1 b.2 hb, add_assoc]
end YangMills.Construction.ColdStepAtMirrorFrames
end
