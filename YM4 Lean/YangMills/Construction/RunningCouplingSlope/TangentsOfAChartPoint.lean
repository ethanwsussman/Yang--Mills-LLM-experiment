import YangMills.Construction.RunningCouplingSlope.TowerOfConstantCurvatureForm
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.ReferenceDensity
variable {F : BlockFrame}
def leftExpDifferential (w : imaginaryQuaternions) : Matrix (Fin 3) (Fin 3) ℝ := fun m m' =>
  imaginaryCoord m (fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (w : ℍ[ℝ]) ((imaginaryBasis m' : imaginaryQuaternions) : ℍ[ℝ]) *
    NormedSpace.exp (-(w : ℍ[ℝ])))
def chartDifferential (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) :
    Matrix (LinkComponent F F.depth) (ChartCoord F) ℝ := fun p q =>
  if p.1.1 = q.1.1 then leftExpDifferential (w q.1.1.1 q.1.1.2) p.2 q.2 else 0
def offCentreGaugeDifferential (W : F.GaugeField F.depth) :
    Matrix (LinkComponent F F.depth) (OffCentreComponent F F.depth F.top) ℝ :=
  (gaugeDifferential W).submatrix id Subtype.val
open Classical in
def ChartAndGaugeDifferentialsBasis : Prop :=
  ∀ F : BlockFrame, Odd F.blockSide → (∀ i, 2 ≤ F.extent i) →
    ∃ (e : ChartCoord F ⊕ OffCentreComponent F F.depth F.top ≃ LinkComponent F F.depth) (d : ℝ), d ≠ 0 ∧
      ∀ (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (W : F.GaugeField F.depth),
        (∀ b, IsAxialTreeBond b → W b.1 b.2 = 1) →
        ((Matrix.fromCols (chartDifferential w) (offCentreGaugeDifferential W)).submatrix id e.symm).det =
          d * ∏ b : ↥(chordBonds (finiteCells F)), (leftExpDifferential (w b.1.1 b.1.2)).det
end YangMills.Construction.RunningCouplingSlope
end
