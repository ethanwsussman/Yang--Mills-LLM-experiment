import YangMills.Construction.RunningCouplingSlope.CoordinatesOfTheStepsOfAChainForm
import Mathlib
set_option autoImplicit false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames
variable {F : BlockFrame}
def leftExpAction {j : ℕ} (A : F.Site j → Fin 4 → imaginaryQuaternions) (W : F.GaugeField j) :
    F.GaugeField j :=
  fun x i => expUnit (A x i) * W x i
def excessEnergy (a : ℝ) (W : F.GaugeField F.depth) (V : F.GaugeField F.top) : ℝ :=
  blockEnergy a (finiteCells F) F.depth W V - minimalAction a (finiteCells F) F.top V
def excessHessian (a : ℝ) (W : F.GaugeField F.depth) (V : F.GaugeField F.top)
    (A : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) : ℝ :=
  deriv (deriv fun r : ℝ => excessEnergy a (leftExpAction (r • A) W) (leftExpAction (r • v) V)) 0
abbrev stepMinimizer (a ρ : ℝ) (V : F.GaugeField F.top) : F.GaugeField F.depth :=
  fieldAboveFrame true a ρ 0 V 0
abbrev TopCoord (F : BlockFrame) : Type := ↥(innerBonds (finiteCells F) F.top) × Fin 3
def topCoords (v : F.Site F.top → Fin 4 → imaginaryQuaternions) : TopCoord F → ℝ :=
  fun e => imaginaryComponents (v e.1.1.1 e.1.1.2 : ℍ[ℝ]) e.2
def covariantDifference (W : F.GaugeField F.depth) (γ : F.Site F.depth → imaginaryQuaternions)
    (b : F.Site F.depth × Fin 4) : ℍ[ℝ] :=
  (W b.1 b.2 : ℍ[ℝ]) * (γ (b.1 + unitStep F.depth b.2) : ℍ[ℝ]) *
      (((W b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
    (γ b.1 : ℍ[ℝ])
def chartTangentCoords (a ρ : ℝ) (V : F.GaugeField F.top) (x : ReferenceDensity.ChartCoord F → ℝ) :
    ReferenceDensity.ChartCoord F → ℝ :=
  fun i => imaginaryComponents (expLeftDeriv (coordsAboveFrame true a ρ 0 V 0 i.1.1.1 i.1.1.2 : ℍ[ℝ])
    (toImaginary (WithLp.toLp 2 fun c => x (i.1, c)) : ℍ[ℝ])) i.2
def frameVelocityOfForm {L n k : ℕ} (j : ℕ) {l : ℕ} (B : Tower.Edge L n k j → Matrices.ComplexMatrix2) :
    F.Site l → Fin 4 → imaginaryQuaternions :=
  fun x i => toImaginary (WithLp.toLp 2 (suTwoComponents (B (edgeOfCoords j (x, i)))))
end RunningCouplingSlope
end YangMills.Construction
end
