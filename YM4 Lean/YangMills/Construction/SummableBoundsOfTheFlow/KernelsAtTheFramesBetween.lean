import YangMills.Construction.SummableBoundsOfTheFlow.TransportAtSixDerivatives
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
variable {F : BlockFrame}
def interpolatedEnergy (s a ρA : ℝ) (m : ℕ) (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) : ℝ :=
  chartedEnergy a (interpolatedCoords s a ρA m V η) V
def logContourNorm (s a ρA : ℝ) (m : ℕ) (c : F.Site F.top × Fin 4) (η : StepVariable (finiteCells F))
    (V : F.GaugeField F.top) : ℝ :=
  Real.log ‖contourAverage (interpolatedField s a ρA m V η) c‖
def contourHaarGap (s a ρA x : ℝ) (m : ℕ) (c : F.Site F.top × Fin 4) (η : StepVariable (finiteCells F))
    (V : F.GaugeField F.top) : ℝ :=
  haarGap (a * x * ‖contourAverage (interpolatedField s a ρA m V η) c‖)
def interpolatedHaarLogRatio (s a ρA : ℝ) (m : ℕ) (b : ↥(chordBonds (finiteCells F)))
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) : ℝ :=
  haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2)
def HasDecayingKernelAt {l j : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (B r : ℝ)
    (P : Finset F.Cell) (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top)
    (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions) : Prop :=
  ContDiffAt ℝ (l + j : ℕ) (jointDisplacement G η V b u c X) 0 ∧
    |jointMixedDeriv G η V b u c X| ≤
      B * Real.exp (-(r * cellSetDiameter (P ∪ chordBondCells b ∪ topBondCells c)))
structure HasInterpolationKernels (s a ρA κ κ₂ rE x : ℝ) (m : ℕ) (K : ℕ → ℝ) (D : ℕ → ℕ → ℝ)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) : Prop where
  analytic : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (interpolatedFrame s a ρA m b) V
  frame_deriv : ∀ b ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X →
    ‖bondDeriv (interpolatedFrame s a ρA m b) V c X‖ ≤
      K k * Real.exp (-(κ₂ * bondListDistance (enclosingCell b.1) c))
  energy : ∀ (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions), 2 ≤ l →
    (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
    HasDecayingKernelAt (interpolatedEnergy s a ρA m) (D l j) rE ∅ η V b u c X
  logContour : ∀ (c₀ : F.Site F.top × Fin 4) (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions), 1 ≤ l + j →
    (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
    HasDecayingKernelAt (logContourNorm s a ρA m c₀) (D l j) (2 ^ 8 * κ) {c₀.1} η V b u c X
  gap : ∀ (c₀ : F.Site F.top × Fin 4) (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions), 1 ≤ l + j →
    (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
    HasDecayingKernelAt (contourHaarGap s a ρA x m c₀) (D l j) (2 ^ 8 * κ) {c₀.1} η V b u c X
  haar : ∀ (b₀ : ↥(chordBonds (finiteCells F))) (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions), 1 ≤ l + j →
    (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
    HasDecayingKernelAt (interpolatedHaarLogRatio s a ρA m b₀) (D l j) (2 ^ 8 * κ)
      {enclosingCell b₀.1.1} η V b u c X
def interpolationKernelBoundsAt (T : StepParameters) (K : ℕ → ℝ) (D : ℕ → ℕ → ℝ) : Prop :=
  ∀ (x : ℝ) (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ) (η : StepVariable (finiteCells F)),
    T.coupling ≤ x → IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
    (∀ b, ‖η b‖ ≤ T.ballRadius) →
    HasInterpolationKernels s T.a T.chainParams.ρA T.κ T.chainParams.κ₂ T.chainParams.δ₂ x
      (frameRadius x) K D V η
def interpolationKernelBoundsStatement : Prop :=
  ∃ (K : StepParameters → ℕ → ℝ) (D : StepParameters → ℕ → ℕ → ℝ), (∀ T k, 0 < K T k) ∧
    (∀ T l j, 0 < D T l j) ∧
    EventuallyInParameters fun T =>
      interpolationKernelBoundsAt T (K (rateParameters T)) (D (rateParameters T))
end Interpolation
end YangMills.Construction
end
