import YangMills.Construction.ColdStepAtMirrorFrames.FramesAgainstTheLeastField
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def frameBoundConstant (c : ColdChainParameters) : ℝ :=
  2 * c.K + c.Kk 3 + (16 ^ 3 + 1) * (c.Kk 1 + c.Kk 2 + c.Kk 3)
structure ReflectedFrameBounds (a σ : ℝ) (c : ColdChainParameters) (m : ℕ) (V : F.GaugeField F.top) :
    Prop where
  near_minimizer : FrameNearMinimizer a c.ρA c.δ₂ (frameBoundConstant c) σ m V
  deviation_le : ∀ b ∈ chordBonds (finiteCells F),
    ‖frameDeviation a c.ρA m b V‖ ≤ 2 * c.K * σ * Real.exp (-(c.δ₂ * m))
  minimizing : ∀ y : F.Cell, IsMinimizingChart a (finiteCells (reflectedFrame F m)) (reflectedField m y V) c.ρA
    (minimizingCoordinates a (finiteCells (reflectedFrame F m)) (reflectedField m y V) c.ρA)
  analytic : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (bondFrameCoord a c.ρA m b) V
  deriv_bound : ∀ b ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (e : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X →
      ‖bondDeriv (bondFrameCoord a c.ρA m b) V e X‖ ≤
        16 ^ k * c.Kk k * Real.exp (-(c.κ₂ * bondListDistance (enclosingCell b.1) e))
  deriv_eq_zero_off_box : ∀ b ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (e : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), (∃ l, ¬ IsCoarseBondInBox (enclosingCell b.1) m (e l)) →
      bondDeriv (bondFrameCoord a c.ρA m b) V e X = 0
def ReflectedFrameChainBounds : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → c.Admissible a L →
    ∀ (F : BlockFrame) (m : ℕ) (σ : ℝ) (V : F.GaugeField F.top), IsBlockTorus L F → 16 ≤ m → 0 < σ →
      5 / 4 * σ ≤ c.s₀ → (∀ i, 4 * m + 5 < F.extent i) → IsSmallCurvature (5 / 4 * σ) V →
        ReflectedFrameBounds a σ c m V
end YangMills.Construction.ColdStepAtMirrorFrames
end
