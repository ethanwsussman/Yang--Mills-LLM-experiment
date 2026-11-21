import YangMills.Construction.ColdStepAtMirrorFrames.FramesAgainstTheLeastField
import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages YangMills.Construction.Interpolation
variable {F : BlockFrame}
structure FramesNearAtTop (L : ℕ) (a σ C ω : ℝ) (c : ColdChainParameters) (m : ℕ) (V : F.GaugeField F.top) :
    Prop where
  small : ∀ star, FrameSmallness star a c.ρA c.δ₂ c.κ₂ C σ c.Kk m V
  gap : ∀ b ∈ chordBonds (finiteCells F), ‖frameGap a c.ρA m b V‖ ≤ ω
  gap_decay : ∀ b ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (e : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions),
    1 ≤ k → k ≤ 3 → AreUnitVectors X →
    ‖bondDeriv (frameGap a c.ρA m b) V e X‖ ≤
      ω * Real.exp (-(c.δ₂ / 4 * bondListDistance (enclosingCell b.1) e))
  between : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
    IsAdmissibleChartPoint L c.σA (fun z i => interpolatedFrame θ a c.ρA m (z, i) V) V
def FrameDensityOnTorus : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L → ∀ C : ℝ, 1 ≤ C →
    ∃ Bk : ℕ → ℝ, (∀ k, 0 < Bk k) ∧
      ∀ (x σ ω s : ℝ) (m : ℕ) (F : BlockFrame) (V : F.GaugeField F.top), 0 ≤ x → 0 < s → s ≤ c.s₀ → 0 ≤ ω →
        ω ≤ 1 → IsBlockTorus L F → IsSmallCurvature s V → FramesNearAtTop L a σ C ω c m V → ∀ Y : F.Cell,
        IsBondAnalyticAt (frameDensity false a c.ρA x m Y) V ∧
        (∀ (k : ℕ) (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
          AreUnitVectors X →
          |bondDeriv (frameDensity false a c.ρA x m Y) V e X| ≤
            x * Bk 0 * ω * Real.exp (-(c.δ₂ / 4 * bondListDistance Y e))) ∧
        ∀ (k : ℕ) (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
          AreUnitVectors X →
          |bondDeriv (frameDensity false a c.ρA x m Y) V e X| ≤ x * Bk k
end YangMills.Construction.ColdStepAtMirrorFrames
end
