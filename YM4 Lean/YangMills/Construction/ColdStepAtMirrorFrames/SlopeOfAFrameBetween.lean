import YangMills.Construction.ColdStepAtMirrorFrames.MirrorFrameAgainstTheChain
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.Interpolation
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def energyAlongInterpolatedBond (s a ρ : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions)
    (V : F.GaugeField F.top) (u : ℝ) : ℝ :=
  chartedEnergy a (Function.update (fun z i => interpolatedFrame s a ρ m (z, i) V) b.1
    (Function.update (fun i => interpolatedFrame s a ρ m (b.1, i) V) b.2
      (interpolatedFrame s a ρ m b V + u • e))) V
def interpolatedSlopeBounds : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L → ∃ C σ₁ : ℝ, 1 ≤ C ∧ 0 < σ₁ ∧
    ∀ (σ : ℝ) (m : ℕ) (F : BlockFrame) (V : F.GaugeField F.top), 0 < σ → σ ≤ σ₁ → 16 ≤ m →
      frameDecayBound (frameBoundConstant c) c.δ₂ m ≤ 2⁻¹ ^ 10 * σ → IsBlockTorus L F →
      IsSmallCurvature (5 / 4 * σ) V →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ chordBonds (finiteCells F), ∀ e : imaginaryQuaternions,
        DifferentiableAt ℝ (energyAlongInterpolatedBond s a c.ρA m b e V) 0 ∧
        ContDiffThreeAlongBonds (interpolatedSlope s a c.ρA m b e) V ∧
        (‖e‖ = 1 → ∀ (k : ℕ) (e' : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
          AreUnitVectors X →
          |bondDeriv (interpolatedSlope s a c.ρA m b e) V e' X| ≤
            C * frameDecayBound (frameBoundConstant c) c.δ₂ m *
              Real.exp (-(c.δ₂ / 8 * bondListDistance (enclosingCell b.1) e')))
end YangMills.Construction.ColdStepAtMirrorFrames
end
