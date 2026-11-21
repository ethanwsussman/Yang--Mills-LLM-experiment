import YangMills.Construction.ClusterExpansionOfAStep.ConvexityOfASetting
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StepSettings
variable {R : StepSetup} {n : ℕ}
def ChartSetting.bondDist (s : ChartSetting R n) (b b' : s.free) : ℝ :=
  bondBlockDist (R := R) (n := n) b.1 b'.1
end YangMills.Construction.StepSettings
namespace YangMills.Construction.TorusLumps
def StepParameters.blockBondBound (ℓ : StepParameters) : ℝ := 4 * (2 * ℓ.side) ^ 4
def StepParameters.offDiagonalBound (ℓ : StepParameters) (lam C : ℝ) : ℝ :=
  8 * ℓ.blockBondBound * C / lam + (2 * ℓ.rt)⁻¹
end YangMills.Construction.TorusLumps
namespace YangMills.Construction.ClusterExpansionOfAStep
open StepSettings TorusLumps ColdStepAtMirrorFrames
def ChartPotentialConvex : Prop :=
  ∀ (R : StepSetup) (lam C : ℝ), 0 < R.params.threshold → 0 < R.params.rt → 0 < R.coupling → 0 < lam →
    ∀ (n : ℕ) [NeZero n] (s : ChartSetting R n) (u : FreeCoords s.free → ℝ), s.HasFullDecay u lam C →
      ∃ (Ψ : BondField s.free → ℝ) (K : s.free → s.free → ℝ),
        (∀ η, s.InBalls η → Ψ =ᶠ[nhds η] u) ∧
        IsUniformlyConvexDecaying R.ballRadius (R.coupling * lam / 8) R.params.rt s.bondDist Ψ K ∧
        (∀ b b', K b b' ≤ C * R.coupling) ∧
        ∀ b, ∑ b' ∈ Finset.univ.erase b, K b b' * Real.exp (R.params.rt * s.bondDist b b') ≤
          R.params.offDiagonalBound lam C * (R.coupling * lam / 8)
end YangMills.Construction.ClusterExpansionOfAStep
end
