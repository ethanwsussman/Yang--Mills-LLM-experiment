import YangMills.Construction.SummableBoundsOfTheFlow.MixturesOfTwoLevels
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.TorusFields
namespace YangMills.Construction.TwoLevelMixtures
variable {n : ℕ}
open Classical in
def levelHessianEntry [NeZero n] (a : ℝ) (L u : ℕ) [NeZero L] (b b' : TorusBond (n * L)) : ℝ :=
  interpForm a L u 0 (Pi.single b 1) (Pi.single b' 1)
def decayWeightExcess (L : ℕ) (r : ℝ) (b b' : TorusBond (n * L)) : ℝ :=
  Real.exp (2 * r * supDist (TorusLumps.parentBlock L b.1) (TorusLumps.parentBlock L b'.1)) - 1
def LevelExpansionsBounded (T : ColdStepAtMirrorFrames.StepParameters) [NeZero T.L] (r : ℝ) : Prop :=
  ∀ (u n : ℕ) [NeZero n], 64 ≤ n → ∀ b ∈ StepCosts.chartBonds T.L n,
    ∑ b' ∈ StepCosts.chartBonds T.L n, |levelHessianEntry T.a T.L u b b'| * decayWeightExcess T.L r b b' ≤ T.lam / 2 ∧
    ∑ b' ∈ StepCosts.chartBonds T.L n, |levelHessianEntry T.a T.L u b' b| * decayWeightExcess T.L r b b' ≤ T.lam / 2
end YangMills.Construction.TwoLevelMixtures
end
