import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.MomentLaw
def weightedFormSize {n : ℕ} [NeZero n] (κ : ℝ) (Y : TorusFields.TorusSite n)
    (A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) : ℝ :=
  ∑ e : TorusFields.TorusBond n, Real.exp (-(κ * (TorusFields.supDist Y e.1 : ℝ))) * ‖A e‖
open Classical in
def crossingComponent (P : TorusLumps.StepParameters) {n : ℕ}
    (A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions)
    (b : TorusFields.TorusBond (n * P.side)) : BlockAverages.imaginaryQuaternions :=
  if BlockAverages.IsCrossingBond (F := TorusLumps.stepBlockFrame P.side n)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame P.side n) 0 b.1, b.2) then
    A (TorusLumps.parentBlock P.side b.1, b.2) else 0
def frameOverCutTopStatement : Prop :=
  ∀ (P : TorusLumps.StepParameters) (c : ColdStepAtMirrorFrames.ColdChainParameters), 1 ≤ P.coupling → Odd P.side →
    c.Admissible P.coupling P.side → ∃ K : ℝ, 0 ≤ K ∧
    ∀ (t m n : ℕ) [NeZero n] (A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions),
      16 ≤ m → 4 * m + 5 < n → 64 ≤ n →
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 → TorusFields.IsCold c.s₀ (expField u A)) →
      (∀ b : TorusFields.TorusBond (n * P.side), b ∉ StepCosts.chartBonds P.side n →
        ResponseInTheExpansion.responseOfLieForm P.coupling c.ρA P.side t A b = 0) ∧
      ∀ b ∈ StepCosts.chartBonds P.side n,
        ‖((StepCosts.frameCoord P c.ρA t m (expField 1 A) b + crossingComponent P A b -
            ResponseInTheExpansion.responseOfLieForm P.coupling c.ρA P.side t A b :
              BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤
          K * weightedFormSize (c.δ₁ / 2) (TorusLumps.parentBlock P.side b.1) A ^ 2 +
            K * Real.exp (-(c.δ₂ * m)) ∧
        ‖((ResponseInTheExpansion.responseOfLieForm P.coupling c.ρA P.side t A b - crossingComponent P A b :
              BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤
          K * weightedFormSize (c.δ₁ / 2) (TorusLumps.parentBlock P.side b.1) A
end YangMills.Construction.MomentLaw
end
