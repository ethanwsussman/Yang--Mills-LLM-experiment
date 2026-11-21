import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.MeanInTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.BlockMeans
open BlockAverages ColdStepAtMirrorFrames
structure SingleTorusMeanBounds (star : Bool) (a ρA σ x κ δ ε ε₃ CE : ℝ) (L t n₀ m : ℕ) (p : ℝ → ℝ)
    (φ h : LocalFamily) : Prop where
  isMean : ∀ F, IsCubicTopTorus L t n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
    IsSmallCurvature (5 / 4 * σ) V → Estimates.HasConditionalMean star a ρA (σ / 64) x m p φ h Y V
  density : IsLocalDensity L t n₀ (5 / 4 * σ) (Estimates.conditionalExpansionMean star a ρA (σ / 64) x m p φ h)
  near_block : ∀ F, IsCubicTopTorus L t n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), IsSmallCurvature (5 / 4 * σ) V → k ≤ 2 →
    AreUnitVectors X →
    |bondDeriv (Estimates.conditionalExpansionMean star a ρA (σ / 64) x m p φ h F Y) V c X -
        bondDeriv (cellCentredExpansion star a ρA m h Y 0) V c X| ≤
      CE * ε * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c))
  decay : ColdStepAtMirrorFrames.DerivDecay L t n₀ (5 / 4 * σ) (Estimates.conditionalExpansionMean star a ρA (σ / 64) x m p φ h) fun k n =>
    2⁻¹ ^ 6 * (if k = 3 then ε₃ else ε) / torusDecayFactor L δ n +
      CE * ε * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ / 2 ^ 6 * n))
def SingleTorusMeanBoundsAt (P : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (φ h : LocalFamily) (ε : ℝ) (star : Bool), P.coupling ≤ x → 0 < ε →
    FamilyNorms.IsNormBoundedLocalFamily P.L t P.n₀ P.σ P.decayRate P.E (P.E / P.η₃) φ →
    IsRegularFamily P.L t P.n₀ P.σ P.decayRate ε (ε / P.η₃) h →
    SingleTorusMeanBounds star P.a P.chainParams.ρA P.σ x P.κ P.decayRate ε (ε / P.η₃) P.CE P.L t P.n₀
      (frameRadius x) P.p φ h
def singleTorusMeanStatement : Prop := EventuallyInParameters SingleTorusMeanBoundsAt
end YangMills.Construction.BlockMeans
end
