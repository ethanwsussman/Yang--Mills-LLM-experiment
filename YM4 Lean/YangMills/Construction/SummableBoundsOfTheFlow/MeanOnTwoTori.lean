import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.MeanInTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BlockMeans
open BlockAverages ColdStepAtMirrorFrames
structure TwoTorusMeanBounds (star : Bool) (a ρA σ x δ ε : ℝ) (L t n₀ m : ℕ) (p : ℝ → ℝ)
    (φ h : LocalFamily) : Prop where
  centred_close : ∀ F F', IsCubicTopTorus L t n₀ F → IsCubicTopTorus L t n₀ F' →
    ∀ (Y : F.Cell) (Y' : F'.Cell) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (r : ℕ),
    IsSmallCurvature (5 / 4 * σ) V → IsSmallCurvature (5 / 4 * σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
    |centredFamily (Estimates.conditionalExpansionMean star a ρA (σ / 64) x m p φ h) F Y V -
        centredFamily (Estimates.conditionalExpansionMean star a ρA (σ / 64) x m p φ h) F' Y' V'| ≤
      2⁻¹ ^ 4 * ε / torusDecayFactor L δ r
  locality : IsLocalOnTori L t n₀ (9 / 8 * σ) (centredFamily (Estimates.conditionalExpansionMean star a ρA (σ / 64) x m p φ h))
    fun r => 2⁻¹ ^ 4 * ε / torusDecayFactor L δ r
def TwoTorusMeanBoundsAt (P : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (φ h : LocalFamily) (ε : ℝ) (star : Bool), P.coupling ≤ x → 0 < ε →
    FamilyNorms.IsNormBoundedLocalFamily P.L t P.n₀ P.σ P.decayRate P.E (P.E / P.η₃) φ →
    IsRegularFamily P.L t P.n₀ P.σ P.decayRate ε (ε / P.η₃) h →
    TwoTorusMeanBounds star P.a P.chainParams.ρA P.σ x P.decayRate ε P.L t P.n₀ (frameRadius x) P.p φ h
def twoTorusMeanStatement : Prop := EventuallyInParameters TwoTorusMeanBoundsAt
end YangMills.Construction.BlockMeans
end
