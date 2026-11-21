import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.MeanInTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames FamilyNorms Estimates MeasureTheory
namespace BlockMeans
variable {F : BlockFrame}
structure ConditionalMeanBounds (star : Bool) (a ρA σ x κ δ ε ε₃ CE : ℝ) (L t n₀ m : ℕ) (p : ℝ → ℝ)
    (φ h : LocalFamily) : Prop where
  isMean : ∀ F, IsCubicTopTorus L t n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
    IsSmallCurvature (5 / 4 * σ) V → HasConditionalMean star a ρA (σ / 64) x m p φ h Y V
  density : IsLocalDensity L t n₀ (5 / 4 * σ) (conditionalExpansionMean star a ρA (σ / 64) x m p φ h)
  near_block : ∀ F, IsCubicTopTorus L t n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), IsSmallCurvature (5 / 4 * σ) V → k ≤ 2 →
    AreUnitVectors X →
    |bondDeriv (conditionalExpansionMean star a ρA (σ / 64) x m p φ h F Y) V c X -
        bondDeriv (cellCentredExpansion star a ρA m h Y 0) V c X| ≤
      CE * ε * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c))
  decay : DerivDecay L t n₀ (5 / 4 * σ) (conditionalExpansionMean star a ρA (σ / 64) x m p φ h) fun k n =>
    2⁻¹ ^ 6 * (if k = 3 then ε₃ else ε) / torusDecayFactor L δ n +
      CE * ε * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ / 2 ^ 6 * n))
  centred_close : ∀ F F', IsCubicTopTorus L t n₀ F → IsCubicTopTorus L t n₀ F' →
    ∀ (Y : F.Cell) (Y' : F'.Cell) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (r : ℕ),
    IsSmallCurvature (5 / 4 * σ) V → IsSmallCurvature (5 / 4 * σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
    |centredFamily (conditionalExpansionMean star a ρA (σ / 64) x m p φ h) F Y V -
        centredFamily (conditionalExpansionMean star a ρA (σ / 64) x m p φ h) F' Y' V'| ≤
      2⁻¹ ^ 4 * ε / torusDecayFactor L δ r
  locality : IsLocalOnTori L t n₀ (9 / 8 * σ) (centredFamily (conditionalExpansionMean star a ρA (σ / 64) x m p φ h))
    fun r => 2⁻¹ ^ 4 * ε / torusDecayFactor L δ r
  flat_form : ∃ q : BondBilinearForm,
    (∀ b b' X X', Filter.Tendsto (fun n => secondDerivAtUniform (conditionalExpansionMean star a ρA (σ / 64) x m p φ h)
      L t n b b' X X') Filter.atTop (nhds (q b b' X X'))) ∧
    ∀ (X : imaginaryQuaternions) (μ ν : Fin 4) (B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
      ‖X‖ = 1 → μ < ν → IsLinearPotential (constantPlaneCurvature X μ ν) B →
      ∃ v : ℝ, HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        q e.1 e.2 (B e.1) (B e.2)) v ∧ |v| ≤ CE * ε * x ^ (-(1 / 2 : ℝ))
def ConditionalMeanBoundsAt (a ρA κ δ η₃ σ E CE y₁ : ℝ) (L n₀ : ℕ) (p : ℝ → ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (φ h : LocalFamily) (ε : ℝ) (star : Bool), y₁ ≤ x → 0 < ε →
    IsNormBoundedLocalFamily L t n₀ σ δ E (E / η₃) φ → IsRegularFamily L t n₀ σ δ ε (ε / η₃) h →
    ConditionalMeanBounds star a ρA σ x κ δ ε (ε / η₃) CE L t n₀ (frameRadius x) p φ h
def conditionalMeanStatement : Prop :=
  EventuallyInParameters fun T => ConditionalMeanBoundsAt T.a T.chainParams.ρA T.κ T.decayRate T.η₃ T.σ T.E T.CE
    T.coupling T.L T.n₀ T.p
end BlockMeans
end YangMills.Construction
end
