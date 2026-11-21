import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.ObservableOfTheFrameGap
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.FamilyNorms MeasureTheory
namespace YangMills.Construction.Interpolation
variable {F : BlockFrame}
def interpolatedStepIntegrand (s a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (φ : LocalFamily)
    (V : F.GaugeField F.top) (w : StepVariable (finiteCells F)) : ℝ :=
  lowerBoltzmann a x φ (finiteCells F) (chartedField (stepCoordinates w) V) *
    (∏ b : ↥(chordBonds (finiteCells F)), cutoffFactor ρ p
      ‖((toImaginary (w b) : imaginaryQuaternions) : ℍ[ℝ]) -
        (interpolatedFrame s a ρA m b.1 V : imaginaryQuaternions)‖) *
    (∏ c ∈ innerBonds (finiteCells F) F.top,
      stepKernel a x (chartedField (stepCoordinates w) V) V c) *
    ∏ b : ↥(chordBonds (finiteCells F)), haarLogDensity (w b)
def interpolatedStepIntegral (s a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (φ : LocalFamily)
    (V : F.GaugeField F.top) : ℝ :=
  ∫ w, interpolatedStepIntegrand s a ρA ρ x m p φ V w
def blockGapMean (s a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (φ : LocalFamily) (Y : F.Cell)
    (V : F.GaugeField F.top) : ℝ :=
  cutoffMean ρ p (familyLawExponent s a ρA x m φ V) fun η => blockGapObservable a ρA m p Y V η
def blockGapDensity (a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (φ : LocalFamily) : TopLevelFamily :=
  fun _ Y V => ∫ s in (0 : ℝ)..1, blockGapMean s a ρA ρ x m p φ Y V
structure BlockGapIntegrable (a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (φ : LocalFamily)
    (V : F.GaugeField F.top) : Prop where
  integrable : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → Integrable (interpolatedStepIntegrand s a ρA ρ x m p φ V)
  integral_pos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < interpolatedStepIntegral s a ρA ρ x m p φ V
  law : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → Integrable (fun η : StepVariable (finiteCells F) =>
      cutoffWeight ρ p η * Real.exp (- familyLawExponent s a ρA x m φ V η)) ∧
    0 < ∫ η : StepVariable (finiteCells F),
      cutoffWeight ρ p η * Real.exp (- familyLawExponent s a ρA x m φ V η)
  observable : ∀ (s : ℝ) (Y : F.Cell), 0 ≤ s → s ≤ 1 →
    Integrable (fun η : StepVariable (finiteCells F) => blockGapObservable a ρA m p Y V η *
      (cutoffWeight ρ p η * Real.exp (- familyLawExponent s a ρA x m φ V η)))
  intervalIntegrable : ∀ Y : F.Cell,
    IntervalIntegrable (fun s => blockGapMean s a ρA ρ x m p φ Y V) volume 0 1
structure FrameInterpolationEstimates (a ρA σ x κ δ ω : ℝ) (CN : ℕ → ℝ) (L t n₀ m : ℕ)
    (p : ℝ → ℝ) (φ : LocalFamily) : Prop where
  integrability : ∀ F, IsCubicTopTorus L t n₀ F → ∀ V : F.GaugeField F.top,
    IsSmallCurvature (5 / 4 * σ) V → BlockGapIntegrable a ρA (σ / 64) x m p φ V
  log_eq : ∀ F, IsCubicTopTorus L t n₀ F → ∀ V : F.GaugeField F.top,
    IsSmallCurvature (5 / 4 * σ) V →
    Real.log (stepIntegral a ρA (σ / 64) x m p φ (finiteCells F) V) =
      Real.log (interpolatedStepIntegral 0 a ρA (σ / 64) x m p φ V) +
        ∑ Y ∈ finiteCells F, blockGapDensity a ρA (σ / 64) x m p φ F Y V
  eq_zero_of_small : ∀ F, IsCubicTopTorus L t n₀ F → (¬ ∀ i, 4 * m + 5 < F.extent i) →
    ∀ (Y : F.Cell) (V : F.GaugeField F.top),
    IsSmallCurvature (5 / 4 * σ) V → blockGapDensity a ρA (σ / 64) x m p φ F Y V = 0
  isLocalDensity : IsLocalDensity L t n₀ (5 / 4 * σ) (blockGapDensity a ρA (σ / 64) x m p φ)
  eq_zero_at_uniform : ∀ F, IsCubicTopTorus L t n₀ F → ∀ Y : F.Cell,
    blockGapDensity a ρA (σ / 64) x m p φ F Y (flatTopField (F := F)) = 0
  decay : ∀ (N : ℕ) (F : BlockFrame), IsCubicTopTorus L t n₀ F → ∀ (Y : F.Cell)
    (V : F.GaugeField F.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), IsSmallCurvature (5 / 4 * σ) V → k ≤ 3 →
    AreUnitVectors X →
    |bondDeriv (blockGapDensity a ρA (σ / 64) x m p φ F Y) V c X| ≤
      CN N * (x ^ N)⁻¹ * ω * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c))
  sub_le : ∀ (N : ℕ) (F F' : BlockFrame), IsCubicTopTorus L t n₀ F → IsCubicTopTorus L t n₀ F' →
    ∀ (Y : F.Cell) (Y' : F'.Cell) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (r : ℕ),
    IsSmallCurvature (5 / 4 * σ) V → IsSmallCurvature (5 / 4 * σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
    |blockGapDensity a ρA (σ / 64) x m p φ F Y V -
        blockGapDensity a ρA (σ / 64) x m p φ F' Y' V'| ≤
      CN N * (x ^ N)⁻¹ / torusDecayFactor L δ r
  locality : ∀ N : ℕ, IsLocalOnTori L t n₀ (9 / 8 * σ) (blockGapDensity a ρA (σ / 64) x m p φ)
    fun r => CN N * (x ^ N)⁻¹ / torusDecayFactor L δ r
  flat_limit : ∃ q : BondBilinearForm,
    (∀ b b' X X', Filter.Tendsto
      (fun n => secondDerivAtUniform (blockGapDensity a ρA (σ / 64) x m p φ) L t n b b' X X')
      Filter.atTop (nhds (q b b' X X'))) ∧
    ∀ (X : imaginaryQuaternions) (μ ν : Fin 4) (B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
      ‖X‖ = 1 → μ < ν → IsLinearPotential (constantPlaneCurvature X μ ν) B →
      ∃ v : ℝ, HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        q e.1 e.2 (B e.1) (B e.2)) v ∧ ∀ N : ℕ, |v| ≤ CN N * (x ^ N)⁻¹
def FrameInterpolationAt (a ρA κ δ δ₂ η₃ σ E y₁ : ℝ) (CN : ℕ → ℝ) (L n₀ : ℕ) (p : ℝ → ℝ) :
    Prop :=
  ∀ (t : ℕ) (x : ℝ) (φ : LocalFamily), y₁ ≤ x →
    IsNormBoundedLocalFamily L t n₀ σ δ E (E / η₃) φ →
    FrameInterpolationEstimates a ρA σ x κ δ (Real.exp (-(δ₂ / 4 * frameRadius x))) CN L t n₀
      (frameRadius x) p φ
def frameInterpolationStatement : Prop :=
  EventuallyInParameters fun T => ∃ CN : ℕ → ℝ, (∀ N, 0 < CN N) ∧
    FrameInterpolationAt T.a T.chainParams.ρA T.κ T.decayRate T.chainParams.δ₂ T.η₃ T.σ T.E T.coupling CN
      T.L T.n₀ T.p
end YangMills.Construction.Interpolation
end
