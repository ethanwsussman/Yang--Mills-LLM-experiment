import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.DisplayOfTheColdStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def interactionFamily (a ρA ρ lam x : ℝ) (m : ℕ) (p : ℝ → ℝ) (f : LocalFamily) : TopLevelFamily :=
  fun _ Y V => interactionDensity false a ρA ρ lam x m p f Y V
def expansionFamily (a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (f : LocalFamily) : TopLevelFamily :=
  fun _ Y V => expansionDensity false a ρA ρ x m p f Y V
def frameFamily (a ρA x : ℝ) (m : ℕ) : TopLevelFamily := fun _ Y V => frameDensity false a ρA x m Y V
structure ColdStepDensityConditions (a ρA ρ lam x σ κ δ δ₂ E E₃ Ct Cs CE : ℝ) (L t n₀ : ℕ) (p : ℝ → ℝ)
    (f : LocalFamily) (u s τ : TopLevelFamily) : Prop where
  regular : ∀ F, IsCubicTopTorus L t n₀ F → ∀ V : F.GaugeField F.top, IsSmallCurvature (9 / 8 * σ) V →
    (∀ b ∈ chordBonds (finiteCells F), ‖stepFrame false a ρA (frameRadius x) b V‖ + ρ < Real.pi) ∧
    ∃ M, IsRegularStep a ρA ρ lam x M (frameRadius x) p f V
  localDensity_u : IsLocalDensity L t n₀ (9 / 8 * σ) u
  localDensity_s : IsLocalDensity L t n₀ (9 / 8 * σ) s
  localDensity_τ : IsLocalDensity L t n₀ (9 / 8 * σ) τ
  abs_u_le : ∀ F, IsCubicTopTorus L t n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
    IsSmallCurvature (9 / 8 * σ) V → |u F Y V| ≤ Cs
  derivDecay_u : DerivDecay L t n₀ (9 / 8 * σ) u fun _ n => Cs * Real.exp (-(κ / 2 ^ 6 * n))
  localOnTori_u : IsLocalOnTori L t n₀ (9 / 8 * σ) u fun r => Cs * Real.exp (-(κ / 2 ^ 9 * r))
  derivDecay_s : DerivDecay L t n₀ (9 / 8 * σ) s fun k n =>
    2⁻¹ ^ 6 * (if k = 3 then E₃ else E) / torusDecayFactor L δ n +
      CE * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ / 2 ^ 6 * n))
  localOnTori_s : IsLocalOnTori L t n₀ (9 / 8 * σ) (centredFamily s) fun r =>
    2⁻¹ ^ 4 * E / torusDecayFactor L δ r
  abs_τ_le : ∀ F, IsCubicTopTorus L t n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
    IsSmallCurvature (9 / 8 * σ) V →
    |τ F Y V| ≤ Ct * x * Real.exp (-(δ₂ / 8 * frameRadius x))
  derivDecay_τ : DerivDecay L t n₀ (9 / 8 * σ) τ fun _ n =>
    Ct * x * Real.exp (-(δ₂ / 8 * frameRadius x)) / torusDecayFactor L δ n
  localOnTori_τ : IsLocalOnTori L t n₀ (9 / 8 * σ) τ fun r =>
    Ct * x * Real.exp (-(δ₂ / 8 * frameRadius x)) / torusDecayFactor L δ r
  τ_eq_zero_of_small : ∀ F, IsCubicTopTorus L t n₀ F → (¬ ∀ i, 4 * frameRadius x + 5 < F.extent i) →
    ∀ (Y : F.Cell) (V : F.GaugeField F.top), IsSmallCurvature (9 / 8 * σ) V → τ F Y V = 0
  flat_limit : ∃ q : BondBilinearForm,
    (∀ b b' X X', Filter.Tendsto (fun n => secondDerivAtUniform s L t n b b' X X') Filter.atTop
      (nhds (q b b' X X'))) ∧
    ∀ (X : imaginaryQuaternions) (μ ν : Fin 4) (B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
      ‖X‖ = 1 → μ < ν → IsLinearPotential (constantPlaneCurvature X μ ν) B →
      ∃ v : ℝ, HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        q e.1 e.2 (B e.1) (B e.2)) v ∧ |v| ≤ CE * x ^ (-(1 / 2 : ℝ))
def StepParameters.interactionFamily (T : StepParameters) (x : ℝ) (f : LocalFamily) : TopLevelFamily :=
  YangMills.Construction.ColdStepAtMirrorFrames.interactionFamily T.a T.chainParams.ρA T.ballRadius
    T.chainParams.lam x (frameRadius x) T.p f
def StepParameters.expansionFamily (T : StepParameters) (x : ℝ) (f : LocalFamily) : TopLevelFamily :=
  YangMills.Construction.ColdStepAtMirrorFrames.expansionFamily T.a T.chainParams.ρA T.ballRadius x (frameRadius x) T.p f
def StepParameters.frameFamily (T : StepParameters) (x : ℝ) : TopLevelFamily :=
  YangMills.Construction.ColdStepAtMirrorFrames.frameFamily T.a T.chainParams.ρA x (frameRadius x)
def StepParameters.IsRegularExpansion (T : StepParameters) (t : ℕ) (f : LocalFamily) : Prop :=
  IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f
def StepParameters.ForAllSteps (T : StepParameters) (Q : ℕ → ℝ → LocalFamily → Prop) : Prop :=
  ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ f : LocalFamily, T.IsRegularExpansion t f → Q t x f
def DensityConditionsAt (T : StepParameters) : Prop :=
  T.ForAllSteps fun t x f =>
    ColdStepDensityConditions T.a T.chainParams.ρA T.ballRadius T.chainParams.lam x T.σ T.κ T.decayRate
      T.chainParams.δ₂ T.E T.energyRatio T.Ct T.Cs T.CE
      T.L t T.n₀ T.p f (T.interactionFamily x f) (T.expansionFamily x f) (T.frameFamily x)
def RegularStepAt (T : StepParameters) : Prop :=
  T.ForAllSteps fun t x f => ∀ F, IsCubicTopTorus T.L t T.n₀ F → ∀ V : F.GaugeField F.top,
    IsSmallCurvature (9 / 8 * T.σ) V →
    (∀ b ∈ chordBonds (finiteCells F),
      ‖stepFrame false T.a T.chainParams.ρA (frameRadius x) b V‖ + T.ballRadius < Real.pi) ∧
    ∃ M, IsRegularStep T.a T.chainParams.ρA T.ballRadius T.chainParams.lam x M (frameRadius x) T.p f V
def MeansAreLocalDensitiesAt (T : StepParameters) : Prop :=
  T.ForAllSteps fun t x f =>
    IsLocalDensity T.L t T.n₀ (9 / 8 * T.σ) (T.interactionFamily x f) ∧
    IsLocalDensity T.L t T.n₀ (9 / 8 * T.σ) (T.expansionFamily x f)
def InteractionDensityBoundsAt (T : StepParameters) : Prop :=
  T.ForAllSteps fun t x f =>
    (∀ F, IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
      IsSmallCurvature (9 / 8 * T.σ) V → |T.interactionFamily x f F Y V| ≤ T.Cs) ∧
    DerivDecay T.L t T.n₀ (9 / 8 * T.σ) (T.interactionFamily x f)
      (fun _ n => T.Cs * Real.exp (-(T.κ / 2 ^ 6 * n))) ∧
    IsLocalOnTori T.L t T.n₀ (9 / 8 * T.σ) (T.interactionFamily x f)
      (fun r => T.Cs * Real.exp (-(T.κ / 2 ^ 9 * r)))
def ExpansionDensityBoundsAt (T : StepParameters) : Prop :=
  T.ForAllSteps fun t x f =>
    DerivDecay T.L t T.n₀ (9 / 8 * T.σ) (T.expansionFamily x f) (fun k n =>
      2⁻¹ ^ 6 * (if k = 3 then T.energyRatio else T.E) / torusDecayFactor T.L T.decayRate n +
        T.CE * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 * n))) ∧
    IsLocalOnTori T.L t T.n₀ (9 / 8 * T.σ) (centredFamily (T.expansionFamily x f))
      (fun r => 2⁻¹ ^ 4 * T.E / torusDecayFactor T.L T.decayRate r)
def FrameDensityBoundsAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x →
    IsLocalDensity T.L t T.n₀ (9 / 8 * T.σ) (T.frameFamily x) ∧
    (∀ F, IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
      IsSmallCurvature (9 / 8 * T.σ) V →
      |T.frameFamily x F Y V| ≤ T.Ct * x * Real.exp (-(T.chainParams.δ₂ / 8 * frameRadius x))) ∧
    DerivDecay T.L t T.n₀ (9 / 8 * T.σ) (T.frameFamily x) (fun _ n =>
      T.Ct * x * Real.exp (-(T.chainParams.δ₂ / 8 * frameRadius x)) / torusDecayFactor T.L T.decayRate n) ∧
    IsLocalOnTori T.L t T.n₀ (9 / 8 * T.σ) (T.frameFamily x) (fun r =>
      T.Ct * x * Real.exp (-(T.chainParams.δ₂ / 8 * frameRadius x)) / torusDecayFactor T.L T.decayRate r) ∧
    ∀ F, IsCubicTopTorus T.L t T.n₀ F → (¬ ∀ i, 4 * frameRadius x + 5 < F.extent i) →
      ∀ (Y : F.Cell) (V : F.GaugeField F.top), IsSmallCurvature (9 / 8 * T.σ) V → T.frameFamily x F Y V = 0
def FlatLimitOfExpansionDensityAt (T : StepParameters) : Prop :=
  T.ForAllSteps fun t x f => ∃ q : BondBilinearForm,
    (∀ b b' X X', Filter.Tendsto (fun n => secondDerivAtUniform (T.expansionFamily x f) T.L t n b b' X X')
      Filter.atTop (nhds (q b b' X X'))) ∧
    ∀ (X : imaginaryQuaternions) (μ ν : Fin 4) (B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
      ‖X‖ = 1 → μ < ν → IsLinearPotential (constantPlaneCurvature X μ ν) B →
      ∃ v : ℝ, HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        q e.1 e.2 (B e.1) (B e.2)) v ∧ |v| ≤ T.CE * x ^ (-(1 / 2 : ℝ))
end YangMills.Construction.ColdStepAtMirrorFrames
end
