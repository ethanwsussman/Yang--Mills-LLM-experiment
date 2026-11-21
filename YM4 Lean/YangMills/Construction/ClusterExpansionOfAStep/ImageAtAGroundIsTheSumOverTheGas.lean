import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames StepSettings StepGas StepCosts TorusLumps TorusFields
  RenormalizationStepParameters
abbrev ClusterExpansionOfAStep.CaseFunctional (R : StepSetup) (n : ℕ) : Type :=
  (W : TorusField (n * R.params.side)) → (support : Finset (TorusSite (n * R.params.side))) →
    (support → R.labels.Ω) → Finset (TorusBond (n * R.params.side)) → BaseChoice R.params.side n → ℝ≥0∞
variable {R : StepSetup} {n : ℕ} [NeZero n]
structure ClusterExpansionOfAStep.IsCaseFunctional (F : ClusterExpansionOfAStep.CaseFunctional R n) : Prop where
  measurable : ∀ (support : Finset (TorusSite (n * R.params.side)))
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
    Measurable fun p : TorusField (n * R.params.side) × (support → R.labels.Ω) => F p.1 support p.2 bad b
  gauge_invariant : ∀ (W : TorusField (n * R.params.side)) (support : Finset (TorusSite (n * R.params.side)))
    (ω : support → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (u : TorusSite (n * R.params.side) → UnitQuaternion),
    IsHullState R.params R.range W support → 0 < R.labelWeight (n * R.params.side) W support ω →
    (∀ c, u (toTorusSite (n * R.params.side) (b c)) = 1) →
    (∀ y : TorusSite n, u (blockSite y fun _ => ⟨(R.params.side - 1) / 2, by
      have := NeZero.pos R.params.side
      omega⟩) = 1) →
    F (gaugeTransform u W) support (R.labels.act support u ω) bad b = F W support ω bad b
def StepGas.GasGround.CaseAvoids (G : GasGround R n) (A : Finset (TorusSite n))
    (bad : Finset (TorusBond (n * R.params.side))) (support : Finset (TorusSite (n * R.params.side))) : Prop :=
  (∀ c ∈ bad, c ∉ G.recordedBad → parentBlock R.params.side c.1 ∉ A) ∧
    ∀ z ∈ support, z ∉ G.recordedSites → parentBlock R.params.side z ∉ A
open Classical in
def StepGas.GasGround.caseIntegrand (G : GasGround R n) (F : ClusterExpansionOfAStep.CaseFunctional R n)
    (bad : Finset (TorusBond (n * R.params.side))) (support : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (W : TorusField (n * R.params.side))
    (ν : G.state.unlabelled support → R.labels.Ω) : ℝ≥0∞ :=
  if IsHullState R.params R.range (G.state.fieldWithStoredLinks W) support ∧
      coarseStateOf R G.cut (G.state.fieldWithStoredLinks W) support (G.state.fillLabels support ν) bad b =
        G.state then
    F (G.state.fieldWithStoredLinks W) support (G.state.fillLabels support ν) bad b *
      ENNReal.ofReal (stepWeight R G.cut G.coarse (G.state.fieldWithStoredLinks W) support
        (G.state.fillLabels support ν) bad b)
  else 0
def StepGas.GasGround.caseIntegral (G : GasGround R n) (F : ClusterExpansionOfAStep.CaseFunctional R n)
    (bad : Finset (TorusBond (n * R.params.side))) (support : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) : ℝ≥0∞ :=
  ∫⁻ W, ∫⁻ ν : G.state.unlabelled support → R.labels.Ω, G.caseIntegrand F bad support b W ν
    ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
open Classical in
def StepGas.GasGround.caseMass (G : GasGround R n) (A : Finset (TorusSite n))
    (F : ClusterExpansionOfAStep.CaseFunctional R n) : ℝ≥0∞ :=
  ∑ bad ∈ (markedBonds R G.cut).powerset, ∑ support : Finset (TorusSite (n * R.params.side)),
    if G.CaseAvoids A bad support then ∑ b : BaseChoice R.params.side n, G.caseIntegral F bad support b else 0
def StepSettings.ChartSetting.settingIntegral (s : ChartSetting R n) (F : ClusterExpansionOfAStep.CaseFunctional R n)
    (bad : Finset (TorusBond (n * R.params.side))) : ℝ≥0∞ :=
  ∫⁻ η, F (s.field η) s.support s.labelling bad s.bases *
    ENNReal.ofReal (s.cutoffProduct η * Real.exp (-s.potential η))
open Classical in
def StepGas.GasGround.gasIntegrand (G : GasGround R n) (F : ClusterExpansionOfAStep.CaseFunctional R n)
    (σ : G.Config) : ℝ≥0∞ :=
  if G.pairConstraint.IsAdmissible σ then (G.settingOf (G.familyOf σ)).settingIntegral F (G.badBondsOf σ) else 0
def StepGas.GasGround.gasMass (G : GasGround R n) (A : Finset (TorusSite n))
    (F : ClusterExpansionOfAStep.CaseFunctional R n) : ℝ≥0∞ :=
  ∫⁻ σ, G.gasIntegrand F σ ∂Measure.pi (G.referenceMeasure A)
def ClusterExpansionOfAStep.CaseMassEqGasMass : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
      ∀ (A : Finset (TorusSite n)) (F : ClusterExpansionOfAStep.CaseFunctional R n), ClusterExpansionOfAStep.IsCaseFunctional F →
        Measurable (G.gasIntegrand F) →
        G.caseMass A F =
          ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
            ENNReal.ofReal (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) *
              G.gasMass A F
end YangMills.Construction
end
