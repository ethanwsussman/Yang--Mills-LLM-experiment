import YangMills.Construction.ClusterExpansionOfAStep.ClusterDefs
import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters StepSettings StepCosts
variable {R : StepSetup} {n : ℕ}
def StepSettings.ChartSetting.integral [NeZero n] (s : ChartSetting R n) : ℝ :=
  ∫ η, s.cutoffProduct η * Real.exp (-s.potential η)
def ClusterExpansionOfAStep.BondJoinsBlocks (L : ℕ) [NeZero n] [NeZero L] (P : Finset (TorusSite n))
    (b : TorusBond (n * L)) : Prop :=
  parentBlock L b.1 ∈ P ∧ parentBlock L (b.1 + TorusFields.unitStep (n * L) b.2) ∈ P
structure StepSettings.ChartSetting.AgreeOn [NeZero n] (s s' : ChartSetting R n)
    (B : TorusBond (n * R.params.side) → Prop) (Q : Finset (TorusSite n)) : Prop where
  free_iff : ∀ b, B b → (b ∈ s.free ↔ b ∈ s'.free)
  bad_iff : ∀ b, B b → (b ∈ s.bad ↔ b ∈ s'.bad)
  fine_eq : ∀ b, B b → b ∉ s.free → s.fine b.1 b.2 = s'.fine b.1 b.2
  support_iff : ∀ z, parentBlock R.params.side z ∈ Q → (z ∈ s.support ↔ z ∈ s'.support)
  labelling_eq : ∀ z (hz : z ∈ s.support) (hz' : z ∈ s'.support), parentBlock R.params.side z ∈ Q →
    s.labelling ⟨z, hz⟩ = s'.labelling ⟨z, hz'⟩
  bases_eq : ∀ y ∈ Q, s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) =
    s'.bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
structure ClusterExpansionOfAStep.IsFourSettings [NeZero n] (s : Fin 2 → Fin 2 → ChartSetting R n)
    (P P' : Finset (TorusSite n)) : Prop where
  coarse_eq : ∀ i j i' j', (s i j).coarse = (s i' j').coarse ∧ (s i j).region = (s i' j').region
  first_agree : ∀ i j j', (s i j).AgreeOn (s i j') (ClusterExpansionOfAStep.BondJoinsBlocks R.params.side P) P
  second_agree : ∀ i i' j, (s i j).AgreeOn (s i' j) (ClusterExpansionOfAStep.BondJoinsBlocks R.params.side P') P'
  rest_agree : ∀ i j i' j', (s i j).AgreeOn (s i' j')
    (fun b => ¬ ClusterExpansionOfAStep.BondJoinsBlocks R.params.side P b ∧ ¬ ClusterExpansionOfAStep.BondJoinsBlocks R.params.side P' b)
    (Finset.univ \ (P ∪ P'))
structure ClusterExpansionOfAStep.CompatibleSupports [NeZero n] (s : Fin 2 → Fin 2 → ChartSetting R n)
    (θ θ' : Finset (TorusSite (n * R.params.side))) : Prop where
  far_apart : ∀ z ∈ θ, ∀ z' ∈ θ', 10 * R.range < supDist z z'
  support_separated : ∀ i j, ∀ z ∈ (s i j).support, z ∈ θ ∨ z ∈ θ' ∨ ∀ z' ∈ θ ∪ θ', 10 * R.range < supDist z z'
def ClusterExpansionOfAStep.DoubleRatioDecay : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n →
      ∀ (s : Fin 2 → Fin 2 → ChartSetting R n) (θ θ' : Finset (TorusSite (n * R.params.side))),
        (∀ i j, (s i j).IsAdmissible) → ClusterExpansionOfAStep.CompatibleSupports s θ θ' →
        ClusterExpansionOfAStep.IsFourSettings s (coreBlocks R.params.side R.range θ) (coreBlocks R.params.side R.range θ') →
        (∀ i j, 0 < (s i j).integral) ∧
        (∀ y ∈ coreBlocks R.params.side R.range θ, ∀ y' ∈ coreBlocks R.params.side R.range θ',
          2 * (R.range : ℝ) / R.params.side - 3 ≤ supDist y y') ∧
        ∀ D : ℕ, (∀ y ∈ coreBlocks R.params.side R.range θ, ∀ y' ∈ coreBlocks R.params.side R.range θ',
            D ≤ supDist y y') →
          |Real.log ((s 1 1).integral * (s 0 0).integral / ((s 1 0).integral * (s 0 1).integral))| ≤
            min ((coreBlocks R.params.side R.range θ).card : ℝ) (coreBlocks R.params.side R.range θ').card *
              Real.exp (-(R.params.rt * D / 8))
end YangMills.Construction
end
