import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.StepSettings
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters StepCosts
variable {R : StepSetup} {n n' : ℕ}
structure SettingsAgreeAwayFromFrames [NeZero n] [NeZero n'] (s : ChartSetting R n) (s' : ChartSetting R n')
    (Y : TorusSite n) (Y' : TorusSite n') (m : ℕ) : Prop where
  lt_extent : 2 * m + 2 < n
  lt_extent' : 2 * m + 2 < n'
  coarse_agree : FieldsAgreeNear s.coarse s'.coarse Y Y' m
  free_iff : ∀ q, IsNearIndex R.params.side m q →
    (nearBond R.params.side Y q ∈ s.free ↔ nearBond R.params.side Y' q ∈ s'.free)
  fine_eq : ∀ q, IsNearIndex R.params.side m q → nearBond R.params.side Y q ∉ s.free →
    s.fine (nearBond R.params.side Y q).1 q.2.2 = s'.fine (nearBond R.params.side Y' q).1 q.2.2
  support_iff : ∀ h o, OffsetInBox m h → o ∈ centredCube R.params.side →
    (fineSite R.params.side Y h o ∈ s.support ↔ fineSite R.params.side Y' h o ∈ s'.support)
  labelling_eq : ∀ h o (hz : fineSite R.params.side Y h o ∈ s.support)
    (hz' : fineSite R.params.side Y' h o ∈ s'.support), OffsetInBox m h →
    o ∈ centredCube R.params.side → s.labelling ⟨_, hz⟩ = s'.labelling ⟨_, hz'⟩
  bases_match : ∀ h, OffsetInBox m h → ∃ o, o ∈ centredCube R.params.side ∧
    toTorusSite (n * R.params.side)
        (s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))) =
      fineSite R.params.side Y h o ∧
    toTorusSite (n' * R.params.side)
        (s'.bases (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h))) =
      fineSite R.params.side Y' h o
end YangMills.Construction.StepSettings
namespace YangMills.Construction.StepLocality
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters StepCosts StepSettings
def DensityLocality : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → ∀ (n n' : ℕ) [NeZero n] [NeZero n'], T.n₀ ≤ n →
      T.n₀ ≤ n' →
      ∀ (s : ChartSetting R n) (s' : ChartSetting R n') (Y : TorusSite n) (Y' : TorusSite n') (m : ℕ),
        s.IsAdmissible → s'.IsAdmissible →
        ((R.range : ℝ) / (4 * R.params.side) ≤ m → SettingsAgreeNear s s' Y Y' m →
          |s.blockActivity T.lam Y - s'.blockActivity T.lam Y'| ≤ Real.exp (-(T.rt * m / 2 ^ 5))) ∧
        (16 * R.frameReach ≤ m → SettingsAgreeAwayFromFrames s s' Y Y' m →
          |s.blockActivity T.lam Y - s'.blockActivity T.lam Y'| ≤
            Real.exp (-(T.rt * ((m : ℝ) - R.frameReach) / 2 ^ 5)) ∧
          Real.exp (-(T.rt * ((m : ℝ) - R.frameReach) / 2 ^ 5)) ≤ Real.exp (-(15 / 16 * T.rt * m / 2 ^ 5)))
end YangMills.Construction.StepLocality
end
