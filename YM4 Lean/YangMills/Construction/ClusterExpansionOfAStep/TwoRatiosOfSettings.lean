import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open StepSettings RenormalizationStepParameters TorusFields
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
abbrev StepSettings.ChartSetting.mass (s : ChartSetting R n) : ℝ :=
  ∫ η, s.cutoffProduct η * Real.exp (-s.potential η)
namespace ClusterExpansionOfAStep
structure PairedSettings (sa sb : ChartSetting R n) (sa' sb' : ChartSetting R n') (H : Finset (Fin 4 → ℤ))
    (Y : TorusSite n) (Y' : TorusSite n') (d m : ℕ) : Prop where
  agree_away : ∀ (y : TorusSite n) (k : ℕ), (∀ h ∈ H, k + 2 ≤ supDist y (Y + siteOfInt h)) →
    SettingsAgreeNear sa sb y y k
  agree_away' : ∀ (y : TorusSite n') (k : ℕ), (∀ h ∈ H, k + 2 ≤ supDist y (Y' + siteOfInt h)) →
    SettingsAgreeNear sa' sb' y y k
  left_agree_near : ∀ h ∈ H, ∀ g, OffsetInBox (d - 1) g →
    SettingsAgreeNear sa sa' (Y + siteOfInt (h + g)) (Y' + siteOfInt (h + g)) m
  right_agree_near : ∀ h ∈ H, ∀ g, OffsetInBox (d - 1) g →
    SettingsAgreeNear sb sb' (Y + siteOfInt (h + g)) (Y' + siteOfInt (h + g)) m
  offsets_injective : ∀ h ∈ H, ∀ h₂ ∈ H, ∀ g g₂, OffsetInBox (d - 1) g → OffsetInBox (d - 1) g₂ →
    (Y + siteOfInt (h + g) = Y + siteOfInt (h₂ + g₂) ↔ h + g = h₂ + g₂)
  offsets_injective' : ∀ h ∈ H, ∀ h₂ ∈ H, ∀ g g₂, OffsetInBox (d - 1) g → OffsetInBox (d - 1) g₂ →
    (Y' + siteOfInt (h + g) = Y' + siteOfInt (h₂ + g₂) ↔ h + g = h₂ + g₂)
def LogMassRatiosClose : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → ∀ (n n' : ℕ) [NeZero n] [NeZero n'],
      T.n₀ ≤ n → T.n₀ ≤ n' → ∀ (sa sb : ChartSetting R n) (sa' sb' : ChartSetting R n')
        (H : Finset (Fin 4 → ℤ)) (Y : TorusSite n) (Y' : TorusSite n') (d m : ℕ),
        sa.IsAdmissible → sb.IsAdmissible → sa'.IsAdmissible → sb'.IsAdmissible → H.Nonempty → 2 ≤ d →
        (R.range : ℝ) / (4 * R.params.side) ≤ (d : ℝ) - 2 → (R.range : ℝ) / (4 * R.params.side) ≤ m →
        PairedSettings sa sb sa' sb' H Y Y' d m →
        |(Real.log sb.mass - Real.log sa.mass) - (Real.log sb'.mass - Real.log sa'.mass)| ≤
          (H.card : ℝ) * (2 * (d : ℝ) + 1) ^ 4 * (2 * Real.exp (-(T.rt / 2 ^ 5 * m))) +
            2 * (H.card : ℝ) * (Real.exp (2 * (T.rt / 2 ^ 5)) * Real.exp (-(3 / 4 * (T.rt / 2 ^ 5) * d)) *
              (2 / (1 - Real.exp (-(T.rt / 2 ^ 5 / 16)))) ^ 4)
end ClusterExpansionOfAStep
end YangMills.Construction
end
