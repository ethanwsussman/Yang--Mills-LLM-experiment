import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace StepGas
open StepSettings StepCosts TorusLumps
variable {R : StepSetup} {n : ℕ} [NeZero n]
def GasGround.IsGasFamily (G : GasGround R n) (γ : GasFamily R n) : Prop :=
  (∀ θ, γ.Occupies θ → G.IsGasSupport θ) ∧ ∀ θ θ', γ.Occupies θ → γ.Occupies θ' → θ ≠ θ' → θ.FarApart θ'
structure GasGround.HasWeightAt (G : GasGround R n) (γ : GasFamily R n)
    (η : FreeCoords (G.settingOf γ).free) : Prop where
  coordNorm_lt : ∀ b, coordNorm (η b) < R.ballRadius
  isHull : IsHullState R.params R.range ((G.settingOf γ).field η) (G.settingOf γ).support
  factor_ne_zero : ∀ X ∈ chainComponents R.range (G.settingOf γ).support,
    R.clusterFactor (n * R.params.side) ((G.settingOf γ).field η) (G.settingOf γ).support
      (G.settingOf γ).labelling X ≠ 0
  baseLaw_ne_zero : baseLaw (R := R) ((G.settingOf γ).field η) (G.settingOf γ).bases ≠ 0
  bondMark_ne_zero : ∀ b ∈ chartBonds R.params.side n, b ∉ (G.settingOf γ).free → b ∉ (G.settingOf γ).bad →
    StepSettings.bondMark R G.coarse ((G.settingOf γ).field η) b ≠ 0
end StepGas
end YangMills.Construction
end
