import YangMills.Construction.BackgroundField.StandardLandauGaugeProblem
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BackgroundField
def gaugeFixingConstants (L e r : ℕ) : GaugeFixingConstants :=
  Classical.epsilon (AreUniqueGaugeFixingConstants L e r)
def gaugeFixingB₁ (L M R : ℕ) : ℝ := (gaugeFixingConstants L (Nat.log L M) (Nat.log L R)).B₁ L
def gaugeFixingC₁ (L M R : ℕ) : ℝ := (gaugeFixingConstants L (Nat.log L M) (Nat.log L R)).c₁
end YangMills.Construction.BackgroundField
end
