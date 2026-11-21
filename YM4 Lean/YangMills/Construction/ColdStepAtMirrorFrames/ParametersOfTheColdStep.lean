import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
structure StepParameters where
  a : ℝ
  L : ℕ
  chainParams : ColdChainParameters
  Ct : ℝ
  κ : ℝ
  η₃ : ℝ
  blockIndex : ℕ
  σ : ℝ
  p : ℝ → ℝ
  Cs : ℝ
  E : ℝ
  n₀ : ℕ
  CE : ℝ
  coupling : ℝ
def StepParameters.decayRate (T : StepParameters) : ℝ := T.κ / 2 ^ 10
def StepParameters.energyRatio (T : StepParameters) : ℝ := T.E / T.η₃
def StepParameters.ballRadius (T : StepParameters) : ℝ := T.σ / 64
structure StepParameters.IsOrdered (T : StepParameters) : Prop where
  one_le_a : 1 ≤ T.a
  odd_L : Odd T.L
  chain_admissible : T.chainParams.Admissible T.a T.L
  κ_pos : 0 < T.κ
  η₃_pos : 0 < T.η₃
  η₃_le_one : T.η₃ ≤ 1
  σ_pos : 0 < T.σ
  cutoff : IsCutoff (T.σ / 64) T.p
  one_le_E : 1 ≤ T.E
def EventuallyInParameters (P : StepParameters → Prop) : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ c : ColdChainParameters, c.Admissible a L →
    ∃ Ct₀ : ℝ, ∀ Ct : ℝ, Ct₀ ≤ Ct →
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η₃ : ℝ, 0 < η₃ → η₃ ≤ 1 → η₃ ≤ η₀ →
    ∃ N₀ : ℕ, ∀ blockIndex : ℕ, N₀ ≤ blockIndex →
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ σ : ℝ, 0 < σ → σ ≤ σ₀ →
    ∀ p : ℝ → ℝ, IsCutoff (σ / 64) p →
    ∃ C₀ : ℝ, ∀ Cs : ℝ, C₀ ≤ Cs →
    ∀ E : ℝ, 1 ≤ E →
    ∃ m₀ : ℕ, ∀ n₀ : ℕ, m₀ ≤ n₀ →
    ∃ C₁ : ℝ, ∀ CE : ℝ, C₁ ≤ CE →
    ∃ g₀ : ℝ, ∀ coupling : ℝ, g₀ ≤ coupling →
      P ⟨a, L, c, Ct, κ, η₃, blockIndex, σ, p, Cs, E, n₀, CE, coupling⟩
end YangMills.Construction.ColdStepAtMirrorFrames
end
