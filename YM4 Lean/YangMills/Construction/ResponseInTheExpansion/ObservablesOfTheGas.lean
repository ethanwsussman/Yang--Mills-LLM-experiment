import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfTheGas
import YangMills.Construction.ClusterExpansionOfAStep.SharedGasOfTwoGrounds
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open Dobrushin CoreColumns StepGas StepSettings RenormalizationStepParameters TorusFields
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
def restrictAdmissible (G : GasGround R n) (F : G.Config → ℝ) (σ : G.Config) : ℝ :=
  if G.pairConstraint.IsAdmissible σ then F σ else 0
structure ClassesControlScore (G : GasGround R n) (Y : TorusSite n) (κ s₀ : ℝ) (s : G.Config → ℝ)
    (H : Finset G.GasSpin) (e : ∀ i : G.GasSpin, G.SpinValue i → ℝ) : Prop where
  core_mem : ∀ i ∈ H, Y ∈ i.1.core
  measurable : ∀ i, Measurable (e i)
  nonneg : ∀ i v, 0 ≤ e i v
  vacant_eq_zero : ∀ i, e i (Sum.inl ()) = 0
  score_le : ∀ σ, G.pairConstraint.IsAdmissible σ →
    s σ ≤ s₀ ∨ ∃ i ∈ H, σ i ≠ Sum.inl () ∧ s σ ≤ e i (σ i)
  activity_bound : ∀ i ∈ H, ∀ σ, G.pairConstraint.IsAdmissible σ →
    ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (e i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity κ i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i))
structure IsGasObservable (G : GasGround R n) (Y : TorusSite n) (κ C u s₀ : ℝ) (D₀ : ℕ)
    (p s : G.Config → ℝ) : Prop where
  one_le : 1 ≤ C
  amplitude_nonneg : 0 ≤ u
  baseScore_nonneg : 0 ≤ s₀
  measurable_value : Measurable (restrictAdmissible G p)
  measurable_score : Measurable (restrictAdmissible G s)
  score_nonneg : ∀ σ, G.pairConstraint.IsAdmissible σ → 0 ≤ s σ
  abs_le : ∀ σ, G.pairConstraint.IsAdmissible σ → |p σ| ≤ (C + s σ) * u
  controlled : ∃ H e, ClassesControlScore G Y κ s₀ s H e
  local_far : ∀ (i : G.GasSpin) (σ σ' : G.Config), G.pairConstraint.IsAdmissible σ →
    G.pairConstraint.IsAdmissible σ' →
    (∀ j, j ≠ i → σ j = σ' j) → D₀ ≤ setGap {Y} i.1.core →
    s σ = s σ' ∧ |p σ - p σ'| ≤ 2 * (1 + s σ) * G.coreWeightFrom Y i * u
def gasObservableBoundsStatement : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters → ∀ C : ℝ,
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.nextCoupling ≤ 1.01 * R.coupling →
      (∀ (n : ℕ) [NeZero n] (G : GasGround R n) (Y : TorusSite n) (u s₀ : ℝ) (D₀ : ℕ)
        (p s : G.Config → ℝ), G.IsAdmissibleGround →
        IsGasObservable G Y T.gasRate C u s₀ D₀ p s → T.rt / 2 ^ 6 * D₀ ≤ T.gasRate * R.coupling →
        |G.expectation ∅ p - p G.allVacant| ≤
          (1 + s₀) * Real.exp (-(6 * T.gasRate * R.coupling)) * u ∧
        |G.expectation ∅ p| ≤ (C + s₀ + Real.exp (-(6 * T.gasRate * R.coupling))) * u) ∧
      ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (G : GasGround R n) (G' : GasGround R n')
        (Y : TorusSite n) (Y' : TorusSite n') (N : ℕ),
        G.IsAdmissibleGround → G'.IsAdmissibleGround → 16 * R.frameReach ≤ N →
        GroundsAgreeNear G G' Y Y' N →
        ∃ g : SharedInnerGas G G' Y Y' N (N - R.frameReach - 1) ∅ ∅,
          ∀ (u s₀ : ℝ) (D₀ : ℕ) (p s : G.Config → ℝ) (p' s' : G'.Config → ℝ),
            IsGasObservable G Y T.gasRate C u s₀ D₀ p s →
            IsGasObservable G' Y' T.gasRate C u s₀ D₀ p' s' →
            T.rt / 2 ^ 6 * D₀ ≤ T.gasRate * R.coupling →
            (∀ τ : g.Config, G.pairConstraint.IsAdmissible (g.extendFirst τ) →
              G'.pairConstraint.IsAdmissible (g.extendSecond τ) →
              s (g.extendFirst τ) = s' (g.extendSecond τ) ∧
                |p (g.extendFirst τ) - p' (g.extendSecond τ)| ≤
                  (1 + s (g.extendFirst τ)) * Real.exp (-(15 / 16 * T.rt * N / 2 ^ 5)) * u) →
            |(G.expectation ∅ p - p G.allVacant) - (G'.expectation ∅ p' - p' G'.allVacant)| ≤
              (1 + s₀) * Real.exp (-(2 * T.gasRate * R.coupling) - T.rt * N / 2 ^ 8) * u
end YangMills.Construction.ResponseInTheExpansion
end
