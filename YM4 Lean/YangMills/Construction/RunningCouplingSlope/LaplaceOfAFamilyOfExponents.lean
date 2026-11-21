import YangMills.Construction.RunningCouplingSlope.FamiliesOfExponents
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open ColdStepAtMirrorFrames LaplaceAsymptotics
def LaplaceMethodHessian : Prop :=
  ∀ ρ lam : ℝ, 0 < ρ → 0 < lam → ∃ C q : ℝ, 0 < C ∧ 0 ≤ q ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (p : ℝ → ℝ) (K x : ℝ)
      (Q B : (Fin 2 → ℝ) × BondField ι → ℝ), IsCutoff ρ p → 0 ≤ K → 1 ≤ x →
      C * ((Fintype.card ι : ℝ) + K) ^ q * x ^ (-(1 / 2) : ℝ) ≤ 1 → IsAdmissibleExponentFamily ρ lam K Q B →
      ContDiffAt ℝ 2 (logCutoffIntegral ρ p x Q B) 0 ∧ ContDiffAt ℝ 2 (gaussianLogValue Q B) 0 ∧
      |iteratedFDeriv ℝ 2 (logCutoffIntegral ρ p x Q B) 0 (fun l => Pi.single l 1) -
          iteratedFDeriv ℝ 2 (gaussianLogValue Q B) 0 (fun l => Pi.single l 1)| ≤
        C * ((Fintype.card ι : ℝ) + K) ^ q * x ^ (-(1 / 2) : ℝ)
end YangMills.Construction.RunningCouplingSlope
end
