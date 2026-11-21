import YangMills.Construction.Analysis.SquareSummableKernels
import Mathlib
open ComplexConjugate
noncomputable section
namespace YangMills.Construction.SquareSummable
def CyclicTraceProductBounds : Prop :=
  ∀ (𝔸 : Type) [Countable 𝔸] [Nonempty 𝔸] (m : ℕ), 2 ≤ m →
    ∀ (A : 𝔸 → 𝔸 → ℂ) (B : Fin m → 𝔸 → 𝔸 → ℂ),
      IsSqSummable A → (∀ k, IsSqSummable (B k)) →
      (Summable (fun α : Fin m → 𝔸 => ∏ k : Fin m, ‖B k (α k) (α (finRotate m k))‖) ∧
        ∑' α : Fin m → 𝔸, ∏ k : Fin m, ‖B k (α k) (α (finRotate m k))‖ ≤
          ∏ k : Fin m, hsNorm (B k) ∧
        CyclicTraceConverges B ∧
        ‖cyclicTrace B‖ ≤ ∏ k : Fin m, hsNorm (B k)) ∧
      (IsSqSummable (adjointKernel A) ∧
        hsNorm (adjointKernel A) = hsNorm A ∧
        adjointKernel (adjointKernel A) = A ∧
        cyclicTrace (fun k => B (finRotate m k)) = cyclicTrace B ∧
        conj (cyclicTrace B) = cyclicTrace (fun k => adjointKernel (B (Fin.rev k)))) ∧
      (Even m →
        ((alternatingCyclicTrace A m).im = 0 ∧
          0 ≤ (alternatingCyclicTrace A m).re ∧
          alternatingCyclicTrace A m = ((schattenEvenNorm A m ^ m : ℝ) : ℂ) ∧
          schattenEvenNorm (adjointKernel A) m = schattenEvenNorm A m) ∧
        ‖cyclicTrace B‖ ≤ ∏ k : Fin m, schattenEvenNorm (B k) m ∧
        ∀ j : ℕ, 1 ≤ j →
          schattenEvenNorm A (j * m) ^ (j * m) ≤ (schattenEvenNorm A m ^ m) ^ j)
end YangMills.Construction.SquareSummable
