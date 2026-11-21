import YangMills.Construction.Lattice.RingsAndRingKernels
import Mathlib
noncomputable section
namespace YangMills.Construction.CyclicKernels
open YangMills.Construction.Tuples
variable {P : Type*}
def IsSymmetricKernelOn (C : P → P → ℝ) : Prop := ∀ p q, C p q = C q p
def cyclicKernelOn [Fintype P] {n : ℕ} (C : P → P → ℝ) (φ : Fin n → P → ℝ) : ℝ :=
  1 / 2 * ∑ τ : Equiv.Perm (TailPosition n), ∑ p : Fin n → P,
    (∏ i, φ i (p i)) *
      ∏ i, C (p (fixFirst τ i)) (p (fixFirst τ (finRotate n i)))
end YangMills.Construction.CyclicKernels
