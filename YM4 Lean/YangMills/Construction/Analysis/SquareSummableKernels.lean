import Mathlib
open ComplexConjugate
noncomputable section
namespace YangMills.Construction.SquareSummable
def IsSqSummable {𝔸 : Type*} [Countable 𝔸] [Nonempty 𝔸] (K : 𝔸 → 𝔸 → ℂ) : Prop :=
  Summable fun p : 𝔸 × 𝔸 => ‖K p.1 p.2‖ ^ 2
def hsNorm {𝔸 : Type*} [Countable 𝔸] [Nonempty 𝔸] (K : 𝔸 → 𝔸 → ℂ) : ℝ :=
  (∑' p : 𝔸 × 𝔸, ‖K p.1 p.2‖ ^ 2) ^ (1 / 2 : ℝ)
def adjointKernel {𝔸 : Type*} [Countable 𝔸] [Nonempty 𝔸] (K : 𝔸 → 𝔸 → ℂ) : 𝔸 → 𝔸 → ℂ :=
  fun a b => conj (K b a)
def cyclicTraceTerm {𝔸 : Type*} [Countable 𝔸] [Nonempty 𝔸] {m : ℕ} (K : Fin m → 𝔸 → 𝔸 → ℂ)
    (a : Fin m → 𝔸) : ℂ :=
  ∏ k : Fin m, K k (a k) (a (finRotate m k))
def CyclicTraceConverges {𝔸 : Type*} [Countable 𝔸] [Nonempty 𝔸] {m : ℕ}
    (K : Fin m → 𝔸 → 𝔸 → ℂ) : Prop :=
  Summable fun a : Fin m → 𝔸 => ‖cyclicTraceTerm K a‖
def cyclicTrace {𝔸 : Type*} [Countable 𝔸] [Nonempty 𝔸] {m : ℕ} (K : Fin m → 𝔸 → 𝔸 → ℂ) : ℂ :=
  ∑' a : Fin m → 𝔸, cyclicTraceTerm K a
def alternatingKernels {𝔸 : Type*} [Countable 𝔸] [Nonempty 𝔸] (K : 𝔸 → 𝔸 → ℂ) (m : ℕ) :
    Fin m → 𝔸 → 𝔸 → ℂ :=
  fun k => if Even (k : ℕ) then K else adjointKernel K
def alternatingCyclicTrace {𝔸 : Type*} [Countable 𝔸] [Nonempty 𝔸] (K : 𝔸 → 𝔸 → ℂ) (m : ℕ) : ℂ :=
  cyclicTrace (alternatingKernels K m)
def schattenEvenNorm {𝔸 : Type*} [Countable 𝔸] [Nonempty 𝔸] (K : 𝔸 → 𝔸 → ℂ) (m : ℕ) : ℝ :=
  ‖alternatingCyclicTrace K m‖ ^ (1 / (m : ℝ))
end YangMills.Construction.SquareSummable
