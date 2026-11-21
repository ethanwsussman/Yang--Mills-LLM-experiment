import YangMills.Construction.Continuum.FreeRingKernelsAndTheFreeBoxKernel
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PropagatorRings
variable {n : ℕ}
def CyclicTraceRingInvariant (ς : Fin n → Fin n) : Prop :=
  ∀ x : Fin n → Fin 4 → ℝ, (∀ i, x (ς i) ≠ x (ς (finRotate n i))) →
    FreeRingKernels.cyclicTrace (Tuples.rotateBy 1 ς) x = FreeRingKernels.cyclicTrace ς x ∧
      FreeRingKernels.cyclicTrace (Tuples.reversed ς) x = FreeRingKernels.cyclicTrace ς x ∧
        ∀ ς' ∈ Tuples.ringClass ς, FreeRingKernels.cyclicTrace ς' x = FreeRingKernels.cyclicTrace ς x
def supportBox (f : Fin n → (Fin 4 → ℝ) → ℝ) : Set (Fin n → Fin 4 → ℝ) :=
  Set.univ.pi fun j => tsupport (f j)
def cyclicIntegrand (ς : Fin n → Fin n) (f : Fin n → (Fin 4 → ℝ) → ℝ)
    (x : Fin n → Fin 4 → ℝ) : ℝ :=
  (∏ j, f j (x j)) * FreeRingKernels.cyclicTrace ς x
def CyclicIntegralAbsConv (ς : Fin n → Fin n) (f : Fin n → (Fin 4 → ℝ) → ℝ) : Prop :=
  (Pairwise fun i j => 0 < TestFunctions.setDistR4 (tsupport (f i)) (tsupport (f j))) ∧
    IsCompact (supportBox f) ∧
      (∃ C : ℝ, ∀ x ∈ supportBox f, |cyclicIntegrand ς f x| ≤ C) ∧
        Measurable (fun x : supportBox f => cyclicIntegrand ς f x) ∧
          Integrable ((supportBox f).indicator (cyclicIntegrand ς f))
def CyclicTraceProperties : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ ς : Fin n → Fin n, Tuples.IsBijectiveTuple ς →
    CyclicTraceRingInvariant ς ∧
      ∀ f : Fin n → (Fin 4 → ℝ) → ℝ, FreeRingKernels.IsAdmissibleTestFamily f →
        CyclicIntegralAbsConv ς f
end YangMills.Construction.PropagatorRings
end
