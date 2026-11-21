import YangMills.Construction.Continuum.LinearInEachArgumentAndVanishingNearAConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LocalVanishing
open TestFunctions DisjointTuples
def supportProduct {k n : ℕ} (f : disjointSupportTuples k n) : Set (Fin n → Fin k → ℝ) :=
  Set.univ.pi fun i => tsupport (f.1 i)
def VanishingFromLocalVanishing : Prop :=
  ∀ k : ℕ, (k = 2 ∨ k = 4) → ∀ n : ℕ, 2 ≤ n → ∀ D : disjointSupportTuples k n → ℂ,
    IsSeparatelyLinear D →
      (∀ f : disjointSupportTuples k n,
        IsCompact (supportProduct f) ∧
        supportProduct f ⊆ injectiveTuples (Fin k → ℝ) n ∧
        ((∀ x : injectiveTuples (Fin k → ℝ) n, x.1 ∈ supportProduct f → VanishesNearConfig D x) →
          D f = 0)) ∧
      ((∀ x : injectiveTuples (Fin k → ℝ) n, VanishesNearConfig D x) →
        ∀ f : disjointSupportTuples k n, D f = 0)
end YangMills.Construction.LocalVanishing
end
