import YangMills.Construction.TorusOrFourSpace.ConvergenceOnSeparatedTuplesAndPartialHierarchies
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.PartialHierarchySeq
variable {P : Params} {J : Sequences.PNatIndexSet} {ρ : J.carrier → ℝ≥0∞}
def ConvergesOnSepTuples (S : PartialHierarchySeq P Kind.euclidean J ρ)
    (Φ : Hierarchy P Kind.euclidean) : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (f : sepC1Tuples P Kind.euclidean k) (ε : ℝ), 0 < ε →
    ∃ j₀ : ℤ, ∀ j : J.carrier, j₀ ≤ (((j.1 : ℕ+) : ℕ) : ℤ) →
      ∃ hf : f.1 ∈ sepLipTuplesWithin P Kind.euclidean k
          (centredBall P Kind.euclidean (ρ j)),
        |S.func j k hk ⟨f.1, hf⟩ - Φ.func k hk f| ≤ ε
end YangMills.Construction.PeriodicSpace.Kind.PartialHierarchySeq
