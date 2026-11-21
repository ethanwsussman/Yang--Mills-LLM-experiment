import YangMills.Construction.TorusOrFourSpace.ConvergenceOnSeparatedTuplesAndPartialHierarchies
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (D : Params) (E : Kind)
abbrev SepFunctionals : Type :=
  (n : ℕ) → 2 ≤ n → sepC1Tuples D E n → ℝ
namespace PartialHierarchySeq
variable {D E} {J₀ : Sequences.PNatIndexSet} {ρ : J₀.carrier → ℝ≥0∞}
def TendsToPointwiseAlong (S : PartialHierarchySeq D E J₀ ρ) (J : Sequences.PNatIndexSet)
    (hJ : J.carrier ⊆ J₀.carrier) (Φ : SepFunctionals D E) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (f : sepC1Tuples D E n),
    ∃ (k : ℤ) (hf : ∀ j : (J.filterGe k).carrier,
        f.1 ∈ sepLipTuplesWithin D E n (centredBall D E (ρ ⟨j.1, hJ j.2.1⟩))),
      IndexedLimits.ConvergesToAlong J k
        (fun j => ((S.func ⟨j.1, hJ j.2.1⟩ n hn ⟨f.1, hf j⟩ : ℝ) : ℂ))
        ((Φ n hn f : ℝ) : ℂ)
end PartialHierarchySeq
end YangMills.Construction.PeriodicSpace.Kind
