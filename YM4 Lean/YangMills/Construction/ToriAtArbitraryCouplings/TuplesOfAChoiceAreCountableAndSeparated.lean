import YangMills.Construction.ToriAtArbitraryCouplings.ChoicesOfCountableDenseSets
import YangMills.Construction.ToriAtArbitraryCouplings.ClassesOfFunctionsSeparatedTuplesAndTheSeparation
import YangMills.Construction.ToriAtArbitraryCouplings.TheCountableFamilyAdaptedToSupports
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace ChoiceTuplesCountableSeparated
def Statement : Prop :=
  ∀ (s : TorusSide) (E : Ambient) (D : s.supportFamily E → Set (s.Point E → ℝ)),
    s.IsCountableC1DenseChoice E D →
    (s.adaptedTupleSet E D).Countable ∧ s.adaptedTupleSet E D ⊆ s.sepTuples E ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ (Q : Fin n → s.supportFamily E) (φ : Fin n → s.Point E → ℝ),
      Pairwise (Function.onFun Disjoint fun i => (Q i).1) → (∀ i, φ i ∈ D (Q i)) →
      (⨅ (i : Fin n) (k : Fin n) (_ : i ≠ k), s.setDist E (Q i).1 (Q k).1) ≤
          s.supportGap E (List.ofFn φ) ∧
        0 < ⨅ (i : Fin n) (k : Fin n) (_ : i ≠ k), s.setDist E (Q i).1 (Q k).1
end ChoiceTuplesCountableSeparated
end YangMills.Construction.ToriAtArbitraryCouplings
end
