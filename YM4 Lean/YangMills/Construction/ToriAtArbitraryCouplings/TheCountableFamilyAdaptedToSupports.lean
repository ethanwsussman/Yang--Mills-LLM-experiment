import YangMills.Construction.ReflectionPositivity.CentredObservableAndFunctionals
import YangMills.Construction.ToriAtArbitraryCouplings.TheCountableFamilyOfSupportsAndCharts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace TorusSide
variable (s : TorusSide)
def IsCountableGradDenseFamily (E : Ambient) (F : s.supportFamily E → Set (s.Point E → ℝ)) : Prop :=
  ∀ K : s.supportFamily E, (F K).Countable ∧ F K ⊆ s.c1VanishingOutside E K.1 ∧
    ∀ g ∈ s.c1VanishingOutside E K.1, ∀ δ : ℝ, 0 < δ → ∃ ψ ∈ F K, s.c1GradNorm E (g - ψ) < δ
def adaptedTupleSet (E : Ambient) (F : s.supportFamily E → Set (s.Point E → ℝ)) :
    Set (Ambient.FnList s.asMirrorData E) :=
  ⋃ (n : ℕ) (_ : 1 ≤ n), {X | ∃ (K : Fin n → s.supportFamily E) (ψ : Fin n → s.Point E → ℝ),
    Pairwise (Function.onFun Disjoint fun i => (K i).1) ∧ (∀ i, ψ i ∈ F (K i)) ∧ X = List.ofFn ψ}
def adaptedTupleSetLengthGeTwo (E : Ambient) (F : s.supportFamily E → Set (s.Point E → ℝ)) :
    Set (Ambient.FnList s.asMirrorData E) :=
  {X | X ∈ s.adaptedTupleSet E F ∧ 2 ≤ X.length}
def evalOnAdaptedTuples {E : Ambient} {F : s.supportFamily E → Set (s.Point E → ℝ)}
    (S : Ambient.ConnectedFamily s.asMirrorData E)
    (X : s.adaptedTupleSetLengthGeTwo E F) : ℝ :=
  S.evalAt X.1.length X.1
end TorusSide
end YangMills.Construction.ToriAtArbitraryCouplings
end
