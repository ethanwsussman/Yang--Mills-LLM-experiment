import YangMills.Construction.TorusOrFourSpace.ClassesOfFunctionsWithSupportInASet
import YangMills.Construction.TorusOrFourSpace.CutOffsOnAProductOfOpenSets
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
namespace Kind.Tuple
variable (D : Params) (E : Kind)
def complexC1SupportedIn (A : Set (E.Pt D)) : Set (E.Pt D → ℂ) :=
  {h | IsClassC D E 1 (ofSingle D E h) ∧ Kind.IsCompactQ D E (Kind.supportQ D E h) ∧
    Kind.supportQ D E h ⊆ A}
def ComplexSupportedFacts (O : Set (E.Pt D)) : Prop :=
  (∃ S : Submodule ℂ (E.Pt D → ℂ), (S : Set (E.Pt D → ℂ)) = complexC1SupportedIn D E O) ∧
  (∃ S : Submodule ℂ (E.Pt D → ℂ), (S : Set (E.Pt D → ℂ)) = singleTestFns D E O) ∧
  singleTestFns D E O ⊆ complexC1SupportedIn D E O ∧
  (∀ φ ∈ singleTestFns D E O,
    (fun y => ((φ y).re : ℂ)) ∈ singleTestFns D E O ∧
      (fun y => ((φ y).im : ℂ)) ∈ singleTestFns D E O) ∧
  (∀ g : E.Pt D → ℝ, (fun y => (g y : ℂ)) ∈ singleTestFns D E O →
    g ∈ Kind.c1SupportedIn D E O) ∧
  (∀ g ∈ Kind.c1SupportedIn D E O, (fun y => (g y : ℂ)) ∈ complexC1SupportedIn D E O) ∧
  (∀ h ∈ complexC1SupportedIn D E O,
    (fun y => (h y).re) ∈ Kind.c1SupportedIn D E O ∧ (fun y => (h y).im) ∈ Kind.c1SupportedIn D E O) ∧
  ∀ h ∈ complexC1SupportedIn D E O, c1NormSingle D E h < ⊤
end Kind.Tuple
def ComplexSupportedClassesClaim : Prop :=
  ∀ (D : Params) (E : Kind) (O : Set (E.Pt D)), Kind.IsOpenQ D E O →
    Kind.Tuple.ComplexSupportedFacts D E O
end YangMills.Construction.PeriodicSpace
