import YangMills.Construction.ReflectionPositivity.RepresentativesLatticeApproximationsLimitsAndBoundedTriples
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOfFourSpaceAndTheirFunctionals
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.ApproximatingSequences
open YangMills.Construction.SeparatedTuples (IsDisjointlySupported RealValued)
def LatticeApproximation.IsBoundedForSomeM (D : AxisMirror.MirrorData)
    (T : LatticeApproximation D.L) : Prop :=
  ∃ (M : ℝ) (hM : 1 ≤ M), T.IsUniformlyBounded D M hM
def LatticeApproximation.IsC1ConstantFamily {L : ℕ} (T : LatticeApproximation L)
    (C : ∀ k : ℕ, (Fin k → Set (Fin 4 → ℝ)) → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ A : Fin k → Set (Fin 4 → ℝ), (∀ l, IsCompact (A l)) →
    Pairwise (Function.onFun Disjoint A) →
    ∀ (j : ℕ+) (f : Fin k → RealValued), IsDisjointlySupported (List.ofFn f) →
      (∀ l, tsupport (f l) ⊆ A l) →
      |∫ U, T.latticeProduct j (List.ofFn f) U ∂T.state j| ≤
        C k A * ∏ l, YangMills.Construction.TestFunctions.c1NormR4 (f l)
def LatticeApproximation.HasC1Constants {L : ℕ} (T : LatticeApproximation L) : Prop :=
  ∃ C, T.IsC1ConstantFamily C
end YangMills.Construction.ReflectionPositivity.ApproximatingSequences
