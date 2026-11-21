import YangMills.Construction.TorusOrFourSpace.TestFunctionsAndDistributionsOnASet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.AlgebraOfTestFns
open Kind
def Claim : Prop :=
  ∀ (D : Params) (E : Kind) (p : ℕ+),
    (∀ (F H : E.Tuple D p → ℂ) (a b : ℂ),
      Tuple.supportT D E (a • F + b • H) ⊆
          Tuple.supportT D E F ∪ Tuple.supportT D E H ∧
        Tuple.supportT D E (F * H) ⊆
          Tuple.supportT D E F ∩ Tuple.supportT D E H) ∧
    (∀ (ν : ℕ) (F H : E.Tuple D p → ℂ), Tuple.IsClassC D E ν F →
      Tuple.IsClassC D E ν H →
        (∀ a b : ℂ, Tuple.IsClassC D E ν (a • F + b • H)) ∧
        Tuple.IsClassC D E ν (F * H) ∧
        Tuple.IsClassC D E ν (fun y => ((F y).re : ℂ)) ∧
        Tuple.IsClassC D E ν (fun y => ((F y).im : ℂ)) ∧
        ∀ α : CoordIndex p, α.degree ≤ ν →
          Tuple.partialDeriv D E α (fun y => ((F y).re : ℂ)) =
              (fun y => ((Tuple.partialDeriv D E α F y).re : ℂ)) ∧
            Tuple.partialDeriv D E α (fun y => ((F y).im : ℂ)) =
              fun y => ((Tuple.partialDeriv D E α F y).im : ℂ)) ∧
    (∀ Ω : Set (E.Tuple D p), Tuple.IsOpenT D E Ω →
      (∃ S : Submodule ℂ (E.Tuple D p → ℂ),
        (S : Set (E.Tuple D p → ℂ)) = Tuple.testFns D E Ω) ∧
      ∀ F ∈ Tuple.testFns D E Ω,
        (fun y => ((F y).re : ℂ)) ∈ Tuple.testFns D E Ω ∧
        (fun y => ((F y).im : ℂ)) ∈ Tuple.testFns D E Ω ∧
        (∀ α : CoordIndex p,
          Tuple.partialDeriv D E α F ∈ Tuple.testFns D E Ω) ∧
        (∀ H : E.Tuple D p → ℂ, Tuple.IsSmoothT D E H →
          H * F ∈ Tuple.testFns D E Ω) ∧
        ∀ ν : ℕ, Tuple.cNorm D E ν F < ⊤) ∧
    Tuple.testFns D E (∅ : Set (E.Tuple D p)) = {0}
end YangMills.Construction.PeriodicSpace.AlgebraOfTestFns
