import YangMills.Construction.TorusOrFourSpace.TestFunctionsAndDistributionsOnASet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.SupportNormFacts
open Kind.Tuple
def Claim : Prop :=
  ∀ (D : Params) (n : ℕ+),
    (∀ (F H : Kind.euclidean.Tuple D n → ℂ) (c : ℂ),
      (∀ C : Set (Kind.euclidean.Tuple D n), IsClosedT D Kind.euclidean C →
        (∀ y, y ∉ C → F y = 0) → supportT D Kind.euclidean F ⊆ C) ∧
      supportT D Kind.euclidean (F + H) ⊆
        supportT D Kind.euclidean F ∪ supportT D Kind.euclidean H ∧
      supportT D Kind.euclidean (c • F) ⊆ supportT D Kind.euclidean F ∧
      supportT D Kind.euclidean (F * H) ⊆
        supportT D Kind.euclidean F ∩ supportT D Kind.euclidean H) ∧
    (∀ F : Kind.euclidean.Tuple D n → ℂ, IsSmoothT D Kind.euclidean F →
      IsCompactT D Kind.euclidean (supportT D Kind.euclidean F) →
      ∀ ν : ℕ, cNorm D Kind.euclidean ν F < ⊤) ∧
    (∀ (F H : Kind.euclidean.Tuple D n → ℂ) (ν : ℕ), IsSmoothT D Kind.euclidean F →
      IsSmoothT D Kind.euclidean H → cNorm D Kind.euclidean ν F < ⊤ →
      cNorm D Kind.euclidean ν H < ⊤ →
      cNorm D Kind.euclidean ν (F + H) ≤
        cNorm D Kind.euclidean ν F + cNorm D Kind.euclidean ν H) ∧
    ∀ Ω : Set (Kind.euclidean.Tuple D n), IsOpenT D Kind.euclidean Ω →
      (∃ S : Submodule ℂ (Kind.euclidean.Tuple D n → ℂ),
        (S : Set (Kind.euclidean.Tuple D n → ℂ)) = testFns D Kind.euclidean Ω) ∧
      (∀ F ψ : Kind.euclidean.Tuple D n → ℂ, IsSmoothT D Kind.euclidean F →
        ψ ∈ testFns D Kind.euclidean Ω → ψ * F ∈ testFns D Kind.euclidean Ω) ∧
      (∀ (Fs : ℕ+ → testFns D Kind.euclidean Ω) (F : testFns D Kind.euclidean Ω),
        TendstoInTestFns Fs F →
        ∀ C : Set (Kind.euclidean.Tuple D n), IsClosedT D Kind.euclidean C →
          (∀ t, supportT D Kind.euclidean (Fs t).1 ⊆ C) → supportT D Kind.euclidean F.1 ⊆ C) ∧
      ∀ (A : ℕ+) (Fs : Fin (A : ℕ) → ℕ+ → testFns D Kind.euclidean Ω)
        (F : Fin (A : ℕ) → testFns D Kind.euclidean Ω),
        (∀ a, TendstoInTestFns (Fs a) (F a)) →
        ∃ (hs : ∀ t, ∑ a, (Fs a t).1 ∈ testFns D Kind.euclidean Ω)
          (h : ∑ a, (F a).1 ∈ testFns D Kind.euclidean Ω),
          TendstoInTestFns (fun t => ⟨∑ a, (Fs a t).1, hs t⟩) ⟨∑ a, (F a).1, h⟩
end YangMills.Construction.PeriodicSpace.SupportNormFacts
