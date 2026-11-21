import YangMills.Construction.EuclideanFunctionals.PulledDownNormsTheInsertionValueAndClassesOfTensors
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.AboveHeight
abbrev above (c : ℝ) : Submodule ℂ FreeSep := finCombIn {x | c < x 3}
def IsThinInsert (c : ℝ) (h : R4 → ℂ) : Prop :=
  h ∈ C1c ℂ ∧ supp h ⊆ {x | |x 3| < c}
def ClassPullDown {s : SharpScale} {S : ConnFamily}
    (σ : EuclidFunctionalWithRecon s S) (c : ℝ) : Prop :=
  ∀ F ∈ above c,
    F ∈ finCombIn upperHalf ∧
    reconClass σ F = ResolvedOps.expComplex σ.recon.ham (c : ℂ)
      (reconClass σ (pullDown c F)) ∧
    ‖reconClass σ F‖ ≤ heightNorm σ c F
def ConjLinearLeft (S : ConnFamily) (c : ℝ) : Prop :=
  ∀ F ∈ above c, ∀ F' ∈ above c, ∀ A ∈ above c,
    ∀ h, IsThinInsert c h → ∀ a a' : ℂ,
      insertion S (a • F + a' • F') h A =
        conj a * insertion S F h A + conj a' * insertion S F' h A
def LinearInsert (S : ConnFamily) (c : ℝ) : Prop :=
  ∀ F ∈ above c, ∀ A ∈ above c,
    ∀ h, IsThinInsert c h → ∀ h', IsThinInsert c h' → ∀ a a' : ℂ,
      insertion S F (fun x => a * h x + a' * h' x) A =
        a * insertion S F h A + a' * insertion S F h' A
def LinearRight (S : ConnFamily) (c : ℝ) : Prop :=
  ∀ F ∈ above c, ∀ A ∈ above c, ∀ A' ∈ above c,
    ∀ h, IsThinInsert c h → ∀ a a' : ℂ,
      insertion S F h (a • A + a' • A') =
        a * insertion S F h A + a' * insertion S F h A'
def Holds : Prop :=
  ∀ (s : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon s S) (c : ℝ), 0 < c →
    ClassPullDown σ c ∧ ConjLinearLeft S c ∧
      LinearInsert S c ∧ LinearRight S c
end YangMills.Construction.EuclideanFunctionals.AboveHeight
