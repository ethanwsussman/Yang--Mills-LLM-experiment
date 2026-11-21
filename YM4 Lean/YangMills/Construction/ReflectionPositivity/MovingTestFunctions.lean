import YangMills.Construction.ReflectionPositivity.SeparatedTuplesOfFourSpaceAndTheirFunctionals
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.MovingTests
open InfiniteLattice (AmbientSpace)
open Mirrors (ReflectingHyperplane)
open SeparatedTuples
def parallelHyperplane (M : ReflectingHyperplane) (c' : ℝ) : ReflectingHyperplane :=
  ⟨M.normalVec, M.normalVec_mem, c'⟩
def TranslatesTendsto : Prop :=
  ∀ r₁ : ℕ, 1 ≤ r₁ → ∀ (X : SepTuple) (w : ℕ → AmbientSpace) (v : AmbientSpace), Tendsto w atTop (𝓝 v) →
    (∃ r₀, r₁ ≤ r₀ ∧
      TendstoAdmissibly r₀ (fun r => push (translate (w r)) X) (push (translate v) X)) ∧
    ∀ Y : SepTuple, SepTuple.Composable Y (push (translate v) X) →
      ∃ r₀, r₁ ≤ r₀ ∧
        (∀ r, r₀ ≤ r → SepTuple.Composable Y (push (translate (w r)) X)) ∧
        TendstoAdmissibly r₀ (fun r => SepTuple.juxt Y (push (translate (w r)) X))
          (SepTuple.juxt Y (push (translate v) X)) ∧
        (∀ r, r₀ ≤ r → SepTuple.Composable (push (translate (w r)) X) Y) ∧
        TendstoAdmissibly r₀ (fun r => SepTuple.juxt (push (translate (w r)) X) Y)
          (SepTuple.juxt (push (translate v) X) Y)
def ReflectionsTendsto : Prop :=
  ∀ r₁ : ℕ, 1 ≤ r₁ → ∀ (M : ReflectingHyperplane) (X₁ X₂ : SepTuple), X₁ ∈ supportedIn M.positiveSide →
    X₂ ∈ supportedIn M.positiveSide → ∀ c : ℕ → ℝ, (∀ r, r₁ ≤ r → c r ≤ M.offset) →
      Tendsto c atTop (𝓝 M.offset) →
        (∀ r, r₁ ≤ r →
          SepTuple.Composable (push (parallelHyperplane M (c r)).reflect X₁) X₂) ∧
        ∃ r₀, r₁ ≤ r₀ ∧
          TendstoAdmissibly r₀
            (fun r => SepTuple.juxt (push (parallelHyperplane M (c r)).reflect X₁) X₂)
            (SepTuple.juxt (push M.reflect X₁) X₂)
def Statement : Prop := TranslatesTendsto ∧ ReflectionsTendsto
end YangMills.Construction.ReflectionPositivity.MovingTests
