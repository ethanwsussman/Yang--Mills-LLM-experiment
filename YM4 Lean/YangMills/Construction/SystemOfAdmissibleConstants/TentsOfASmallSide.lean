import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace SystemOfAdmissibleConstants
open YangMills.Construction.TestFunctions YangMills.Construction.TorusMetric
def scaledIntLattice (ε : ℝ) : Set (Fin 4 → ℝ) := {α | ∀ μ, ∃ k : ℤ, α μ = ε * k}
def hatFunction (ε : ℝ) (α x : Fin 4 → ℝ) : ℝ := ∏ μ, max 0 (1 - |x μ - α μ| / ε)
def torusHatFunction {ℓ : ℝ} (ε : ℝ) (α : Fin 4 → ℝ) (x : Torus4 ℓ) : ℝ :=
  ∏ μ, max 0 (1 - ‖x μ - ((α μ : ℝ) : AddCircle ℓ)‖ / ε)
def scaledIntLatticeFundDomain (ℓ ε : ℝ) : Set (Fin 4 → ℝ) :=
  {α | α ∈ scaledIntLattice ε ∧ ∀ μ, 0 ≤ α μ ∧ α μ < ℓ}
def hatPartitionOfUnity_prop : Prop :=
  (∀ ε : ℝ, 0 < ε →
    (∀ α x, 0 ≤ hatFunction ε α x ∧ hatFunction ε α x ≤ 1) ∧
    (∀ x, {α | α ∈ scaledIntLattice ε ∧ hatFunction ε α x ≠ 0}.Finite ∧
      ∑ᶠ α : scaledIntLattice ε, hatFunction ε α x = 1) ∧
    (∀ α x, hatFunction ε α x ≠ 0 → ∀ μ, |x μ - α μ| < ε) ∧
    (∀ α, tsupport (hatFunction ε α) ⊆ closedBallR4 α (2 * ε)) ∧
    (∀ α x z, |hatFunction ε α x - hatFunction ε α z| ≤ 2 / ε * euclidDistR4 x z) ∧
    (∀ (M : ℝ), 1 ≤ M → 2 * ε ≤ 1 → ∀ f : (Fin 4 → ℝ) → ℝ, IsBoundedFun f → IsLipschitzFor euclidDistR4 f →
      ∀ α, IsLipschitzFor euclidDistR4 (fun x => hatFunction ε α x * f x) ∧
        max (uniformNorm fun x => hatFunction ε α x * f x)
          (2 * ε * lipConstR4 fun x => hatFunction ε α x * f x) ≤ 5 * sharpNormR4 M f) ∧
    (∀ (R : ℝ), 0 < R → ∀ f : (Fin 4 → ℝ) → ℝ, (∃ y, tsupport f ⊆ closedBallR4 y R) →
      {α | α ∈ scaledIntLattice ε ∧ ∃ x, hatFunction ε α x * f x ≠ 0}.Finite ∧
      ({α | α ∈ scaledIntLattice ε ∧ ∃ x, hatFunction ε α x * f x ≠ 0}.ncard : ℝ) ≤ (2 * R / ε + 3) ^ 4)) ∧
  (∀ ℓ ε : ℝ, 0 < ε → ∀ q : ℕ, 3 ≤ q → ℓ = q * ε →
    (∀ α (x : Torus4 ℓ), 0 ≤ torusHatFunction ε α x ∧ torusHatFunction ε α x ≤ 1) ∧
    (∀ x : Torus4 ℓ, ∑ᶠ α : scaledIntLatticeFundDomain ℓ ε, torusHatFunction ε α x = 1) ∧
    (∀ α, tsupport (torusHatFunction (ℓ := ℓ) ε α) ⊆ closedBallTorus (torusProj ℓ α) (2 * ε)) ∧
    (∀ α (x z : Torus4 ℓ), |torusHatFunction ε α x - torusHatFunction ε α z| ≤ 2 / ε * euclidDistTorus x z) ∧
    (∀ (M : ℝ), 1 ≤ M → 2 * ε ≤ 1 → ∀ f : Torus4 ℓ → ℝ, IsBoundedFun f →
      IsLipschitzFor euclidDistTorus f → ∀ α, IsLipschitzFor euclidDistTorus (fun x => torusHatFunction ε α x * f x) ∧
        max (uniformNorm fun x => torusHatFunction ε α x * f x)
          (2 * ε * lipConstTorus fun x => torusHatFunction ε α x * f x) ≤ 5 * sharpNormTorus M f) ∧
    (∀ (R : ℝ), 0 < R → ∀ f : Torus4 ℓ → ℝ, (∃ y, tsupport f ⊆ closedBallTorus y R) →
      ({α | α ∈ scaledIntLatticeFundDomain ℓ ε ∧ ∃ x, torusHatFunction ε α x * f x ≠ 0}.ncard : ℝ) ≤
        min ((2 * R / ε + 3) ^ 4) ((ℓ / ε) ^ 4)))
end SystemOfAdmissibleConstants
end YangMills.Construction
end
