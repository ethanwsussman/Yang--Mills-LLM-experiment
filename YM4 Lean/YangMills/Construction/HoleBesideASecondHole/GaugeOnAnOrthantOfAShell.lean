import YangMills.Construction.HoleBesideASecondHole.AShellIsFilled
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LatticeFractionalIntegration
namespace ShellOrthant
def orthantLower (l : ℝ) (s : ℤ) : ℝ := if s = 1 then -(l / 2) else -(1.9 * l)
def orthantUpper (l : ℝ) (s : ℤ) : ℝ := if s = -1 then l / 2 else 1.9 * l
def IsInShellOrthant (o : Fin 4 → ℝ) (l : ℝ) (s : Fin 4 → ℤ) (x : LatticeFractionalIntegration.Lattice4) : Prop :=
  (∀ k, orthantLower l (s k) ≤ (x k : ℝ) - o k ∧ (x k : ℝ) - o k ≤ orthantUpper l (s k)) ∧
    ShellFilling.IsBeyondSupDist o (1.1 * l) x
def HasQuarticGaugeOn (c K : ℝ) (P : Finset LatticeFractionalIntegration.Lattice4) : Prop :=
  ∀ (X : LatticeFractionalIntegration.Lattice4 → Fin 4 → UnitQuaternion) (ε : ℝ), 0 ≤ ε → ε ≤ c →
    ShellFilling.plaquetteDefect P X ≤ ε ^ 2 →
    ∃ γ : LatticeFractionalIntegration.Lattice4 → UnitQuaternion,
      ∑ b ∈ bondsOf P, ‖((latticeGaugeTransform γ X b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 ≤ (K * ε) ^ 4
def orthantQuarticGaugeStatement : Prop :=
  ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ (l : ℝ) (o : Fin 4 → ℝ) (s : Fin 4 → ℤ)
    (P : Finset LatticeFractionalIntegration.Lattice4),
    100 ≤ l → (∀ k, s k = 1 ∨ s k = -1) → (∀ x, x ∈ P ↔ IsInShellOrthant o l s x) → HasQuarticGaugeOn c K P
end ShellOrthant
end YangMills.Construction
end
