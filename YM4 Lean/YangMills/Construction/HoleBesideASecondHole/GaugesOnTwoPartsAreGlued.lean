import YangMills.Construction.HoleBesideASecondHole.GaugeOnAnOrthantOfAShell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ShellOrthant
def orthantGaugeGluingStatement : Prop :=
  ∀ c K : ℝ, 0 < c → 0 < K → ∃ c' K' : ℝ, 0 < c' ∧ 0 < K' ∧
    ∀ (l : ℝ) (o : Fin 4 → ℝ) (s : Fin 4 → ℤ) (i : Fin 4)
      (P Pp Pm : Finset YangMills.Construction.LatticeFractionalIntegration.Lattice4),
      100 ≤ l → (∀ k, s k = 1 ∨ s k = -1 ∨ s k = 0) → s i = 0 →
      (∀ x, x ∈ P ↔ IsInShellOrthant o l s x) →
      (∀ x, x ∈ Pp ↔ IsInShellOrthant o l (Function.update s i 1) x) →
      (∀ x, x ∈ Pm ↔ IsInShellOrthant o l (Function.update s i (-1)) x) →
      HasQuarticGaugeOn c K Pp → HasQuarticGaugeOn c K Pm → HasQuarticGaugeOn c' K' P
end YangMills.Construction.ShellOrthant
end
