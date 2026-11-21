import YangMills.Construction.HoleBesideASecondHole.GaugeOnAnOrthantOfAShell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ShellOrthant
def ShellQuarticGauge : Prop :=
  ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ (l : ℝ) (o : Fin 4 → ℝ) (P : Finset LatticeFractionalIntegration.Lattice4),
    100 ≤ l → (∀ x, x ∈ P ↔ IsInShellOrthant o l (fun _ => 0) x) → HasQuarticGaugeOn c K P
end ShellOrthant
end YangMills.Construction
end
