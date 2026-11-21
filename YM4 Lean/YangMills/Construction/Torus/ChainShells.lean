import YangMills.Construction.Torus.SeparatedChains
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Torus.ChainShells
variable {d : ℕ} {S : ℝ}
structure ShellFacts (L : ℕ) (ξ : ℝ) (M t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)) : Prop where
  succ_isCubeUnion : ∀ n ≤ lastNonemptyIndex Ω,
    IsCubeUnion ((M : ℝ) * scaleSpacing L ξ n) (Ω (n + 1))
  shell_eq_sUnion : ∀ n ≤ lastNonemptyIndex Ω, shell Ω n =
    ⋃₀ {Q ∈ cubePartition d S ((M : ℝ) * scaleSpacing L ξ n) | Q ⊆ Ω n ∧ ¬ Q ⊆ Ω (n + 1)}
  shell_subset : ∀ n ≤ lastNonemptyIndex Ω, shell Ω n ⊆
    Ω n ∩ cubeComplement ((M : ℝ) * scaleSpacing L ξ n) (Ω (n + 1))
  zero_eq_iUnion_shell : Ω 0 = ⋃ m ∈ Iic (lastNonemptyIndex Ω), shell Ω m
  shell_eq_empty : ∀ m, lastNonemptyIndex Ω < m → m ≤ t → shell Ω m = ∅
def ShellsStatement : Prop :=
  ∀ (d L : ℕ) (S ξ : ℝ) (M R₁ t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)), 0 < d → 3 ≤ L → Odd L →
    IsSeparatedChain L ξ M R₁ t Ω → ShellFacts L ξ M t Ω
end YangMills.Construction.Torus.ChainShells
end
