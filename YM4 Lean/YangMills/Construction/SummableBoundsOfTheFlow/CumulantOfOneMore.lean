import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Cumulants
variable {Ω ι : Type} [DecidableEq ι]
def cumulantWeight (n : ℕ) : ℝ := (-1 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ)
def blockProd (X : ι → Ω → ℝ) (B : Finset ι) : Ω → ℝ := fun ω => ∏ k ∈ B, X k ω
def jointCumulant (E : (Ω → ℝ) → ℝ) (S : Finset ι) (X : ι → Ω → ℝ) : ℝ :=
  ∑ π : Finpartition S, cumulantWeight π.parts.card * ∏ B ∈ π.parts, E (blockProd X B)
end Cumulants
end YangMills.Construction
end
