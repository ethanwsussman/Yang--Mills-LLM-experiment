import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TraceBounds
def pairTraceBound (n R c₄ M err : ℝ) : ℝ :=
  (15 * n) ^ 8 * ((c₄ * ((n ^ 5)⁻¹ + (R ^ 4)⁻¹)) * (2 * (288 * (n ^ 4)⁻¹) + c₄ * ((n ^ 5)⁻¹ + (R ^ 4)⁻¹)) * M ^ 2 +
    6 ^ 4 * ((err + M * (R ^ 5)⁻¹) * (2 * (M + err) + (err + M * (R ^ 5)⁻¹)) * (288 * (n ^ 4)⁻¹) ^ 2))
def PairTraceBoundIsSmall : Prop :=
  ∀ c₄ M C₁ c₁ vt : ℝ, 0 ≤ c₄ → 0 ≤ M → 0 ≤ C₁ → 0 < c₁ → 0 < vt → ∃ A : ℝ, 0 ≤ A ∧ ∀ n R err : ℝ, 1 ≤ n → n ≤ R → 0 ≤ err →
    (vt * n)⁻¹ ≤ 1 → err ≤ C₁ * ((vt * n)⁻¹ + Real.exp (-(c₁ * R))) →
    pairTraceBound n R c₄ M err ≤ A * (n⁻¹ + n ^ 4 * (R ^ 4)⁻¹)
end YangMills.Construction.TraceBounds
end
