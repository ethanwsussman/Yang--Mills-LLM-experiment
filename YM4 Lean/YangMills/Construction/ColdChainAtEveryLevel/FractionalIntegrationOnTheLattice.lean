import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LatticeFractionalIntegration
abbrev Lattice4 : Type := Fin 4 → ℤ
def supNorm (v : Lattice4) : ℕ := Finset.univ.sup fun i => (v i).natAbs
def cubicKernel (v : Lattice4) : ℝ := 1 / ((max 1 (supNorm v) : ℕ) : ℝ) ^ 3
def hardyLittlewoodSobolevStatement : Prop :=
  ∀ p q : ℝ, 1 < p → p < 4 → 1 / q = 1 / p - 1 / 4 → ∃ C : ℝ, 0 < C ∧
    ∀ (A B : Finset Lattice4) (f : Lattice4 → ℝ),
      (∑ x ∈ B, |∑ y ∈ A, cubicKernel (x - y) * f y| ^ q) ^ (1 / q) ≤
        C * (∑ y ∈ A, |f y| ^ p) ^ (1 / p)
end LatticeFractionalIntegration
end YangMills.Construction
end
