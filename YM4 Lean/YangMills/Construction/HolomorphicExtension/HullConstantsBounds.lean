import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HolomorphicExtension
def HullConstantsBoundsStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    let w : ℝ := (1 - ε / 2) * (Real.pi / 2)
    let L : ℝ := 2 * w * ε ^ (-(1 / 2) : ℝ)
    let q : ℝ := Real.exp (Real.arsinh (w / L))
    let t : ℝ := (1 - ε) / ((1 - ε / 2) * (1 - ε / 24))
    (0 < w ∧ w < Real.pi / 2 ∧ 0 < L ∧ w / L = 1 / 2 * ε ^ (1 / 2 : ℝ)) ∧
    1 < q ∧
    (0 < (1 - ε / 2) * (1 - ε / 24) ∧ 0 ≤ t ∧ t < 1) ∧
    ∀ n : ℕ, 1 ≤ n →
      0 < q ^ (-(1 - t) / (n : ℝ)) ∧ q ^ (-(1 - t) / (n : ℝ)) < 1
end YangMills.Construction.HolomorphicExtension
end
