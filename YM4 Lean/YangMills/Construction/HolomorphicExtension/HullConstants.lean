import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HolomorphicExtension.HullConstants
def halfWidth (ε : ℝ) : ℝ :=
  (1 - ε / 2) * (Real.pi / 2)
def length (ε : ℝ) : ℝ :=
  2 * halfWidth ε * ε ^ (-(1 / 2) : ℝ)
def ratio (ε : ℝ) : ℝ :=
  Real.exp (Real.arsinh (halfWidth ε / length ε))
def radius (ε : ℝ) : ℝ :=
  (length ε ^ 2 + halfWidth ε ^ 2) ^ (1 / 2 : ℝ)
def exponent (ε : ℝ) : ℝ :=
  (1 - ε) / ((1 - ε / 2) * (1 - ε / 24))
def boundFactor (n : ℕ+) (ε : ℝ) : ℝ :=
  (2 : ℝ) ^ (n : ℕ) *
    (1 - ratio ε ^ (-(1 - exponent ε) / (((n : ℕ) : ℝ)))) ^ (-(((n : ℕ) : ℤ)))
end YangMills.Construction.HolomorphicExtension.HullConstants
end
