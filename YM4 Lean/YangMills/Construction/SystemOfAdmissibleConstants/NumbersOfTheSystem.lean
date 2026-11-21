import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace AdmissibleConstants
def truncatedDist (d : ℝ) : ℝ := min d 1
def cumulantConstant (L : ℕ) (A b : ℝ) : ℝ :=
  2 * max (10 * 2 ^ 53 * (L : ℝ) ^ 5 * A * Real.exp (b + b ^ ((20 : ℝ) / 19)))
    (24 * 2 ^ 40 * (L : ℝ) ^ 12)
def transferConstant (L : ℕ) (A b : ℝ) : ℝ :=
  max (10 * 2 ^ 20 * A * Real.exp (3 * b)) (384 * (L : ℝ) ^ 4)
def cumulantBound (L : ℕ) (A b : ℝ) (n : ℕ) (d R : ℝ) : ℝ :=
  (n.factorial : ℝ) * (cumulantConstant L A b * (1 + R) ^ 4 * ((n : ℝ) / truncatedDist d) ^ 5) ^ n
def onePointBound (L : ℕ) (A b R : ℝ) : ℝ := transferConstant L A b * (1 + R) ^ 4
def torusCumulantBound (L : ℕ) (A b : ℝ) (n : ℕ) (d : ℝ) : ℝ :=
  (n.factorial : ℝ) * (cumulantConstant L A b * ((n : ℝ) / truncatedDist d) ^ 5) ^ n
def growthPrefactor (d : ℝ) : ℝ := Real.exp (truncatedDist d ^ (-5 : ℤ))
def growthRate (L : ℕ) (A b R : ℝ) : ℝ := Real.exp 5 * cumulantConstant L A b * (1 + R) ^ 4
end AdmissibleConstants
end YangMills.Construction
end
