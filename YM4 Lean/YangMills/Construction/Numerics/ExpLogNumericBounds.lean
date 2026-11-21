import Mathlib
namespace YangMills.Construction.Numerics
def ExpLogNumericBounds : Prop :=
  Real.exp (1 / 100) < 1.0101 ∧
  Real.exp (9 / 400) < 1.0228 ∧
  Real.exp (1 / 20) < 1.0513 ∧
  Real.exp (3 / 40) < 1.078 ∧
  Real.exp (1 / 8) < 1.1332 ∧
  Real.exp (1 / 5) < 1.2215 ∧
  Real.log (9 / 8) < 0.1178 ∧
  1 / 8 < Real.log 2 ∧
  Real.log 10 < Real.pi
end YangMills.Construction.Numerics
