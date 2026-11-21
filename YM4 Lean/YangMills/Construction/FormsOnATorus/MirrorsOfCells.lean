import YangMills.Construction.ClusterExpansionOfAStep.IsometriesOfTheEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusFields
def cellReflection (c : ℕ) (u k : Fin 4 → ℤ) : TorusIsometry where
  axisPerm := 1
  axisSign := fun i => (-1) ^ (k i).natAbs
  offset := fun i => u i + c * k i - (-1) ^ (k i).natAbs * u i
  axisSign_unit := fun i => neg_one_pow_eq_or ℤ (k i).natAbs
def integerCoords {n : ℕ} (x : TorusSite n) : Fin 4 → ℤ := fun i => ((x i).val : ℤ)
def plaquetteCellImage {n : ℕ} (c M : ℕ) (p : TorusPlaquette n) (k : Fin 4 → Fin M) : TorusPlaquette n :=
  (cellReflection c (integerCoords p.1) fun i => ((k i : ℕ) : ℤ)).mapPlaquette p
end YangMills.Construction.TorusFields
end
