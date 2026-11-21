import Mathlib
set_option autoImplicit false
open scoped NNReal ENNReal
noncomputable section
namespace YangMills.Construction.Families
universe u v w
def positiveNat : Set ℕ := {n | 1 ≤ n}
section FamilyMaps
variable {ι : Type u} {P : Type v}
abbrev Family (P : Type v) (V : Set ι) : Type (max u v) := V → P
abbrev Tuple (P : Type v) (n : ℕ) : Type v := Family P (Set.Icc 1 n)
end FamilyMaps
section UnorderedSums
variable {J : Type w}
def ennrealSum (c : J → ℝ≥0) : ℝ≥0∞ := ⨆ F : Finset J, ((∑ j ∈ F, c j : ℝ≥0) : ℝ≥0∞)
def IsAbsSummable (c : J → ℂ) : Prop := ennrealSum (fun j => ‖c j‖₊) < ∞
def familySum (c : J → ℂ) : ℂ := ∑' j, c j
end UnorderedSums
end YangMills.Construction.Families
