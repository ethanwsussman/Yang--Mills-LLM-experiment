import YangMills.Construction.Functions.WeightedModulusSum
import YangMills.Construction.Lattice.SettingOfTheTorusBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SublevelSets
open WeightedModulusSum
def SublevelSetsOpen : Prop :=
  ∀ (n : ℕ) (a : Weights n) (r : ℝ), 0 < r →
    IsOpen {z : Fin n → ℂ | a.weightedNorm z < r} ∧
      (0 : Fin n → ℂ) ∈ {z : Fin n → ℂ | a.weightedNorm z < r} ∧
      (r = 1 → {z : Fin n → ℂ | a.weightedNorm z < r} = a.unitSet)
def SourceDisksAreUnitSets : Prop :=
  ∀ (D : TorusBound.Setup) (n : ℕ) (f : Fin n → D.Torus → ℝ) (r : ℝ),
    D.IsRealFamily f → (∀ i, 0 < D.sharpNorm (f i)) → 0 < r →
      ∃ a : Weights n,
        (∀ i, a.c i = D.sharpNorm (f i) / r) ∧
        D.disc r f = a.unitSet ∧
        (∀ z : Fin n → ℂ, a.weightedNorm z = 1 / r * ∑ i, ‖z i‖ * D.sharpNorm (f i)) ∧
        (n : ℝ) ^ n * ∏ i, a.c i = ((n : ℝ) / r) ^ n * ∏ i, D.sharpNorm (f i)
def SublevelAndDiskStatement : Prop := SublevelSetsOpen ∧ SourceDisksAreUnitSets
end YangMills.Construction.SublevelSets
end
