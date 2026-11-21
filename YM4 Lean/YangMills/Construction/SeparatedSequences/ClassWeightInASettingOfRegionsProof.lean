import YangMills.Construction.SeparatedSequences.ClassWeightInASettingOfRegions
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice.DirichletOperators
noncomputable section
namespace YangMills.Construction.SeparatedClasses.MassForm
open SingleSequence SingleSequence.SequenceData
variable (s : SequenceData) (𝒮 : RegionSequence.NestedRegions)
variable {s 𝒮}
theorem scale_eq_levelMeshRatio (hS : s.IsNestedRegions 𝒮) (n : ℕ) :
    𝒮.scale n = s.params.levelMeshRatio n := by
  have hL : (s.data.L : ℝ) ≠ 0 := by
    have := s.data.isAdmissible.2
    exact_mod_cast (by omega : s.data.L ≠ 0)
  have h1 : 𝒮.scale n = (𝒮.L : ℝ) ^ (n : ℤ) * 𝒮.ξ := rfl
  rw [h1, hS.L_eq, hS.ξ_eq]
  change (s.data.L : ℝ) ^ (n : ℤ) * (s.data.L : ℝ) ^ (-(s.data.t : ℤ)) =
    (s.data.L : ℝ) ^ ((n : ℤ) - (s.data.t : ℤ))
  rw [← zpow_add₀ hL, sub_eq_add_neg]
end YangMills.Construction.SeparatedClasses.MassForm
