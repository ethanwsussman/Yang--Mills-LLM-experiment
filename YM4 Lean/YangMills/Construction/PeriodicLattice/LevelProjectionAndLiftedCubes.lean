import YangMills.Construction.Geometry.TorusMetric
import YangMills.Construction.Lattice.LevelCoordinates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def levelProj (L m K k : ℕ) (w : Fin 4 → ℝ) : FourTorus L m :=
  TorusMetric.torusProj (torusSide L m) (meshSize L (levelDepth K k) • w)
def IsGridPoint (W γ : ℝ) : Prop := ∃ a : ℤ, γ = W * ((a : ℝ) + 1 / 2)
theorem levelProj_eq_iff_isLevelLift {L : ℕ} (hL : L ≠ 0) (m K k : ℕ) (x : FourTorus L m)
    (w : Fin 4 → ℝ) : levelProj L m K k w = x ↔ IsLevelLift L m K k x w := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have hmul : ∀ r : ℝ, (L : ℝ) ^ levelDepth K k * (meshSize L (levelDepth K k) * r) = r := fun r => by
    simp only [meshSize]
    rw [← mul_assoc, ← zpow_add₀ hL', add_neg_cancel, zpow_zero, one_mul]
  have hmul' : ∀ r : ℝ, meshSize L (levelDepth K k) * ((L : ℝ) ^ levelDepth K k * r) = r := fun r => by
    simp only [meshSize]
    rw [← mul_assoc, ← zpow_add₀ hL', neg_add_cancel, zpow_zero, one_mul]
  constructor
  · intro h
    refine ⟨meshSize L (levelDepth K k) • w, fun μ => ?_, fun μ => ?_⟩
    · exact congrFun h μ
    · simp [toLevelUnits, hmul]
  · rintro ⟨v, hv, hw⟩
    funext μ
    simp only [levelProj, TorusMetric.torusProj, Pi.smul_apply, smul_eq_mul, hw μ, toLevelUnits,
      hmul', hv μ]
end PeriodicLattice
end YangMills.Construction
