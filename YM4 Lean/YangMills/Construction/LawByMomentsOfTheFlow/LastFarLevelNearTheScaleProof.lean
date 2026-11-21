import YangMills.Construction.LawByMomentsOfTheFlow.GapOfTheSupportsFromAbove
import YangMills.Construction.LawByMomentsOfTheFlow.LastFarLevelNearTheScale
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
open Classical in
private theorem separationLevel_le_and_separated {k : ℕ} (P : LevelData k) (ℓ : TorusLumps.StepParameters) (β : ℝ) :
    P.separationLevel ℓ β ≤ P.windowLevel ∧ P.SeparatedBelow ℓ β (P.separationLevel ℓ β) := by
  unfold LevelData.separationLevel
  refine ⟨Nat.findGreatest_le _, Nat.findGreatest_spec (m := 0) (Nat.zero_le _) ?_⟩
  intro u hu
  exact absurd hu (Nat.not_lt_zero u)
theorem separationLevelNearScale_holds (hA : separationUpperBoundStatement) :
    separationLevelNearScaleStatement := by
  intro ℓ hℓ k hk R d hd
  have hL3 : 3 ≤ ℓ.side := by
    have := hℓ.L_ge
    omega
  obtain ⟨C₁, hC₁, hgap⟩ := hA ℓ.side hℓ.L_odd hL3 k hk R d hd
  have hLr : (2 : ℝ) ≤ ℓ.side := by exact_mod_cast (by omega : 2 ≤ ℓ.side)
  refine ⟨1 + C₁, fun P hF β => ?_⟩
  obtain ⟨hle, hfar⟩ := separationLevel_le_and_separated P ℓ β
  rcases Nat.lt_or_ge P.scaleLevel (P.separationLevel ℓ β) with hts | hts
  · obtain ⟨e, he⟩ : ∃ e : ℕ, P.separationLevel ℓ β = P.scaleLevel + e + 1 :=
      ⟨P.separationLevel ℓ β - P.scaleLevel - 1, by omega⟩
    have h8 := (hfar (P.scaleLevel + e) (by omega)).2
    have hg := hgap P hF (P.scaleLevel + e) (by omega)
    have h8r : (8 : ℝ) < (P.separation ℓ.side (P.scaleLevel + e) : ℝ) := by exact_mod_cast h8
    have hz : (ℓ.side : ℝ) ^ ((P.scaleLevel : ℤ) - ((P.scaleLevel + e : ℕ) : ℤ)) = ((ℓ.side : ℝ) ^ e)⁻¹ := by
      have : (P.scaleLevel : ℤ) - ((P.scaleLevel + e : ℕ) : ℤ) = -(e : ℤ) := by
        push_cast
        ring
      rw [this, zpow_neg, zpow_natCast]
    rw [hz] at hg
    have hpow : (e : ℝ) + 1 ≤ (ℓ.side : ℝ) ^ e := by
      have h1 : (2 : ℝ) ^ e ≤ (ℓ.side : ℝ) ^ e := pow_le_pow_left₀ (by norm_num) hLr e
      have h2 : (e : ℝ) + 1 ≤ (2 : ℝ) ^ e := by
        have : e + 1 ≤ 2 ^ e := Nat.lt_two_pow_self
        exact_mod_cast this
      linarith
    have hepos : (0 : ℝ) < (ℓ.side : ℝ) ^ e := by positivity
    have h6 : 6 < C₁ * ((ℓ.side : ℝ) ^ e)⁻¹ := by linarith
    have h7 : 6 * (ℓ.side : ℝ) ^ e < C₁ := by
      have := mul_lt_mul_of_pos_right h6 hepos
      rwa [mul_assoc, inv_mul_cancel₀ (ne_of_gt hepos), mul_one] at this
    have her : (P.separationLevel ℓ β : ℝ) = (P.scaleLevel : ℝ) + e + 1 := by
      rw [he]
      push_cast
      ring
    rw [her]
    nlinarith
  · have : (P.separationLevel ℓ β : ℝ) ≤ (P.scaleLevel : ℝ) := by exact_mod_cast hts
    linarith
end YangMills.Construction.LevelTestFunctions
end
