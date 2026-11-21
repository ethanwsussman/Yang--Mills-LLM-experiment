import YangMills.Construction.ClusterExpansionOfAStep.AnglesAlongOneDirection
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderAtAbelianFields
import YangMills.Construction.ClusterExpansionOfAStep.WrittenFieldHasItsCurvature
import YangMills.Construction.SummableBoundsOfTheFlow.OneNumberOfOneTotal
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.FamilyNorms
open TorusLumps TorusFields BlockAverages
private def planeAngles : Fin 4 → Fin 4 → ℝ :=
  fun i j => if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0
private theorem planeAngles_antisymm (i j : Fin 4) : planeAngles i j = - planeAngles j i := by
  unfold planeAngles
  by_cases h1 : i = 0 ∧ j = 1
  · obtain ⟨rfl, rfl⟩ := h1
    simp
  · by_cases h2 : i = 1 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h2
      simp
    · have h1' : ¬ (j = 0 ∧ i = 1) := fun h => h2 ⟨h.2, h.1⟩
      have h2' : ¬ (j = 1 ∧ i = 0) := fun h => h1 ⟨h.2, h.1⟩
      simp [h1, h2, h1', h2']
private theorem planeAngles_cases (i j : Fin 4) :
    planeAngles i j = 0 ∨ planeAngles i j = 1 ∨ planeAngles i j = -1 := by
  unfold planeAngles
  split_ifs <;> simp
private theorem planeAngles_integral (i j : Fin 4) :
    ∃ z : ℤ, ((1 : ℕ) : ℝ) * planeAngles i j = z := by
  rcases planeAngles_cases i j with h | h | h <;> rw [h]
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨-1, by simp⟩
private theorem abs_planeAngles_le (i j : Fin 4) : |planeAngles i j| ≤ 1 := by
  rcases planeAngles_cases i j with h | h | h <;> rw [h] <;> simp
private theorem curvatureAlong_planeAngles :
    curvatureAlong quaternionI planeAngles = unitPlaneCurvature := by
  funext i j
  unfold curvatureAlong planeAngles unitPlaneCurvature planeCurvature
  by_cases h1 : i = 0 ∧ j = 1
  · simp [h1]
  · by_cases h2 : i = 1 ∧ j = 0
    · simp only [h2, if_true, and_self]
      have hn : ¬ ((1 : Fin 4) = 0 ∧ (0 : Fin 4) = 1) := by simp
      obtain ⟨rfl, rfl⟩ := h2
      simp only [hn, if_false, if_true, and_self]
      exact neg_one_smul ℝ (quaternionI : imaginaryQuaternions)
    · simp [h1, h2]
private theorem norm_quaternionI : ‖quaternionI‖ = 1 := by
  have h : Quaternion.normSq ((quaternionI : imaginaryQuaternions) : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_def']
    simp [quaternionI]
  have h2 : ‖((quaternionI : imaginaryQuaternions) : ℍ[ℝ])‖ *
      ‖((quaternionI : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, h]
  have h3 : ‖quaternionI‖ = ‖((quaternionI : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
  rw [h3]
  nlinarith [norm_nonneg ((quaternionI : imaginaryQuaternions) : ℍ[ℝ])]
abbrev _root_.YangMills.SharedProofs.p9532 := @norm_quaternionI
theorem equalTotalsEqualLimitStatement_holds (hA : SecondOrderAtAbelianFields)
    (hW : AbelianFieldOfAnglesHasCurvature) : equalTotalsEqualLimitStatement := by
  intro p hp C h h' v v' H H' htot hv hv'
  obtain ⟨w, hw, hwε⟩ := (hA p hp C h H).2.2.2.2.2.2.2 planeAngles 1 quaternionI
    planeAngles_antisymm one_pos planeAngles_integral norm_quaternionI
  obtain ⟨w', hw', hwε'⟩ := (hA p hp C h' H').2.2.2.2.2.2.2 planeAngles 1 quaternionI
    planeAngles_antisymm one_pos planeAngles_integral norm_quaternionI
  rw [curvatureAlong_planeAngles] at hw hw'
  have e1 : w = v := hw.unique hv
  have e2 : w' = v' := hw'.unique hv'
  subst e1 e2
  by_contra hne
  have hd : 0 < |w - w'| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n₁, hn₁⟩ := hwε (|w - w'| / 16) (by positivity)
  obtain ⟨n₂, hn₂⟩ := hwε' (|w - w'| / 16) (by positivity)
  have hσ : 0 < p.threshold := hp.σ_pos
  have hs0 : 0 < min 1 (p.threshold / 2) := lt_min one_pos (by linarith)
  obtain ⟨n₃, hn₃⟩ := exists_nat_gt (2 * Real.pi / min 1 (p.threshold / 2))
  set n : ℕ := max (max (max n₁ n₂) (max n₃ p.n₀)) 1 with hn
  have h1n : 1 ≤ n := le_max_right _ _
  haveI : NeZero n := ⟨by omega⟩
  have l1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have l2 : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have l3 : n₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have l4 : p.n₀ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  set γ : ℝ := 2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 with hγ
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast h1n
  have hγ0 : 0 < γ := by
    rw [hγ]
    have := Real.pi_pos
    positivity
  have hγσ : γ < min 1 (p.threshold / 2) := by
    have a1 : 2 * Real.pi / min 1 (p.threshold / 2) < n := lt_of_lt_of_le hn₃ (by exact_mod_cast l3)
    have a2 : 2 * Real.pi < n * min 1 (p.threshold / 2) := by
      rwa [div_lt_iff₀ hs0] at a1
    have a3 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have a4 : 2 * Real.pi < (n : ℝ) ^ 2 * min 1 (p.threshold / 2) :=
      lt_of_lt_of_le a2 (mul_le_mul_of_nonneg_right a3 hs0.le)
    rw [hγ, div_lt_iff₀ (by positivity)]
    simpa [mul_comm] using a4
  have hγ1 : γ < 1 := lt_of_lt_of_le hγσ (min_le_left _ _)
  have hγ2 : γ < p.threshold / 2 := lt_of_lt_of_le hγσ (min_le_right _ _)
  set V := abelianFieldOfAngles n quaternionI γ planeAngles with hV
  have hAb : IsAbelianWithCurvature quaternionI planeAngles γ V :=
    hW n quaternionI planeAngles 1 norm_quaternionI planeAngles_antisymm planeAngles_integral
  have hcold : IsCold p.threshold V := by
    intro x μ ν hμν
    have e := hAb.2 x μ ν hμν
    have b := norm_coe_expUnit_smul_sub_one_le quaternionI norm_quaternionI (γ * planeAngles μ ν)
    have c : TorusFields.curvature V x μ ν =
        ‖((expUnit ((γ * planeAngles μ ν) • quaternionI) : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
      unfold TorusFields.curvature
      rw [e]
    rw [c]
    refine lt_of_le_of_lt b ?_
    have q0 := abs_planeAngles_le μ ν
    have q1 : |γ * planeAngles μ ν| ≤ γ := by
      rw [abs_mul, abs_of_pos hγ0]
      nlinarith
    have q2 : (γ * planeAngles μ ν) ^ 2 ≤ γ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) q1 2
    nlinarith
  have t := htot n l4 V hcold
  have b1 := hn₁ n l1 V hAb
  have b2 := hn₂ n l2 V hAb
  set N : ℝ := ((Finset.univ : Finset (TorusSite n)).card : ℝ) with hN
  have hNpos : 0 < N := by
    rw [hN]
    exact_mod_cast Finset.card_pos.mpr ⟨0, Finset.mem_univ _⟩
  have s1 : |∑ y, centered h n y V - N * (γ ^ 2 / 2 * w)| ≤ N * (|w - w'| / 16 * γ ^ 2) := by
    have : ∑ y, centered h n y V - N * (γ ^ 2 / 2 * w) =
        ∑ y : TorusSite n, (centered h n y V - γ ^ 2 / 2 * w) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun y _ => b1 y).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have s2 : |∑ y, centered h' n y V - N * (γ ^ 2 / 2 * w')| ≤ N * (|w - w'| / 16 * γ ^ 2) := by
    have : ∑ y, centered h' n y V - N * (γ ^ 2 / 2 * w') =
        ∑ y : TorusSite n, (centered h' n y V - γ ^ 2 / 2 * w') := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun y _ => b2 y).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [t] at s1
  have s3 : |N * (γ ^ 2 / 2 * w) - N * (γ ^ 2 / 2 * w')| ≤ 2 * (N * (|w - w'| / 16 * γ ^ 2)) := by
    have := abs_sub_le (N * (γ ^ 2 / 2 * w)) (∑ y, centered h' n y V) (N * (γ ^ 2 / 2 * w'))
    rw [abs_sub_comm (N * (γ ^ 2 / 2 * w)) (∑ y, centered h' n y V)] at this
    linarith
  have s4 : N * (γ ^ 2 / 2 * w) - N * (γ ^ 2 / 2 * w') = N * γ ^ 2 / 2 * (w - w') := by ring
  rw [s4, abs_mul, abs_of_pos (by positivity : 0 < N * γ ^ 2 / 2)] at s3
  have hp2 : 0 < N * γ ^ 2 := by positivity
  nlinarith
end YangMills.Construction.FamilyNorms
end
