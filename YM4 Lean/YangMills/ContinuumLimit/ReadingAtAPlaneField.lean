import Mathlib
import YangMills.Construction.ClusterExpansionOfAStep.OneCouplingAtGivenParametersProof
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderAtAbelianFieldsProof
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.ClusterExpansionOfAStep.ActionAtAFieldOfOnePlane
import YangMills.Construction.ResponseInTheExpansion.ExpansionOfTheResponse
set_option autoImplicit false

noncomputable section

namespace YangMills.ContinuumLimit

open YangMills.Construction
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
open YangMills.Construction.TorusLumps YangMills.Construction.PlaneFields
open YangMills.Construction.CouplingUniqueness YangMills.Construction.RenormalizationStepParameters

theorem exists_plane_field (hA : PlaneFields.LeastActionAtPlaneField)
    {T : ParameterAssignment} (hT : T.Admissible) (y : ℝ) :
    ∃ N₀ : ℕ, max 64 (T.stepParameters y).n₀ ≤ N₀ ∧ ∀ (t n : ℕ) [NeZero n], N₀ ≤ n →
      ∃ U : TorusField n,
        IsAbelianWithCurvature quaternionI (planeForm 0 1)
          (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2) U ∧
        IsCold (T.stepParameters y).threshold U ∧
        Real.pi ^ 2 ≤ actionAtLevel (T.stepParameters y).coupling (T.stepParameters y).side (t + 1)
          Finset.univ U := by
  obtain ⟨γ₀, hγ₀, hU⟩ := hA T hT
  obtain ⟨δ, hδ, hexp⟩ := expUnit_near_one hT.σ_pos
  obtain ⟨n₃, h₃⟩ := exists_nat_gt (2 * Real.pi / min γ₀ δ)
  refine ⟨max (max 64 (T.stepParameters y).n₀) n₃, le_max_left _ _, fun t n _ hn => ?_⟩
  have hn₃ : n₃ ≤ n := le_trans (le_max_right _ _) hn
  have hn64 : 64 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnR : (64 : ℝ) ≤ n := by exact_mod_cast hn64
  have hn0 : (0 : ℝ) < n := by linarith
  set γ : ℝ := 2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 with hγ
  have hmin : 0 < min γ₀ δ := lt_min hγ₀ hδ
  have hγpos : 0 < γ := by
    rw [hγ]
    have := Real.pi_pos
    positivity
  have hγlt : γ < min γ₀ δ := by
    have h3 : 2 * Real.pi / min γ₀ δ < n := lt_of_lt_of_le h₃ (by exact_mod_cast hn₃)
    have h4 : 2 * Real.pi < n * min γ₀ δ := by
      rwa [div_lt_iff₀ hmin] at h3
    rw [hγ, div_lt_iff₀ (by positivity)]
    have h5 : (1 : ℝ) ≤ n := by linarith
    have h6 : (n : ℝ) * min γ₀ δ ≤ min γ₀ δ * (n : ℝ) ^ 2 := by
      have h7 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left h7 hmin.le
      linarith
    simp only [Nat.cast_one, mul_one]
    linarith
  obtain ⟨U, hab, hact⟩ := hU t n 1 quaternionI 0 1 hn64 norm_quaternionI (by decide)
    (le_trans hγlt.le (min_le_left _ _))
  have hcold : IsCold (T.stepParameters y).threshold U := by
    intro x μ ν hμν
    unfold TorusFields.curvature
    rw [hab.2 x μ ν hμν]
    apply hexp
    rw [abs_mul, abs_of_pos hγpos]
    calc γ * |planeForm 0 1 μ ν| ≤ γ * 1 :=
          mul_le_mul_of_nonneg_left (abs_planeForm_le_one _ _ _ _) hγpos.le
      _ = γ := mul_one _
      _ < δ := lt_of_lt_of_le hγlt (min_le_right _ _)
  refine ⟨U, hab, hcold, ?_⟩
  have hside : (2 : ℕ) ^ 40 ≤ T.side := hT.L_ge
  have hside1 : 1 ≤ T.side := le_trans (Nat.one_le_two_pow) hside
  have hL1 : (1 : ℝ) ≤ (T.side : ℝ) ^ (t + 1) := by
    have h1 : (1 : ℝ) ≤ T.side := by exact_mod_cast hside1
    exact one_le_pow₀ h1
  set M : ℝ := (n : ℝ) * (T.side : ℝ) ^ (t + 1) with hM
  have hM64 : 64 ≤ M := by
    rw [hM]
    nlinarith
  set θ : ℝ := 2 * Real.pi * ((1 : ℕ) : ℝ) / M ^ 2 with hθ
  have hθ1 : |θ| ≤ 1 := by
    have hpi := Real.pi_pos
    have hpi4 := Real.pi_le_four
    rw [abs_of_nonneg (by rw [hθ]; positivity), hθ, div_le_one (by positivity)]
    simp only [Nat.cast_one, mul_one]
    nlinarith
  have hcos := sq_div_four_le_one_sub_cos hθ1
  have e₃ : M ^ 4 * (θ ^ 2 / 4) = Real.pi ^ 2 := by
    rw [hθ]
    have : M ≠ 0 := by linarith
    field_simp
    push_cast
    ring
  have hM4 : 0 ≤ M ^ 4 := by positivity
  have e₅ : actionAtLevel (T.stepParameters y).coupling (T.stepParameters y).side (t + 1)
      Finset.univ U = M ^ 4 * (1 - Real.cos θ) := hact
  rw [e₅]
  calc Real.pi ^ 2 = M ^ 4 * (θ ^ 2 / 4) := e₃.symm
    _ ≤ M ^ 4 * (1 - Real.cos θ) := mul_le_mul_of_nonneg_left hcos hM4

theorem abs_sum_centered_le {g : LocalDensity} {n : ℕ} [NeZero n] {U : TorusField n} {ε : ℝ}
    (hb : ∀ Y : TorusSite n, |centered g n Y U| ≤ ε * (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2) ^ 2) :
    |∑ y, centered g n y U| ≤ 4 * Real.pi ^ 2 * ε := by
  set γ : ℝ := 2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 with hγ
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hvol : (n : ℝ) ^ 4 * γ ^ 2 = 4 * Real.pi ^ 2 := by
    rw [hγ]
    field_simp
    push_cast
    ring
  calc |∑ y, centered g n y U| ≤ ∑ y, |centered g n y U| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y : TorusSite n, ε * γ ^ 2 := Finset.sum_le_sum fun y _ => hb y
    _ = (n : ℝ) ^ 4 * (ε * γ ^ 2) := by
        rw [Finset.sum_const, card_torusSite, nsmul_eq_mul]
        push_cast
        ring
    _ = ε * ((n : ℝ) ^ 4 * γ ^ 2) := by ring
    _ = 4 * Real.pi ^ 2 * ε := by
        rw [hvol]
        ring

theorem abs_sum_centered_div_le {g : LocalDensity} {n : ℕ} [NeZero n] {U : TorusField n} {ε A : ℝ}
    (hb : ∀ Y : TorusSite n, |centered g n Y U| ≤ ε * (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2) ^ 2)
    (hA : Real.pi ^ 2 ≤ A) :
    |∑ y, centered g n y U| / A ≤ 4 * ε := by
  have hpi : 0 < Real.pi ^ 2 := by
    have := Real.pi_pos
    positivity
  have hApos : 0 < A := lt_of_lt_of_le hpi hA
  have hγpos : 0 < (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2) ^ 2 := by
    have := Real.pi_pos
    have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    positivity
  have hε : 0 ≤ ε := by
    have h0 := le_trans (abs_nonneg _) (hb 0)
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) hγpos
    linarith
  have hs := abs_sum_centered_le hb
  rw [div_le_iff₀ hApos]
  nlinarith

private theorem weight_pos (ℓ : StepParameters) (m : ℕ) : 0 < ℓ.weight m := by
  unfold StepParameters.weight
  exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)

private theorem secondOrderAtAbelianFields : SecondOrderAtAbelianFields :=
  SecondOrderAtAbelianFields.of_secondOrderOnMultiplesOfSide AbelianSecondOrder.secondOrderOnMultiplesOfSide

theorem curvature_family_of_cold_bounds {ℓ : StepParameters} {E E₃ C : ℝ} {f : LocalDensity}
    (hE : E ≤ E₃) (hC : E₃ ≤ C) (h : WeightedResponses.ColdDensityBounds ℓ E E₃ f) :
    IsCurvatureFamily ℓ C f := by
  refine ⟨h.smooth, h.gauge, h.translation, fun n _ hn y W hW k c X hk1 hk3 hX => ?_,
    fun n n' _ _ hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu => ?_⟩
  · refine (h.decay n hn y W hW k c X hk1 hk3 hX).trans ?_
    apply div_le_div_of_nonneg_right _ (weight_pos ℓ _).le
    split_ifs
    · exact hC
    · exact hE.trans hC
  · refine (h.local_density n n' hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu).trans ?_
    exact div_le_div_of_nonneg_right (hE.trans hC) (weight_pos ℓ _).le

theorem noLimitFormTerm_of_cold_bounds {ℓ : StepParameters} (hℓ : ℓ.Admissible) {E E₃ : ℝ}
    {f : LocalDensity} (hE : E ≤ E₃) (h : WeightedResponses.ColdDensityBounds ℓ E E₃ f) :
    HasNoLimitFormTerm f := by
  intro A A' hA hA'
  have hs := (secondOrderAtAbelianFields ℓ hℓ E₃ f
    (curvature_family_of_cold_bounds hE le_rfl h)).2.2.2.2.1 A A' hA hA'
  have h1 := hs.hasSum
  rw [h.no_curvature_term A A' hA hA'] at h1
  exact h1

theorem curvature_family_of_coldExpansion {ℓ : StepParameters} {t : ℕ} {x C : ℝ} {D : TorusFunctional}
    {f : LocalDensity} (hE : ℓ.E ≤ ℓ.E₃) (hC : ℓ.E₃ ≤ C) (h : ColdExpansion ℓ t x D f) :
    IsCurvatureFamily ℓ C f := by
  refine ⟨h.smooth, h.gauge, h.translation, fun n _ hn y W hW k c X hk1 hk3 hX => ?_,
    fun n n' _ _ hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu => ?_⟩
  · refine (h.decay n hn y W hW k c X hk1 hk3 hX).trans ?_
    apply div_le_div_of_nonneg_right _ (weight_pos ℓ _).le
    split_ifs
    · exact hC
    · exact hE.trans hC
  · refine (h.local_density n n' hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu).trans ?_
    exact div_le_div_of_nonneg_right (hE.trans hC) (weight_pos ℓ _).le

theorem noLimitFormTerm_of_coldExpansion {ℓ : StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional}
    {f : LocalDensity} (h : ColdExpansion ℓ t x D f) : HasNoLimitFormTerm f :=
  fun A A' hA hA' => h.no_curvature_term A A' hA hA'

end YangMills.ContinuumLimit

end
