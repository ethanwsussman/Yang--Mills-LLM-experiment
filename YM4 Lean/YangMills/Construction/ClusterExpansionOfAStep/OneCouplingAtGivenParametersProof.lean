import YangMills.Construction.ClusterExpansionOfAStep.ActionAtAFieldOfOnePlane
import YangMills.Construction.ClusterExpansionOfAStep.OneCouplingAtGivenParameters
import YangMills.Construction.SummableBoundsOfTheFlow.OneNumberOfOneTotalProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps PlaneFields CouplingUniqueness
theorem PlaneFields.planeForm_antisymm (μ ν : Fin 4) (hμν : μ ≠ ν) (i j : Fin 4) :
    planeForm μ ν i j = - planeForm μ ν j i := by
  unfold planeForm
  by_cases h₁ : i = μ ∧ j = ν
  · obtain ⟨rfl, rfl⟩ := h₁
    simp [hμν, hμν.symm]
  · by_cases h₂ : i = ν ∧ j = μ
    · obtain ⟨rfl, rfl⟩ := h₂
      simp [hμν, hμν.symm]
    · have h₃ : ¬ (j = μ ∧ i = ν) := fun h => h₂ ⟨h.2, h.1⟩
      have h₄ : ¬ (j = ν ∧ i = μ) := fun h => h₁ ⟨h.2, h.1⟩
      simp [h₁, h₂, h₃, h₄]
theorem PlaneFields.abs_planeForm_le_one (μ ν i j : Fin 4) : |planeForm μ ν i j| ≤ 1 := by
  unfold planeForm
  split_ifs <;> simp
theorem PlaneFields.planeForm_isInt (μ ν i j : Fin 4) :
    ∃ k : ℤ, ((1 : ℕ) : ℝ) * planeForm μ ν i j = k := by
  unfold planeForm
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-1, by simp⟩
  · exact ⟨0, by simp⟩
theorem TorusLumps.norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
theorem CouplingUniqueness.centered_small_at_planeField (hS : TorusLumps.SecondOrderAtAbelianFields)
    {p : StepParameters} (hp : p.Admissible) {C : ℝ}
    {g : LocalDensity} (hc : IsCurvatureFamily p C g) (hn : HasNoLimitFormTerm g) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ) [NeZero n], N ≤ n → ∀ U : TorusField n,
      IsAbelianWithCurvature quaternionI (planeForm 0 1) (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2) U →
      ∀ Y : TorusSite n, |centered g n Y U| ≤ ε * (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2) ^ 2 := by
  have hanti := planeForm_antisymm 0 1 (by decide)
  obtain ⟨v, hv, hb⟩ := (hS p hp C g hc).2.2.2.2.2.2.2 (planeForm 0 1) 1 quaternionI hanti one_pos
    (planeForm_isInt 0 1) norm_quaternionI
  have hA : ∀ i j, curvatureAlong quaternionI (planeForm 0 1) i j =
      - curvatureAlong quaternionI (planeForm 0 1) j i := by
    intro i j
    simp only [curvatureAlong]
    rw [hanti i j]
    apply Subtype.ext
    simp
  have h0 : v = 0 := hv.unique (hn _ _ hA hA)
  subst h0
  obtain ⟨N, hN⟩ := hb ε hε
  refine ⟨N, fun n _ hle U hU Y => ?_⟩
  simpa using hN n hle U hU Y
theorem CouplingUniqueness.expUnit_near_one {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
      ‖((expUnit (s • quaternionI) : UnitQuaternion) : ℍ[ℝ]) - 1‖ < σ := by
  have hcont : Continuous fun s : ℝ => ((expUnit (s • quaternionI) : UnitQuaternion) : ℍ[ℝ]) :=
    continuous_subtype_val.comp (continuous_expUnit.comp (by fun_prop))
  have h0 : ((expUnit ((0 : ℝ) • quaternionI) : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [zero_smul, expUnit_zero]
    rfl
  have := Metric.continuous_iff.mp hcont 0 σ hσ
  obtain ⟨δ, hδ, hb⟩ := this
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have := hb s (by simpa [Real.dist_eq] using hs)
  rw [h0, dist_eq_norm] at this
  exact this
theorem CouplingUniqueness.sq_div_four_le_one_sub_cos {θ : ℝ} (h : |θ| ≤ 1) :
    θ ^ 2 / 4 ≤ 1 - Real.cos θ := by
  have hb := Real.cos_bound h
  have h1 := (abs_le.mp hb).2
  have h2 : |θ| ^ 2 ≤ 1 := by nlinarith [abs_nonneg θ]
  have h3 : |θ| ^ 4 = θ ^ 2 * |θ| ^ 2 := by
    have h5 : θ ^ 2 = |θ| ^ 2 := (sq_abs θ).symm
    rw [h5]
    ring
  have h4 : θ ^ 2 * |θ| ^ 2 ≤ θ ^ 2 := by nlinarith [sq_nonneg θ]
  rw [h3] at h1
  nlinarith [sq_nonneg θ]
theorem TorusFields.card_torusSite (n : ℕ) [NeZero n] :
    (Finset.univ : Finset (TorusSite n)).card = n ^ 4 := by
  simp [TorusSite, ZMod.card]
theorem CouplingUniqueness.coupling_eq_of_coldForm (hS : TorusLumps.SecondOrderAtAbelianFields)
    {p : StepParameters} (hp : p.Admissible) {γ₀ : ℝ}
    (hγ₀ : 0 < γ₀)
    (hU : ∀ (t n l : ℕ) [NeZero n] (X : imaginaryQuaternions) (μ ν : Fin 4), 64 ≤ n → ‖X‖ = 1 → μ < ν →
      2 * Real.pi * l / (n : ℝ) ^ 2 ≤ γ₀ →
      ∃ U : TorusField n, IsAbelianWithCurvature X (planeForm μ ν) (2 * Real.pi * l / (n : ℝ) ^ 2) U ∧
        actionAtLevel p.coupling p.side (t + 1) Finset.univ U =
          ((n : ℝ) * (p.side : ℝ) ^ (t + 1)) ^ 4 *
            (1 - Real.cos (2 * Real.pi * l / ((n : ℝ) * (p.side : ℝ) ^ (t + 1)) ^ 2)))
    {t : ℕ} {x' x'' C C' : ℝ} {D : TorusFunctional} {g' g'' : LocalDensity}
    (G' : IsCurvatureFamily p C g') (G'' : IsCurvatureFamily p C' g'') (N' : HasNoLimitFormTerm g')
    (N'' : HasNoLimitFormTerm g'') (e' : HasColdForm p (t + 1) x' D g')
    (e'' : HasColdForm p (t + 1) x'' D g'') : x' = x'' := by
  obtain ⟨δ, hδ, hexp⟩ := expUnit_near_one hp.σ_pos
  have main : ∀ ε : ℝ, 0 < ε → |x' - x''| ≤ 8 * ε := by
    intro ε hε
    obtain ⟨n₁, h₁⟩ := centered_small_at_planeField hS hp G' N' ε hε
    obtain ⟨n₂, h₂⟩ := centered_small_at_planeField hS hp G'' N'' ε hε
    obtain ⟨n₃, h₃⟩ := exists_nat_gt (2 * Real.pi / min γ₀ δ)
    set n : ℕ := max (max (max n₁ n₂) (max n₃ p.n₀)) 64 with hn
    have hn₁ : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
    have hn₂ : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
    have hn₃ : n₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
    have hn₀ : p.n₀ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
    have hn64 : 64 ≤ n := le_max_right _ _
    have : NeZero n := ⟨by omega⟩
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
    have hcold : IsCold p.threshold U := by
      intro x μ ν hμν
      unfold curvature
      rw [hab.2 x μ ν hμν]
      apply hexp
      rw [abs_mul, abs_of_pos hγpos]
      calc γ * |planeForm 0 1 μ ν| ≤ γ * 1 :=
            mul_le_mul_of_nonneg_left (abs_planeForm_le_one _ _ _ _) hγpos.le
        _ = γ := mul_one _
        _ < δ := lt_of_lt_of_le hγlt (min_le_right _ _)
    have e₁ := e' n hn₀ U hcold
    have e₂ := e'' n hn₀ U hcold
    set A := actionAtLevel p.coupling p.side (t + 1) Finset.univ U with hAdef
    have hdiff : (x' - x'') * A = ∑ y, centered g' n y U - ∑ y, centered g'' n y U := by
      linarith
    have hsum : ∀ (g : LocalDensity), (∀ Y : TorusSite n, |centered g n Y U| ≤ ε * γ ^ 2) →
        |∑ y, centered g n y U| ≤ (n : ℝ) ^ 4 * (ε * γ ^ 2) := by
      intro g hb
      calc |∑ y, centered g n y U| ≤ ∑ y, |centered g n y U| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _y : TorusSite n, ε * γ ^ 2 := Finset.sum_le_sum fun y _ => hb y
        _ = (n : ℝ) ^ 4 * (ε * γ ^ 2) := by
          rw [Finset.sum_const, card_torusSite, nsmul_eq_mul]
          push_cast
          ring
    have s₁ := hsum g' (h₁ n hn₁ U hab)
    have s₂ := hsum g'' (h₂ n hn₂ U hab)
    have hvol : (n : ℝ) ^ 4 * γ ^ 2 = 4 * Real.pi ^ 2 := by
      rw [hγ]
      field_simp
      push_cast
      ring
    have hLpos : (0 : ℝ) < (p.side : ℝ) ^ (t + 1) := by
      have : (0 : ℝ) < p.side := by
        have := hp.L_ge
        have h2 : (0 : ℕ) < p.side := by
          have : 0 < 2 ^ 16 := by norm_num
          omega
        exact_mod_cast h2
      positivity
    have hL1 : (1 : ℝ) ≤ (p.side : ℝ) ^ (t + 1) := by
      have h1 : (1 : ℝ) ≤ p.side := by
        have h2 : 1 ≤ p.side := by
          have := hp.L_ge
          have : 0 < 2 ^ 16 := by norm_num
          omega
        exact_mod_cast h2
      exact one_le_pow₀ h1
    set M : ℝ := (n : ℝ) * (p.side : ℝ) ^ (t + 1) with hM
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
    have hAge : Real.pi ^ 2 ≤ A := by
      have e₃ : M ^ 4 * (θ ^ 2 / 4) = Real.pi ^ 2 := by
        rw [hθ]
        have : M ≠ 0 := by linarith
        field_simp
        push_cast
        ring
      have hM4 : 0 ≤ M ^ 4 := by positivity
      have e₅ : A = M ^ 4 * (1 - Real.cos θ) := hact
      calc Real.pi ^ 2 = M ^ 4 * (θ ^ 2 / 4) := e₃.symm
        _ ≤ M ^ 4 * (1 - Real.cos θ) := mul_le_mul_of_nonneg_left hcos hM4
        _ = A := e₅.symm
    have hpi : 0 < Real.pi ^ 2 := by
      have := Real.pi_pos
      positivity
    have hfin : |x' - x''| * A ≤ 2 * ((n : ℝ) ^ 4 * (ε * γ ^ 2)) := by
      have hA0 : 0 ≤ A := by linarith
      have e₄ : |x' - x''| * A = |(x' - x'') * A| := by rw [abs_mul, abs_of_nonneg hA0]
      rw [e₄, hdiff]
      calc |∑ y, centered g' n y U - ∑ y, centered g'' n y U|
          ≤ |∑ y, centered g' n y U| + |∑ y, centered g'' n y U| := abs_sub _ _
        _ ≤ 2 * ((n : ℝ) ^ 4 * (ε * γ ^ 2)) := by linarith
    have hfin2 : |x' - x''| * Real.pi ^ 2 ≤ 8 * ε * Real.pi ^ 2 := by
      have h1 : |x' - x''| * Real.pi ^ 2 ≤ |x' - x''| * A :=
        mul_le_mul_of_nonneg_left hAge (abs_nonneg _)
      have h2 : 2 * ((n : ℝ) ^ 4 * (ε * γ ^ 2)) = 2 * ε * ((n : ℝ) ^ 4 * γ ^ 2) := by ring
      rw [h2, hvol] at hfin
      have h3 : 2 * ε * (4 * Real.pi ^ 2) = 8 * ε * Real.pi ^ 2 := by ring
      linarith
    exact le_of_mul_le_mul_right hfin2 hpi
  by_contra hne
  have hpos : 0 < |x' - x''| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have := main (|x' - x''| / 16) (by positivity)
  linarith
theorem CouplingUniqueness.couplingIsUnique_holds (hS : TorusLumps.SecondOrderAtAbelianFields)
    (hA : PlaneFields.LeastActionAtPlaneField) : CouplingUniqueness.CouplingIsUnique := by
  intro T hT y hy t x' x'' C C' D g' g'' G' G'' N' N'' e' e''
  obtain ⟨γ₀, hγ₀, hU⟩ := hA T hT
  exact coupling_eq_of_coldForm hS (hT.fits y hy) hγ₀ hU G' G'' N' N'' e' e''
end YangMills.Construction
end
