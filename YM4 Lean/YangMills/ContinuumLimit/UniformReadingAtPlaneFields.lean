import Mathlib
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.ClusterExpansionOfAStep.OneCouplingAtGivenParameters
import YangMills.Construction.ClusterExpansionOfAStep.OneCouplingAtGivenParametersProof
set_option autoImplicit false

noncomputable section

open scoped Quaternion

namespace YangMills.ContinuumLimit

open YangMills.Construction
open BlockAverages hiding unitStep gaugeTransform IsCold
open TorusFields TorusLumps AbelianSecondOrder PlaneFields CouplingUniqueness

set_option maxHeartbeats 1000000 in
theorem centered_sub_symmetric_le_uniform {ℓ : StepParameters} {d : ℕ} {C : ℝ} (hfit : ℓ.Admissible)
    (hd0 : 0 < d) (hC0 : 0 ≤ C)
    (ω : Fin 4 → Fin 4 → ℝ) (hω : ∀ i j, ω i j = - ω j i) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ h : LocalDensity, IsCurvatureFamilyOnMultiples ℓ d C h →
      ∀ γ : ℝ, 0 < γ → γ < γ₀ → ∀ (n : ℕ) [NeZero n], d ∣ n →
      4 * Real.log (1 / γ) ^ 2 + 4 < n → ∀ (X : imaginaryQuaternions) (V : TorusField n), ‖X‖ = 1 →
        IsAbelianWithCurvature X ω γ V →
        ∀ Y : TorusSite n, |centered h n Y V - γ ^ 2 / 2 *
          ∑' cc : OffsetBond × OffsetBond, symmetricAngle ω cc.1 * symmetricAngle ω cc.2 *
            secondDerivLimitOnMultiples d h cc.1 cc.2 X X| ≤ ε * γ ^ 2 := by
  have hrate := weightRate_pos hfit
  set K := arrayNorm ω with hKd
  have hK0 : 0 ≤ K := arrayNorm_nonneg ω
  have hK := abs_symmetricAngle_le ω
  obtain ⟨L₀, hL₀⟩ := exists_large_log ℓ.weightRate C (thirdOrderConstant ℓ C K) (boxCloseConstant ℓ C K) K
    ℓ.threshold (ℓ.n₀ : ℝ) ε hrate hfit.σ_pos hε
  refine ⟨Real.exp (-L₀), Real.exp_pos _, fun h hF γ hγ hγ₀ n _ hd hside X V hX hV Y => ?_⟩
  set L := Real.log (1 / γ) with hLd
  have hγL : Real.exp (-L) = γ := by
    rw [hLd, Real.log_div one_ne_zero hγ.ne', Real.log_one, zero_sub, neg_neg, Real.exp_log hγ]
  have hLL : L₀ ≤ L := by
    have : -L₀ ≥ -L := by
      have := Real.log_lt_log hγ hγ₀
      rw [Real.log_exp] at this
      have e : L = - Real.log γ := by
        rw [hLd, Real.log_div one_ne_zero hγ.ne', Real.log_one, zero_sub]
      linarith
    linarith
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩ := hL₀ L hLL
  rw [hγL] at l2 l3 l4 l5 l6
  set r : ℕ := ⌈L ^ 2⌉₊ with hr
  have r1 : L ^ 2 ≤ r := Nat.le_ceil _
  have r2 : (r : ℝ) < L ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hnR : (4 * L ^ 2 + 4 : ℝ) < n := hside
  have hrn : 2 * r + 2 < n := by
    have : ((2 * r + 2 : ℕ) : ℝ) < n := by
      push_cast
      linarith [sq_nonneg L]
    exact_mod_cast this
  have hn : ℓ.n₀ ≤ n := by
    have : (ℓ.n₀ : ℝ) < n := lt_of_le_of_lt l7 hnR
    exact_mod_cast this.le
  have hcV : IsCold ℓ.threshold V := by
    intro x μ ν hμ
    refine lt_of_le_of_lt (curvature_le_of_abelian hX hV x hμ) (lt_of_le_of_lt ?_ l2)
    rw [abs_mul, abs_of_pos hγ]
    exact mul_le_mul_of_nonneg_left (abs_le_arrayNorm ω μ ν) hγ.le
  have hcold : 4 * (γ * (K * (1 + (r : ℝ)))) < ℓ.threshold := by
    refine lt_of_le_of_lt ?_ l3
    have h1 : K * (1 + (r : ℝ)) ≤ K * (2 + L ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hK0
    have h2 := mul_le_mul_of_nonneg_left h1 hγ.le
    linarith
  have e1 := centered_sub_boxSecondSum hfit hd0 hF hn hd X hX ω hγ V hV hcV Y (symmetricAngle ω)
    (symmetricAngle_closed ω hω) hK0 hK hrn hcold
  have e2 := boxSecondSum_sub_tsum_le hfit hd0 hF hn hd hrn X hX hK0 hK
  set Q := ∑' cc : OffsetBond × OffsetBond, symmetricAngle ω cc.1 * symmetricAngle ω cc.2 *
    secondDerivLimitOnMultiples d h cc.1 cc.2 X X with hQ
  set S := boxSecondSum h n r (symmetricAngle ω) X with hS
  have l1' : 3 * L ≤ ℓ.weightRate * L ^ 2 := by
    have h2 : 3 ≤ L * ℓ.weightRate := (div_le_iff₀ hrate).1 l1
    calc 3 * L ≤ (L * ℓ.weightRate) * L := mul_le_mul_of_nonneg_right h2 l0
      _ = ℓ.weightRate * L ^ 2 := by ring
  have l1'' : ℓ.weightRate * L ^ 2 ≤ ℓ.weightRate * r := mul_le_mul_of_nonneg_left r1 hrate.le
  have x1 : Real.exp (-ℓ.weightRate * r) ≤ γ ^ 3 := by
    have : γ ^ 3 = Real.exp (-(3 * L)) := by
      rw [← hγL, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [this]
    apply Real.exp_le_exp.2
    linarith
  have x2 : Real.exp (-(ℓ.weightRate / 2) * r) ≤ γ := by
    rw [← hγL]
    apply Real.exp_le_exp.2
    linarith
  have hγ2 : 0 < γ ^ 2 := by positivity
  have y1 : C * Real.exp (-ℓ.weightRate * r) ≤ ε / 3 * γ ^ 2 := by
    have h2 := mul_le_mul_of_nonneg_left x1 hC0
    have h3 : C * γ ^ 3 = (C * γ) * γ ^ 2 := by ring
    rw [h3] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right l4.le hγ2.le)
  have y2 : thirdOrderConstant ℓ C K * γ ^ 3 / 2 ≤ ε / 3 * γ ^ 2 := by
    have h3 : thirdOrderConstant ℓ C K * γ ^ 3 / 2 = (thirdOrderConstant ℓ C K * γ / 2) * γ ^ 2 := by ring
    rw [h3]
    exact mul_le_mul_of_nonneg_right l5.le hγ2.le
  have hcc0 : 0 ≤ boxCloseConstant ℓ C K := by
    unfold boxCloseConstant
    have : 0 ≤ ∑' cc, pairDecayWeight ℓ cc := tsum_nonneg pairDecayWeight_nonneg
    positivity
  have y3 : γ ^ 2 / 2 * |S - Q| ≤ ε / 3 * γ ^ 2 := by
    have h4 : |S - Q| ≤ boxCloseConstant ℓ C K * γ :=
      e2.trans (mul_le_mul_of_nonneg_left x2 hcc0)
    have h5 : γ ^ 2 / 2 * |S - Q| ≤ γ ^ 2 / 2 * (boxCloseConstant ℓ C K * γ) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h6 : γ ^ 2 / 2 * (boxCloseConstant ℓ C K * γ) = (boxCloseConstant ℓ C K * γ / 2) * γ ^ 2 := by ring
    rw [h6] at h5
    exact h5.trans (mul_le_mul_of_nonneg_right l6.le hγ2.le)
  have tri : |centered h n Y V - γ ^ 2 / 2 * Q| ≤
      |centered h n Y V - γ ^ 2 / 2 * S| + γ ^ 2 / 2 * |S - Q| := by
    have e0 : centered h n Y V - γ ^ 2 / 2 * Q =
        (centered h n Y V - γ ^ 2 / 2 * S) + γ ^ 2 / 2 * (S - Q) := by ring
    rw [e0]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ γ ^ 2 / 2)]
  linarith

theorem centered_small_at_planeField_uniform {ℓ : StepParameters} (hfit : ℓ.Admissible) {C : ℝ}
    (hC0 : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ g : LocalDensity, IsCurvatureFamily ℓ C g → CouplingUniqueness.HasNoLimitFormTerm g →
      ∀ (n : ℕ) [NeZero n], N ≤ n → ∀ U : TorusField n,
        IsAbelianWithCurvature quaternionI (PlaneFields.planeForm 0 1)
          (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2) U →
        ∀ Y : TorusSite n, |centered g n Y U| ≤ ε * (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2) ^ 2 := by
  have hanti := planeForm_antisymm 0 1 (by decide)
  have hA : ∀ i j, curvatureAlong quaternionI (planeForm 0 1) i j =
      - curvatureAlong quaternionI (planeForm 0 1) j i := by
    intro i j
    simp only [curvatureAlong]
    rw [hanti i j]
    exact neg_smul (planeForm 0 1 j i) quaternionI
  obtain ⟨γ₀, h0, hγ⟩ := centered_sub_symmetric_le_uniform hfit one_pos hC0 (planeForm 0 1) hanti hε
  obtain ⟨N, hN⟩ := exists_side_large 1 one_pos h0
  refine ⟨N, fun g hg hz n _ hn U hU Y => ?_⟩
  have hF1 : IsCurvatureFamilyOnMultiples ℓ 1 C g :=
    { smooth := fun n _ hn _ => hg.smooth n hn
      gauge := fun n _ hn _ => hg.gauge n hn
      translation := fun n _ hn _ => hg.translation n hn
      decay := fun n _ hn _ => hg.decay n hn
      local_density := fun n n' _ _ hn hn' _ _ => hg.local_density n n' hn hn' }
  have e0 : ∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
      (fun m : ℕ => flatSecondDeriv g (1 * m) c c' X X') =
        fun n : ℕ => mixedDeriv (g n 0) (trivialField n) ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] := by
    intro c c' X X'
    funext m
    rw [one_mul]
    rfl
  have e : ∀ (c c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
      secondDerivLimitOnMultiples 1 g c c' X X' = secondDerivLimit g c c' X X' := by
    intro c c' X X'
    unfold secondDerivLimitOnMultiples
    rw [e0]
    rfl
  have hzero : ∑' cc : OffsetBond × OffsetBond, secondDerivLimitOnMultiples 1 g cc.1 cc.2
      (linearPotential (curvatureAlong quaternionI (planeForm 0 1)) cc.1)
      (linearPotential (curvatureAlong quaternionI (planeForm 0 1)) cc.2) = 0 := by
    simp only [e]
    exact (hz _ _ hA hA).tsum_eq
  obtain ⟨a, b, c⟩ := hN n hn
  have key := hγ g hF1 _ a b n (one_dvd n) c quaternionI U norm_quaternionI hU Y
  rw [← tsum_linear_eq_symmetric hfit one_pos hF1 (planeForm 0 1) hanti quaternionI
    (linearPotential (curvatureAlong quaternionI (planeForm 0 1)))
    (isLinearPotential_linearPotential _ hA), hzero, mul_zero, sub_zero] at key
  exact key

end YangMills.ContinuumLimit

end
