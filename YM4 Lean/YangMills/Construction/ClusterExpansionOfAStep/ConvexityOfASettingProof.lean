import YangMills.Construction.ClusterExpansionOfAStep.ExpansionsOfCutsAndMixes
import YangMills.Construction.ClusterExpansionOfAStep.ExpansionsOfTheDensitiesOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.ExpansionsOfTheLogarithmsOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.MeanOfTheGainProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology RealInnerProductSpace
open Filter
namespace YangMills.Construction.ClusterExpansionOfAStep
open StepSettings RenormalizationStepParameters TorusLumps TorusFields LineCalculus StepFloors
section Bilinear
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem abs_apply_single_single_le (B : (ι → ImCoords) →L[ℝ] (ι → ImCoords) →L[ℝ] ℝ) (i j : ι) {m : ℝ}
    (h : ∀ X Y : ImCoords, ‖X‖ = 1 → ‖Y‖ = 1 → |B (Pi.single i X) (Pi.single j Y)| ≤ m) (a c : ImCoords) :
    |B (Pi.single i a) (Pi.single j c)| ≤ m * (‖a‖ * ‖c‖) := by
  by_cases ha : a = 0
  · subst ha
    simp
  by_cases hc : c = 0
  · subst hc
    simp
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have hnc : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
  have hX : ‖(‖a‖⁻¹ • a : ImCoords)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hna]
  have hY : ‖(‖c‖⁻¹ • c : ImCoords)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnc]
  have ea : (Pi.single i a : ι → ImCoords) = ‖a‖ • (Pi.single i (‖a‖⁻¹ • a) : ι → ImCoords) := by
    rw [← Pi.single_smul, smul_smul, mul_inv_cancel₀ hna, one_smul]
  have ec : (Pi.single j c : ι → ImCoords) = ‖c‖ • (Pi.single j (‖c‖⁻¹ • c) : ι → ImCoords) := by
    rw [← Pi.single_smul, smul_smul, mul_inv_cancel₀ hnc, one_smul]
  have h0 := h _ _ hX hY
  have hp : 0 ≤ ‖a‖ * ‖c‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc |B (Pi.single i a) (Pi.single j c)|
      = (‖a‖ * ‖c‖) * |B (Pi.single i (‖a‖⁻¹ • a)) (Pi.single j (‖c‖⁻¹ • c))| := by
        rw [ea, ec]
        simp only [map_smul, smul_apply, smul_eq_mul, abs_mul, abs_norm]
        ring
    _ ≤ (‖a‖ * ‖c‖) * m := mul_le_mul_of_nonneg_left h0 hp
    _ = m * (‖a‖ * ‖c‖) := by ring
theorem abs_apply_self_le_of_row_sums (B : (ι → ImCoords) →L[ℝ] (ι → ImCoords) →L[ℝ] ℝ)
    (hs : ∀ v w, B v w = B w v) (M : ι → ι → ℝ)
    (hM0 : ∀ i j, 0 ≤ M i j)
    (hM : ∀ i j (X Y : ImCoords), ‖X‖ = 1 → ‖Y‖ = 1 → |B (Pi.single i X) (Pi.single j Y)| ≤ M i j) {K : ℝ}
    (hr : ∀ i, ∑ j, M i j ≤ K) (v : ι → ImCoords) : |B v v| ≤ K * ∑ i, ‖v i‖ ^ 2 := by
  have e : B v v = ∑ i, ∑ j, B (Pi.single i (v i)) (Pi.single j (v j)) := by
    have hv : v = ∑ i, (Pi.single i (v i) : ι → ImCoords) := (Finset.univ_sum_single v).symm
    calc B v v = B (∑ i, (Pi.single i (v i) : ι → ImCoords)) (∑ j, (Pi.single j (v j) : ι → ImCoords)) := by
          rw [← hv]
      _ = _ := by
        simp only [map_sum, ContinuousLinearMap.coe_sum', Finset.sum_apply]
        exact Finset.sum_comm
  have ht : ∀ i j, 2 * |B (Pi.single i (v i)) (Pi.single j (v j))| ≤
      M i j * ‖v i‖ ^ 2 + M j i * ‖v j‖ ^ 2 := by
    intro i j
    have h1 := abs_apply_single_single_le B i j (hM i j) (v i) (v j)
    have h2 := abs_apply_single_single_le B j i (hM j i) (v j) (v i)
    rw [hs] at h2
    rcases le_total (M i j) (M j i) with h | h
    · nlinarith [mul_nonneg (hM0 i j) (sq_nonneg (‖v i‖ - ‖v j‖)),
        mul_le_mul_of_nonneg_right h (sq_nonneg ‖v j‖)]
    · nlinarith [mul_nonneg (hM0 j i) (sq_nonneg (‖v i‖ - ‖v j‖)),
        mul_le_mul_of_nonneg_right h (sq_nonneg ‖v i‖)]
  have h1 : ∑ i, ∑ j, 2 * |B (Pi.single i (v i)) (Pi.single j (v j))| ≤
      ∑ i, ∑ j, (M i j * ‖v i‖ ^ 2 + M j i * ‖v j‖ ^ 2) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ht i j
  have h2 : ∑ i, ∑ j, (M i j * ‖v i‖ ^ 2 + M j i * ‖v j‖ ^ 2) =
      ∑ i, ∑ j, M i j * ‖v i‖ ^ 2 + ∑ i, ∑ j, M j i * ‖v j‖ ^ 2 := by
    simp only [Finset.sum_add_distrib]
  have h3 : ∑ i, ∑ j, M j i * ‖v j‖ ^ 2 = ∑ i, ∑ j, M i j * ‖v i‖ ^ 2 := Finset.sum_comm
  have h4 : ∑ i, ∑ j, 2 * |B (Pi.single i (v i)) (Pi.single j (v j))| =
      2 * ∑ i, ∑ j, |B (Pi.single i (v i)) (Pi.single j (v j))| := by
    simp only [Finset.mul_sum]
  have h5 : ∑ i, ∑ j, M i j * ‖v i‖ ^ 2 ≤ K * ∑ i, ‖v i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hr i) (by positivity)
  have h6 : |∑ i, ∑ j, B (Pi.single i (v i)) (Pi.single j (v j))| ≤
      ∑ i, ∑ j, |B (Pi.single i (v i)) (Pi.single j (v j))| :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
  rw [e]
  linarith
end Bilinear
theorem abs_mul_add_neg_mul_add_neg_le {x ν A B D mA mB mD : ℝ} (hx : 0 ≤ x) (h0 : 0 ≤ ν) (hA : |A| ≤ mA)
    (hB : |B| ≤ mB) (hD : |D| ≤ mD) : |x * A + -ν * B + -1 * D| ≤ x * mA + ν * mB + mD := by
  have a1 := mul_le_mul_of_nonneg_left (abs_le.1 hA).2 hx
  have a2 := mul_le_mul_of_nonneg_left (abs_le.1 hA).1 hx
  have b1 := mul_le_mul_of_nonneg_left (abs_le.1 hB).2 h0
  have b2 := mul_le_mul_of_nonneg_left (abs_le.1 hB).1 h0
  have d1 := (abs_le.1 hD).2
  have d2 := (abs_le.1 hD).1
  rw [abs_le]
  constructor <;> nlinarith
section Setting
variable {R : StepSetup} {n : ℕ} [NeZero n] {s : ChartSetting R n} {g g₁ g₂ : FreeCoords s.free → ℝ}
  {K K₁ K₂ lam C : ℝ}
theorem inBalls_zero (hρ : 0 ≤ R.ballRadius) : s.InBalls 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GainMean.inBalls_zero <;> assumption
theorem norm_single_zero_one : ‖(EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : ImCoords)‖ = 1 := by
  simp
theorem one_le_exp_bondBlockDist (hrt : 0 ≤ R.params.rt) (b b' : s.free) :
    1 ≤ Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) :=
  Real.one_le_exp (mul_nonneg (mul_nonneg (by norm_num) hrt) (Nat.cast_nonneg _))
theorem potentialPiece_majorant (h : s.IsPotentialPiece g K) (hρ : 0 ≤ R.ballRadius) (hrt : 0 ≤ R.params.rt) :
    ∃ M : s.free → s.free → ℝ, (∀ b b', 0 ≤ M b b') ∧
      (∀ η, s.InBalls η → ∀ b b' (X X' : ImCoords), ‖X‖ = 1 → ‖X'‖ = 1 →
        |fderiv ℝ (fderiv ℝ g) η (Pi.single b X) (Pi.single b' X')| ≤ M b b') ∧
      (∀ b b', M b b' ≤ K) ∧ (∀ b, ∑ b', M b b' ≤ K) ∧
      ∀ b, ∑ b', M b b' * (Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) ≤ K := by
  obtain ⟨M, hM, hr⟩ := h.standingConstraints
  have hM0 : ∀ b b', 0 ≤ M b b' := fun b b' =>
    (abs_nonneg _).trans (hM 0 (inBalls_zero hρ) b b' _ _ norm_single_zero_one norm_single_zero_one)
  have hW := one_le_exp_bondBlockDist (s := s) hrt
  have hle : ∀ b b', M b b' ≤ M b b' * Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) :=
    fun b b' => le_mul_of_one_le_right (hM0 b b') (hW b b')
  refine ⟨M, hM0, fun η hη b b' X X' hX hX' => ?_, fun b b' => ?_, fun b => ?_, fun b => ?_⟩
  · rw [← mixedSecondDeriv_eq_fderiv_fderiv ((h.smooth η hη).of_le (by norm_num))]
    exact hM η hη b b' X X' hX hX'
  · refine (hle b b').trans (le_trans ?_ (hr b))
    exact Finset.single_le_sum (f := fun b' => M b b' *
      Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1))
      (fun b'' _ => mul_nonneg (hM0 b b'') (Real.exp_pos _).le) (Finset.mem_univ b')
  · exact (Finset.sum_le_sum fun b' _ => hle b b').trans (hr b)
  · refine (Finset.sum_le_sum fun b' _ => ?_).trans (hr b)
    exact mul_le_mul_of_nonneg_left (by linarith) (hM0 b b')
theorem potentialPiece_abs_fderiv_single_le (h : s.IsPotentialPiece g K) {η : FreeCoords s.free}
    (hη : s.InBalls η) (b : s.free) {X : ImCoords} (hX : ‖X‖ = 1) : |fderiv ℝ g η (Pi.single b X)| ≤ K := by
  rw [← deriv_update_eq_fderiv ((h.smooth η hη).differentiableAt (by norm_num))]
  exact h.first η hη b X hX
theorem isOpen_setOf_contDiffAt_three (g : FreeCoords s.free → ℝ) : IsOpen {η | ContDiffAt ℝ 3 g η} :=
  isOpen_iff_mem_nhds.2 fun _ h => ContDiffAt.eventually h (by simp)
theorem potentialPiece_abs_fderiv_fderiv_le (h : s.IsPotentialPiece g K) (hρ : 0 ≤ R.ballRadius)
    (hrt : 0 ≤ R.params.rt) {η : FreeCoords s.free} (hη : s.InBalls η) (v : FreeCoords s.free) :
    |fderiv ℝ (fderiv ℝ g) η v v| ≤ K * ∑ b, ‖v b‖ ^ 2 := by
  obtain ⟨M, hM0, hM, -, hr, -⟩ := potentialPiece_majorant h hρ hrt
  refine abs_apply_self_le_of_row_sums _ (fun v w => ?_) M hM0 (hM η hη) hr v
  exact ((h.smooth η hη).isSymmSndFDerivAt (by simp; norm_num)).eq v w
theorem hasHessianDecay_cost_sub_pieces (hS : s.HasCostDecay lam C) (h1 : s.IsPotentialPiece g₁ K₁)
    (h2 : s.IsPotentialPiece g₂ K₂) (hx : 0 ≤ R.coupling) (hlam : 0 ≤ lam) (hρ : 0 ≤ R.ballRadius)
    (hrt : 0 ≤ R.params.rt) (hK : K₁ + K₂ ≤ R.coupling * lam / 16)
    (hK1 : 0 ≤ K₁) (hK2 : 0 ≤ K₂) {ν C' : ℝ} (h0 : 0 ≤ ν) (hν : ν ≤ 1) (hC' : C + lam ≤ C') :
    s.HasHessianDecay (fun η => R.coupling * s.costSum η + -ν * g₁ η + -1 * g₂ η) lam C' := by
  obtain ⟨U, hU, hb, hc⟩ := hS.contDiffOn
  have hcS : ∀ {η}, s.InBalls η → ContDiffAt ℝ 3 s.costSum η := fun hη => hc.contDiffAt (hU.mem_nhds (hb _ hη))
  have two : ∀ {f : FreeCoords s.free → ℝ} {η}, ContDiffAt ℝ 3 f η → ContDiffAt ℝ 2 f η := fun h =>
    h.of_le (by norm_num)
  have one : ∀ {f : FreeCoords s.free → ℝ} {η}, ContDiffAt ℝ 3 f η → DifferentiableAt ℝ f η := fun h =>
    h.differentiableAt (by norm_num)
  have hH : ∀ η, s.InBalls η →
      fderiv ℝ (fderiv ℝ fun η => R.coupling * s.costSum η + -ν * g₁ η + -1 * g₂ η) η =
        R.coupling • fderiv ℝ (fderiv ℝ s.costSum) η + (-ν) • fderiv ℝ (fderiv ℝ g₁) η +
          (-1 : ℝ) • fderiv ℝ (fderiv ℝ g₂) η := by
    intro η hη
    have a0 := two (hcS hη)
    have a1 := two (h1.smooth η hη)
    have a2 := two (h2.smooth η hη)
    rw [fderiv_fderiv_add ((contDiffAt_const.mul a0).add (contDiffAt_const.mul a1)) (contDiffAt_const.mul a2),
      fderiv_fderiv_add (contDiffAt_const.mul a0) (contDiffAt_const.mul a1), fderiv_fderiv_const_mul _ a0,
      fderiv_fderiv_const_mul _ a1, fderiv_fderiv_const_mul _ a2]
  have hF : ∀ η, s.InBalls η →
      fderiv ℝ (fun η => R.coupling * s.costSum η + -ν * g₁ η + -1 * g₂ η) η =
        R.coupling • fderiv ℝ s.costSum η + (-ν) • fderiv ℝ g₁ η + (-1 : ℝ) • fderiv ℝ g₂ η := by
    intro η hη
    have a0 := one (hcS hη)
    have a1 := one (h1.smooth η hη)
    have a2 := one (h2.smooth η hη)
    have h5 : HasFDerivAt (fun η => R.coupling * s.costSum η + -ν * g₁ η + -1 * g₂ η)
        (R.coupling • fderiv ℝ s.costSum η + (-ν) • fderiv ℝ g₁ η + (-1 : ℝ) • fderiv ℝ g₂ η) η :=
      ((a0.hasFDerivAt.const_mul R.coupling).add (a1.hasFDerivAt.const_mul (-ν))).add
        (a2.hasFDerivAt.const_mul (-1))
    exact h5.fderiv
  obtain ⟨MS, hMS, hMSC, hMSr⟩ := hS.decay
  obtain ⟨M₁, -, hM₁, hM₁K, -, hM₁r⟩ := potentialPiece_majorant h1 hρ hrt
  obtain ⟨M₂, -, hM₂, hM₂K, -, hM₂r⟩ := potentialPiece_majorant h2 hρ hrt
  have hMS' : ∀ η, s.InBalls η → ∀ b b' (X X' : ImCoords), ‖X‖ = 1 → ‖X'‖ = 1 →
      |fderiv ℝ (fderiv ℝ s.costSum) η (Pi.single b X) (Pi.single b' X')| ≤ MS b b' := by
    intro η hη b b' X X' hX hX'
    rw [← mixedSecondDeriv_eq_fderiv_fderiv (two (hcS hη))]
    exact hMS η hη b b' X X' hX hX'
  have hxl : 0 ≤ R.coupling * lam := mul_nonneg hx hlam
  have hCx : (C + lam) * R.coupling ≤ C' * R.coupling := mul_le_mul_of_nonneg_right hC' hx
  refine ⟨?_, fun η hη v => ?_, ⟨fun b b' => R.coupling * MS b b' + ν * M₁ b b' + M₂ b b',
    fun η hη b b' X X' hX hX' => ?_, fun b => ?_⟩, fun η hη b X hX => ?_, fun η hη b b' X X' hX hX' => ?_⟩
  · refine ⟨U ∩ ({η | ContDiffAt ℝ 3 g₁ η} ∩ {η | ContDiffAt ℝ 3 g₂ η}),
      hU.inter ((isOpen_setOf_contDiffAt_three g₁).inter (isOpen_setOf_contDiffAt_three g₂)),
      fun η hη => ⟨hb η hη, h1.smooth η hη, h2.smooth η hη⟩, fun η hη => ?_⟩
    have c0 : ContDiffAt ℝ 3 s.costSum η := hc.contDiffAt (hU.mem_nhds hη.1)
    exact (((contDiffAt_const.mul c0).add (contDiffAt_const.mul hη.2.1)).add
      (contDiffAt_const.mul hη.2.2)).contDiffWithinAt
  · rw [hH η hη]
    simp only [add_apply, smul_apply, smul_eq_mul]
    have f0 := hS.hessian_ge η hη v
    rw [second_deriv_along_line (two (hcS hη))] at f0
    have s1 := (abs_le.1 (potentialPiece_abs_fderiv_fderiv_le h1 hρ hrt hη v)).2
    have s2 := (abs_le.1 (potentialPiece_abs_fderiv_fderiv_le h2 hρ hrt hη v)).2
    have hQ : 0 ≤ ∑ b, ‖v b‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have q0 := mul_le_mul_of_nonneg_left f0 hx
    have q1 : ν * fderiv ℝ (fderiv ℝ g₁) η v v ≤ K₁ * ∑ b, ‖v b‖ ^ 2 := by
      calc ν * fderiv ℝ (fderiv ℝ g₁) η v v ≤ ν * (K₁ * ∑ b, ‖v b‖ ^ 2) := mul_le_mul_of_nonneg_left s1 h0
        _ ≤ 1 * (K₁ * ∑ b, ‖v b‖ ^ 2) := mul_le_mul_of_nonneg_right hν (mul_nonneg hK1 hQ)
        _ = K₁ * ∑ b, ‖v b‖ ^ 2 := one_mul _
    have q3 := mul_le_mul_of_nonneg_right hK hQ
    have q4 := mul_nonneg hxl hQ
    nlinarith
  · rw [hH η hη]
    simp only [add_apply, smul_apply, smul_eq_mul]
    exact abs_mul_add_neg_mul_add_neg_le hx h0 (hMS' η hη b b' X X' hX hX') (hM₁ η hη b b' X X' hX hX')
      (hM₂ η hη b b' X X' hX hX')
  · have e : ∑ b', (R.coupling * MS b b' + ν * M₁ b b' + M₂ b b') *
          (Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) =
        R.coupling * ∑ b', MS b b' * (Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) +
          ν * ∑ b', M₁ b b' * (Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) +
          ∑ b', M₂ b b' * (Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b' _ => by ring
    rw [e]
    have r0 := mul_le_mul_of_nonneg_left (hMSr b) hx
    have r1 : ν * ∑ b', M₁ b b' * (Real.exp (2 * R.params.rt * bondBlockDist (R := R) (n := n) b.1 b'.1) - 1)
        ≤ K₁ := by
      calc _ ≤ ν * K₁ := mul_le_mul_of_nonneg_left (hM₁r b) h0
        _ ≤ 1 * K₁ := mul_le_mul_of_nonneg_right hν hK1
        _ = K₁ := one_mul _
    have r2 := hM₂r b
    nlinarith
  · rw [hF η hη]
    simp only [add_apply, smul_apply, smul_eq_mul]
    have f0 := hS.firstDeriv_le η hη b X hX
    rw [deriv_update_eq_fderiv (one (hcS hη))] at f0
    have f3 := abs_mul_add_neg_mul_add_neg_le hx h0 f0 (potentialPiece_abs_fderiv_single_le h1 hη b hX)
      (potentialPiece_abs_fderiv_single_le h2 hη b hX)
    have f4 : ν * K₁ ≤ K₁ := by nlinarith
    nlinarith
  · rw [hH η hη]
    simp only [add_apply, smul_apply, smul_eq_mul]
    have f3 := abs_mul_add_neg_mul_add_neg_le hx h0 ((hMS' η hη b b' X X' hX hX').trans (hMSC b b'))
      ((hM₁ η hη b b' X X' hX hX').trans (hM₁K b b')) ((hM₂ η hη b b' X X' hX hX').trans (hM₂K b b'))
    have f4 : ν * K₁ ≤ K₁ := by nlinarith
    nlinarith
end Setting
theorem settingsUniformlyConvex_of_floors (hCost : CostHessianFloor)
    (hDens : totalDensityPieceBound) (hLogs : LogJacobianIsPotentialPiece)
    (hFl : EventuallyFloorConditions) : SettingsUniformlyConvex := by
  obtain ⟨rt₀, hrt₀, hc⟩ := hCost
  refine ⟨rt₀, hrt₀, fun T hT hrt => ?_⟩
  obtain ⟨C₁, y₁, hC₁, h1⟩ := hc T hT hrt
  obtain ⟨C₂, c₂, X₂, hC₂, hc₂, h2⟩ := hDens T hT
  obtain ⟨C₃, y₃, hC₃, h3⟩ := hLogs T hT
  obtain ⟨y₄, h4⟩ := hFl T hT (C₂ + C₃) c₂ (by positivity) hc₂
  have hlam : 0 < T.lam := hT.chain.2.2.1
  have hσ : 0 < T.threshold := hT.σ_pos
  have hTρ : 0 < T.ballRadius := by
    unfold ParameterAssignment.ballRadius
    positivity
  refine ⟨C₁ + T.lam * (1 + T.ballRadius) + T.lam, max (max (max y₁ y₃) (max y₄ X₂)) 1, by positivity, ?_⟩
  intro y hy R hR n _ hn s hs
  have hyy₁ : y₁ ≤ y := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hy
  have hyy₃ : y₃ ≤ y := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hy
  have hyy₄ : y₄ ≤ y := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hy
  have hyX : X₂ ≤ y := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hy
  have hy1 : (1 : ℝ) ≤ y := le_trans (le_max_right _ _) hy
  have hyx : y ≤ R.coupling := hR.le_coupling
  have hx1 : 1 ≤ R.coupling := hy1.trans hyx
  have hx : 0 ≤ R.coupling := by linarith
  have hρe : R.ballRadius = T.ballRadius := by
    show R.params.threshold / 64 = T.threshold / 64
    rw [hR.params_eq]
    rfl
  have hρ : 0 ≤ R.ballRadius := by
    rw [hρe]
    exact hTρ.le
  have hrt' : 0 ≤ R.params.rt := by
    rw [hR.params_eq]
    exact hT.rt_pos.le
  have S := h1 y hyy₁ R hR n hn s hs
  have D := h2 y hyX R hR n hn s hs
  have J := h3 y hyy₃ R hR n hn s hs
  have hfl := (h4 R.coupling (hyy₄.trans hyx)).drift_le
  have hE : 0 ≤ T.E₃ := by
    have hB := hT.B_ge
    have hη := hT.η₃_pos
    unfold ParameterAssignment.E₃ ParameterAssignment.E
    positivity
  have hp : R.coupling ^ C₂ ≤ R.coupling ^ (C₂ + C₃) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have he : Real.exp (-c₂ * (R.range : ℝ)) = Real.exp (-(c₂ * clusterRange R.coupling)) := by
    rw [neg_mul]
    rfl
  have hK1 : 0 ≤ C₂ * (1 + T.E₃) + R.coupling ^ C₂ * Real.exp (-c₂ * (R.range : ℝ)) := by
    have : 0 ≤ R.coupling ^ C₂ := Real.rpow_nonneg hx _
    positivity
  have hK : C₂ * (1 + T.E₃) + R.coupling ^ C₂ * Real.exp (-c₂ * (R.range : ℝ)) + C₃ ≤ R.coupling * T.lam / 16 := by
    rw [he]
    have q1 := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-(c₂ * clusterRange R.coupling))).le
    have q2 := mul_nonneg hC₃.le hE
    nlinarith
  have hCf : T.lam * (1 + R.ballRadius) ≤ C₁ + T.lam * (1 + T.ballRadius) + T.lam := by
    rw [hρe]
    linarith
  have part : ∀ ν : ℝ, 0 ≤ ν → ν ≤ 1 →
      s.HasFullDecay (s.partPotential ν) T.lam (C₁ + T.lam * (1 + T.ballRadius) + T.lam) := by
    intro ν h0 hν
    have e : s.partPotential ν = fun η => R.coupling * s.costSum η + -ν * s.totalDensity η +
        -1 * ∑ Y : TorusSite n, s.logJacobian (s.field η) η Y := by
      funext η
      simp only [ChartSetting.partPotential, ChartSetting.costSum, ChartSetting.totalDensity,
        Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    rw [e]
    refine hasFullDecay_iff_hasHessianDecay.2
      (hasHessianDecay_cost_sub_pieces S D J hx hlam.le hρ hrt' hK hK1 hC₃.le h0 hν ?_)
    nlinarith [mul_nonneg hlam.le hTρ.le]
  have pot : s.HasFullDecay s.potential T.lam (C₁ + T.lam * (1 + T.ballRadius) + T.lam) := by
    have e : s.potential = s.partPotential 1 := by
      funext η
      simp [ChartSetting.potential, ChartSetting.partPotential]
    rw [e]
    exact part 1 zero_le_one le_rfl
  have gauss := hasFullDecay_gaussian (s := s) hx hlam.le hρ hCf
  refine ⟨pot, part, fun v X h0 hv => pot.restrict hx hlam.le hρ hCf h0 hv X, fun τ h0 hτ => ?_,
    fun τ X h0 hτ => ?_⟩
  · exact (part 0 le_rfl zero_le_one).convexComb gauss h0 hτ
  · exact hasFullDecay_iff_hasHessianDecay.2
      (((hasFullDecay_iff_hasHessianDecay.1 (part 0 le_rfl zero_le_one)).restrict_add_gaussian hx hlam.le hρ hCf
        X).convexComb (hasFullDecay_iff_hasHessianDecay.1 gauss) h0 hτ)
end YangMills.Construction.ClusterExpansionOfAStep
end
