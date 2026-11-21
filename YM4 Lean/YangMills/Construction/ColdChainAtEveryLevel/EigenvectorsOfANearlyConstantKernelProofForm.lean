import YangMills.Construction.ColdChainAtEveryLevel.EigenvectorsOfANearlyConstantKernel
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace NearlyConstantKernel
section
variable {ι : Type} {s : Finset ι} {u : ι → ℝ} {e : ι → ι → ι → ℍ[ℝ]} {η : ℝ}
theorem coe_real_mul_comm (r : ℝ) (q : ℍ[ℝ]) : (r : ℍ[ℝ]) * q = q * (r : ℍ[ℝ]) :=
  Quaternion.coe_commutes r q
theorem coe_sqrt_mul_coe_sqrt {r : ℝ} (h : 0 ≤ r) : (Real.sqrt r : ℍ[ℝ]) * (Real.sqrt r : ℍ[ℝ]) = (r : ℍ[ℝ]) := by
  rw [← Quaternion.coe_mul, Real.mul_self_sqrt h]
theorem norm_coe_real_sqrt (r : ℝ) : ‖(Real.sqrt r : ℍ[ℝ])‖ = Real.sqrt r := by
  rw [Quaternion.norm_coe, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
theorem sum_coe_real (t : Finset ι) (f : ι → ℝ) : ∑ i ∈ t, (f i : ℍ[ℝ]) = ((∑ i ∈ t, f i : ℝ) : ℍ[ℝ]) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, Quaternion.coe_add]
theorem norm_perturbationApply_le_mul (hu : ∀ i ∈ s, 0 ≤ u i) (hs : ∑ i ∈ s, u i = 1) (i : ι)
    (he : ∀ i' ∈ s, ∀ i'' ∈ s, ‖e i i' i''‖ ≤ η) (hη : 0 ≤ η) {g : ι → ℍ[ℝ]} {d : ℝ}
    (hg : ∀ j ∈ s, ‖g j‖ ≤ d) : ‖perturbationApply s u e g i‖ ≤ η * d := by
  unfold perturbationApply
  have hd : ∀ a ∈ s, ∀ b ∈ s, ‖(u a : ℍ[ℝ]) * ((u b : ℍ[ℝ]) * (e i a b * g b))‖ ≤ u a * (u b * (η * d)) := by
    intro a ha b hb
    rw [norm_mul, norm_mul, norm_mul, Quaternion.norm_coe, Quaternion.norm_coe, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (hu a ha), abs_of_nonneg (hu b hb)]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (hu b hb)) (hu a ha)
    exact mul_le_mul (he a ha b hb) (hg b hb) (norm_nonneg _) hη
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ a ∈ s, ‖∑ b ∈ s, (u a : ℍ[ℝ]) * ((u b : ℍ[ℝ]) * (e i a b * g b))‖ ≤ u a * (η * d) := by
    intro a ha
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (hd a ha)).trans (le_of_eq ?_))
    rw [← Finset.mul_sum, ← Finset.sum_mul, hs, one_mul]
  refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, hs, one_mul]
theorem perturbationApply_mul_right (g : ι → ℍ[ℝ]) (c : ℍ[ℝ]) (i : ι) :
    perturbationApply s u e (fun j => g j * c) i = perturbationApply s u e g i * c := by
  simp only [perturbationApply, Finset.sum_mul, mul_assoc]
theorem symmetrizedApplyCore_sqrt_mul (hu : ∀ i ∈ s, 0 ≤ u i) (hs : ∑ i ∈ s, u i = 1) (H : ι → ℍ[ℝ]) (i : ι) :
    symmetrizedApplyCore s u e (fun j => (Real.sqrt (u j) : ℍ[ℝ]) * H j) i =
      ∑ j ∈ s, (u j : ℍ[ℝ]) * H j + perturbationApply s u e H i := by
  have e1 : ∀ a ∈ s, ∀ b ∈ s, (u a : ℍ[ℝ]) * ((Real.sqrt (u b) : ℍ[ℝ]) * ((1 + e i a b) *
      ((Real.sqrt (u b) : ℍ[ℝ]) * H b))) =
      (u a : ℍ[ℝ]) * ((u b : ℍ[ℝ]) * H b) + (u a : ℍ[ℝ]) * ((u b : ℍ[ℝ]) * (e i a b * H b)) := by
    intro a _ b hb
    rw [← mul_add]
    congr 1
    have h1 : (1 + e i a b) * ((Real.sqrt (u b) : ℍ[ℝ]) * H b) =
        (Real.sqrt (u b) : ℍ[ℝ]) * ((1 + e i a b) * H b) := by
      rw [← mul_assoc, ← coe_real_mul_comm, mul_assoc]
    rw [h1, ← mul_assoc, coe_sqrt_mul_coe_sqrt (hu b hb), ← mul_add, add_mul, one_mul]
  unfold symmetrizedApplyCore perturbationApply
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => e1 a ha b hb]
  simp only [Finset.sum_add_distrib]
  congr 1
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_coe_real, hs]
  simp
end
theorem unitEigenvectorsNearOne_holds : UnitEigenvectorsNearOne := by
  intro ι s u e η hu hs hη0 hη he
  have hweighted : ∀ {g : ι → ℍ[ℝ]} {d : ℝ}, (∀ j ∈ s, ‖g j‖ ≤ d) →
      ‖∑ j ∈ s, (u j : ℍ[ℝ]) * g j‖ ≤ d := by
    intro g d hg
    refine (norm_sum_le _ _).trans ?_
    have : ∀ j ∈ s, ‖(u j : ℍ[ℝ]) * g j‖ ≤ u j * d := by
      intro j hj
      rw [norm_mul, Quaternion.norm_coe, Real.norm_eq_abs, abs_of_nonneg (hu j hj)]
      exact mul_le_mul_of_nonneg_left (hg j hj) (hu j hj)
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    rw [← Finset.sum_mul, hs, one_mul]
  refine ⟨fun v l hl hv heq => ?_, fun h hb hm hh hherm => ?_⟩
  · have l0 : 0 < l := by linarith
    have l1 : ((l⁻¹ : ℝ) : ℍ[ℝ]) * (l : ℍ[ℝ]) = 1 := by
      rw [← Quaternion.coe_mul, inv_mul_cancel₀ l0.ne']
      simp
    set H : ι → ℍ[ℝ] := fun i => ((l⁻¹ : ℝ) : ℍ[ℝ]) * symmetrizedApplyCore s u e v i with hH
    have hvH : ∀ i ∈ s, v i = (Real.sqrt (u i) : ℍ[ℝ]) * H i := by
      intro i hi
      calc v i = ((l⁻¹ : ℝ) : ℍ[ℝ]) * ((l : ℍ[ℝ]) * v i) := by rw [← mul_assoc, l1, one_mul]
        _ = ((l⁻¹ : ℝ) : ℍ[ℝ]) * ((Real.sqrt (u i) : ℍ[ℝ]) * symmetrizedApplyCore s u e v i) := by rw [heq i hi]
        _ = _ := by
          rw [hH]
          simp only []
          rw [← mul_assoc, ← mul_assoc, coe_real_mul_comm (l⁻¹)]
    set c : ℍ[ℝ] := ∑ j ∈ s, (u j : ℍ[ℝ]) * H j with hc
    have hfull : ∀ i, symmetrizedApplyCore s u e v i = c + perturbationApply s u e H i := by
      intro i
      rw [← symmetrizedApplyCore_sqrt_mul hu hs H i]
      unfold symmetrizedApplyCore
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
      rw [hvH b hb]
    have hlH : ∀ i, (l : ℍ[ℝ]) * H i = c + perturbationApply s u e H i := by
      intro i
      rw [← hfull i, hH]
      simp only []
      rw [← mul_assoc, coe_real_mul_comm l, l1, one_mul]
    have hnv : ∀ i ∈ s, ‖v i‖ = Real.sqrt (u i) * ‖H i‖ := by
      intro i hi
      rw [hvH i hi, norm_mul, norm_coe_real_sqrt]
    have hsq : ∀ i ∈ s, Real.sqrt (u i) ^ 2 = u i := fun i hi => Real.sq_sqrt (hu i hi)
    have hact : ∀ i ∈ s, ‖perturbationApply s u e H i‖ ≤ η := by
      intro i hi
      unfold perturbationApply
      have hterm : ∀ a ∈ s, ∀ b ∈ s, ‖(u a : ℍ[ℝ]) * ((u b : ℍ[ℝ]) * (e i a b * H b))‖ ≤
          u a * (η * ((u b + ‖v b‖ ^ 2) / 2)) := by
        intro a ha b hb
        rw [norm_mul, norm_mul, norm_mul, Quaternion.norm_coe, Quaternion.norm_coe, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (hu a ha), abs_of_nonneg (hu b hb)]
        refine mul_le_mul_of_nonneg_left ?_ (hu a ha)
        have h1 : u b * (‖e i a b‖ * ‖H b‖) = ‖e i a b‖ * (Real.sqrt (u b) * ‖v b‖) := by
          rw [hnv b hb]
          have h0 : Real.sqrt (u b) * Real.sqrt (u b) = u b := Real.mul_self_sqrt (hu b hb)
          calc u b * (‖e i a b‖ * ‖H b‖) = (Real.sqrt (u b) * Real.sqrt (u b)) * (‖e i a b‖ * ‖H b‖) := by
                rw [h0]
            _ = _ := by ring
        rw [h1]
        refine mul_le_mul (he i hi a ha b hb) ?_ (by positivity) hη0
        have := hsq b hb
        nlinarith [sq_nonneg (Real.sqrt (u b) - ‖v b‖)]
      refine (norm_sum_le _ _).trans ?_
      have h2 : ∀ a ∈ s, ‖∑ b ∈ s, (u a : ℍ[ℝ]) * ((u b : ℍ[ℝ]) * (e i a b * H b))‖ ≤ u a * η := by
        intro a ha
        refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (hterm a ha)).trans (le_of_eq ?_))
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib, hs, hv]
        ring
      refine (Finset.sum_le_sum h2).trans (le_of_eq ?_)
      rw [← Finset.sum_mul, hs, one_mul]
    have hHb : ∀ i ∈ s, l * ‖H i‖ ≤ ‖c‖ + η := by
      intro i hi
      have h1 : ‖(l : ℍ[ℝ]) * H i‖ = l * ‖H i‖ := by
        rw [norm_mul, Quaternion.norm_coe, Real.norm_eq_abs, abs_of_pos l0]
      rw [← h1, hlH i]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (hact i hi))
    have hc1 : l ≤ ‖c‖ + η := by
      by_contra hcon
      have hlt : ‖c‖ + η < l := not_le.1 hcon
      have hb : ∀ i ∈ s, ‖v i‖ ^ 2 ≤ u i * ((‖c‖ + η) / l) ^ 2 := by
        intro i hi
        rw [hnv i hi, mul_pow, hsq i hi]
        refine mul_le_mul_of_nonneg_left ?_ (hu i hi)
        have h2 : ‖H i‖ ≤ (‖c‖ + η) / l := by
          rw [le_div_iff₀ l0]
          linarith [hHb i hi]
        exact pow_le_pow_left₀ (norm_nonneg _) h2 2
      have h3 := Finset.sum_le_sum hb
      rw [hv, ← Finset.sum_mul, hs, one_mul] at h3
      have h4 : (‖c‖ + η) / l < 1 := by
        rw [div_lt_one l0]
        exact hlt
      have h5 : 0 ≤ (‖c‖ + η) / l := by positivity
      nlinarith
    have hcn : 1 / 4 ≤ ‖c‖ := by linarith
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hcn
      norm_num at hcn
    have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc0
    have hact' : ∀ i ∈ s, ‖perturbationApply s u e (fun j => H j * c⁻¹) i‖ ≤ 4 * η := by
      intro i hi
      rw [perturbationApply_mul_right, norm_mul, norm_inv]
      have h1 := hact i hi
      have h2 : ‖c‖⁻¹ ≤ 4 := by
        rw [inv_le_comm₀ hcpos (by norm_num)]
        linarith
      calc _ ≤ η * 4 := mul_le_mul h1 h2 (by positivity) hη0
        _ = _ := by ring
    have hmean : ∑ i ∈ s, (u i : ℍ[ℝ]) * (H i * c⁻¹) = 1 := by
      simp only [← mul_assoc]
      rw [← Finset.sum_mul, ← hc, mul_inv_cancel₀ hc0]
    have heq' : ∀ i ∈ s, 1 + perturbationApply s u e (fun j => H j * c⁻¹) i = H i * c⁻¹ * (l : ℍ[ℝ]) := by
      intro i _
      rw [perturbationApply_mul_right]
      have h1 : 1 + perturbationApply s u e H i * c⁻¹ = (c + perturbationApply s u e H i) * c⁻¹ := by
        rw [add_mul, mul_inv_cancel₀ hc0]
      rw [h1, ← hlH i]
      calc (l : ℍ[ℝ]) * H i * c⁻¹ = H i * (l : ℍ[ℝ]) * c⁻¹ := by rw [coe_real_mul_comm l (H i)]
        _ = H i * ((l : ℍ[ℝ]) * c⁻¹) := mul_assoc _ _ _
        _ = H i * (c⁻¹ * (l : ℍ[ℝ])) := by rw [coe_real_mul_comm l c⁻¹]
        _ = _ := (mul_assoc _ _ _).symm
    have hl1 : ‖(l : ℍ[ℝ]) - 1‖ ≤ 4 * η := by
      have h1 : (l : ℍ[ℝ]) - 1 = ∑ i ∈ s, (u i : ℍ[ℝ]) * perturbationApply s u e (fun j => H j * c⁻¹) i := by
        have h2 : ∑ i ∈ s, (u i : ℍ[ℝ]) * (1 + perturbationApply s u e (fun j => H j * c⁻¹) i) = (l : ℍ[ℝ]) := by
          rw [Finset.sum_congr rfl fun i hi => by rw [heq' i hi]]
          simp only [← mul_assoc]
          rw [← Finset.sum_mul]
          simp only [mul_assoc]
          rw [hmean, one_mul]
        simp only [mul_add, mul_one, Finset.sum_add_distrib] at h2
        rw [sum_coe_real, hs] at h2
        rw [← h2]
        simp
      rw [h1]
      exact hweighted hact'
    refine ⟨fun j => H j * c⁻¹, c, hc0, fun i hi => ?_, hmean, heq', fun i hi => ?_⟩
    · have e1 : (l : ℍ[ℝ]) * (H i * c⁻¹ - 1) = perturbationApply s u e (fun j => H j * c⁻¹) i - ((l : ℍ[ℝ]) - 1) := by
        have := heq' i hi
        rw [coe_real_mul_comm] at *
        simp only [sub_mul, mul_sub, one_mul, mul_one]
        rw [← this]
        abel
      have e2 : ‖(l : ℍ[ℝ]) * (H i * c⁻¹ - 1)‖ = l * ‖H i * c⁻¹ - 1‖ := by
        rw [norm_mul, Quaternion.norm_coe, Real.norm_eq_abs, abs_of_pos l0]
      have e3 : l * ‖H i * c⁻¹ - 1‖ ≤ 8 * η := by
        rw [← e2, e1]
        refine (norm_sub_le _ _).trans ?_
        have := hact' i hi
        linarith
      have e4 : (1 / 2) * ‖H i * c⁻¹ - 1‖ ≤ l * ‖H i * c⁻¹ - 1‖ :=
        mul_le_mul_of_nonneg_right hl (norm_nonneg _)
      linarith
    · rw [hvH i hi, mul_assoc (H i), inv_mul_cancel₀ hc0, mul_one]
  · have hbn : ∀ i ∈ s, 1 / 2 ≤ ‖h i‖ ∧ ‖h i‖ ≤ 2 := by
      intro i hi
      have h1 := hb i hi
      have h2 := norm_sub_norm_le (1 : ℍ[ℝ]) (h i)
      have h3 := norm_sub_le (h i) (1 : ℍ[ℝ])
      have h4 : ‖h i‖ ≤ ‖h i - 1‖ + ‖(1 : ℍ[ℝ])‖ := by simpa using norm_add_le (h i - 1) 1
      rw [norm_sub_rev, norm_one] at h2
      rw [norm_one] at h4
      constructor <;> linarith
    set W : ℝ := ∑ i ∈ s, u i * ‖h i‖ ^ 2 with hW
    have hW4 : 1 / 4 ≤ W := by
      have : ∀ i ∈ s, u i * (1 / 4) ≤ u i * ‖h i‖ ^ 2 := by
        intro i hi
        refine mul_le_mul_of_nonneg_left ?_ (hu i hi)
        have := (hbn i hi).1
        nlinarith
      have h2 := Finset.sum_le_sum this
      rwa [← Finset.sum_mul, hs, one_mul] at h2
    have hWpos : 0 < W := by linarith
    set lam : ℍ[ℝ] := 1 + perturbationMean s u e h with hlam
    have hact2 : ∀ i ∈ s, ‖perturbationApply s u e h i‖ ≤ η * 2 :=
      fun i hi => norm_perturbationApply_le_mul hu hs i (he i hi) hη0 fun j hj => (hbn j hj).2
    have hmean2 : ‖perturbationMean s u e h‖ ≤ η * 2 := hweighted hact2
    set t : ι → ι → ι → ℍ[ℝ] := fun i a b =>
      ((u i * u a * u b : ℝ) : ℍ[ℝ]) * (star (h i) * ((1 + e i a b) * h b)) with ht
    have hfullh : ∀ i ∈ s, ∑ a ∈ s, ∑ b ∈ s, t i a b = (u i : ℍ[ℝ]) * (star (h i) * (h i * lam)) := by
      intro i hi
      have e1 : ∑ a ∈ s, ∑ b ∈ s, (u a : ℍ[ℝ]) * ((u b : ℍ[ℝ]) * ((1 + e i a b) * h b)) = h i * lam := by
        rw [← hh i hi]
        have := symmetrizedApplyCore_sqrt_mul (e := e) hu hs h i
        rw [hm] at this
        rw [← this]
        unfold symmetrizedApplyCore
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb' => ?_
        congr 1
        have h1 : (1 + e i a b) * ((Real.sqrt (u b) : ℍ[ℝ]) * h b) =
            (Real.sqrt (u b) : ℍ[ℝ]) * ((1 + e i a b) * h b) := by
          rw [← mul_assoc, ← coe_real_mul_comm, mul_assoc]
        rw [h1, ← mul_assoc ((Real.sqrt (u b) : ℝ) : ℍ[ℝ]) ((Real.sqrt (u b) : ℝ) : ℍ[ℝ]),
          coe_sqrt_mul_coe_sqrt (hu b hb')]
      rw [← e1]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [ht, Quaternion.coe_mul]
      have c1 := coe_real_mul_comm (u a)
      have c2 := coe_real_mul_comm (u b)
      rw [mul_assoc, mul_assoc]
      congr 1
      calc (u a : ℍ[ℝ]) * ((u b : ℍ[ℝ]) * (star (h i) * ((1 + e i a b) * h b)))
          = (u a : ℍ[ℝ]) * (star (h i) * ((u b : ℍ[ℝ]) * ((1 + e i a b) * h b))) := by
            rw [← mul_assoc (u b : ℍ[ℝ]), c2 (star (h i)), mul_assoc]
        _ = _ := by rw [← mul_assoc (u a : ℍ[ℝ]), c1 (star (h i)), mul_assoc]
    have hstar : ∀ i ∈ s, ∀ a ∈ s, ∀ b ∈ s, star (t i a b) = t b a i := by
      intro i hi a ha b hb'
      simp only [ht, star_mul, star_add, star_one, star_star, hherm i hi a ha b hb']
      rw [Quaternion.star_coe, ← coe_real_mul_comm]
      have : u i * u a * u b = u b * u a * u i := by ring
      rw [this, mul_assoc (star (h b))]
    set Q : ℍ[ℝ] := ∑ i ∈ s, ∑ a ∈ s, ∑ b ∈ s, t i a b with hQ
    have hQself : star Q = Q := by
      simp only [hQ, star_sum]
      have e1 : ∑ i ∈ s, ∑ a ∈ s, ∑ b ∈ s, star (t i a b) = ∑ i ∈ s, ∑ a ∈ s, ∑ b ∈ s, t b a i :=
        Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun a ha =>
          Finset.sum_congr rfl fun b hb' => hstar i hi a ha b hb'
      rw [e1]
      calc ∑ i ∈ s, ∑ a ∈ s, ∑ b ∈ s, t b a i = ∑ a ∈ s, ∑ i ∈ s, ∑ b ∈ s, t b a i := Finset.sum_comm
        _ = ∑ a ∈ s, ∑ b ∈ s, ∑ i ∈ s, t b a i := Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ b ∈ s, ∑ a ∈ s, ∑ i ∈ s, t b a i := Finset.sum_comm
    have hQW : Q = (W : ℍ[ℝ]) * lam := by
      have e1 : Q = ∑ i ∈ s, (u i : ℍ[ℝ]) * (star (h i) * (h i * lam)) :=
        Finset.sum_congr rfl hfullh
      rw [e1, hW, ← sum_coe_real, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc (star (h i)), Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self,
        Quaternion.coe_mul]
      have e2 : ((u i * ‖h i‖ ^ 2 : ℝ) : ℍ[ℝ]) = (u i : ℍ[ℝ]) * ((‖h i‖ : ℍ[ℝ]) * (‖h i‖ : ℍ[ℝ])) := by
        rw [sq, Quaternion.coe_mul, Quaternion.coe_mul]
      rw [e2]
      simp only [mul_assoc]
    have hW0 : (W : ℍ[ℝ]) ≠ 0 := fun h0 => hWpos.ne'
      (by simpa using congrArg (fun q : ℍ[ℝ] => q.re) h0)
    have hlamself : star lam = lam := by
      have h1 : star ((W : ℍ[ℝ]) * lam) = (W : ℍ[ℝ]) * lam := by rw [← hQW]; exact hQself
      rw [star_mul, Quaternion.star_coe, ← coe_real_mul_comm] at h1
      exact mul_left_cancel₀ hW0 h1
    have hlamcoe := YangMills.Construction.BlockAverages.eq_coe_re_of_star_eq hlamself
    set l : ℝ := lam.re with hl
    have hl1 : |l - 1| ≤ η * 2 := by
      have h1 : ((l - 1 : ℝ) : ℍ[ℝ]) = perturbationMean s u e h := by
        rw [Quaternion.coe_sub, ← hlamcoe, hlam]
        simp
      have h2 : ‖((l - 1 : ℝ) : ℍ[ℝ])‖ = |l - 1| := by
        rw [Quaternion.norm_coe, Real.norm_eq_abs]
      rw [← h2, h1]
      exact hmean2
    have hlge : 1 / 2 ≤ l := by
      have := (abs_le.1 hl1).1
      linarith
    set w : ℝ := (Real.sqrt W)⁻¹ with hw
    have hsW : 0 < Real.sqrt W := Real.sqrt_pos.2 hWpos
    have hwpos : 0 < w := inv_pos.2 hsW
    have hw2 : w ^ 2 * W = 1 := by
      rw [hw, inv_pow, Real.sq_sqrt hWpos.le]
      field_simp
    refine ⟨l, w, hlge, hwpos, ?_, fun i hi => ?_⟩
    · have e1 : ∀ i ∈ s, ‖(Real.sqrt (u i) : ℍ[ℝ]) * ((w : ℍ[ℝ]) * h i)‖ ^ 2 = w ^ 2 * (u i * ‖h i‖ ^ 2) := by
        intro i hi
        rw [norm_mul, norm_mul, norm_coe_real_sqrt, Quaternion.norm_coe, Real.norm_eq_abs, abs_of_pos hwpos,
          mul_pow, mul_pow, Real.sq_sqrt (hu i hi)]
        ring
      rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, ← hW, hw2]
    · have hsplit := symmetrizedApplyCore_sqrt_mul (e := e) hu hs (fun j => (w : ℍ[ℝ]) * h j) i
      rw [hsplit]
      have e2 : ∑ j ∈ s, (u j : ℍ[ℝ]) * ((w : ℍ[ℝ]) * h j) = (w : ℍ[ℝ]) := by
        have : ∀ j ∈ s, (u j : ℍ[ℝ]) * ((w : ℍ[ℝ]) * h j) = (w : ℍ[ℝ]) * ((u j : ℍ[ℝ]) * h j) := by
          intro j _
          rw [← mul_assoc, ← mul_assoc, coe_real_mul_comm (u j) (w : ℍ[ℝ])]
        rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hm, mul_one]
      have e3 : perturbationApply s u e (fun j => (w : ℍ[ℝ]) * h j) i = perturbationApply s u e h i * (w : ℍ[ℝ]) := by
        rw [← perturbationApply_mul_right]
        congr 1
        funext j
        exact coe_real_mul_comm w (h j)
      rw [e2, e3]
      have e4 : (w : ℍ[ℝ]) + perturbationApply s u e h i * (w : ℍ[ℝ]) = (1 + perturbationApply s u e h i) * (w : ℍ[ℝ]) := by
        rw [add_mul, one_mul]
      rw [e4, hh i hi, hlamcoe]
      calc (Real.sqrt (u i) : ℍ[ℝ]) * (h i * (l : ℍ[ℝ]) * (w : ℍ[ℝ]))
          = (Real.sqrt (u i) : ℍ[ℝ]) * ((l : ℍ[ℝ]) * ((w : ℍ[ℝ]) * h i)) := by
            congr 1
            calc h i * (l : ℍ[ℝ]) * (w : ℍ[ℝ]) = (l : ℍ[ℝ]) * h i * (w : ℍ[ℝ]) := by
                  rw [coe_real_mul_comm l (h i)]
              _ = (l : ℍ[ℝ]) * (h i * (w : ℍ[ℝ])) := mul_assoc _ _ _
              _ = _ := by rw [coe_real_mul_comm w (h i)]
        _ = _ := by
            rw [← mul_assoc, coe_real_mul_comm (Real.sqrt (u i)) (l : ℍ[ℝ]), mul_assoc]
end NearlyConstantKernel
end YangMills.Construction
end
