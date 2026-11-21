import YangMills.Construction.RunningCouplingSlope.CoefficientsAdd
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
open Filter
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps
namespace SlopeCoefficient
variable {n : ℕ}
theorem isGaugeTotalAt_add {H H' : GaugeTotal} (h : IsGaugeTotalAt H n) (h' : IsGaugeTotalAt H' n) :
    IsGaugeTotalAt (addGaugeTotal H H') n where
  contDiffAt_perturb := fun k c X => (h.contDiffAt_perturb k c X).add (h'.contDiffAt_perturb k c X)
  gauge_invariant_near := by
    filter_upwards [h.gauge_invariant_near, h'.gauge_invariant_near] with p hp hp'
    simp only [addGaugeTotal, hp, hp']
  constant_gauge_invariant := fun g => by
    filter_upwards [h.constant_gauge_invariant g, h'.constant_gauge_invariant g] with V hV hV'
    simp only [addGaugeTotal, hV, hV']
  isometry_invariant := fun g => by
    filter_upwards [h.isometry_invariant g, h'.isometry_invariant g] with V hV hV' V' hc
    simp only [addGaugeTotal, hV V' hc, hV' V' hc]
theorem isGaugeTotalAt_of_add {H H' : GaugeTotal} (hs : IsGaugeTotalAt (addGaugeTotal H H') n)
    (h : IsGaugeTotalAt H n) : IsGaugeTotalAt H' n where
  contDiffAt_perturb := fun k c X => by
    have hd := (hs.contDiffAt_perturb k c X).sub (h.contDiffAt_perturb k c X)
    refine hd.congr_of_eventuallyEq (Eventually.of_forall fun σ => ?_)
    simp [addGaugeTotal]
  gauge_invariant_near := by
    filter_upwards [hs.gauge_invariant_near, h.gauge_invariant_near] with p hp hq
    simp only [addGaugeTotal] at hp
    linarith
  constant_gauge_invariant := fun g => by
    filter_upwards [hs.constant_gauge_invariant g, h.constant_gauge_invariant g] with V hV hW
    simp only [addGaugeTotal] at hV
    linarith
  isometry_invariant := fun g => by
    filter_upwards [hs.isometry_invariant g, h.isometry_invariant g] with V hV hW V' hc
    have hV₁ := hV V' hc
    have hW₁ := hW V' hc
    simp only [addGaugeTotal] at hV₁
    linarith
theorem hessianAtTrivial_add {H H' : GaugeTotal} (h : IsGaugeTotalAt H n) (h' : IsGaugeTotalAt H' n)
    (c c' : TorusBond n) (X X' : imaginaryQuaternions) :
    hessianAtTrivial (addGaugeTotal H H') n c c' X X' =
      hessianAtTrivial H n c c' X X' + hessianAtTrivial H' n c c' X X' := by
  unfold hessianAtTrivial mixedDeriv
  have e := iteratedFDeriv_add_apply (h.contDiffAt_perturb 2 ![c, c'] ![X, X'])
    (h'.contDiffAt_perturb 2 ![c, c'] ![X, X'])
  have e2 : (fun σ : Fin 2 → ℝ => addGaugeTotal H H' n (perturb ![c, c'] ![X, X'] σ (trivialField n))) =
      (fun σ => H n (perturb ![c, c'] ![X, X'] σ (trivialField n))) +
        fun σ => H' n (perturb ![c, c'] ![X, X'] σ (trivialField n)) := rfl
  rw [e2, e]
  rfl
theorem isGaugeTotalAt_zero : IsGaugeTotalAt zeroGaugeTotal n where
  contDiffAt_perturb := fun k c X => contDiffAt_const
  gauge_invariant_near := Eventually.of_forall fun _ => rfl
  constant_gauge_invariant := fun _ => Eventually.of_forall fun _ => rfl
  isometry_invariant := fun _ => Eventually.of_forall fun _ _ _ => rfl
theorem hessianAtTrivial_zero (c c' : TorusBond n) (X X' : imaginaryQuaternions) :
    hessianAtTrivial zeroGaugeTotal n c c' X X' = 0 := by
  unfold hessianAtTrivial mixedDeriv
  have hz : (fun σ : Fin 2 → ℝ => zeroGaugeTotal n (perturb ![c, c'] ![X, X'] σ (trivialField n))) =
      fun _ => 0 := rfl
  rw [hz, iteratedFDeriv_const_of_ne (by norm_num)]
  rfl
theorem slopeCoefficientAdditive : SlopeCoefficientAdditive := by
  refine ⟨?_, ?_, fun H H' n hs h => isGaugeTotalAt_of_add hs h⟩
  · rintro H H' b b' ⟨K, hK, hS⟩ ⟨K', hK', hS'⟩
    refine ⟨fun c c' => K c c' + K' c c', ?_, ?_⟩
    · obtain ⟨M, θ, hθ, hd⟩ := hK.exp_decay
      obtain ⟨M', θ', hθ', hd'⟩ := hK'.exp_decay
      refine ⟨?_, ⟨|M| + |M'|, min θ θ', lt_min hθ hθ', ?_⟩, fun c c' X X' => ?_⟩
      · filter_upwards [hK.eventually_isGaugeTotalAt, hK'.eventually_isGaugeTotalAt] with n ha hb
        exact isGaugeTotalAt_add ha hb
      · filter_upwards [hK.eventually_isGaugeTotalAt, hK'.eventually_isGaugeTotalAt, hd, hd'] with
          n ha hb he he' c c' X X' hX hX'
        rw [hessianAtTrivial_add ha hb]
        have t : (0 : ℝ) ≤ supDist c.1 c'.1 := Nat.cast_nonneg _
        have b1 : Real.exp (-(θ * supDist c.1 c'.1)) ≤ Real.exp (-(min θ θ' * supDist c.1 c'.1)) :=
          Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) t))
        have b2 : Real.exp (-(θ' * supDist c.1 c'.1)) ≤ Real.exp (-(min θ θ' * supDist c.1 c'.1)) :=
          Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) t))
        have c1 := (he c c' X X' hX hX').trans
          (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le)
        have c2 := (he' c c' X X' hX hX').trans
          (mul_le_mul_of_nonneg_right (le_abs_self M') (Real.exp_pos _).le)
        have d1 := mul_le_mul_of_nonneg_left b1 (abs_nonneg M)
        have d2 := mul_le_mul_of_nonneg_left b2 (abs_nonneg M')
        have habs := abs_add_le (hessianAtTrivial H n c c' X X') (hessianAtTrivial H' n c c' X X')
        rw [add_mul]
        linarith
      · have hl := (hK.tendsto_kernel c c' X X').add (hK'.tendsto_kernel c c' X X')
        rw [← mul_add] at hl
        refine hl.congr' ?_
        filter_upwards [hK.eventually_isGaugeTotalAt, hK'.eventually_isGaugeTotalAt] with n ha hb
        exact (hessianAtTrivial_add ha hb _ _ _ _).symm
    · have hsum := hS.add hS'
      have e : secondMomentTerm (fun c c' => K c c' + K' c c') =
          fun z => secondMomentTerm K z + secondMomentTerm K' z := by
        funext z
        simp only [secondMomentTerm]
        ring
      rw [e]
      exact hsum
  · refine ⟨fun _ _ => 0, ⟨Eventually.of_forall fun _ => isGaugeTotalAt_zero, ⟨0, 1, one_pos, ?_⟩,
      fun c c' X X' => ?_⟩, ?_⟩
    · refine Eventually.of_forall fun n c c' X X' _ _ => ?_
      rw [hessianAtTrivial_zero]
      simp
    · simp only [hessianAtTrivial_zero, mul_zero]
      exact tendsto_const_nhds
    · have hz : secondMomentTerm (fun _ _ => 0) = fun _ => 0 := by
        funext z
        simp [secondMomentTerm]
      rw [hz]
      exact hasSum_zero
end SlopeCoefficient
end YangMills.Construction
end
