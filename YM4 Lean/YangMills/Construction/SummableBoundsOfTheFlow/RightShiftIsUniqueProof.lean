import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftIsUnique
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
private theorem hasDerivAt_exp_line {W : ℍ[ℝ]} (hd : DifferentiableAt ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) W) (v : ℍ[ℝ]) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (W + τ • v)) (fderiv ℝ NormedSpace.exp W v) 0 := by
  have hg : HasDerivAt (fun τ : ℝ => W + τ • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add W
  have hE : HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (fderiv ℝ NormedSpace.exp W) (W + (0 : ℝ) • v) := by
    simpa using hd.hasFDerivAt
  exact hE.comp_hasDerivAt (0 : ℝ) hg
private theorem inner_one_left (q : ℍ[ℝ]) : inner ℝ (1 : ℍ[ℝ]) q = q.re := by
  simp [Quaternion.inner_def]
private theorem inner_coe_right_of_re_eq_zero {v : ℍ[ℝ]} (hv : v.re = 0) (c : ℝ) : inner ℝ v (c : ℍ[ℝ]) = 0 := by
  simp [Quaternion.inner_def, hv]
private theorem eq_zero_of_fderiv_exp_eq_zero {W v : ℍ[ℝ]} (hW : W.re = 0) (hv : v.re = 0) (hr : ‖W‖ < Real.pi)
    (hd : DifferentiableAt ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) W)
    (h0 : fderiv ℝ NormedSpace.exp W v = 0) : v = 0 := by
  by_cases hW0 : W = 0
  · subst hW0
    have h := (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := ℍ[ℝ])).fderiv
    rw [h] at h0
    simpa using h0
  have hrp : 0 < ‖W‖ := norm_pos_iff.2 hW0
  have hline := hasDerivAt_exp_line hd v
  rw [h0] at hline
  set g : ℝ → ℍ[ℝ] := fun τ => W + τ • v with hg
  set n : ℝ → ℝ := fun τ => ‖g τ‖ with hn
  have hgre : ∀ τ, (g τ).re = 0 := fun τ => by simp [hg, hW, hv]
  have hF : ∀ τ, NormedSpace.exp (g τ) = ((Real.cos (n τ) : ℝ) : ℍ[ℝ]) + (Real.sin (n τ) / n τ) • g τ :=
    fun τ => Quaternion.exp_of_re_eq_zero _ (hgre τ)
  have hgd : HasDerivAt g v 0 := by
    show HasDerivAt (fun τ : ℝ => W + τ • v) v 0
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add W
  have hg0 : g 0 = W := by simp [hg]
  have hnd : DifferentiableAt ℝ n 0 :=
    hgd.differentiableAt.norm ℝ (by rw [hg0]; exact hW0)
  have hn0 : n 0 = ‖W‖ := by simp [hn, hg0]
  set ν := deriv n 0 with hν
  have hnD : HasDerivAt n ν 0 := hnd.hasDerivAt
  have hre : HasDerivAt (fun τ => Real.cos (n τ)) 0 0 := by
    have := ((innerSL ℝ (1 : ℍ[ℝ])).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline)
    simp only [map_zero] at this
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
    show Real.cos (n τ) = inner ℝ (1 : ℍ[ℝ]) (NormedSpace.exp (g τ))
    rw [inner_one_left, hF]
    simp [hgre]
  have hcos : HasDerivAt (fun τ => Real.cos (n τ)) (-Real.sin (n 0) * ν) 0 := hnD.cos
  have hsin0 : 0 < Real.sin ‖W‖ := Real.sin_pos_of_pos_of_lt_pi hrp hr
  have hν0 : ν = 0 := by
    have := hcos.unique hre
    rw [hn0] at this
    have hmul : Real.sin ‖W‖ * ν = 0 := by linarith
    rcases mul_eq_zero.1 hmul with h | h
    · exact absurd h hsin0.ne'
    · exact h
  have hs : DifferentiableAt ℝ (fun t : ℝ => Real.sin t / t) (n 0) := by
    rw [hn0]
    exact Real.differentiableAt_sin.div differentiableAt_id hrp.ne'
  have hsn : HasDerivAt (fun τ => Real.sin (n τ) / n τ) 0 0 := by
    have := hs.hasDerivAt.comp (0 : ℝ) hnD
    rw [hν0, mul_zero] at this
    exact this
  have hlin : HasDerivAt (fun τ => inner ℝ v (g τ)) (inner ℝ v v) 0 :=
    (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hgd
  have hprod := hsn.mul hlin
  have hv2 : HasDerivAt (fun τ => (Real.sin (n τ) / n τ) * inner ℝ v (g τ)) 0 0 := by
    have := ((innerSL ℝ v).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline)
    simp only [map_zero] at this
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
    show (Real.sin (n τ) / n τ) * inner ℝ v (g τ) = inner ℝ v (NormedSpace.exp (g τ))
    rw [hF, inner_add_right _ ((Real.cos (n τ) : ℝ) : ℍ[ℝ]), inner_coe_right_of_re_eq_zero hv, zero_add, inner_smul_right]
  have heq := hprod.unique hv2
  have hs0 : 0 < Real.sin (n 0) / n 0 := by rw [hn0]; exact div_pos hsin0 hrp
  have hvv : inner ℝ v v = 0 := by
    simp only [zero_mul, zero_add] at heq
    rcases mul_eq_zero.1 heq with h | h
    · exact absurd h hs0.ne'
    · exact h
  exact inner_self_eq_zero.1 hvv
theorem rightTranslationDerivUnique_holds : RightTranslationDerivUnique := by
  intro w X u u' hw h h'
  have hd : DifferentiableAt ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (w : ℍ[ℝ]) :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (w : ℍ[ℝ])).differentiableAt
  have e1 := (hasDerivAt_exp_line hd (u : ℍ[ℝ])).unique h
  have e2 := (hasDerivAt_exp_line hd (u' : ℍ[ℝ])).unique h'
  have hz : fderiv ℝ NormedSpace.exp (w : ℍ[ℝ]) ((u : ℍ[ℝ]) - u') = 0 := by
    rw [map_sub, e1, e2, sub_self]
  have hv := eq_zero_of_fderiv_exp_eq_zero w.2 (by simp [show (u : ℍ[ℝ]).re = 0 from u.2, show (u' : ℍ[ℝ]).re = 0 from u'.2]) hw hd hz
  exact Subtype.ext (sub_eq_zero.1 hv)
end Interpolation
end YangMills.Construction
end
