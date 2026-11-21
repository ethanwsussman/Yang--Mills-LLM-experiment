import YangMills.Construction.ResponseInTheExpansion.RightShiftNearZero
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open scoped Quaternion Topology
open BlockAverages Interpolation
namespace LinearResponse
theorem rightTranslationDerivUniqueNearZero_holds : RightTranslationDerivUniqueNearZero := by
  have hs : HasStrictFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ]) 0 := hasStrictFDerivAt_exp_zero
  have hl := hs.isLittleO.def (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨S, hS, hSb⟩ := Filter.eventually_iff_exists_mem.1 hl
  obtain ⟨r₀, hr₀, hball⟩ := Metric.nhds_basis_ball.mem_iff.1 hS
  refine ⟨r₀, hr₀, fun w X u u' hw h h' => ?_⟩
  by_contra hne
  set vv : ℍ[ℝ] := (u : ℍ[ℝ]) - (u' : ℍ[ℝ]) with hvv
  have hv0 : vv ≠ 0 := fun h0 => hne (Subtype.ext (sub_eq_zero.1 h0))
  have hv : 0 < ‖vv‖ := norm_pos_iff.2 hv0
  set g : ℝ → ℍ[ℝ] := fun τ => NormedSpace.exp ((w : ℍ[ℝ]) + τ • (u : ℍ[ℝ])) -
    NormedSpace.exp ((w : ℍ[ℝ]) + τ • (u' : ℍ[ℝ])) with hg
  have hgd : HasDerivAt g 0 0 := by
    have := h.sub h'
    rw [sub_self] at this
    exact this
  have hlo := hgd.isLittleO.def (show (0 : ℝ) < ‖vv‖ / 4 by positivity)
  have hc : ∀ a : ℍ[ℝ], ∀ᶠ τ : ℝ in 𝓝 0, ‖(w : ℍ[ℝ]) + τ • a‖ < r₀ := fun a => by
    have hcont : Continuous fun τ : ℝ => ‖(w : ℍ[ℝ]) + τ • a‖ := by fun_prop
    have h0 : ‖(w : ℍ[ℝ]) + (0 : ℝ) • a‖ < r₀ := by simpa using hw
    exact hcont.continuousAt.eventually (Iio_mem_nhds h0)
  have hall := ((hlo.and (hc u)).and (hc u')).filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))
  obtain ⟨τ, ⟨⟨h1, h2⟩, h3⟩, hτ⟩ := (hall.and self_mem_nhdsWithin).exists
  have hτ0 : τ ≠ 0 := hτ
  have hτp : 0 < |τ| := abs_pos.2 hτ0
  have hin : (((w : ℍ[ℝ]) + τ • (u : ℍ[ℝ]), (w : ℍ[ℝ]) + τ • (u' : ℍ[ℝ])) : ℍ[ℝ] × ℍ[ℝ]) ∈ S := by
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [dist_zero_right, Prod.fst_zero, Prod.snd_zero]
    exact max_lt h2 h3
  have h4 := hSb _ hin
  simp only [ContinuousLinearMap.one_apply] at h4
  have e1 : (w : ℍ[ℝ]) + τ • (u : ℍ[ℝ]) - ((w : ℍ[ℝ]) + τ • (u' : ℍ[ℝ])) = τ • vv := by
    rw [hvv, smul_sub]
    abel
  rw [e1] at h4
  have h5 : ‖g τ‖ ≤ ‖vv‖ / 4 * |τ| := by
    have e2 : g 0 = 0 := by simp [hg]
    simpa [e2] using h1
  have h6 : ‖τ • vv‖ ≤ ‖g τ - τ • vv‖ + ‖g τ‖ := by
    have := norm_sub_le (g τ) (g τ - τ • vv)
    simpa [norm_sub_rev, add_comm] using this
  rw [norm_smul, Real.norm_eq_abs] at h6 h4
  nlinarith [mul_pos hτp hv]
end LinearResponse
end YangMills.Construction
end
