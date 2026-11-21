import YangMills.Construction.ClusterExpansionOfAStep.SlopeFromOscillation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ColdStepAtMirrorFrames
namespace GradientFromOscillation
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem abs_taylor_two_remainder_le {G : BondField ι → ℝ} (hG : ContDiff ℝ 2 G) (p v : BondField ι) (M' : ℝ)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, |secondDerivAlong G (p + t • v) v v| ≤ M') :
    |G (p + v) - G p - fderiv ℝ G p v| ≤ M' := by
  have hd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hdf : Differentiable ℝ (fun ζ => fderiv ℝ G ζ v) :=
    ((hG.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => p + t • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  set φ' : ℝ → ℝ := fun t => fderiv ℝ G (p + t • v) v with hφ'
  have hφ : ∀ t, HasDerivAt (fun t => G (p + t • v)) (φ' t) t := fun t =>
    (hd (p + t • v)).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hφ2 : ∀ t, HasDerivAt φ' (secondDerivAlong G (p + t • v) v v) t := by
    intro t
    show HasDerivAt ((fun ζ => fderiv ℝ G ζ v) ∘ fun t : ℝ => p + t • v)
      (fderiv ℝ (fun ζ => fderiv ℝ G ζ v) (p + t • v) v) t
    exact (hdf (p + t • v)).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hM0 : 0 ≤ M' := (abs_nonneg _).trans (h 0 (by simp))
  have s1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, |φ' t - φ' 0| ≤ M' := by
    intro t ht
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ')
      (f' := fun t => secondDerivAlong G (p + t • v) v v) (s := Set.Icc (0 : ℝ) 1) (C := M') (x := 0) (y := t)
      (fun t _ => (hφ2 t).hasDerivWithinAt) (fun t ht => h t ht) (convex_Icc _ _) (by simp) ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at this
    have h2 : M' * t ≤ M' := by nlinarith [ht.2]
    exact this.trans h2
  have s2 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => G (p + t • v) - t * φ' 0) (f' := fun t => φ' t - 1 * φ' 0)
    (s := Set.Icc (0 : ℝ) 1) (C := M') (x := 0) (y := 1)
    (fun t _ => ((hφ t).sub ((hasDerivAt_id t).mul_const (φ' 0))).hasDerivWithinAt)
    (fun t ht => by simpa using s1 t ht) (convex_Icc _ _) (by simp) (by simp)
  simp only [one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_zero, Real.norm_eq_abs, abs_one,
    mul_one] at s2
  have e0 : φ' 0 = fderiv ℝ G p v := by simp [hφ']
  rw [e0] at s2
  have : G (p + v) - G p - (fderiv ℝ G p) v = G (p + v) - (fderiv ℝ G p) v - G p := by ring
  rw [this]
  exact s2
theorem bondGradBoundOfOscillation_holds : BondGradBoundOfOscillation := by
  intro ι _ _ G ρ τ e M b hG hτ hτρ hM hosc hsec η hη
  have hρ : 0 < ρ := hτ.trans hτρ
  have he : 0 ≤ e := (abs_nonneg _).trans (hosc η η hη hη fun _ _ => rfl)
  have hB : 0 ≤ e / (2 * τ) + 4 * M * τ := by positivity
  unfold bondGradNorm
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hB fun X hX => ?_
  rw [Real.norm_eq_abs]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  have hsingle : (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b) X = bondVariation b X := rfl
  rw [hsingle]
  have hsize : ∀ (s : ℝ), |s| = 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ c,
      ‖(η + t • bondVariation b ((s * τ) • X - (τ / ρ) • η b)) c‖ < ρ := by
    intro s hs t ht c
    by_cases hc : c = b
    · subst hc
      have e1 : (η + t • bondVariation c ((s * τ) • X - (τ / ρ) • η c)) c =
          (1 - t * (τ / ρ)) • η c + (t * (s * τ)) • X := by
        simp only [Pi.add_apply, Pi.smul_apply, bondVariation, Pi.single_eq_same, smul_sub, smul_smul]
        module
      rw [e1]
      have h1 : 0 ≤ 1 - t * (τ / ρ) := by
        have : t * (τ / ρ) ≤ 1 * 1 := by
          apply mul_le_mul ht.2 _ (by positivity) (by norm_num)
          rw [div_le_one hρ]
          exact hτρ.le
        linarith
      calc ‖(1 - t * (τ / ρ)) • η c + (t * (s * τ)) • X‖
          ≤ ‖(1 - t * (τ / ρ)) • η c‖ + ‖(t * (s * τ)) • X‖ := norm_add_le _ _
        _ = (1 - t * (τ / ρ)) * ‖η c‖ + t * τ := by
          rw [norm_smul, norm_smul, hX, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1, abs_mul, abs_mul,
            hs, abs_of_nonneg ht.1, abs_of_pos hτ]
          ring
        _ < ρ := by
          have h2 := hη c
          have h3 : t * (τ / ρ) * ρ = t * τ := by field_simp
          have hq1 : t * (τ / ρ) < 1 := by
            nlinarith [ht.1, ht.2]
          have h7 := mul_lt_mul_of_pos_left h2 (sub_pos.mpr hq1)
          linarith
    · have : (η + t • bondVariation b ((s * τ) • X - (τ / ρ) • η b)) c = η c := by
        simp [bondVariation, Pi.single_eq_of_ne hc]
      rw [this]
      exact hη c
  set L := fderiv ℝ G η with hL
  have hrem : ∀ (s : ℝ), |s| = 1 →
      |G (η + bondVariation b ((s * τ) • X - (τ / ρ) • η b)) - G η -
        L (bondVariation b ((s * τ) • X - (τ / ρ) • η b))| ≤ M * (2 * τ) ^ 2 := by
    intro s hs
    refine abs_taylor_two_remainder_le hG η _ _ fun t ht => ?_
    refine (hsec _ (hsize s hs t ht) _).trans ?_
    have hn : ‖(s * τ) • X - (τ / ρ) • η b‖ ≤ 2 * τ := by
      calc ‖(s * τ) • X - (τ / ρ) • η b‖ ≤ ‖(s * τ) • X‖ + ‖(τ / ρ) • η b‖ := norm_sub_le _ _
        _ = τ + τ / ρ * ‖η b‖ := by
          rw [norm_smul, norm_smul, hX, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, hs, abs_of_pos hτ,
            abs_of_pos (by positivity)]
          ring
        _ ≤ 2 * τ := by
          have h2 := (hη b).le
          have h3 : τ / ρ * ‖η b‖ ≤ τ / ρ * ρ := by gcongr
          have h4 : τ / ρ * ρ = τ := by field_simp
          linarith
    have := pow_le_pow_left₀ (norm_nonneg _) hn 2
    exact mul_le_mul_of_nonneg_left this hM
  have hp := hrem 1 (by simp)
  have hm := hrem (-1) (by simp)
  have hdiff : ∀ t, t = (1 : ℝ) ∨ t = -1 → ∀ c, ‖(η + bondVariation b ((t * τ) • X - (τ / ρ) • η b)) c‖ < ρ := by
    intro t ht c
    have h1 : |t| = 1 := by rcases ht with rfl | rfl <;> simp
    have := hsize t h1 1 (by simp) c
    simpa using this
  have hosc' := hosc _ _ (hdiff 1 (Or.inl rfl)) (hdiff (-1) (Or.inr rfl)) (fun c hc => by
    simp [bondVariation, Pi.single_eq_of_ne hc])
  have hlin : L (bondVariation b ((1 * τ) • X - (τ / ρ) • η b)) - L (bondVariation b ((-1 * τ) • X - (τ / ρ) • η b)) =
      2 * τ * L (bondVariation b X) := by
    have h1 : bondVariation b ((1 * τ) • X - (τ / ρ) • η b) - bondVariation b ((-1 * τ) • X - (τ / ρ) • η b) =
        (2 * τ) • bondVariation b X := by
      funext c
      by_cases hc : c = b
      · subst hc
        simp only [bondVariation, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same]
        module
      · simp [bondVariation, Pi.single_eq_of_ne hc]
    rw [← map_sub, h1, map_smul, smul_eq_mul]
  have hfinal : 2 * τ * |L (bondVariation b X)| ≤ e + 8 * M * τ ^ 2 := by
    have e2 : 2 * τ * |L (bondVariation b X)| = |2 * τ * L (bondVariation b X)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * τ)]
    rw [e2, ← hlin]
    set a := G (η + bondVariation b ((1 * τ) • X - (τ / ρ) • η b))
    set c := G (η + bondVariation b ((-1 * τ) • X - (τ / ρ) • η b))
    set u := L (bondVariation b ((1 * τ) • X - (τ / ρ) • η b))
    set w := L (bondVariation b ((-1 * τ) • X - (τ / ρ) • η b))
    rw [abs_le] at hp hm hosc' ⊢
    constructor <;> nlinarith [hp.1, hp.2, hm.1, hm.2, hosc'.1, hosc'.2]
  have h2τ : 0 < 2 * τ := by positivity
  have : |L (bondVariation b X)| ≤ (e + 8 * M * τ ^ 2) / (2 * τ) := by
    rw [le_div_iff₀ h2τ]
    linarith
  refine this.trans (le_of_eq ?_)
  field_simp
  ring
end GradientFromOscillation
end YangMills.Construction
end
