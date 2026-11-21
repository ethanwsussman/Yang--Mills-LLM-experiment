import YangMills.Construction.ClusterExpansionOfAStep.CutOfAConvexLaw
import YangMills.Construction.ClusterExpansionOfAStep.SegmentOfConvexLaws
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open ColdStepAtMirrorFrames
namespace RestrictedLaw
open BallLaws
set_option linter.unusedSectionVars false
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ m κ : ℝ}
theorem sum_inner_bondVariation (S : Finset ι) (b : ι) (η : BondField ι) (e : BondVector) :
    ∑ x ∈ S, inner ℝ (η x) ((bondVariation b e : BondField ι) x) = if b ∈ S then inner ℝ (η b) e else 0 := by
  by_cases hb : b ∈ S
  · rw [if_pos hb, Finset.sum_eq_single b]
    · simp [bondVariation]
    · intro x _ hx
      simp [bondVariation, Pi.single_eq_of_ne hx]
    · exact fun hn => absurd hb hn
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun x hx => ?_
    have : x ≠ b := fun hh => hb (hh ▸ hx)
    simp [bondVariation, Pi.single_eq_of_ne this]
theorem bondGradNorm_sub_restrictedPotential_le {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ}
    {c C₁ : ℝ} (hρ : 0 < ρ)
    (H : IsUniformlyConvexDecaying ρ m κ d Ψ K) (hc : 0 ≤ c)
    (hf : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm Ψ b η ≤ C₁) (X : Finset ι)
    {η : BondField ι} (hη : ∀ b, ‖η b‖ < ρ) (b : ι) :
    bondGradNorm (fun ζ => Ψ ζ - restrictedPotential c X Ψ ζ) b η ≤ restrictedGradBound ρ c C₁ X K b := by
  have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans (hf η hη b)
  have d₀ : Differentiable ℝ Ψ := H.smooth.differentiable (by norm_num)
  have d₁ : DifferentiableAt ℝ (fun ζ => Ψ (restrictCLM X ζ)) η :=
    (H.smooth.comp (restrictCLM X).contDiff).differentiable (by norm_num) η
  have d₂ : DifferentiableAt ℝ (gaussianOn c (Finset.univ \ X)) η :=
    (gaussianOn_contDiff c _).differentiable (by norm_num) η
  have hfd : ∀ a : BondField ι, fderiv ℝ (fun ζ => Ψ ζ - restrictedPotential c X Ψ ζ) η a =
      fderiv ℝ Ψ η a - fderiv ℝ Ψ (restrictCLM X η) (restrictCLM X a) -
        c * ∑ x ∈ Finset.univ \ X, inner ℝ (η x) (a x) := by
    intro a
    rw [restrictedPotential_eq]
    have := ((d₀ η).hasFDerivAt.sub (d₁.hasFDerivAt.add d₂.hasFDerivAt)).fderiv
    erw [this]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
    rw [fderiv_comp_clm H.smooth, gaussianOn_fderiv]
    ring
  unfold restrictedGradBound
  split_ifs with hb
  · have hS : 0 ≤ ∑ b' ∈ Finset.univ \ X, K b b' := Finset.sum_nonneg fun b' _ => kernel_nonneg hρ H b b'
    refine bondGradNorm_le_of_forall (mul_nonneg hρ.le hS) fun e => ?_
    rw [hfd, restrictCLM_bondVariation, if_pos hb, sum_inner_bondVariation, if_neg (by simp [hb]), mul_zero,
      sub_zero]
    set a : BondField ι := bondVariation b e with ha
    set ξ : BondField ι := η - restrictCLM X η with hξ
    have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => fderiv ℝ Ψ (restrictCLM X η + t • ξ) a)
        (secondDerivAlong Ψ (restrictCLM X η + t • ξ) a ξ) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => restrictCLM X η + t • ξ) ξ t := by
        simpa using ((hasDerivAt_id t).smul_const ξ).const_add (restrictCLM X η)
      exact (differentiable_fderiv_apply H.smooth a (restrictCLM X η + t • ξ)).hasFDerivAt.comp_hasDerivAt t h1
    have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖(restrictCLM X η + t • ξ) x‖ < ρ := by
      intro t ht x
      rw [hξ, restrictCLM_apply]
      by_cases hx : x ∈ X
      · simp [restrictToSet, hx, hη x]
      · simp only [restrictToSet, hx, if_false, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
          zero_add, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        calc t * ‖η x‖ ≤ 1 * ‖η x‖ := by gcongr; exact ht.2
          _ < ρ := by simpa using hη x
    have hξsum : ξ = ∑ x ∈ Finset.univ \ X, bondVariation x (η x) := by
      funext y
      rw [Finset.sum_apply]
      rw [hξ, restrictCLM_apply]
      by_cases hy : y ∈ X
      · simp only [Pi.sub_apply, restrictToSet, hy, if_true, sub_self]
        symm
        refine Finset.sum_eq_zero fun x hx => ?_
        have : y ≠ x := fun hh => (Finset.mem_sdiff.mp hx).2 (hh ▸ hy)
        simp [bondVariation, Pi.single_eq_of_ne this]
      · simp only [Pi.sub_apply, restrictToSet, hy, if_false, sub_zero]
        rw [Finset.sum_eq_single y]
        · simp [bondVariation]
        · intro x _ hx
          simp [bondVariation, Pi.single_eq_of_ne hx.symm]
        · intro hn
          exact absurd (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩) hn
    have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖secondDerivAlong Ψ (restrictCLM X η + t • ξ) a ξ‖ ≤
        ρ * (∑ b' ∈ Finset.univ \ X, K b b') * ‖e‖ := by
      intro t ht
      rw [Real.norm_eq_abs]
      have e1 : secondDerivAlong Ψ (restrictCLM X η + t • ξ) a ξ =
          ∑ x ∈ Finset.univ \ X, secondDerivAlong Ψ (restrictCLM X η + t • ξ) a (bondVariation x (η x)) := by
        unfold secondDerivAlong
        rw [hξsum, map_sum]
      rw [e1]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun x _ => ?_
      have := H.kernel _ (hmem t ht) b x e (η x)
      have hK := kernel_nonneg hρ H b x
      calc _ ≤ K b x * ‖e‖ * ‖η x‖ := this
        _ ≤ K b x * ‖e‖ * ρ := by
            gcongr
            exact (hη x).le
        _ = ρ * K b x * ‖e‖ := by ring
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t : ℝ => fderiv ℝ Ψ (restrictCLM X η + t • ξ) a)
      (f' := fun t => secondDerivAlong Ψ (restrictCLM X η + t • ξ) a ξ)
      (s := Set.Icc (0 : ℝ) 1) (C := ρ * (∑ b' ∈ Finset.univ \ X, K b b') * ‖e‖) (x := 0) (y := 1)
      (fun t _ => (hder t).hasDerivWithinAt) hbound (convex_Icc 0 1) (by simp) (by simp)
    have e0 : restrictCLM X η + (0 : ℝ) • ξ = restrictCLM X η := by simp
    have e1 : restrictCLM X η + (1 : ℝ) • ξ = η := by simp [hξ]
    simp only [e0, e1] at hmv
    simpa [Real.norm_eq_abs] using hmv
  · have hbS : b ∈ Finset.univ \ X := Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hb⟩
    refine bondGradNorm_le_of_forall (by positivity) fun e => ?_
    rw [hfd, restrictCLM_bondVariation, if_neg hb, sum_inner_bondVariation, if_pos hbS, map_zero, sub_zero]
    have h1 := abs_fderiv_bondVariation_le Ψ η b e
    have h2 : |inner ℝ (η b) e| ≤ ρ * ‖e‖ := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      gcongr
      exact (hη b).le
    calc |fderiv ℝ Ψ η (bondVariation b e) - c * inner ℝ (η b) e|
        ≤ |fderiv ℝ Ψ η (bondVariation b e)| + |c * inner ℝ (η b) e| := abs_sub _ _
      _ ≤ C₁ * ‖e‖ + c * (ρ * ‖e‖) := by
          rw [abs_mul, abs_of_nonneg hc]
          gcongr
          exact h1.trans (by gcongr; exact hf η hη b)
      _ = (C₁ + c * ρ) * ‖e‖ := by ring
theorem restrictedLawMeanBound_of_segment (hseg : ConvexLawSegmentBound) : RestrictedLawMeanBound := by
  intro ι _ _ ρ m κ A O c C₁ d Ψ K p hρ hm hκ hp hd H hA hc hf X Z F hF hFZ hFO
  have hc0 : 0 ≤ c := by linarith
  have H₀ := isUniformlyConvexDecaying_restrictedPotential hρ hm hd H hc X
  have hA₀ : ∀ b, ∑ b' ∈ Finset.univ.erase b, (K b b' + if b = b' then c else 0) * Real.exp (κ * d b b') ≤
      A * m := by
    intro b
    have e : ∑ b' ∈ Finset.univ.erase b, (K b b' + if b = b' then c else 0) * Real.exp (κ * d b b') =
        ∑ b' ∈ Finset.univ.erase b, K b b' * Real.exp (κ * d b b') := by
      refine Finset.sum_congr rfl fun b' hb' => ?_
      have : b ≠ b' := fun h => (Finset.mem_erase.mp hb').1 h.symm
      simp [this]
    rw [e]
    exact hA b
  exact hseg ι ρ m κ A O d (restrictedPotential c X Ψ) Ψ _ K p hρ hm hκ hp hd H₀ H hA₀ hA Z F
    (restrictedGradBound ρ c C₁ X K) hF hFZ hFO
    (fun η hη b => bondGradNorm_sub_restrictedPotential_le hρ H hc0 hf X hη b)
end RestrictedLaw
theorem restrictedLawMeanBound (hseg : ConvexLawSegmentBound) : RestrictedLawMeanBound := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.RestrictedLaw.restrictedLawMeanBound_of_segment <;> assumption
end YangMills.Construction.ClusterExpansionOfAStep
end
