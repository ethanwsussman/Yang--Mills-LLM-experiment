import YangMills.Construction.ClusterExpansionOfAStep.CutOfAConvexLaw
import YangMills.Construction.ClusterExpansionOfAStep.MarginalOfACutLaw
import YangMills.Construction.ClusterExpansionOfAStep.SegmentOfConvexLaws
import YangMills.Construction.ClusterExpansionOfAStep.TwoLawsOnACommonPart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open ColdStepAtMirrorFrames BallLaws
namespace SharedMarginal
set_option linter.unusedSectionVars false
variable {ι ι₀ : Type} [Fintype ι] [DecidableEq ι] [Fintype ι₀] [DecidableEq ι₀] {ρ m κ A : ℝ}
theorem extendByZero_bondVariation {j : ι₀ → ι} (hj : Function.Injective j) (a : ι₀) (v : BondVector) :
    extendByZero j (bondVariation a v) = bondVariation (j a) v := by
  funext b
  by_cases hb : ∃ a', j a' = b
  · obtain ⟨a', rfl⟩ := hb
    rw [extendByZero_apply_image hj]
    by_cases h : a' = a
    · subst h
      simp [bondVariation]
    · have h' : j a' ≠ j a := fun e => h (hj e)
      simp [bondVariation, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
  · have hb' : ∀ a', j a' ≠ b := fun a' e => hb ⟨a', e⟩
    rw [extendByZero_apply_of_not_mem_range _ hb']
    have hne : b ≠ j a := fun e => hb' a e.symm
    simp [bondVariation, Pi.single_eq_of_ne hne]
theorem extendByZero_norm_lt {j : ι₀ → ι} (hj : Function.Injective j) (hρ : 0 < ρ) {ξ : BondField ι₀}
    (hξ : ∀ a, ‖ξ a‖ < ρ) : ∀ b, ‖extendByZero j ξ b‖ < ρ := by
  intro b
  by_cases hb : ∃ a, j a = b
  · obtain ⟨a, rfl⟩ := hb
    rw [extendByZero_apply_image hj]
    exact hξ a
  · rw [extendByZero_apply_of_not_mem_range _ fun a e => hb ⟨a, e⟩]
    simpa using hρ
theorem sum_comp_injective_le {j : ι₀ → ι} (hj : Function.Injective j) (f : ι → ℝ) (hf : ∀ b, 0 ≤ f b)
    (s : Finset ι₀) : ∑ a ∈ s, f (j a) ≤ ∑ b, f b := by
  rw [← Finset.sum_image (f := f) (g := j) (s := s) fun _ _ _ _ e => hj e]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b _ _ => hf b
theorem isUniformlyConvexDecaying_comp_extendByZero {d : ι → ι → ℝ} {d₀ : ι₀ → ι₀ → ℝ}
    {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} {j : ι₀ → ι}
    (hρ : 0 < ρ) (hm : 0 < m) (hκ : 0 ≤ κ) (hd : IsPseudoMetricOnBonds d) (hj : Function.Injective j)
    (hd₀ : ∀ a b, d₀ a b = d (j a) (j b))
    (H : IsUniformlyConvexDecaying ρ m κ d Ψ K) :
    IsUniformlyConvexDecaying ρ m κ d₀ (fun ξ => Ψ (extendByZero j ξ)) fun a a' => K (j a) (j a') := by
  refine ⟨H.smooth.comp (extendByZero j).contDiff, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ u
    rw [secondDerivAlong_comp_clm H.smooth]
    have h := H.floor _ (extendByZero_norm_lt hj hρ hξ) (extendByZero j u)
    have e : ∑ a, ‖u a‖ ^ 2 ≤ ∑ b, ‖extendByZero j u b‖ ^ 2 := by
      have := sum_comp_injective_le hj (fun b => ‖extendByZero j u b‖ ^ 2) (fun _ => by positivity) Finset.univ
      simpa [extendByZero_apply_image hj] using this
    nlinarith
  · intro ξ hξ a a' e e'
    rw [secondDerivAlong_comp_clm H.smooth, extendByZero_bondVariation hj, extendByZero_bondVariation hj]
    exact H.kernel _ (extendByZero_norm_lt hj hρ hξ) _ _ e e'
  · intro a a'
    exact H.symm _ _
  · intro a
    have h := H.standingConstraints (j a)
    have hs := sum_comp_injective_le hj (fun b => K (j a) b * (Real.exp (2 * κ * d (j a) b) - 1)) (fun b => by
      have h1 := kernel_nonneg hρ H (j a) b
      have h2 := pseudoMetric_nonneg hd (j a) b
      have : 1 ≤ Real.exp (2 * κ * d (j a) b) := Real.one_le_exp (by positivity)
      exact mul_nonneg h1 (by linarith)) Finset.univ
    simp only [hd₀]
    exact hs.trans h
theorem kernel_exp_sum_comp_le {d : ι → ι → ℝ} {d₀ : ι₀ → ι₀ → ℝ} {Ψ : BondField ι → ℝ}
    {K : ι → ι → ℝ} {j : ι₀ → ι}
    (hρ : 0 < ρ) (hj : Function.Injective j) (hd₀ : ∀ a b, d₀ a b = d (j a) (j b))
    (H : IsUniformlyConvexDecaying ρ m κ d Ψ K)
    (hA : ∀ b, ∑ b' ∈ Finset.univ.erase b, K b b' * Real.exp (κ * d b b') ≤ A * m) (a : ι₀) :
    ∑ a' ∈ Finset.univ.erase a, K (j a) (j a') * Real.exp (κ * d₀ a a') ≤ A * m := by
  refine le_trans ?_ (hA (j a))
  simp only [hd₀]
  rw [← Finset.sum_image (f := fun b => K (j a) b * Real.exp (κ * d (j a) b)) (g := j)
    (s := Finset.univ.erase a) fun _ _ _ _ e => hj e]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ =>
    mul_nonneg (kernel_nonneg hρ H _ _) (Real.exp_pos _).le
  intro b hb
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hb
  exact Finset.mem_erase.mpr ⟨fun e => (Finset.mem_erase.mp ha').1 (hj e), Finset.mem_univ _⟩
theorem sharedMarginalMeanBound_of (hcut : RestrictedLawMeanBound) (hmar : MarginalOfRestrictedLaw)
    (hseg : ConvexLawSegmentBound) : SharedMarginalMeanBound := by
  intro ι ι' ι₀ _ _ _ _ _ _ ρ m κ A O c C₁ d d' d₀ Ψ Ψ' K K' p j j' hρ hm hκ hp hd hd' hj hj' h₀ h₀' H H' hA hA' hc
    hf hf' Z F B hF hFZ hFO hB
  have D₀ : IsPseudoMetricOnBonds d₀ := ⟨fun a => by rw [h₀, hd.self], fun a b => by rw [h₀, h₀, hd.symm],
    fun a b c => by rw [h₀, h₀, h₀]; exact hd.triangle _ _ _⟩
  have c1 := hcut ι ρ m κ A O c C₁ d Ψ K p hρ hm hκ hp hd H hA hc hf (Finset.univ.image j) (Z.image j)
    (fun η => F fun a => η (j a)) (hF.comp (measurable_pi_lambda _ fun a => measurable_pi_apply (j a)))
    (fun η η' h => hFZ _ _ fun a ha => h _ (Finset.mem_image_of_mem j ha))
    (fun η η' h h' => hFO _ _ (fun a => h _) fun a => h' _)
  have c2 := hcut ι' ρ m κ A O c C₁ d' Ψ' K' p hρ hm hκ hp hd' H' hA' hc hf' (Finset.univ.image j') (Z.image j')
    (fun η => F fun a => η (j' a)) (hF.comp (measurable_pi_lambda _ fun a => measurable_pi_apply (j' a)))
    (fun η η' h => hFZ _ _ fun a ha => h _ (Finset.mem_image_of_mem j' ha))
    (fun η η' h h' => hFO _ _ (fun a => h _) fun a => h' _)
  rw [hmar ι ι₀ ρ c Ψ p j F hρ hp hj, Finset.sum_image fun _ _ _ _ e => hj e] at c1
  rw [hmar ι' ι₀ ρ c Ψ' p j' F hρ hp hj', Finset.sum_image fun _ _ _ _ e => hj' e] at c2
  have c3 := hseg ι₀ ρ m κ A O d₀ (fun ξ => Ψ (extendByZero j ξ)) (fun ξ => Ψ' (extendByZero j' ξ)) _ _ p
    hρ hm hκ hp D₀
    (isUniformlyConvexDecaying_comp_extendByZero hρ hm hκ hd hj h₀ H)
    (isUniformlyConvexDecaying_comp_extendByZero hρ hm hκ hd' hj' (fun a b => (h₀' a b)) H')
    (kernel_exp_sum_comp_le hρ hj h₀ H hA) (kernel_exp_sum_comp_le hρ hj' h₀' H' hA') Z F B hF hFZ hFO hB
  rw [mul_add, mul_add]
  set x₁ := ballExpectation (cutoffFactor ρ p) Ψ (fun η => F fun a => η (j a))
  set x₂ := ballExpectation (cutoffFactor ρ p) Ψ' (fun η => F fun a => η (j' a))
  set y₁ := ballExpectation (cutoffFactor ρ p) (fun ξ => Ψ (extendByZero j ξ)) F
  set y₂ := ballExpectation (cutoffFactor ρ p) (fun ξ => Ψ' (extendByZero j' ξ)) F
  have e : x₁ - x₂ = (x₁ - y₁) - (x₂ - y₂) - (y₂ - y₁) := by ring
  rw [e]
  have t1 := abs_sub (x₁ - y₁ - (x₂ - y₂)) (y₂ - y₁)
  have t2 := abs_sub (x₁ - y₁) (x₂ - y₂)
  linarith
end SharedMarginal
theorem sharedMarginalMeanBound (hcut : RestrictedLawMeanBound) (hmar : MarginalOfRestrictedLaw)
    (hseg : ConvexLawSegmentBound) : SharedMarginalMeanBound := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedMarginal.sharedMarginalMeanBound_of <;> assumption
end YangMills.Construction.ClusterExpansionOfAStep
end
