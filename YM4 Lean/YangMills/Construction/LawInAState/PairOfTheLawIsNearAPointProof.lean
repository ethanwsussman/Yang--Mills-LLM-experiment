import YangMills.Construction.LawInAState.FromSixteenCopiesToOneBoxProof
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import YangMills.Construction.LawInAState.PairOfTheLawIsNearAPoint
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPair
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
open TorusMetric TestFunctions TestPairs
open InfiniteLattice (AmbientSpace)
namespace NormalizedPairLocalized
private theorem norm_sub_le_lipschitz {f : AmbientSpace → ℝ} (hl : IsLipschitzFor euclidDistR4 f) (x y : AmbientSpace) :
    ‖f x - f y‖ ≤ bestLipschitzConstant euclidDistR4 f * euclidDistR4 x y := by
  have hd : 0 ≤ euclidDistR4 x y := Real.sqrt_nonneg _
  obtain ⟨C₀, hC₀, hC₁⟩ := hl
  rcases hd.eq_or_lt with h0 | hpos
  · have hx := hC₁ x y
    rw [← h0, mul_zero] at hx ⊢
    exact hx
  · rw [← div_le_iff₀ hpos]
    refine le_csInf ⟨C₀, hC₀, hC₁⟩ ?_
    rintro C ⟨_, hC⟩
    rw [div_le_iff₀ hpos]
    exact hC x y
abbrev _root_.YangMills.DeltaSharedProofs.p501590 := @norm_sub_le_lipschitz
abbrev _root_.YangMills.SharedProofs.p56457 := @norm_sub_le_lipschitz
private theorem euclidNormVec_le_two_mul {v : AmbientSpace} {s : ℝ} (hs : 0 ≤ s) (h : ∀ i, |v i| ≤ s) :
    euclidNormVec v ≤ 2 * s := by apply _root_.YangMills.SharedProofs.p16936 <;> assumption
private theorem abs_apply_le_euclidNormVec (v : AmbientSpace) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.SharedProofs.p10398 <;> assumption
private theorem mem_tsupport_of_ne_zero {f : AmbientSpace → ℝ} {x : AmbientSpace} (h : f x ≠ 0) : x ∈ tsupport f :=
  subset_tsupport f h
end NormalizedPairLocalized
open NormalizedPairLocalized in
theorem normalizedPair_localized (hG : GeometryAndKernelBounds) : normalizedPairLocalizedStatement := by
  intro d vt f h hd hv hv1 hp
  obtain ⟨x₁, x₂, ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩, ⟨b₁, b₂, b₃, b₄, b₅, b₆⟩, c₁, c₂⟩ := id hp.mem_class
  have hcen : IsCentrePairR4 d vt x₁ x₂ (f, h) := ⟨⟨a₄, a₅, a₆⟩, ⟨b₄, b₅, b₆⟩, c₁, c₂⟩
  obtain ⟨⟨-, ⟨-, hsup⟩, apart, kp, chain⟩, -⟩ := hG.1 d vt ⟨hd, hv, hv1⟩ x₁ x₂ f h hp.mem_class hcen
  have hfs := hp.norm_left
  have hhs := hp.norm_right
  rw [hfs] at a₆
  rw [hhs] at b₆
  have hbound : ∀ (g : AmbientSpace → ℝ), IsBoundedFun g → uniformNorm g = 1 → ∀ x, |g x| ≤ 1 := by
    intro g ⟨C, hC⟩ hs x
    have hle := le_ciSup (f := fun x => ‖g x‖) ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩ x
    rw [← hs]
    exact hle
  have hlip : ∀ (g : AmbientSpace → ℝ), IsLipschitzFor euclidDistR4 g → bestLipschitzConstant euclidDistR4 g ≤ 1 / (vt * d) →
      ∀ (x x' : AmbientSpace) (t : ℝ), (∀ i, |x i - x' i| ≤ t) → |g x - g x'| ≤ 2 / (vt * d) * t := by
    intro g hg hc x x' t ht
    have ht0 : 0 ≤ t := (abs_nonneg _).trans (ht 0)
    have k1 := norm_sub_le_lipschitz hg x x'
    have k2 : euclidDistR4 x x' ≤ 2 * t := euclidNormVec_le_two_mul ht0 fun i => ht i
    have k3 : 0 ≤ euclidDistR4 x x' := Real.sqrt_nonneg _
    calc |g x - g x'| ≤ _ := k1
      _ ≤ 1 / (vt * d) * (2 * t) := mul_le_mul hc k2 k3 (by positivity)
      _ = _ := by ring
  have hnear : ∀ (g : AmbientSpace → ℝ) (c : AmbientSpace), tsupport g ⊆ closedBallR4 c (5 * d) →
      ∀ x, g x ≠ 0 → ∀ i, |x i - c i| ≤ 6 * d := by
    intro g c hc x hx i
    have k1 : euclidNormVec (x - c) ≤ 5 * d := hc (mem_tsupport_of_ne_zero hx)
    have k2 := NormalizedPairLocalized.abs_apply_le_euclidNormVec (x - c) i
    simp only [Pi.sub_apply] at k2
    linarith
  refine ⟨midpointR4 x₁ x₂, ⟨hbound f kp.1 hfs, hbound h kp.2.1 hhs,
    hnear f _ fun x hx => hsup (Or.inl hx), hnear h _ fun x hx => hsup (Or.inr hx),
    hlip f a₁ a₆, hlip h b₁ b₆,
    fun x x' hx hx' => (apart x (mem_tsupport_of_ne_zero hx) x' (mem_tsupport_of_ne_zero hx')).1⟩, ?_⟩
  have k1 := chain.1
  have k2 := chain.2.1
  simp only [kernelLowerConst, hfs, hhs, mul_one] at k1
  linarith
end YangMills.Construction.StateLaws
end
