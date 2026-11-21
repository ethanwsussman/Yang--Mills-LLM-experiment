import YangMills.Construction.TwoPoints.ConvolutionIsOfClassC1
import YangMills.Construction.TwoPoints.FormAtRiemannSumsIsADoubleRiemannSumProof
import YangMills.Construction.TwoPoints.FormIsTheLimitAtRiemannSums
import YangMills.Construction.TwoPoints.RiemannSumsInTheSharpNorm
import YangMills.Construction.TwoPoints.TranslationModulusOfAFunction
import Mathlib
open Filter Set
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
namespace FormIsGridSumLimit
open InfiniteLattice (AmbientSpace)
theorem euclidNorm_add_le (x y : AmbientSpace) :
    euclidNorm (x + y) ≤ euclidNorm x + euclidNorm y := by apply _root_.YangMills.Construction.TwoPoints.GridSumForm.euclidNorm_add_le <;> assumption
theorem euclidNorm_neg (x : AmbientSpace) : euclidNorm (-x) = euclidNorm x := by
  simp [euclidNorm]
theorem continuous_euclidNorm : Continuous (euclidNorm : AmbientSpace → ℝ) := by apply _root_.YangMills.Construction.TwoPoints.GridSumForm.continuous_euclidNorm <;> assumption
theorem sharpNorm_nonneg (Sc : FixedScale) (f : AmbientSpace → ℂ) : 0 ≤ Sc.sharpNorm f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
def nearSet (Z : Set AmbientSpace) (r : ℝ) : Set AmbientSpace :=
  {y | ∃ z ∈ Z, euclidNorm (y - z) ≤ r}
theorem exists_sep_margin {ε : ℝ} {K₁ K₂ : Set AmbientSpace} (c₁ : IsCompact K₁)
    (c₂ : IsCompact K₂) (hsep : ∀ z₁ ∈ K₁, ∀ z₂ ∈ K₂, 2 * ε < euclidNorm (z₂ - z₁)) :
    ∃ d : ℝ, 0 < d ∧ ∀ z₁ ∈ K₁, ∀ z₂ ∈ K₂, 2 * ε + d ≤ euclidNorm (z₂ - z₁) := by
  rcases (K₁ ×ˢ K₂).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun z₁ a z₂ b => ?_⟩
    have hm : (z₁, z₂) ∈ K₁ ×ˢ K₂ := ⟨a, b⟩
    rw [hemp] at hm
    exact hm.elim
  · have hcont : Continuous fun p : AmbientSpace × AmbientSpace => euclidNorm (p.2 - p.1) :=
      continuous_euclidNorm.comp (continuous_snd.sub continuous_fst)
    obtain ⟨p, hp, hmin⟩ := (c₁.prod c₂).exists_isMinOn hne hcont.continuousOn
    refine ⟨euclidNorm (p.2 - p.1) - 2 * ε, sub_pos.2 (hsep _ hp.1 _ hp.2),
      fun z₁ a z₂ b => ?_⟩
    have hle : euclidNorm (p.2 - p.1) ≤ euclidNorm (z₂ - z₁) :=
      hmin (show (z₁, z₂) ∈ K₁ ×ˢ K₂ from ⟨a, b⟩)
    linarith
theorem minkowskiSum_subset_nearSet {Z P : Set AmbientSpace} {ε r : ℝ}
    (hP : P ⊆ euclidOpenBall (0 : AmbientSpace) ε) (hr : ε ≤ r) :
    minkowskiSum Z P ⊆ nearSet Z r := by
  rintro _ ⟨z, hz, p, hp, rfl⟩
  refine ⟨z, hz, ?_⟩
  have hp' : euclidNorm p < ε := by simpa [euclidOpenBall] using hP hp
  rw [add_sub_cancel_left]
  linarith
theorem minkowskiSum_minkowskiSum_subset_nearSet {Z P : Set AmbientSpace} {ε δ r : ℝ}
    (hP : P ⊆ euclidOpenBall (0 : AmbientSpace) ε) (hr : δ + ε ≤ r) :
    minkowskiSum (minkowskiSum Z (euclidClosedBall (0 : AmbientSpace) δ)) P ⊆ nearSet Z r := by
  rintro _ ⟨_, ⟨z, hz, b, hb, rfl⟩, p, hp, rfl⟩
  refine ⟨z, hz, ?_⟩
  have hb' : euclidNorm b ≤ δ := by simpa [euclidClosedBall] using hb
  have hp' : euclidNorm p < ε := by simpa [euclidOpenBall] using hP hp
  have hrw : z + b + p - z = b + p := by abel
  rw [hrw]
  linarith [euclidNorm_add_le b p]
theorem nearSet_separatedBy {ε d : ℝ} {K₁ K₂ : Set AmbientSpace}
    (hgap : ∀ z₁ ∈ K₁, ∀ z₂ ∈ K₂, 2 * ε + d ≤ euclidNorm (z₂ - z₁)) :
    SeparatedBy (d / 2) (nearSet K₁ (d / 4 + ε)) (nearSet K₂ (d / 4 + ε)) := by
  rintro y₁ ⟨z₁, hz₁, e₁⟩ y₂ ⟨z₂, hz₂, e₂⟩
  have hrw : z₂ - z₁ = -(y₂ - z₂) + (y₁ - z₁) + -(y₁ - y₂) := by abel
  have hle : euclidNorm (z₂ - z₁) ≤
      euclidNorm (y₂ - z₂) + euclidNorm (y₁ - z₁) + euclidNorm (y₁ - y₂) := by
    rw [hrw]
    refine (euclidNorm_add_le _ _).trans ?_
    rw [euclidNorm_neg]
    have := euclidNorm_add_le (-(y₂ - z₂)) (y₁ - z₁)
    rw [euclidNorm_neg] at this
    linarith
  linarith [hgap z₁ hz₁ z₂ hz₂]
theorem exists_common_ball {K₁ K₂ : Set AmbientSpace} (c₁ : IsCompact K₁) (c₂ : IsCompact K₂)
    {r : ℝ} (hr : 0 < r) :
    ∃ R : ℝ, 0 < R ∧ nearSet K₁ r ⊆ euclidClosedBall (0 : AmbientSpace) R ∧
      nearSet K₂ r ⊆ euclidClosedBall (0 : AmbientSpace) R := by
  obtain ⟨B₁, hB₁⟩ := c₁.exists_bound_of_continuousOn continuous_euclidNorm.continuousOn
  obtain ⟨B₂, hB₂⟩ := c₂.exists_bound_of_continuousOn continuous_euclidNorm.continuousOn
  have hball : ∀ {y z : AmbientSpace} {B : ℝ}, euclidNorm (y - z) ≤ r →
      ‖euclidNorm z‖ ≤ B → euclidNorm y ≤ B + r := by
    intro y z B hy hz
    have hrw : y = (y - z) + z := by abel
    have ht := euclidNorm_add_le (y - z) z
    rw [← hrw] at ht
    linarith [le_abs_self (euclidNorm z), Real.norm_eq_abs (euclidNorm z)]
  refine ⟨|B₁| + |B₂| + r, by positivity, ?_, ?_⟩
  · rintro y ⟨z, hz, hy⟩
    have := hball hy (hB₁ z hz)
    simp only [euclidClosedBall, mem_ofPred_eq, sub_zero]
    linarith [le_abs_self B₁, abs_nonneg B₂]
  · rintro y ⟨z, hz, hy⟩
    have := hball hy (hB₂ z hz)
    simp only [euclidClosedBall, mem_ofPred_eq, sub_zero]
    linarith [le_abs_self B₂, abs_nonneg B₁]
theorem tsupport_sub_subset_union (f g : AmbientSpace → ℂ) :
    tsupport (f - g) ⊆ tsupport f ∪ tsupport g := by
  simp only [tsupport]
  rw [← closure_union]
  exact closure_mono (Function.support_sub f g)
theorem norm_complexifyForm_sub_le {Sc : FixedScale}
    {B : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {C : ℝ → ℝ → ℝ}
    (hlin : ComplexifyLinear B) (hbd : ComplexifyBallBound Sc B C)
    {d R : ℝ} (hd : 0 < d) (hR : 0 < R) {U₁ U₂ : Set AmbientSpace}
    (hU₁ : U₁ ⊆ euclidClosedBall (0 : AmbientSpace) R)
    (hU₂ : U₂ ⊆ euclidClosedBall (0 : AmbientSpace) R)
    (hU : SeparatedBy d U₁ U₂) {u₁ v₁ u₂ v₂ : AmbientSpace → ℂ}
    (hu₁ : u₁ ∈ compactC1Complex) (hv₁ : v₁ ∈ compactC1Complex)
    (hu₂ : u₂ ∈ compactC1Complex) (hv₂ : v₂ ∈ compactC1Complex)
    (su₁ : tsupport u₁ ⊆ U₁) (sv₁ : tsupport v₁ ⊆ U₁)
    (su₂ : tsupport u₂ ⊆ U₂) (sv₂ : tsupport v₂ ⊆ U₂) :
    ‖complexifyForm B u₁ u₂ - complexifyForm B v₁ v₂‖ ≤
      4 * C d R * (Sc.sharpNorm (u₁ - v₁) * Sc.sharpNorm u₂) +
        4 * C d R * (Sc.sharpNorm v₁ * Sc.sharpNorm (u₂ - v₂)) := by
  have hdisj : ∀ {f h : AmbientSpace → ℂ}, tsupport f ⊆ U₁ → tsupport h ⊆ U₂ →
      DisjointSupports f h := by
    intro f h sf sh
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    have h0 := hU x (sf hx) x (sh hx')
    have hz : euclidNorm (x - x) = 0 := by simp [euclidNorm]
    linarith
  have hcomb : ∀ a b : AmbientSpace → ℂ, (1 : ℂ) • a + (-1 : ℂ) • b = a - b := by
    intro a b
    funext x
    simp [sub_eq_add_neg]
  have q₁ : IsDisjointSupportPair u₁ u₂ := ⟨hu₁, hu₂, hdisj su₁ su₂⟩
  have q₂ : IsDisjointSupportPair v₁ u₂ := ⟨hv₁, hu₂, hdisj sv₁ su₂⟩
  have q₃ : IsDisjointSupportPair u₂ v₁ :=
    ⟨hu₂, hv₁, (hdisj sv₁ su₂ : Disjoint (tsupport v₁) (tsupport u₂)).symm⟩
  have q₄ : IsDisjointSupportPair v₂ v₁ :=
    ⟨hv₂, hv₁, (hdisj sv₁ sv₂ : Disjoint (tsupport v₁) (tsupport v₂)).symm⟩
  obtain ⟨-, l₁, -⟩ := hlin 1 (-1) u₁ v₁ u₂ q₁ q₂
  obtain ⟨-, -, l₂⟩ := hlin 1 (-1) u₂ v₂ v₁ q₃ q₄
  rw [hcomb] at l₁ l₂
  have w₁ : tsupport (u₁ - v₁) ⊆ U₁ :=
    (tsupport_sub_subset_union u₁ v₁).trans (union_subset su₁ sv₁)
  have w₂ : tsupport (u₂ - v₂) ⊆ U₂ :=
    (tsupport_sub_subset_union u₂ v₂).trans (union_subset su₂ sv₂)
  have k₁ := hbd d R hd hR 0 0 (u₁ - v₁) (compactC1Complex.sub_mem hu₁ hv₁) u₂ hu₂
    (w₁.trans hU₁) (su₂.trans hU₂) (fun y hy y' hy' => hU y (w₁ hy) y' (su₂ hy'))
  have k₂ := hbd d R hd hR 0 0 v₁ hv₁ (u₂ - v₂) (compactC1Complex.sub_mem hu₂ hv₂)
    (sv₁.trans hU₁) (w₂.trans hU₂) (fun y hy y' hy' => hU y (sv₁ hy) y' (w₂ hy'))
  have hsplit : complexifyForm B u₁ u₂ - complexifyForm B v₁ v₂ =
      complexifyForm B (u₁ - v₁) u₂ + complexifyForm B v₁ (u₂ - v₂) := by
    rw [l₁, l₂]
    ring
  rw [hsplit, ← mul_assoc, ← mul_assoc]
  exact (norm_add_le _ _).trans (add_le_add k₁ k₂)
end FormIsGridSumLimit
open FormIsGridSumLimit in
theorem FormIsGridSumLimit.proof
    (hMod : TranslationModulusProperties.Statement) (hConv : ConvolveC1.Statement)
    (hTerms : RiemannSumTermProperties.Statement)
    (hBounds : ConvolutionRiemannSumSharpEstimates.Statement)
    (hFirst : AdmissibleFormConsequences.Statement) :
    FormIsGridSumLimit.Statement := by
  intro Sc B hB hA ε hε φ₁ hφ₁ φ₂ hφ₂ k₁ hk₁ k₂ hk₂ hsep
  obtain ⟨C, hC⟩ := hA.ballDecay
  obtain ⟨-, -, -, -, h5⟩ := hFirst
  obtain ⟨⟨-, hlin, -, -, hbd⟩, -⟩ := h5 Sc B C hB hA hC
  have hc₁ : φ₁ ∈ compactC1Complex := ⟨hφ₁.1, hφ₁.2.1, subset_univ _⟩
  have hc₂ : φ₂ ∈ compactC1Complex := ⟨hφ₂.1, hφ₂.2.1, subset_univ _⟩
  have hb₁ : tsupport φ₁ ⊆ euclidOpenBall (0 : InfiniteLattice.AmbientSpace) ε := hφ₁.2.2
  have hb₂ : tsupport φ₂ ⊆ euclidOpenBall (0 : InfiniteLattice.AmbientSpace) ε := hφ₂.2.2
  have hK₁ : IsCompact (tsupport k₁) := hk₁.2.1
  have hK₂ : IsCompact (tsupport k₂) := hk₂.2.1
  obtain ⟨d, hd, hgap⟩ := exists_sep_margin hK₁ hK₂ hsep
  have hr : 0 < d / 4 + ε := by positivity
  obtain ⟨R, hR, hN₁, hN₂⟩ := exists_common_ball hK₁ hK₂ hr
  have hdist := nearSet_separatedBy hgap
  have hd2 : 0 < d / 2 := by positivity
  obtain ⟨hg₁, hsg₁⟩ := hConv k₁ hk₁ φ₁ hc₁
  obtain ⟨hg₂, hsg₂⟩ := hConv k₂ hk₂ φ₂ hc₂
  have tg₁ := hsg₁.trans (minkowskiSum_subset_nearSet hb₁ (r := d / 4 + ε) (by linarith))
  have tg₂ := hsg₂.trans (minkowskiSum_subset_nearSet hb₂ (r := d / 4 + ε) (by linarith))
  refine ⟨Set.disjoint_left.2 fun x hx hx' => ?_, ?_⟩
  · have h0 := hdist x (tg₁ hx) x (tg₂ hx')
    have hz : euclidNorm (x - x) = 0 := by simp [euclidNorm]
    linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have t₁ := (hMod Sc φ₁ hc₁).1.2.2.2.2.2
  have t₂ := (hMod Sc φ₂ hc₂).1.2.2.2.2.2
  have hlim := (t₁.const_mul (4 * C (d / 2) R * l1Norm k₁ *
      (l1Norm k₂ * Sc.sharpNorm φ₂))).add
    (t₂.const_mul (4 * C (d / 2) R * (l1Norm k₁ * Sc.sharpNorm φ₁) * l1Norm k₂))
  simp only [mul_zero, add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < d / 4 by positivity)] with δ hδ
  obtain ⟨-, -, -, -, hf₁, hsf₁⟩ := hTerms k₁ hk₁ φ₁ hc₁ δ hδ.1
  obtain ⟨-, -, -, -, hf₂, hsf₂⟩ := hTerms k₂ hk₂ φ₂ hc₂ δ hδ.1
  have tf₁ := hsf₁.trans
    (minkowskiSum_minkowskiSum_subset_nearSet hb₁ (r := d / 4 + ε) (by linarith [hδ.2]))
  have tf₂ := hsf₂.trans
    (minkowskiSum_minkowskiSum_subset_nearSet hb₂ (r := d / 4 + ε) (by linarith [hδ.2]))
  obtain ⟨a₁, a₂, -, -⟩ := hBounds Sc k₁ hk₁ φ₁ hc₁ δ hδ.1
  obtain ⟨c₁, -, c₃, -⟩ := hBounds Sc k₂ hk₂ φ₂ hc₂ δ hδ.1
  have key := norm_complexifyForm_sub_le hlin hbd hd2 hR hN₁ hN₂ hdist hg₁ hf₁ hg₂ hf₂
    tg₁ tf₁ tg₂ tf₂
  have hC0 : 0 ≤ 4 * C (d / 2) R := by
    have := hC.1 (d / 2) R hd2 hR
    linarith
  have m₁ := mul_le_mul a₁ c₃ (sharpNorm_nonneg Sc _) ((sharpNorm_nonneg Sc _).trans a₁)
  have m₂ := mul_le_mul a₂ c₁ (sharpNorm_nonneg Sc _) ((sharpNorm_nonneg Sc _).trans a₂)
  have n₁ := mul_le_mul_of_nonneg_left m₁ hC0
  have n₂ := mul_le_mul_of_nonneg_left m₂ hC0
  rw [norm_sub_rev]
  refine key.trans ((add_le_add n₁ n₂).trans (le_of_eq ?_))
  ring
end YangMills.Construction.TwoPoints
end
