import YangMills.Construction.Continuum.PlateauOfAFunctionOnTuples
import YangMills.Construction.TwoPoints.ConvolutionIsOfClassC1
import YangMills.Construction.TwoPoints.FirstConsequencesOfThreePropertiesProof
import YangMills.Construction.TwoPoints.FormAtMollifiedFunctions
import YangMills.Construction.TwoPoints.RiemannSumsInTheSharpNorm
import YangMills.Construction.TwoPoints.TranslationModulusOfAFunction
import Mathlib
set_option autoImplicit false
open Set MeasureTheory Filter Metric
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
namespace MollifiedFormLimit
theorem sup_norm_le_euclidNorm (z : AmbientSpace) : ‖z‖ ≤ euclidNorm z := by apply _root_.YangMills.Construction.TwoPoints.AdmissibleFormConsequences.norm_le_euclidNorm <;> assumption
theorem continuous_euclidNorm : Continuous fun x : AmbientSpace => euclidNorm x := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem sharpNorm_nonneg (σ : FixedScale) (g : AmbientSpace → ℂ) : 0 ≤ σ.sharpNorm g :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem l1Norm_eq_one_of_probability {k : AmbientSpace → ℂ} (hcont : Continuous k)
    (hcpt : IsCompact (tsupport k)) (hnonneg : ∀ x, IsRealNonneg (k x))
    (hmass : lebesgueIntegral k = 1) : l1Norm k = 1 := by
  have hint : Integrable k := hcont.integrable_of_hasCompactSupport hcpt
  have e1 : l1Norm k = ∫ x, ‖k x‖ :=
    (integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable).symm
  have e2 : ∀ x, ‖k x‖ = Complex.reCLM (k x) := by
    intro x
    have hx : k x = (((k x).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [(hnonneg x).1])
    have hn : ‖k x‖ = |(k x).re| := by
      conv_lhs => rw [hx]
      exact Complex.norm_real _
    rw [hn, abs_of_nonneg (hnonneg x).2]
    rfl
  have e3 : (∫ x, k x) = 1 := hmass
  rw [e1, integral_congr_ae (Eventually.of_forall e2), Complex.reCLM.integral_comp_comm hint, e3]
  simp
theorem le_euclidNorm_sub_of_disjoint_cthickening {A B : Set AmbientSpace} {r : ℝ} (hr : 0 < r)
    (hAB : Disjoint (cthickening r A) (cthickening r B)) {a b : AmbientSpace} (ha : a ∈ A)
    (hb : b ∈ B) : r ≤ euclidNorm (a - b) := by
  by_contra hlt
  have hab : dist a b ≤ r := by
    rw [dist_eq_norm]
    exact (sup_norm_le_euclidNorm _).trans (not_le.1 hlt).le
  exact disjoint_left.1 hAB (mem_cthickening_of_dist_le a a r A ha (by simpa using hr.le))
    (mem_cthickening_of_dist_le a b r B hb hab)
theorem tsupport_convolve_subset_cthickening {k g : AmbientSpace → ℂ} {ρ r : ℝ}
    (hsum : tsupport (convolve k g) ⊆ minkowskiSum (tsupport k) (tsupport g))
    (hk : tsupport k ⊆ euclidOpenBall (0 : AmbientSpace) ρ) (hρ : ρ ≤ r) :
    tsupport (convolve k g) ⊆ cthickening r (tsupport g) := by
  intro x hx
  obtain ⟨y, hy, y', hy', rfl⟩ := hsum hx
  refine mem_cthickening_of_dist_le _ y' _ _ hy' ?_
  rw [dist_eq_norm, add_sub_cancel_right]
  have hyρ : euclidNorm (y - (0 : AmbientSpace)) < ρ := hk hy
  rw [sub_zero] at hyρ
  exact ((sup_norm_le_euclidNorm y).trans hyρ.le).trans hρ
theorem tsupport_sub_subset_of_isClosed {u v : AmbientSpace → ℂ} {A : Set AmbientSpace}
    (hA : IsClosed A) (hu : tsupport u ⊆ A) (hv : tsupport v ⊆ A) : tsupport (u - v) ⊆ A := by
  refine closure_minimal (fun x hx => ?_) hA
  rcases Function.support_sub u v hx with hx' | hx'
  · exact hu (subset_tsupport _ hx')
  · exact hv (subset_tsupport _ hx')
end MollifiedFormLimit
open MollifiedFormLimit in
theorem MollifiedFormLimit.holds (hmod : TranslationModulusProperties.Statement)
    (hconvC1 : ConvolveC1.Statement) (hriemann : ConvolutionRiemannSumSharpEstimates.Statement)
    (hcons : AdmissibleFormConsequences.Statement) :
    MollifiedFormLimit.Statement := by
  intro σ S hS hP f hf g hg hfg ι hι
  obtain ⟨D, hD⟩ := hP.ballDecay
  obtain ⟨⟨-, hbilin, -, -, hest⟩, -⟩ := hcons.2.2.2.2 σ S D hS hP hD
  obtain ⟨r, hr, hsep⟩ := Disjoint.exists_cthickenings
    (show Disjoint (tsupport f) (tsupport g) from hfg) hf.2.1 hg.2.1.isClosed
  have hAc : IsCompact (cthickening r (tsupport f)) := hf.2.1.cthickening
  have hBc : IsCompact (cthickening r (tsupport g)) := hg.2.1.cthickening
  obtain ⟨η, hη, hsep'⟩ := Disjoint.exists_cthickenings hsep hAc hBc.isClosed
  obtain ⟨M, hM⟩ := (hAc.union hBc).exists_bound_of_continuousOn continuous_euclidNorm.continuousOn
  have hRpos : 0 < |M| + 1 := by positivity
  have hinball : ∀ x ∈ cthickening r (tsupport f) ∪ cthickening r (tsupport g),
      x ∈ euclidClosedBall (0 : AmbientSpace) (|M| + 1) := by
    intro x hx
    have hxM := hM x hx
    show euclidNorm (x - 0) ≤ |M| + 1
    rw [sub_zero]
    have habs := le_abs_self (euclidNorm x)
    rw [Real.norm_eq_abs] at hxM
    linarith [le_abs_self M]
  set L : ℝ := 4 * D η (|M| + 1) with hLdef
  have hL : 0 ≤ L := mul_nonneg (by norm_num) (hD.1 _ _ hη hRpos)
  have hbd : ∀ u ∈ compactC1Complex, ∀ v ∈ compactC1Complex,
      tsupport u ⊆ cthickening r (tsupport f) →
      tsupport v ⊆ cthickening r (tsupport g) →
      ‖complexifyForm S u v‖ ≤ L * σ.sharpNorm u * σ.sharpNorm v := by
    intro u hu v hv hus hvs
    refine hest η (|M| + 1) hη hRpos 0 0 u hu v hv (fun x hx => hinball x (Or.inl (hus hx)))
      (fun x hx => hinball x (Or.inr (hvs hx))) ?_
    intro a ha b hb
    exact le_euclidNorm_sub_of_disjoint_cthickening hη hsep' (hus ha) (hvs hb)
  have hstep : ∀ n : ℕ, 1 ≤ n → 0 < 1 / (n : ℝ) := fun n hn =>
    one_div_pos.2 (by exact_mod_cast hn)
  have hto0 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hto0' : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hto0, (eventually_ge_atTop 1).mono hstep⟩
  have hlarge : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 1 / (n : ℝ) ≤ r := by
    filter_upwards [eventually_ge_atTop 1, hto0.eventually_lt_const hr] with n a b
    exact ⟨a, b.le⟩
  have hmoll : ∀ n : ℕ, 1 ≤ n → 1 / (n : ℝ) ≤ r → ∀ u ∈ compactC1Complex,
      convolve (ι n) u ∈ compactC1Complex ∧
        tsupport (convolve (ι n) u) ⊆ cthickening r (tsupport u) ∧
        σ.sharpNorm (convolve (ι n) u) ≤ σ.sharpNorm u ∧
        σ.sharpNorm (convolve (ι n) u - u) ≤ σ.translationModulus u (1 / (n : ℝ)) := by
    intro n hn hnr u hu
    have hιn := hι n hn
    have hC0 : ContDiff ℝ 0 (ι n) := hιn.1.1.1.of_le (by exact_mod_cast bot_le)
    have hcc : ι n ∈ ccIn (univ : Set AmbientSpace) :=
      ⟨hC0, hιn.1.1.2.1, subset_univ _⟩
    obtain ⟨p1, p2⟩ := hconvC1 (ι n) hcc u hu
    obtain ⟨-, -, q3, q4⟩ := hriemann σ (ι n) hcc u hu (1 / (n : ℝ)) (hstep n hn)
    have hmass : l1Norm (ι n) = 1 :=
      l1Norm_eq_one_of_probability hC0.continuous hιn.1.1.2.1 hιn.2.1 hιn.2.2
    refine ⟨p1, tsupport_convolve_subset_cthickening p2 hιn.1.1.2.2 hnr, ?_, ?_⟩
    · simpa [hmass] using q3
    · exact q4 hιn.2.1 hιn.2.2 (hιn.1.1.2.2.trans fun y hy =>
        show euclidNorm (y - (0 : AmbientSpace)) ≤ 1 / (n : ℝ) from le_of_lt hy)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hlarge
  refine ⟨⟨N, fun n hn => ?_⟩, ?_⟩
  · obtain ⟨a, b⟩ := hN n hn
    exact Disjoint.mono (hmoll n a b f hf).2.1 (hmoll n a b g hg).2.1 hsep
  have hfA : tsupport f ⊆ cthickening r (tsupport f) := self_subset_cthickening _
  have hgB : tsupport g ⊆ cthickening r (tsupport g) := self_subset_cthickening _
  have hnear : ∀ n : ℕ, 1 ≤ n → 1 / (n : ℝ) ≤ r →
      ‖complexifyForm S (convolve (ι n) f) (convolve (ι n) g) - complexifyForm S f g‖ ≤
        L * σ.translationModulus f (1 / (n : ℝ)) * σ.sharpNorm g +
          L * σ.sharpNorm f * σ.translationModulus g (1 / (n : ℝ)) := by
    intro n hn hnr
    obtain ⟨F₁, F₂, F₃, F₄⟩ := hmoll n hn hnr f hf
    obtain ⟨G₁, G₂, G₃, G₄⟩ := hmoll n hn hnr g hg
    have dFG : DisjointSupports (convolve (ι n) f) (convolve (ι n) g) :=
      Disjoint.mono F₂ G₂ hsep
    have dfG : DisjointSupports f (convolve (ι n) g) := Disjoint.mono hfA G₂ hsep
    have pFG : IsDisjointSupportPair (convolve (ι n) f) (convolve (ι n) g) :=
      ⟨F₁, G₁, dFG⟩
    have pfG : IsDisjointSupportPair f (convolve (ι n) g) := ⟨hf, G₁, dfG⟩
    have pGf : IsDisjointSupportPair (convolve (ι n) g) f := ⟨G₁, hf, dfG.symm⟩
    have pgf : IsDisjointSupportPair g f := ⟨hg, hf, Disjoint.symm hfg⟩
    obtain ⟨-, e₁, -⟩ := hbilin 1 (-1) _ _ _ pFG pfG
    obtain ⟨-, -, e₂⟩ := hbilin 1 (-1) _ _ _ pGf pgf
    have hcomb : ∀ u v : AmbientSpace → ℂ, (1 : ℂ) • u + (-1 : ℂ) • v = u - v := by
      intro u v
      simp [sub_eq_add_neg]
    rw [hcomb] at e₁ e₂
    have hdecomp : complexifyForm S (convolve (ι n) f) (convolve (ι n) g) -
        complexifyForm S f g =
        complexifyForm S (convolve (ι n) f - f) (convolve (ι n) g) +
          complexifyForm S f (convolve (ι n) g - g) := by
      rw [e₁, e₂]
      ring
    have k₁ := hbd _ (compactC1Complex.sub_mem F₁ hf) _ G₁
      (tsupport_sub_subset_of_isClosed hAc.isClosed F₂ hfA) G₂
    have k₂ := hbd _ hf _ (compactC1Complex.sub_mem G₁ hg) hfA
      (tsupport_sub_subset_of_isClosed hBc.isClosed G₂ hgB)
    have m₁ := sharpNorm_nonneg σ (convolve (ι n) f - f)
    have m₂ := sharpNorm_nonneg σ (convolve (ι n) g)
    have m₃ := sharpNorm_nonneg σ f
    have l₁ : L * σ.sharpNorm (convolve (ι n) f - f) * σ.sharpNorm (convolve (ι n) g) ≤
        L * σ.translationModulus f (1 / (n : ℝ)) * σ.sharpNorm g :=
      mul_le_mul (mul_le_mul_of_nonneg_left F₄ hL) G₃ m₂ (mul_nonneg hL (m₁.trans F₄))
    have l₂ : L * σ.sharpNorm f * σ.sharpNorm (convolve (ι n) g - g) ≤
        L * σ.sharpNorm f * σ.translationModulus g (1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left G₄ (mul_nonneg hL m₃)
    rw [hdecomp]
    exact (norm_add_le _ _).trans (add_le_add (k₁.trans l₁) (k₂.trans l₂))
  have hlimf := (((hmod σ f hf).1).2.2.2.2.2).comp hto0'
  have hlimg := (((hmod σ g hg).1).2.2.2.2.2).comp hto0'
  have hupper : Tendsto (fun n : ℕ => L * σ.translationModulus f (1 / (n : ℝ)) * σ.sharpNorm g +
      L * σ.sharpNorm f * σ.translationModulus g (1 / (n : ℝ))) atTop (𝓝 0) := by
    have t := ((hlimf.const_mul L).mul_const (σ.sharpNorm g)).add
      (hlimg.const_mul (L * σ.sharpNorm f))
    simpa using t
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hlarge.mono fun n hn => hnear n hn.1 hn.2) hupper
end YangMills.Construction.TwoPoints
end
