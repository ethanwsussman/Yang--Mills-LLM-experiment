import YangMills.Construction.Matrices.EveryPolynomialOnPowersOfGHasFiniteDegrees
import YangMills.Construction.TransferOperators.HatIsLinearAndKeepsRealFunctions
import YangMills.Construction.TransferOperators.SeriesOfTheOperatorHatConverges
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2 YangMills.Construction.TransferOperators
noncomputable section
namespace YangMills.Construction.SpinHarmonics.HatLinearReal
variable {J : Type} [Finite J]
theorem integrable_isotypicIntegrand (B : Set J) (l : ↥B → HalfNatural)
    (F : C(J → specialUnitary, ℂ)) (u : J → specialUnitary) :
    Integrable (fun w : ↥B → specialUnitary => isotypicKernel l (restrictTo B u) w *
      F (glue B w (restrictTo Bᶜ u))) (haarPi ↥B) := by
  have hpair : Continuous fun w : ↥B → specialUnitary =>
      ((u, w) : (J → specialUnitary) × (↥B → specialUnitary)) :=
    Continuous.prodMk_right u
  have hcont := (continuous_partKernelIntegrand B l F).comp hpair
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
theorem partIsotypicProjC_smul_add (B : Set J) (l : ↥B → HalfNatural) (a : ℂ)
    (F H : C(J → specialUnitary, ℂ)) :
    partIsotypicProjC B l (a • F + H) =
      a • partIsotypicProjC B l F + partIsotypicProjC B l H := by
  ext u
  have hfun : (fun w : ↥B → specialUnitary => isotypicKernel l (restrictTo B u) w *
      (a • F + H) (glue B w (restrictTo Bᶜ u))) =
      fun w => a * (isotypicKernel l (restrictTo B u) w *
          F (glue B w (restrictTo Bᶜ u))) +
        isotypicKernel l (restrictTo B u) w *
          H (glue B w (restrictTo Bᶜ u)) := by
    funext w
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
    ring
  change (∫ w, isotypicKernel l (restrictTo B u) w *
      (a • F + H) (glue B w (restrictTo Bᶜ u)) ∂haarPi ↥B) =
    a * (∫ w, isotypicKernel l (restrictTo B u) w *
      F (glue B w (restrictTo Bᶜ u)) ∂haarPi ↥B) +
    ∫ w, isotypicKernel l (restrictTo B u) w *
      H (glue B w (restrictTo Bᶜ u)) ∂haarPi ↥B
  rw [hfun, integral_add ((integrable_isotypicIntegrand B l F u).const_mul a)
    (integrable_isotypicIntegrand B l H u), integral_const_mul]
omit [Finite J] in
theorem mulPullback_smul_add (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) (a : ℂ) (F H : C(J → specialUnitary, ℂ)) :
    mulPullback B f hf (a • F + H) =
      a • mulPullback B f hf F + mulPullback B f hf H := by
  simp only [mulPullback, mul_add, mul_smul_comm]
theorem hatSeriesTerm_smul_add (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) (a : ℂ) (F H : C(J → specialUnitary, ℂ))
    (p : (↥B → HalfNatural) × (↥B → HalfNatural)) :
    hatSeriesTerm β B f hf (a • F + H) p =
      a • hatSeriesTerm β B f hf F p + hatSeriesTerm β B f hf H p := by
  simp only [hatSeriesTerm, hatSummand, partIsotypicProjC_smul_add, mulPullback_smul_add,
    smul_add]
  rw [smul_comm]
theorem summable_hatSeriesTerm (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) (F : C(J → specialUnitary, ℂ))
    (h : F ∈ hatSummableSet β B f hf) : Summable (hatSeriesTerm β B f hf F) := by
  have hfin : ∑' p, ‖hatSeriesTerm β B f hf F p‖ₑ < ⊤ := by
    have : ∀ p, ‖hatSeriesTerm β B f hf F p‖ₑ =
        ‖charCoeffRatio β p.1 p.2‖ₑ * ‖hatSummand B f hf F p.1 p.2‖ₑ := fun p => enorm_smul _ _
    simp only [this]
    exact h
  refine Summable.of_nnnorm (ENNReal.tsum_coe_ne_top_iff_summable.1 ?_)
  simpa only [enorm_eq_nnnorm] using hfin.ne
theorem hatSum_eq_tsum (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) (F : C(J → specialUnitary, ℂ)) :
    hatSum β B f hf F = ∑' p, hatSeriesTerm β B f hf F p := rfl
theorem charCoeffProd_im (β : ℝ) (hc : ∀ l, (weightCharCoeff β l).im = 0) {K : Type}
    [Finite K] (l : K → HalfNatural) : (charCoeffProd β l).im = 0 := by
  unfold charCoeffProd
  refine finprod_induction (p := fun x : ℂ => x.im = 0) (by simp) ?_ fun b => hc (l b)
  intro x y hx hy
  simp [Complex.mul_im, hx, hy]
theorem charCoeffRatio_im (β : ℝ) (hc : ∀ l, (weightCharCoeff β l).im = 0) {K : Type}
    [Finite K] (l l' : K → HalfNatural) : (charCoeffRatio β l l').im = 0 := by
  simp [charCoeffRatio, Complex.div_im, charCoeffProd_im β hc l, charCoeffProd_im β hc l']
theorem partIsotypicProjC_im (B : Set J) (l : ↥B → HalfNatural)
    (hk : ∀ u u' : ↥B → specialUnitary, (isotypicKernel l u u').im = 0)
    (G : C(J → specialUnitary, ℂ)) (hG : ∀ u, (G u).im = 0) (u : J → specialUnitary) :
    (partIsotypicProjC B l G u).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  change (starRingEnd ℂ) (∫ w, isotypicKernel l (restrictTo B u) w *
      G (glue B w (restrictTo Bᶜ u)) ∂haarPi ↥B) =
    ∫ w, isotypicKernel l (restrictTo B u) w *
      G (glue B w (restrictTo Bᶜ u)) ∂haarPi ↥B
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  change (starRingEnd ℂ) (isotypicKernel l (restrictTo B u) w *
      G (glue B w (restrictTo Bᶜ u))) =
    isotypicKernel l (restrictTo B u) w * G (glue B w (restrictTo Bᶜ u))
  rw [map_mul, Complex.conj_eq_iff_im.2 (hk _ _), Complex.conj_eq_iff_im.2 (hG _)]
omit [Finite J] in
theorem mulPullback_im (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) (G : C(J → specialUnitary, ℂ)) (hG : ∀ u, (G u).im = 0)
    (u : J → specialUnitary) : (mulPullback B f hf G u).im = 0 := by
  change (pullFromPart B f u * G u).im = 0
  simp [Complex.mul_im, pullFromPart, hf.2, hG u]
theorem hatSum_im (β : ℝ) (hc : ∀ l, (weightCharCoeff β l).im = 0) (B : Set J)
    (f : (↥B → specialUnitary) → ℂ) (hf : IsRealEntryPolynomial f)
    (hk : ∀ (l : ↥B → HalfNatural) (u u' : ↥B → specialUnitary), (isotypicKernel l u u').im = 0)
    (F : C(J → specialUnitary, ℂ)) (h : F ∈ hatSummableSet β B f hf) (hF : ∀ u, (F u).im = 0)
    (u : J → specialUnitary) : (hatSum β B f hf F u).im = 0 := by
  have hs : HasSum (hatSeriesTerm β B f hf F) (hatSum β B f hf F) :=
    (summable_hatSeriesTerm β B f hf F h).hasSum
  have hu : HasSum (fun p => hatSeriesTerm β B f hf F p u) (hatSum β B f hf F u) :=
    ContinuousMap.hasSum_apply hs u
  have him := Complex.imCLM.hasSum hu
  have hzero : (fun p => Complex.imCLM (hatSeriesTerm β B f hf F p u)) = fun _ => 0 := by
    funext p
    have hterm : (hatSummand B f hf F p.1 p.2 u).im = 0 :=
      partIsotypicProjC_im B p.2 (hk p.2) _
        (mulPullback_im B f hf _ (partIsotypicProjC_im B p.1 (hk p.1) F hF)) u
    change ((charCoeffRatio β p.1 p.2 • hatSummand B f hf F p.1 p.2) u).im = 0
    simp [Complex.mul_im, charCoeffRatio_im β hc p.1 p.2, hterm]
  rw [hzero] at him
  exact him.unique hasSum_zero
theorem holds (hS : HatSeriesConvergesStatement)
    (hP : PolynomialDegrees.Statement)
    (hK : PeterWeylOrthonormalAndKernel)
    (hC : BondWeightCharCoeffStatement) : HatLinearRealStatement := by
  intro J _ _ β B f hf hβ hB
  have : Nonempty ↥B := hB.to_subtype
  obtain ⟨D, hD⟩ := (hP ↥B f hf.1).2
  have hdom : ∀ F : C(J → specialUnitary, ℂ), (F : (J → specialUnitary) → ℂ) ∈ smoothSet →
      F ∈ hatSummableSet β B f hf := by
    intro F hF
    obtain ⟨-, -, -, -, -, -, h, -⟩ := hS J β B f hf D hβ hB hD F hF
    exact h
  have hc : ∀ l, (weightCharCoeff β l).im = 0 := by
    intro l
    rw [((hC.2 β hβ).2.1 l).1]
    exact Complex.ofReal_im _
  have hk : ∀ (l : ↥B → HalfNatural) (u u' : ↥B → specialUnitary),
      (isotypicKernel l u u').im = 0 :=
    fun l u u' => ((hK ↥B l).2.2.2.2 u u').1
  refine ⟨fun a F H hFs hHs => ?_, fun F hFs hFr u => hatSum_im β hc B f hf hk F (hdom F hFs) hFr u⟩
  have sF := summable_hatSeriesTerm β B f hf F (hdom F hFs)
  have sH := summable_hatSeriesTerm β B f hf H (hdom H hHs)
  rw [hatSum_eq_tsum, hatSum_eq_tsum, hatSum_eq_tsum]
  simp only [hatSeriesTerm_smul_add]
  rw [(sF.const_smul a).tsum_add sH, sF.tsum_const_smul a]
end YangMills.Construction.SpinHarmonics.HatLinearReal
end
