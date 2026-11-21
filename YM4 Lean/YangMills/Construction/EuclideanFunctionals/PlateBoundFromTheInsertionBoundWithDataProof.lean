import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.EuclideanFunctionals.BoundsAndContinuityOfTheMomentsProof
import YangMills.Construction.EuclideanFunctionals.BracketOfTheParametrix
import YangMills.Construction.EuclideanFunctionals.ExpansionTranslationsContinuityAndSmearingOfTheInsertionValue
import YangMills.Construction.EuclideanFunctionals.MollificationWithinACompactSet
import YangMills.Construction.EuclideanFunctionals.PlateBoundFromTheInsertionBoundWithData
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror YangMills.Construction.RealPlane
open Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ProductBoundFromInsertionProof
open ParametrixBracket InsertionForm ProductBoundFromInsertion
variable {m : SharpScale} {S : ConnFamily} {σ : EuclidFunctionalWithRecon m S}
theorem supp_eq_tsupport {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) : supp f = tsupport f :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
theorem mem_C1c_iff_contDiff {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) :
    f ∈ C1c 𝕜 ↔ ContDiff ℝ 1 f ∧ HasCompactSupport f := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.mem_C1c_iff_contDiff <;> assumption
theorem heightNorm_nonneg (c : ℝ) (G : FreeSep) : 0 ≤ heightNorm σ c G :=
  norm_nonneg _
theorem uniformNorm_nonneg {X E : Type*} [NormedAddCommGroup E] (f : X → E) :
    0 ≤ TestFunctions.uniformNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem productConst_nonneg {p C cI cS cPar cCau : ℝ}
    (hpar : ProductBoundParams p C cI cS cPar cCau) :
    0 ≤ productConst m p C cPar cCau := by
  have hP := hpar.cPar_pos
  have h1 : 0 ≤ productAbsConst cPar cCau := by
    unfold productAbsConst
    have : 0 ≤ (cPar ^ 5)⁻¹ := by positivity
    exact mul_nonneg (by norm_num) (this.trans (le_max_right _ _))
  have h2 : 0 ≤ laplacianCubedConst := by
    unfold laplacianCubedConst
    exact Finset.sum_nonneg fun γ _ => by positivity
  have hM : 0 ≤ m.M := by linarith [m.one_le]
  have hC := hpar.constant_nonneg
  have h3 := uniformNorm_nonneg EuclideanAnalysis.CubedLaplacian.parametrixOne
  have h4 : 0 ≤ EuclideanAnalysis.gradUniformNorm EuclideanAnalysis.CubedLaplacian.parametrixOne :=
    Real.iSup_nonneg fun _ => by simp only [Real.norm_eq_abs]; exact abs_nonneg _
  have h5 := uniformNorm_nonneg EuclideanAnalysis.CubedLaplacian.remainderDensityOne
  have h6 : 0 ≤ EuclideanAnalysis.gradUniformNorm EuclideanAnalysis.CubedLaplacian.remainderDensityOne :=
    Real.iSup_nonneg fun _ => by simp only [Real.norm_eq_abs]; exact abs_nonneg _
  unfold productConst
  positivity
theorem isOpen_timeSlab_mul (c η : ℝ) : IsOpen (thinSlab c η) :=
  isOpen_lt (continuous_apply 3).abs continuous_const
theorem timeSlab_mul_subset {c η : ℝ} (hc : c < 1 / 8) (hη : 0 < η) :
    thinSlab c η ⊆ timeSlab (η / 4) := fun x hx => by
  have h1 : |x 3| < c * η := hx
  have h2 : c * η ≤ 1 / 8 * η := by nlinarith
  show |x 3| < η / 4
  linarith
theorem norm_insertion_le_of_smooth (hBr : ParametrixBracket.Main)
    {p C cI cS cPar cCau : ℝ} (hcone : σ.ConeCondition) (hins : InsertionBoundHolds σ p C cI)
    (hpar : ProductBoundParams p C cI cS cPar cCau) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {F A : FreeSep} (hF : F ∈ finCombIn {y | η / 4 < y 3})
    (hA : A ∈ finCombIn {y | η / 4 < y 3}) {g : R4 → ℝ}
    (hg : g ∈ smoothCompactSupp R4 ℝ) (hgs : supp g ⊆ thinSlab cS η) :
    ‖insertion S F (fun y => (g y : ℂ)) A‖ ≤
      1 / 2 * productConst m p C cPar cCau * η ^ (-productExponent p) *
        heightNorm σ (η / 4) F * heightNorm σ (η / 4) A * l1Norm g := by
  obtain ⟨-, -, -, -, hrep, hbd⟩ :=
    hBr m S σ p C cI cS cPar cCau hcone hins hpar η hη hη1 F hF A hA
  have hR := hrep g hg hgs
  set B : ℝ := 1 / 2 * productConst m p C cPar cCau *
    η ^ (-productExponent p) * heightNorm σ (η / 4) F * heightNorm σ (η / 4) A with hB
  have hB0 : 0 ≤ B := by
    have h1 := productConst_nonneg (m := m) hpar
    have h3 := heightNorm_nonneg (σ := σ) (η / 4) F
    have h4 := heightNorm_nonneg (σ := σ) (η / 4) A
    positivity
  have hint : Integrable fun x => B * ‖g x‖ :=
    ((hg.1.continuous.integrable_of_hasCompactSupport hg.2).norm).const_mul B
  rw [hR.eq_sum, hR.sum_eq]
  refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun x => ?_)).trans_eq ?_
  · unfold weightedIntegrand
    by_cases hx : x ∈ supp g
    · rw [Set.indicator_of_mem hx, norm_mul, Complex.norm_real, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have hb := (hbd x (hgs hx)).sum_le
      exact (norm_add_le _ _).trans hb
    · rw [Set.indicator_of_notMem hx, norm_zero]
      positivity
  · rw [integral_const_mul]
    rfl
theorem boundedByL1OnSlab_of_bracket (hMoll : MollificationInCompact)
    (hForm : InsertionForm.InsertionFormTheorem)
    (hBr : ParametrixBracket.Main)
    {p C cI cS cPar cCau : ℝ} (hcone : σ.ConeCondition) (hins : InsertionBoundHolds σ p C cI)
    (hpar : ProductBoundParams p C cI cS cPar cCau) :
    BoundedByL1OnSlab σ p C cS cPar cCau := by
  intro η hη hη1 h hh hsupp F hF A hA
  have hηq : 0 < η / 4 := by positivity
  have hcm : (fun y => (h y : ℂ)) ∈ C1c ℂ := by
    rw [mem_C1c_iff_contDiff] at hh ⊢
    exact ⟨Complex.ofRealCLM.contDiff.comp hh.1, hh.2.comp_left Complex.ofReal_zero⟩
  have hcs : supp (fun y => (h y : ℂ)) ⊆ thinSlab cS η := by
    rw [supp_eq_tsupport]
    have : tsupport (fun y => (h y : ℂ)) = tsupport h := by
      simp [tsupport, Function.support]
    rw [this]
    exact hsupp
  obtain ⟨Q, hQ, hQO, hcQ, hs, hprops, hconv, hreal⟩ :=
    hMoll _ (isOpen_timeSlab_mul cS η) _ hcm hcs
  have hreal' := hreal fun x => Complex.ofReal_im _
  obtain ⟨-, -, -, -, hcont, -⟩ := hForm m S σ (η / 4) hηq F hF A hA
  have hQs : Q ⊆ timeSlab (η / 4) := hQO.trans (timeSlab_mul_subset hpar.cS_lt_eighth hη)
  have hsm : ∀ j, 1 ≤ j → hs j ∈ C1c ℂ ∧ supp (hs j) ⊆ Q := fun j hj => by
    obtain ⟨h1, h2, -⟩ := hprops j hj
    exact ⟨(mem_C1c_iff_contDiff _).2 ⟨h1.1.of_le (by exact_mod_cast le_top), h1.2⟩, h2⟩
  have hlim := hcont Q hQ hQs hs _ hsm hcm hcQ hconv
  have hnorm : l1Norm (fun y => (h y : ℂ)) = l1Norm h := by
    simp [l1Norm]
  set B : ℝ := 1 / 2 * productConst m p C cPar cCau *
    η ^ (-productExponent p) * heightNorm σ (η / 4) F * heightNorm σ (η / 4) A with hB
  have hB0 : 0 ≤ B := by
    have h1 := productConst_nonneg (m := m) hpar
    have h2 : 0 ≤ η ^ (-productExponent p) := Real.rpow_nonneg hη.le _
    have h3 := heightNorm_nonneg (σ := σ) (η / 4) F
    have h4 := heightNorm_nonneg (σ := σ) (η / 4) A
    positivity
  have hbound : ∀ j, 1 ≤ j → ‖insertion S F (hs j) A‖ ≤ B * l1Norm h := fun j hj => by
    obtain ⟨h1, h2, h3⟩ := hprops j hj
    have hgc : (fun y => (((hs j y).re : ℝ) : ℂ)) = hs j :=
      funext fun x => Complex.ext rfl (by simp [hreal' j hj x])
    have hgm : (fun x => (hs j x).re) ∈ smoothCompactSupp R4 ℝ :=
      ⟨Complex.reCLM.contDiff.comp h1.1, h1.2.comp_left Complex.zero_re⟩
    have hgt : tsupport (fun x => (hs j x).re) ⊆ tsupport (hs j) :=
      closure_mono fun x hx h0 => hx (by simp [h0])
    have hgs : supp (fun x => (hs j x).re) ⊆ thinSlab cS η := by
      rw [supp_eq_tsupport]
      exact hgt.trans ((supp_eq_tsupport (hs j)).symm.subset.trans (h2.trans hQO))
    have hv := norm_insertion_le_of_smooth hBr hcone hins hpar hη hη1 hF hA hgm hgs
    rw [hgc] at hv
    have hle : l1Norm (fun x => (hs j x).re) ≤ l1Norm h := by
      rw [← hnorm]
      refine le_trans (le_of_eq ?_) h3
      unfold l1Norm
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have hx : (((hs j x).re : ℝ) : ℂ) = hs j x := congrFun hgc x
      calc ‖(hs j x).re‖ = ‖(((hs j x).re : ℝ) : ℂ)‖ := (Complex.norm_real _).symm
        _ = ‖hs j x‖ := by rw [hx]
    exact hv.trans (mul_le_mul_of_nonneg_left hle hB0)
  have := le_of_tendsto hlim.norm (eventually_atTop.2 ⟨1, hbound⟩)
  calc _ ≤ B * l1Norm h := this
    _ = _ := by rw [hB]; ring
theorem norm_insertion_productFunction_le
    (hForm : InsertionForm.InsertionFormTheorem)
    (hRules : MotionMulRules.MotionMulTupleRules)
    {p C cI cS cPar cCau : ℝ} (hpar : ProductBoundParams p C cI cS cPar cCau)
    (ha : BoundedByL1OnSlab σ p C cS cPar cCau) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {φ : RealPlane → ℝ} (hφ : φ ∈ realLabels) {α : RealPlane → ℂ}
    (hα : α ∈ complexProfiles) (hsupp : tsupport α ⊆ planeStrip cS η) {F A : FreeSep}
    (hF : F ∈ finCombIn {y | η / 4 < y 3}) (hA : A ∈ finCombIn {y | η / 4 < y 3}) :
    ‖insertion S F (productFunction α φ) A‖ ≤
      productConst m p C cPar cCau * l1Norm φ *
        η ^ (-productExponent p) * profileL1Norm α *
        heightNorm σ (η / 4) F * heightNorm σ (η / 4) A := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hprod, -⟩ := hRules
  obtain ⟨hmem, hps, -, -, -, -, -, -, hnormP⟩ := hprod α hα φ hφ
  obtain ⟨-, ⟨-, hlin⟩, -⟩ := hForm m S σ (η / 4) (by positivity) F hF A hA
  have hmem' := (mem_C1c_iff_contDiff _).1 hmem
  have hts : tsupport (productFunction α φ) ⊆ thinSlab cS η := by
    rw [← supp_eq_tsupport]
    intro x hx
    have h1 : planeComponent x ∈ planeStrip cS η := hsupp (hps hx).1
    have h2 : |planeComponent x 0| < cS * η := h1
    show |x 3| < cS * η
    simpa [planeComponent] using h2
  have hintP : Integrable fun x => ‖productFunction α φ x‖ :=
    (hmem'.1.continuous.integrable_of_hasCompactSupport hmem'.2).norm
  have part : ∀ f : ℂ → ℝ, (∀ z, ‖f z‖ ≤ ‖z‖) → f 0 = 0 → ContDiff ℝ 1 f →
      (fun x => f (productFunction α φ x)) ∈ C1c ℝ ∧
      tsupport (fun x => f (productFunction α φ x)) ⊆ thinSlab cS η ∧
      l1Norm (fun x => f (productFunction α φ x)) ≤ profileL1Norm α * l1Norm φ := by
    intro f hf f0 hfc
    have hcd : ContDiff ℝ 1 fun x => f (productFunction α φ x) := hfc.comp hmem'.1
    have hcs : HasCompactSupport fun x => f (productFunction α φ x) := hmem'.2.comp_left f0
    refine ⟨(mem_C1c_iff_contDiff _).2 ⟨hcd, hcs⟩, ?_, ?_⟩
    · refine (show tsupport _ ⊆ tsupport (productFunction α φ) from
        closure_mono fun x hx h0 => hx ?_).trans hts
      simp [h0, f0]
    · have hle : l1Norm (fun x => f (productFunction α φ x)) ≤ ∫ x, ‖productFunction α φ x‖ :=
        integral_mono (hcd.continuous.integrable_of_hasCompactSupport hcs).norm hintP
          fun x => hf _
      rw [hnormP] at hle
      exact hle
  have hre : ∀ z : ℂ, ‖z.re‖ ≤ ‖z‖ := fun z => Complex.abs_re_le_norm z
  have him : ∀ z : ℂ, ‖z.im‖ ≤ ‖z‖ := fun z => Complex.abs_im_le_norm z
  obtain ⟨m₁, s₁, n₁⟩ := part (fun z => z.re) hre Complex.zero_re Complex.reCLM.contDiff
  obtain ⟨m₂, s₂, n₂⟩ := part (fun z => z.im) him Complex.zero_im Complex.imCLM.contDiff
  have v₁ := ha η hη hη1 _ m₁ s₁ F hF A hA
  have v₂ := ha η hη hη1 _ m₂ s₂ F hF A hA
  have cm : ∀ {g : R4 → ℝ}, g ∈ C1c ℝ →
      tsupport g ⊆ thinSlab cS η → IsSlabInsert (η / 4) fun y => (g y : ℂ) := by
    intro g hg hgs
    have hg' := (mem_C1c_iff_contDiff _).1 hg
    refine ⟨(mem_C1c_iff_contDiff _).2 ⟨Complex.ofRealCLM.contDiff.comp hg'.1,
      hg'.2.comp_left Complex.ofReal_zero⟩, ?_⟩
    rw [supp_eq_tsupport]
    have : tsupport (fun y => (g y : ℂ)) = tsupport g := by
      simp [tsupport, Function.support]
    rw [this]
    exact hgs.trans (timeSlab_mul_subset hpar.cS_lt_eighth hη)
  have hdecomp : productFunction α φ = (1 : ℂ) • (fun y => (((productFunction α φ y).re : ℝ) : ℂ)) +
      Complex.I • (fun y => (((productFunction α φ y).im : ℝ) : ℂ)) := by
    funext x
    simp [mul_comm Complex.I, Complex.re_add_im]
  have hval := (hlin 1 Complex.I _ _ (cm m₁ s₁) (cm m₂ s₂)).2
  rw [← hdecomp, one_mul] at hval
  rw [hval]
  set N := heightNorm σ (η / 4) F
  set N' := heightNorm σ (η / 4) A
  set K := productConst m p C cPar cCau
  set E := η ^ (-productExponent p)
  have hK : 0 ≤ K := productConst_nonneg hpar
  have hE : 0 ≤ E := Real.rpow_nonneg hη.le _
  have hN : 0 ≤ N := heightNorm_nonneg _ _
  have hN' : 0 ≤ N' := heightNorm_nonneg _ _
  have hW : 0 ≤ 1 / 2 * K * E := by positivity
  have w₁ : 1 / 2 * K * E * l1Norm (fun x => (productFunction α φ x).re) * N * N' ≤
      1 / 2 * K * E * (profileL1Norm α * l1Norm φ) * N * N' := by gcongr
  have w₂ : 1 / 2 * K * E * l1Norm (fun x => (productFunction α φ x).im) * N * N' ≤
      1 / 2 * K * E * (profileL1Norm α * l1Norm φ) * N * N' := by gcongr
  calc _ ≤ ‖insertion S F (fun y => (((productFunction α φ y).re : ℝ) : ℂ)) A‖ +
        ‖Complex.I * insertion S F (fun y => (((productFunction α φ y).im : ℝ) : ℂ)) A‖ :=
        norm_add_le _ _
    _ = ‖insertion S F (fun y => (((productFunction α φ y).re : ℝ) : ℂ)) A‖ +
        ‖insertion S F (fun y => (((productFunction α φ y).im : ℝ) : ℂ)) A‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ 1 / 2 * K * E * (profileL1Norm α * l1Norm φ) * N * N' +
        1 / 2 * K * E * (profileL1Norm α * l1Norm φ) * N * N' :=
        add_le_add (v₁.trans w₁) (v₂.trans w₂)
    _ = _ := by ring
theorem main (hMoll : MollificationInCompact)
    (hForm : InsertionForm.InsertionFormTheorem)
    (hBr : ParametrixBracket.Main)
    (hRules : MotionMulRules.MotionMulTupleRules) : ProductBoundFromInsertion.Main := by
  intro m S σ p C cI cS cPar cCau hcone hins hpar
  have ha := boundedByL1OnSlab_of_bracket hMoll hForm hBr hcone hins hpar
  refine ⟨ha, ?_, fun φ _ => ?_, hpar.cS_pos, hpar.cS_lt_quarter, ?_⟩
  · have := hpar.exponent_nonneg
    unfold productExponent
    linarith
  · exact mul_nonneg (productConst_nonneg hpar)
      (integral_nonneg fun _ => norm_nonneg _)
  · intro η hη hη1 φ hφ α hα hsupp F hF A hA
    exact norm_insertion_productFunction_le hForm hRules hpar ha hη hη1 hφ hα hsupp hF hA
end YangMills.Construction.EuclideanFunctionals.ProductBoundFromInsertionProof
