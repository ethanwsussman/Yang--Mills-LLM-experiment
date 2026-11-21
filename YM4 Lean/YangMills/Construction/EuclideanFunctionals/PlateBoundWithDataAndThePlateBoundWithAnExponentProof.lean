import YangMills.Construction.EuclideanFunctionals.InvarianceOfTheMomentsAndReductionToTheTimePlane
import YangMills.Construction.EuclideanFunctionals.PlateBoundFromTheInsertionBoundWithData
import YangMills.Construction.EuclideanFunctionals.PlateBoundWithDataAndThePlateBoundWithAnExponent
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RealPlane
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ProductBoundExponent
variable {m : SharpScale} {S : ConnFamily}
theorem productBoundWith_mono_const (σ : EuclidFunctionalWithRecon m S) {p c : ℝ}
    (hp : 0 < p) (hc : c ∈ productBoundFractions) {φ : RealPlane → ℝ} {K K' : ℝ} (hKK : K ≤ K')
    (h : ProductBoundWith σ hp hc φ K) : ProductBoundWith σ hp hc φ K' := by
  intro t ht α hα hsupp F hF A hA
  refine (h t ht α hα hsupp F hF A hA).trans ?_
  have hpow : 0 ≤ t ^ (-p) := Real.rpow_nonneg ht.1.le _
  have hα0 : 0 ≤ profileL1Norm α := MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  have hF0 : 0 ≤ heightNorm σ (t / 4) F := norm_nonneg _
  have hA0 : 0 ≤ heightNorm σ (t / 4) A := norm_nonneg _
  gcongr
theorem exponentIffConstants_holds (σ : EuclidFunctionalWithRecon m S) {c : ℝ}
    (hc : c ∈ productBoundFractions) : ExponentIffConstants σ hc := by
  classical
  intro p hp
  constructor
  · intro h
    refine ⟨fun φ => if hφ : φ ∈ realLabels then max (h φ hφ).choose 0 else 0,
      ⟨hp, fun φ hφ => ?_, hc.1, hc.2, ?_⟩⟩
    · simp only [dif_pos hφ]
      exact le_max_right _ _
    · intro t h0 h1 φ hφ α hα hsupp F hF A hA
      simp only [dif_pos hφ]
      exact productBoundWith_mono_const σ hp hc (le_max_left _ _) (h φ hφ).choose_spec
        t ⟨h0, h1⟩ α hα hsupp F hF A hA
  · rintro ⟨K, hK⟩ φ hφ
    exact ⟨K φ, fun t ht α hα hsupp F hF A hA => hK.le_bound t ht.1 ht.2 φ hφ α hα hsupp F hF A hA⟩
theorem fractionMonotone_holds (σ : EuclidFunctionalWithRecon m S) :
    FractionMonotone σ := by
  intro p hp K hK c c' hc' hcc hc h
  refine ⟨hp, hK, hc', hcc.trans_lt hc, ?_⟩
  intro t h0 h1 φ hφ α hα hsupp F hF A hA
  refine h.le_bound t h0 h1 φ hφ α hα (hsupp.trans fun y hy => ?_) F hF A hA
  exact lt_of_lt_of_le hy (mul_le_mul_of_nonneg_right hcc h0.le)
theorem productBoundParams_of_insertion (σ : EuclidFunctionalWithRecon m S) {c : ℝ}
    (hc : c ∈ productBoundFractions) (hc8 : c < 1 / 8) {p K cI : ℝ}
    (hI : InsertionBoundHolds σ p K cI) :
    ProductBoundParams p K cI c (parametrixFrac cI c) (cauchyFrac c) := by
  have hpos : 0 < parametrixFrac cI c :=
    lt_min (by linarith [hI.pos_fraction]) (by linarith)
  have hle₁ : parametrixFrac cI c ≤ 1 / 2 * cI := min_le_left _ _
  have hle₂ : parametrixFrac cI c ≤ 1 / 8 - c := min_le_right _ _
  refine ⟨hI.nonneg_exponent, hI.nonneg_constant, hI.pos_fraction, hI.fraction_lt_eighth, hc.1, hpos, ?_,
    hle₁, by linarith, ?_⟩
  · unfold cauchyFrac
    linarith
  · unfold cauchyFrac
    linarith
theorem productBoundWith_labelConst (hProd : ProductBoundFromInsertion.Main)
    (σ : EuclidFunctionalWithRecon m S) {c : ℝ} (hc : c ∈ productBoundFractions)
    (hc8 : c < 1 / 8) (hcone : σ.ConeCondition) {p K cI : ℝ}
    (hI : InsertionBoundHolds σ p K cI) {φ : RealPlane → ℝ} (hφ : φ ∈ realLabels) :
    ProductBoundWith σ (productExponent_pos hI) hc φ (labelConst m p K cI c φ) := by
  intro t ht α hα hsupp F hF A hA
  exact (hProd m S σ p K cI c _ _ hcone hI (productBoundParams_of_insertion σ hc hc8 hI)).2.le_bound
    t ht.1 ht.2 φ hφ α hα hsupp F hF A hA
theorem main_holds (hProd : ProductBoundFromInsertion.Main)
    (hRed : MomentSymmetry.ReductionHolds) : Main := by
  intro m S σ
  refine ⟨fun c hc => exponentIffConstants_holds σ hc, fractionMonotone_holds σ, ?_⟩
  intro c hc hc8 hcone p K cI hI
  have hwith : ∀ φ ∈ realLabels,
      ProductBoundWith σ (productExponent_pos hI) hc φ (labelConst m p K cI c φ) :=
    fun φ hφ => productBoundWith_labelConst hProd σ hc hc8 hcone hI hφ
  have hbound : ProductBoundWithExponent σ (productExponent_pos hI) hc :=
    fun φ hφ => ⟨_, hwith φ hφ⟩
  refine ⟨⟨productBoundParams_of_insertion σ hc hc8 hI, hbound, hwith⟩, fun w => ?_⟩
  have hr := (hRed m S σ).2.2.1 w _ c (productExponent_pos hI) hc
  exact ⟨hr.2.2.2 hbound, fun φ hφ => (hr.2.1 φ hφ _).2 (hwith φ hφ)⟩
end YangMills.Construction.EuclideanFunctionals.ProductBoundExponent
