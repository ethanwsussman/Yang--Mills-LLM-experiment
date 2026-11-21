import YangMills.Construction.Matrices.EveryPolynomialOnPowersOfGHasFiniteDegrees
import YangMills.Construction.TransferOperators.HatAndFunctionsOfTheOtherVariables
import YangMills.Construction.TransferOperators.SeriesOfTheOperatorHatConverges
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SpinHarmonics.HatComplementMul
variable {J : Type} [Finite J]
omit [Finite J] in
theorem restrictTo_compl_glue (B : Set J) (v : ↥B → specialUnitary) (z : ↥Bᶜ → specialUnitary) :
    restrictTo Bᶜ (glue B v z) = z := by
  funext b
  exact glue_of_notMem B v z b
theorem partIsotypicProjC_pullFromComplement_mul (B : Set J) (s : ↥B → HalfNatural)
    (ω : C(↥Bᶜ → specialUnitary, ℂ)) (F : C(J → specialUnitary, ℂ)) :
    partIsotypicProjC B s (pullFromComplement B ω * F) =
      pullFromComplement B ω * partIsotypicProjC B s F := by
  ext u
  change ∫ w, isotypicKernel s (restrictTo B u) w *
      (ω (restrictTo Bᶜ (glue B w (restrictTo Bᶜ u))) *
        F (glue B w (restrictTo Bᶜ u))) ∂haarPi ↥B =
    ω (restrictTo Bᶜ u) * ∫ w, isotypicKernel s (restrictTo B u) w *
      F (glue B w (restrictTo Bᶜ u)) ∂haarPi ↥B
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [restrictTo_compl_glue]
  ring
theorem hatSummand_pullFromComplement_mul (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) (ω : C(↥Bᶜ → specialUnitary, ℂ))
    (F : C(J → specialUnitary, ℂ)) (s t : ↥B → HalfNatural) :
    hatSummand B f hf (pullFromComplement B ω * F) s t =
      pullFromComplement B ω * hatSummand B f hf F s t := by
  have hmul : ∀ H : C(J → specialUnitary, ℂ), mulPullback B f hf (pullFromComplement B ω * H) =
      pullFromComplement B ω * mulPullback B f hf H := fun H =>
    mul_left_comm _ _ _
  simp only [hatSummand, partIsotypicProjC_pullFromComplement_mul, hmul]
theorem summable_of_mem_hatSummableSet {β : ℝ} {B : Set J} {f : (↥B → specialUnitary) → ℂ}
    {hf : IsRealEntryPolynomial f} {F : C(J → specialUnitary, ℂ)}
    (hF : F ∈ hatSummableSet β B f hf) :
    Summable fun p : (↥B → HalfNatural) × (↥B → HalfNatural) =>
      charCoeffRatio β p.1 p.2 • hatSummand B f hf F p.1 p.2 := by
  have hfin : ∑' p : (↥B → HalfNatural) × (↥B → HalfNatural),
      ‖charCoeffRatio β p.1 p.2 • hatSummand B f hf F p.1 p.2‖ₑ ≠ ∞ := by
    simp only [enorm_smul]
    exact ne_of_lt hF
  refine Summable.of_norm ?_
  simpa only [toReal_enorm] using ENNReal.summable_toReal hfin
theorem statement_holds (series : HatSeriesConvergesStatement)
    (degrees : PolynomialDegrees.Statement) :
    HatComplementMulStatement := by
  intro J _ _ β B f hf hβ hB ω F _ hF
  have : Nonempty ↥B := hB.to_subtype
  obtain ⟨-, D, hD⟩ := degrees ↥B f hf.1
  have hdom : F ∈ hatSummableSet β B f hf :=
    (series J β B f hf D hβ hB hD F hF).2.2.2.2.2.2.1
  have hsum := summable_of_mem_hatSummableSet hdom
  have hterm : ∀ p : (↥B → HalfNatural) × (↥B → HalfNatural),
      charCoeffRatio β p.1 p.2 • hatSummand B f hf (pullFromComplement B ω * F) p.1 p.2 =
        pullFromComplement B ω * (charCoeffRatio β p.1 p.2 • hatSummand B f hf F p.1 p.2) := by
    intro p
    rw [hatSummand_pullFromComplement_mul, mul_smul_comm]
  simp only [hatSum, hterm]
  exact hsum.tsum_mul_left _
end YangMills.Construction.SpinHarmonics.HatComplementMul
end
