import YangMills.Construction.Matrices.ProjectionsCommuteWithTwoSidedTranslationsProof
import YangMills.Construction.Matrices.TensorOperatorOfAnIntegralOperatorProof
import YangMills.Construction.TransferOperators.SquareRootOfTheBondKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Matrices Matrices.ComplexMatrix2 TransferOperators
open scoped ENNReal
namespace SpinHarmonics
section
variable {J : Type} [Finite J]
def sobolevDecay (q : ℕ) (F : HaarL2 J) : ℝ≥0∞ :=
  ⨆ l : J → HalfNatural, ENNReal.ofReal ((1 + weightSum l) ^ q * ‖isotypicProj l F‖)
def degreeTotal {B : Type} (D : B → ℕ) : ℕ := ∑ᶠ b, D b
def IsDegreeCompatible {B : Type} (D : B → ℕ) (l l' : B → HalfNatural) : Prop :=
  ∀ b, |(l' b).toReal - (l b).toReal| ≤ (D b : ℝ) / 2
omit [Finite J] in
theorem continuous_restrictTo (B : Set J) :
    Continuous (restrictTo B : (J → specialUnitary) → ↥B → specialUnitary) :=
  continuous_pi fun _ => continuous_apply _
omit [Finite J] in
theorem continuous_glue (B : Set J) :
    Continuous fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2 := by apply _root_.YangMills.Construction.SpinHarmonics.TensorOneKernelOpProof.continuous_glue <;> assumption
theorem continuous_isotypicKernel {K : Type} [Finite K] (l : K → HalfNatural) :
    Continuous fun p : (K → specialUnitary) × (K → specialUnitary) => isotypicKernel l p.1 p.2 := by apply _root_.YangMills.Construction.SpinHarmonics.BiTranslation.continuous_isotypicKernel <;> assumption
theorem continuous_partKernelIntegrand (B : Set J) (l : ↥B → HalfNatural)
    (F : C(J → specialUnitary, ℂ)) :
    Continuous fun p : (J → specialUnitary) × (↥B → specialUnitary) =>
      isotypicKernel l (restrictTo B p.1) p.2 * F (glue B p.2 (restrictTo Bᶜ p.1)) := by
  have h₁ : Continuous fun p : (J → specialUnitary) × (↥B → specialUnitary) =>
      (restrictTo B p.1, p.2) :=
    ((continuous_restrictTo B).comp continuous_fst).prodMk continuous_snd
  have h₂ : Continuous fun p : (J → specialUnitary) × (↥B → specialUnitary) =>
      (p.2, restrictTo Bᶜ p.1) :=
    continuous_snd.prodMk ((continuous_restrictTo Bᶜ).comp continuous_fst)
  have h₃ : Continuous fun p : (J → specialUnitary) × (↥B → specialUnitary) =>
      glue B p.2 (restrictTo Bᶜ p.1) :=
    Continuous.comp (g := fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2)
      (continuous_glue B) h₂
  have h₄ : Continuous fun p : (J → specialUnitary) × (↥B → specialUnitary) =>
      isotypicKernel l (restrictTo B p.1) p.2 := by
    have h := (continuous_isotypicKernel l).comp h₁
    exact h
  exact h₄.mul (F.continuous.comp h₃)
theorem continuous_partKernelIntegral (B : Set J) (l : ↥B → HalfNatural)
    (F : C(J → specialUnitary, ℂ)) :
    Continuous fun u : J → specialUnitary => ∫ w, isotypicKernel l (restrictTo B u) w *
      F (glue B w (restrictTo Bᶜ u)) ∂haarPi ↥B := by
  have h := continuous_parametric_integral_of_continuous (μ := haarPi ↥B)
    (f := fun (u : J → specialUnitary) (w : ↥B → specialUnitary) =>
      isotypicKernel l (restrictTo B u) w * F (glue B w (restrictTo Bᶜ u))) (s := Set.univ)
    (continuous_partKernelIntegrand B l F) isCompact_univ
  simpa only [Measure.restrict_univ] using h
def partIsotypicProjC (B : Set J) (l : ↥B → HalfNatural) (F : C(J → specialUnitary, ℂ)) :
    C(J → specialUnitary, ℂ) :=
  ⟨fun u => ∫ w, isotypicKernel l (restrictTo B u) w *
    F (glue B w (restrictTo Bᶜ u)) ∂haarPi ↥B, continuous_partKernelIntegral B l F⟩
theorem continuous_entryEval {K : Type} : Continuous (entryEval : (K → specialUnitary) → _ → ℂ) := by
  refine continuous_pi fun x => ?_
  have he : ∀ (b : K) (i j : Fin 2), Continuous fun u : K → specialUnitary =>
      (u b : ComplexMatrix2) i j := fun b i j =>
    Continuous.matrix_elem (A := fun u : K → specialUnitary => (u b : ComplexMatrix2))
      (continuous_subtype_val.comp (continuous_apply b)) i j
  rcases x with ⟨b, i, j⟩ | ⟨b, i, j⟩
  · exact he b i j
  · exact continuous_star.comp (he b i j)
theorem IsEntryPolynomial.continuous {K : Type} {f : (K → specialUnitary) → ℂ}
    (hf : IsEntryPolynomial f) : Continuous f := by
  obtain ⟨p, hp⟩ := hf
  rw [show f = fun u => MvPolynomial.eval (entryEval u) p from funext hp]
  exact (MvPolynomial.continuous_eval p).comp continuous_entryEval
def mulPullback (B : Set J) (f : (↥B → specialUnitary) → ℂ) (hf : IsRealEntryPolynomial f)
    (F : C(J → specialUnitary, ℂ)) : C(J → specialUnitary, ℂ) :=
  (⟨pullFromPart B f, hf.1.continuous.comp (continuous_restrictTo B)⟩ :
    C(J → specialUnitary, ℂ)) * F
def hatSummand (B : Set J) (f : (↥B → specialUnitary) → ℂ) (hf : IsRealEntryPolynomial f)
    (F : C(J → specialUnitary, ℂ)) (l l' : ↥B → HalfNatural) : C(J → specialUnitary, ℂ) :=
  partIsotypicProjC B l' (mulPullback B f hf (partIsotypicProjC B l F))
def charCoeffRatio (β : ℝ) {B : Type} [Finite B] (l l' : B → HalfNatural) : ℂ :=
  charCoeffProd β l / charCoeffProd β l'
def HatSummable (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ) (hf : IsRealEntryPolynomial f)
    (F : C(J → specialUnitary, ℂ)) : Prop :=
  ∑' p : (↥B → HalfNatural) × (↥B → HalfNatural),
    ‖charCoeffRatio β p.1 p.2‖ₑ * ‖hatSummand B f hf F p.1 p.2‖ₑ < ∞
def hatSum (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ) (hf : IsRealEntryPolynomial f)
    (F : C(J → specialUnitary, ℂ)) : C(J → specialUnitary, ℂ) :=
  ∑' p : (↥B → HalfNatural) × (↥B → HalfNatural),
    charCoeffRatio β p.1 p.2 • hatSummand B f hf F p.1 p.2
def hatSummableSet (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) : Set C(J → specialUnitary, ℂ) :=
  {F | HatSummable β B f hf F}
def hatMap (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ) (hf : IsRealEntryPolynomial f) :
    hatSummableSet β B f hf → C(J → specialUnitary, ℂ) :=
  fun F => hatSum β B f hf F
def permuteArgs {A : Type*} (σ : Equiv.Perm J) (H : (J → specialUnitary) → A)
    (u : J → specialUnitary) : A :=
  H fun b => u (σ b)
end
end SpinHarmonics
end YangMills.Construction
end
