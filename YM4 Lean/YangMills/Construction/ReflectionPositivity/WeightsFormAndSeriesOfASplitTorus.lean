import YangMills.Construction.ReflectionPositivity.HalvesOfASplitTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open SpinHarmonics
namespace InfiniteLattice.PeriodSublattice
variable (Γ : PeriodSublattice 1)
def numSplitPlaquettes (e : AmbientSpace) (h : ℤ) (c : ℝ) : ℕ :=
  Nat.card {q : Γ.QuotientPlaquette // Γ.IsSplitPlaquette e h c q}
def splitFaceWeight (β : ℝ) (e : AmbientSpace) (h : ℤ) (c : ℝ) (U : Γ.QuotientField) : ℝ :=
  Real.exp (-β * ∑ᶠ (q : Γ.QuotientPlaquette) (_ : Γ.IsSplitPlaquette e h c q),
    Γ.quotientFaceEnergy U q)
def integrateOut (S : Set Γ.QuotientLink) (f : Γ.QuotientField → ℂ)
    (U : Γ.QuotientField) : ℂ :=
  ∫ V, f (SpinHarmonics.glue S V (SpinHarmonics.restrictTo Sᶜ U)) ∂Matrices.ComplexMatrix2.haarPi ↥S
def reflectionPairing (β : ℝ) (P : NormalFamilies.NormalLevelPair 1)
    (G F : Γ.QuotientField → ℂ) : ℂ :=
  ∫ U, Γ.conjReflect P G U * F U * (Γ.boltzmannWeight β U : ℂ) ∂Γ.quotientHaar
def perturbedReflWeight (β : ℝ) (P : NormalFamilies.NormalLevelPair 1)
    (E : Γ.QuotientField → ℝ) (U : Γ.QuotientField) : ℝ :=
  Real.exp (E U + Γ.compPullback P.reflectSymmetry E U) * Γ.boltzmannWeight β U
def perturbedReflMeasure (β : ℝ) (P : NormalFamilies.NormalLevelPair 1)
    (E : Γ.QuotientField → ℝ) : Measure Γ.QuotientField :=
  (ENNReal.ofReal (∫ U, Γ.perturbedReflWeight β P E U ∂Γ.quotientHaar))⁻¹ •
    Γ.quotientHaar.withDensity fun U => ENNReal.ofReal (Γ.perturbedReflWeight β P E U)
def HasReflectionSeries (h : ℤ) (P : NormalFamilies.NormalLevelPair 1) (K : Γ.QuotientField → ℂ)
    (a : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (α : ι → ℝ) (H : ι → Γ.QuotientField → ℂ),
    (∀ i, 0 ≤ α i) ∧
    HasSum α a ∧
    (∀ i, H i ∈ Γ.plusAlgebra P.normal h P.level) ∧
    (∀ i, PeriodSublattice.supNorm (H i) ≤ 1) ∧
    (∀ U, Summable fun i => ‖(α i : ℂ) * H i U * Γ.conjReflect P (H i) U‖) ∧
    TendstoUniformly
      (fun (s : Finset ι) U => ∑ i ∈ s, (α i : ℂ) * H i U * Γ.conjReflect P (H i) U)
      K Filter.atTop
end InfiniteLattice.PeriodSublattice
end YangMills.Construction
