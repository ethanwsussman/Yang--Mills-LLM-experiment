import YangMills.Construction.ReflectionPositivity.SpectralVariablesAsASpaceAndTheMomentumTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.ReflectionPositivity.EnergyMomentum
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
def energyMomentumMonomial (μ : Fin 4) (n : ℕ) (w : orthLattice μ) (x : SpectralSpace μ) : ℂ :=
  (expNegNatMulEnergy n x.energy : ℂ) *
    Complex.exp (Complex.I * (angleDot μ x.momentum (w : Fin 4 → ℤ) : ℂ))
def energyMomentumPolys (μ : Fin 4) : Submodule ℂ (SpectralSpace μ → ℂ) :=
  Submodule.span ℂ (range fun a : ℕ × orthLattice μ => energyMomentumMonomial μ a.1 a.2)
def ReflectionPair.IsSpectralMeasure (p : ReflectionPair) (ν : unitPositiveClass) (μ : Fin 4)
    (ψ : p.Hilb ν μ) (σ : Measure (SpectralSpace μ)) : Prop :=
  IsFiniteMeasure σ ∧ ∀ (n : ℕ) (w : orthLattice μ),
    inner ℂ ψ ((p.transferOp ν μ ^ n * p.shiftMonomial ν μ (w : Fin 4 → ℤ)) ψ) =
      ∫ x, energyMomentumMonomial μ n w x ∂σ
def polarIntegral {μ : Fin 4} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (σ : E → Measure (SpectralSpace μ)) [∀ χ, IsFiniteMeasure (σ χ)] (ψ ψ' : E)
    (φ : SpectralSpace μ → ℂ) : ℂ :=
  (1 / 4) * ∑ k ∈ Finset.range 4, Complex.I ^ k * ∫ x, φ x ∂σ (ψ' + Complex.I ^ k • ψ)
def withDensityReal {α : Type*} [MeasurableSpace α] (ϱ : Measure α) (f : α → ℝ) : Measure α :=
  ϱ.withDensity fun x => ENNReal.ofReal (f x)
theorem withDensityReal_apply {α : Type*} [MeasurableSpace α] (ϱ : Measure α) [IsFiniteMeasure ϱ]
    {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {C : ℝ} (hC : ∀ x, f x ≤ C)
    {S : Set α} (hS : MeasurableSet S) :
    withDensityReal ϱ f S = ENNReal.ofReal (∫ x, S.indicator 1 x * f x ∂ϱ) := by
  have e : (fun x => S.indicator (1 : α → ℝ) x * f x) = S.indicator f := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  have hi : Integrable f (ϱ.restrict S) :=
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
      exact hC x)
  rw [withDensityReal, withDensity_apply _ hS, e, integral_indicator hS,
    ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hf0)]
instance isFiniteMeasure_torusMeasure (μ : Fin 4) : IsFiniteMeasure (torusMeasure μ) :=
  ⟨by
    rw [torusMeasure_univ]
    exact ENNReal.ofReal_lt_top⟩
end YangMills.Construction.ReflectionPositivity.DirectionPictures
