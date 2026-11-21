import YangMills.Construction.ReflectionPositivity.CubeAndCubeVectors
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField axisStep shift unitRegionObservables)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass siteReflect)
def CubeCorrelationsTheorem : Prop :=
  ∀ (ν : unitPositiveClass) (μ : Fin 4) (r : ℕ+),
  (∀ A ∈ unitRegionObservables (cubeOfRadius r), ∀ B ∈ unitRegionObservables (cubeOfRadius r),
    ∀ y : Fin 4 → ℤ, 2 * (r : ℤ) ≤ y μ →
      ∫ U, conj (A U) * (shift (intPoint y)).actOn B U
          ∂(ν : Measure (GaugeField (1 : ℝ))) =
        inner ℂ (cubeVector ν μ r ((siteReflect μ).actOn A))
          ((ReflectionPair.site.transferOp ν μ ^ (y μ - 2 * (r : ℤ)).toNat *
            ReflectionPair.site.shiftMonomial ν μ (y - y μ • Pi.single μ 1))
            (cubeVector ν μ r B))) ∧
  (∀ A ∈ unitRegionObservables (cubeOfRadius r), ∀ B ∈ unitRegionObservables (cubeOfRadius r),
    ∀ y : Fin 4 → ℤ,
      ∫ U, conj (A U) * (shift (intPoint (-y))).actOn B U
          ∂(ν : Measure (GaugeField (1 : ℝ))) =
        conj (∫ U, conj (B U) * (shift (intPoint y)).actOn A U
          ∂(ν : Measure (GaugeField (1 : ℝ))))) ∧
  ∀ A ∈ unitRegionObservables (cubeOfRadius r),
    ((‖cubeVector ν μ r A‖ ^ 2 : ℝ) : ℂ) =
      ∫ U, conj ((siteReflect μ).actOn A U) *
        (shift ((2 * (r : ℕ)) • axisStep (1 : ℝ) μ)).actOn A U
        ∂(ν : Measure (GaugeField (1 : ℝ)))
end YangMills.Construction.ReflectionPositivity.DirectionPictures
