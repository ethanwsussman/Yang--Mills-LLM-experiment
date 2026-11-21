import YangMills.Construction.ReflectionPositivity.LinkCubeAndItsCubeVectors
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField axisStep shift closedHalfSpace
  halfSpaceLocalObservables unitRegionObservables observableSupNorm)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass linkReflect)
def transversePart (μ : Fin 4) (y : Fin 4 → ℤ) : Fin 4 → ℤ :=
  y - y μ • Pi.single μ 1
def blockCorrelation (meas : unitPositiveClass) (F G : GaugeField (1 : ℝ) → ℂ)
    (y : Fin 4 → ℤ) : ℂ :=
  ∫ U, conj (F U) * (shift (intPoint y)).actOn G U
    ∂(meas : Measure (GaugeField (1 : ℝ)))
def LinkBlockCorrelationTheorem : Prop :=
  ∀ (meas : unitPositiveClass) (r : ℕ+) (F G : GaugeField (1 : ℝ) → ℂ),
    F ∈ unitRegionObservables (linkBlock r) → G ∈ unitRegionObservables (linkBlock r) →
    ∀ y : Fin 4 → ℤ,
      (∀ μ : Fin 4,
        (linkReflect μ).setImage (linkBlock r) = linkBlock r ∧
        (linkReflect μ).actOn F ∈ unitRegionObservables (linkBlock r) ∧
        (shift ((r : ℕ) • axisStep 1 μ)).setImage (linkBlock r) ⊆ closedHalfSpace μ ∧
        (shift ((r : ℕ) • axisStep 1 μ)).actOn F ∈ halfSpaceLocalObservables μ ∧
        ‖linkBlockVector meas μ r F‖ ≤ observableSupNorm F) ∧
      (∀ μ : Fin 4, 2 * (r : ℤ) ≤ y μ →
        blockCorrelation meas F G y =
          inner ℂ (linkBlockVector meas μ r ((linkReflect μ).actOn F))
            ((ReflectionPair.link.transferOp meas μ ^ (y μ - 2 * (r : ℤ)).toNat *
                ReflectionPair.link.shiftMonomial meas μ (transversePart μ y))
              (linkBlockVector meas μ r G))) ∧
      blockCorrelation meas F G (-y) = conj (blockCorrelation meas G F y)
end YangMills.Construction.ReflectionPositivity.DirectionPictures
