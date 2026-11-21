import YangMills.Construction.ReflectionPositivity.TwoPicturesOfADirection
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open InfiniteLattice (GaugeField axisStep shift halfSpaceLocalObservables)
open MirrorHyperplanes (unitPositiveClass linkReflect siteReflect)
def MatrixElementsEqCorrelations : Prop :=
  ∀ (ρ : unitPositiveClass) (i : Fin 4),
    ∀ A ∈ halfSpaceLocalObservables i, ∀ B ∈ halfSpaceLocalObservables i, ∀ (n : ℕ) (v : Fin 4 → ℤ),
      v i = 0 →
      inner ℂ (ReflectionPair.link.obsClass ρ i A)
          ((ReflectionPair.link.transferOp ρ i ^ n * ReflectionPair.link.shiftMonomial ρ i v)
            (ReflectionPair.link.obsClass ρ i B)) =
        ∫ U, conj ((linkReflect i).actOn A U) *
          (shift (n • axisStep 1 i + intPoint v)).actOn B U
          ∂(ρ : Measure (GaugeField (1 : ℝ))) ∧
      inner ℂ (ReflectionPair.site.obsClass ρ i A)
          ((ReflectionPair.site.transferOp ρ i ^ n * ReflectionPair.site.shiftMonomial ρ i v)
            (ReflectionPair.site.obsClass ρ i B)) =
        ∫ U, conj ((siteReflect i).actOn A U) *
          (shift (n • axisStep 1 i + intPoint v)).actOn B U
          ∂(ρ : Measure (GaugeField (1 : ℝ)))
end YangMills.Construction.ReflectionPositivity.DirectionPictures
