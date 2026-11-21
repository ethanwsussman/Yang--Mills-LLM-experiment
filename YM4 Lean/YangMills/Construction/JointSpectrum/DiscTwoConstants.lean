import YangMills.Construction.EnergyMomentum.LatticeBasics
import YangMills.Construction.JointSpectrum.DiscAndCone
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace DiscTwoConstants
open MeasureTheory
open scoped ENNReal
def SqIntegralLeSupProduct (m : Measure DiscGeometry.closedUnitDisc) (C₀ : ℝ)
    (p : Polynomial ℂ) : Prop :=
  ∫⁻ z, ‖Polynomial.eval (z : ℂ) p‖ₑ ^ 2 ∂m ≤
    ENNReal.ofReal C₀ *
      LatticeBasics.supNormE (fun t : unitInterval => Polynomial.eval ((t : ℝ) : ℂ) p) *
      LatticeBasics.supNormE (fun ζ : Circle => Polynomial.eval (ζ : ℂ) p)
def DiscTwoConstantsStatement : Prop :=
  ∀ (m : Measure DiscGeometry.closedUnitDisc) [IsFiniteMeasure m],
    (∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ p : Polynomial ℂ, SqIntegralLeSupProduct m C₀ p) →
      m (Subtype.val ⁻¹' DiscGeometry.nearRegion) = 0
end DiscTwoConstants
end YangMills.Construction
