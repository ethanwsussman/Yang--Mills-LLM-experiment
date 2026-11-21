import YangMills.Construction.OneLoopLaw.CoefficientOfAFunctional
import YangMills.Construction.PeriodicOperators.RiemannSumsAndShifts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.BondFormHessianOnTorus
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.Tempered YangMills.Construction.PeriodicOperators.RiemannSums
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def PlaneWaveExpansion : Prop :=
  ∀ L n : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → ∀ F : FieldFamily L,
    IsAdmissibleMember (F n) →
    (∀ (a a' : Fin 3) (μ ν : Fin 4), ∀ p ∈ dualLattice (2 * L ^ n), ∀ p' ∈ dualLattice (2 * L ^ n),
      p + p' ∉ periodLattice →
        complexHessian F n (fourierModeForm L n a p μ) (fourierModeForm L n a' p' ν) = 0) ∧
    ∀ (x y : EffectiveAction.IntBond) (a a' : Fin 3),
      complexHessian F n (FunctionalStiffness.liftedPauliForm L n a x)
          (FunctionalStiffness.liftedPauliForm L n a' y) =
        (((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) * ∑ᶠ c : DualClasses (2 * L ^ n),
          Complex.exp (Complex.I * bilinDot
              (toComplexVec (Quotient.out c : dualLattice (2 * L ^ n)))
              (toComplexVec (castVec (y.1 - x.1)))) *
            ((((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) *
              complexHessian F n
                (fourierModeForm L n a (Quotient.out c : dualLattice (2 * L ^ n)) x.2)
                (fourierModeForm L n a'
                  (-(Quotient.out c : dualLattice (2 * L ^ n)) : AmbientSpace) y.2))
end YangMills.Construction.OneLoopLaw.BondFormHessianOnTorus
end
