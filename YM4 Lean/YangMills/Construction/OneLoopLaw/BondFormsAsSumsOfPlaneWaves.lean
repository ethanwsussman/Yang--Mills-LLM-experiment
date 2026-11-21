import YangMills.Construction.OneLoopLaw.CoefficientOfAFunctional
import YangMills.Construction.PeriodicOperators.RiemannSumsAndShifts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.FourierExpansion
open YangMills.Construction.PeriodicOperators YangMills.Construction.PeriodicOperators.Tempered
open YangMills.Construction.PeriodicOperators.RiemannSums YangMills.Construction.Conventions
def BondFormFourierExpansion : Prop :=
  ∀ L n : ℕ, IsAdmissibleBlockingFactor L → 0 < n →
    Finite (DualClasses (2 * L ^ n)) ∧
    ∀ (a : Fin 3) (b : EffectiveAction.IntBond),
      FunctionalStiffness.liftedPauliForm L n a b =
        (((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) • ∑ᶠ k : DualClasses (2 * L ^ n),
          Complex.exp (-(Complex.I * bilinDot (toComplexVec (Quotient.out k : dualLattice (2 * L ^ n)))
              (toComplexVec (castVec b.1)))) •
            fourierModeForm L n a (Quotient.out k : dualLattice (2 * L ^ n)) b.2
end YangMills.Construction.OneLoopLaw.FourierExpansion
end
