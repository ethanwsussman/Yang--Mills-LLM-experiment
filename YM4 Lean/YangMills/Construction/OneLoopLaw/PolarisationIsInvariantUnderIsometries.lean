import YangMills.Construction.PeriodicOperators.TemperedFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.ComplexHessianInvariance
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators.Tempered
def Statement : Prop :=
  ∀ L n : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → ∀ F : FieldFamily L, IsAdmissibleMember (F n) →
    ∀ σ : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n, IsDistancePreserving σ →
      MapsSublatticeOnto 0 0 σ →
      ∀ B ∈ complexEdgeForms L n 0 0, ∀ B' ∈ complexEdgeForms L n 0 0,
        complexHessian F n (isometryOnTangent (k := 0) (j := 0) σ (identityField L n) B)
            (isometryOnTangent (k := 0) (j := 0) σ (identityField L n) B') =
          complexHessian F n B B'
end YangMills.Construction.OneLoopLaw.ComplexHessianInvariance
end
