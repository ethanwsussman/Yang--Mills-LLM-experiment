import YangMills.Construction.RunningCouplingSlope.OnePlainStepOnTheWhole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
open YangMills.Construction.Tower YangMills.Construction.Tower.FullSpace
def MeanStepOnForms : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ δ : ℝ, 0 < δ ∧ ∀ k m : ℕ, m < k →
    ∀ V ∈ nearIdentityFields L k m δ,
      (∀ B ∈ FullSpace.complexEdgeForms (meshAt L k m),
        meanCovariantStep V B ∈ FullSpace.complexEdgeForms (meshAt L k (m + 1))) ∧
      (∀ B ∈ FullSpace.complexEdgeForms (meshAt L k m), ∀ B' ∈ FullSpace.complexEdgeForms (meshAt L k m),
        ∀ w : ℂ, meanCovariantStep V (w • B + B') =
          w • meanCovariantStep V B + meanCovariantStep V B') ∧
      (∀ c : FullSpace.Edge L k (m + 1), c.IsPositivelyOriented → ∀ B ∈ FullSpace.complexEdgeForms (meshAt L k m),
        (∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k m) c, B b = 0) →
          meanCovariantStep V B c = 0) ∧
      ∀ c : FullSpace.Edge L k (m + 1), c.IsPositivelyOriented → ∀ V' ∈ nearIdentityFields L k m δ,
        (∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k m) c, V b = V' b) →
          meanRadius V c = meanRadius V' c ∧ normalizedMean V c = normalizedMean V' c ∧
          (∀ B ∈ FullSpace.complexEdgeForms (meshAt L k m),
            meanCovariantStep V B c = meanCovariantStep V' B c) ∧
          ∀ y : FullSpace.Vertex L k (m + 1), (y = c.initial ∨ y = c.terminal) →
            ∀ x ∈ FullSpace.cubeVertices L (meshAt L k m) y,
              FullSpace.complexContourMean L V y x = FullSpace.complexContourMean L V' y x
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
