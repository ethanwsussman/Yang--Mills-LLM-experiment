import YangMills.Construction.OneLoopLaw.KernelsAndTensorFormOfASymbol
import YangMills.Construction.Towers.TheFunctionOfTheMassiveJets
import YangMills.Construction.Towers.TheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.SharpLogFn
open YangMills.Construction.Coordinates.ComplexCoordinates
open YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn)
def SharpMixedDerivative : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∃ O : Set (Coordinates.ComplexCoordinates 4), (0 : Coordinates.ComplexCoordinates 4) ∈ O ∧
      O ⊆ momentumPolydisc stripHalfWidth ∧
      ∃ G : Coordinates.ComplexCoordinates 4 → ℂ, IsHolomorphicScalarIn O G ∧ ∀ w ∈ O, w ∈ realLocus 4 →
        G w = massiveLogFnSharp L k w 0 1) ∧
    -OneLoopLaw.TemperedStiffness.secondPartialAtZero (fun p => massiveLogFnSharp L k p 0 1) 0 1 =
      ((massiveStiffness hL (finestMesh L k ^ 2) -
          finestMesh L k ^ 2 * massiveStiffnessDeriv hL (finestMesh L k ^ 2) +
          1 / 2 * finestMesh L k ^ 4 *
            massiveStiffnessDeriv2 hL (finestMesh L k ^ 2) : ℝ) : ℂ)
end YangMills.Construction.Tower.MassiveOpFunctions.SharpLogFn
end
