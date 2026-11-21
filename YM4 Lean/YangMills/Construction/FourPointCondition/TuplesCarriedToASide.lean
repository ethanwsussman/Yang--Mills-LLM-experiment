import YangMills.Construction.FourPointCondition.CutoffNamesTheUnitOfLength
import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FourPointCondition
def dilatedTupleToSideStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (m M p : ℕ) (d n vt : ℝ), ℓ.Admissible →
    n * PeriodicLattice.torusSide ℓ.side m = d * PeriodicLattice.torusSide ℓ.side M →
    ∀ f : Fin p → PeriodicLattice.FourTorus ℓ.side m → ℝ,
    ResponseInTheExpansion.IsSeparatedTestTuple ℓ m d vt f →
      ResponseInTheExpansion.IsSeparatedTestTuple ℓ M n vt (fun i => FourPointBounds.dilateToSide ℓ.side m M (f i)) ∧
      ∀ q : ℕ, p = q + 1 → ∀ g : Fin (q + 1) → PeriodicLattice.FourTorus ℓ.side m → ℝ,
        ResponseInTheExpansion.IsSeparatedTestTuple ℓ m d vt g →
        ResponseInTheExpansion.gaussianCumulantLimit (PeriodicLattice.torusSide ℓ.side M)
            (fun i => FourPointBounds.dilateToSide ℓ.side m M (g i)) =
          ResponseInTheExpansion.gaussianCumulantLimit (PeriodicLattice.torusSide ℓ.side m) g
end YangMills.Construction.FourPointCondition
end
