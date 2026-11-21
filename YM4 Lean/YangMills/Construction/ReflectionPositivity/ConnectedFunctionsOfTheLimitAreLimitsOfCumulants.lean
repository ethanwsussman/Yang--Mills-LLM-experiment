import YangMills.Construction.Continuum.SeparatedTuplesAsListsAndAsMaps
import YangMills.Construction.Conventions.ContinuumLimitsOfLatticeApproximationsDefs
import YangMills.Construction.InfiniteLattice.ConnectedCorrelations
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
def UrsellOfLimitIsLimitOfCumulants : Prop :=
  ∀ (D : AxisMirror.MirrorData) (T : LimitConventions.ApproxTriple D.L) (s : TestSpaces.SepTuple → ℝ),
    LimitConventions.ApproxTriple.ConvergesTo T (fun X => s (TupleLists.ofList X)) →
    ∀ (m : ℕ), 2 ≤ m → ∀ X : TestSpaces.SepTupleOfCard m,
      Tendsto (fun j => InfiniteLattice.ursellFunction (T.state j) m X.1) atTop
        (𝓝 (TestSpaces.cumulant s X : ℂ))
end YangMills.Construction.ReflectionPositivity
end
