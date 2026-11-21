import YangMills.Construction.Continuum.ConnectedFunctionsCentredFunctionalsOnTheSpanAndCumulantsOfAState
import YangMills.Construction.Conventions.ContinuumLimitsOfLatticeApproximationsDefs
import YangMills.Construction.ReflectionPositivity.BoundedLatticeApproximationsAndTheirC1Constants
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
def CentredAtPlaquetteMeans : Prop :=
  ∀ (D : AxisMirror.MirrorData) (T : LimitConventions.ApproxTriple D.L) (s : TestSpaces.SepTuple → ℝ),
    ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM D T →
    LimitConventions.ApproxTriple.IsReflPos T →
    LimitConventions.ApproxTriple.ConvergesTo T (fun X => s (TupleLists.ofList X)) →
    TestSpaces.IsMultilinearSepFunctional s ∧
    (∃ c : ℕ+ → ℝ, ∀ (j : ℕ+)
        (p : InfiniteLattice.ElementaryPlaquette (InfiniteLattice.refinedSpacing D.L (T.cutoff j))),
      ∫ U, InfiniteLattice.faceEnergy U p ∂T.state j = c j) ∧
    (∀ c : ℕ+ → ℝ, (∀ (j : ℕ+)
        (p : InfiniteLattice.ElementaryPlaquette (InfiniteLattice.refinedSpacing D.L (T.cutoff j))),
        ∫ U, InfiniteLattice.faceEnergy U p ∂T.state j = c j) →
      ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM D { T with offset := c } ∧
        LimitConventions.ApproxTriple.IsReflPos { T with offset := c } ∧
        LimitConventions.ApproxTriple.ConvergesTo { T with offset := c }
          (TestSpaces.centredPartFunctional s)) ∧
    (∀ (f : (Fin 4 → ℝ) → ℝ) (hf : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))),
      Tendsto (fun j => ∫ U, ApproximatingSequences.LatticeApproximation.smearedField T j f U ∂T.state j)
        atTop (𝓝 (s ⟨1, TestSpaces.singletonSepTuple f hf⟩))) ∧
    ((∀ (j : ℕ+)
        (p : InfiniteLattice.ElementaryPlaquette (InfiniteLattice.refinedSpacing D.L (T.cutoff j))),
        ∫ U, InfiniteLattice.faceEnergy U p ∂T.state j = T.offset j) →
      ∀ (f : (Fin 4 → ℝ) → ℝ), f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) →
        ∀ j : ℕ+, ∫ U, ApproximatingSequences.LatticeApproximation.smearedField T j f U ∂T.state j = 0)
end YangMills.Construction.ReflectionPositivity
end
