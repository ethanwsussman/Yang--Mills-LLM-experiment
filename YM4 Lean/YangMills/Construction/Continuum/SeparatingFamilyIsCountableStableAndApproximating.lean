import YangMills.Construction.Continuum.SeparatingFamilyOfTheCanonicalDecomposition
import YangMills.Construction.Continuum.TuplesAndFunctionalsOfTheCanonicalDecomposition
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CanonicalDecomposition
def hyperoctahedralEquiv (s : YangMills.Construction.Conventions.StandingParameters)
    (w : YangMills.Construction.InfiniteLattice.AmbientSpace ≃ₗ[ℝ]
      YangMills.Construction.InfiniteLattice.AmbientSpace) :
    YangMills.Construction.Continuum.SeparatedFourTuples.EuclideanFour s ≃
      YangMills.Construction.Continuum.SeparatedFourTuples.EuclideanFour s :=
  w.toEquiv
structure SeparatingTuplesProperties (s : YangMills.Construction.Conventions.StandingParameters)
    (M : ℝ) : Prop where
  countable : (separatingTuples s).Countable
  hyperoctahedral_mem : ∀ X ∈ separatingTuples s,
    ∀ w ∈ YangMills.Construction.InfiniteLattice.hyperoctahedralLinearGroup,
    ∃ Y ∈ separatingTuples s,
      Y.1 = YangMills.Construction.Continuum.CanonicalDecomposition.transportedTuple
        (hyperoctahedralEquiv s w) X.1
  shift_mem : ∀ X ∈ separatingTuples s, ∀ v ∈ adicVecSet s.L,
    ∃ Y ∈ separatingTuples s,
      Y.1 = YangMills.Construction.Continuum.CanonicalDecomposition.shiftedTuple s v X.1
  concat_mem : ∀ X ∈ separatingTuples s, ∀ Y ∈ separatingTuples s,
    ∀ hXY : YangMills.Construction.Continuum.SeparatedFourTuples.CanConcat X Y,
      YangMills.Construction.Continuum.SeparatedFourTuples.concat X Y hXY ∈ separatingTuples s
  approx : HasSupportApprox s M (separatingTuples s)
def SeparatingTuplesProperties.Claim : Prop :=
  ∀ (s : YangMills.Construction.Conventions.StandingParameters) (M : ℝ), 1 ≤ M →
    SeparatingTuplesProperties s M
end YangMills.Construction.CanonicalDecomposition
