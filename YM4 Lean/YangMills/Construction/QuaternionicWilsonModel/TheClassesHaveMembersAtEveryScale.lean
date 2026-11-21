import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import YangMills.Construction.Torus.DistributionsOffTheDiagonalsAndRegularMaps
import YangMills.Construction.Torus.LiftsShapeConditionAndCollinearQuadruples
import YangMills.Construction.Torus.SeparatedTuplesAndIsometriesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff
noncomputable section
namespace YangMills.Construction
namespace TopAux
namespace NonemptyTestClasses
def NonemptyOnEuclideanSpace (d ϑ : ℝ) : Prop :=
  (∃ X : TestSpaces.SepTupleOfCard 2, (X.1 0, X.1 1) ∈ TestFunctions.separatedPairsR4 d ϑ ∧
      TestSpaces.HasSmoothComponents univ X.1) ∧
    ∃ X : TestSpaces.SepTupleOfCard 4, X.1 ∈ QuadrupleClasses.collinearQuadsR4 d ϑ ∧
      TestSpaces.HasSmoothComponents univ X.1
def NonemptyOnTorus (s : Conventions.StandingParameters) (d ϑ : ℝ) : Prop :=
  (∃ X : AmbientPoints.separatedTuples s .torus 2,
      (X.1 0, X.1 1) ∈ TestFunctions.separatedPairsFourTorus s.L s.m d ϑ ∧
      ∀ i, AmbientPoints.IsSmoothReal (X.1 i)) ∧
    ∃ X : AmbientPoints.separatedTuples s .torus 4, X.1 ∈ QuadrupleClasses.collinearQuadsTorus s d ϑ ∧
      ∀ i, AmbientPoints.IsSmoothReal (X.1 i)
def Statement : Prop :=
  (∀ (s : Conventions.StandingParameters) (d : ℝ), d ≤ 1 / 40 → 40 * d ≤ PeriodicLattice.torusSide s.L s.m) ∧
    ∃ ϑ₀ ∈ Ioc (0 : ℝ) 1, ∀ ϑ ∈ Ioc (0 : ℝ) ϑ₀, ∀ d : ℝ, 0 < d →
      NonemptyOnEuclideanSpace d ϑ ∧
        ∀ s : Conventions.StandingParameters, 40 * d ≤ PeriodicLattice.torusSide s.L s.m →
          NonemptyOnTorus s d ϑ
end NonemptyTestClasses
end TopAux
end YangMills.Construction
end
