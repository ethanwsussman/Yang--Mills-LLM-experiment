import YangMills.Construction.TorusOrFourSpace.DerivativesOfFunctionsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.DistanceAndLiftsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.DistanceOpenSetsDerivativesAndTensorsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.OpenSetsAndBallsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.ProductsAndProjectionsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.SumsProductsAndTestFunctionsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.TensorsOfFunctionsOfOnePoint
import YangMills.Construction.TorusOrFourSpace.TwoSensesOfClassC1AtOnePoint
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicSpace.TupleFacts
theorem allFacts_holds
    (wellPosed : WellPosedness.WellPosed)
    (lifts : TupleMetric.QuotientDistanceAndLifts)
    (openSets : TupleTopology.QuotientOpenAndBalls)
    (products : TupleProducts.Statement)
    (derivatives : TupleDerivatives.Statement)
    (singleC1 : SingletonC1.Statement)
    (algebra : AlgebraOfTestFns.Claim)
    (tensors : TensorOfSingles.Claim) : AllFacts := by
  intro D E p
  obtain ⟨l1, l2, l3, l4, l5⟩ := lifts D E p
  obtain ⟨o1, o2, o3, o4, o5⟩ := openSets D E p
  obtain ⟨r1, r2, r3⟩ := products D E p
  obtain ⟨d1, d2⟩ := derivatives D E p
  obtain ⟨s1, s2, s3, s4⟩ := algebra D E p
  obtain ⟨t1, t2, t3⟩ := tensors D E p
  have w := (wellPosed D E).2.2.2.2.2.1
  exact ⟨l1, l2, l3, l4, l5, w, o1, o2, o3, o4, o5, r1, r2, r3, d1, d2, singleC1 D E, s1, s2, s3,
    s4, t1, t2, t3⟩
end YangMills.Construction.PeriodicSpace.TupleFacts
