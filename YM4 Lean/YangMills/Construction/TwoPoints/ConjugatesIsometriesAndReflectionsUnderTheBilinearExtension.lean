import YangMills.Construction.EuclideanFunctionals.CombinationsOfTuplesComplexComponentsAndConvergenceInC1
import YangMills.Construction.LimitsAlongPeriodicGibbsStates.ReflectionsInHyperplanesAndTheSixteenFamiliesOfMirrors
import YangMills.Construction.TwoPoints.RealFunctionsOnSeparatedPairsAndTheirBilinearExtension
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.PairFunctions
def IsSymmOnPairs (T : sepPairs → ℝ) : Prop :=
  ∀ u v : EuclideanFunctionals.R4 → ℝ, [u, v] ∈ sepPairs → evalPair T u v = evalPair T v u
namespace ConjIsometryReflection
def ConjCommutesAndForm (T : sepPairs → ℝ) : Prop :=
  (∀ u ∈ TwoPoints.compactC1Complex, ∀ v ∈ TwoPoints.compactC1Complex, TwoPoints.DisjointSupports u v →
    complexExtension T (TwoPoints.conjFun u) (TwoPoints.conjFun v) =
      conj (complexExtension T u v)) ∧
    TwoPoints.IsDisjointForm (realPartForm T)
def InvariantUnderMotions (T : sepPairs → ℝ) : Prop :=
  ∀ g : EuclideanFunctionals.EuclidMotion,
    (∀ u v : EuclideanFunctionals.R4 → ℝ, [u, v] ∈ sepPairs →
      evalPair T (g.actFn u) (g.actFn v) = evalPair T u v) →
    ∀ u ∈ TwoPoints.compactC1Complex, ∀ v ∈ TwoPoints.compactC1Complex, TwoPoints.DisjointSupports u v →
      complexExtension T (g.actFn u) (g.actFn v) = complexExtension T u v
def ReflectedTwoPointFunction (T : sepPairs → ℝ) : Prop :=
  ∀ S : EuclideanFunctionals.ConnFamily, S.fn 2 le_rfl = T →
    ∀ (e : EuclideanFunctionals.R4) (he : TwoPoints.euclidNorm e = 1),
      ∀ u ∈ TwoPoints.cc1In {x : EuclideanFunctionals.R4 | 0 < TwoPoints.euclidDot e x},
        let F : EuclideanFunctionals.FreeSep := EuclideanFunctionals.complexTuple fun _ : Fin 1 => u
        let G : EuclideanFunctionals.FreeSep := PeriodicGibbsLimits.reflectedConj e he 0 F
        F ∈ EuclideanFunctionals.finCombIn
            {x : EuclideanFunctionals.R4 | 0 < TwoPoints.euclidDot e x} ∧
          EuclideanFunctionals.MulDefined G F ∧
          EuclideanFunctionals.centeredFnFree S (EuclideanFunctionals.freeMul G F) =
            complexExtension T (TwoPoints.reflectFun e (TwoPoints.conjFun u)) u
def Statement : Prop :=
  ∀ T : sepPairs → ℝ, IsSymmOnPairs T → IsBilinearOnPairs T →
    ConjCommutesAndForm T ∧ InvariantUnderMotions T ∧ ReflectedTwoPointFunction T
end ConjIsometryReflection
end YangMills.Construction.PairFunctions
end
