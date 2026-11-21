import YangMills.Construction.EuclideanFunctionals.ContinuationOfTheInsertionFunctionOfATriple
import YangMills.Construction.EuclideanFunctionals.FractionsAndConstantsOfThePlateBound
import YangMills.Construction.TestFunctions.LaplacianOfR4
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ParametrixBracket
variable {m : SharpScale} {S : ConnFamily}
def parametrixFn (r : ℝ) : R4 → ℝ :=
  fun x => EuclideanAnalysis.CubedLaplacian.laplacianCubedParametrix r (WithLp.toLp 2 x)
def remainderFn (r : ℝ) : R4 → ℝ :=
  fun x => (EuclideanAnalysis.CubedLaplacian.remainderDensity r (WithLp.toLp 2 x)).re
def insertionMajorant (σ : EuclidFunctionalWithRecon m S) (p C η : ℝ) (k : R4 → ℝ)
    (F A : FreeSep) : ℝ :=
  (2 : ℝ) ^ p * C * η ^ (-p) * m.sharpNorm k * heightNorm σ (η / 4) F * heightNorm σ (η / 4) A
structure IsSmallKernel (r : ℝ) (k : R4 → ℝ) : Prop where
  mem_C1c : k ∈ C1c ℝ
  supp_subset : supp k ⊆ {z | TorusMetric.euclidNormVec z ≤ r}
structure InsertionFnDerivBounds (σ : EuclidFunctionalWithRecon m S)
    (p C cS cCau η : ℝ) (k : R4 → ℝ) (F A : FreeSep) : Prop where
  contDiffOn : ContDiffOn ℝ ∞ (tripleInsertionFn S F k A) (timeSlab (η / 8))
  analytic : ∀ γ : Multiindex,
    IsRealAnalyticFn (ν := 4)
      {z | z ∈ Coordinates.ComplexCoordinates.realLocus 4 ∧ |(z 3).re| < η / 8}
      fun z => iteratedPartial γ (tripleInsertionFn S F k A) fun μ => (z μ).re
  norm_le : ∀ x ∈ thinSlab cS η, ∀ γ : Multiindex,
    ‖iteratedPartial γ (tripleInsertionFn S F k A) x‖ ≤
      (Multiindex.fact γ : ℝ) * cauchyRadius cCau η ^ (-(Multiindex.order γ : ℤ)) *
        insertionMajorant σ p C η k F A
def smearIntegrand (φ u : R4 → ℂ) : R4 → ℂ :=
  (supp φ).indicator fun x => φ x * u x
structure SmearingFormula (S : ConnFamily) (η : ℝ) (φ : R4 → ℂ) (k : R4 → ℝ)
    (F A : FreeSep) : Prop where
  mem_C1c : conv φ (fun y => (k y : ℂ)) ∈ C1c ℂ
  supp_subset : supp (conv φ fun y => (k y : ℂ)) ⊆ timeSlab (η / 8)
  integrable : Integrable (smearIntegrand φ (tripleInsertionFn S F k A))
  eq_integral : insertion S F (conv φ fun y => (k y : ℂ)) A =
    ∫ x, smearIntegrand φ (tripleInsertionFn S F k A) x
def weightedIntegrand (h g : R4 → ℝ) (u : R4 → ℂ) : R4 → ℂ :=
  (supp h).indicator fun x => (g x : ℂ) * u x
def bracketFn (S : ConnFamily) (r : ℝ) (F A : FreeSep) : R4 → ℂ :=
  fun x =>
    TestFunctions.laplacianR4^[3] (tripleInsertionFn S F (parametrixFn r) A) x +
      tripleInsertionFn S F (remainderFn r) A x
structure ParametrixRepresentation (S : ConnFamily) (r : ℝ) (h : R4 → ℝ) (F A : FreeSep) : Prop where
  integrable_param : Integrable (weightedIntegrand h (TestFunctions.laplacianR4^[3] h)
    (tripleInsertionFn S F (parametrixFn r) A))
  integrable_rem : Integrable (weightedIntegrand h h
    (tripleInsertionFn S F (remainderFn r) A))
  integrable_bracket : Integrable (weightedIntegrand h h (bracketFn S r F A))
  eq_sum : insertion S F (fun y => (h y : ℂ)) A =
    (∫ x, weightedIntegrand h (TestFunctions.laplacianR4^[3] h)
        (tripleInsertionFn S F (parametrixFn r) A) x) +
      ∫ x, weightedIntegrand h h (tripleInsertionFn S F (remainderFn r) A) x
  sum_eq :
    (∫ x, weightedIntegrand h (TestFunctions.laplacianR4^[3] h)
        (tripleInsertionFn S F (parametrixFn r) A) x) +
      (∫ x, weightedIntegrand h h (tripleInsertionFn S F (remainderFn r) A) x) =
    ∫ x, weightedIntegrand h h (bracketFn S r F A) x
structure BracketBounds (σ : EuclidFunctionalWithRecon m S)
    (p C cPar cCau η : ℝ) (F A : FreeSep) (x : R4) : Prop where
  param_le :
    ‖TestFunctions.laplacianR4^[3]
        (tripleInsertionFn S F (parametrixFn (paramRadius cPar η)) A) x‖ ≤
      laplacianCubedConst * cauchyRadius cCau η ^ (-6 : ℤ) *
        insertionMajorant σ p C η (parametrixFn (paramRadius cPar η)) F A
  rem_le :
    ‖tripleInsertionFn S F (remainderFn (paramRadius cPar η)) A x‖ ≤
      insertionMajorant σ p C η (remainderFn (paramRadius cPar η)) F A
  sum_le :
    ‖TestFunctions.laplacianR4^[3]
        (tripleInsertionFn S F (parametrixFn (paramRadius cPar η)) A) x‖ +
      ‖tripleInsertionFn S F (remainderFn (paramRadius cPar η)) A x‖ ≤
      1 / 2 * productConst m p C cPar cCau * η ^ (-productExponent p) *
        heightNorm σ (η / 4) F * heightNorm σ (η / 4) A
def Main : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S)
    (p C cI cS cPar cCau : ℝ), σ.ConeCondition → InsertionBoundHolds σ p C cI →
    ProductBoundParams p C cI cS cPar cCau →
    ∀ η : ℝ, 0 < η → η ≤ 1 →
    ∀ F ∈ finCombIn {y | η / 4 < y 3}, ∀ A ∈ finCombIn {y | η / 4 < y 3},
      (∀ k : R4 → ℝ, IsSmallKernel (paramRadius cPar η) k →
        ExtendableTriple cI η F k A ∧
          InsertionFnDerivBounds σ p C cS cCau η k F A) ∧
      (∀ k : R4 → ℝ, IsSmallKernel (paramRadius cPar η) k →
        ∀ φ : R4 → ℂ, Continuous φ → HasCompactSupport φ → supp φ ⊆ thinSlab cS η →
          SmearingFormula S η φ k F A) ∧
      IsSmallKernel (paramRadius cPar η) (parametrixFn (paramRadius cPar η)) ∧
      IsSmallKernel (paramRadius cPar η) (remainderFn (paramRadius cPar η)) ∧
      (∀ h ∈ smoothCompactSupp R4 ℝ, supp h ⊆ thinSlab cS η →
        ParametrixRepresentation S (paramRadius cPar η) h F A) ∧
      ∀ x ∈ thinSlab cS η, BracketBounds σ p C cPar cCau η F A x
end YangMills.Construction.EuclideanFunctionals.ParametrixBracket
