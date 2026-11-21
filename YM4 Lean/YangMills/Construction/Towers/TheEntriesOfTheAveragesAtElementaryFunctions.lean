import YangMills.Construction.Towers.BondsOnWhichTheAveragesDepend
import YangMills.Construction.Towers.TheTwoOperatorFunctionsAsFunctionsOfValues
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ElementaryEntries
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.FieldValueFunctions (backgroundCoords gaugeFieldOfCoeffs)
open YangMills.Construction.Tower.SupportOfMeans.Unbounded (supportEdges)
open YangMills.Construction.Tower.FullSpace.AsDifferentials (complexQuadraticTerm)
def singleSiteFunction {σ : Type} (a : Fin 3) (x : σ) : σ → YangMills.Construction.Matrices.ComplexMatrix2 :=
  open Classical in fun y => if y = x then YangMills.Construction.Matrices.ComplexMatrix2.pauliFamily a else 0
def DependsOnCubesOf (L k : ℕ) (hL : 0 < L) (ρ : ℝ) {u : ℕ}
    (c : YangMills.Construction.Tower.FullSpace.Edge L k u)
    (g : ((YangMills.Construction.Tower.FullSpace.fieldPeriodicData L k hL).Carrier → ℂ) → ℂ) : Prop :=
  HolomorphicInValuesBelow (YangMills.Construction.Tower.FullSpace.fieldPeriodicData L k hL) ρ
    (backgroundCoords L k hL (supportEdges c)) g
structure EdgeEntries (L k : ℕ) (hL : 0 < L) (ρ : ℝ) {i : ℕ}
    (c : YangMills.Construction.Tower.FullSpace.Edge L k (i + 1)) : Prop where
  iterDeriv_entries : ∀ (a' a : Fin 3)
      (b : YangMills.Construction.Tower.FullSpace.PositiveEdge (YangMills.Construction.Tower.meshAt L k 0)),
    DependsOnCubesOf L k hL ρ c fun f => YangMills.Construction.Tower.pauliCoeff a'
      (YangMills.Construction.Tower.FullSpace.complexIterDeriv L k (i + 1) (gaugeFieldOfCoeffs hL f)
        (YangMills.Construction.Tower.FullSpace.basisForm a b) c)
  covDiff_entries : ∀ (a' a : Fin 3) (x : YangMills.Construction.Tower.FullSpace.Vertex L k (i + 1)),
    DependsOnCubesOf L k hL ρ c fun f => YangMills.Construction.Tower.pauliCoeff a'
      (YangMills.Construction.Tower.FullSpace.covDiff
        (YangMills.Construction.Tower.FullSpace.complexIter L k (i + 1) (gaugeFieldOfCoeffs hL f))
        (singleSiteFunction a x) c)
  cubeAverage_entries : ∀ (a' a : Fin 3) (x : YangMills.Construction.Tower.FullSpace.Vertex L k i),
    DependsOnCubesOf L k hL ρ c fun f => YangMills.Construction.Tower.pauliCoeff a'
      (YangMills.Construction.Tower.FullSpace.adjointCubeAverage
        (YangMills.Construction.Tower.FullSpace.complexIter L k i (gaugeFieldOfCoeffs hL f))
        (singleSiteFunction a x) c.initial)
  contourDrift_entries : ∀ (a' a : Fin 3)
      (b : YangMills.Construction.Tower.FullSpace.PositiveEdge (YangMills.Construction.Tower.meshAt L k i)),
    DependsOnCubesOf L k hL ρ c fun f => YangMills.Construction.Tower.pauliCoeff a'
      (YangMills.Construction.Tower.FullSpace.contourLogDrift
        (YangMills.Construction.Tower.FullSpace.complexIter L k i (gaugeFieldOfCoeffs hL f))
        (YangMills.Construction.Tower.FullSpace.basisForm a b) c.initial)
def QuadraticEntries (L k : ℕ) (hL : 0 < L) (ρ : ℝ)
    (c : YangMills.Construction.Tower.FullSpace.PositiveEdge (YangMills.Construction.Tower.meshAt L k k)) :
    Prop :=
  ∀ (a'' a a' : Fin 3)
    (b b' : YangMills.Construction.Tower.FullSpace.PositiveEdge (YangMills.Construction.Tower.meshAt L k 0)),
    DependsOnCubesOf L k hL ρ c.1 fun f => YangMills.Construction.Tower.pauliCoeff a''
      (complexQuadraticTerm L k (gaugeFieldOfCoeffs hL f)
        (YangMills.Construction.Tower.FullSpace.basisForm a b)
        (YangMills.Construction.Tower.FullSpace.basisForm a' b') c)
def EntriesHolomorphic : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
    ∀ k : ℕ, 1 ≤ k →
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ i < k, ∀ c : YangMills.Construction.Tower.FullSpace.Edge L k (i + 1),
        c.IsPositivelyOriented → EdgeEntries L k hL ρ c) ∧
      ∀ c : YangMills.Construction.Tower.FullSpace.PositiveEdge (YangMills.Construction.Tower.meshAt L k k),
        QuadraticEntries L k hL ρ c
end YangMills.Construction.Tower.FullSpace.ElementaryEntries
end
