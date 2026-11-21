import YangMills.Construction.Towers.TheTwoOperatorFunctionsAsFunctionsOfValues
import YangMills.Construction.Towers.TranslationsAndIsometriesOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ShiftCovariance
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.FieldValueFunctions
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.AsDifferentials (boundedSubmodule)
open YangMills.Construction.Tower.FullSpace.AsDifferentials (complexQuadraticTerm iterMean)
open YangMills.Construction.Tower.LevelwiseMeans.Unbounded (IsDefinedAt)
open YangMills.Construction.Tower.FullSpace.Translations (spaceShift)
abbrev latticeShift (n : Fin 4 → ℤ) :
    InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace :=
  spaceShift (castVec n)
def iterDriftFn (L k : ℕ) (hL : 0 < L) :
    ((fieldPeriodicData L k hL).Carrier → ℂ) →
      (colourVertices L k k).Carrier → (colourEdges L k 0).Carrier → ℂ :=
  fun f => (edgePauliCoordinates L k 0).kernel (vertexCoordinate (Vertex L k k))
    (iterContourLogDrift L k (gaugeFieldOfCoeffs hL f) k)
structure ShiftCommutesAt (L k : ℕ) (U : Edge L k 0 → ComplexMatrix2) (n : Fin 4 → ℤ) : Prop where
  covDiffTranspose_shift : ∀ g ∈ complexEdgeForms (meshAt L k 0),
    covDiffTranspose L k (pushField (latticeShift n) U)
        (isometryOnTangent (latticeShift n) U g) =
      pushSiteFunction (latticeShift n) (covDiffTranspose L k U g)
  averageTranspose_shift : ∀ g : Vertex L k k → ComplexMatrix2,
    (∀ y, g y ∈ ComplexMatrix2.traceless) →
    iterAverageTranspose L k (pushField (latticeShift n) U)
        (pushSiteFunction (latticeShift n) g) =
      pushSiteFunction (latticeShift n) (iterAverageTranspose L k U g)
  iterMean_shift : ∃ ς : ℝ, 0 < ς ∧ ∀ B ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)),
    GroupLieProduct.supNorm B < ς → ∀ c : Edge L k k, c.IsPositivelyOriented →
      IsDefinedAt (expTwist B U) k c ∧
      IsDefinedAt (expTwist (isometryOnTangent (latticeShift n) U B)
        (pushField (latticeShift n) U)) k (edgeImage (latticeShift n) c) ∧
      iterMean (expTwist (isometryOnTangent (latticeShift n) U B)
          (pushField (latticeShift n) U)) k (edgeImage (latticeShift n) c) =
        iterMean (expTwist B U) k c
  quadraticTerm_shift : ∀ B ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)),
    ∀ B' ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)),
    ∀ c c' : PositiveEdge (meshAt L k k), c'.1 = edgeImage (latticeShift n) c.1 →
      complexQuadraticTerm L k (pushField (latticeShift n) U)
          (isometryOnTangent (latticeShift n) U B)
          (isometryOnTangent (latticeShift n) U B') c' =
        complexQuadraticTerm L k U B B' c
  bracketTerm_shift : ∀ l : Vertex L k 0 → ComplexMatrix2,
    (∀ x, l x ∈ ComplexMatrix2.traceless) →
    ∀ B ∈ complexEdgeForms (meshAt L k 0),
      levelBracketTerm (pushField (latticeShift n) U)
          (pushSiteFunction (latticeShift n) l)
          (isometryOnTangent (latticeShift n) U B) =
        isometryOnTangent (latticeShift n) U (levelBracketTerm U l B)
  zeroExtend_shift : ∀ g : Vertex L k k → ComplexMatrix2,
    (∀ y, g y ∈ ComplexMatrix2.traceless) →
    (zeroExtend (pushSiteFunction (latticeShift n) g) : Vertex L k 0 → ComplexMatrix2) =
      pushSiteFunction (latticeShift n) (zeroExtend g)
structure KernelsShiftCovariant (L k : ℕ) (hL : 0 < L)
    (f : (fieldPeriodicData L k hL).Carrier → ℂ) (n : Fin 4 → ℤ) : Prop where
  covDiff : ∀ i' i,
    covDiffFn L k hL (shiftField (fieldPeriodicData L k hL) n f)
        ((colourEdges L k 0).translate n i') ((colourVertices L k 0).translate n i) =
      covDiffFn L k hL f i' i
  average : ∀ i' i,
    averageKernelFn L k hL (shiftField (fieldPeriodicData L k hL) n f)
        ((colourVertices L k k).translate n i') ((colourVertices L k 0).translate n i) =
      averageKernelFn L k hL f i' i
  drift : ∀ i' i,
    iterDriftFn L k hL (shiftField (fieldPeriodicData L k hL) n f)
        ((colourVertices L k k).translate n i') ((colourEdges L k 0).translate n i) =
      iterDriftFn L k hL f i' i
  covariantAverage : ∀ i' i,
    covariantAverageFn L k hL (shiftField (fieldPeriodicData L k hL) n f)
        ((colourEdges L k k).translate n i') ((colourEdges L k 0).translate n i) =
      covariantAverageFn L k hL f i' i
def Claim : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ → ∀ n : Fin 4 → ℤ,
      gaugeFieldOfCoeffs hL f ∈ smallIterateFields L k ∧
      pushField (latticeShift n) (gaugeFieldOfCoeffs hL f) ∈ smallIterateFields L k ∧
      IsSupBelow (fieldPeriodicData L k hL) (shiftField (fieldPeriodicData L k hL) n f) ρ ∧
      gaugeFieldOfCoeffs hL (shiftField (fieldPeriodicData L k hL) n f) =
        pushField (latticeShift n) (gaugeFieldOfCoeffs hL f) ∧
      ShiftCommutesAt L k (gaugeFieldOfCoeffs hL f) n ∧
      KernelsShiftCovariant L k hL f n
end YangMills.Construction.Tower.FullSpace.ShiftCovariance
end
