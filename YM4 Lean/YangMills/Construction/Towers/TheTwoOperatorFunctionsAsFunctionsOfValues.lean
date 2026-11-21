import YangMills.Construction.Towers.TheJetsOfTheTwoOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
def HolomorphicInValuesBelow (F : PeriodicData) (ρ : ℝ) (S : Set F.Carrier)
    (g : (F.Carrier → ℂ) → ℂ) : Prop :=
  ∃ (l : ℕ) (e : Fin l ≃ S) (h : Coordinates.ComplexCoordinates l → ℂ),
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1)
      (Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk 0 ρ) (fun z _ => h z) ∧
    ∀ ζ, IsSupBelow F ζ ρ → g ζ = h (fieldValues e ζ)
end PeriodicOperators
namespace Tower.FullSpace.FieldValueFunctions
open PeriodicOperators
open LocalKernels (FieldIdx FieldComponent)
open _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials (complexQuadraticTerm)
variable {L k : ℕ}
def gaugeFieldOfCoeffs (hL : 0 < L) (f : FieldIdx L k hL → ℂ) :
    Edge L k 0 → Matrices.ComplexMatrix2 :=
  expForm (backgroundOfCoeffs hL f)
def backgroundCoords (L k : ℕ) (hL : 0 < L) (S : Set (Edge L k 0)) :
    Set (FieldIdx L k hL) :=
  {κ | ∃ (a : Fin 3) (b : PositiveEdge (meshAt L k 0)), b.1 ∈ S ∧ κ = ⟨.background, (a, b)⟩}
def sourceBilinear (U J : Edge L k 0 → Matrices.ComplexMatrix2)
    (μ : Edge L k k → Matrices.ComplexMatrix2) (B B' : Edge L k 0 → Matrices.ComplexMatrix2) : ℂ :=
  2 * finiteEdgePairing J (levelBracketTerm U (gaugeParam U B) B') +
    finiteEdgePairing J (levelBracketTerm U (gaugeParam U B)
      (covDiff U (gaugeParam U B'))) -
    traceFinsumPairing (restrictToPositiveEdges μ)
      (complexQuadraticTerm L k U (shiftedForm U B) (shiftedForm U B'))
def hessianBilinear (U J : Edge L k 0 → Matrices.ComplexMatrix2)
    (μ : Edge L k k → Matrices.ComplexMatrix2) (B B' : Edge L k 0 → Matrices.ComplexMatrix2) : ℂ :=
  backgroundForm L k U B B' + sourceBilinear U J μ B B'
def rawHessianKernel (U J : Edge L k 0 → Matrices.ComplexMatrix2)
    (μ : Edge L k k → Matrices.ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge (meshAt L k 0))
      (Fin 3 × PositiveEdge (meshAt L k 0)) :=
  fun ι' ι => hessianBilinear U J μ (basisForm ι'.1 ι'.2) (basisForm ι.1 ι.2)
def rawHessianFn (L k : ℕ) (hL : 0 < L) :
    ((fieldPeriodicData L k hL).Carrier → ℂ) →
      (colourEdges L k 0).Carrier → (colourEdges L k 0).Carrier → ℂ :=
  fun f => rawHessianKernel (gaugeFieldOfCoeffs hL f) (sourceOfCoeffs hL f)
    (coarseOfCoeffs hL f)
def covDiffFn (L k : ℕ) (hL : 0 < L) :
    ((fieldPeriodicData L k hL).Carrier → ℂ) →
      (colourEdges L k 0).Carrier → (colourVertices L k 0).Carrier → ℂ :=
  fun f => covDiffKernel L k 0 (gaugeFieldOfCoeffs hL f)
def averageKernelFn (L k : ℕ) (hL : 0 < L) :
    ((fieldPeriodicData L k hL).Carrier → ℂ) →
      (colourVertices L k k).Carrier → (colourVertices L k 0).Carrier → ℂ :=
  fun f => iterAverageKernel L k (gaugeFieldOfCoeffs hL f)
def covariantAverageFn (L k : ℕ) (hL : 0 < L) :
    ((fieldPeriodicData L k hL).Carrier → ℂ) →
      (colourEdges L k k).Carrier → (colourEdges L k 0).Carrier → ℂ :=
  fun f => iterCovariantKernel L k (gaugeFieldOfCoeffs hL f)
end Tower.FullSpace.FieldValueFunctions
end YangMills.Construction
end
