import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import YangMills.Construction.Towers.TheInversesThatFormTheResponse
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace ResponseOperators
open YangMills.Construction.PeriodicOperators
open FreeResolvents (trivialRescaledOperators)
open FreeStrip (edges topEdges)
open BackgroundFieldResponse (blockCovariance responseKernel responseDefect)
open ResponseInverses (IsInverseRadius SymbolsSummable blockCovarianceHat xiHat)
open PlaneWaveCalculus (IsRealColourTrivial)
open YangMills.Construction.TorusMetric (l1NormVec)
open YangMills.Construction.LocalKernels (projPositiveEdge)
open YangMills.Construction.LocalKernels.Periodisation (periodSide)
def covSymbol (L k : ℕ) (κ : Fin 4 → ℂ) : QuotHom (topEdges L k) (topEdges L k) :=
  symbolHom (topEdges L k) (topEdges L k) (blockCovariance L k) κ
def respSymbol (L k : ℕ) (κ : Fin 4 → ℂ) : QuotHom (topEdges L k) (edges L k) :=
  symbolHom (topEdges L k) (edges L k) (responseKernel L k) κ
def defectSymbol (L k : ℕ) (κ : Fin 4 → ℂ) : QuotHom (topEdges L k) (topEdges L k) :=
  symbolHom (topEdges L k) (topEdges L k) (responseDefect L k) κ
structure ResponseSymbolsOn (L k : ℕ) (O : Set (Fin 4 → ℂ)) : Prop where
  cov_summable : SymbolSummableOn (topEdges L k) (topEdges L k) (blockCovariance L k) O
  resp_summable : SymbolSummableOn (topEdges L k) (edges L k) (responseKernel L k) O
  defect_summable : SymbolSummableOn (topEdges L k) (topEdges L k) (responseDefect L k) O
  xi_isInvertible : ∀ κ ∈ O, IsInvertibleQuotHom (xiHat L k κ)
  cov_isInvertible : ∀ κ ∈ O, IsInvertibleQuotHom (covSymbol L k κ)
  cov_eq : ∀ κ ∈ O, covSymbol L k κ = blockCovarianceHat L k κ
  resp_eq : ∀ κ ∈ O, respSymbol L k κ =
    (quotHomInverse (xiHat L k κ)).comp
      ((symbolHom (topEdges L k) (edges L k) (trivialRescaledOperators L k).Qt κ).comp
        (quotHomInverse (covSymbol L k κ)))
  defect_eq : ∀ κ ∈ O, defectSymbol L k κ =
    quotHomInverse (covSymbol L k κ) - LinearMap.id
  cov_holomorphic : QuotHomFamilyHolomorphicOn (n := 4) O (covSymbol L k)
  resp_holomorphic : QuotHomFamilyHolomorphicOn (n := 4) O (respSymbol L k)
  defect_holomorphic : QuotHomFamilyHolomorphicOn (n := 4) O (defectSymbol L k)
  cov_bounded : QuotHomFamilyBoundedOn O (covSymbol L k)
  resp_bounded : QuotHomFamilyBoundedOn O (respSymbol L k)
  defect_bounded : QuotHomFamilyBoundedOn O (defectSymbol L k)
structure HasDecayRate (I I' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ) (υ : ℝ) : Prop where
  bound : ∃ c : ℝ, ∀ x' x,
    ‖T x' x‖ ≤ c * Real.exp (-υ * l1NormVec (I.pos x - I'.pos x'))
  summable : SymbolSummableOn I I' T (openImStrip υ)
  applyKernel_blochWave : ∀ κ ∈ openImStrip υ, ∀ (φ : I.UnitQuot → ℂ) x',
    ApplySummableAt T (blochWave I κ φ) x' ∧
      applyKernel T (blochWave I κ φ) x' =
        blochWave I' κ (applyKernel (quotSymbol I I' T κ) φ) x'
def IsResponseRate (δ₀ : ℝ) (L k : ℕ) (υ : ℝ) : Prop :=
  2 * δ₀ < υ ∧ HasDecayRate (topEdges L k) (topEdges L k) (blockCovariance L k) υ ∧
    HasDecayRate (topEdges L k) (edges L k) (responseKernel L k) υ ∧
    HasDecayRate (topEdges L k) (topEdges L k) (responseDefect L k) υ
def MapsLieFormsToLieForms {σ σ' : Type} (T : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')) : Prop :=
  ∀ f ∈ Matrices.GroupLieProduct.hermitianTracelessFunctions σ,
    (∀ x', ApplySummableAt T (toPauliCoeffs f) x') →
      ofPauliCoeffs (applyKernel T (toPauliCoeffs f)) ∈
        Matrices.GroupLieProduct.hermitianTracelessFunctions σ'
def ClassFnEqForm (L n k j : ℕ) (f : PositiveEdge L n k j → Matrices.ComplexMatrix2)
    (g : (colourEdges L k j).QuotMod (periodSide L n) → ℂ) : Prop :=
  ∀ x : (colourEdges L k j).Carrier,
    g ((colourEdges L k j).mkQuot (periodSide L n) x) =
      toPauliCoeffs f (x.1, projPositiveEdge L n k j x.2)
def ClassFnsAreForms (L n k j : ℕ) : Prop :=
  ∀ g : (colourEdges L k j).QuotMod (periodSide L n) → ℂ,
    ∃! f : PositiveEdge L n k j → Matrices.ComplexMatrix2,
      f ∈ Matrices.GroupLieProduct.tracelessFunctions (PositiveEdge L n k j) ∧
        ClassFnEqForm L n k j f g
structure PeriodicMatrixPreservesLieForms (L n k i j : ℕ)
    (T : (colourEdges L k j).Carrier → (colourEdges L k i).Carrier → ℂ) : Prop where
  summable : ∀ x' x,
    PeriodizationSummableAt (colourEdges L k i) (colourEdges L k j) T (periodSide L n) x' x
  factorsThroughQuot : ∀ x₁' x₂' x₁ x₂,
    (colourEdges L k j).mkQuot (periodSide L n) x₁' =
        (colourEdges L k j).mkQuot (periodSide L n) x₂' →
      (colourEdges L k i).mkQuot (periodSide L n) x₁ =
        (colourEdges L k i).mkQuot (periodSide L n) x₂ →
      periodization (colourEdges L k i) (colourEdges L k j) T (periodSide L n) x₁' x₁ =
        periodization (colourEdges L k i) (colourEdges L k j) T (periodSide L n) x₂' x₂
  preserves_lie_forms : ∀ f ∈ Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k i),
    ∀ g, ClassFnEqForm L n k i f g →
      ∃ f' ∈ Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k j),
        ClassFnEqForm L n k j f'
          (applyKernel
            (periodicMatrix (colourEdges L k i) (colourEdges L k j) T (periodSide L n)) g)
structure TorusSideFacts (L n k : ℕ) : Prop where
  forms_top : ClassFnsAreForms L n k k
  forms_bottom : ClassFnsAreForms L n k 0
  cov : PeriodicMatrixPreservesLieForms L n k k k (blockCovariance L k)
  resp : PeriodicMatrixPreservesLieForms L n k k 0 (responseKernel L k)
  defect : PeriodicMatrixPreservesLieForms L n k k k (responseDefect L k)
structure AtLevel (δ₀ : ℝ) (L k : ℕ) : Prop where
  cov_periodic : IsPeriodicKernel (topEdges L k) (topEdges L k) (blockCovariance L k)
  resp_periodic : IsPeriodicKernel (topEdges L k) (edges L k) (responseKernel L k)
  defect_periodic : IsPeriodicKernel (topEdges L k) (topEdges L k) (responseDefect L k)
  free_summable : SymbolsSummable L k
  near : ExistsOpenNear IsOpen (imStrip (2 * δ₀)) (ResponseSymbolsOn L k)
  exists_rate : ∃ υ, IsResponseRate δ₀ L k υ
  rate_of_inverseRadius : ∀ υ, IsInverseRadius δ₀ L k υ → IsResponseRate δ₀ L k υ
  cov_real : IsRealColourTrivial (blockCovariance L k)
  resp_real : IsRealColourTrivial (responseKernel L k)
  defect_real : IsRealColourTrivial (responseDefect L k)
  cov_lie : MapsLieFormsToLieForms (blockCovariance L k)
  resp_lie : MapsLieFormsToLieForms (responseKernel L k)
  defect_lie : MapsLieFormsToLieForms (responseDefect L k)
  torus_sides : ∀ n : ℕ, 0 < n → TorusSideFacts L n k
def Claim : Prop :=
  ∃ δ₀ ∈ FreeStrip.halfSupRate, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ k : ℕ, 1 ≤ k → AtLevel δ₀ L k
end ResponseOperators
end Tower
end YangMills.Construction
end
