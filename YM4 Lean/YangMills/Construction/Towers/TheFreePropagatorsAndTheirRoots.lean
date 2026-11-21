import YangMills.Construction.PeriodicOperators.SymbolsOnStrips
import YangMills.Construction.Towers.MatricesThatMultiplyTheCoefficients
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace FreeResolvents
open PeriodicOperators
open PeriodicOperators.StripSymbols (openStripInterior)
open Tower.PlaneWaves
def IsRightHalfPlaneArg (z : ℂ) (φ : ℝ) : Prop :=
  φ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧ z = (‖z‖ : ℂ) * Complex.exp (Complex.I * φ)
def rightHalfPlaneArg (z : ℂ) : ℝ := Classical.epsilon (IsRightHalfPlaneArg z)
def principalRpow (σ : ℝ) (z : ℂ) : ℂ :=
  ((‖z‖ ^ σ : ℝ) : ℂ) * Complex.exp (Complex.I * σ * rightHalfPlaneArg z)
def resolventExponents : Set ℝ := {-1, -(1 / 2), 1 / 2}
def shiftedSymbolPow (L k : ℕ) (σ : ℝ) (q : Fin 4 → ℂ) : ℂ :=
  principalRpow σ (symbolSquare L k q + 1)
def vertexPowMatrix (L k : ℕ) (σ : ℝ) (κ : Fin 4 → ℂ) :
    QuotHom (colourVertices L k 0) (colourVertices L k 0) :=
  vertexFourierMultiplier L k (shiftedSymbolPow L k σ) κ
def edgePowMatrix (L k : ℕ) (σ : ℝ) (κ : Fin 4 → ℂ) :
    QuotHom (colourEdges L k 0) (colourEdges L k 0) :=
  edgeFourierMultiplier L k (shiftedSymbolPow L k σ) κ
def trivialRescaledOperators (L k : ℕ) :=
  Tower.FullSpace.rescaledOperators L k fun _ => 1
def edgeOperatorAddOne (L k : ℕ) :
    (colourEdges L k 0).Carrier → (colourEdges L k 0).Carrier → ℂ :=
  fun a b => (trivialRescaledOperators L k).K a b + idKernel (colourEdges L k 0) a b
def vertexOperatorAddOne (L k : ℕ) :
    (colourVertices L k 0).Carrier → (colourVertices L k 0).Carrier → ℂ :=
  fun a b => (trivialRescaledOperators L k).Delta a b + idKernel (colourVertices L k 0) a b
structure PowerMatrixFacts (I : PeriodicData) (Scales : ℝ → (Fin 4 → ℂ) → QuotHom I I → Prop)
    (M : ℝ → (Fin 4 → ℂ) → QuotHom I I) (P : I.Carrier → I.Carrier → ℂ) : Prop where
  scales_unique : ∀ σ ∈ resolventExponents, ∀ κ ∈ imStrip (1 / 8),
    Scales σ κ (M σ κ) ∧ ∀ A, Scales σ κ A → A = M σ κ
  holomorphicOn : ∀ σ ∈ resolventExponents,
    QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior (1 / 8)) (M σ)
  boundedOn : ∀ σ ∈ resolventExponents, QuotHomFamilyBoundedOn (openStripInterior (1 / 8)) (M σ)
  quasiPeriodic : ∀ σ ∈ resolventExponents, IsQuasiPeriodic (imStrip (1 / 8)) (M σ)
  continuousOn : ∀ σ ∈ resolventExponents, QuotHomFamilyContinuousOn (n := 4) realDualPoints (M σ)
  periodic : ∀ σ ∈ resolventExponents, IsPeriodicKernel I I (matFunKernel I I (M σ))
  im_eq_zero : ∀ σ ∈ resolventExponents, ∀ a b, (matFunKernel I I (M σ) a b).im = 0
  transpose_eq : ∀ σ ∈ resolventExponents,
    kernelTranspose I I (matFunKernel I I (M σ)) = matFunKernel I I (M σ)
  symbol_invertible : IsPeriodicKernel I I P ∧ SymbolSummableOn I I P realDualPoints ∧
    SymbolInvertibleOnReals I P
  inverse_eq : periodicInverse I P = matFunKernel I I (M (-1))
  inv_comp : (∀ a b, CompSummableAt (matFunKernel I I (M (-1))) P a b) ∧
    compKernel (matFunKernel I I (M (-1))) P = idKernel I
  comp_inv : (∀ a b, CompSummableAt P (matFunKernel I I (M (-1))) a b) ∧
    compKernel P (matFunKernel I I (M (-1))) = idKernel I
  invSqrt_comp_invSqrt : (∀ a b, CompSummableAt (matFunKernel I I (M (-(1 / 2))))
      (matFunKernel I I (M (-(1 / 2)))) a b) ∧
    compKernel (matFunKernel I I (M (-(1 / 2))))
      (matFunKernel I I (M (-(1 / 2)))) = matFunKernel I I (M (-1))
  sqrt_comp_invSqrt : (∀ a b, CompSummableAt (matFunKernel I I (M (1 / 2)))
      (matFunKernel I I (M (-(1 / 2)))) a b) ∧
    compKernel (matFunKernel I I (M (1 / 2)))
      (matFunKernel I I (M (-(1 / 2)))) = idKernel I
def FreeResolventRoots : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ κ ∈ imStrip (1 / 8), ∀ p ∈ freqBox L k,
      (9 / 10 : ℝ) ≤ (symbolSquare L k (shiftedFreq κ p) + 1).re) ∧
    (∀ z : ℂ, 0 < z.re → ∃! φ : ℝ, IsRightHalfPlaneArg z φ) ∧
    IsNhdOf IsOpen (imStrip (1 / 9)) (openStripInterior (1 / 8)) ∧
    PowerMatrixFacts (colourEdges L k 0)
      (fun σ κ A => ScalesEdgeCoeffs L k (shiftedSymbolPow L k σ) κ A)
      (edgePowMatrix L k) (edgeOperatorAddOne L k) ∧
    PowerMatrixFacts (colourVertices L k 0)
      (fun σ κ A => ScalesVertexCoeffs L k (shiftedSymbolPow L k σ) κ A)
      (vertexPowMatrix L k) (vertexOperatorAddOne L k) ∧
    (∀ σ ∈ resolventExponents, Tower.IsColourTrivial
      (matFunKernel (colourEdges L k 0) (colourEdges L k 0) (edgePowMatrix L k σ))) ∧
    ∀ σ ∈ resolventExponents, Tower.IsColourTrivial
      (matFunKernel (colourVertices L k 0) (colourVertices L k 0) (vertexPowMatrix L k σ))
end FreeResolvents
end Tower
end YangMills.Construction
end
