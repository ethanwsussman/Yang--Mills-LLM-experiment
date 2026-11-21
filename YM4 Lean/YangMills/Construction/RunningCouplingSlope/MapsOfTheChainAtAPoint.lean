import YangMills.Construction.RunningCouplingSlope.GaussianNumbersOfTheSoftChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
variable {L n k : ℕ}
def restrictToTopLinear (L n k : ℕ) :
    Tower.vertexFunctionSpace L n k 0 →ₗ[ℝ] Tower.vertexFunctionSpace L n k k :=
  Tower.linearMapWithValues _ _ (Tower.restrictVertexFunction k)
def extendFromTopLinear (L n k : ℕ) :
    Tower.vertexFunctionSpace L n k k →ₗ[ℝ] Tower.vertexFunctionSpace L n k 0 :=
  Tower.linearMapWithValues _ _ Tower.extendByZero
def topCovDiffLinear (W : Tower.Edge L n k k → Matrices.ComplexMatrix2) :
    Tower.vertexFunctionSpace L n k k →ₗ[ℝ] Tower.edgeFormSpace L n k k :=
  Tower.linearMapWithValues _ _ (Tower.covDiff W)
def IsChainDriftMap (X : ChainPoint L n k)
    (T : LevelForms L n k →ₗ[ℝ] Tower.vertexFunctionSpace L n k k) : Prop :=
  ∀ ξ, (T ξ : Tower.Vertex L n k k → Matrices.ComplexMatrix2) = chainDrift X ξ k
def chainDriftMap (X : ChainPoint L n k) : LevelForms L n k →ₗ[ℝ] Tower.vertexFunctionSpace L n k k :=
  Classical.epsilon (IsChainDriftMap X)
def fineSlotTranspose (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) :
    LevelForms L n k →ₗ[ℝ] Tower.vertexFunctionSpace L n k 0 :=
  Tower.covDiffRealTranspose L n k U ∘ₗ LinearMap.fst ℝ _ _
structure ChainLinearMapsAt (X : ChainPoint L n k) : Prop where
  topDeriv_spec : IsTopDeriv X (topDeriv X)
  orbit_spec : IsGaugeOrbitMap X (gaugeOrbitMap X)
  shifted_spec : IsShiftedGaugeMap X (shiftedGaugeMap X)
  drift_spec : IsChainDriftMap X (chainDriftMap X)
  restrict_apply : ∀ l : Tower.vertexFunctionSpace L n k 0,
    (restrictToTopLinear L n k l : Tower.Vertex L n k k → Matrices.ComplexMatrix2) =
      Tower.restrictVertexFunction k (l : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2)
  extend_apply : ∀ g : Tower.vertexFunctionSpace L n k k,
    (extendFromTopLinear L n k g : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) =
      Tower.extendByZero (g : Tower.Vertex L n k k → Matrices.ComplexMatrix2)
  extend_pairing : ∀ (g : Tower.vertexFunctionSpace L n k k) (l : Tower.vertexFunctionSpace L n k 0),
    Tower.traceFinsumPairing (extendFromTopLinear L n k g : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2)
        (l : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) =
      Tower.traceFinsumPairing (g : Tower.Vertex L n k k → Matrices.ComplexMatrix2)
        (restrictToTopLinear L n k l : Tower.Vertex L n k k → Matrices.ComplexMatrix2)
  restrict_extend : ∀ g, restrictToTopLinear L n k (extendFromTopLinear L n k g) = g
  topCovDiff_apply : ∀ g : Tower.vertexFunctionSpace L n k k,
    (topCovDiffLinear (levelField X k) g : Tower.Edge L n k k → Matrices.ComplexMatrix2) =
      Tower.covDiff (levelField X k) (g : Tower.Vertex L n k k → Matrices.ComplexMatrix2)
  topDeriv_surjective : Function.Surjective (topDeriv X)
  topDeriv_orbit : ∀ l, topDeriv X (gaugeOrbitMap X l) =
    topCovDiffLinear (levelField X k) (restrictToTopLinear L n k l)
  mean_eq : ∀ l, composedCubeAverageLinear X l =
    restrictToTopLinear L n k l + chainDriftMap X (gaugeOrbitMap X l)
  mean_transpose : ∃ t : Tower.vertexFunctionSpace L n k k →ₗ[ℝ] Tower.vertexFunctionSpace L n k 0,
    (∀ (g : Tower.vertexFunctionSpace L n k k) (l : Tower.vertexFunctionSpace L n k 0),
      Tower.traceFinsumPairing (t g : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2)
          (l : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) =
        Tower.traceFinsumPairing (g : Tower.Vertex L n k k → Matrices.ComplexMatrix2)
          (composedCubeAverageLinear X l : Tower.Vertex L n k k → Matrices.ComplexMatrix2)) ∧
    ∀ g, composedCubeAverageLinear X (t g) = ((L : ℝ) ^ (4 * k))⁻¹ • g
  mean_extend : ∀ g, composedCubeAverageLinear X (extendFromTopLinear L n k g) =
    ((L : ℝ) ^ (4 * k))⁻¹ • g
  orbit_fst : ∀ l, (gaugeOrbitMap X l).1 = Tower.covDiffLinear L n k X.fine l
  iterTranspose_pairing : ∀ (g : Tower.vertexFunctionSpace L n k k) (l : Tower.vertexFunctionSpace L n k 0),
    Tower.traceFinsumPairing
        (Tower.iterAverageRealTranspose L n k X.fine g : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2)
        (l : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) =
      Tower.traceFinsumPairing (g : Tower.Vertex L n k k → Matrices.ComplexMatrix2)
        (Tower.iterAverageLinear L n k X.fine l : Tower.Vertex L n k k → Matrices.ComplexMatrix2)
  iterAverage_transpose : ∀ g, Tower.iterAverageLinear L n k X.fine
    (Tower.iterAverageRealTranspose L n k X.fine g) = ((L : ℝ) ^ (4 * k))⁻¹ • g
  orbit_injective : Function.Injective (gaugeOrbitMap X ∘ₗ (topVanishingGauges L n k).subtype)
end YangMills.Construction.RunningCouplingSlope
end
