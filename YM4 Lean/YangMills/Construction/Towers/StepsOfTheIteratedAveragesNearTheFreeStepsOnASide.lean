import YangMills.Construction.Towers.TheConstantOfTheStepsOfTheIteratedAverages
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
open PeriodicOperators (OpNormSummable wOpNorm)
namespace SmoothingStepsNearFree
def MapNormLE (a a' : ℝ) (r r' : PauliComponentsOfSymmetricKernel)
    (f : (r.space.index → Matrices.ComplexMatrix2) → r'.space.index → Matrices.ComplexMatrix2)
    (c : ℝ) : Prop :=
  OpNormSummable (meshWeight a) (meshWeight a') univ (r.mapOnCoeffs r' f) ∧
    wOpNorm (meshWeight a) (meshWeight a') univ (r.mapOnCoeffs r' f) ≤ ENNReal.ofReal c
def distFromOne {L m k j : ℕ} (V : Edge L m k j → Matrices.ComplexMatrix2) : ℝ :=
  (maxOperatorNorm fun b => V b - 1).toReal
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m k j : ℕ, 0 < m → j < k →
    ∀ V ∈ fieldsIn L m k j PeriodicLattice.complexGaugeGroup,
      (∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L / 2) →
      MapNormLE (meshAt L k j) (meshAt L k (j + 1))
          (edgePauliCoordinates L m k j) (edgePauliCoordinates L m k (j + 1))
          (fun B => (L : ℝ)⁻¹ • (covariantSmoothingDeriv V B - crossingSmoothing L m k j B))
          (smoothingStepConstant L * distFromOne V) ∧
        MapNormLE (meshAt L k j) (meshAt L k (j + 1))
          (vertexCoordinate (Vertex L m k j)) (vertexCoordinate (Vertex L m k (j + 1)))
          (fun f => adjointCubeAverage V f - vertexSmoothing L m k j f)
          (smoothingStepConstant L * distFromOne V)
end SmoothingStepsNearFree
end Tower
end YangMills.Construction
end
