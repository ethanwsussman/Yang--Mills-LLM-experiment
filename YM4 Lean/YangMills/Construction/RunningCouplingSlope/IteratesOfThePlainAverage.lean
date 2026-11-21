import YangMills.Construction.RunningCouplingSlope.PlainCovariantMaps
import YangMills.Construction.Towers.IteratedAveragesOfSmallRegularFields
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
variable {L n k j : ℕ}
namespace PlainMeanIterates
structure PointwiseConditions (L n k : ℕ) (C : ℝ) (v : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) : Prop where
  exists_log : ∀ j ≤ k, ∃ A ∈ Tower.complexEdgeForms L n k j,
    meanIterate (Tower.remainderGaugeField v) j =
        PeriodicLattice.expTwist A (fun _ => 1) ∧
      Tower.maxOperatorNorm A ≤
        ENNReal.ofReal (10 * Tower.meshAt L k j * (Tower.maxOperatorNorm v).toReal)
  mem_small : ∀ j < k, meanIterate (Tower.remainderGaugeField v) j ∈ Tower.smallComplexFields L n k j
  radius_inv_le : ∀ j < k, ∀ c : Tower.Edge L n k (j + 1),
    meanRadius (meanIterate (Tower.remainderGaugeField v) j) c ≠ 0 ∧
      ‖(meanRadius (meanIterate (Tower.remainderGaugeField v) j) c)⁻¹‖ ≤ C
  opNorm_Q : Tower.SmoothingContraction.TorusOpNormLE (Tower.finestMesh L k) (Tower.meshAt L k k)
    (meanKernelQ L n k (Tower.remainderGaugeField v)) C
  opNorm_R : Tower.SmoothingContraction.TorusOpNormLE (Tower.finestMesh L k) (Tower.meshAt L k k)
    (meanKernelR L n k (Tower.remainderGaugeField v)) C
  opNorm_from : ∀ s m : ℕ, s + m = k →
    Tower.SmoothingContraction.TorusOpNormLE (Tower.meshAt L k s) (Tower.meshAt L k k)
      (meanKernelFrom L n k (Tower.remainderGaugeField v) s m) C
structure HolomorphicDependence (L n k : ℕ) (ρ : ℝ) : Prop where
  entries_iterate : ∀ j ≤ k, ∀ b : Tower.Edge L n k j,
    Tower.IteratedSmallFieldMeans.HolomorphicInEntries Coordinates.ComplexCoordinates.matrixEquiv
      (Tower.complexEdgeForms L n k 0 : Set _) ρ
      fun v => meanIterate (Tower.remainderGaugeField v) j b
  kernel_Q : ∀ ι' ι, Tower.IteratedSmallFieldMeans.HolomorphicInEntries Tower.LeftChartFields.scalarCoords
    (Tower.complexEdgeForms L n k 0 : Set _) ρ
    fun v => meanKernelQ L n k (Tower.remainderGaugeField v) ι' ι
  kernel_R : ∀ ι' ι, Tower.IteratedSmallFieldMeans.HolomorphicInEntries Tower.LeftChartFields.scalarCoords
    (Tower.complexEdgeForms L n k 0 : Set _) ρ
    fun v => meanKernelR L n k (Tower.remainderGaugeField v) ι' ι
structure Locality (L n k : ℕ) (ρ : ℝ) : Prop where
  local_Q : ∀ c : Tower.Edge L n k k,
    ∀ v ∈ Tower.IteratedSmallFieldMeans.smallFormBall L n k ρ,
    ∀ v' ∈ Tower.IteratedSmallFieldMeans.smallFormBall L n k ρ,
    ∀ B ∈ Tower.complexEdgeForms L n k 0, ∀ B' ∈ Tower.complexEdgeForms L n k 0,
      EqOn v v' (Tower.edgesOverEdge c) → EqOn B B' (Tower.edgesOverEdge c) →
        meanCovariant (Tower.remainderGaugeField v) k B c =
          meanCovariant (Tower.remainderGaugeField v') k B' c
  local_R : ∀ y : Tower.Vertex L n k k,
    ∀ v ∈ Tower.IteratedSmallFieldMeans.smallFormBall L n k ρ,
    ∀ v' ∈ Tower.IteratedSmallFieldMeans.smallFormBall L n k ρ,
    ∀ l l' : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2,
      (∀ x, l x ∈ PeriodicLattice.complexLieAlgebra) → (∀ x, l' x ∈ PeriodicLattice.complexLieAlgebra) →
      (∀ x : Tower.Vertex L n k 0, (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k y →
        l x = l' x) →
      EqOn v v' (PeriodicLattice.bondsInside (PeriodicLattice.refinedBlock k y)) →
        composedCubeAverage (quietPoint (Tower.remainderGaugeField v)) k l y =
          composedCubeAverage (quietPoint (Tower.remainderGaugeField v')) k l' y
  local_radius : ∀ j < k, ∀ c : Tower.Edge L n k (j + 1),
    ∀ v ∈ Tower.IteratedSmallFieldMeans.smallFormBall L n k ρ,
    ∀ v' ∈ Tower.IteratedSmallFieldMeans.smallFormBall L n k ρ,
      EqOn v v' (PeriodicLattice.bondsInside
        (PeriodicLattice.refinedBlock (j + 1) c.source ∪ PeriodicLattice.refinedBlock (j + 1) c.target)) →
        meanRadius (meanIterate (Tower.remainderGaugeField v) j) c =
          meanRadius (meanIterate (Tower.remainderGaugeField v') j) c
structure TorusConditions (L n k : ℕ) (ρ C : ℝ) : Prop where
  pointwise : ∀ v ∈ Tower.IteratedSmallFieldMeans.smallFormBall L n k ρ, PointwiseConditions L n k C v
  holomorphic : HolomorphicDependence L n k ρ
  locality : Locality L n k ρ
end PlainMeanIterates
def PlainMeanIterates.Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ C : ℝ, 0 < ρ ∧ 1 ≤ C ∧
    ∀ k n : ℕ, 1 ≤ k → 0 < n → PlainMeanIterates.TorusConditions L n k ρ C
end YangMills.Construction.RunningCouplingSlope
end
