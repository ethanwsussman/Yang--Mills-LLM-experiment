import YangMills.Construction.RunningCouplingSlope.PlainCovariantMaps
import YangMills.Construction.RunningCouplingSlope.PlainSaddlesOnTheWholeLattice
import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.LocalKernels YangMills.Construction.LocalKernels.Periodisation
structure MeanChainNearIdentity (ρ : ℝ) (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) : Prop where
  mem_smallIterate : U ∈ smallIterateFields L n k
  mem_smallComplex : ∀ m < k, meanIterate U m ∈ smallComplexFields L n k m
  norm_sub_one_lt : ∀ m < k, ∀ b, Matrices.ComplexMatrix2.operatorNorm (meanIterate U m b - 1) < ρ
  mem_complexGroup : ∀ m ≤ k, meanIterate U m ∈ fieldsIn L n k m PeriodicLattice.complexGaugeGroup
structure MeanChainLifts (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) : Prop where
  iterate_lift : ∀ m ≤ k, FullLattice.meanIterate (liftGaugeField L n k 0 U) m =
    liftGaugeField L n k m (meanIterate U m)
  radius_lift : ∀ m < k, ∀ c : FullSpace.Edge L k (m + 1), c.IsPositivelyOriented →
    FullLattice.meanRadius (FullLattice.meanIterate (liftGaugeField L n k 0 U) m) c =
      meanRadius (meanIterate U m) (FullSpace.projEdge L n k (m + 1) c)
  step_periodizes : ∀ (m : ℕ) (h : m + 1 ≤ k),
    Periodizes L n (CellClass.edgeClass k m (Nat.le_of_succ_le h)) (CellClass.edgeClass k (m + 1) h) 6
      (fun B => (L : ℝ)⁻¹ • FullLattice.meanCovariantStep
        (FullLattice.meanIterate (liftGaugeField L n k 0 U) m) B)
      (fun B => (L : ℝ)⁻¹ • meanCovariantStep (meanIterate U m) B)
  covariant_periodizes : Periodizes L n (edgesAtZero k) (CellClass.edgeClass k k le_rfl) 6
    (fun B => finestMesh L k •
      FullLattice.meanCovariant (liftGaugeField L n k 0 U) k B)
    (fun B => finestMesh L k • meanCovariant U k B)
  cubeAverage_periodizes : Periodizes L n (verticesAtZero k) (CellClass.vertexClass k k le_rfl) 6
    (FullLattice.meanCubeAverage (liftGaugeField L n k 0 U) k)
    (composedCubeAverage (quietPoint U) k)
def MeanChainLiftsNearIdentity : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ U : Edge L n k 0 → Matrices.ComplexMatrix2, MeanChainNearIdentity ρ L n k U → MeanChainLifts L n k U
end YangMills.Construction.RunningCouplingSlope
end
