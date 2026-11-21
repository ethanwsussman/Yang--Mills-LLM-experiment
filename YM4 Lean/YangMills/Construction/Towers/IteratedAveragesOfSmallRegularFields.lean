import YangMills.Construction.Towers.AveragesAreContractions
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.TheSettingOfTheRemainder
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace Tower
open YangMills.Construction.PeriodicOperators (colourEdges colourVertices)
open YangMills.Construction.Tower.SmoothingContraction (OpNormLE TorusOpNormLE)
open YangMills.Construction.Tower.LeftChartFields (scalarCoords)
namespace IteratedSmallFieldMeans
def HolomorphicInEntries {β E : Type} {l : ℕ} (e : E ≃ Coordinates.ComplexCoordinates l)
    (formSet : Set (β → Matrices.ComplexMatrix2)) (ρ : ℝ) (v : (β → Matrices.ComplexMatrix2) → E) :
    Prop :=
  ∃ (F : Finset β) (f : (F → Matrices.ComplexMatrix2) → E),
    (∀ basis : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
      Matrices.GroupLieProduct.IsHolomorphicOnTraceless basis e
        (Matrices.GroupLieProduct.supBall F ρ) f) ∧
    ∀ A ∈ formSet, maxOperatorNorm A < ENNReal.ofReal ρ → f (fun x => A x) = v A
section FiniteSide
variable {L n k : ℕ}
def meanIterate (j : ℕ) (A : Edge L n k 0 → Matrices.ComplexMatrix2) :
    Edge L n k j → Matrices.ComplexMatrix2 :=
  PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField A)
def smallFormBall (L n k : ℕ) (ρ : ℝ) : Set (Edge L n k 0 → Matrices.ComplexMatrix2) :=
  {A | A ∈ complexEdgeForms L n k 0 ∧ maxOperatorNorm A ≤ ENNReal.ofReal ρ}
def rescaledCovMean (U B : Edge L n k 0 → Matrices.ComplexMatrix2) :
    Edge L n k k → Matrices.ComplexMatrix2 :=
  finestMesh L k • iterCovariantDeriv L n k U k B
structure PointwiseConditions (L n k : ℕ) (C : ℝ) (A : Edge L n k 0 → Matrices.ComplexMatrix2) :
    Prop where
  mem_fields : ∀ j ≤ k, meanIterate j A ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup
  mem_polydisc : ∀ j < k, ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    meanIterate j A ∈ nearIdentityPolydisc (polydiscRadius L) c
  norm_sub_one_le : ∀ j ≤ k, ∀ e : Edge L n k j,
    Matrices.ComplexMatrix2.operatorNorm (meanIterate j A e - 1) ≤
      C * meshAt L k j * (maxOperatorNorm A).toReal
  norm_sub_one_lt_half : ∀ j ≤ k, ∀ e : Edge L n k j,
    Matrices.ComplexMatrix2.operatorNorm (meanIterate j A e - 1) < polydiscRadius L / 2
  mem_smallIterate : remainderGaugeField A ∈ smallIterateFields L n k
  opNorm_Q : TorusOpNormLE (finestMesh L k) (meshAt L k k)
    (rescaledOperators L n k (remainderGaugeField A)).Q C
  opNorm_R : TorusOpNormLE (finestMesh L k) (meshAt L k k)
    (rescaledOperators L n k (remainderGaugeField A)).R C
structure HolomorphicDependence (L n k : ℕ) (ρ : ℝ) : Prop where
  entries_iterate : ∀ j ≤ k, ∀ e : Edge L n k j,
    HolomorphicInEntries Coordinates.ComplexCoordinates.matrixEquiv
      (complexEdgeForms L n k 0 : Set _) ρ fun A => meanIterate j A e
  kernel_Q : ∀ i' i, HolomorphicInEntries scalarCoords (complexEdgeForms L n k 0 : Set _) ρ
    fun A => (rescaledOperators L n k (remainderGaugeField A)).Q i' i
  kernel_R : ∀ i' i, HolomorphicInEntries scalarCoords (complexEdgeForms L n k 0 : Set _) ρ
    fun A => (rescaledOperators L n k (remainderGaugeField A)).R i' i
structure Locality (L n k : ℕ) (ρ : ℝ) : Prop where
  local_Q : ∀ c : Edge L n k k, ∀ A ∈ smallFormBall L n k ρ, ∀ A' ∈ smallFormBall L n k ρ,
    ∀ B ∈ complexEdgeForms L n k 0, ∀ B' ∈ complexEdgeForms L n k 0,
      EqOn A A' (edgesOverEdge c) → EqOn B B' (edgesOverEdge c) →
        rescaledCovMean (remainderGaugeField A) B c =
          rescaledCovMean (remainderGaugeField A') B' c
  local_R : ∀ y : Vertex L n k k, ∀ A ∈ smallFormBall L n k ρ, ∀ A' ∈ smallFormBall L n k ρ,
    ∀ φ φ' : Vertex L n k 0 → Matrices.ComplexMatrix2,
      (∀ x, φ x ∈ PeriodicLattice.complexLieAlgebra) →
      (∀ x, φ' x ∈ PeriodicLattice.complexLieAlgebra) →
      (∀ x : Vertex L n k 0, (x : PeriodicLattice.FourTorus L n) ∈
        PeriodicLattice.refinedBlock k y → φ x = φ' x) →
      EqOn A A' (PeriodicLattice.bondsInside (PeriodicLattice.refinedBlock k y)) →
        iterAdjointCubeAverage L n k (remainderGaugeField A) k φ y =
          iterAdjointCubeAverage L n k (remainderGaugeField A') k φ' y
structure TorusConditions (L n k : ℕ) (ρ C : ℝ) : Prop where
  pointwise : ∀ A ∈ smallFormBall L n k ρ, PointwiseConditions L n k C A
  holomorphic : HolomorphicDependence L n k ρ
  locality : Locality L n k ρ
end FiniteSide
end IteratedSmallFieldMeans
namespace FullSpace.IteratedSmallFieldMeans
open YangMills.Construction.Tower.IteratedSmallFieldMeans (HolomorphicInEntries)
section Infinite
variable {L k : ℕ}
def meanIterate (j : ℕ) (A : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) :
    FullSpace.Edge L k j → Matrices.ComplexMatrix2 :=
  FullSpace.complexIter L k j (FullSpace.remainderGaugeField A)
def smallFormBall (L k : ℕ) (ρ : ℝ) : Set (FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) :=
  {A | A ∈ FullSpace.complexEdgeForms (meshAt L k 0) ∧ maxOperatorNorm A ≤ ENNReal.ofReal ρ}
def rescaledCovMean (U B : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) :
    FullSpace.Edge L k k → Matrices.ComplexMatrix2 :=
  finestMesh L k • FullSpace.iterCovariantDeriv L k U k B
structure PointwiseConditions (L k : ℕ) (C : ℝ) (A : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) :
    Prop where
  mem_fields : ∀ j ≤ k,
    meanIterate j A ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup
  mem_polydisc : ∀ j < k, ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
    meanIterate j A ∈ FullSpace.nearIdentityPolydisc L k j (polydiscRadius L) c
  norm_sub_one_le : ∀ j ≤ k, ∀ e : FullSpace.Edge L k j,
    Matrices.ComplexMatrix2.operatorNorm (meanIterate j A e - 1) ≤
      C * meshAt L k j * (maxOperatorNorm A).toReal
  norm_sub_one_lt_half : ∀ j ≤ k, ∀ e : FullSpace.Edge L k j,
    Matrices.ComplexMatrix2.operatorNorm (meanIterate j A e - 1) < polydiscRadius L / 2
  mem_smallIterate : FullSpace.remainderGaugeField A ∈ FullSpace.smallIterateFields L k
  opNorm_Q : OpNormLE (colourEdges L k 0) (colourEdges L k k)
    (FullSpace.rescaledOperators L k (FullSpace.remainderGaugeField A)).Q C
  opNorm_R : OpNormLE (colourVertices L k 0) (colourVertices L k k)
    (FullSpace.rescaledOperators L k (FullSpace.remainderGaugeField A)).R C
structure HolomorphicDependence (L k : ℕ) (ρ : ℝ) : Prop where
  entries_iterate : ∀ j ≤ k, ∀ e : FullSpace.Edge L k j,
    HolomorphicInEntries Coordinates.ComplexCoordinates.matrixEquiv
      (FullSpace.complexEdgeForms (meshAt L k 0) : Set _) ρ fun A => meanIterate j A e
  kernel_Q : ∀ i' i, HolomorphicInEntries scalarCoords
    (FullSpace.complexEdgeForms (meshAt L k 0) : Set _) ρ
    fun A => (FullSpace.rescaledOperators L k (FullSpace.remainderGaugeField A)).Q i' i
  kernel_R : ∀ i' i, HolomorphicInEntries scalarCoords
    (FullSpace.complexEdgeForms (meshAt L k 0) : Set _) ρ
    fun A => (FullSpace.rescaledOperators L k (FullSpace.remainderGaugeField A)).R i' i
def cubeEdges (y : FullSpace.Vertex L k k) : Set (FullSpace.Edge L k 0) :=
  {e | (e.initial : InfiniteLattice.AmbientSpace) ∈ FullSpace.cubeOfOrder L (meshAt L k 0) k y ∧
    (e.terminal : InfiniteLattice.AmbientSpace) ∈ FullSpace.cubeOfOrder L (meshAt L k 0) k y}
structure Locality (L k : ℕ) (ρ : ℝ) : Prop where
  local_Q : ∀ c : FullSpace.Edge L k k, ∀ A ∈ smallFormBall L k ρ, ∀ A' ∈ smallFormBall L k ρ,
    ∀ B ∈ FullSpace.complexEdgeForms (meshAt L k 0),
    ∀ B' ∈ FullSpace.complexEdgeForms (meshAt L k 0),
      EqOn A A' (FullSpace.edgesOverEdge c) → EqOn B B' (FullSpace.edgesOverEdge c) →
        rescaledCovMean (FullSpace.remainderGaugeField A) B c =
          rescaledCovMean (FullSpace.remainderGaugeField A') B' c
  local_R : ∀ y : FullSpace.Vertex L k k, ∀ A ∈ smallFormBall L k ρ, ∀ A' ∈ smallFormBall L k ρ,
    ∀ φ φ' : FullSpace.Vertex L k 0 → Matrices.ComplexMatrix2,
      (∀ x, φ x ∈ PeriodicLattice.complexLieAlgebra) →
      (∀ x, φ' x ∈ PeriodicLattice.complexLieAlgebra) →
      (∀ x : FullSpace.Vertex L k 0, (x : InfiniteLattice.AmbientSpace) ∈
        FullSpace.cubeOfOrder L (meshAt L k 0) k y → φ x = φ' x) →
      EqOn A A' (cubeEdges y) →
        FullSpace.iterAdjointCubeAverage L k (FullSpace.remainderGaugeField A) k φ y =
          FullSpace.iterAdjointCubeAverage L k (FullSpace.remainderGaugeField A') k φ' y
structure FullConditions (L k : ℕ) (ρ C : ℝ) : Prop where
  pointwise : ∀ A ∈ smallFormBall L k ρ, PointwiseConditions L k C A
  holomorphic : HolomorphicDependence L k ρ
  locality : Locality L k ρ
end Infinite
end FullSpace.IteratedSmallFieldMeans
namespace IteratedSmallFieldMeans
def AdmissibleConstants (L : ℕ) (ρ C : ℝ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 ∧ 1 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
    (∀ n : ℕ, 0 < n → TorusConditions L n k ρ C) ∧ FullSpace.IteratedSmallFieldMeans.FullConditions L k ρ C
def chosenConstants (L : ℕ) : ℝ × ℝ := Classical.epsilon fun p => AdmissibleConstants L p.1 p.2
def smallRadius (L : ℕ) : ℝ := (chosenConstants L).1
def boundConstant (L : ℕ) : ℝ := (chosenConstants L).2
def IteratedMeansClaim : Prop :=
  (∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    AdmissibleConstants L (smallRadius L) (boundConstant L)) ∧
  ∀ (D : Type) (m : D → ℕ),
    IsRemainderConst m (fun d => smallRadius (m d)) ∧ IsRemainderConst m (fun d => boundConstant (m d))
end IteratedSmallFieldMeans
end Tower
end YangMills.Construction
end
