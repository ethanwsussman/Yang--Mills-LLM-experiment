import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators
namespace FullLattice
open Tower.FullSpace
variable {L k j : ℕ}
def contourLeg (y : FullSpace.Vertex L k (j + 1)) (x : FullSpace.Vertex L k j) (π : Equiv.Perm (Fin 4)) :
    List (FullSpace.Edge L k j) :=
  FullSpace.stepsInOrder (FullSpace.cubeOffset L y x) (FullSpace.toFiner (meshAt L k j) y)
    ((List.finRange 4).map π)
def contourHolonomy (V : FullSpace.Edge L k j → Matrices.ComplexMatrix2) (c : FullSpace.Edge L k (j + 1))
    (x : FullSpace.Vertex L k j) (π : Equiv.Perm (Fin 4)) : Matrices.ComplexMatrix2 :=
  FullSpace.linkHolonomy V (contourLeg c.initial x π) * FullSpace.linkHolonomy V (FullSpace.crossingPath c x) *
    (FullSpace.linkHolonomy V (contourLeg c.terminal (FullSpace.shifted c x) π))⁻¹
def contourMean (V : FullSpace.Edge L k j → Matrices.ComplexMatrix2) (c : FullSpace.Edge L k (j + 1)) :
    Matrices.ComplexMatrix2 :=
  ((1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L) •
    ∑ᶠ x ∈ FullSpace.cubeVertices L (meshAt L k j) c.initial, ∑ π : Equiv.Perm (Fin 4), contourHolonomy V c x π
def meanRadius (V : FullSpace.Edge L k j → Matrices.ComplexMatrix2) (c : FullSpace.Edge L k (j + 1)) : ℂ :=
  (Matrix.det (contourMean V c)) ^ (1 / 2 : ℂ)
def normalizedMean (V : FullSpace.Edge L k j → Matrices.ComplexMatrix2) :
    FullSpace.Edge L k (j + 1) → Matrices.ComplexMatrix2 :=
  fun c => (meanRadius V c)⁻¹ • contourMean V c
def meanIterate (U : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) :
    (j : ℕ) → FullSpace.Edge L k j → Matrices.ComplexMatrix2
  | 0 => U
  | j + 1 => open Classical in fun c =>
    if c.IsPositivelyOriented then normalizedMean (meanIterate U j) c
    else (normalizedMean (meanIterate U j) c.opposite)⁻¹
def meanCovariantStep (V B : FullSpace.Edge L k j → Matrices.ComplexMatrix2) :
    FullSpace.Edge L k (j + 1) → Matrices.ComplexMatrix2 :=
  FullSpace.extendOddly (fun c => logDirectionalDeriv ℂ (fun X => normalizedMean (FullSpace.expTwist X V) c)
      (normalizedMean V c) B) +
    FullSpace.covDiff (normalizedMean V) (FullSpace.contourLogDrift V B)
def meanCovariant (U : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) :
    (j : ℕ) → (FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) → FullSpace.Edge L k j → Matrices.ComplexMatrix2
  | 0, B => B
  | j + 1, B => meanCovariantStep (meanIterate U j) (meanCovariant U j B)
def meanCubeAverage (U : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) :
    (j : ℕ) → (FullSpace.Vertex L k 0 → Matrices.ComplexMatrix2) → FullSpace.Vertex L k j → Matrices.ComplexMatrix2
  | 0, l => l
  | j + 1, l => FullSpace.adjointCubeAverage (meanIterate U j) (meanCubeAverage U j l)
def meanKernelQ (L k : ℕ) (U : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) :
    KernelMatrix (Fin 3 × FullSpace.PositiveEdge (meshAt L k 0))
      (Fin 3 × FullSpace.PositiveEdge (meshAt L k k)) :=
  (FullSpace.edgePauliCoordinates L k 0).kernel (FullSpace.edgePauliCoordinates L k k) fun B => finestMesh L k • meanCovariant U k B
def meanKernelR (L k : ℕ) (U : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) :
    KernelMatrix (Fin 3 × FullSpace.Vertex L k 0) (Fin 3 × FullSpace.Vertex L k k) :=
  (vertexCoordinate (FullSpace.Vertex L k 0)).kernel (vertexCoordinate (FullSpace.Vertex L k k)) (meanCubeAverage U k)
def invRadiusDiag (U : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) (j : ℕ) :
    KernelMatrix (Fin 3 × FullSpace.PositiveEdge (meshAt L k (j + 1)))
      (Fin 3 × FullSpace.PositiveEdge (meshAt L k (j + 1))) :=
  open Classical in
  fun ι' ι => if ι' = ι then (meanRadius (meanIterate U j) ι.2.1)⁻¹ else 0
def meanStepKernel (L k : ℕ) (U : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) (j : ℕ) :
    KernelMatrix (Fin 3 × FullSpace.PositiveEdge (meshAt L k j))
      (Fin 3 × FullSpace.PositiveEdge (meshAt L k (j + 1))) :=
  (FullSpace.edgePauliCoordinates L k j).kernel (FullSpace.edgePauliCoordinates L k (j + 1))
    fun B => (L : ℝ)⁻¹ • meanCovariantStep (meanIterate U j) B
def noiseCovariance (a : ℝ) (L k : ℕ) (U : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) :
    (j : ℕ) → KernelMatrix (Fin 3 × FullSpace.PositiveEdge (meshAt L k j))
      (Fin 3 × FullSpace.PositiveEdge (meshAt L k j))
  | 0 => 0
  | j + 1 =>
    ((a⁻¹ : ℝ) : ℂ) • invRadiusDiag U j +
      (((L : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ) •
        compKernel (compKernel (meanStepKernel L k U j) (noiseCovariance a L k U j))
          (meshTranspose (meshAt L k j) (meshAt L k (j + 1))
            (meanStepKernel L k U j))
def edgeSaddle (a : ℝ) (L k : ℕ) (U : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) :
    KernelMatrix (Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) ⊕
        Fin 3 × FullSpace.PositiveEdge (meshAt L k k))
      (Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) ⊕ Fin 3 × FullSpace.PositiveEdge (meshAt L k k)) :=
  fun ι' ι => match ι', ι with
    | .inl i', .inl i => (FullSpace.rescaledOperators L k U).X i' i
    | .inl i', .inr c => meshTranspose (finestMesh L k) (meshAt L k k)
        (meanKernelQ L k U) i' c
    | .inr c', .inl i => meanKernelQ L k U c' i
    | .inr c', .inr c => -noiseCovariance a L k U k c' c
def vertexSaddle (L k : ℕ) (U : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) :
    KernelMatrix (Fin 3 × FullSpace.Vertex L k 0 ⊕ Fin 3 × FullSpace.Vertex L k k)
      (Fin 3 × FullSpace.Vertex L k 0 ⊕ Fin 3 × FullSpace.Vertex L k k) :=
  saddleMatrix (FullSpace.rescaledOperators L k U).Delta (FullSpace.rescaledOperators L k U).Rt (meanKernelR L k U)
def edgeSaddleOfForm (a : ℝ) (L k : ℕ) :
    ((colourEdges L k 0).Carrier → ℂ) → (FullSpace.vectorIndices L k).Carrier →
      (FullSpace.vectorIndices L k).Carrier → ℂ :=
  fun f => edgeSaddle a L k (FullSpace.BackgroundJets.gaugeFieldOfForm L k f)
def vertexSaddleOfForm (L k : ℕ) :
    ((colourEdges L k 0).Carrier → ℂ) → (FullSpace.ghostIndices L k).Carrier →
      (FullSpace.ghostIndices L k).Carrier → ℂ :=
  fun f => vertexSaddle L k (FullSpace.BackgroundJets.gaugeFieldOfForm L k f)
end FullLattice
def edgeIndexProj (L n k : ℕ) (ι : (FullSpace.vectorIndices L k).Carrier) :
    Fin 3 × PositiveEdge L n k 0 ⊕ Fin 3 × PositiveEdge L n k k :=
  Sum.map (fun ι => (ι.1, LocalKernels.projPositiveEdge L n k 0 ι.2))
    (fun ι => (ι.1, LocalKernels.projPositiveEdge L n k k ι.2)) ι
def ghostIndexProj (L n k : ℕ) (ι : (FullSpace.ghostIndices L k).Carrier) :
    Fin 3 × Vertex L n k 0 ⊕ Fin 3 × Vertex L n k k :=
  Sum.map (fun ι => (ι.1, FullSpace.projVertex L n k 0 ι.2))
    (fun ι => (ι.1, FullSpace.projVertex L n k k ι.2)) ι
def PeriodizesTo {L k : ℕ} {I : PeriodicData} {P : Type}
    (T : ((colourEdges L k 0).Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (im : I.Carrier → P)
    (M : Matrix P P ℂ) (s : ℕ) (g : (colourEdges L k 0).QuotMod s → ℂ) : Prop :=
  ∀ ι' ι, periodicValue (colourEdges L k 0) I I T s g ι' ι = M (im ι') (im ι)
end YangMills.Construction.RunningCouplingSlope
end
