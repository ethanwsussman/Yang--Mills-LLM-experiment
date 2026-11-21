import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.Towers.ExponentialConjugatesOfKernelsAndMaps
import YangMills.Construction.Towers.PlaneWaves
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.PeriodicOperators (PeriodicData KernelMatrix colourVertices colourEdges
  colourFaces toComplexVec expConj applyKernel wOpNorm OpNormSummable)
open YangMills.Construction.PeriodicOperators.Quotients (MapsFiniteNorm finiteNormSpace)
namespace SmoothingContraction
def levelIndexData (L k : ℕ) : Fin 3 → ℕ → PeriodicData
  | 0, j => colourVertices L k j
  | 1, j => colourEdges L k j
  | 2, j => colourFaces L k j
def torusPairs (L m k : ℕ) : Fin 3 → ℕ → Type
  | 0, j => Fin 3 × Vertex L m k j
  | 1, j => Fin 3 × PositiveEdge L m k j
  | 2, j => Fin 3 × Face L m k j
def OpNormLE (I I' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ) (c : ℝ) : Prop :=
  MapsFiniteNorm I I' T ∧
    OpNormSummable I.weightOf I'.weightOf (finiteNormSpace I) (applyKernel T) ∧
    wOpNorm I.weightOf I'.weightOf (finiteNormSpace I) (applyKernel T) ≤
      ENNReal.ofReal c
def TorusOpNormLE {σ σ' : Type} (a a' : ℝ) (T : KernelMatrix (Fin 3 × σ) (Fin 3 × σ'))
    (c : ℝ) : Prop :=
  OpNormSummable (meshWeight a) (meshWeight a') univ (applyKernel T) ∧
    wOpNorm (meshWeight a) (meshWeight a') univ (applyKernel T) ≤ ENNReal.ofReal c
def OnFullSpace (L k : ℕ) : Prop :=
  (∀ (i i' : Fin 3) (j j' : ℕ), j ≤ k → j' ≤ k →
    ∀ T : (levelIndexData L k i' j').Carrier → (levelIndexData L k i j).Carrier → ℂ,
      expConj (levelIndexData L k i j) (levelIndexData L k i' j') 0 T = T) ∧
  ∀ θ : InfiniteLattice.AmbientSpace,
    (∀ i : ℕ, i + 1 ≤ k →
      OpNormLE (colourEdges L k i) (colourEdges L k (i + 1))
        (expConjOfMap (IndexedEvaluation.edgeForms L k i) (IndexedEvaluation.edgeForms L k (i + 1)) θ
          fun B => (L : ℝ)⁻¹ • FullSpace.crossingSmoothing L
            (a := meshAt L k (i + 1)) (a' := meshAt L k i) B)
        (Real.exp (2 * TorusMetric.l1NormVec θ * meshAt L k (i + 1))) ∧
      OpNormLE (colourVertices L k i) (colourVertices L k (i + 1))
        (expConjOfMap (IndexedEvaluation.vertices L k i) (IndexedEvaluation.vertices L k (i + 1)) θ
          (FullSpace.vertexSmoothing L (a := meshAt L k (i + 1)) (a' := meshAt L k i)))
        (Real.exp (TorusMetric.l1NormVec θ * meshAt L k (i + 1)))) ∧
    OpNormLE (colourEdges L k 0) (colourEdges L k k)
      (expConj (colourEdges L k 0) (colourEdges L k k) θ
        (FullSpace.rescaledOperators L k fun _ => 1).Q)
      (Real.exp (2 * TorusMetric.l1NormVec θ)) ∧
    OpNormLE (colourVertices L k 0) (colourVertices L k k)
      (expConj (colourVertices L k 0) (colourVertices L k k) θ
        (FullSpace.rescaledOperators L k fun _ => 1).R)
      (Real.exp (TorusMetric.l1NormVec θ))
def OnTorus (L m k : ℕ) : Prop :=
  (∀ (i i' : Fin 3) (j j' : ℕ), j ≤ k → j' ≤ k →
    ∀ T : KernelMatrix (torusPairs L m k i j) (torusPairs L m k i' j'),
      expConjAtZero T = T) ∧
  (∀ i : ℕ, i + 1 ≤ k →
    TorusOpNormLE (meshAt L k i) (meshAt L k (i + 1))
      (expConjOfMapAtZero (edgePauliCoordinates L m k i) (edgePauliCoordinates L m k (i + 1))
        fun B => (L : ℝ)⁻¹ • crossingSmoothing L m k i B)
      (Real.exp (2 * TorusMetric.l1NormVec 0 * meshAt L k (i + 1))) ∧
    TorusOpNormLE (meshAt L k i) (meshAt L k (i + 1))
      (expConjOfMapAtZero (vertexCoordinate (Vertex L m k i))
        (vertexCoordinate (Vertex L m k (i + 1))) (vertexSmoothing L m k i))
      (Real.exp (TorusMetric.l1NormVec 0 * meshAt L k (i + 1)))) ∧
  TorusOpNormLE (finestMesh L k) (meshAt L k k)
    (expConjAtZero (rescaledOperators L m k (trivialField L m k 0)).Q)
    (Real.exp (2 * TorusMetric.l1NormVec 0)) ∧
  TorusOpNormLE (finestMesh L k) (meshAt L k k)
    (expConjAtZero (rescaledOperators L m k (trivialField L m k 0)).R)
    (Real.exp (TorusMetric.l1NormVec 0))
def PlaneWaveSums (L k : ℕ) : Prop :=
  ∀ κ : Fin 4 → ℝ,
    (∀ μ : Fin 4, ∑ w ∈ PlaneWaves.freqBox L k,
      ‖PlaneWaves.edgeWeight L k (PlaneWaves.shiftedFreq (fun ν => (κ ν : ℂ)) w) μ‖ ^ 2 ≤ 1) ∧
    ∑ w ∈ PlaneWaves.freqBox L k,
      PlaneWaves.vertexWeight L k (PlaneWaves.shiftedFreq (fun ν => (κ ν : ℂ)) w) ^ 2 = 1
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    OnFullSpace L k ∧ (∀ m : ℕ, 0 < m → OnTorus L m k) ∧ PlaneWaveSums L k
end SmoothingContraction
end YangMills.Construction.Tower
end
