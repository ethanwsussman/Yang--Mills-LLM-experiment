import YangMills.Construction.RunningCouplingSlope.LeastChainOverAField
import Mathlib
set_option autoImplicit false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open Tower BlockAverages ColdStepAtMirrorFrames
def sideAtStep (L n k j : ℕ) : ℕ := torusSideBelow L (k - (j + 1)) (2 * L ^ n)
def frameAtStep (L n k j : ℕ) : BlockAverages.BlockFrame :=
  TorusFields.torusFrame L j (sideAtStep L n k j)
def topFieldAtStep (a ρ : ℝ) (L n k j : ℕ) (V : TorusFields.TorusField (2 * L ^ n)) :
    (frameAtStep L n k j).GaugeField (frameAtStep L n k j).top :=
  TorusFields.readAtLevel (frameAtStep L n k j) (frameAtStep L n k j).top
    (minimizerBelow a ρ L k (k - (j + 1)) (2 * L ^ n) V)
def chartHessianAtStep (a ρ : ℝ) (L n k j : ℕ) (V : TorusFields.TorusField (2 * L ^ n)) :
    Matrix (ReferenceDensity.ChartCoord (frameAtStep L n k j))
      (ReferenceDensity.ChartCoord (frameAtStep L n k j)) ℝ :=
  ReferenceDensity.chartedHessian a ρ (topFieldAtStep a ρ L n k j V) 0
def minimizerCoordAtStep (a ρ : ℝ) (L n k j : ℕ) (V : TorusFields.TorusField (2 * L ^ n))
    (b : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (frameAtStep L n k j)))) :
    BlockAverages.imaginaryQuaternions :=
  ColdStepAtMirrorFrames.coordsAboveFrame true a ρ 0 (topFieldAtStep a ρ L n k j V) 0 b.1.1 b.1.2
open Classical in
def treeEdges (F : BlockAverages.BlockFrame) : Finset (F.Site F.depth × Fin 4) :=
  (BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells F) F.depth).filter
    BlockAverages.IsAxialTreeBond
abbrev TreeCoord (F : BlockAverages.BlockFrame) : Type := ↥(treeEdges F) × Fin 3
abbrev LevelCoord (F : BlockAverages.BlockFrame) : Type :=
  ReferenceDensity.ChartCoord F ⊕ TreeCoord F
abbrev ChainCoord (L n k : ℕ) : Type := Σ j : Fin k, LevelCoord (frameAtStep L n k j)
abbrev TreeChainCoord (L n k : ℕ) : Type := Σ j : Fin k, TreeCoord (frameAtStep L n k j)
def coordLevel {L n k : ℕ} (e : ChainCoord L n k) : ℕ := e.1
def suTwoComponents (B : Matrices.ComplexMatrix2) : Fin 3 → ℝ :=
  ![(B 0 0).re, -(B 0 1).im, (B 0 1).re]
def imaginaryComponents (w : ℍ[ℝ]) : Fin 3 → ℝ := ![w.imI, w.imJ, w.imK]
variable {L n k : ℕ}
def edgeOfCoords (j : ℕ) {F : BlockAverages.BlockFrame} {l : ℕ} (b : F.Site l × Fin 4) :
    Tower.Edge L n k j :=
  PeriodicLattice.Bond.forwardFrom
    (PeriodicLattice.offsetSite 0 (BlockAverages.siteCoords b.1)) b.2
def levelCoords (j : Fin k) (B : Tower.Edge L n k j → Matrices.ComplexMatrix2) :
    LevelCoord (frameAtStep L n k j) → ℝ
  | .inl i => suTwoComponents (B (edgeOfCoords j i.1.1)) i.2
  | .inr i => suTwoComponents (B (edgeOfCoords j i.1.1)) i.2
def transportCoords (X : ChainPoint L n k) (ξ : LevelForms L n k) : ChainCoord L n k → ℝ :=
  fun e => levelCoords e.1 (tangentTransport X ξ e.1) e.2
def slotOfLevel (ξ : LevelForms L n k) :
    (j : Fin k) → Tower.Edge L n k j → Matrices.ComplexMatrix2
  | ⟨0, _⟩ => ξ.1
  | ⟨m + 1, h⟩ => ξ.2 ⟨m, Nat.lt_of_succ_lt h⟩
def slotCoords (ξ : LevelForms L n k) : ChainCoord L n k → ℝ :=
  fun e => levelCoords e.1 (slotOfLevel ξ e.1) e.2
def expLeftDeriv (w x : ℍ[ℝ]) : ℍ[ℝ] :=
  deriv (fun r : ℝ => NormedSpace.exp (w + r • x) * NormedSpace.exp (-w)) 0
def chartDirection (a ρ : ℝ) (L n k : ℕ) (V : TorusFields.TorusField (2 * L ^ n)) (j : Fin k)
    (x : ReferenceDensity.ChartCoord (frameAtStep L n k j) → ℝ) :
    LevelCoord (frameAtStep L n k j) → ℝ
  | .inl i => imaginaryComponents (expLeftDeriv (minimizerCoordAtStep a ρ L n k j V i.1 : ℍ[ℝ])
      (ColdStepAtMirrorFrames.toImaginary (WithLp.toLp 2 fun c => x (i.1, c)) : ℍ[ℝ])) i.2
  | .inr _ => 0
def IsChartPlusGauge (a ρ : ℝ) (V : TorusFields.TorusField (2 * L ^ n)) (X : ChainPoint L n k)
    (x : (j : Fin k) → ReferenceDensity.ChartCoord (frameAtStep L n k j) → ℝ)
    (v : ChainCoord L n k → ℝ) : Prop :=
  ∀ j : Fin k, ∃ g : Tower.Vertex L n k j → Matrices.ComplexMatrix2,
    g ∈ Tower.vertexFunctionSpace L n k j ∧ Tower.restrictVertexFunction (j + 1) g = 0 ∧
    ∀ e, v ⟨j, e⟩ = chartDirection a ρ L n k V j (x j) e +
      levelCoords j (Tower.covDiff (levelField X j) g) e
end RunningCouplingSlope
end YangMills.Construction
end
