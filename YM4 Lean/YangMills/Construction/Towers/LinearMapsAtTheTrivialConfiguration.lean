import YangMills.Construction.Towers.FormsOnTowers
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace Tower
def maxOperatorNorm {ι : Type*} (f : ι → Matrices.ComplexMatrix2) : ℝ≥0∞ :=
  ⨆ i, ENNReal.ofReal (Matrices.ComplexMatrix2.operatorNorm (f i))
def composeFromZero {F : ℕ → Type*} (step : ∀ j, F j → F (j + 1)) : ∀ m, F 0 → F m
  | 0, A => A
  | m + 1, A => step m (composeFromZero step m A)
section Periodic
def crossingSmoothing (L n k j : ℕ) (A : Edge L n k j → Matrices.ComplexMatrix2) :
    Edge L n k (j + 1) → Matrices.ComplexMatrix2 :=
  fun c => PeriodicLattice.inverseFourthPowerWeight L •
    ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source,
      edgeFormPathSum A (PeriodicLattice.crossingPath c x)
def cubeContourAverage (L n k j : ℕ) (A : Edge L n k j → Matrices.ComplexMatrix2) :
    Vertex L n k (j + 1) → Matrices.ComplexMatrix2 :=
  fun y => PeriodicLattice.inverseFourthPowerWeight L •
    ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      PeriodicLattice.contourFormAverage A y x
def vertexSmoothing (L n k j : ℕ) (g : Vertex L n k j → Matrices.ComplexMatrix2) :
    Vertex L n k (j + 1) → Matrices.ComplexMatrix2 :=
  fun y => PeriodicLattice.inverseFourthPowerWeight L •
    ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y, g x
abbrev FineOnlyVertex (L n k j : ℕ) : Type :=
  {x : Vertex L n k j //
    (x : PeriodicLattice.FourTorus L n) ∉
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (j + 1))}
abbrev fineOnlyFunctions (L n k j : ℕ) :
    Submodule ℝ (FineOnlyVertex L n k j → Matrices.ComplexMatrix2) :=
  Matrices.GroupLieProduct.hermitianTracelessFunctions (FineOnlyVertex L n k j)
def fineOnlyPairing {L n k j : ℕ} (g g' : FineOnlyVertex L n k j → Matrices.ComplexMatrix2) :
    ℂ :=
  traceFinsumPairing g g'
def cubeCentre {L n k j : ℕ} (x : FineOnlyVertex L n k j) : Vertex L n k (j + 1) :=
  Classical.epsilon fun y : Vertex L n k (j + 1) =>
    x.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y ∧
      (x.1 : PeriodicLattice.FourTorus L n) ≠ y
def fineOnlyContourAverage (L n k j : ℕ) (A : Edge L n k j → Matrices.ComplexMatrix2) :
    FineOnlyVertex L n k j → Matrices.ComplexMatrix2 :=
  fun x => PeriodicLattice.contourFormAverage A (cubeCentre x) x.1
def linearSmoothingIter (L n k m : ℕ) :
    (Edge L n k 0 → Matrices.ComplexMatrix2) → Edge L n k m → Matrices.ComplexMatrix2 :=
  PeriodicLattice.iterateFromBare (linearSmoothing L n k) m
def crossingSmoothingIter (L n k m : ℕ) :
    (Edge L n k 0 → Matrices.ComplexMatrix2) → Edge L n k m → Matrices.ComplexMatrix2 :=
  PeriodicLattice.iterateFromBare (crossingSmoothing L n k) m
def vertexSmoothingIter (L n k m : ℕ) :
    (Vertex L n k 0 → Matrices.ComplexMatrix2) → Vertex L n k m → Matrices.ComplexMatrix2 :=
  composeFromZero (F := fun j => Vertex L n k j → Matrices.ComplexMatrix2)
    (vertexSmoothing L n k) m
def cubeContourAverageIter (L n k m : ℕ) (A : Edge L n k 0 → Matrices.ComplexMatrix2) :
    Vertex L n k m → Matrices.ComplexMatrix2 :=
  ∑ i ∈ Finset.range m,
    restrictVertexFunction m (cubeContourAverage L n k i (crossingSmoothingIter L n k i A))
end Periodic
namespace FullSpace
open InfiniteLattice (AmbientSpace)
section Step
variable (L : ℕ) {a a' : ℝ}
def crossingSmoothing (A : InfiniteLattice.Link a' → Matrices.ComplexMatrix2) :
    InfiniteLattice.Link a → Matrices.ComplexMatrix2 :=
  fun c => PeriodicLattice.inverseFourthPowerWeight L •
    ∑ᶠ x ∈ cubeVertices L a' c.initial, edgeFormPathSum A (crossingPath c x)
def cubeContourAverage (A : InfiniteLattice.Link a' → Matrices.ComplexMatrix2) :
    InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2 :=
  fun y => PeriodicLattice.inverseFourthPowerWeight L •
    ∑ᶠ x ∈ cubeVertices L a' y, contourAverage L A y x
def vertexSmoothing (g : InfiniteLattice.LatticePoint a' → Matrices.ComplexMatrix2) :
    InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2 :=
  fun y => PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ cubeVertices L a' y, g x
end Step
abbrev FineOnlyVertex (a a' : ℝ) : Type :=
  {x : InfiniteLattice.LatticePoint a' // (x : AmbientSpace) ∉ InfiniteLattice.latticeSubgroup a}
abbrev fineOnlyFunctions (a a' : ℝ) :
    Submodule ℝ (FineOnlyVertex a a' → Matrices.ComplexMatrix2) :=
  Matrices.GroupLieProduct.hermitianTracelessFunctions (FineOnlyVertex a a')
def cubeCentre (L : ℕ) {a a' : ℝ} (x : FineOnlyVertex a a') : InfiniteLattice.LatticePoint a :=
  Classical.epsilon fun y : InfiniteLattice.LatticePoint a =>
    x.1 ∈ cubeVertices L a' y ∧ (x.1 : AmbientSpace) ≠ y
def fineOnlyContourAverage (L : ℕ) {a a' : ℝ}
    (A : InfiniteLattice.Link a' → Matrices.ComplexMatrix2) :
    FineOnlyVertex a a' → Matrices.ComplexMatrix2 :=
  fun x => contourAverage L A (cubeCentre L x) x.1
def linearSmoothingIter (L k m : ℕ) :
    (Edge L k 0 → Matrices.ComplexMatrix2) → Edge L k m → Matrices.ComplexMatrix2 :=
  composeFromZero (F := fun j => Edge L k j → Matrices.ComplexMatrix2)
    (fun _ => linearSmoothing L) m
def crossingSmoothingIter (L k m : ℕ) :
    (Edge L k 0 → Matrices.ComplexMatrix2) → Edge L k m → Matrices.ComplexMatrix2 :=
  composeFromZero (F := fun j => Edge L k j → Matrices.ComplexMatrix2)
    (fun _ => crossingSmoothing L) m
def vertexSmoothingIter (L k m : ℕ) :
    (Vertex L k 0 → Matrices.ComplexMatrix2) → Vertex L k m → Matrices.ComplexMatrix2 :=
  composeFromZero (F := fun j => Vertex L k j → Matrices.ComplexMatrix2)
    (fun _ => vertexSmoothing L) m
def cubeContourAverageIter (L k m : ℕ) (A : Edge L k 0 → Matrices.ComplexMatrix2) :
    Vertex L k m → Matrices.ComplexMatrix2 :=
  ∑ i ∈ Finset.range m, restrictVertexFunction (meshAt L k m)
    (cubeContourAverage L (a := meshAt L k (i + 1)) (crossingSmoothingIter L k i A))
end FullSpace
end Tower
end YangMills.Construction
end
