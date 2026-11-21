import YangMills.Construction.Towers.LinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace TrivialLinearization
def setAverage {ι : Type*} (S : Set ι) (f : ι → Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2 :=
  ((S.ncard : ℂ)⁻¹) • ∑ᶠ x ∈ S, f x
def pivotScale (L : ℕ) : ℂ := (((L : ℝ) ^ (-3 : ℤ) : ℝ) : ℂ)
section Periodic
def baseVerticesOfCube (L n k m : ℕ) (y : Tower.Vertex L n k m) : Set (Tower.Vertex L n k 0) :=
  {x | (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock m y}
def OneStepIdentities (L n k j : ℕ) : Prop :=
  (∀ B ∈ Tower.edgeFormSpace L n k j, Tower.linearSmoothing L n k j B =
    Tower.crossingSmoothing L n k j B -
      Tower.vertexCoboundary (Tower.cubeContourAverage L n k j B)) ∧
  ∀ f ∈ Tower.vertexFunctionSpace L n k j,
    Tower.linearSmoothing L n k j (Tower.vertexCoboundary f) =
      Tower.vertexCoboundary (Tower.restrictVertexFunction (j + 1) f) ∧
    Tower.crossingSmoothing L n k j (Tower.vertexCoboundary f) =
      Tower.vertexCoboundary (Tower.vertexSmoothing L n k j f) ∧
    Tower.cubeContourAverage L n k j (Tower.vertexCoboundary f) =
      Tower.vertexSmoothing L n k j f - Tower.restrictVertexFunction (j + 1) f ∧
    ∀ (y : Tower.Vertex L n k (j + 1)) (x : Tower.FineOnlyVertex L n k j),
      x.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      (x.1 : PeriodicLattice.FourTorus L n) ≠ y →
      Tower.fineOnlyContourAverage L n k j (Tower.vertexCoboundary f) x =
        f x.1 - Tower.restrictVertexFunction (j + 1) f y
def OneStepConstantForms (L n k j : ℕ) : Prop :=
  ∀ B ∈ Tower.edgeFormSpace L n k j, ∀ a : Fin 4 → Matrices.ComplexMatrix2,
    (∀ (x : Tower.Vertex L n k j) (μ : Fin 4), B (PeriodicLattice.Bond.forwardFrom x μ) = a μ) →
    (∀ (y : Tower.Vertex L n k (j + 1)) (x : Tower.Vertex L n k j) (ν : Fin 4 → ℤ),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      PeriodicLattice.IsBlockOffset y x ν →
      PeriodicLattice.contourFormAverage B y x = ∑ μ, ν μ • a μ) ∧
    Tower.cubeContourAverage L n k j B = 0 ∧
    Tower.linearSmoothing L n k j B = Tower.crossingSmoothing L n k j B ∧
    Tower.crossingSmoothing L n k j B ∈ Tower.edgeFormSpace L n k (j + 1) ∧
    ∀ (x : Tower.Vertex L n k (j + 1)) (μ : Fin 4),
      Tower.crossingSmoothing L n k j B (PeriodicLattice.Bond.forwardFrom x μ) = (L : ℂ) • a μ
def OneStepPivotSupported (L n k j : ℕ) : Prop :=
  ∀ B ∈ Tower.edgeFormSpace L n k j,
    (∀ b : Tower.Edge L n k j, b.IsPositivelyOriented →
      (∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented → b ≠ PeriodicLattice.pivot c) →
        B b = 0) →
    Tower.cubeContourAverage L n k j B = 0 ∧
    Tower.fineOnlyContourAverage L n k j B = 0 ∧
    ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
      Tower.linearSmoothing L n k j B c = Tower.crossingSmoothing L n k j B c ∧
      Tower.crossingSmoothing L n k j B c = pivotScale L • B (PeriodicLattice.pivot c)
def SmoothingsSurjective (L n k j m : ℕ) : Prop :=
  (∀ C ∈ Tower.edgeFormSpace L n k (j + 1), ∃ B ∈ Tower.edgeFormSpace L n k j,
    Tower.linearSmoothing L n k j B = C) ∧
  (∀ C ∈ Tower.edgeFormSpace L n k (j + 1), ∃ B ∈ Tower.edgeFormSpace L n k j,
    Tower.crossingSmoothing L n k j B = C) ∧
  (∀ C ∈ Tower.edgeFormSpace L n k m, ∃ B ∈ Tower.edgeFormSpace L n k 0,
    Tower.linearSmoothingIter L n k m B = C) ∧
  ∀ C ∈ Tower.edgeFormSpace L n k m, ∃ B ∈ Tower.edgeFormSpace L n k 0,
    Tower.crossingSmoothingIter L n k m B = C
def IterateIdentitiesAndBounds (L n k m : ℕ) : Prop :=
  ∀ B ∈ Tower.edgeFormSpace L n k 0,
    Tower.linearSmoothingIter L n k m B =
      Tower.crossingSmoothingIter L n k m B -
        Tower.vertexCoboundary (Tower.cubeContourAverageIter L n k m B) ∧
    Tower.maxOperatorNorm (Tower.crossingSmoothingIter L n k m B) ≤
      (L : ℝ≥0∞) ^ m * Tower.maxOperatorNorm B ∧
    Tower.maxOperatorNorm (Tower.cubeContourAverageIter L n k m B) ≤
      ∑ i ∈ Finset.range m, 2 * ((L : ℝ≥0∞) - 1) * (L : ℝ≥0∞) ^ i * Tower.maxOperatorNorm B ∧
    ∑ i ∈ Finset.range m, 2 * ((L : ℝ≥0∞) - 1) * (L : ℝ≥0∞) ^ i * Tower.maxOperatorNorm B ≤
      2 * (L : ℝ≥0∞) ^ m * Tower.maxOperatorNorm B ∧
    Tower.maxOperatorNorm (Tower.linearSmoothingIter L n k m B) ≤
      5 * (L : ℝ≥0∞) ^ m * Tower.maxOperatorNorm B
def IterateAverages (L n k m : ℕ) : Prop :=
  (∀ B ∈ Tower.edgeFormSpace L n k 0, ∀ c : Tower.Edge L n k m,
    Tower.crossingSmoothingIter L n k m B c =
      setAverage (baseVerticesOfCube L n k m c.source) fun x =>
        Tower.edgeFormPathSum B (PeriodicLattice.crossingPath c x)) ∧
  ∀ f ∈ Tower.vertexFunctionSpace L n k 0, ∀ y : Tower.Vertex L n k m,
    Tower.vertexSmoothingIter L n k m f y = setAverage (baseVerticesOfCube L n k m y) f
end Periodic
end TrivialLinearization
namespace FullSpace
namespace TrivialLinearization
open YangMills.Construction.Tower.TrivialLinearization (setAverage pivotScale)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def baseVerticesOfCube (L k m : ℕ) (y : FullSpace.Vertex L k m) : Set (FullSpace.Vertex L k 0) :=
  {x | (x : AmbientSpace) ∈ FullSpace.cubeOfOrder L (Tower.meshAt L k 0) m y}
def OneStepIdentities (L k j : ℕ) : Prop :=
  (∀ B ∈ FullSpace.edgeFormSpace (Tower.meshAt L k j),
    FullSpace.linearSmoothing (a := Tower.meshAt L k (j + 1)) L B =
      FullSpace.crossingSmoothing (a := Tower.meshAt L k (j + 1)) L B -
        FullSpace.vertexCoboundary
          (FullSpace.cubeContourAverage (a := Tower.meshAt L k (j + 1)) L B)) ∧
  ∀ f ∈ FullSpace.vertexFunctionSpace (Tower.meshAt L k j),
    FullSpace.linearSmoothing (a := Tower.meshAt L k (j + 1)) L (FullSpace.vertexCoboundary f) =
      FullSpace.vertexCoboundary
        (FullSpace.restrictVertexFunction (Tower.meshAt L k (j + 1)) f) ∧
    FullSpace.crossingSmoothing (a := Tower.meshAt L k (j + 1)) L
        (FullSpace.vertexCoboundary f) =
      FullSpace.vertexCoboundary
        (FullSpace.vertexSmoothing (a := Tower.meshAt L k (j + 1)) L f) ∧
    FullSpace.cubeContourAverage (a := Tower.meshAt L k (j + 1)) L
        (FullSpace.vertexCoboundary f) =
      FullSpace.vertexSmoothing (a := Tower.meshAt L k (j + 1)) L f -
        FullSpace.restrictVertexFunction (Tower.meshAt L k (j + 1)) f ∧
    ∀ (y : FullSpace.Vertex L k (j + 1))
      (x : FullSpace.FineOnlyVertex (Tower.meshAt L k (j + 1)) (Tower.meshAt L k j)),
      x.1 ∈ FullSpace.cubeVertices L (Tower.meshAt L k j) y → (x.1 : AmbientSpace) ≠ y →
      FullSpace.fineOnlyContourAverage L (FullSpace.vertexCoboundary f) x =
        f x.1 - FullSpace.restrictVertexFunction (Tower.meshAt L k (j + 1)) f y
def OneStepConstantForms (L k j : ℕ) : Prop :=
  ∀ B ∈ FullSpace.edgeFormSpace (Tower.meshAt L k j), ∀ a : Fin 4 → Matrices.ComplexMatrix2,
    (∀ (x : FullSpace.Vertex L k j) (μ : Fin 4),
      B (InfiniteLattice.Link.forwardFrom x μ) = a μ) →
    (∀ (y : FullSpace.Vertex L k (j + 1)) (x : FullSpace.Vertex L k j) (ν : Fin 4 → ℤ),
      x ∈ FullSpace.cubeVertices L (Tower.meshAt L k j) y → FullSpace.IsCubeOffset L y x ν →
      FullSpace.contourAverage L B y x = ∑ μ, ν μ • a μ) ∧
    FullSpace.cubeContourAverage (a := Tower.meshAt L k (j + 1)) L B = 0 ∧
    FullSpace.linearSmoothing (a := Tower.meshAt L k (j + 1)) L B =
      FullSpace.crossingSmoothing (a := Tower.meshAt L k (j + 1)) L B ∧
    FullSpace.crossingSmoothing (a := Tower.meshAt L k (j + 1)) L B ∈
      FullSpace.edgeFormSpace (Tower.meshAt L k (j + 1)) ∧
    ∀ (x : FullSpace.Vertex L k (j + 1)) (μ : Fin 4),
      FullSpace.crossingSmoothing (a := Tower.meshAt L k (j + 1)) L B
          (InfiniteLattice.Link.forwardFrom x μ) =
        (L : ℂ) • a μ
def OneStepPivotSupported (L k j : ℕ) : Prop :=
  ∀ B ∈ FullSpace.edgeFormSpace (Tower.meshAt L k j),
    (∀ b : FullSpace.Edge L k j, b.IsPositivelyOriented →
      (∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
        b ≠ FullSpace.pivotLink L (Tower.meshAt L k j) c) →
        B b = 0) →
    FullSpace.cubeContourAverage (a := Tower.meshAt L k (j + 1)) L B = 0 ∧
    FullSpace.fineOnlyContourAverage (a := Tower.meshAt L k (j + 1)) L B = 0 ∧
    ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
      FullSpace.linearSmoothing L B c = FullSpace.crossingSmoothing L B c ∧
      FullSpace.crossingSmoothing L B c =
        pivotScale L • B (FullSpace.pivotLink L (Tower.meshAt L k j) c)
def SmoothingsSurjective (L k j m : ℕ) : Prop :=
  (∀ C ∈ FullSpace.edgeFormSpace (Tower.meshAt L k (j + 1)),
    ∃ B ∈ FullSpace.edgeFormSpace (Tower.meshAt L k j), FullSpace.linearSmoothing L B = C) ∧
  (∀ C ∈ FullSpace.edgeFormSpace (Tower.meshAt L k (j + 1)),
    ∃ B ∈ FullSpace.edgeFormSpace (Tower.meshAt L k j), FullSpace.crossingSmoothing L B = C) ∧
  (∀ C ∈ FullSpace.edgeFormSpace (Tower.meshAt L k m),
    ∃ B ∈ FullSpace.edgeFormSpace (Tower.meshAt L k 0), FullSpace.linearSmoothingIter L k m B = C) ∧
  ∀ C ∈ FullSpace.edgeFormSpace (Tower.meshAt L k m),
    ∃ B ∈ FullSpace.edgeFormSpace (Tower.meshAt L k 0), FullSpace.crossingSmoothingIter L k m B = C
def IterateIdentitiesAndBounds (L k m : ℕ) : Prop :=
  ∀ B ∈ FullSpace.edgeFormSpace (Tower.meshAt L k 0),
    FullSpace.linearSmoothingIter L k m B =
      FullSpace.crossingSmoothingIter L k m B -
        FullSpace.vertexCoboundary (FullSpace.cubeContourAverageIter L k m B) ∧
    Tower.maxOperatorNorm (FullSpace.crossingSmoothingIter L k m B) ≤
      (L : ℝ≥0∞) ^ m * Tower.maxOperatorNorm B ∧
    Tower.maxOperatorNorm (FullSpace.cubeContourAverageIter L k m B) ≤
      ∑ i ∈ Finset.range m, 2 * ((L : ℝ≥0∞) - 1) * (L : ℝ≥0∞) ^ i * Tower.maxOperatorNorm B ∧
    ∑ i ∈ Finset.range m, 2 * ((L : ℝ≥0∞) - 1) * (L : ℝ≥0∞) ^ i * Tower.maxOperatorNorm B ≤
      2 * (L : ℝ≥0∞) ^ m * Tower.maxOperatorNorm B ∧
    Tower.maxOperatorNorm (FullSpace.linearSmoothingIter L k m B) ≤
      5 * (L : ℝ≥0∞) ^ m * Tower.maxOperatorNorm B
def IterateAverages (L k m : ℕ) : Prop :=
  (∀ B ∈ FullSpace.edgeFormSpace (Tower.meshAt L k 0), ∀ c : FullSpace.Edge L k m,
    FullSpace.crossingSmoothingIter L k m B c =
      setAverage (baseVerticesOfCube L k m c.initial) fun x =>
        FullSpace.edgeFormPathSum B (FullSpace.crossingPath c x)) ∧
  ∀ f ∈ FullSpace.vertexFunctionSpace (Tower.meshAt L k 0), ∀ y : FullSpace.Vertex L k m,
    FullSpace.vertexSmoothingIter L k m f y = setAverage (baseVerticesOfCube L k m y) f
end TrivialLinearization
end FullSpace
end Tower
end YangMills.Construction
end
