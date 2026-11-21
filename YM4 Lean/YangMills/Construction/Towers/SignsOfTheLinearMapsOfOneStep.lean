import YangMills.Construction.Towers.LinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
namespace StepMaps
abbrev straightFormAverage (L n k j : ℕ) :
    (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k (j + 1) → Matrices.ComplexMatrix2 :=
  crossingSmoothing L n k j
abbrev stepContourAverage (L n k j : ℕ) :
    (Edge L n k j → Matrices.ComplexMatrix2) → Vertex L n k (j + 1) → Matrices.ComplexMatrix2 :=
  cubeContourAverage L n k j
abbrev cubeMean (L n k j : ℕ) :
    (Vertex L n k j → Matrices.ComplexMatrix2) → Vertex L n k (j + 1) → Matrices.ComplexMatrix2 :=
  vertexSmoothing L n k j
abbrev linearAxialFunction (L n k j : ℕ) :
    (Edge L n k j → Matrices.ComplexMatrix2) → FineOnlyVertex L n k j → Matrices.ComplexMatrix2 :=
  fineOnlyContourAverage L n k j
end StepMaps
namespace FullSpace.StepMaps
abbrev straightFormAverage (L k j : ℕ) :
    (Edge L k j → Matrices.ComplexMatrix2) → Edge L k (j + 1) → Matrices.ComplexMatrix2 :=
  crossingSmoothing L
abbrev stepContourAverage (L k j : ℕ) :
    (Edge L k j → Matrices.ComplexMatrix2) → Vertex L k (j + 1) → Matrices.ComplexMatrix2 :=
  cubeContourAverage L
abbrev cubeMean (L k j : ℕ) :
    (Vertex L k j → Matrices.ComplexMatrix2) → Vertex L k (j + 1) → Matrices.ComplexMatrix2 :=
  vertexSmoothing L
abbrev linearAxialFunction (L k j : ℕ) :
    (Edge L k j → Matrices.ComplexMatrix2) →
      FineOnlyVertex (meshAt L k (j + 1)) (meshAt L k j) → Matrices.ComplexMatrix2 :=
  fineOnlyContourAverage L
end FullSpace.StepMaps
end YangMills.Construction.Tower
end
