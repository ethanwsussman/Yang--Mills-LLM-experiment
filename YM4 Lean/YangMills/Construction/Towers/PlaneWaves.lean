import YangMills.Construction.Towers.TheHolomorphicActionOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace PlaneWaves
open PeriodicOperators (colourVertices colourEdges colourFaces castVec toComplexVec bilinDot
  intShift)
def freqWindow (L k : ℕ) : Finset ℤ :=
  Finset.Icc (-⌊1 / 2 * ((finestMesh L k)⁻¹ - 1)⌋) ⌊1 / 2 * ((finestMesh L k)⁻¹ - 1)⌋
theorem mem_freqWindow (L k : ℕ) (j : ℤ) :
    j ∈ freqWindow L k ↔ |(j : ℝ)| ≤ 1 / 2 * ((finestMesh L k)⁻¹ - 1) := by
  rw [freqWindow, Finset.mem_Icc, abs_le, neg_le, Int.le_floor, Int.le_floor, Int.cast_neg, neg_le]
def freqBox (L k : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => freqWindow L k
theorem mem_freqBox (L k : ℕ) (m : Fin 4 → ℤ) :
    m ∈ freqBox L k ↔ ∀ ν, |(m ν : ℝ)| ≤ 1 / 2 * ((finestMesh L k)⁻¹ - 1) := by
  simp only [freqBox, Fintype.mem_piFinset, mem_freqWindow]
def shiftedFreq (κ : Fin 4 → ℂ) (m : Fin 4 → ℤ) : Fin 4 → ℂ :=
  fun μ => κ μ + 2 * (Real.pi : ℂ) * (m μ : ℂ)
abbrev VertexClass (L k : ℕ) : Type :=
  Quot fun x y : FullSpace.Vertex L k 0 =>
    ∃ a : Fin 4 → ℤ, y = FullSpace.vertexImage (intShift a) x
def fourierPhase (m : Fin 4 → ℤ) (x : InfiniteLattice.AmbientSpace) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
    bilinDot (toComplexVec (castVec m)) (toComplexVec x))
def fourierCoeff (L k : ℕ) (g : FullSpace.Vertex L k 0 → Matrices.ComplexMatrix2) (m : Fin 4 → ℤ) :
    Matrices.ComplexMatrix2 :=
  ((finestMesh L k ^ 4 : ℝ) : ℂ) •
    ∑ᶠ c : VertexClass L k, fourierPhase m (Quot.out c : FullSpace.Vertex L k 0) • g (Quot.out c)
def vertexFieldOfClasses (L k : ℕ) (l : (colourVertices L k 0).UnitQuot → ℂ) :
    FullSpace.Vertex L k 0 → Matrices.ComplexMatrix2 :=
  ofPauliCoeffs fun ι => l ((colourVertices L k 0).mkQuot 1 ι)
def edgeFieldOfClasses (L k : ℕ) (b : (colourEdges L k 0).UnitQuot → ℂ) :
    PeriodicOperators.PosEdge L k 0 → Matrices.ComplexMatrix2 :=
  ofPauliCoeffs fun ι => b ((colourEdges L k 0).mkQuot 1 ι)
def faceFieldOfClasses (L k : ℕ) (f : (colourFaces L k 0).UnitQuot → ℂ) :
    FullSpace.Face L k 0 → Matrices.ComplexMatrix2 :=
  ofPauliCoeffs fun ι => f ((colourFaces L k 0).mkQuot 1 ι)
def edgeAt (L k : ℕ) (x : FullSpace.Vertex L k 0) (μ : Fin 4) :
    PeriodicOperators.PosEdge L k 0 :=
  ⟨InfiniteLattice.Link.forwardFrom x μ, μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
def vertexFourierCoeff (L k : ℕ) (l : (colourVertices L k 0).UnitQuot → ℂ) (m : Fin 4 → ℤ) :
    Matrices.ComplexMatrix2 :=
  fourierCoeff L k (vertexFieldOfClasses L k l) m
def edgeFourierCoeff (L k : ℕ) (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4)
    (m : Fin 4 → ℤ) : Matrices.ComplexMatrix2 :=
  fourierCoeff L k (fun x => edgeFieldOfClasses L k b (edgeAt L k x μ)) m
def faceFourierCoeff (L k : ℕ) (f : (colourFaces L k 0).UnitQuot → ℂ) (μ ν : Fin 4)
    (h : μ < ν) (m : Fin 4 → ℤ) : Matrices.ComplexMatrix2 :=
  fourierCoeff L k (fun x => faceFieldOfClasses L k f ⟨x, μ, ν, h⟩) m
def forwardSymbol (L k : ℕ) (q : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun μ => ((finestMesh L k : ℝ) : ℂ)⁻¹ *
    (Complex.exp (Complex.I * ((finestMesh L k : ℝ) : ℂ) * q μ) - 1)
def symbolSquare (L k : ℕ) (q : Fin 4 → ℂ) : ℂ :=
  ∑ μ, forwardSymbol L k q μ * forwardSymbol L k (-q) μ
def unitSymbol (q : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun μ => Complex.exp (Complex.I * q μ) - 1
def dirichletSum (L k : ℕ) (τ : ℂ) : ℂ :=
  ((finestMesh L k : ℝ) : ℂ) * ∑ j ∈ freqWindow L k,
    Complex.exp (Complex.I * ((finestMesh L k : ℝ) : ℂ) * (j : ℂ) * τ)
def vertexWeight (L k : ℕ) (q : Fin 4 → ℂ) : ℂ := ∏ ν, dirichletSum L k (q ν)
def edgeWeight (L k : ℕ) (q : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun μ => Complex.exp (Complex.I * (1 - ((finestMesh L k : ℝ) : ℂ)) * q μ / 2) *
    dirichletSum L k (q μ) * vertexWeight L k q
end PlaneWaves
end Tower
end YangMills.Construction
end
