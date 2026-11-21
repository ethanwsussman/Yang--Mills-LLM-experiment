import YangMills.Construction.RunningCouplingSlope.TriplesOfTheChain
import YangMills.Construction.RunningCouplingSlope.WaveSumsOfTheKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def hessianOfFreeEnergy {L n k : ℕ} (a : ℝ) (τ τ' : LevelTriple L n k) : ℝ :=
  deriv (fun s : ℝ => deriv (fun u : ℝ => tripleFreeEnergy a (s • τ + u • τ')) 0) 0
def backgroundOnlyTriple {L n k : ℕ} (A : Tower.edgeFormSpace L n k 0) : LevelTriple L n k :=
  ((A, 0), 0, 0)
def levelFormsNormSq {L n k : ℕ} (ξ : LevelForms L n k) : ℝ :=
  levelPairing (formValues ξ) (formValues ξ)
def topFormNormSq {L n k : ℕ} (μ : Tower.edgeFormSpace L n k k) : ℝ :=
  (Tower.edgeFormPairing (μ : Tower.Edge L n k k → Matrices.ComplexMatrix2)
    (μ : Tower.Edge L n k k → Matrices.ComplexMatrix2)).re
def tripleNormSq {L n k : ℕ} (τ : LevelTriple L n k) : ℝ :=
  levelFormsNormSq τ.1 + levelFormsNormSq τ.2.1 + topFormNormSq τ.2.2
def backgroundCurvatureNormSq {L n k : ℕ} (A : Tower.edgeFormSpace L n k 0) : ℝ :=
  (Tower.traceFinsumPairing
    (Tower.CriticalBranchResponse.formCoboundary L n k A : Tower.Face L n k 0 → Matrices.ComplexMatrix2)
    (Tower.CriticalBranchResponse.formCoboundary L n k A : Tower.Face L n k 0 → Matrices.ComplexMatrix2)).re
def planeWaveValues (L n k : ℕ) [NeZero (2 * L ^ n)] (f : TorusFields.TorusSite (2 * L ^ n) → ℝ) :
    Tower.Edge L n k k → Matrices.ComplexMatrix2 :=
  ∑ x, f x • pauliUnitForm L n k (centredCoords x)
def planeWaveOnTorus {s : ℕ} (f : TorusFields.TorusSite s → ℝ) :
    TorusFields.TorusBond s → BlockAverages.imaginaryQuaternions := fun c =>
  if c.2 = SlopeCoefficient.secondAxis then f c.1 • thirdGenerator else 0
end YangMills.Construction.RunningCouplingSlope
end
