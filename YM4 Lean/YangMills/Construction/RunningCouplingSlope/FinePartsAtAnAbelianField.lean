import YangMills.Construction.Towers.FactsOnThePartsOfTheHessianOfTheWilsonActionProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators
def diagExpAngle (ψ : ℝ) : Matrices.ComplexMatrix2 :=
  !![Complex.exp (ψ * Complex.I), 0; 0, Complex.exp (-(ψ * Complex.I))]
def adjointRotation (ψ : ℝ) : Fin 3 → Fin 3 → ℂ :=
  ![![(Real.cos (2 * ψ) : ℂ), (Real.sin (2 * ψ) : ℂ), 0],
    ![-(Real.sin (2 * ψ) : ℂ), (Real.cos (2 * ψ) : ℂ), 0], ![0, 0, 1]]
def crossThird (u v : Fin 3 → ℂ) : ℂ := -2 * (u 0 * v 1 - u 1 * v 0)
variable {L n k : ℕ}
def abelianGaugeField (φ : Tower.Edge L n k 0 → ℝ) : Tower.Edge L n k 0 → Matrices.ComplexMatrix2 :=
  fun b => diagExpAngle (φ b)
theorem faceEdge_isPositive (p : Tower.Face L n k 0) (i : Fin 4) :
    (Tower.faceEdge p i).IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.CurvatureHessianFacts.faceEdge_isPositivelyOriented <;> assumption
def facePositiveEdge (p : Tower.Face L n k 0) (i : Fin 4) : Tower.PositiveEdge L n k 0 :=
  ⟨Tower.faceEdge p i, faceEdge_isPositive p i⟩
def holonomyAngle (φ : Tower.Edge L n k 0 → ℝ) (p : Tower.Face L n k 0) : Fin 4 → ℝ :=
  ![0, φ (Tower.faceEdge p 0),
    φ (Tower.faceEdge p 0) + φ (Tower.faceEdge p 1) - φ (Tower.faceEdge p 2),
    φ (Tower.faceEdge p 0) + φ (Tower.faceEdge p 1) - φ (Tower.faceEdge p 2) -
      φ (Tower.faceEdge p 3)]
def covDiffEntry (L n k : ℕ) (φ : Tower.Edge L n k 0 → ℝ)
    (ι' : Fin 3 × Tower.PositiveEdge L n k 0) (ι : Fin 3 × Tower.Vertex L n k 0) : ℂ :=
  open Classical in
  (((Tower.finestMesh L k)⁻¹ : ℝ) : ℂ) *
    ((if ι.2 = ι'.2.1.target then adjointRotation (φ ι'.2.1) ι'.1 ι.1 else 0) -
      (if ι.2 = ι'.2.1.source ∧ ι.1 = ι'.1 then 1 else 0))
def holonomyDefectEntry (L n k : ℕ) (φ : Tower.Edge L n k 0 → ℝ)
    (ι' : Fin 3 × Tower.Face L n k 0) (ι : Fin 3 × Tower.PositiveEdge L n k 0) : ℂ :=
  open Classical in
  (((Tower.finestMesh L k)⁻¹ : ℝ) : ℂ) * ∑ i : Fin 4, Tower.transportSign i *
    (if ι.2 = facePositiveEdge ι'.2 i then
      adjointRotation (holonomyAngle φ ι'.2 i) ι'.1 ι.1 - (if ι.1 = ι'.1 then 1 else 0) else 0)
def faceTraceEntry (L n k : ℕ) (φ : Tower.Edge L n k 0 → ℝ)
    (ι' ι : Fin 3 × Tower.Face L n k 0) : ℂ :=
  open Classical in
  if ι = ι' then (Real.cos (holonomyAngle φ ι'.2 3) : ℂ) else 0
def curvatureHalfSum (L n k : ℕ) [Fintype (Tower.Face L n k 0)] (φ : Tower.Edge L n k 0 → ℝ)
    (ι' ι : Fin 3 × Tower.PositiveEdge L n k 0) : ℂ :=
  open Classical in
  ∑ p : Tower.Face L n k 0, ∑ i : Fin 4, ∑ j ∈ Finset.Ioi i,
    if facePositiveEdge p i = ι'.2 ∧ facePositiveEdge p j = ι.2 then
      (((Tower.finestMesh L k ^ 2)⁻¹ * Real.sin (holonomyAngle φ p 3) : ℝ) : ℂ) *
        (Tower.transportSign i * Tower.transportSign j) *
        crossThird (fun c => adjointRotation (holonomyAngle φ p i) c ι'.1)
          (fun c => adjointRotation (holonomyAngle φ p j) c ι.1)
    else 0
def AbelianFineKernels : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n →
    ∀ [Fintype (Fin 3 × Tower.PositiveEdge L n k 0)] [Fintype (Fin 3 × Tower.Vertex L n k 0)]
      [Fintype (Fin 3 × Tower.Face L n k 0)] [Fintype (Tower.Face L n k 0)],
    ∀ φ : Tower.Edge L n k 0 → ℝ, (∀ b, φ b.opposite = -φ b) →
      (Tower.rescaledOperators L n k (abelianGaugeField φ)).D = covDiffEntry L n k φ ∧
      Tower.holonomyDefectKernel L n k (abelianGaugeField φ) = holonomyDefectEntry L n k φ ∧
      Tower.halfFaceTraceKernel L n k (abelianGaugeField φ) = faceTraceEntry L n k φ ∧
      Tower.curvatureKernel (abelianGaugeField φ) = fun ι' ι =>
        (1 / 2 : ℂ) * (curvatureHalfSum L n k φ ι' ι + curvatureHalfSum L n k φ ι ι')
end YangMills.Construction.RunningCouplingSlope
end
