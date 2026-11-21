import YangMills.Construction.Towers.TheMassiveFunctional
import YangMills.Construction.Towers.TransposesOfDifferencesAtScalarFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace FullSpace
section Fields
variable {a : ℝ}
def abelianLinkField (θ : PositiveEdge a → ℝ) :
    YangMills.Construction.InfiniteLattice.Link a → YangMills.Construction.Matrices.ComplexMatrix2 :=
  open Classical in fun b =>
    if h : b.IsPositivelyOriented then
      YangMills.Construction.Matrices.ComplexMatrix2.matExp
        (Complex.I • ((θ ⟨b, h⟩ : ℂ) • YangMills.Construction.Matrices.ComplexMatrix2.pauliFamily 2))
    else if h' : b.opposite.IsPositivelyOriented then
      (YangMills.Construction.Matrices.ComplexMatrix2.matExp
        (Complex.I • ((θ ⟨b.opposite, h'⟩ : ℂ) •
          YangMills.Construction.Matrices.ComplexMatrix2.pauliFamily 2)))⁻¹
    else 1
def faceAngle (θ : PositiveEdge a → ℝ)
    (p : YangMills.Construction.InfiniteLattice.ElementaryPlaquette a) : ℝ :=
  edgeDifference θ p
def edgeComponent (w : PositiveEdge a → ℂ) (μ : Fin 4)
    (x : YangMills.Construction.InfiniteLattice.LatticePoint a) : ℂ :=
  w (forwardEdge x μ)
def chargedShift (θ : PositiveEdge a → ℝ) (μ : Fin 4)
    (w : YangMills.Construction.InfiniteLattice.LatticePoint a → ℂ)
    (x : YangMills.Construction.InfiniteLattice.LatticePoint a) : ℂ :=
  Complex.exp (2 * Complex.I * (θ (forwardEdge x μ) : ℂ)) *
    w (x + YangMills.Construction.InfiniteLattice.axisStep a μ)
def faceNumbers (θ : PositiveEdge a → ℝ) (w : PositiveEdge a → ℂ)
    (p : YangMills.Construction.InfiniteLattice.ElementaryPlaquette a) : Fin 4 → ℂ :=
  ![edgeComponent w p.lowAxis p.corner,
    chargedShift θ p.lowAxis (edgeComponent w p.highAxis) p.corner,
    -Complex.exp (2 * Complex.I * (faceAngle θ p : ℂ)) *
      chargedShift θ p.highAxis (edgeComponent w p.lowAxis) p.corner,
    -Complex.exp (2 * Complex.I * (faceAngle θ p : ℂ)) * edgeComponent w p.highAxis p.corner]
def linearAbelianAngle : PositiveEdge a → ℝ :=
  open Classical in fun b =>
    if b.1.terminal - b.1.initial = YangMills.Construction.InfiniteLattice.axisStep a 1 then
      (b.1.initial : YangMills.Construction.InfiniteLattice.AmbientSpace) 0
    else 0
def diagonalComponent
    (B : YangMills.Construction.InfiniteLattice.Link a → YangMills.Construction.Matrices.ComplexMatrix2) :
    PositiveEdge a → ℝ :=
  fun b => (YangMills.Construction.Matrices.ComplexMatrix2.halfTrace
    (B b.1 * YangMills.Construction.Matrices.ComplexMatrix2.pauliFamily 2)).re
end Fields
def abelianGaugeLaplacian {L : ℕ} (θ : PositiveEdge (meshAt L 0 0) → ℝ) :
    (Vertex L 0 0 → YangMills.Construction.Matrices.ComplexMatrix2) →
      Vertex L 0 0 → YangMills.Construction.Matrices.ComplexMatrix2 :=
  gaugeLaplacian (abelianLinkField θ)
def abelianMassiveHessian {L : ℕ} (θ : PositiveEdge (meshAt L 0 0) → ℝ) :
    (Edge L 0 0 → YangMills.Construction.Matrices.ComplexMatrix2) →
      Edge L 0 0 → YangMills.Construction.Matrices.ComplexMatrix2 :=
  massiveHessian (abelianLinkField θ)
end FullSpace
def raisingPauli : YangMills.Construction.Matrices.ComplexMatrix2 :=
  (1 / 2 : ℂ) • (YangMills.Construction.Matrices.ComplexMatrix2.pauliFamily 0 +
    Complex.I • YangMills.Construction.Matrices.ComplexMatrix2.pauliFamily 1)
def loweringPauli : YangMills.Construction.Matrices.ComplexMatrix2 :=
  (1 / 2 : ℂ) • (YangMills.Construction.Matrices.ComplexMatrix2.pauliFamily 0 -
    Complex.I • YangMills.Construction.Matrices.ComplexMatrix2.pauliFamily 1)
def IsNeutral {σ : Type} (f : σ → YangMills.Construction.Matrices.ComplexMatrix2) : Prop :=
  ∃ c : σ → ℂ, ∀ s, f s = c s • YangMills.Construction.Matrices.ComplexMatrix2.pauliFamily 2
def IsPositivelyCharged {σ : Type} (f : σ → YangMills.Construction.Matrices.ComplexMatrix2) : Prop :=
  ∃ c : σ → ℂ, ∀ s, f s = c s • raisingPauli
def IsNegativelyCharged {σ : Type} (f : σ → YangMills.Construction.Matrices.ComplexMatrix2) : Prop :=
  ∃ c : σ → ℂ, ∀ s, f s = c s • loweringPauli
def FullSpace.offDiagonalComponent {a : ℝ}
    (B : YangMills.Construction.InfiniteLattice.Link a → YangMills.Construction.Matrices.ComplexMatrix2) :
    FullSpace.PositiveEdge a → ℂ :=
  fun b => 2 * YangMills.Construction.Matrices.ComplexMatrix2.halfTrace (B b.1 * loweringPauli)
end Tower
end YangMills.Construction
end
