import YangMills.Construction.Lattice.WeightedWilsonActions
import YangMills.Construction.Matrices.SpecialUnitaryScalarVectorParts
import YangMills.Construction.PeriodicLattice.TriplesOnFiniteBondSets
import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import YangMills.Construction.Towers.FiniteSetsOfPlaquettesAndBonds
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Matrices
namespace PeriodicOperators
section KernelMatrices
variable {N N' : Type}
def HasFiniteSupport {ι E : Type*} [Zero E] (f : ι → E) : Prop := (Function.support f).Finite
abbrev KernelMatrix (N N' : Type) : Type := N' → N → ℂ
def kernelLinComb (c c' : ℂ) (T T' : KernelMatrix N N') : KernelMatrix N N' :=
  fun x' x => c * T x' x + c' * T' x' x
end KernelMatrices
end PeriodicOperators
namespace Tower
open YangMills.Construction.PeriodicOperators (KernelMatrix applyKernel)
def pauliCoeff (a : Fin 3) (X : ComplexMatrix2) : ℂ :=
  open Classical in
  if h : X ∈ ComplexMatrix2.traceless then OneLoop.pauliCoordinateEquiv ⟨X, h⟩ a else 0
def toPauliCoeffs {σ : Type} (B : σ → ComplexMatrix2) : Fin 3 × σ → ℂ :=
  fun x => pauliCoeff x.1 (B x.2)
def ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) : σ → ComplexMatrix2 :=
  fun b => ∑ a, c (a, b) • ComplexMatrix2.pauliFamily a
section PeriodicSide
variable {L n k j : ℕ}
def complexFaceTerm (U : Edge L n k j → ComplexMatrix2) (p : Face L n k j) : ℂ :=
  PeriodicLattice.plaquetteEnergy U p
def complexAction (U : Edge L n k j → ComplexMatrix2) : ℂ :=
  ∑ᶠ p : Face L n k j, complexFaceTerm U p
def complexActionDeriv (U B : Edge L n k j → ComplexMatrix2) : ℂ :=
  holLeftDeriv complexAction U B
def complexActionHessian (U B B' : Edge L n k j → ComplexMatrix2) : ℂ :=
  holLeftSecondDeriv complexAction U B B'
def edgeSupport (B : Edge L n k j → ComplexMatrix2) : Set (Edge L n k j) :=
  {b | b.IsPositivelyOriented ∧ B b ≠ 0}
def basisForm (a : Fin 3) (b : PositiveEdge L n k j) : Edge L n k j → ComplexMatrix2 :=
  open Classical in
  extendOddly fun b' => if b' = b.1 then ComplexMatrix2.pauliFamily a else 0
def complexHessianKernel (U : Edge L n k j → ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge L n k j) (Fin 3 × PositiveEdge L n k j) :=
  fun x' x => complexActionHessian U (basisForm x'.1 x'.2) (basisForm x.1 x.2)
def complexHessianOperator (U B : Edge L n k j → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  open Classical in
  extendOddly fun b => if h : b.IsPositivelyOriented then
    ofPauliCoeffs (applyKernel (complexHessianKernel U) (toPauliCoeffs (restrictToPositiveEdges B)))
      ⟨b, h⟩ else 0
end PeriodicSide
namespace FullSpace
open YangMills.Construction.Tower.FaceEdgeFinsets.Unbounded (facesMeeting)
section Unbounded
variable {L k j : ℕ}
theorem faceVariable_eq_edge_product {a : ℝ} {G : Set ComplexMatrix2}
    {U : InfiniteLattice.Link a → ComplexMatrix2}
    (hU : IsFieldIn G U) (p : InfiniteLattice.ElementaryPlaquette a) :
    faceVariable U p =
      U (InfiniteLattice.Link.forwardFrom p.corner p.lowAxis) *
        U (InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.lowAxis)
          p.highAxis) *
        (U (InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.highAxis)
          p.lowAxis))⁻¹ *
        (U (InfiniteLattice.Link.forwardFrom p.corner p.highAxis))⁻¹ := by
  simp [faceVariable, linkHolonomy, faceBoundary, hU.2, mul_assoc]
def complexFaceTerm (U : Edge L k j → ComplexMatrix2) (p : Face L k j) : ℂ :=
  1 - (1 / 2) * ComplexMatrix2.fullTrace (faceVariable U p)
def faceTermSum (S : Set (Face L k j)) (U : Edge L k j → ComplexMatrix2) : ℂ :=
  ∑ᶠ p ∈ S, complexFaceTerm U p
def edgeSupport (B : Edge L k j → ComplexMatrix2) : Set (Edge L k j) :=
  {b | b.IsPositivelyOriented ∧ B b ≠ 0}
def HasFiniteEdgeSupport (B : Edge L k j → ComplexMatrix2) : Prop := (edgeSupport B).Finite
def complexActionDeriv (U B : Edge L k j → ComplexMatrix2) : ℂ :=
  holLeftDeriv OneLoop.pauliBasis (Equiv.funUnique (Fin 1) ℂ).symm
    (fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (faceTermSum (facesMeeting (edgeSupport B))) U B
def complexActionHessian (U B B' : Edge L k j → ComplexMatrix2) : ℂ :=
  holLeftSecondDeriv OneLoop.pauliBasis (Equiv.funUnique (Fin 1) ℂ).symm
    (fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (faceTermSum (facesMeeting (edgeSupport B ∪ edgeSupport B'))) U B B'
def basisForm (a : Fin 3) (b : PositiveEdge (meshAt L k j)) :
    Edge L k j → ComplexMatrix2 :=
  open Classical in
  extendOddly fun b' => if b' = b.1 then ComplexMatrix2.pauliFamily a else 0
def complexHessianKernel (U : Edge L k j → ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge (meshAt L k j))
      (Fin 3 × PositiveEdge (meshAt L k j)) :=
  fun x' x => complexActionHessian U (basisForm x'.1 x'.2) (basisForm x.1 x.2)
def complexHessianOperator (U B : Edge L k j → ComplexMatrix2) : Edge L k j → ComplexMatrix2 :=
  open Classical in
  extendOddly fun b => if h : b.IsPositivelyOriented then
    ofPauliCoeffs (applyKernel (complexHessianKernel U) (toPauliCoeffs (restrictToPositiveEdges B)))
      ⟨b, h⟩ else 0
end Unbounded
end FullSpace
end Tower
end YangMills.Construction
end
