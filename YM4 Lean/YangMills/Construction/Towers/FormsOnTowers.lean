import YangMills.Construction.Lattice.GaugeFieldSpacesAndRealAnalyticMaps
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
def traceFinsumPairing {ι : Type*} (f g : ι → Matrices.ComplexMatrix2) : ℂ :=
  ∑ᶠ i, Matrices.ComplexMatrix2.halfTrace (f i * g i)
def traceFinsumNorm {ι : Type*} (f : ι → Matrices.ComplexMatrix2) : ℝ :=
  Real.sqrt (traceFinsumPairing f f).re
def HasFiniteSupp {ι : Type*} (f : ι → Matrices.ComplexMatrix2) : Prop := (Function.support f).Finite
section FiniteSide
variable {L m k j : ℕ}
abbrev PositiveEdge (L m k j : ℕ) : Type :=
  PeriodicLattice.PositivelyOrientedBond L m (PeriodicLattice.levelDepth k j)
def edgeFormSpace (L m k j : ℕ) : Submodule ℝ (Edge L m k j → Matrices.ComplexMatrix2) where
  carrier := {A | PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra A}
  add_mem' := by
    rintro A A' ⟨hA, sA⟩ ⟨hA', sA'⟩
    refine ⟨fun e he => Matrices.ComplexMatrix2.hermitianTraceless.add_mem (hA e he) (hA' e he), fun e => ?_⟩
    simp only [Pi.add_apply, sA, sA']
    abel
  zero_mem' := ⟨fun e _ => Matrices.ComplexMatrix2.hermitianTraceless.zero_mem, fun e => by simp⟩
  smul_mem' := by
    rintro c A ⟨hA, sA⟩
    refine ⟨fun e he => Matrices.ComplexMatrix2.hermitianTraceless.smul_mem c (hA e he), fun e => ?_⟩
    simp only [Pi.smul_apply, sA, smul_neg]
abbrev vertexFunctionSpace (L m k j : ℕ) : Submodule ℝ (Vertex L m k j → Matrices.ComplexMatrix2) :=
  Matrices.GroupLieProduct.hermitianTracelessFunctions (Vertex L m k j)
abbrev faceFunctionSpace (L m k j : ℕ) : Submodule ℝ (Face L m k j → Matrices.ComplexMatrix2) :=
  Matrices.GroupLieProduct.hermitianTracelessFunctions (Face L m k j)
def restrictToPositiveEdges (A : Edge L m k j → Matrices.ComplexMatrix2) :
    PositiveEdge L m k j → Matrices.ComplexMatrix2 := fun e => A e
def edgeFormPairing (A A' : Edge L m k j → Matrices.ComplexMatrix2) : ℂ :=
  traceFinsumPairing (restrictToPositiveEdges A) (restrictToPositiveEdges A')
def edgeFormNorm (A : Edge L m k j → Matrices.ComplexMatrix2) : ℝ :=
  traceFinsumNorm (restrictToPositiveEdges A)
def vertexCoboundary (u : Vertex L m k j → Matrices.ComplexMatrix2) : Edge L m k j → Matrices.ComplexMatrix2 :=
  fun e => u e.target - u e.source
def edgeCoboundary (A : Edge L m k j → Matrices.ComplexMatrix2) : Face L m k j → Matrices.ComplexMatrix2 :=
  fun p => A (PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis) +
    A (PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L m _ p.firstAxis) p.secondAxis) -
    A (PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L m _ p.secondAxis) p.firstAxis) -
    A (PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis)
def IsClosedEdgeForm (A : Edge L m k j → Matrices.ComplexMatrix2) : Prop := edgeCoboundary A = 0
def IsTranslationInvariantEdgeForm (A : Edge L m k j → Matrices.ComplexMatrix2) : Prop :=
  ∀ (μ : Fin 4) (x y : Vertex L m k j),
    A (PeriodicLattice.Bond.forwardFrom x μ) = A (PeriodicLattice.Bond.forwardFrom y μ)
def restrictVertexFunction (i : ℕ) (u : Vertex L m k j → Matrices.ComplexMatrix2) :
    Vertex L m k i → Matrices.ComplexMatrix2 :=
  PeriodicLattice.restrictGaugeMap i u
def edgeFormPathSum (A : Edge L m k j → Matrices.ComplexMatrix2) (γ : List (Edge L m k j)) :
    Matrices.ComplexMatrix2 :=
  PeriodicLattice.bondFormSumAlong A γ
end FiniteSide
namespace FullSpace
section Forms
variable {a : ℝ}
abbrev PositiveEdge (a : ℝ) : Type :=
  {e : InfiniteLattice.Link a // e.IsPositivelyOriented}
def edgeFormSpace (a : ℝ) : Submodule ℝ (InfiniteLattice.Link a → Matrices.ComplexMatrix2) where
  carrier := {A | (∀ e : InfiniteLattice.Link a, e.IsPositivelyOriented →
      A e ∈ Matrices.ComplexMatrix2.hermitianTraceless) ∧
    ∀ e : InfiniteLattice.Link a, A e.opposite = -A e}
  add_mem' := by
    rintro A A' ⟨hA, sA⟩ ⟨hA', sA'⟩
    refine ⟨fun e he => Matrices.ComplexMatrix2.hermitianTraceless.add_mem (hA e he) (hA' e he), fun e => ?_⟩
    simp only [Pi.add_apply, sA, sA']
    abel
  zero_mem' := ⟨fun e _ => Matrices.ComplexMatrix2.hermitianTraceless.zero_mem, fun e => by simp⟩
  smul_mem' := by
    rintro c A ⟨hA, sA⟩
    refine ⟨fun e he => Matrices.ComplexMatrix2.hermitianTraceless.smul_mem c (hA e he), fun e => ?_⟩
    simp only [Pi.smul_apply, sA, smul_neg]
abbrev vertexFunctionSpace (a : ℝ) : Submodule ℝ (InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) :=
  Matrices.GroupLieProduct.hermitianTracelessFunctions (InfiniteLattice.LatticePoint a)
def restrictToPositiveEdges (A : InfiniteLattice.Link a → Matrices.ComplexMatrix2) :
    PositiveEdge a → Matrices.ComplexMatrix2 := fun e => A e
def finiteEdgePairing (A A' : InfiniteLattice.Link a → Matrices.ComplexMatrix2) : ℂ :=
  traceFinsumPairing (restrictToPositiveEdges A) (restrictToPositiveEdges A')
def vertexCoboundary (u : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) :
    InfiniteLattice.Link a → Matrices.ComplexMatrix2 :=
  fun e => u e.terminal - u e.initial
def edgeCoboundary (A : InfiniteLattice.Link a → Matrices.ComplexMatrix2) :
    InfiniteLattice.ElementaryPlaquette a → Matrices.ComplexMatrix2 :=
  fun p => A (InfiniteLattice.Link.forwardFrom p.corner p.lowAxis) +
    A (InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.lowAxis) p.highAxis) -
    A (InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.highAxis) p.lowAxis) -
    A (InfiniteLattice.Link.forwardFrom p.corner p.highAxis)
def restrictVertexFunction (b : ℝ) (u : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) :
    InfiniteLattice.LatticePoint b → Matrices.ComplexMatrix2 :=
  fun x => u (toFiner a x)
def edgeFormPathSum (A : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (γ : List (InfiniteLattice.Link a)) : Matrices.ComplexMatrix2 :=
  sumAlong A γ
end Forms
end FullSpace
end Tower
end YangMills.Construction
end
