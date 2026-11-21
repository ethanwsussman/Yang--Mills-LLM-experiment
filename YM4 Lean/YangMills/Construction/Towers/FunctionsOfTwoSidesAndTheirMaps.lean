import YangMills.Construction.Towers.KernelsOfThreeMapsOfATower
import YangMills.Construction.Towers.LatticesFormsAndKernelsInTheUnitsOfTheTopLevel
import YangMills.Construction.Towers.PeriodicExtensionsLocalKernelsAndKernelsThatDescend
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.UnitScale.OneStepChart
structure TwoScaleFunctions where
  fullSpace : PairedFunctionSpace
  torusSpace : PairedFunctionSpace
  extend : (torusSpace.index → Matrices.ComplexMatrix2) → fullSpace.index → Matrices.ComplexMatrix2
  Slot : Type
  eval : (fullSpace.index → Matrices.ComplexMatrix2) → Slot → Matrices.ComplexMatrix2
  shift : (Fin 4 → ℤ) → (fullSpace.index → Matrices.ComplexMatrix2) → fullSpace.index →
    Matrices.ComplexMatrix2
def vertexFunctions (L m k j : ℕ) : TwoScaleFunctions where
  fullSpace := pairedFunctions (FullSpace.Vertex L k j)
  torusSpace := pairedFunctions (Vertex L m k j)
  extend := fun f x => f (FullSpace.projVertex L m k j x)
  Slot := FullSpace.Vertex L k j
  eval := fun f => f
  shift := fun z f (x : FullSpace.Vertex L k j) => f (x + integerPoint _ (-z))
def edgeForms (L m k j : ℕ) : TwoScaleFunctions where
  fullSpace := FullSpace.edgePairedSpace (meshAt L k j)
  torusSpace := edgePairedSpace L m k j
  extend := fun f b => f (FullSpace.projEdge L m k j b)
  Slot := FullSpace.PositiveEdge (meshAt L k j)
  eval := FullSpace.restrictToPositiveEdges
  shift := fun z f b =>
    f (linkTranslate (b : FullSpace.Edge L k j) (integerPoint _ (-z)))
def faceFunctions (L m k j : ℕ) : TwoScaleFunctions where
  fullSpace := pairedFunctions (FullSpace.Face L k j)
  torusSpace := pairedFunctions (Face L m k j)
  extend := fun f p => f (FullSpace.projFace L m k j p)
  Slot := FullSpace.Face L k j
  eval := fun f => f
  shift := fun z f p =>
    f ⟨InfiniteLattice.ElementaryPlaquette.corner (p : FullSpace.Face L k j) + integerPoint _ (-z),
      InfiniteLattice.ElementaryPlaquette.lowAxis (p : FullSpace.Face L k j),
      InfiniteLattice.ElementaryPlaquette.highAxis (p : FullSpace.Face L k j),
      InfiniteLattice.ElementaryPlaquette.lowAxis_lt_highAxis (p : FullSpace.Face L k j)⟩
def fineOnlyVertexFunctions (L m k j : ℕ) : TwoScaleFunctions where
  fullSpace := pairedFunctions (FullSpace.FineOnlyVertex (meshAt L k (j + 1)) (meshAt L k j))
  torusSpace := pairedFunctions (FineOnlyVertex L m k j)
  extend := open Classical in fun f x =>
    if h : ((FullSpace.projVertex L m k j
          (x : FullSpace.FineOnlyVertex (meshAt L k (j + 1)) (meshAt L k j)).1 :
            Vertex L m k j) : PeriodicLattice.FourTorus L m) ∉
        PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k (j + 1)) then
      f ⟨FullSpace.projVertex L m k j
        (x : FullSpace.FineOnlyVertex (meshAt L k (j + 1)) (meshAt L k j)).1, h⟩ else 0
  Slot := FullSpace.FineOnlyVertex (meshAt L k (j + 1)) (meshAt L k j)
  eval := fun f => f
  shift := open Classical in fun z f x =>
    if h : (((x : FullSpace.FineOnlyVertex (meshAt L k (j + 1)) (meshAt L k j)).1 +
          integerPoint _ (-z) : FullSpace.Vertex L k j) : InfiniteLattice.AmbientSpace) ∉
        InfiniteLattice.latticeSubgroup (meshAt L k (j + 1)) then
      f ⟨(x : FullSpace.FineOnlyVertex (meshAt L k (j + 1)) (meshAt L k j)).1 +
        integerPoint _ (-z), h⟩ else 0
def HasRealFiniteKernel (X Y : TwoScaleFunctions)
    (O : (X.fullSpace.index → Matrices.ComplexMatrix2) → Y.fullSpace.index → Matrices.ComplexMatrix2) :
    Prop :=
  ∃ K : Y.Slot → X.Slot → ℝ, (∀ q, {p | K q p ≠ 0}.Finite) ∧ ∀ f ∈ X.fullSpace.complexSubmodule, ∀ q,
    Y.eval (O f) q = ∑ᶠ p, K q p • X.eval f p
def CommutesWithShift (X Y : TwoScaleFunctions)
    (O : (X.fullSpace.index → Matrices.ComplexMatrix2) → Y.fullSpace.index → Matrices.ComplexMatrix2) :
    Prop :=
  ∀ z, ∀ f ∈ X.fullSpace.complexSubmodule, O (X.shift z f) = Y.shift z (O f)
structure TwoScaleMap (X Y : TwoScaleFunctions)
    (O : (X.fullSpace.index → Matrices.ComplexMatrix2) → Y.fullSpace.index → Matrices.ComplexMatrix2)
    (O' : (X.torusSpace.index → Matrices.ComplexMatrix2) → Y.torusSpace.index →
      Matrices.ComplexMatrix2) : Prop where
  map_extend : ∀ f ∈ X.torusSpace.complexSubmodule, O (X.extend f) = Y.extend (O' f)
  transpose_map_extend : ∀ g ∈ Y.torusSpace.complexSubmodule,
    PairedFunctionSpace.transposeOfValues X.fullSpace Y.fullSpace O (Y.extend g) =
      X.extend (PairedFunctionSpace.transposeOfValues X.torusSpace Y.torusSpace O' g)
  commutes : CommutesWithShift X Y O
  transpose_commutes :
    CommutesWithShift Y X (PairedFunctionSpace.transposeOfValues X.fullSpace Y.fullSpace O)
  realKernel : HasRealFiniteKernel X Y O
  transpose_realKernel :
    HasRealFiniteKernel Y X (PairedFunctionSpace.transposeOfValues X.fullSpace Y.fullSpace O)
structure PeriodicCompatibility (L m k : ℕ) : Prop where
  vertexCoboundary : ∀ j, j ≤ k → TwoScaleMap (vertexFunctions L m k j) (edgeForms L m k j)
    FullSpace.vertexCoboundary Tower.vertexCoboundary
  edgeCoboundary : ∀ j, j ≤ k → TwoScaleMap (edgeForms L m k j) (faceFunctions L m k j)
    FullSpace.edgeCoboundary Tower.edgeCoboundary
  restrict : ∀ j, j < k → TwoScaleMap (vertexFunctions L m k j) (vertexFunctions L m k (j + 1))
    (FullSpace.restrictVertexFunction (meshAt L k (j + 1))) (Tower.restrictVertexFunction (j + 1))
  linear : ∀ j, j < k → TwoScaleMap (edgeForms L m k j) (edgeForms L m k (j + 1))
    (FullSpace.linearSmoothing L) (Tower.linearSmoothing L m k j)
  crossing : ∀ j, j < k → TwoScaleMap (edgeForms L m k j) (edgeForms L m k (j + 1))
    (FullSpace.crossingSmoothing L) (Tower.crossingSmoothing L m k j)
  cubeContour : ∀ j, j < k → TwoScaleMap (edgeForms L m k j) (vertexFunctions L m k (j + 1))
    (FullSpace.cubeContourAverage L) (Tower.cubeContourAverage L m k j)
  vertexSmoothing : ∀ j, j < k → TwoScaleMap (vertexFunctions L m k j) (vertexFunctions L m k (j + 1))
    (FullSpace.vertexSmoothing L) (Tower.vertexSmoothing L m k j)
  fineOnlyContour : ∀ j, j < k →
    TwoScaleMap (edgeForms L m k j) (fineOnlyVertexFunctions L m k j)
      (FullSpace.fineOnlyContourAverage L (a := meshAt L k (j + 1)) (a' := meshAt L k j))
      (Tower.fineOnlyContourAverage L m k j)
  linearIter : ∀ j, j ≤ k → TwoScaleMap (edgeForms L m k 0) (edgeForms L m k j)
    (FullSpace.linearSmoothingIter L k j) (Tower.linearSmoothingIter L m k j)
  crossingIter : ∀ j, j ≤ k → TwoScaleMap (edgeForms L m k 0) (edgeForms L m k j)
    (FullSpace.crossingSmoothingIter L k j) (Tower.crossingSmoothingIter L m k j)
  vertexSmoothingIter : ∀ j, j ≤ k → TwoScaleMap (vertexFunctions L m k 0) (vertexFunctions L m k j)
    (FullSpace.vertexSmoothingIter L k j) (Tower.vertexSmoothingIter L m k j)
  cubeContourIter : ∀ j, j ≤ k →
    TwoScaleMap (edgeForms L m k 0) (vertexFunctions L m k j)
      (FullSpace.cubeContourAverageIter L k j) (Tower.cubeContourAverageIter L m k j)
structure IsSlotEvaluation (S : PairedFunctionSpace) (P : Type)
    (v : (S.index → Matrices.ComplexMatrix2) → P → Matrices.ComplexMatrix2) : Prop where
  eval_mem : ∀ f ∈ S.complexSubmodule, ∀ p, v f p ∈ Matrices.ComplexMatrix2.traceless
  exists_eval_eq : ∀ w : P → Matrices.ComplexMatrix2, (∀ p, w p ∈ Matrices.ComplexMatrix2.traceless) →
    ∃ f ∈ S.complexSubmodule, v f = w
  eq_of_eval_eq : ∀ f ∈ S.complexSubmodule, ∀ g ∈ S.complexSubmodule, v f = v g → f = g
  eval_add : ∀ f ∈ S.complexSubmodule, ∀ g ∈ S.complexSubmodule, v (f + g) = v f + v g
  eval_smul : ∀ z : ℂ, ∀ f ∈ S.complexSubmodule, v (z • f) = z • v f
  isFinitelySupported_iff : ∀ f ∈ S.complexSubmodule,
    S.IsFinitelySupported f ↔ (Function.support (v f)).Finite
  pair_eq : ∀ f g, S.pair f g = traceFinsumPairing (v f) (v g)
structure CellCoordinates (s : ℕ) (X : TwoScaleFunctions) where
  TorusSlot : Type
  torusEval : (X.torusSpace.index → Matrices.ComplexMatrix2) → TorusSlot → Matrices.ComplexMatrix2
  proj : X.Slot → TorusSlot
  shiftSlot : (Fin 4 → ℤ) → X.Slot → X.Slot
  full_basis : IsSlotEvaluation X.fullSpace X.Slot X.eval
  torus_coordinates : IsSlotEvaluation X.torusSpace TorusSlot torusEval
  finite_torusSlot : Finite TorusSlot
  extend_mem : ∀ f ∈ X.torusSpace.complexSubmodule, X.extend f ∈ X.fullSpace.complexSubmodule
  eval_extend : ∀ f ∈ X.torusSpace.complexSubmodule, ∀ p,
    X.eval (X.extend f) p = torusEval f (proj p)
  proj_surjective : Function.Surjective proj
  proj_eq_iff : ∀ p p', proj p = proj p' ↔ ∃ v : Fin 4 → ℤ, p' = shiftSlot (s • v) p
  shiftSlot_zero : ∀ p, shiftSlot 0 p = p
  shiftSlot_add : ∀ z z' p, shiftSlot (z + z') p = shiftSlot z (shiftSlot z' p)
  eq_zero_of_shiftSlot_eq : ∀ z p, shiftSlot z p = p → z = 0
  shift_mem : ∀ z, ∀ f ∈ X.fullSpace.complexSubmodule, X.shift z f ∈ X.fullSpace.complexSubmodule
  eval_shift : ∀ z, ∀ f ∈ X.fullSpace.complexSubmodule, ∀ p,
    X.eval (X.shift z f) p = X.eval f (shiftSlot (-z) p)
structure PeriodicOperator (X Y : TwoScaleFunctions)
    (O : (X.fullSpace.index → Matrices.ComplexMatrix2) → Y.fullSpace.index → Matrices.ComplexMatrix2)
    (O' : (X.torusSpace.index → Matrices.ComplexMatrix2) → Y.torusSpace.index →
      Matrices.ComplexMatrix2) : Prop where
  full_mem : ∀ f ∈ X.fullSpace.complexSubmodule, O f ∈ Y.fullSpace.complexSubmodule
  torus_mem : ∀ f ∈ X.torusSpace.complexSubmodule, O' f ∈ Y.torusSpace.complexSubmodule
  map_extend : ∀ f ∈ X.torusSpace.complexSubmodule, O (X.extend f) = Y.extend (O' f)
  commutes : CommutesWithShift X Y O
  realKernel : HasRealFiniteKernel X Y O
end YangMills.Construction.Tower.UnitScale.OneStepChart
end
