import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
namespace RealLinearMaps
variable {L m k : ℕ}
def cubeMinusCentre (i : ℕ) (y : Vertex L m k (i + 1)) : Set (Vertex L m k i) :=
  {x | x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y ∧
    (x : PeriodicLattice.FourTorus L m) ≠ (y : PeriodicLattice.FourTorus L m)}
def extendByZero (g : Vertex L m k k → Matrices.ComplexMatrix2) :
    Vertex L m k 0 → Matrices.ComplexMatrix2 :=
  open Classical in fun x =>
    if hx : (x : PeriodicLattice.FourTorus L m) ∈
        PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k k) then
      g ⟨x, hx⟩
    else 0
structure StepLinearity (L m k i : ℕ) : Prop where
  blocks_pairwiseDisjoint : Pairwise fun y z : Vertex L m k (i + 1) =>
    Disjoint (cubeMinusCentre i y) (cubeMinusCentre i z)
  iUnion_blocks : ⋃ y : Vertex L m k (i + 1), cubeMinusCentre i y =
    {x : Vertex L m k i | (x : PeriodicLattice.FourTorus L m) ∉
      PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k (i + 1))}
  contourLogDeriv_isLinear : EventuallyNearIdentity (fieldSpace L m k i) fun V =>
    ∃ T : edgeFormSpace L m k i →ₗ[ℝ] fineOnlyFunctions L m k i, ∀ A : edgeFormSpace L m k i,
      (T A : FineOnlyVertex L m k i → Matrices.ComplexMatrix2) =
        contourLogDeriv L m k i V (A : Edge L m k i → Matrices.ComplexMatrix2)
  contourLogDrift_isLinear : EventuallyNearIdentity (fieldSpace L m k i) fun V =>
    ∃ T : edgeFormSpace L m k i →ₗ[ℝ] vertexFunctionSpace L m k (i + 1),
      ∀ A : edgeFormSpace L m k i,
      (T A : Vertex L m k (i + 1) → Matrices.ComplexMatrix2) =
        contourLogDrift V (A : Edge L m k i → Matrices.ComplexMatrix2)
  adjointCubeAverage_isLinear : EventuallyNearIdentity (fieldSpace L m k i) fun V =>
    ∃ T : vertexFunctionSpace L m k i →ₗ[ℝ] vertexFunctionSpace L m k (i + 1),
      ∀ f : vertexFunctionSpace L m k i,
      (T f : Vertex L m k (i + 1) → Matrices.ComplexMatrix2) =
        adjointCubeAverage V (f : Vertex L m k i → Matrices.ComplexMatrix2)
  complexSmoothingDeriv_isLinear : EventuallyNearIdentity (fieldSpace L m k i) fun V =>
    ∃ T : edgeFormSpace L m k i →ₗ[ℝ] edgeFormSpace L m k (i + 1), ∀ A : edgeFormSpace L m k i,
      (T A : Edge L m k (i + 1) → Matrices.ComplexMatrix2) =
        complexSmoothingDeriv V (A : Edge L m k i → Matrices.ComplexMatrix2)
  covariantSmoothingDeriv_isLinear : EventuallyNearIdentity (fieldSpace L m k i) fun V =>
    ∃ T : edgeFormSpace L m k i →ₗ[ℝ] edgeFormSpace L m k (i + 1), ∀ A : edgeFormSpace L m k i,
      (T A : Edge L m k (i + 1) → Matrices.ComplexMatrix2) =
        covariantSmoothingDeriv V (A : Edge L m k i → Matrices.ComplexMatrix2)
  complexIterDeriv_isLinear : EventuallyNearIdentity (fieldSpace L m k 0) fun U =>
    ∃ T : edgeFormSpace L m k 0 →ₗ[ℝ] edgeFormSpace L m k (i + 1), ∀ A : edgeFormSpace L m k 0,
      (T A : Edge L m k (i + 1) → Matrices.ComplexMatrix2) =
        complexIterDeriv L m k (i + 1) U (A : Edge L m k 0 → Matrices.ComplexMatrix2)
  iterCovariantDeriv_isLinear : EventuallyNearIdentity (fieldSpace L m k 0) fun U =>
    ∃ T : edgeFormSpace L m k 0 →ₗ[ℝ] edgeFormSpace L m k (i + 1), ∀ A : edgeFormSpace L m k 0,
      (T A : Edge L m k (i + 1) → Matrices.ComplexMatrix2) =
        iterCovariantDeriv L m k U (i + 1) (A : Edge L m k 0 → Matrices.ComplexMatrix2)
  iterContourLogDrift_isLinear : EventuallyNearIdentity (fieldSpace L m k 0) fun U =>
    ∃ T : edgeFormSpace L m k 0 →ₗ[ℝ] vertexFunctionSpace L m k (i + 1),
      ∀ A : edgeFormSpace L m k 0,
      (T A : Vertex L m k (i + 1) → Matrices.ComplexMatrix2) =
        iterContourLogDrift L m k U (i + 1) (A : Edge L m k 0 → Matrices.ComplexMatrix2)
  iterAdjointCubeAverage_isLinear : EventuallyNearIdentity (fieldSpace L m k 0) fun U =>
    ∃ T : vertexFunctionSpace L m k 0 →ₗ[ℝ] vertexFunctionSpace L m k (i + 1),
      ∀ f : vertexFunctionSpace L m k 0,
      (T f : Vertex L m k (i + 1) → Matrices.ComplexMatrix2) =
        iterAdjointCubeAverage L m k U (i + 1) (f : Vertex L m k 0 → Matrices.ComplexMatrix2)
structure RestrictionTranspose (L m k : ℕ)
    (r : (pairedFunctions (Vertex L m k 0)).realSubmodule →ₗ[ℝ]
      (pairedFunctions (Vertex L m k k)).realSubmodule) :
    Prop where
  pair_transpose : ∀ (g : (pairedFunctions (Vertex L m k k)).realSubmodule)
    (f : (pairedFunctions (Vertex L m k 0)).realSubmodule),
      traceFinsumPairing (PairedFunctionSpace.realTransposeMap r g).1 f.1 =
        traceFinsumPairing g.1 (r f).1
  transpose_eq_extendByZero : ∀ g : (pairedFunctions (Vertex L m k k)).realSubmodule,
    (PairedFunctionSpace.realTransposeMap r g).1 = extendByZero (L := L) (m := m) (k := k) g.1
  comp_transpose : ∀ g : (pairedFunctions (Vertex L m k k)).realSubmodule,
    r (PairedFunctionSpace.realTransposeMap r g) = g
  surjective : Function.Surjective r
structure TowerLinearity (L m k : ℕ) : Prop where
  covDiff_isLinear : ∀ i ≤ k, ∀ V ∈ fieldSpace L m k i,
    ∃ T : vertexFunctionSpace L m k i →ₗ[ℝ] edgeFormSpace L m k i,
      ∀ f : vertexFunctionSpace L m k i,
      (T f : Edge L m k i → Matrices.ComplexMatrix2) =
        covDiff V (f : Vertex L m k i → Matrices.ComplexMatrix2)
  contourFamily_isLinear : EventuallyNearIdentity (fieldSpace L m k k) fun W =>
    ∃ T : edgeFormSpace L m k 0 →ₗ[ℝ] fineOnlyFamilySpace L m k, ∀ A : edgeFormSpace L m k 0,
      (T A : FineOnlyFamily L m k) = contourFamily W A
  exists_restriction : ∃ r : (pairedFunctions (Vertex L m k 0)).realSubmodule →ₗ[ℝ]
      (pairedFunctions (Vertex L m k k)).realSubmodule,
    (∀ f : (pairedFunctions (Vertex L m k 0)).realSubmodule,
      (r f).1 = restrictVertexFunction (L := L) (m := m) (k := k) (j := 0) k f.1) ∧
    RestrictionTranspose L m k r
def RealLinearMapsStatement : Prop :=
  ∀ L m k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 1 ≤ k →
    (∀ i < k, StepLinearity L m k i) ∧ TowerLinearity L m k
end RealLinearMaps
end YangMills.Construction.Tower
end
