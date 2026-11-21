import YangMills.Construction.Lattice.CubeGeometryAndTranslation
import YangMills.Construction.Lattice.DirichletUnitMeshGreen
import YangMills.Construction.Lattice.TwoScaleOperatorOnTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open ScaledFun
variable {d N : ℕ}
namespace Scales
variable {L j : ℕ} (S : Scales d L j N) (Λ' : Set (GridPoint d S.coarseMesh))
structure CenteredTwoScaleConclusions (δ : ℝ) (k : DecayConstants) : Prop where
  op_isSymmetric : (S.centeredTwoScaleOp Λ' 1).IsSymmetric
  op_pos : ∀ A : OneForm d S.fineMesh, A ≠ 0 → 0 < inner ℝ A (S.centeredTwoScaleOp Λ' 1 A)
  op_isUnit : IsUnit (S.centeredTwoScaleOp Λ' 1 : Module.End ℝ (OneForm d S.fineMesh))
  green_isSymmetric :
    ∀ h : IsUnit (S.centeredTwoScaleOp Λ' 1 : Module.End ℝ (OneForm d S.fineMesh)),
      LinearMap.IsSymmetric (S.centeredTwoScaleGreen Λ' 1 h)
  green_pos :
    ∀ (h : IsUnit (S.centeredTwoScaleOp Λ' 1 : Module.End ℝ (OneForm d S.fineMesh)))
      (A : OneForm d S.fineMesh), A ≠ 0 → 0 < inner ℝ A (S.centeredTwoScaleGreen Λ' 1 h A)
  green_eq_conj :
    ∀ h : IsUnit (S.centeredTwoScaleOp Λ' 1 : Module.End ℝ (OneForm d S.fineMesh)),
      S.centeredTwoScaleGreen Λ' 1 h = S.conjCentering (S.resolventRepresentation Λ')
  props : S.TwoScaleRepresentationProps Λ' (twoScaleDecayRate d L) (twoScaleNormBound d L)
  decay :
    ∀ h : IsUnit (S.centeredTwoScaleOp Λ' 1 : Module.End ℝ (OneForm d S.fineMesh)),
      S.HasLocalizedDecay δ k (S.centeredTwoScaleGreen Λ' 1 h)
end Scales
end PeriodicLattice
namespace CubeCovering
open PeriodicLattice
variable {L m : ℕ}
namespace Cube
variable {C : CubeData L m} (Q : Cube C)
structure BoundaryGreenConclusions {o : Q.Origin} (hQ : Q.IsBoundary) (B : Q.BoundaryData o)
    (δ : ℝ) (k : DecayConstants) : Prop where
  op_isSymmetric : (DirichletLaplacian.dirichletOp B.links B.plaquettes B.sites 1).IsSymmetric
  op_pos : ∀ A : DirichletLaplacian.supportedForms B.links, A ≠ 0 →
    0 < inner ℝ A (DirichletLaplacian.dirichletOp B.links B.plaquettes B.sites 1 A)
  green_isSymmetric : ∀ A A' : DirichletLaplacian.supportedForms B.links,
    inner ℝ (Q.boundaryGreen hQ o B A) (A' : OneForm 4 C.unitMeshOf) =
      inner ℝ (A : OneForm 4 C.unitMeshOf) (Q.boundaryGreen hQ o B A')
  green_pos : ∀ A : DirichletLaplacian.supportedForms B.links, A ≠ 0 →
    0 < inner ℝ (A : OneForm 4 C.unitMeshOf) (Q.boundaryGreen hQ o B A)
  repr : DirichletLaplacian.DirichletReprFacts B.links B.plaquettes B.sites
  decay : DirichletLaplacian.HasLocalizedDecayUnit δ k (Q.boundaryGreen hQ o B)
structure GreenConclusions (o : Q.Origin) (δ : ℝ) (k : DecayConstants) : Prop where
  of_interior : Q.IsInterior → Q.meshes.CenteredTwoScaleConclusions (coarseSiteSet o) δ k
  of_boundary : ∀ (hQ : Q.IsBoundary) (B : Q.BoundaryData o), Q.BoundaryGreenConclusions hQ B δ k
  of_subset : ∀ Λ' : Set (GridPoint 4 Q.meshes.coarseMesh), Q.meshes.CenteredTwoScaleConclusions Λ' δ k
end Cube
def IsCubeDecayPair (L : ℕ) (p : ℝ × DecayConstants) : Prop :=
  0 < p.1 ∧ ∀ (m : ℕ) (C : CubeData L m) (Q : Cube C) (o : Q.Origin), Q.GreenConclusions o p.1 p.2
def cubeDecayPair (L : ℕ) : ℝ × DecayConstants := Classical.epsilon (IsCubeDecayPair L)
def cubeDecayRate (L : ℕ) : ℝ := (cubeDecayPair L).1
def cubeDecayConstants (L : ℕ) : DecayConstants := (cubeDecayPair L).2
end CubeCovering
end YangMills.Construction
