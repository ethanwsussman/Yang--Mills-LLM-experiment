import YangMills.Construction.Lattice.DecayingKernels
import YangMills.Construction.Lattice.DirichletLaplacianUnitMesh
import YangMills.Construction.Lattice.LocalizedDecayAnyMesh
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace DirichletLaplacian
open PeriodicLattice
variable {d N : ℕ} {hN : 0 < N}
variable (𝔟 : Set (Link d (Mesh.one hN))) (𝔭 : Set (DirichletLaplacian.Plaquette d (Mesh.one hN)))
  (𝔰 : Set (GridPoint d (Mesh.one hN)))
def dirichletShiftedOp : Module.End ℝ (supportedForms 𝔟) := dirichletOp 𝔟 𝔭 𝔰 1 - LinearMap.id
def dirichletOpExtended : OneForm d (Mesh.one hN) →ₗ[ℝ] OneForm d (Mesh.one hN) :=
  LinearMap.id + indicatorMul 𝔟 ∘ₗ maskedHodgeLaplacian 𝔭 𝔰 ∘ₗ indicatorMul 𝔟
def dirichletCompressedCov : OneForm d (Mesh.one hN) →ₗ[ℝ] OneForm d (Mesh.one hN) :=
  subspaceInverse (supportedForms 𝔟) (dirichletOpExtended 𝔟 𝔭 𝔰)
def IsMinimizingLift (B A : supportedForms 𝔟) : Prop :=
  A = B ∧ ∀ A' : supportedForms 𝔟, A' = B →
    inner ℝ (A : OneForm d (Mesh.one hN)) (dirichletShiftedOp 𝔟 𝔭 𝔰 A : OneForm d (Mesh.one hN)) ≤
      inner ℝ (A' : OneForm d (Mesh.one hN)) (dirichletShiftedOp 𝔟 𝔭 𝔰 A' : OneForm d (Mesh.one hN))
structure DirichletReprFacts : Prop where
  ker_constraint_eq : LinearMap.ker (LinearMap.id :
    SiteFun d (Mesh.one hN) →ₗ[ℝ] SiteFun d (Mesh.one hN)) = ⊥
  gaugeProj_eq_zero :
    (((⊥ : Submodule ℝ (SiteFun d (Mesh.one hN))).map (discreteLaplacian (Mesh.one hN))).starProjection :
      SiteFun d (Mesh.one hN) →L[ℝ] SiteFun d (Mesh.one hN)) = 0
  gaugeSpace_trivial : ∀ ω : SiteFun d (Mesh.one hN),
    (∀ y, y ∉ (∅ : Set (GridPoint d (Mesh.one hN))) → ω y = 0) → ω = 0
  gaugeCov_eq_zero : ∀ T : SiteFun d (Mesh.one hN) →ₗ[ℝ] SiteFun d (Mesh.one hN),
    subspaceInverse ⊥ T = 0
  ker_id_eq : LinearMap.ker (LinearMap.id : supportedForms 𝔟 →ₗ[ℝ] supportedForms 𝔟) = ⊥
  kernelCov_eq_zero : subspaceInverse ⊥ (dirichletShiftedOp 𝔟 𝔭 𝔰) = 0
  isMinimizingLift_iff : ∀ B A : supportedForms 𝔟, IsMinimizingLift 𝔟 𝔭 𝔰 B A ↔ A = B
  inner_dirichletShiftedOp : ∀ B : supportedForms 𝔟,
    inner ℝ (B : OneForm d (Mesh.one hN)) (dirichletShiftedOp 𝔟 𝔭 𝔰 B : OneForm d (Mesh.one hN)) =
      ‖indicatorMul 𝔭 (discreteCurl (Mesh.one hN) (B : OneForm d (Mesh.one hN)))‖ ^ 2 +
        ‖indicatorMul 𝔰 (LinearMap.adjoint (discreteGrad (Mesh.one hN)) (B : OneForm d (Mesh.one hN)))‖ ^ 2
  inner_dirichletOp : ∀ B : supportedForms 𝔟,
    ‖(B : OneForm d (Mesh.one hN))‖ ^ 2 +
        ‖indicatorMul 𝔭 (discreteCurl (Mesh.one hN) (B : OneForm d (Mesh.one hN)))‖ ^ 2 +
        ‖indicatorMul 𝔰 (LinearMap.adjoint (discreteGrad (Mesh.one hN)) (B : OneForm d (Mesh.one hN)))‖ ^ 2 =
      inner ℝ (B : OneForm d (Mesh.one hN)) (dirichletOp 𝔟 𝔭 𝔰 1 B : OneForm d (Mesh.one hN))
  compressedCov_eq_green : dirichletCompressedCov 𝔟 𝔭 𝔰 = dirichletGreen 𝔟 𝔭 𝔰 (a := 1) one_pos
  inner_dirichletGreen : ∀ J : OneForm d (Mesh.one hN),
    inner ℝ J (dirichletGreen 𝔟 𝔭 𝔰 (a := 1) one_pos J) = inner ℝ J (dirichletCompressedCov 𝔟 𝔭 𝔰 J)
end DirichletLaplacian
namespace DirichletLaplacian
open PeriodicLattice
instance instNonemptyDecayConstants : Nonempty DecayConstants :=
  ⟨{ base := 1
     holder := fun _ => 1
     grad := fun _ => 1
     gradHolder := fun _ _ => 1
     base_pos := one_pos
     holder_pos := fun _ _ _ => one_pos
     grad_pos := fun _ _ _ => one_pos
     gradHolder_pos := fun _ _ _ _ _ => one_pos }⟩
end DirichletLaplacian
end YangMills.Construction
