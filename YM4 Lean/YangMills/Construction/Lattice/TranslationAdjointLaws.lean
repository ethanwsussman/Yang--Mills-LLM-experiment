import YangMills.Construction.Lattice.PeriodicTorus
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
def siteFunTranslation {s : Mesh N} (v : GridPoint d s) :
    SiteFun d s ≃ₗ[ℝ] SiteFun d s where
  toFun f := ofMap fun x => f (x - v)
  invFun f := ofMap fun x => f (x + v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := ScaledFun.ext fun x => by simp
  right_inv f := ScaledFun.ext fun x => by simp
def multiFieldTranslation {s : Mesh N} (ι : Type) (v : GridPoint d s) :
    MultiField d s ι ≃ₗ[ℝ] MultiField d s ι where
  toFun f := ofMap fun q => f (q.1, q.2 - v)
  invFun f := ofMap fun q => f (q.1, q.2 + v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := ScaledFun.ext fun q => by simp
  right_inv f := ScaledFun.ext fun q => by simp
structure IsOrthogonalCommutingFamily {s : Mesh N} {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (τ : GridPoint d s → E ≃ₗ[ℝ] E) : Prop where
  inner_eq : ∀ (v : GridPoint d s) (f g : E), inner ℝ (τ v f) (τ v g) = inner ℝ f g
  adjoint_eq : ∀ v : GridPoint d s,
    LinearMap.adjoint (τ v : E →ₗ[ℝ] E) = (τ (-v) : E →ₗ[ℝ] E)
  commute : ∀ v w : GridPoint d s,
    (τ v : E →ₗ[ℝ] E) ∘ₗ (τ w : E →ₗ[ℝ] E) = (τ w : E →ₗ[ℝ] E) ∘ₗ (τ v : E →ₗ[ℝ] E)
variable (d) in
structure ForwardDiffTranslationLaws (s : Mesh N) : Prop where
  siteFun_translations :
    IsOrthogonalCommutingFamily (siteFunTranslation (d := d) (s := s))
  multiField_translations : ∀ (ι : Type) [Fintype ι] [Nonempty ι],
    IsOrthogonalCommutingFamily (multiFieldTranslation (d := d) (s := s) ι)
  forwardDiff_eq : ∀ μ : Fin d, forwardDiff s μ =
    s.h⁻¹ • ((siteFunTranslation (-s.basisStep μ) : SiteFun d s →ₗ[ℝ] SiteFun d s) -
      LinearMap.id)
  adjoint_forwardDiff_eq : ∀ μ : Fin d, LinearMap.adjoint (forwardDiff s μ) =
    s.h⁻¹ • ((siteFunTranslation (s.basisStep μ) : SiteFun d s →ₗ[ℝ] SiteFun d s) -
      LinearMap.id)
  adjoint_forwardDiff_apply : ∀ (μ : Fin d) (f : SiteFun d s) (x : GridPoint d s),
    LinearMap.adjoint (forwardDiff s μ) f x = -(forwardDiff s μ f (x - s.basisStep μ))
  forwardDiff_comm : ∀ μ ν : Fin d,
    forwardDiff s μ ∘ₗ forwardDiff s ν = forwardDiff s ν ∘ₗ forwardDiff s μ
  adjoint_forwardDiff_comm : ∀ μ ν : Fin d,
    LinearMap.adjoint (forwardDiff s μ) ∘ₗ LinearMap.adjoint (forwardDiff s ν) =
      LinearMap.adjoint (forwardDiff s ν) ∘ₗ LinearMap.adjoint (forwardDiff s μ)
  forwardDiff_comm_adjoint : ∀ μ ν : Fin d,
    forwardDiff s μ ∘ₗ LinearMap.adjoint (forwardDiff s ν) =
      LinearMap.adjoint (forwardDiff s ν) ∘ₗ forwardDiff s μ
  forwardDiff_comm_translation : ∀ (μ : Fin d) (v : GridPoint d s),
    forwardDiff s μ ∘ₗ (siteFunTranslation v : SiteFun d s →ₗ[ℝ] SiteFun d s) =
      (siteFunTranslation v : SiteFun d s →ₗ[ℝ] SiteFun d s) ∘ₗ forwardDiff s μ
  adjoint_forwardDiff_comm_translation : ∀ (μ : Fin d) (v : GridPoint d s),
    LinearMap.adjoint (forwardDiff s μ) ∘ₗ
        (siteFunTranslation v : SiteFun d s →ₗ[ℝ] SiteFun d s) =
      (siteFunTranslation v : SiteFun d s →ₗ[ℝ] SiteFun d s) ∘ₗ
        LinearMap.adjoint (forwardDiff s μ)
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
end Scales
end YangMills.Construction.PeriodicLattice
