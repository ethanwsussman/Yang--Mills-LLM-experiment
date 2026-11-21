import YangMills.Construction.Lattice.PeriodicTorus
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
section Coefficients
variable {E F G X Y Z : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
def matrixCoeff (e : Y → F) (e' : X → E) (U : E →ₗ[ℝ] F) (p : Y) (q : X) : ℝ :=
  inner ℝ (e p) (U (e' q))
end Coefficients
def shiftOp (s : Mesh N) (v : GridPoint d s) : SiteFun d s →ₗ[ℝ] SiteFun d s where
  toFun f := ofMap fun x => f (x + v)
  map_add' f g := ScaledFun.ext fun x => by simp only [ofMap_apply, add_apply]
  map_smul' c f := ScaledFun.ext fun x => by
    simp only [ofMap_apply, smul_apply, RingHom.id_apply]
def twoFormCoeff {s : Mesh N} (F : TwoForm d s) (μ ν : Fin d) : SiteFun d s :=
  ofMap fun x =>
    if h : μ < ν then F (⟨(μ, ν), h⟩, x)
    else if h' : ν < μ then -F (⟨(ν, μ), h'⟩, x) else 0
variable (d) in
structure DifferenceOperatorIdentities (s : Mesh N) : Prop where
  adjoint_forwardDiff_eq_neg (μ : Fin d) (f : SiteFun d s) (x : GridPoint d s) :
    LinearMap.adjoint (forwardDiff s μ) f x = -forwardDiff s μ f (x - s.basisStep μ)
  neg_forwardDiff_eq (μ : Fin d) (f : SiteFun d s) (x : GridPoint d s) :
    -forwardDiff s μ f (x - s.basisStep μ) = s.h⁻¹ * (f (x - s.basisStep μ) - f x)
  forwardDiff_comm (μ ν : Fin d) :
    forwardDiff s μ ∘ₗ forwardDiff s ν = forwardDiff s ν ∘ₗ forwardDiff s μ
  forwardDiff_comm_adjoint (μ ν : Fin d) :
    forwardDiff s μ ∘ₗ LinearMap.adjoint (forwardDiff s ν) =
      LinearMap.adjoint (forwardDiff s ν) ∘ₗ forwardDiff s μ
  adjoint_comm (μ ν : Fin d) :
    LinearMap.adjoint (forwardDiff s μ) ∘ₗ LinearMap.adjoint (forwardDiff s ν) =
      LinearMap.adjoint (forwardDiff s ν) ∘ₗ LinearMap.adjoint (forwardDiff s μ)
  shiftOp_comm_forwardDiff (v : GridPoint d s) (μ : Fin d) :
    shiftOp s v ∘ₗ forwardDiff s μ = forwardDiff s μ ∘ₗ shiftOp s v
  shiftOp_comm_adjoint (v : GridPoint d s) (μ : Fin d) :
    shiftOp s v ∘ₗ LinearMap.adjoint (forwardDiff s μ) =
      LinearMap.adjoint (forwardDiff s μ) ∘ₗ shiftOp s v
  norm_forwardDiff_eq_norm_adjoint (μ : Fin d) (f : SiteFun d s) :
    ‖forwardDiff s μ f‖ = ‖LinearMap.adjoint (forwardDiff s μ) f‖
  norm_adjoint_le (μ : Fin d) (f : SiteFun d s) :
    ‖LinearMap.adjoint (forwardDiff s μ) f‖ ≤ 2 * s.h⁻¹ * ‖f‖
  adjoint_grad_apply (A : OneForm d s) :
    LinearMap.adjoint (discreteGrad s) A =
      ∑ μ, LinearMap.adjoint (forwardDiff s μ) (A.comp μ)
  adjoint_curl_comp (F : TwoForm d s) (ν : Fin d) :
    MultiField.comp (LinearMap.adjoint (discreteCurl s) F) ν =
      ∑ μ ∈ univ.erase ν, LinearMap.adjoint (forwardDiff s μ) (twoFormCoeff F μ ν)
  curl_comp_grad : discreteCurl s ∘ₗ discreteGrad (d := d) s = 0
  adjoint_grad_comp_grad :
    LinearMap.adjoint (discreteGrad s) ∘ₗ discreteGrad (d := d) s = discreteLaplacian s
  grad_comp_laplacian :
    discreteGrad s ∘ₗ discreteLaplacian (d := d) s = fieldLaplacian s (Fin d) ∘ₗ discreteGrad s
  hodge_decomp :
    fieldLaplacian (d := d) s (Fin d) =
      LinearMap.adjoint (discreteCurl s) ∘ₗ discreteCurl s +
        discreteGrad s ∘ₗ LinearMap.adjoint (discreteGrad s)
  inner_fieldLaplacian (ι : Type) [Fintype ι] [Nonempty ι] (f : MultiField d s ι) :
    inner ℝ f (fieldLaplacian s ι f) = ‖fieldGrad s ι f‖ ^ 2
  norm_fieldGrad_fieldGrad (ι : Type) [Fintype ι] [Nonempty ι] (f : MultiField d s ι) :
    ‖fieldGrad s (Fin d × ι) (fieldGrad s ι f)‖ = ‖fieldLaplacian s ι f‖
  norm_curl_sq_add_norm_adjoint_grad_sq (A : OneForm d s) :
    ‖discreteCurl s A‖ ^ 2 + ‖LinearMap.adjoint (discreteGrad s) A‖ ^ 2 =
      inner ℝ A (fieldLaplacian s (Fin d) A)
  inner_fieldLaplacian_oneForm_le (A : OneForm d s) :
    inner ℝ A (fieldLaplacian s (Fin d) A) ≤ 4 * d * (s.h ^ 2)⁻¹ * ‖A‖ ^ 2
  laplacian_eq_zero_iff (f : SiteFun d s) :
    discreteLaplacian s f = 0 ↔ ∃ c : ℝ, ∀ x, f x = c
def constOne (s : Mesh N) : SiteFun d s := ofMap fun _ => 1
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
structure CellIdentities : Prop where
  fineCell_partition (x : GridPoint d S.fineMesh) :
    ∃! y : GridPoint d S.unitMesh, x ∈ S.fineCell y
  fineCell_card (y : GridPoint d S.unitMesh) :
    ((S.fineCell y).card : ℝ) = (fineScale L j ^ d)⁻¹
  fineCell_shift (y : GridPoint d S.unitMesh) (μ : Fin d) :
    (fun x => x + S.unitToFine (S.unitMesh.basisStep μ)) ''
        (S.fineCell y : Set (GridPoint d S.fineMesh)) =
      S.fineCell (y + S.unitMesh.basisStep μ)
  coarseCell_partition (y : GridPoint d S.unitMesh) :
    ∃! y' : GridPoint d S.coarseMesh, y ∈ S.coarseCell y'
  coarseCell_card (y' : GridPoint d S.coarseMesh) : (S.coarseCell y').card = L ^ d
  coarseCell_shift (y' : GridPoint d S.coarseMesh) (μ : Fin d) :
    (fun y => y + S.coarseToUnit (S.coarseMesh.basisStep μ)) ''
        (S.coarseCell y' : Set (GridPoint d S.unitMesh)) =
      S.coarseCell (y' + S.coarseMesh.basisStep μ)
  fineFormAverage_comp_grad :
    S.fineFormAverage ∘ₗ discreteGrad S.fineMesh = discreteGrad S.unitMesh ∘ₗ S.fineSiteAverage
  coarseFormAverage_comp_grad :
    S.coarseFormAverage ∘ₗ discreteGrad S.unitMesh =
      discreteGrad S.coarseMesh ∘ₗ S.coarseSiteAverage
end Scales
end YangMills.Construction.PeriodicLattice
