import YangMills.Construction.Lattice.GreenOperatorsOfCubes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open ScaledFun
variable {d N : ℕ}
structure DilatedSite (d : ℕ) (s : Mesh N) (r : ℝ) where
  base : GridPoint d s
section Dilation
variable (s : Mesh N) (r : ℝ) (ι κ : Type)
def DilatedSite.equivSite : DilatedSite d s r ≃ GridPoint d s where
  toFun := DilatedSite.base
  invFun := DilatedSite.mk
  left_inv _ := rfl
  right_inv _ := rfl
instance : Fintype (DilatedSite d s r) := Fintype.ofEquiv _ (DilatedSite.equivSite s r).symm
variable (d) in
abbrev DilatedFun : Type := DilatedSite d s r → ℝ
variable (d) in
abbrev DilatedField : Type := ι × DilatedSite d s r → ℝ
variable (d) in
abbrev DilatedOneForm : Type := DilatedField d s r (Fin d)
def dilateFieldEquiv : DilatedField d s r ι ≃ₗ[ℝ] MultiField d s ι where
  toFun f := ofMap fun q => f (q.1, ⟨q.2⟩)
  invFun g := fun q => g (q.1, q.2.base)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
variable {ι κ}
variable (d) in
def dilatedInner {X : Type} [Fintype X] (f g : X → ℝ) : ℝ := ∑ x, (r * s.h) ^ d * f x * g x
variable [Fintype ι] [Fintype κ]
variable {s r}
def dilatedTorusDist (r : ℝ) (u u' : Torus d N) : ℝ := r * taxicabDist u u'
def dilatedDist (x x' : DilatedSite d s r) : ℝ :=
  dilatedTorusDist r (x.base : Torus d N) (x'.base : Torus d N)
variable (s r) in
def dilatedBall (u : Torus d N) : Set (DilatedSite d s r) :=
  {x | r * maxDist (x.base : Torus d N) u ≤ r}
def dilatedNormAt (f : DilatedField d s r ι) (x : DilatedSite d s r) : ℝ := ⨆ i, |f (i, x)|
def dilatedSupNorm (f : DilatedField d s r ι) : ℝ := ⨆ x, dilatedNormAt f x
def dilatedFunSupNorm (ζ : DilatedFun d s r) : ℝ := ⨆ x, |ζ x|
def dilatedHolderSup (lam α : ℝ) (v : DilatedSite d s r → DilatedSite d s r → ℝ) : ℝ :=
  sSup {t | ∃ x x' : DilatedSite d s r, 0 < dilatedDist x x' ∧ dilatedDist x x' ≤ lam ∧
    t = (lam / dilatedDist x x') ^ α * v x x'}
def funHolderAt (lam α : ℝ) (ζ : DilatedFun d s r) : ℝ :=
  dilatedHolderSup lam α fun x x' => |ζ x - ζ x'|
def fieldHolderAt (lam α : ℝ) (f : DilatedField d s r ι) : ℝ :=
  dilatedHolderSup lam α fun x x' => ⨆ i, |f (i, x) - f (i, x')|
end Dilation
section Decay
variable (s : Mesh N) (r : ℝ)
end Decay
namespace Scales
variable {L j : ℕ} (S : Scales d L j N) (Λ' : Set (GridPoint d S.coarseMesh)) (r r' : ℝ)
end Scales
end PeriodicLattice
namespace DirichletLaplacian
open PeriodicLattice
variable {d N : ℕ} {hN : 0 < N} (r ξ a : ℝ)
end DirichletLaplacian
namespace CubeCovering
open PeriodicLattice SeparatedSequences
variable {L m : ℕ}
namespace Cube
variable {C : CubeData L m} (Q : Cube C)
def unitScale : ℝ := C.levelScale Q.level
def decayWeight (o : Q.Origin) (δ : ℝ) (y y' : Space) : ℝ :=
  Real.exp (-δ * (Q.unitScale)⁻¹ * dilatedTorusDist Q.unitScale (chartAt o y) (chartAt o y'))
end Cube
end CubeCovering
end YangMills.Construction
