import YangMills.Construction.EuclideanFunctionals.SymmetricEuclideanFunctional
import Mathlib
set_option autoImplicit false
open YangMills.Construction.EuclideanSpectral
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
def conjReflection (w : EuclidMotion) : EuclidMotion := w * timeFlip * w⁻¹
def movedHalfSpace (w : EuclidMotion) : Set R4 := w '' upperHalf
section Transport
variable {c : SharpScale} {S : ConnFamily}
def movedClass (σ : SymmEuclidFunctional c S) (w : hyperoctahedral)
    (A : freeSpanIn (movedHalfSpace w)) : σ.space :=
  classOrZero σ.osData.cls ((w : EuclidMotion)⁻¹.actFree A.1)
end Transport
structure NormalPicture (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  refl : EuclidMotion
  half : Set R4
  cls : freeSpanIn half → H
  vac : H
  pvm : ProjMeasure H 4
  ham : pvm.fnDomain energyFn →ₗ[ℂ] H
  mom : ∀ j : Fin 3,
    pvm.fnDomain (fun p => (momCoord j p : ℂ)) →ₗ[ℂ] H
def normalPicture {c : SharpScale} {S : ConnFamily} (σ : SymmEuclidFunctional c S)
    (w : hyperoctahedral) : NormalPicture σ.space where
  refl := conjReflection w
  half := movedHalfSpace w
  cls := movedClass σ w
  vac := σ.osData.vac
  pvm := σ.osData.pvm
  ham := hamiltonianOp σ.osData.pvm
  mom := momentumOp σ.osData.pvm
end YangMills.Construction.EuclideanFunctionals
