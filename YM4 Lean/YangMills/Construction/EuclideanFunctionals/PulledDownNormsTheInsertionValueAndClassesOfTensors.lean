import YangMills.Construction.EuclideanFunctionals.SymmetricEuclideanFunctionalWithReconstruction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
def singleComponent (f : R4 → ℂ) : FreeSep := complexTuple fun _ : Fin 1 => f
def pullDown (t : ℝ) (F : FreeSep) : FreeSep :=
  (EuclidMotion.transl ((-t) • timeVec)).actFree F
def insertion (S : ConnFamily) (F : FreeSep) (f : R4 → ℂ) (G : FreeSep) : ℂ :=
  centeredFnFree S (freeMul3 (flipConj F) (singleComponent f) G)
variable {s : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon s S)
def reconClass (F : FreeSep) : σ.space := readClass σ.recon.cls F
def heightNorm (t : ℝ) (F : FreeSep) : ℝ := ‖reconClass σ (pullDown t F)‖
def tensorClass {q : ℕ} (f : Fin q → R4 → ℂ) : σ.space :=
  reconClass σ (complexTuple f)
end YangMills.Construction.EuclideanFunctionals
