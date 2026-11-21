import YangMills.Construction.ForwardTube.ArgumentsOfTheGramKernel
import YangMills.Construction.RotationInvariance.PlaneKernelsOfTheFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals
open ForwardTube
def gramLabelOrder {n n' : ℕ} (φ : Fin n → realLabels) (φ' : Fin n' → realLabels) :
    Fin (n + n') → realLabels :=
  Fin.append (fun i => φ (Fin.rev i)) φ'
def gramKernelOfPoints (S : ConnFamily) {n n' : ℕ} (x : Fin n → ℂ × ℂ) (φ : Fin n → realLabels)
    (y : Fin n' → ℂ × ℂ) (φ' : Fin n' → realLabels) : ℂ :=
  if h : 2 ≤ n + n' then
    planeKernel S (q := n + n' - 1)
      (fun k => gramLabelOrder φ φ' (Fin.cast (by omega) k)) (gramKernelArgs x y)
  else if n + n' = 0 then 1 else 0
def gramKernel (S : ConnFamily) (p r : LabelledTuple) : ℂ :=
  gramKernelOfPoints S p.points p.labels r.points r.labels
def gramKernelImag (S : ConnFamily) (s : ℝ) (p r : LabelledTuple) : ℂ :=
  gramKernel S (LabelledTuple.imagBoost s p) (LabelledTuple.imagBoost s r)
end EuclideanFunctionals
end YangMills.Construction
end
