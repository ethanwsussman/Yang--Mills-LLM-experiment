import YangMills.Construction.EuclideanFunctionals.FormsOfTheOperatorsOverTheWedge
import YangMills.Construction.EuclideanFunctionals.PlateOperatorOfALabelAProfileAndALength
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction
namespace ForwardTube
def translatedPower (A : Set (ℂ × ℂ)) (q : ℕ) (η : ℝ) : Set (Fin q → ℂ × ℂ) :=
  Set.univ.pi fun _ => (fun u => timeTranslate (η / 2) + u) '' A
def shiftedForwardTubePow (q : ℕ) (η : ℝ) : Set (Fin q → ℂ × ℂ) :=
  translatedPower forwardTube q η
end ForwardTube
namespace EuclideanFunctionals
open ForwardTube
namespace EuclidFunctionalWithRecon
variable {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
def alternatingVec : (n : ℕ) → (Fin n → ℂ × ℂ) →
    (Fin n → σ.space →L[ℂ] σ.space) → σ.space
  | 0, _, _ => σ.recon.vac
  | n + 1, w, B =>
    σ.wedgeIntegralOp (w 0) (B 0 (alternatingVec n (Fin.tail w) (Fin.tail B)))
def productOps {n : ℕ} (η : ℝ) (α : Fin n → RealPlane → ℂ)
    (φ : Fin n → RealPlane → ℝ) (a : Fin n) : σ.space →L[ℂ] σ.space :=
  productOperator σ (φ a) (α a) η
def productArgs {n : ℕ} (η : ℝ) (x : Fin n → ℂ × ℂ) (a : Fin n) : ℂ × ℂ :=
  if h : (a : ℕ) = 0 then x a - timeTranslate (η / 4)
  else x a - x ⟨a - 1, by omega⟩ - timeTranslate (η / 2)
def productVec {n : ℕ} (η : ℝ) (α : Fin n → RealPlane → ℂ)
    (φ : Fin n → RealPlane → ℝ) (x : Fin n → ℂ × ℂ) : σ.space :=
  σ.alternatingVec n (productArgs η x) (σ.productOps η α φ)
def productKernel {q : ℕ} (η : ℝ) (α : Fin (q + 1) → RealPlane → ℂ)
    (φ : Fin (q + 1) → RealPlane → ℝ) (v : Fin q → ℂ × ℂ) : ℂ :=
  ⟪σ.recon.vac, σ.productOps η α φ 0
    (σ.alternatingVec q (fun i => v i - timeTranslate (η / 2))
      (Fin.tail (σ.productOps η α φ)))⟫_ℂ
end EuclidFunctionalWithRecon
def entryProduct {n : ℕ} (h : Fin n → R4 → ℂ) : FreeSep := complexTuple h
theorem entryProduct_zero (h : Fin 0 → R4 → ℂ) : entryProduct h = toFree [] := by
  simp [entryProduct, complexTuple]
end EuclideanFunctionals
end YangMills.Construction
