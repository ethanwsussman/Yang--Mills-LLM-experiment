import YangMills.Construction.ReflectionPositivity.CoordinatesDoubledSpaceAndFunctionalsOfALinkMirror
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkPositivity
variable {D : MirrorData} (C : LinkLevel D)
def IsBoundedBorelFn (Φ : D.FieldSpace → ℂ) : Prop :=
  YangMills.Construction.TestFunctions.IsBoundedFun Φ ∧ Measurable[borel D.FieldSpace] Φ
def IsLinearOnPosHalf {n : ℕ} (w : Fin n → C.KernelLabel) : Prop :=
  ∀ (a b : ℂ), ∀ G₁ ∈ C.halfAlgebra .pos, ∀ G₂ ∈ C.halfAlgebra .pos,
    a • G₁ + b • G₂ ∈ C.halfAlgebra .pos ∧
      C.transferFunctional w (a • G₁ + b • G₂) =
        a * C.transferFunctional w G₁ + b * C.transferFunctional w G₂
def sumTerm (G G' : D.FieldSpace → ℂ) (k : C.KernelWord) : ℂ :=
  (C.seriesWeight k.2 : ℂ) * starRingEnd ℂ (C.transferFunctional k.2 G) * C.transferFunctional k.2 G'
def HasSumOfSquares : Prop :=
  ∀ G ∈ C.halfAlgebra .pos, ∀ G' ∈ C.halfAlgebra .pos,
    Summable (fun k => ‖sumTerm C G G' k‖) ∧
      HasSum (sumTerm C G G') (C.thetaForm G G')
def TransferExpansion : Prop :=
  Countable C.KernelWord ∧
    (∀ {n : ℕ} (w : Fin n → C.KernelLabel), 0 < C.seriesWeight w) ∧
    (∀ {n : ℕ} (w : Fin n → C.KernelLabel), IsLinearOnPosHalf C w) ∧
    (∀ {n : ℕ} (w : Fin n → C.KernelLabel), ∀ G ∈ C.halfAlgebra .pos,
      ‖C.transferFunctional w G‖ ≤ YangMills.Construction.TestFunctions.uniformNorm G) ∧
    (∀ G ∈ C.halfAlgebra .pos, IsBoundedBorelFn (G ∘ C.reflectField)) ∧
    HasSumOfSquares C
def FormSesquilinearOn (A : Set (D.FieldSpace → ℂ)) : Prop :=
  ∀ (a b : ℂ), ∀ G₁ ∈ A, ∀ G₂ ∈ A, ∀ H ∈ A,
    a • G₁ + b • G₂ ∈ A ∧
      C.thetaForm (a • G₁ + b • G₂) H =
        starRingEnd ℂ a * C.thetaForm G₁ H + starRingEnd ℂ b * C.thetaForm G₂ H ∧
      C.thetaForm H (a • G₁ + b • G₂) =
        a * C.thetaForm H G₁ + b * C.thetaForm H G₂
def FormHermitianOn (A : Set (D.FieldSpace → ℂ)) : Prop :=
  ∀ G ∈ A, ∀ G' ∈ A, C.thetaForm G' G = starRingEnd ℂ (C.thetaForm G G')
def FormNonnegOn (A : Set (D.FieldSpace → ℂ)) : Prop :=
  ∀ G ∈ A, 0 ≤ C.thetaForm G G
def FormCauchySchwarzOn (A : Set (D.FieldSpace → ℂ)) : Prop :=
  ∀ G ∈ A, ∀ G' ∈ A,
    ((‖C.thetaForm G G'‖ ^ 2 : ℝ) : ℂ) ≤ C.thetaForm G G * C.thetaForm G' G'
def IsPosHermitianFormOn (A : Set (D.FieldSpace → ℂ)) : Prop :=
  FormSesquilinearOn C A ∧ FormHermitianOn C A ∧ FormNonnegOn C A ∧ FormCauchySchwarzOn C A
def edgesInSlab (σ : SlabSide) : Set D.Edge :=
  {e | (e.source : D.Torus) ∈ C.openSlab σ ∧ (e.target : D.Torus) ∈ C.openSlab σ}
def NegHalfProperties : Prop :=
  (∀ G ∈ C.halfAlgebra .neg, G ∘ C.reflectField ∈ C.halfAlgebra .pos) ∧
    (∀ G ∈ C.halfAlgebra .neg, ∀ G' ∈ C.halfAlgebra .neg,
      C.thetaForm G G' =
        C.thetaForm (G ∘ C.reflectField) (G' ∘ C.reflectField)) ∧
    IsPosHermitianFormOn C (C.halfAlgebra .neg) ∧
    ∀ (σ : SlabSide) (Φ : D.FieldSpace → ℂ),
      D.IsBoundedMeasurableInLinks (edgesInSlab C σ) Φ → 0 ≤ C.thetaForm Φ Φ
def ReflectionPositivityAtLink : Prop :=
  ∀ (D : MirrorData) (C : LinkLevel D), TransferExpansion C ∧
    IsPosHermitianFormOn C (C.halfAlgebra .pos) ∧ NegHalfProperties C
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkPositivity
end
