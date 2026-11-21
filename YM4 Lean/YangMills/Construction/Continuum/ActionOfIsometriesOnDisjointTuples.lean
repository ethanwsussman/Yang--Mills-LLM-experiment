import YangMills.Construction.Continuum.TuplesOfDisjointSupports
import YangMills.Construction.Lattice.EuclideanIsometries
import Mathlib
set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
namespace YangMills.Construction.DisjointTuples
open InfiniteLattice SchwingerFunctions TestFunctions
namespace IsometryAction
def MapsC1cAndSupport (r : (Fin 4 → ℝ) → Fin 4 → ℝ) : Prop :=
  ∀ f : RealFun, IsC1c f →
    IsC1c (pushFun r f) ∧ tsupport (pushFun r f) = r '' tsupport f
def PreservesAppend (r : (Fin 4 → ℝ) → Fin 4 → ℝ) : Prop :=
  ∀ (X Y : DisjointTuple) (hXY : DisjointTuple.Appendable X Y),
    IsDisjointTuple (pushList r X.1) ∧ IsDisjointTuple (pushList r Y.1) ∧
      ∃ h : DisjointTuple.Appendable (pushTuple r X) (pushTuple r Y),
        pushTuple r (DisjointTuple.append X Y hXY) =
          DisjointTuple.append (pushTuple r X) (pushTuple r Y) h
def IntertwinesTranslations (A : Matrix (Fin 4) (Fin 4) ℝ) (r : (Fin 4 → ℝ) → Fin 4 → ℝ) :
    Prop :=
  ∀ v : Fin 4 → ℝ,
    r ∘ translate v = translate (A *ᵥ v) ∘ r ∧
    (∀ (E : Type) (g : (Fin 4 → ℝ) → E),
      pushFun r (pushFun (translate v) g) =
        pushFun (translate (A *ᵥ v)) (pushFun r g)) ∧
    (∀ X : DisjointTuple,
      pushTuple r (pushTuple (translate v) X) =
        pushTuple (translate (A *ᵥ v)) (pushTuple r X)) ∧
    ∀ F : FreeTupleSpace,
      liftMap (pushTuple r) (liftMap (pushTuple (translate v)) F) =
        liftMap (pushTuple (translate (A *ᵥ v))) (liftMap (pushTuple r) F)
def SharpNormInvariant (r : (Fin 4 → ℝ) → Fin 4 → ℝ) : Prop :=
  ∀ M : ℝ, 1 ≤ M → ∀ f : RealFun, IsC1c f →
    sharpNormR4 M (pushFun r f) = sharpNormR4 M f
def IntegralInvariant (r : (Fin 4 → ℝ) → Fin 4 → ℝ) : Prop :=
  ∀ f : RealFun, IsC1c f → ∫ x, pushFun r f x = ∫ x, f x
def PushFunComp : Prop :=
  ∀ r s : (Fin 4 → ℝ) → Fin 4 → ℝ, IsSpaceIsometry r → IsSpaceIsometry s →
    ∀ (E : Type) (g : (Fin 4 → ℝ) → E),
      pushFun (r ∘ s) g = pushFun r (pushFun s g)
def ExistsLinearNotMultilinear : Prop :=
  ∃ (φ : FreeTupleSpace →ₗ[ℂ] ℂ) (f g : RealFun) (X Y Z : DisjointTuple),
    IsC1c f ∧ IsC1c g ∧
      X.1 = [f] ∧ Y.1 = [g] ∧ Z.1 = [f + g] ∧
        φ (ofTuple Z) ≠ φ (ofTuple X) + φ (ofTuple Y)
def IsometryActionFacts : Prop :=
  (∀ (r : (Fin 4 → ℝ) → Fin 4 → ℝ) (c : Fin 4 → ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ),
    IsSpaceIsometry r → A ∈ O4 → r = affineEuclid A c →
      MapsC1cAndSupport r ∧ PreservesAppend r ∧ IntertwinesTranslations A r ∧
        SharpNormInvariant r ∧ IntegralInvariant r) ∧
    PushFunComp ∧ ExistsLinearNotMultilinear
end IsometryAction
end YangMills.Construction.DisjointTuples
