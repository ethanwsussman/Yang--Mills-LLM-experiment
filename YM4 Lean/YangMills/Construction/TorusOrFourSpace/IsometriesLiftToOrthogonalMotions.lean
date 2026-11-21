import YangMills.Construction.Euclidean.OrthogonalIsometries
import YangMills.Construction.TorusOrFourSpace.IsometriesLargestDistanceAndOrdersOnOpenSubsets
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotions
import Mathlib
set_option autoImplicit false
open Matrix
open YangMills.Construction.Euclidean (RealMatrix4 hyperoctahedral4 O4)
open YangMills.Construction.Tower.OrthogonalMotions (IsIntegerMatrix)
noncomputable section
namespace YangMills.Construction.PeriodicSpace
def hyperoctahedralMatrices : Set RealMatrix4 :=
  {S | ∃ w ∈ hyperoctahedral4, ((w : O4) : RealMatrix4) = S}
def HyperoctahedralMatricesEqIntegerOrthogonal : Prop :=
  ∀ S : RealMatrix4, S ∈ hyperoctahedralMatrices ↔ S ∈ O4 ∧ IsIntegerMatrix S
namespace Kind
variable (D : Params) (E : Kind)
def motionMatrices : Kind → Set RealMatrix4
  | .euclidean => {S | S ∈ O4}
  | .torus => hyperoctahedralMatrices
def LiftsVia (f : E.Pt D → E.Pt D) (A : RealMatrix4) (b : Fin 4 → ℝ) : Prop :=
  ∀ x, f (E.quotMap D x) = E.quotMap D (A *ᵥ x + b)
def liftedMap (A : RealMatrix4) (b : Fin 4 → ℝ) : E.Pt D → E.Pt D :=
  @Classical.epsilon _ ⟨id⟩ fun f => LiftsVia D E f A b
def hyperoctahedralAct (w : RealMatrix4) : E.Pt D → E.Pt D := liftedMap D E w 0
def isometryInv (f : E.Pt D → E.Pt D) : E.Pt D → E.Pt D := Function.invFun f
def ContinuousPreservesCompact (f : E.Pt D → E.Pt D) : Prop :=
  MetricNotions.IsContinuousWrt (quotDist D E) (quotDist D E) f ∧
    ∀ K, IsCompactQ D E K → IsCompactQ D E (f '' K)
def HyperoctahedralPreservesPeriods : Prop :=
  ∀ w ∈ hyperoctahedralMatrices,
    (fun x => w *ᵥ x) '' (E.periodGroup D : Set (Fin 4 → ℝ)) = (E.periodGroup D : Set (Fin 4 → ℝ))
def IsometryHasLift : Prop :=
  ∀ f, IsIsometry D E f → ∃ A ∈ O4, ∃ b : Fin 4 → ℝ,
    LiftsVia D E f A b ∧ (E = Kind.torus → A ∈ hyperoctahedralMatrices)
def LiftedMapsAreIsometries : Prop :=
  ∀ (b : Fin 4 → ℝ), ∀ A ∈ motionMatrices E,
    (∃! f, LiftsVia D E f A b) ∧ LiftsVia D E (liftedMap D E A b) A b ∧
      IsIsometry D E (liftedMap D E A b)
def HyperoctahedralActIsometries : Prop :=
  ∀ w ∈ hyperoctahedralMatrices,
    (∀ x, hyperoctahedralAct D E w (E.quotMap D x) = E.quotMap D (w *ᵥ x)) ∧
      IsIsometry D E (hyperoctahedralAct D E w)
def TranslationIsometries : Prop :=
  ∀ (a : E.Pt D) (b : Fin 4 → ℝ), IsLift D E a b →
    liftedMap D E 1 b = (fun y => y + a) ∧ IsIsometry D E fun y => y + a
def IsometryBijective : Prop :=
  ∀ f, IsIsometry D E f → Function.Bijective f ∧
    Function.LeftInverse (isometryInv D E f) f ∧
      Function.RightInverse (isometryInv D E f) f
def IsometryInvLift : Prop :=
  ∀ f, IsIsometry D E f → ∀ A ∈ O4, ∀ b : Fin 4 → ℝ, LiftsVia D E f A b →
    IsIsometry D E (isometryInv D E f) ∧
      (∀ x, isometryInv D E f (E.quotMap D x) =
        E.quotMap D (A⁻¹ *ᵥ x - A⁻¹ *ᵥ b)) ∧
      (E = Kind.torus → A ∈ hyperoctahedralMatrices)
def IsometryContinuousCompact : Prop :=
  ∀ f, IsIsometry D E f → ContinuousPreservesCompact D E f ∧
    ContinuousPreservesCompact D E (isometryInv D E f)
def SupportCompIsometry : Prop :=
  ∀ f, IsIsometry D E f → ∀ (Z : Type) [Zero Z] (g : E.Pt D → Z),
    supportQ D E (g ∘ f) = f ⁻¹' supportQ D E g
def RegularityCompIsometry : Prop :=
  ∀ f, IsIsometry D E f → ∀ g : E.Pt D → ℝ,
    (IsC1Fn D E g → IsC1Fn D E (g ∘ f)) ∧ (IsSmoothFn D E g → IsSmoothFn D E (g ∘ f))
def SepTuplesCompIsometry : Prop :=
  ∀ f, IsIsometry D E f → ∀ n : ℕ, 1 ≤ n → ∀ g ∈ sepC1Tuples D E n,
    (fun i => g i ∘ f) ∈ sepC1Tuples D E n
def IsometryOrthogonalLiftTheorem : Prop :=
  HyperoctahedralMatricesEqIntegerOrthogonal ∧
    ∀ (D : Params) (E : Kind),
      HyperoctahedralPreservesPeriods D E ∧ IsometryHasLift D E ∧
        LiftedMapsAreIsometries D E ∧ HyperoctahedralActIsometries D E ∧
        TranslationIsometries D E ∧ IsometryBijective D E ∧
        IsometryInvLift D E ∧ IsometryContinuousCompact D E ∧
        SupportCompIsometry D E ∧ RegularityCompIsometry D E ∧
        SepTuplesCompIsometry D E
end Kind
end YangMills.Construction.PeriodicSpace
