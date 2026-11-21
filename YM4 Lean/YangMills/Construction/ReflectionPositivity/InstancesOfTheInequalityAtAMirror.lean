import YangMills.Construction.PassageToTheLimit.SeparatedTuplesMultilinearFunctionalsCentredFunctionalTensors
import YangMills.Construction.ReflectionPositivity.CombinationsOfTuples
import YangMills.Construction.ReflectionPositivity.SupportsTranslationsSeparationAndTransportOfTuples
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
namespace Ambient
variable (D : MirrorData)
def sepLipTuples : Set (FnList D torus) :=
  {X | LimitSpaces.Ambient.periodic.IsSepLipTuple D.toStandingParameters Set.univ X.get}
def sepLipTuplesSuppIn (O : Set (torus.Point D)) : Set (FnList D torus) :=
  {X | X ∈ sepLipTuples D ∧
    ∀ f ∈ X, LimitSpaces.Ambient.periodic.SupportedWithin D.toStandingParameters O f}
end Ambient
namespace CoordMirror
open Ambient
variable (D : MirrorData) (S : CoordMirror) (E : Ambient)
def positivitySum {A : Set (FnList D E)} (σ : A → ℂ) {r : ℕ} (X : Fin r → FnList D E)
    (c : Fin r → ℂ) : ℂ :=
  ∑ i, ∑ k, conj (c i) * c k * evalOrZeroC σ (S.reflectAppend D E (X i) (X k))
def suppUnion {r : ℕ} (X : Fin r → FnList D E) : Set (E.Point D) :=
  ⋃ i, listSupport D E (X i)
structure PositivityInstance where
  size : ℕ
  one_le_size : 1 ≤ size
  tuples : Fin size → separatedWithin D E (S.upperSide D E)
  coeffs : Fin size → ℂ
namespace PositivityInstance
variable {D S E}
def lhs (I : S.PositivityInstance D E) (σ : separatedAll D E → ℂ) : ℂ :=
  S.positivitySum D E σ (fun i => (I.tuples i : FnList D E)) I.coeffs
def Holds (I : S.PositivityInstance D E) (σ : separatedAll D E → ℂ) : Prop :=
  (I.lhs σ).im = 0 ∧ 0 ≤ (I.lhs σ).re
def HoldsReal (I : S.PositivityInstance D E) (σ : separatedAll D E → ℝ) : Prop :=
  I.Holds fun X => (σ X : ℂ)
def suppUnion (I : S.PositivityInstance D E) : Set (E.Point D) :=
  CoordMirror.suppUnion D E fun i => (I.tuples i : FnList D E)
def distToMirror (I : S.PositivityInstance D E) : ℝ≥0∞ :=
  setDist D E I.suppUnion (S.carrier D E)
end PositivityInstance
structure LipPositivityInstance where
  size : ℕ
  one_le_size : 1 ≤ size
  tuples : Fin size → sepLipTuplesSuppIn D (S.upperSide D torus)
  coeffs : Fin size → ℂ
namespace LipPositivityInstance
variable {D S}
def lhs (I : S.LipPositivityInstance D) (σ : sepLipTuples D → ℂ) : ℂ :=
  S.positivitySum D torus σ (fun i => (I.tuples i : FnList D torus)) I.coeffs
def Holds (I : S.LipPositivityInstance D) (σ : sepLipTuples D → ℂ) : Prop :=
  (I.lhs σ).im = 0 ∧ 0 ≤ (I.lhs σ).re
def HoldsReal (I : S.LipPositivityInstance D) (σ : sepLipTuples D → ℝ) : Prop :=
  I.Holds fun X => (σ X : ℂ)
end LipPositivityInstance
end CoordMirror
end YangMills.Construction.ReflectionPositivity.AxisMirror
end
