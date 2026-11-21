import YangMills.Construction.TorusOrFourSpace.BoxesStockOfSupportsAndFamilyOfTuples
import YangMills.Construction.TorusOrFourSpace.InducedMapsOfAdicIsometries
import YangMills.Construction.TorusOrFourSpace.StandingSignsOfTheSupportAdaptedFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.AdicIsometryGroup
open PeriodicLattice (SignedFrame)
open SupportAdapted
variable (D : Params) (E : Kind)
def AdicRationalsCountableSubring : Prop :=
  ∃ R : Subring ℚ, (R : Set ℚ).Countable ∧
    PeriodicLattice.adicGridPoints D.L = (fun x : ℚ => (x : ℝ)) '' (R : Set ℚ)
def FrameImageAdicPoints : Prop :=
  ∀ w : SignedFrame,
    imageSet w.actOnVector (adicPoints4 D.L) = adicPoints4 D.L
def EuclidAdicIsometriesCountableGroup : Prop :=
  (adicIsometriesR4 D.L).Countable ∧
    IsEuclidIsometryGroup (adicIsometriesR4 D.L)
def IsQuotHomeomorph (r : E.Pt D → E.Pt D) : Prop :=
  ∃ r' : E.Pt D → E.Pt D, r ∘ r' = id ∧ r' ∘ r = id ∧
    MetricNotions.IsContinuousWrt (Kind.quotDist D E) (Kind.quotDist D E) r ∧
    MetricNotions.IsContinuousWrt (Kind.quotDist D E) (Kind.quotDist D E) r'
def AdicIsometriesCountableHomeomorphGroup : Prop :=
  (Kind.adicIsometriesQ D E).Countable ∧ IsQuotIsometryGroup D E (Kind.adicIsometriesQ D E) ∧
    ∀ r ∈ Kind.adicIsometriesQ D E, IsQuotHomeomorph D E r
abbrev adicPointsQ : Set (E.Pt D) :=
  E.quotMap D '' adicPoints4 D.L
def translateBy (a' : E.Pt D) : E.Pt D → E.Pt D := fun y => y + a'
def FrameMapsAndShiftsMem : Prop :=
  (∀ w : SignedFrame, Kind.signedFrameMap D E w ∈ Kind.adicIsometriesQ D E) ∧
    ∀ a' ∈ adicPointsQ D E, translateBy D E a' ∈ Kind.adicIsometriesQ D E
def DescendedShiftedFrameMap : Prop :=
  ∀ a ∈ adicPoints4 D.L, ∀ w : SignedFrame,
    Kind.descendedMap D E (AdicInducedMaps.shiftedFrameMap a w) =
      fun y => Kind.signedFrameMap D E w y + E.quotMap D a
def generators : Set (Equiv.Perm (E.Pt D)) :=
  {g | (∃ w : SignedFrame, ⇑g = Kind.signedFrameMap D E w) ∨
    ∃ a' ∈ adicPointsQ D E, ⇑g = translateBy D E a'}
def AdicIsometriesEqClosure : Prop :=
  Kind.adicIsometriesQ D E =
    (fun g : Equiv.Perm (E.Pt D) => (⇑g : E.Pt D → E.Pt D)) ''
      (Subgroup.closure (generators D E) : Set (Equiv.Perm (E.Pt D)))
def PushFnLinear : Prop :=
  ∀ r : E.Pt D ≃ E.Pt D, ⇑r ∈ Kind.adicIsometriesQ D E →
    IsLinearMap ℝ (Kind.pushFn D E r : (E.Pt D → ℝ) → E.Pt D → ℝ)
def PushFnTrans : Prop :=
  ∀ r r' : E.Pt D ≃ E.Pt D, ⇑r ∈ Kind.adicIsometriesQ D E →
    ⇑r' ∈ Kind.adicIsometriesQ D E → ∀ f : E.Pt D → ℝ,
      Kind.pushFn D E (r'.trans r) f =
        Kind.pushFn D E r (Kind.pushFn D E r' f)
def PushFnOfFrameMap : Prop :=
  ∀ (w : SignedFrame) (r : E.Pt D ≃ E.Pt D), ⇑r = Kind.signedFrameMap D E w →
    ∀ f : E.Pt D → ℝ, Kind.pushFn D E r f = frameActFn D E w f
def PushFnOfTranslate : Prop :=
  ∀ a' ∈ adicPointsQ D E, ∀ r : E.Pt D ≃ E.Pt D, ⇑r = translateBy D E a' →
    ∀ f : E.Pt D → ℝ, Kind.pushFn D E r f = Kind.shiftFn D E a' f
def SupportPushFn : Prop :=
  ∀ r : E.Pt D ≃ E.Pt D, ⇑r ∈ Kind.adicIsometriesQ D E → ∀ f : E.Pt D → ℝ,
    Kind.supportQ D E (Kind.pushFn D E r f) = imageSet (⇑r) (Kind.supportQ D E f)
def PushFnPreservesC1CompactSupport : Prop :=
  ∀ r : E.Pt D ≃ E.Pt D, ⇑r ∈ Kind.adicIsometriesQ D E → ∀ f : E.Pt D → ℝ,
    Kind.IsC1Fn D E f → Kind.IsCompactQ D E (Kind.supportQ D E f) →
      Kind.IsC1Fn D E (Kind.pushFn D E r f) ∧
        Kind.IsCompactQ D E (Kind.supportQ D E (Kind.pushFn D E r f))
def SupportStockInvariant : Prop :=
  ∀ r ∈ Kind.adicIsometriesQ D E, ∀ Q ∈ Kind.supportStock D E,
    imageSet r Q ∈ Kind.supportStock D E
def Claim : Prop :=
  ∀ (D : Params) (E : Kind),
    AdicRationalsCountableSubring D ∧
      FrameImageAdicPoints D ∧
      EuclidAdicIsometriesCountableGroup D ∧
      AdicIsometriesCountableHomeomorphGroup D E ∧
      FrameMapsAndShiftsMem D E ∧
      DescendedShiftedFrameMap D E ∧
      AdicInducedMaps.AdicIsoEqFrameAddConst D E ∧
      AdicIsometriesEqClosure D E ∧
      PushFnLinear D E ∧
      PushFnTrans D E ∧
      PushFnOfFrameMap D E ∧
      PushFnOfTranslate D E ∧
      SupportPushFn D E ∧
      PushFnPreservesC1CompactSupport D E ∧
      SupportStockInvariant D E
end YangMills.Construction.PeriodicSpace.AdicIsometryGroup
