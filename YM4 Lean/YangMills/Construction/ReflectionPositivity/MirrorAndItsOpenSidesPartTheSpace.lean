import YangMills.Construction.ReflectionPositivity.FunctionsOfClassC1AndSupports
import YangMills.Construction.ReflectionPositivity.ReflectionsHyperplanesMirrorsAndOpenSides
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
namespace CoordMirror
variable (D : MirrorData) (S : CoordMirror)
def IsPartition (E : Ambient) : Prop :=
  S.carrier D E ∪ S.upperSide D E ∪ S.lowerSide D E = univ ∧
    Disjoint (S.carrier D E) (S.upperSide D E) ∧
    Disjoint (S.carrier D E) (S.lowerSide D E) ∧
    Disjoint (S.upperSide D E) (S.lowerSide D E)
def SidesOpenCarrierClosed (E : Ambient) : Prop :=
  MetricNotions.IsOpenWrt (Ambient.metric D E) (S.upperSide D E) ∧
    MetricNotions.IsOpenWrt (Ambient.metric D E) (S.lowerSide D E) ∧
    MetricNotions.IsClosedWrt (Ambient.metric D E) (S.carrier D E) ∧
    MetricNotions.closureWrt (Ambient.metric D E) (S.upperSide D E) =
      S.upperSide D E ∪ S.carrier D E ∧
    MetricNotions.closureWrt (Ambient.metric D E) (S.lowerSide D E) =
      S.lowerSide D E ∪ S.carrier D E
def TorusSideClosures : Prop :=
  MetricNotions.closureWrt (Ambient.metric D .torus) (S.upperSide D .torus) =
      D.projection '' coordSet S.axis
        (fun t => 0 ≤ t - S.height ∧ t - S.height ≤ D.side / 2) ∧
    MetricNotions.closureWrt (Ambient.metric D .torus) (S.lowerSide D .torus) =
      D.projection '' coordSet S.axis
        (fun t => 0 ≤ -(t - S.height) ∧ -(t - S.height) ≤ D.side / 2)
def EuclideanSideClosures : Prop :=
  MetricNotions.closureWrt (Ambient.metric D .euclidean) (S.upperSide D .euclidean) =
      coordSet S.axis (fun t => t - S.height ≥ 0) ∧
    MetricNotions.closureWrt (Ambient.metric D .euclidean) (S.lowerSide D .euclidean) =
      coordSet S.axis (fun t => -(t - S.height) ≥ 0)
def shiftHalfSide : CoordMirror := ⟨S.axis, S.height + D.side / 2⟩
def ShiftHalfSideSameMirror : Prop :=
  (S.shiftHalfSide D).carrier D .torus = S.carrier D .torus ∧
    (S.shiftHalfSide D).reflect D .torus = S.reflect D .torus ∧
    (S.shiftHalfSide D).upperSide D .torus = S.lowerSide D .torus ∧
    (S.shiftHalfSide D).lowerSide D .torus = S.upperSide D .torus
end CoordMirror
def CarrierAndSidesPartition : Prop :=
  ∀ (D : MirrorData) (S : CoordMirror),
    (∀ E : Ambient, S.IsPartition D E ∧ S.SidesOpenCarrierClosed D E) ∧
      S.TorusSideClosures D ∧ S.EuclideanSideClosures D ∧ S.ShiftHalfSideSameMirror D
end YangMills.Construction.ReflectionPositivity.AxisMirror
