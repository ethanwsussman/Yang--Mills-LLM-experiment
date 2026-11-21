import YangMills.Construction.ReflectionPositivity.HeightOverALinkPosition
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.LevelPartition
variable {D : MirrorData}
def RepInIntervalIsCentered (C : LinkLevel D) : Prop :=
  ∀ (y : D.Torus) (r : ℝ), D.IsRep (y D.dir) r →
    r ∈ Ioo (C.pos - D.side / 2) (C.pos + D.side / 2) → r = C.centeredRep y
def parts (C : LinkLevel D) : Fin 4 → Set D.Torus :=
  ![C.openSlab .pos, C.openSlab .neg, D.nearPlane C.pos, D.farPlane C.pos]
def PartsPartition (C : LinkLevel D) : Prop :=
  Pairwise (Function.onFun Disjoint (parts C)) ∧ ⋃ i, parts C i = univ
def PartsAsLevelSets (C : LinkLevel D) : Prop :=
  C.openSlab .pos = C.centeredRepSet (Ioo C.pos (C.pos + D.side / 2)) ∧
    C.openSlab .neg = C.centeredRepSet (Ioo (C.pos - D.side / 2) C.pos) ∧
    D.nearPlane C.pos = C.centeredRepSet {C.pos} ∧
    D.farPlane C.pos = C.centeredRepSet {C.pos - D.side / 2}
def HalfPeriodShift (C : LinkLevel D) : Prop :=
  C.pos + D.side / 2 = C.pos + (D.sitesPerSide : ℝ) * D.spacing ∧
    D.IsLinkLevel (C.pos + D.side / 2) ∧
    D.reflect (C.pos + D.side / 2) = D.reflect C.pos ∧
    D.mirrorSet (C.pos + D.side / 2) = D.mirrorSet C.pos ∧
    D.openSlab (C.pos + D.side / 2) .pos = D.openSlab C.pos .neg ∧
    D.openSlab (C.pos + D.side / 2) .neg = D.openSlab C.pos .pos
def Claim : Prop :=
  ∀ (D : MirrorData) (C : LinkLevel D),
    (RepInIntervalIsCentered C ∧ PartsPartition C ∧ PartsAsLevelSets C) ∧ HalfPeriodShift C
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.LevelPartition
end
