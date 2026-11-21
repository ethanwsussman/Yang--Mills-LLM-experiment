import YangMills.Construction.ReflectionPositivity.InequalityOnTuplesAtALinkMirror
import YangMills.Construction.ReflectionPositivity.SequencesOfLatticeDataAndTheirLimits
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
namespace CoordMirror
def timeAt (c : ℝ) : CoordMirror := ⟨3, c⟩
end CoordMirror
namespace Ambient
abbrev upperHalf (D : MirrorData) : Set (euclidean.Point D) :=
  (CoordMirror.timeAt 0).upperSide D euclidean
namespace LatticeDataSeq
variable {D : MirrorData} (S : LatticeDataSeq D euclidean)
def timeData (j : ℕ+) : CutoffMirrors.MirrorData :=
  ⟨S.standingAt j, S.β j, S.β_pos j, 3⟩
def linkHeight (j : ℕ+) : ℝ := PeriodicLattice.meshSize D.L (S.K j : ℕ) / 2
def linkLevel (j : ℕ+) : CutoffMirrors.LinkLevel (S.timeData j) :=
  ⟨S.linkHeight j, 0, by
    have e : (S.timeData j).spacing = PeriodicLattice.meshSize D.L (S.K j : ℕ) := rfl
    rw [e, linkHeight]
    push_cast
    ring⟩
def centredProduct (j : ℕ+) (X : FnList D euclidean) :
    (S.timeData j).FieldSpace → ℂ :=
  fun U => CutoffMirrors.MirrorData.FunTuple.prodOver (D := S.timeData j) (S.listAt j X)
    fun f => (((S.timeData j).centredObservable f U.1 : ℝ) : ℂ)
variable {r : ℕ}
def latticeFn (c : Fin r → ℂ) (X : Fin r → separatedWithin D euclidean (upperHalf D))
    (j : ℕ+) : (S.timeData j).FieldSpace → ℂ :=
  CutoffMirrors.TupleInequality.tupleCombination (D := S.timeData j)
    (fun i => S.listAt j (X i).1) c
theorem latticeFn_apply (c : Fin r → ℂ)
    (X : Fin r → separatedWithin D euclidean (upperHalf D)) (j : ℕ+)
    (U : (S.timeData j).FieldSpace) :
    S.latticeFn c X j U = ∑ i, c i * S.centredProduct j (X i).1 U :=
  rfl
end LatticeDataSeq
end Ambient
end YangMills.Construction.ReflectionPositivity.AxisMirror
end
