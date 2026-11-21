import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import YangMills.Construction.Continuum.OpenHalvesAndFlatnessOutsideAnOpenSet
import YangMills.Construction.Continuum.TranslationsAsMotionsAndSmoothSeparatedTuples
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedTupleForms
open InfiniteLattice (AmbientSpace)
def componentList {n : ℕ} (f : Fin n → AmbientSpace → ℝ) : List SeparatedTuples.RealValued :=
  List.ofFn f
def componentLists (T : Set SeparatedTuples.SepTuple) : Set (List SeparatedTuples.RealValued) :=
  Subtype.val '' T
def sepTupleComponents (Y : TestSpaces.SepTuple) : List SeparatedTuples.RealValued := componentList Y.2.1
def IsometriesEqMotions : Prop :=
  ∀ r : AmbientSpace → AmbientSpace,
    Tower.FullSpace.IsDistancePreserving r ↔ Motions.IsRigidMotion r
def MotionsClosedUnderComp : Prop :=
  ∀ r s : AmbientSpace → AmbientSpace, Motions.IsRigidMotion r → Motions.IsRigidMotion s →
    Motions.IsRigidMotion (r ∘ s)
def MotionsClosedUnderInv : Prop :=
  ∀ r : Motions.RigidMotion, Motions.IsRigidMotion r.invFun
def UpperHalfSpacesEq : Prop := TimeAxis.upperHalfSpace = TestSpaces.upperHalfSpace
def TimeReflectionsEq : Prop := TimeAxis.timeReflection = TestSpaces.timeReflect
def SizedTuplesEq (O : Set AmbientSpace) (n : ℕ) : Prop :=
  componentLists {X | X ∈ SeparatedTuples.supportedIn O ∧ X.size = n} =
    componentList '' TestSpaces.disjointSupportTuples O n
def SupportedTuplesEqUnion (O : Set AmbientSpace) : Prop :=
  componentLists (SeparatedTuples.supportedIn O) =
    ⋃ n : ℕ, componentList '' TestSpaces.disjointSupportTuples O n
def WholeSpaceTuplesEq : Prop :=
  Function.Injective sepTupleComponents ∧
    Set.range sepTupleComponents =
      componentLists (SeparatedTuples.supportedIn (Set.univ : Set AmbientSpace))
def SmoothTuplesEq (O : Set AmbientSpace) (n : ℕ) : Prop :=
  componentLists (SmoothSeparatedTuples.smoothSupportedInOfSize O n) =
    componentList '' {f | f ∈ TestSpaces.disjointSupportTuples O n ∧
      TestSpaces.HasSmoothComponents O f}
def DisjointSupportTuplesMono (O O' : Set AmbientSpace) (n : ℕ) : Prop :=
  O ⊆ O' → TestSpaces.disjointSupportTuples O n ⊆ TestSpaces.disjointSupportTuples O' n
def MotionPreservesTuples (O : Set AmbientSpace) {n : ℕ} (X : Fin n → AmbientSpace → ℝ)
    (r : Motions.RigidMotion) : Prop :=
  IsOpen (r.toFun '' O) ∧
    Motions.actOnTuple r X ∈ TestSpaces.disjointSupportTuples (r.toFun '' O) n ∧
    (TestSpaces.HasSmoothComponents O X →
      TestSpaces.HasSmoothComponents (r.toFun '' O) (Motions.actOnTuple r X))
def TsupportOfMovedComponent {n : ℕ} (X : Fin n → AmbientSpace → ℝ) (r : Motions.RigidMotion) :
    Prop :=
  ∀ i, tsupport (Motions.actOnPointFun r (X i)) = r.toFun '' tsupport (X i)
def MotionActionsEq {n : ℕ} (X : Fin n → AmbientSpace → ℝ) (r : Motions.RigidMotion) : Prop :=
  ∀ Z : SeparatedTuples.SepTuple, Z.1 = componentList X →
    (SeparatedTuples.push r.toFun Z).1 = componentList (Motions.actOnTuple r X)
def TranslationActionsEq {n : ℕ} (X : Fin n → AmbientSpace → ℝ) (v : AmbientSpace) : Prop :=
  ∀ Z : SeparatedTuples.SepTuple, Z.1 = componentList X →
    (SeparatedTuples.push (SeparatedTuples.translate v) Z).1 =
      componentList (SmoothSeparatedTuples.translateFamily v X)
def JuxtEqConcat {q q' : ℕ} (X : TestSpaces.SepTupleOfCard q)
    (Y : TestSpaces.SepTupleOfCard q') : Prop :=
  ∀ Z W : SeparatedTuples.SepTuple, Z.1 = componentList X.1 → W.1 = componentList Y.1 →
    (SeparatedTuples.SepTuple.Composable Z W ↔
        Motions.concatTuple X.1 Y.1 ∈ TestSpaces.disjointSupportTuples Set.univ (q + q')) ∧
      (SeparatedTuples.SepTuple.Composable Z W →
        (SeparatedTuples.SepTuple.juxt Z W).1 = componentList (Motions.concatTuple X.1 Y.1))
def TwoFormsAgree : Prop :=
  IsometriesEqMotions ∧ MotionsClosedUnderComp ∧ MotionsClosedUnderInv ∧
    UpperHalfSpacesEq ∧ TimeReflectionsEq ∧
    (∀ O : Set AmbientSpace, IsOpen O →
      SupportedTuplesEqUnion O ∧
        ∀ n : ℕ, SizedTuplesEq O n ∧ SmoothTuplesEq O n ∧
          (∀ O' : Set AmbientSpace, IsOpen O' → DisjointSupportTuplesMono O O' n) ∧
          ∀ X ∈ TestSpaces.disjointSupportTuples O n,
            (∀ r : Motions.RigidMotion,
              MotionPreservesTuples O X r ∧ TsupportOfMovedComponent X r ∧ MotionActionsEq X r) ∧
              ∀ v : AmbientSpace, TranslationActionsEq X v) ∧
    WholeSpaceTuplesEq ∧
    ∀ (q q' : ℕ) (X : TestSpaces.SepTupleOfCard q) (Y : TestSpaces.SepTupleOfCard q'),
      JuxtEqConcat X Y
end YangMills.Construction.SeparatedTupleForms
end
