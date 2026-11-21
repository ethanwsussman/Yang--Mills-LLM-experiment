import YangMills.Construction.ChessboardTori.CellDatumAndUpperChessboardValue
import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.InfiniteLattice.IsometriesOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.ReflectionFormOfAPeriodicGibbsState
import YangMills.Construction.ReflectionsAndOneInsertion.PeriodicGibbsLimitStandingDefs
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
open InfiniteLattice (AmbientSpace IsBoundedObservable IsRegionMeasurable halfSpacingTimes timeAxis
  timeReflect timeReflectAtOrigin localObsAbove)
open ChessboardTori (ReflectionGrid GridCell)
open MirrorGridsAllSides (conjFun transportFun)
noncomputable section
namespace ReflectionsAndOneInsertion
def timeUnitVec : AmbientSpace := ChessboardTori.coordVec timeAxis
def spaceTimePoint (v : Fin 3 → ℝ) (t : ℝ) : AmbientSpace := Fin.snoc (α := fun _ => ℝ) v t
def addHalfStep {a : ℝ} (t : halfSpacingTimes a) {u : ℝ} (hu : ∃ k : ℤ, u = k * a) :
    halfSpacingTimes a :=
  ⟨t + u / 2, by
    obtain ⟨q, hq⟩ := t.2
    obtain ⟨k, rfl⟩ := hu
    exact ⟨q + k, by rw [hq]; push_cast; ring⟩⟩
end ReflectionsAndOneInsertion
namespace ChessboardTori.GridCell
open ReflectionsAndOneInsertion
variable {D : ChessboardSetup} (c : GridCell D)
theorem side_mem_zmultiples : ∃ k : ℤ, c.side = k * D.mesh :=
  ⟨c.grid.cellRatio, c.grid.cellSide_eq⟩
def baseTime : halfSpacingTimes D.mesh :=
  ⟨c.bottomTime, by
    obtain ⟨i, hi⟩ := c.grid.origin_mem timeAxis
    refine ⟨2 * i + 1 + 2 * c.grid.cellRatio * c.index timeAxis, ?_⟩
    simp only [bottomTime, centre, side, ReflectionGrid.cellCentre, hi, c.grid.cellSide_eq]
    push_cast
    ring⟩
def midTime : halfSpacingTimes D.mesh := addHalfStep c.baseTime c.side_mem_zmultiples
def timeStep (i : ℤ) : InfiniteLattice.LatticePoint D.mesh :=
  ⟨((i : ℝ) * c.side) • timeUnitVec, Pi.single timeAxis (i * c.grid.cellRatio), fun μ => by
    by_cases h : μ = timeAxis
    · subst h
      simp [timeUnitVec, ChessboardTori.coordVec, side, c.grid.cellSide_eq]
      ring
    · simp [timeUnitVec, ChessboardTori.coordVec, Pi.single_eq_of_ne h]⟩
def timeShift (i : ℤ) : D.LatticeSym := InfiniteLattice.shift (c.timeStep i)
def shiftedCell (i : ℤ) : Set AmbientSpace := (c.timeShift i).setImage c.cell
end ChessboardTori.GridCell
namespace ReflectionsAndOneInsertion
def ReflectShiftRelations (D : InsertionData) : Prop :=
  ∀ (t : halfSpacingTimes D.mesh) (u : ℝ) (hu : ∃ k : ℤ, u = k * D.mesh) (v : Fin 3 → ℝ) (s : ℝ),
    (timeReflect (addHalfStep t hu)).toFun ∘ (timeReflect t).toFun =
        SeparatedTuples.translate (u • timeUnitVec) ∧
      (timeReflect (addHalfStep t hu)).toFun ∘
          SeparatedTuples.translate (u • timeUnitVec) = (timeReflect t).toFun ∧
      (timeReflect t).toFun ∘ SeparatedTuples.translate (spaceTimePoint v t) =
        SeparatedTuples.translate (spaceTimePoint v t) ∘
          (timeReflectAtOrigin D.mesh).toFun ∧
      SeparatedTuples.translate ((-s) • timeUnitVec) ∘ (timeReflectAtOrigin D.mesh).toFun =
        (timeReflectAtOrigin D.mesh).toFun ∘ SeparatedTuples.translate (s • timeUnitVec)
def ObservableActionLaws (D : InsertionData) : Prop :=
  ∀ (r r' : D.LatticeSym) (A B : D.GaugeField → ℂ), IsBoundedObservable A → IsBoundedObservable B →
    (r.comp r').actOn A = r.actOn (r'.actOn A) ∧
      r.actOn (A * B) = r.actOn A * r.actOn B ∧
      r.actOn (conjFun A) = conjFun (r.actOn A) ∧
      InfiniteLattice.observableSupNorm (r.actOn A) = InfiniteLattice.observableSupNorm A ∧
      ∀ S : Set AmbientSpace, IsRegionMeasurable S A → IsRegionMeasurable (r.setImage S) (r.actOn A)
def FunctionAndSpanActionLaws : Prop :=
  ∀ r r' : Equiv.Perm AmbientSpace, SeparatedTuples.IsEuclidIsometry r →
    SeparatedTuples.IsEuclidIsometry r' →
    (∀ (𝕜 : Type) [RCLike 𝕜] (f : AmbientSpace → 𝕜),
      TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f → HasCompactSupport f →
        transportFun (r * r') f = transportFun r (transportFun r' f) ∧
        ReflectionPositivity.CutoffMirrors.euclidSupp (transportFun r f) =
          r '' ReflectionPositivity.CutoffMirrors.euclidSupp f ∧
        ∀ M : ℝ, 1 ≤ M →
          TestFunctions.sharpNormR4 M (transportFun r f) = TestFunctions.sharpNormR4 M f) ∧
    ∀ Ξ Ξ' : SeparatedTuples.FormalSpan, R4TupleForms.FormalMulDefined Ξ Ξ' →
      SeparatedTuples.pushSpan (⇑(r * r')) Ξ =
        SeparatedTuples.pushSpan r (SeparatedTuples.pushSpan r' Ξ) ∧
      R4TupleForms.FormalMulDefined (SeparatedTuples.pushSpan r Ξ)
        (SeparatedTuples.pushSpan r Ξ') ∧
      SeparatedTuples.pushSpan r (SeparatedTuples.formalMul Ξ Ξ') =
        SeparatedTuples.formalMul (SeparatedTuples.pushSpan r Ξ)
          (SeparatedTuples.pushSpan r Ξ') ∧
      SeparatedTuples.conjugation (SeparatedTuples.pushSpan r Ξ) =
        SeparatedTuples.pushSpan r (SeparatedTuples.conjugation Ξ)
def ObservableLocality (D : InsertionData) : Prop :=
  (∀ (S : Set AmbientSpace) (A : D.GaugeField → ℂ), IsBoundedObservable A →
    (IsRegionMeasurable S A ↔
      ∃ A' ∈ InfiniteLattice.boundedBorelSpace
          (InfiniteLattice.LinkVariables (InfiniteLattice.positiveLinksWithin D.mesh S)),
        ∀ U, A U = A' (InfiniteLattice.restrictField U
          (InfiniteLattice.positiveLinksWithin D.mesh S)))) ∧
  (∀ (S₁ S₂ : Set AmbientSpace) (A : D.GaugeField → ℂ), IsBoundedObservable A →
    IsRegionMeasurable S₁ A → IsRegionMeasurable S₂ A → IsRegionMeasurable (S₁ ∩ S₂) A) ∧
  (∀ t : halfSpacingTimes D.mesh, localObsAbove t =
    {A | ∃ B' : Finset D.Link,
      (B' : Set D.Link) ⊆ InfiniteLattice.linksWithin (InfiniteLattice.abovePlane t) ∧
      MirrorGridsAllSides.GridSetup.IsBoundedMeasurableInLinks D B' A}) ∧
  ∀ (g : ReflectionGrid D), g.HasAdmissibleSide → ∀ S ∈ g.cellSet,
    ReflectionGrid.cellObservables (D := D) S =
      {A | IsBoundedObservable A ∧ IsRegionMeasurable (interior S) A}
def IsShiftOrTimeReflect {D : InsertionData} (r : D.LatticeSym) : Prop :=
  (∃ v : InfiniteLattice.LatticePoint D.mesh, r = InfiniteLattice.shift v) ∨
    ∃ s : halfSpacingTimes D.mesh, r = timeReflect s
def ShiftsAndReflectsDescend (D : InsertionData) : Prop :=
  ∀ r : D.LatticeSym, IsShiftOrTimeReflect r →
    (∃! r' : D.Torus → D.Torus, MirrorGridsAllSides.GridSetup.Descends D r.toFun r') ∧
    ∃ s : MirrorGridsAllSides.GridSetup.TorusSymmetry D,
      MirrorGridsAllSides.GridSetup.Descends D r.toFun s.toFun ∧
      ∀ A : D.GaugeField → ℂ, IsBoundedObservable A →
        ∀ U ∈ MirrorGridsAllSides.GridSetup.torusFields D,
          D.liftedObservable (r.actOn A) U =
            MirrorGridsAllSides.GridSetup.TorusSymmetry.precompose s (D.liftedObservable A) U
def CellArithmetic {D : InsertionData} (c : GridCell D) : Prop :=
  (∃ k : ℤ, c.side = k * D.mesh) ∧
  c.centre timeAxis = c.bottomTime + c.side / 2 ∧
  (∃ k : ℤ, c.centre timeAxis = k * D.mesh) ∧
  (∃ k : ℤ, c.bottomTime = D.mesh * ((k : ℝ) + 1 / 2)) ∧
  (∃ s : D.LatticeSym, s.toFun = SeparatedTuples.translate (c.side • timeUnitVec)) ∧
  (∃ s : D.LatticeSym, s.toFun =
    fun x => x - (2 * (x timeAxis - c.bottomTime)) • timeUnitVec) ∧
  ∃ s : D.LatticeSym, s.toFun =
    fun x => x - (2 * (x timeAxis - (c.bottomTime + c.side / 2))) • timeUnitVec
def CellAndWalls {D : InsertionData} (c : GridCell D) : Prop :=
  c.cell = {x | ∀ μ, x μ - c.centre μ ∈ Icc (-(c.side / 2)) (c.side / 2)} ∧
  c.cell ⊆ {x | c.bottomTime ≤ x timeAxis ∧ x timeAxis ≤ c.bottomTime + c.side} ∧
  c.grid.wallSet =
    range (fun p : Fin 4 × ℤ => {x : AmbientSpace | x p.1 = c.centre p.1 + ((p.2 : ℝ) + 1 / 2) * c.side}) ∧
  {x : AmbientSpace | x timeAxis = c.bottomTime} ∈ c.grid.wallSet
def CellObservableAlgebras {D : InsertionData} (c : GridCell D) : Prop :=
  (∀ i : ℤ, c.shiftedCell i ∈ c.grid.cellSet) ∧
  ∀ (F : D.GaugeField → ℂ) (hF : F ∈ ReflectionGrid.cellObservables (D := D) c.cell),
    F ∈ localObsAbove c.baseTime ∧
    (∀ A ∈ localObsAbove c.baseTime,
      F * (c.timeShift 1).actOn A ∈ localObsAbove c.baseTime) ∧
    conjFun ((timeReflect c.midTime).actOn F) ∈
      ReflectionGrid.cellObservables (D := D) c.cell ∧
    (∀ i : ℤ, (c.timeShift i).actOn F ∈
      ReflectionGrid.cellObservables (D := D) (c.shiftedCell i)) ∧
    ∀ (m : ℕ+ → ℕ+) (hm : c.IsAdmissibleSideSequence m),
      0 ≤ c.limsupChessboardNorm m hm F hF ∧
        c.limsupChessboardNorm m hm F hF ≤ InfiniteLattice.observableSupNorm F
def ReflectionsObservablesCells.Statement : Prop :=
  ∀ D : InsertionData,
    ReflectShiftRelations D ∧
    ObservableActionLaws D ∧
    FunctionAndSpanActionLaws ∧
    ObservableLocality D ∧
    ShiftsAndReflectsDescend D ∧
    ∀ c : GridCell D,
      CellArithmetic c ∧ CellAndWalls c ∧ CellObservableAlgebras c
end ReflectionsAndOneInsertion
end
end YangMills.Construction
