import YangMills.Construction.ChessboardTori.GridElementaryProperties
import YangMills.Construction.ChessboardTori.NamesOfAMirrorGridOnATorus
import YangMills.Construction.Torus.LiftsAndInducedMaps
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def ChessboardSetup.periodVectors (D : ChessboardSetup) : Set AmbientSpace :=
  range (TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m))
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def descendToTorus (f : AmbientSpace → AmbientSpace) : D.Torus → D.Torus :=
  TorusLifts.descendedMap (PeriodicLattice.torusSide D.L D.m) (PeriodicLattice.torusSide D.L D.m) f
def CellCarrierForm : Prop :=
  ∀ (a b : Fin 4 → ℤ), ∀ r ∈ g.reflectionGroup, r '' g.cell a = g.cell b →
    (∀ i,
      (Even (b i - a i) →
        g.ActsOnCoord r i (g.coordShift ((b i - a i) / 2))) ∧
      (Odd (b i - a i) →
        g.ActsOnCoord r i (g.coordReflect ((a i + b i + 1) / 2)))) ∧
    orientationSign r = (∑ i, (b i - a i)).negOnePow
def SameTorusImageCriterion : Prop :=
  ∀ a b : Fin 4 → ℤ,
    (D.proj '' g.cell a = D.proj '' g.cell b ↔
      ∃ j : Fin 4 → ℤ, ∀ i, ((b i - a i : ℤ) : ℝ) = g.cellsAcross * (j i : ℝ)) ∧
    (D.proj '' g.cell a = D.proj '' g.cell b ↔
      ∃ v ∈ D.periodVectors, g.cell b = translate v '' g.cell a) ∧
    (D.proj '' g.cell a = D.proj '' g.cell b →
      D.proj '' interior (g.cell b) = D.proj '' interior (g.cell a))
def BlockCellsRepresent (B : Set AmbientSpace) : Prop :=
  (∀ S ∈ g.cellSet, ∃! p : Set AmbientSpace × AmbientSpace,
    p.1 ∈ g.cellsWithin B ∧ p.2 ∈ D.periodVectors ∧ S = translate p.2 '' p.1) ∧
  BijOn (fun S => D.proj '' S) (g.cellsWithin B) g.torusCellSet
def elementsIntoBlock (B S : Set AmbientSpace) : Set (Equiv.Perm AmbientSpace) :=
  {r | r ∈ g.reflectionGroup ∧ r '' S ∈ g.cellsWithin B}
def BlockElementsRepresent (B S : Set AmbientSpace) : Prop :=
  (∀ r ∈ g.reflectionGroup, ∃! p : AmbientSpace × Equiv.Perm AmbientSpace,
    p.1 ∈ D.periodVectors ∧ p.2 ∈ g.elementsIntoBlock B S ∧
      (r : AmbientSpace → AmbientSpace) = translate p.1 ∘ p.2) ∧
  (∀ r ∈ g.reflectionGroup, ∀ v ∈ D.periodVectors, ∀ r₀ ∈ g.elementsIntoBlock B S,
    (r : AmbientSpace → AmbientSpace) = translate v ∘ r₀ →
      orientationSign r = orientationSign r₀ ∧ descendToTorus r = descendToTorus (D := D) r₀) ∧
  BijOn (fun r₀ : Equiv.Perm AmbientSpace => descendToTorus (D := D) r₀)
    (g.elementsIntoBlock B S) g.inducedTorusMaps
def HalfOddCount (B S : Set AmbientSpace) : Prop :=
  ((g.cellsWithin B).ncard : ℝ) = g.cellsAcross ^ 4 ∧
    (({T ∈ g.cellsWithin B | ∃ r ∈ g.reflectionGroup, orientationSign r = -1 ∧ T = r '' S}.ncard : ℕ) : ℝ) =
      g.cellsAcross ^ 4 / 2 ∧
    (g.inducedTorusMaps.ncard : ℝ) = g.cellsAcross ^ 4 ∧
    (({s ∈ g.inducedTorusMaps | g.torusSign s = -1}.ncard : ℕ) : ℝ) = g.cellsAcross ^ 4 / 2
end ReflectionGrid
def CellsBlocksAndSigns.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D),
    g.CellCarrierForm ∧
    (2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
      g.SameTorusImageCriterion ∧
      ∀ B ∈ g.blocks, g.BlockCellsRepresent B ∧
        ∀ S ∈ g.cellSet, g.BlockElementsRepresent B S ∧
          g.HalfOddCount B S)
end YangMills.Construction.ChessboardTori
end
