import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.LevelCoordinates
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.Lattice.ToriLatticesNormsAndFunctionsOfFinitelyManyVariables
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace TorusMeasure
variable (s : Conventions.StandingParameters)
def proj : (Fin 4 → ℝ) → s.Torus := TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m)
def IsLift (u : s.Torus) (t : Fin 4 → ℝ) : Prop := PeriodicLattice.IsLevelLift s.L s.m s.K s.K u t
def classOf (t : Fin 4 → ℝ) : s.Torus := PeriodicLattice.torusClassOf s.L s.m s.K s.K t
def addVec (u : s.Torus) (t : Fin 4 → ℝ) : s.Torus :=
  PeriodicLattice.shiftBy s.L s.m s.K s.K u t
variable {s}
def pointNorm (u : s.Torus) : ℝ :=
  TorusMetric.torusEuclidNorm (S := PeriodicLattice.torusSide s.L s.m) u
def pointDist (u w : s.Torus) : ℝ :=
  TestFunctions.euclidDistTorus (ℓ := PeriodicLattice.torusSide s.L s.m) u w
def setDist (A A' : Set s.Torus) : ℝ≥0∞ :=
  TorusMetric.setEuclidDist (S := PeriodicLattice.torusSide s.L s.m) A A'
variable (s) in
abbrev euclidTopology : TopologicalSpace s.Torus := PeriodicLattice.metricTopology s.L s.m
def closedWrapBall (x : s.Torus) (r : ℝ) : Set s.Torus := {u | pointNorm (u - x) ≤ r}
def closedWrapBallR4 (x : Fin 4 → ℝ) (r : ℝ) : Set (Fin 4 → ℝ) := TestFunctions.closedBallR4 x r
def IsNullMeasurableR4 (S : Set (Fin 4 → ℝ)) : Prop := NullMeasurableSet S volume
def IsNullMeasurableFunR4 (f : (Fin 4 → ℝ) → ℝ) : Prop := NullMeasurable f volume
def volumeR4 (S : Set (Fin 4 → ℝ)) : ℝ≥0∞ := volume S
def integralR4 (f : (Fin 4 → ℝ) → ℝ) : ℝ := ∫ t, f t
def omega4 : ℝ := Real.pi ^ 2 / 2
def IsMeasurableFun (h : s.Torus → ℝ) : Prop :=
  IsNullMeasurableFunR4 (h ∘ proj s)
def torusIntegral (h : s.Torus → ℝ) : ℝ :=
  ∫ t in Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) (PeriodicLattice.torusSide s.L s.m), h (proj s t)
def IsMeasurableTorusSet (E : Set s.Torus) : Prop :=
  IsNullMeasurableR4 (proj s ⁻¹' E)
theorem isMeasurableTorusSet_iff_indicator (E : Set s.Torus) :
    IsMeasurableTorusSet E ↔ IsMeasurableFun (E.indicator (1 : s.Torus → ℝ)) := by
  have hcomp : (E.indicator (1 : s.Torus → ℝ)) ∘ proj s =
      (proj s ⁻¹' E).indicator fun _ => (1 : ℝ) := by
    funext t
    by_cases ht : proj s t ∈ E <;> simp [Set.indicator, ht]
  unfold IsMeasurableTorusSet IsMeasurableFun IsNullMeasurableR4
    IsNullMeasurableFunR4
  rw [hcomp]
  constructor
  · intro hE B _
    classical
    rw [Set.indicator_const_preimage_eq_union]
    refine NullMeasurableSet.union ?_ ?_
    · split_ifs
      · exact hE
      · exact MeasurableSet.empty.nullMeasurableSet
    · split_ifs
      · exact hE.compl
      · exact MeasurableSet.empty.nullMeasurableSet
  · intro hf
    have hpre : ((proj s ⁻¹' E).indicator fun _ => (1 : ℝ)) ⁻¹' {1} = proj s ⁻¹' E := by
      ext t
      by_cases ht : proj s t ∈ E <;> simp [Set.indicator, ht]
    rw [← hpre]
    exact hf (measurableSet_singleton 1)
def torusVolume (E : Set s.Torus) : ℝ := torusIntegral (E.indicator (1 : s.Torus → ℝ))
def setTorusIntegral (E : Set s.Torus) (h : s.Torus → ℝ) : ℝ :=
  torusIntegral fun u => E.indicator (1 : s.Torus → ℝ) u * h u
end TorusMeasure
end YangMills.Construction
