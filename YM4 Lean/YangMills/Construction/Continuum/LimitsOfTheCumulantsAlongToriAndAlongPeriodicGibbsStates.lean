import YangMills.Construction.GrowingTori.DefinitionsForSequencesOfGrowingTori
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.InfiniteLattice.TorusFunctionalsAndTuplesReadOnATorus
import YangMills.Construction.Torus.CentredFunctionalOfAFamilyOfMaps
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory YangMills.Construction.AmbientPoints
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped Topology
noncomputable section
namespace YangMills.Construction.CumulantLimits
structure ToralSequence (D : GrowingTori.GrowthParameters) (g : ℝ) where
  passage : ℕ+ → GrowingTori.FirstPassagePoint D g
  sideExponent : ℕ+ → ℕ+
  tendsto_side : Tendsto (fun j => PeriodicLattice.torusSide D.L (sideExponent j)) atTop atTop
structure PeriodicGibbsSequence (D : GrowingTori.GrowthParameters) (g : ℝ) where
  passage : ℕ+ → GrowingTori.FirstPassagePoint D g
  measure : ∀ j, Measure (InfiniteLattice.GaugeField
    (PeriodicLattice.meshSize D.L (((passage j).K : ℕ) : ℤ)))
  measure_mem : ∀ j, measure j ∈ InfiniteLattice.periodicGibbsSet D.L (passage j).K (passage j).β
variable {D : GrowingTori.GrowthParameters} {g : ℝ} {s : Conventions.StandingParameters}
abbrev ToralSequence.side (Q : ToralSequence D g) (j : ℕ+) : ℝ :=
  PeriodicLattice.torusSide D.L (Q.sideExponent j)
def ToralSequence.cumulant (Q : ToralSequence D g) (j : ℕ+) {n : ℕ}
    (f : Fin n → Pt s .euclidean → ℝ) : ℂ :=
  TorusCumulants.cumulantOfFamily D.L (Q.sideExponent j) (Q.passage j).K (Q.passage j).β f
def PeriodicGibbsSequence.cumulant (Q : PeriodicGibbsSequence D g)
    (j : ℕ+) {n : ℕ} (f : Fin n → Pt s .euclidean → ℝ) : ℂ :=
  InfiniteLattice.smearedEnergyCumulant (Q.measure j) f
def ToralSequence.Defines (Q : ToralSequence D g)
    (S : TupleMapFamily s .euclidean) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (f : separatedTuples s .euclidean n),
    Tendsto (fun j => Q.cumulant j f.1) atTop (𝓝 (S n hn f : ℂ))
def PeriodicGibbsSequence.Defines (Q : PeriodicGibbsSequence D g)
    (S : TupleMapFamily s .euclidean) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (f : separatedTuples s .euclidean n),
    Tendsto (fun j => Q.cumulant j f.1) atTop (𝓝 (S n hn f : ℂ))
variable (D g)
abbrev moments (S : TupleMapFamily s .euclidean) : allSeparatedTuples s .euclidean → ℝ :=
  centredOfMaps S
end YangMills.Construction.CumulantLimits
end
