import YangMills.Construction.InfiniteLattice.LatticeAtOneSpacingWithItsTorusAndCovering
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
noncomputable section
namespace YangMills.Construction.FixedSpacing.Setup
variable (D : Setup)
def lift (U : D.TorusFields) : D.Fields :=
  InfiniteLattice.liftCompactField U
theorem lift_apply (U : D.TorusFields) (b : InfiniteLattice.Link D.mesh) :
    D.lift U b = U.linkValue (D.projLink b) :=
  InfiniteLattice.liftCompactField_apply U b
def liftedGibbs : Measure D.Fields := D.gibbs.map D.lift
def withExponent (m' : ℕ+) : Setup := { D with m := m' }
def torusLimits : Set (Measure D.Fields) :=
  {ν | ∃ (n : ℕ → ℕ+) (ρ : ℕ → GibbsAtFixedSpacing.BorelProb D.mesh)
      (ρ' : GibbsAtFixedSpacing.BorelProb D.mesh),
    Tendsto (fun i => (D.withExponent (n i)).side) atTop atTop ∧
    (∀ i, (ρ i).1 = (D.withExponent (n i)).liftedGibbs) ∧ ρ'.1 = ν ∧
    GibbsAtFixedSpacing.BorelProb.TendstoWeak ρ ρ'}
def periodicGibbsSet : Set (Measure D.Fields) := {ν | InfiniteLattice.IsPeriodicGibbs D.β ν}
def periodization (f : InfiniteLattice.AmbientSpace → ℝ) : D.Torus → ℝ :=
  TestFunctions.periodize D.side f
theorem periodization_proj (f : InfiniteLattice.AmbientSpace → ℝ) (x : InfiniteLattice.AmbientSpace) :
    D.periodization f (D.proj x) =
      ∑' k : Fin 4 → ℤ, f (x + TestFunctions.latticeTranslate D.side k) :=
  TestFunctions.periodize_torusProj D.side f x
def torusConnected {n : ℕ} (f : Fin n → InfiniteLattice.AmbientSpace → ℝ) : ℂ :=
  D.cumulant fun i => D.smeared (D.periodization (f i))
end YangMills.Construction.FixedSpacing.Setup
