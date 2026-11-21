import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Lattice.SourcesWithoutConstantPart
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
structure ChessboardSetup extends Conventions.StandingParameters where
  β : ℝ
  beta_pos : 0 < β
namespace ChessboardSetup
variable (D : ChessboardSetup)
def mesh : ℝ := PeriodicLattice.meshSize D.L (D.K : ℕ)
def sideSet : Set ℝ := PeriodicLattice.torusSides D.L
def withExponent (n : ℕ+) : ChessboardSetup := ⟨⟨D.L, D.isAdmissible, D.K, n⟩, D.β, D.beta_pos⟩
abbrev gridPoints : AddSubgroup AmbientSpace := InfiniteLattice.latticeSubgroup D.mesh
abbrev GaugeField : Type := InfiniteLattice.GaugeField D.mesh
abbrev Link : Type := InfiniteLattice.Link D.mesh
abbrev Plaquette : Type := InfiniteLattice.ElementaryPlaquette D.mesh
abbrev PeriodicLink : Type := PeriodicLattice.Bond D.L D.m ((D.K : ℕ) : ℤ)
def HasBoundedSupport (v : AmbientSpace → ℂ) : Prop :=
  ∃ S : Set AmbientSpace, Bornology.IsBounded S ∧ ∀ x, x ∉ S → v x = 0
def smeared (v : AmbientSpace → ℂ) (U : D.GaugeField) : ℂ :=
  InfiniteLattice.smearedEnergy v U
def proj : AmbientSpace → D.Torus := TorusMetric.torusProj (PeriodicLattice.torusSide D.L D.m)
def projLink (b : D.Link) : D.PeriodicLink := InfiniteLattice.projectLink D.L D.m ((D.K : ℕ) : ℤ) b
def liftField (U : D.PeriodicLink → Matrices.ComplexMatrix2) : D.GaugeField :=
  InfiniteLattice.liftField D.L D.m ((D.K : ℕ) : ℤ) U
def liftedMeasure : Measure D.GaugeField :=
  InfiniteLattice.liftedWilsonMeasure D.L D.m D.K D.β
def liftedExpectation (F : D.GaugeField → ℂ) : ℂ := ∫ U, F U ∂D.liftedMeasure
def partitionFunction (w : D.Torus → ℂ) : ℂ :=
  PeriodicLattice.generatingFunctionOfSource D.L D.m D.K D.β w
def descend (W : AmbientSpace → ℂ) : D.Torus → ℂ :=
  fun u => W (TestFunctions.liftPoint (ℓ := PeriodicLattice.torusSide D.L D.m) u)
theorem descend_comp_proj {W : AmbientSpace → ℂ}
    (hW : ∀ (x : AmbientSpace) (k : Fin 4 → ℤ),
      W (x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k) = W x) :
    D.descend W ∘ D.proj = W := by
  funext x
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq
    (TestFunctions.torusProj_liftPoint (ℓ := PeriodicLattice.torusSide D.L D.m) (D.proj x))
  change W (TestFunctions.liftPoint (ℓ := PeriodicLattice.torusSide D.L D.m) (D.proj x)) = W x
  rw [hk, hW]
def partitionFunctionOfPeriodic (W : AmbientSpace → ℂ) : ℂ := D.partitionFunction (D.descend W)
end ChessboardSetup
end ChessboardTori
end YangMills.Construction
end
