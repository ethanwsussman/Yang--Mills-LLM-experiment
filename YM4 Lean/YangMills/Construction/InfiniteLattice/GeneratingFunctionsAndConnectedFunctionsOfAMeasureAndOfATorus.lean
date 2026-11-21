import YangMills.Construction.InfiniteLattice.PlaquettesAndTheDensityAtACutoff
import YangMills.Construction.InfiniteLattice.SmearedDensityAndConnectedFunctionsOfAMeasure
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace Cumulants
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
def expectationC (η : Measure Ω) (Y : Ω → ℂ) : ℂ := ∫ ω, Y ω ∂η
def laplaceTransform (η : Measure Ω) (X : Fin n → Ω → ℝ) (z : Fin n → ℂ) : ℂ :=
  expectationC η fun ω => Complex.exp (∑ j, z j * (X j ω : ℂ))
def principalLog (w : ℂ) : ℂ := Complex.log w
theorem mixedCumulant_eq_iteratedFDeriv (η : Measure Ω) (X : Fin n → Ω → ℝ) :
    mixedCumulant η X =
      iteratedFDeriv ℂ n (fun z => principalLog (laplaceTransform η X z)) 0
        fun i => Pi.single i 1 := rfl
end Cumulants
namespace PeriodicLattice
variable {n : ℕ}
structure IsBoundedFamily {L m : ℕ} (h : Fin n → FourTorus L m → ℝ) : Prop where
  one_le_card : 1 ≤ n
  bounded_apply : ∀ j, TestFunctions.IsBoundedFun (h j)
def torusUrsellFunction (L m K : ℕ) (β : ℝ) (h : Fin n → FourTorus L m → ℝ) : ℂ :=
  gibbsCumulant L m K β fun j U => smearedObservable (h j) U
end PeriodicLattice
namespace InfiniteLattice
open YangMills.Construction.TestFunctions
variable {n : ℕ}
def cutoffSmearedEnergyRe {L K : ℕ} (f : AmbientSpace → ℝ) (U : RefinedGaugeField L K) : ℝ :=
  (cutoffSmearedEnergy (fun x => (f x : ℂ)) U).re
theorem cutoffSmearedEnergyRe_eq_smearedEnergy {L K : ℕ} (f : AmbientSpace → ℝ)
    (U : RefinedGaugeField L K) : cutoffSmearedEnergyRe f U = smearedEnergy f U := by
  unfold cutoffSmearedEnergyRe cutoffSmearedEnergy
  rw [← plaquetteSmearing_eq_smearedEnergy_of_support, plaquetteSmearing_ofReal,
    Complex.ofReal_re]
theorem ofReal_cutoffSmearedEnergyRe {L K : ℕ} (f : AmbientSpace → ℝ) (U : RefinedGaugeField L K) :
    ((cutoffSmearedEnergyRe f U : ℝ) : ℂ) = cutoffSmearedEnergy (fun x => (f x : ℂ)) U := by
  rw [cutoffSmearedEnergyRe_eq_smearedEnergy]
  unfold cutoffSmearedEnergy
  rw [← plaquetteSmearing_eq_smearedEnergy_of_support, plaquetteSmearing_ofReal]
def ursellFunctionOfFamily {L K : ℕ} (η : Measure (RefinedGaugeField L K))
    (f : Fin n → AmbientSpace → ℝ) : ℂ :=
  Cumulants.mixedCumulant η fun j U => cutoffSmearedEnergyRe (f j) U
end InfiniteLattice
end YangMills.Construction
end
