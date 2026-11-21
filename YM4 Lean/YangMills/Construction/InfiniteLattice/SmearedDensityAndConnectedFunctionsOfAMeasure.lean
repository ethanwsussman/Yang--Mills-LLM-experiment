import YangMills.Construction.InfiniteLattice.ConnectedCorrelations
import YangMills.Construction.InfiniteLattice.RefinedLattices
import YangMills.Construction.InfiniteLattice.SidesOfAPlaquetteAndTheDensityOfBoundedSupport
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def plaquetteSmearing {a : ℝ} (f : AmbientSpace → ℂ) (U : GaugeField a) : ℂ :=
  ∑ᶠ p : ElementaryPlaquette a, f p.center * (faceEnergy U p : ℂ)
theorem plaquetteSmearing_eq_smearedEnergy_of_support {a : ℝ} (f : AmbientSpace → ℂ)
    (U : GaugeField a) : plaquetteSmearing f U = boundedSupportObservable f U := by
  unfold plaquetteSmearing boundedSupportObservable
  refine finsum_congr fun p => ?_
  by_cases hzero : f p.center = 0 <;> simp [hzero]
theorem plaquetteSmearing_eq_smearedEnergy {a : ℝ} (f : AmbientSpace → ℂ) (U : GaugeField a) :
    plaquetteSmearing f U = smearedEnergy f U := by
  unfold plaquetteSmearing smearedEnergy
  refine finsum_congr fun p => ?_
  rw [Complex.real_smul, mul_comm]
theorem plaquetteSmearing_ofReal {a : ℝ} (f : AmbientSpace → ℝ) (U : GaugeField a) :
    plaquetteSmearing (fun x => (f x : ℂ)) U = ((smearedEnergy f U : ℝ) : ℂ) := by
  have hmap := AddMonoidHom.map_finsum_of_injective Complex.ofRealHom.toAddMonoidHom
    Complex.ofReal_injective fun p : ElementaryPlaquette a => faceEnergy U p • f p.center
  unfold plaquetteSmearing smearedEnergy
  refine Eq.trans (finsum_congr fun p => ?_) hmap.symm
  simp [mul_comm]
theorem isBoundedBorelCompactlySupported_of_continuous {f : AmbientSpace → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) : IsBoundedBorelCompactlySupported f :=
  ⟨hf.measurable, hc.exists_bound_of_continuous hf, hc⟩
def ursellFunctionOfMeasure {L K : ℕ} (ν : Measure (RefinedGaugeField L K)) {n : ℕ}
    (f : Fin n → AmbientSpace → ℝ) : ℂ :=
  ursellFunction ν n f
theorem ursellFunctionOfMeasure_eq_mixedCumulant {L K : ℕ}
    (ν : Measure (RefinedGaugeField L K)) {n : ℕ} (f : Fin n → AmbientSpace → ℝ) :
    ursellFunctionOfMeasure ν f =
      Cumulants.mixedCumulant ν fun j U => (plaquetteSmearing (fun x => (f j x : ℂ)) U).re := by
  unfold ursellFunctionOfMeasure ursellFunction
  congr 1
  funext j U
  rw [plaquetteSmearing_ofReal, Complex.ofReal_re]
end InfiniteLattice
end YangMills.Construction
