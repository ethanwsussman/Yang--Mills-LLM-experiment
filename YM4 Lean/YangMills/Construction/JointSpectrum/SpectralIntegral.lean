import YangMills.Construction.JointSpectrum.ScalarSpectralMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.JointSpectrum.SpectralIntegral
open YangMills.Construction.JointSpectrum
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [Nonempty ι]
def integralDomain (T : CommutingFamily H ι) (f : SpectralDomain ι → ℂ) : Set H :=
  {x | YangMills.Construction.ScalarSpectralMeasures.sqNormLIntegral
      (YangMills.Construction.ScalarSpectralMeasures.spectralMeasure T x) f < ∞}
def spectralIntegral (T : CommutingFamily H ι) (f : SpectralDomain ι → ℂ) (x : H) : H :=
  open Classical in
  if x ∈ integralDomain T f then YangMills.Construction.ScalarSpectralMeasures.l2Calculus T x f
  else 0
def jointSpectralMeasure (T : CommutingFamily H ι) (B : Set (SpectralDomain ι)) : H → H :=
  spectralIntegral T (B.indicator 1)
end YangMills.Construction.JointSpectrum.SpectralIntegral
