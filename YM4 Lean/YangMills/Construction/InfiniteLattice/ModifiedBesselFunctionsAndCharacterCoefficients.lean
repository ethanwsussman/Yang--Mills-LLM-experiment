import YangMills.Construction.InfiniteLattice.SingleBondWeight
import YangMills.Construction.Matrices.RepresentationsFieldsAndSmoothFunctionsOnG
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open Matrices.ComplexMatrix2
def modBesselI (n : ℕ) (z : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ φ in (0 : ℝ)..Real.pi, Real.exp (z * Real.cos φ) * Real.cos ((n : ℝ) * φ)
def weightCharCoeff (β : ℝ) (l : HalfNatural) : ℂ :=
  ((2 * l.toReal + 1 : ℝ) : ℂ)⁻¹ *
    ∫ g : specialUnitary, InfiniteLattice.singleBondWeight β g * spinCharacter l g ∂haarProb
end YangMills.Construction.SpinHarmonics
end
