import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SymbolTranslation
structure Properties (I I' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ) : Prop where
  exp_phase_eq_of_mkQuot_eq : ∀ (m : Fin 4 → ℤ) a b, I.mkQuot 1 a = I.mkQuot 1 b →
    Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec m)) (toComplexVec (I.pos a))) =
      Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec m)) (toComplexVec (I.pos b)))
  quotSymbol_addTwoPiInt : ∀ k (m : Fin 4 → ℤ), SymbolSummableAt I I' T k →
    SymbolSummableAt I I' T (addTwoPiInt k m) ∧
      IsUnit (phaseMul I' m : Module.End ℂ (I'.UnitQuot → ℂ)) ∧
      ∀ f : I.UnitQuot → ℂ, applyKernel (quotSymbol I I' T (addTwoPiInt k m)) f =
        Ring.inverse (phaseMul I' m : Module.End ℂ (I'.UnitQuot → ℂ))
          (applyKernel (quotSymbol I I' T k) (phaseMul I m f))
structure EndoProperties (I : PeriodicData) (T : I.Carrier → I.Carrier → ℂ) : Prop where
  trace_addTwoPiInt : ∀ [Fintype I.UnitQuot] k (m : Fin 4 → ℤ), SymbolSummableAt I I T k →
    Matrix.trace (Matrix.of (quotSymbol I I T (addTwoPiInt k m))) =
      Matrix.trace (Matrix.of (quotSymbol I I T k))
  det_addTwoPiInt : ∀ [Fintype I.UnitQuot] [DecidableEq I.UnitQuot] k (m : Fin 4 → ℤ),
    SymbolSummableAt I I T k →
      Matrix.det (Matrix.of (quotSymbol I I T (addTwoPiInt k m))) =
        Matrix.det (Matrix.of (quotSymbol I I T k))
def Claim : Prop :=
  (∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    ∀ T : I'.Carrier → I.Carrier → ℂ, IsPeriodicKernel I I' T → Properties I I' T) ∧
  ∀ I : PeriodicData, IsPeriodic I →
    ∀ T : I.Carrier → I.Carrier → ℂ, IsPeriodicKernel I I T → EndoProperties I T
end YangMills.Construction.PeriodicOperators.SymbolTranslation
end
