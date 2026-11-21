import YangMills.Construction.OneLoopLaw.CoefficientOfAFunctional
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace Massive
def axisSymbol (μ : Fin 4) (q : Fin 4 → ℂ) : ℂ := 2 - 2 * Complex.cos (q μ)
def latticeSymbol (q : Fin 4 → ℂ) : ℂ := ∑ μ, axisSymbol μ q
def resolvent (z : ℂ) (q : Fin 4 → ℂ) : ℂ := (latticeSymbol q + z)⁻¹
def partialIn (μ : Fin 4) (f : (Fin 4 → ℂ) → ℂ) (q : Fin 4 → ℂ) : ℂ :=
  deriv (fun t : ℂ => f (Function.update q μ t)) (q μ)
def restrictToSubmodule {E : Type} [AddCommGroup E] [Module ℝ E] (V : Submodule ℝ E) (T : E → E) :
    V →ₗ[ℝ] V :=
  Classical.epsilon fun T' : V →ₗ[ℝ] V => ∀ f : V, (T' f : E) = T f
def shiftedDetOn {E : Type} [AddCommGroup E] [Module ℝ E] (V : Submodule ℝ E) (T : E → E)
    (z : ℝ) : ℝ :=
  LinearMap.det (restrictToSubmodule V fun f => T f + z • f)
end Massive
section PeriodicCase
variable {L n : ℕ}
def gaugeLaplacian (U : Edge L n 0 0 → Matrices.ComplexMatrix2)
    (l : Vertex L n 0 0 → Matrices.ComplexMatrix2) : Vertex L n 0 0 → Matrices.ComplexMatrix2 :=
  PairedFunctionSpace.transposeOfValues (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0)
    (covDiff U) (covDiff U l)
def massiveHessian (U B : Edge L n 0 0 → Matrices.ComplexMatrix2) :
    Edge L n 0 0 → Matrices.ComplexMatrix2 :=
  complexHessianOperator U B + covDiff U
    (PairedFunctionSpace.transposeOfValues (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0)
      (covDiff U) B)
def massiveLogDet (z : ℝ) (U : Edge L n 0 0 → Matrices.ComplexMatrix2) : ℝ :=
  Real.log (Massive.shiftedDetOn (vertexFunctionSpace L n 0 0) (gaugeLaplacian U) z) -
    (1 / 2) * Real.log (Massive.shiftedDetOn (edgeFormSpace L n 0 0) (massiveHessian U) z)
def massiveLogDetFunctional (L n : ℕ) (z : ℝ) (U : Edge L n 0 0 → Matrices.ComplexMatrix2) : ℝ :=
  massiveLogDet z U - massiveLogDet z (Tower.trivialField L n 0 0)
end PeriodicCase
def massiveFieldFamily (L : ℕ) (z : ℝ) : PeriodicOperators.Tempered.FieldFamily L :=
  fun n => massiveLogDetFunctional L n z
def MassiveStiffnessExists {L : ℕ} (hL : 0 < L) (z : ℝ) : Prop :=
  ∃ c : ℝ, OneLoopLaw.FunctionalStiffness.HasStiffnessConstant hL (massiveFieldFamily L z) c
def massiveStiffness {L : ℕ} (hL : 0 < L) (z : ℝ) : ℝ :=
  OneLoopLaw.FunctionalStiffness.stiffnessConstant hL (massiveFieldFamily L z)
def massiveStiffnessDeriv {L : ℕ} (hL : 0 < L) (z : ℝ) : ℝ :=
  deriv (massiveStiffness hL) z
def massiveStiffnessDeriv2 {L : ℕ} (hL : 0 < L) (z : ℝ) : ℝ :=
  deriv (deriv (massiveStiffness hL)) z
namespace FullSpace
variable {L : ℕ}
def covDiffAdjoint (U B : Edge L 0 0 → Matrices.ComplexMatrix2) :
    Vertex L 0 0 → Matrices.ComplexMatrix2 :=
  PairedFunctionSpace.transposeOfValues (pairedFunctions (Vertex L 0 0)) (edgePairedSpace (meshAt L 0 0))
    (covDiff U) B
def gaugeLaplacian (U : Edge L 0 0 → Matrices.ComplexMatrix2) (l : Vertex L 0 0 → Matrices.ComplexMatrix2) :
    Vertex L 0 0 → Matrices.ComplexMatrix2 :=
  covDiffAdjoint U (covDiff U l)
def massiveHessian (U B : Edge L 0 0 → Matrices.ComplexMatrix2) : Edge L 0 0 → Matrices.ComplexMatrix2 :=
  complexHessianOperator U B + covDiff U (covDiffAdjoint U B)
end FullSpace
end Tower
end YangMills.Construction
end
