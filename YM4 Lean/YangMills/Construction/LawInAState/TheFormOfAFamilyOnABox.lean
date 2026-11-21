import YangMills.Construction.ClusterExpansionOfAStep.FormsOfAFamily
import YangMills.Construction.LawInAState.AxialFormsOnTheLattice
import YangMills.Construction.LawInAState.SecondOrderOfAFunctionOfTheField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BoxForm
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields
def bondsWithin (m : ℕ) : Finset LatticeBond :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(m : ℤ)) m) ×ˢ Finset.univ
def constantCurvaturePotential (ω : Fin 4 → Fin 4 → ℝ) : LatticeBond → ℝ :=
  AxialForms.axialForm fun _ μ ν => ω μ ν
def boxFormStatement : Prop :=
  ∀ ℓ : StepParameters, ℓ.Admissible → ∀ C : ℝ, 0 ≤ C → ∃ C' c : ℝ, 0 < c ∧
    ∀ f : LocalDensity, IsCurvatureFamily ℓ C f → ∀ ω ω' : Fin 4 → Fin 4 → ℝ,
      (∀ i j, ω i j = - ω j i) → (∀ i j, ω' i j = - ω' j i) → (∀ i j, |ω i j| ≤ 1) → (∀ i j, |ω' i j| ≤ 1) →
      ∀ (n : ℕ) [NeZero n] (z : TorusSite n) (m : ℕ), ℓ.n₀ ≤ n → 2 * (m + 1) + 2 < n →
        |∑ c ∈ bondsWithin m, ∑ c' ∈ bondsWithin m, StateLaw.flatHessian (f n z) (bondFrom z c) (bondFrom z c') *
            (constantCurvaturePotential ω c * constantCurvaturePotential ω' c') -
          ∑' cc, limitFormTerm f (curvatureAlong FlatHessian.quaternionI ω) (curvatureAlong FlatHessian.quaternionI ω') cc| ≤
          C' * Real.exp (-(c * m))
end YangMills.Construction.BoxForm
end
