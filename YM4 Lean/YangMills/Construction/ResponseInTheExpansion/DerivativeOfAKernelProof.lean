import YangMills.Construction.ResponseInTheExpansion.DerivativeOfAKernel
import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABondProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields
open YangMills.Construction.StepCosts YangMills.Construction.WeightedResponses
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
namespace KernelDerivative
theorem hasDerivAt_partitionFn (s : ℝ) : HasDerivAt partitionFn (deriv partitionFn s) s := by apply _root_.YangMills.Construction.WeightedResponses.BondScore.hasDerivAt_partitionFn <;> assumption
theorem partitionFn_pos (hK : BondKernelProperties) (s : ℝ) : 0 < partitionFn s := by apply _root_.YangMills.Construction.WeightedResponses.BondScore.partitionFn_pos <;> assumption
theorem kernelHasCouplingDerivative_holds (hK : BondKernelProperties) (hT : BondScoreProperties) :
    KernelHasCouplingDerivative := by
  intro ℓ hfit x n _ b c W V
  set w := readAtLevel (stepBlockFrame ℓ.side n) 0 W with hw
  set q := bondMean ℓ w b c with hq
  set ρ := (q * (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re with hρ
  set r := ‖q‖ with hr
  have hz := partitionFn_pos hK (ℓ.coupling * x * r)
  have h1 : HasDerivAt (fun X : ℝ => ℓ.coupling * X * ρ) (ℓ.coupling * ρ) x := by
    simpa using ((hasDerivAt_id x).const_mul ℓ.coupling).mul_const ρ
  have h2 : HasDerivAt (fun X : ℝ => ℓ.coupling * X * r) (ℓ.coupling * r) x := by
    simpa using ((hasDerivAt_id x).const_mul ℓ.coupling).mul_const r
  have h3 : HasDerivAt (fun X : ℝ => partitionFn (ℓ.coupling * X * r))
      (deriv partitionFn (ℓ.coupling * x * r) * (ℓ.coupling * r)) x :=
    HasDerivAt.comp (h₂ := partitionFn) x (hasDerivAt_partitionFn _) h2
  have h4 : HasDerivAt
      (fun X : ℝ => Real.exp (ℓ.coupling * X * ρ) / partitionFn (ℓ.coupling * X * r))
      ((Real.exp (ℓ.coupling * x * ρ) * (ℓ.coupling * ρ) * partitionFn (ℓ.coupling * x * r) -
        Real.exp (ℓ.coupling * x * ρ) * (deriv partitionFn (ℓ.coupling * x * r) * (ℓ.coupling * r))) /
          partitionFn (ℓ.coupling * x * r) ^ 2) x :=
    h1.exp.div h3 hz.ne'
  have he : (fun X => bondKernelAt ℓ X W V b c) =
      fun X : ℝ => Real.exp (ℓ.coupling * X * ρ) / partitionFn (ℓ.coupling * X * r) := by
    funext X
    rw [bondKernelAt_eq_kernelOfElement]
    rfl
  rw [he]
  have hs : bondScore ℓ x W V b c =
      r * (deriv partitionFn (ℓ.coupling * x * r) / partitionFn (ℓ.coupling * x * r)) - ρ :=
    (hT ℓ hfit x n b c).2.1 W V
  have hk : bondKernelAt ℓ x W V b c =
      Real.exp (ℓ.coupling * x * ρ) / partitionFn (ℓ.coupling * x * r) := by
    rw [bondKernelAt_eq_kernelOfElement]
    rfl
  rw [hs, hk]
  have hfin : ∀ E Z d : ℝ, Z ≠ 0 → -ℓ.coupling * (r * (d / Z) - ρ) * (E / Z) =
      (E * (ℓ.coupling * ρ) * Z - E * (d * (ℓ.coupling * r))) / Z ^ 2 := by
    intro E Z d hZ
    field_simp
    ring
  rw [hfin _ _ _ hz.ne']
  exact h4
end KernelDerivative
end YangMills.Construction.ResponseInTheExpansion
end
