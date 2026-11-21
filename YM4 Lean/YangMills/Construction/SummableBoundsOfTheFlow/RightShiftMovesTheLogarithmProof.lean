import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftMovesTheLogarithm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
namespace LogDerivRightTranslation
variable {Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions}
  {U : Set (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)}
theorem fderiv_apply_eq_of_curve (hU : IsOpen U) (hdiag : ∀ r, diagonalTriple r ∈ U) (hsm : ContDiffOn ℝ 3 Θ U)
    (hexp : ∀ z ∈ U, expUnit (Θ z) = expUnit z.1 * expUnit z.2.1 * (expUnit z.2.2)⁻¹)
    (hzero : ∀ r, Θ (diagonalTriple r) = 0) (w : imaginaryQuaternions)
    (γ : ℝ → imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)
    (γ' : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)
    (h0 : γ 0 = diagonalTriple w) (hγ : HasDerivAt γ γ' 0) (A : ℝ → ℍ[ℝ]) (A' : ℍ[ℝ]) (hA : HasDerivAt A A' 0)
    (hEq : ∀ τ, (((expUnit (γ τ).1 * expUnit (γ τ).2.1 * (expUnit (γ τ).2.2)⁻¹ : UnitQuaternion)) : ℍ[ℝ]) = A τ) :
    ((fderiv ℝ Θ (diagonalTriple w) γ' : imaginaryQuaternions) : ℍ[ℝ]) = A' := by
  have hd : DifferentiableAt ℝ Θ (diagonalTriple w) :=
    ((hsm.contDiffAt (hU.mem_nhds (hdiag w))).differentiableAt (by simp))
  have hd' : HasFDerivAt Θ (fderiv ℝ Θ (diagonalTriple w)) (γ 0) := by
    rw [h0]
    exact hd.hasFDerivAt
  have h1 : HasDerivAt (fun τ => Θ (γ τ)) (fderiv ℝ Θ (diagonalTriple w) γ') 0 := hd'.comp_hasDerivAt 0 hγ
  have h2 : HasDerivAt (fun τ => ((Θ (γ τ) : imaginaryQuaternions) : ℍ[ℝ]))
      ((fderiv ℝ Θ (diagonalTriple w) γ' : imaginaryQuaternions) : ℍ[ℝ]) 0 := by
    have hs := (imaginaryQuaternions.subtypeL : imaginaryQuaternions →L[ℝ] ℍ[ℝ]).hasFDerivAt (x := Θ (γ 0))
    exact hs.comp_hasDerivAt 0 h1
  have hE : HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ])
      ((Θ (γ 0) : imaginaryQuaternions) : ℍ[ℝ]) := by
    rw [h0, hzero]
    exact hasFDerivAt_exp_zero (𝕂 := ℝ)
  have h3 := hE.comp_hasDerivAt (0 : ℝ) h2
  have hc : ContinuousAt γ 0 := hγ.continuousAt
  have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), γ τ ∈ U := hc.eventually (by rw [h0]; exact hU.mem_nhds (hdiag w))
  have h4 : (NormedSpace.exp ∘ fun τ => ((Θ (γ τ) : imaginaryQuaternions) : ℍ[ℝ])) =ᶠ[𝓝 0] A := by
    filter_upwards [hev] with τ hτ
    have h6 : ((expUnit (Θ (γ τ)) : UnitQuaternion) : ℍ[ℝ]) = _ := congrArg Subtype.val (hexp _ hτ)
    rw [hEq τ] at h6
    exact h6
  have h5 := (h3.congr_of_eventuallyEq h4.symm).unique hA
  simpa using h5
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem coe_expUnit (w : imaginaryQuaternions) :
    ((expUnit w : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (w : ℍ[ℝ]) := rfl
theorem coe_mul_unit (g h : UnitQuaternion) : ((g * h : UnitQuaternion) : ℍ[ℝ]) = (g : ℍ[ℝ]) * (h : ℍ[ℝ]) := rfl
end LogDerivRightTranslation
open LogDerivRightTranslation in
theorem logDerivAlongRightTranslation_holds : logDerivAlongRightTranslationStatement := by
  intro Θ U hU hdiag hsm hexp hzero w X
  refine ⟨?_, fun u hs => ?_⟩
  · have hγ : HasDerivAt
        (fun τ : ℝ => ((w, τ • X, w) : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions))
        (0, X, 0) 0 := by
      have h1 : HasDerivAt (fun τ : ℝ => τ • X) X 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const X
      exact (hasDerivAt_const (0 : ℝ) w).prodMk (h1.prodMk (hasDerivAt_const (0 : ℝ) w))
    have hA : HasDerivAt (fun τ : ℝ => NormedSpace.exp (w : ℍ[ℝ]) * NormedSpace.exp (τ • (X : ℍ[ℝ])) *
        (((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ]))
        (NormedSpace.exp (w : ℍ[ℝ]) * (X : ℍ[ℝ]) * (((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ])) 0 := by
      have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (X : ℍ[ℝ]) (0 : ℝ)
      simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
      exact (h2.const_mul _).mul_const _
    exact fderiv_apply_eq_of_curve hU hdiag hsm hexp hzero w _ _ (by simp [diagonalTriple]) hγ _ _ hA
      (fun τ => by
        simp only [coe_mul_unit, coe_expUnit]
        simp)
  · have hγ : HasDerivAt
        (fun τ : ℝ => ((w + τ • u, 0, w) : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions))
        (u, 0, 0) 0 := by
      have h1 : HasDerivAt (fun τ : ℝ => w + τ • u) u 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add w
      exact h1.prodMk ((hasDerivAt_const (0 : ℝ) (0 : imaginaryQuaternions)).prodMk (hasDerivAt_const (0 : ℝ) w))
    have hA := hs.mul_const (((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ])
    exact fderiv_apply_eq_of_curve hU hdiag hsm hexp hzero w _ _ (by simp [diagonalTriple]) hγ _ _ hA
      (fun τ => by
        simp only [coe_mul_unit, coe_expUnit, expUnit_zero]
        simp)
end Interpolation
end YangMills.Construction
end
