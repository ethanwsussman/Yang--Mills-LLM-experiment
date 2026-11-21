import YangMills.Construction.ColdStepAtMirrorFrames.ZeroFamilyIsAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace ZeroFamilyRegular
theorem torusDecayWeight_nonneg (L : ℕ) (δ x : ℝ) : 0 ≤ torusDecayFactor L δ x := by
  unfold torusDecayFactor
  have hpos : (0 : ℝ) < max 1 ((x / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  exact (mul_pos hpos (Real.exp_pos _)).le
theorem bondDeriv_zero {j k : ℕ} (W : F.GaugeField j) (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fun _ : F.GaugeField j => (0 : ℝ)) W c X = 0 := by
  unfold bondDeriv
  have : (fun τ : Fin k → ℝ => (fun _ : F.GaugeField j => (0 : ℝ)) (leftTranslate (bondSpread c X τ) W)) =
      fun _ => (0 : ℝ) := rfl
  rw [this, iteratedFDeriv_fun_zero]
  rfl
theorem subtractTrivial_zero : subtractTrivial (fun _ _ _ => 0) = fun _ _ _ => 0 := by
  funext F y W
  simp [subtractTrivial]
end ZeroFamilyRegular
open ZeroFamilyRegular in
theorem zeroFamilyIsRegular : ZeroFamilyIsRegular := by
  intro L t n₀ σ δ E E₃ hE hE₃
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F _ y W _ k c X
    exact contDiffAt_const
  · intro F _ y W γ _
    rfl
  · intro F _ y h W _
    rfl
  · intro F _ y W k c X _ _ _ _
    rw [bondDeriv_zero, abs_zero]
    apply div_nonneg _ (torusDecayWeight_nonneg _ _ _)
    split_ifs <;> assumption
  · intro F F' _ _ y y' W W' r k h X _ _ _ _ _ _
    rw [subtractTrivial_zero]
    rw [bondDeriv_zero, bondDeriv_zero, sub_zero, abs_zero]
    exact div_nonneg hE (torusDecayWeight_nonneg _ _ _)
  · refine ⟨fun _ _ _ _ => 0, ?_, ?_⟩
    · intro b b' X X'
      have : (fun n => hessianAtTrivial (fun _ _ _ => 0) L t n b b' X X') = fun _ => 0 := by
        funext n
        unfold hessianAtTrivial
        exact bondDeriv_zero _ _ _
      rw [this]
      exact tendsto_const_nhds
    · intro _ _ _ _ _ _ _ _
      exact hasSum_zero
end YangMills.Construction.ColdStepAtMirrorFrames
end
