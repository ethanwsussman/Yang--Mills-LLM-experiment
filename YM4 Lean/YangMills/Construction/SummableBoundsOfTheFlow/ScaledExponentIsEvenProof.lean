import YangMills.Construction.SummableBoundsOfTheFlow.ScaledExponentIsEven
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ScaledVariables
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.ReferenceDensity
variable {F : BlockFrame}
private theorem secondDerivAlong_neg_neg {ι : Type} [Fintype ι] [DecidableEq ι] (Ψ : BondField ι → ℝ)
    (η u v : BondField ι) : secondDerivAlong Ψ η (-u) (-v) = secondDerivAlong Ψ η u v := by
  have hlin : (fun ζ => fderiv ℝ Ψ ζ (-u)) = fun ζ => -(fderiv ℝ Ψ ζ u) := by
    funext ζ
    exact map_neg _ _
  unfold secondDerivAlong
  rw [hlin, fderiv_fun_neg]
  simp
private theorem bondVariation_neg {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι) (e : BondVector) :
    bondVariation b (-e) = -bondVariation b e := by
  unfold bondVariation
  funext i
  by_cases hib : i = b
  · subst hib
    simp
  · simp [Pi.single_eq_of_ne hib]
private theorem haarGapShift_neg (a l r : ℝ) : haarGapShift a (-l) r = haarGapShift a l r := by
  unfold haarGapShift
  rw [neg_sq]
private theorem neg_smul_neg_eq (l : ℝ) (ζ : StepVariable (finiteCells F)) : (-l) • (-ζ) = l • ζ := by
  rw [neg_smul, smul_neg, neg_neg]
private theorem rescaledCellTerm_neg_neg (a ρ l : ℝ) (Y : F.Cell) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) :
    rescaledCellTerm a ρ (-l) Y V (-ζ) = rescaledCellTerm a ρ l Y V ζ := by
  unfold rescaledCellTerm
  have hsm : (-l) • (-ζ) = l • ζ := neg_smul_neg_eq l ζ
  rw [hsm]
  have hsecond : ∀ (b : ↥(chordBonds (finiteCells F))) (v : ℝ),
      secondDerivAlong (chartedEnergyAtMinimizer a ρ V) ((v * -l) • (-ζ)) (bondVariation b ((-ζ) b)) (-ζ) =
        secondDerivAlong (chartedEnergyAtMinimizer a ρ V) ((v * l) • ζ) (bondVariation b (ζ b)) ζ := by
    intro b v
    have hpt : (v * -l) • (-ζ) = (v * l) • ζ := by
      rw [mul_neg, neg_smul, smul_neg, neg_neg]
    rw [hpt, Pi.neg_apply, bondVariation_neg, secondDerivAlong_neg_neg]
  simp only [hsecond, haarGapShift_neg]
theorem rescaledTermsEven_holds : RescaledTermsEven := by
  intro F a ρ lam f p ν l Y V ζ
  have hsm : (-l) • (-ζ) = l • ζ := neg_smul_neg_eq l ζ
  have hexp : rescaledExponent a ρ f ν (-l) V (-ζ) = rescaledExponent a ρ f ν l V ζ := by
    unfold rescaledExponent
    simp only [rescaledCellTerm_neg_neg, hsm]
  refine ⟨rescaledCellTerm_neg_neg a ρ l Y V ζ, hexp, ?_, ?_, ?_⟩
  · unfold rescaledEnergy
    rw [hexp]
    simp only [abs_neg, Pi.neg_apply, norm_neg]
  · unfold rescaledCellRemainder
    rw [rescaledCellTerm_neg_neg]
    simp only [Pi.neg_apply, norm_neg]
  · unfold rescaledCellExpansion
    rw [hsm]
end YangMills.Construction.ScaledVariables
end
