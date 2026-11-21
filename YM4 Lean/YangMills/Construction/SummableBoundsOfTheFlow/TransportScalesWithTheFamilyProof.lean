import YangMills.Construction.SummableBoundsOfTheFlow.FlatFormOfAFamilyProof
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionIsAdmittedProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Interpolation
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace ScaledFamily
theorem iteratedFDeriv_zero_const_mul {k : ℕ} {c : ℝ} (hc : c ≠ 0) (g : (Fin k → ℝ) → ℝ)
    (v : Fin k → (Fin k → ℝ)) :
    iteratedFDeriv ℝ k (fun τ => c * g τ) 0 v = c * iteratedFDeriv ℝ k g 0 v := by apply _root_.YangMills.SharedProofs.p20802 <;> assumption
theorem bondDeriv_const_mul {j k : ℕ} {c : ℝ} (hc : c ≠ 0) (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (b : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fun W' => c * G W') W b X = c * bondDeriv G W b X :=
  iteratedFDeriv_zero_const_mul hc _ _
def scaleFamily (c : ℝ) (h : LocalFamily) : LocalFamily := fun F y W => c * h F y W
theorem subtractTrivial_scaleFamily (c : ℝ) (h : LocalFamily) (F : BlockFrame) (y : F.Site F.depth)
    (W : F.GaugeField F.depth) :
    subtractTrivial (scaleFamily c h) F y W = c * subtractTrivial h F y W := by
  simp only [ColdStepAtMirrorFrames.subtractTrivial, scaleFamily]; ring
theorem centredExpansion_scaleFamily (star : Bool) (a ρA : ℝ) (m : ℕ) (c : ℝ) (h : LocalFamily)
    (y : F.Site F.depth) (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    centredExpansion star a ρA m (scaleFamily c h) y η V = c * centredExpansion star a ρA m h y η V :=
  subtractTrivial_scaleFamily c h F y _
theorem cellCentredExpansion_scaleFamily (star : Bool) (a ρA : ℝ) (m : ℕ) (c : ℝ) (h : LocalFamily)
    (Y : F.Cell) (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) :
    cellCentredExpansion star a ρA m (scaleFamily c h) Y η V = c * cellCentredExpansion star a ρA m h Y η V := by
  simp only [cellCentredExpansion, centredExpansion_scaleFamily, Finset.mul_sum]
theorem abs_le_of_abs_mul_le {c d A E ε : ℝ} (hc : 0 < c) (hE : E = c * ε) (h : |c * d| ≤ A * E) :
    |d| ≤ A * ε := by
  rw [abs_mul, abs_of_pos hc, hE] at h
  have h' : c * |d| ≤ c * (A * ε) := by linarith
  exact le_of_mul_le_mul_left h' hc
theorem isRegularFamily_scaleFamily {L t n₀ : ℕ} {σ δ η₃ ε c : ℝ} {h : LocalFamily} (hc : 0 < c)
    (hh : IsRegularFamily L t n₀ σ δ ε (ε / η₃) h) :
    IsRegularFamily L t n₀ σ δ (c * ε) (c * ε / η₃) (scaleFamily c h) := by apply _root_.YangMills.Construction.Interpolation.FlatLimitOfFamily.isRegularFamily_scaleFamily <;> assumption
end ScaledFamily
open ScaledFamily in
theorem transportScalingStatement_proof : transportScalingStatement := by
  intro T hE hη hT ε hε t x h F V hx hh hF hV star
  set c : ℝ := T.E / ε with hcdef
  have hc : 0 < c := div_pos hE hε
  have hc0 : c ≠ 0 := hc.ne'
  have hcε : c * ε = T.E := by rw [hcdef]; field_simp
  have hrow : IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio (scaleFamily c h) := by
    have := isRegularFamily_scaleFamily (c := c) hc hh
    rwa [hcε] at this
  obtain ⟨hA, hB⟩ := hT t x (scaleFamily c h) F V hx hrow hF hV star
  have blockFun : ∀ {G : BlockFrame} (Y : G.Cell) (η : StepVariable (finiteCells G)),
      cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) (scaleFamily c h) Y η =
        fun V' => c * cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) h Y η V' := by
    intro G Y η
    funext V'
    exact cellCentredExpansion_scaleFamily star T.a T.chainParams.ρA (frameRadius x) c h Y η V'
  have hE₃ : T.energyRatio = T.E / T.η₃ := rfl
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro Y η hη' k b X
    have h0 := hA.smooth Y η hη' k b X
    rw [blockFun] at h0
    have h1 := (contDiffAt_const (c := c⁻¹)).mul h0
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
    simp only
    field_simp
  · intro Y k b X h1 h2 hX
    have := hA.lowDeriv Y k b X h1 h2 hX
    rw [blockFun, bondDeriv_const_mul hc0] at this
    have e : (2⁻¹ : ℝ) ^ 6 * T.E / torusDecayFactor T.L T.decayRate (bondSpan Y b) =
        (2⁻¹ ^ 6 / torusDecayFactor T.L T.decayRate (bondSpan Y b)) * T.E := by ring
    have e' : (2⁻¹ : ℝ) ^ 6 * ε / torusDecayFactor T.L T.decayRate (bondSpan Y b) =
        (2⁻¹ ^ 6 / torusDecayFactor T.L T.decayRate (bondSpan Y b)) * ε := by ring
    rw [e] at this
    rw [e']
    exact abs_le_of_abs_mul_le hc hcε.symm this
  · intro Y η b X hη' hX
    have := hA.thirdDeriv Y η b X hη' hX
    rw [blockFun, bondDeriv_const_mul hc0, hE₃] at this
    have e : (2⁻¹ : ℝ) ^ 6 * (T.E / T.η₃) / torusDecayFactor T.L T.decayRate (bondSpan Y b) =
        (2⁻¹ ^ 6 / T.η₃ / torusDecayFactor T.L T.decayRate (bondSpan Y b)) * T.E := by ring
    have e' : (2⁻¹ : ℝ) ^ 6 * (ε / T.η₃) / torusDecayFactor T.L T.decayRate (bondSpan Y b) =
        (2⁻¹ ^ 6 / T.η₃ / torusDecayFactor T.L T.decayRate (bondSpan Y b)) * ε := by ring
    rw [e] at this
    rw [e']
    exact abs_le_of_abs_mul_le hc hcε.symm this
  · intro Y η hη'
    have := hA.abs_le Y η hη'
    rw [cellCentredExpansion_scaleFamily] at this
    have e : (2⁻¹ : ℝ) ^ 8 * T.E / torusDecayFactor T.L T.decayRate T.blockIndex =
        (2⁻¹ ^ 8 / torusDecayFactor T.L T.decayRate T.blockIndex) * T.E := by ring
    have e' : (2⁻¹ : ℝ) ^ 8 * ε / torusDecayFactor T.L T.decayRate T.blockIndex =
        (2⁻¹ ^ 8 / torusDecayFactor T.L T.decayRate T.blockIndex) * ε := by ring
    rw [e] at this
    rw [e']
    exact abs_le_of_abs_mul_le hc hcε.symm this
  · intro F' V' Y Y' r hF' hV' hAg k e X hk he hX
    have := hB F' V' Y Y' r hF' hV' hAg k e X hk he hX
    rw [blockFun, blockFun, bondDeriv_const_mul hc0, bondDeriv_const_mul hc0, ← mul_sub] at this
    have e1 : (2⁻¹ : ℝ) ^ 5 * T.E / torusDecayFactor T.L T.decayRate r =
        (2⁻¹ ^ 5 / torusDecayFactor T.L T.decayRate r) * T.E := by ring
    have e2 : (2⁻¹ : ℝ) ^ 5 * ε / torusDecayFactor T.L T.decayRate r =
        (2⁻¹ ^ 5 / torusDecayFactor T.L T.decayRate r) * ε := by ring
    rw [e1] at this
    rw [e2]
    exact abs_le_of_abs_mul_le hc hcε.symm this
end YangMills.Construction.Interpolation
end
