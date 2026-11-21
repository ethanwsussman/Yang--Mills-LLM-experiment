import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormAboveTheFrame
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionIsAdmittedProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation.FlatLimitOfFamily
variable {F : BlockFrame}
theorem iteratedFDeriv_const_mul_at_zero {k : ℕ} {c : ℝ} (hc : c ≠ 0) (g : (Fin k → ℝ) → ℝ)
    (v : Fin k → (Fin k → ℝ)) :
    iteratedFDeriv ℝ k (fun τ => c * g τ) 0 v = c * iteratedFDeriv ℝ k g 0 v := by apply _root_.YangMills.SharedProofs.p20802 <;> assumption
theorem bondDeriv_const_mul {j k : ℕ} {c : ℝ} (hc : c ≠ 0) (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (b : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fun W' => c * G W') W b X = c * bondDeriv G W b X :=
  iteratedFDeriv_const_mul_at_zero hc _ _
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
theorem isRegularFamily_scaleFamily {L t n₀ : ℕ} {σ δ η₃ ε c : ℝ} {h : LocalFamily} (hc : 0 < c)
    (hh : IsRegularFamily L t n₀ σ δ ε (ε / η₃) h) :
    IsRegularFamily L t n₀ σ δ (c * ε) (c * ε / η₃) (scaleFamily c h) := by
  have hc0 : c ≠ 0 := hc.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F hF y W hW k b X
    exact contDiffAt_const.mul (hh.smooth F hF y W hW k b X)
  · intro F hF y W γ hW
    simp only [scaleFamily, hh.gauge_invariant F hF y W γ hW]
  · intro F hF y g W hW
    simp only [scaleFamily, hh.translation_invariant F hF y g W hW]
  · intro F hF y W k b X hW h1 h3 hX
    have e : bondDeriv (scaleFamily c h F y) W b X = c * bondDeriv (h F y) W b X :=
      bondDeriv_const_mul hc0 (h F y) W b X
    rw [e, abs_mul, abs_of_pos hc]
    have := hh.decay F hF y W k b X hW h1 h3 hX
    have h2 := mul_le_mul_of_nonneg_left this hc.le
    refine h2.trans (le_of_eq ?_)
    split_ifs <;> ring
  · intro F F' hF hF' y y' W W' r k e X hW hW' hA hk he hX
    have e1 : bondDeriv (subtractTrivial (scaleFamily c h) F y) W (bondsAt y e) X =
        c * bondDeriv (subtractTrivial h F y) W (bondsAt y e) X := by
      rw [← bondDeriv_const_mul hc0]
      congr 1
      funext W''
      exact subtractTrivial_scaleFamily c h F y W''
    have e2 : bondDeriv (subtractTrivial (scaleFamily c h) F' y') W' (bondsAt y' e) X =
        c * bondDeriv (subtractTrivial h F' y') W' (bondsAt y' e) X := by
      rw [← bondDeriv_const_mul hc0]
      congr 1
      funext W''
      exact subtractTrivial_scaleFamily c h F' y' W''
    rw [e1, e2, ← mul_sub, abs_mul, abs_of_pos hc]
    have := hh.locality F F' hF hF' y y' W W' r k e X hW hW' hA hk he hX
    have h2 := mul_le_mul_of_nonneg_left this hc.le
    refine h2.trans (le_of_eq ?_)
    ring
  · obtain ⟨q, hq, hz⟩ := hh.flat_limit
    refine ⟨fun b b' X X' => c * q b b' X X', ?_, ?_⟩
    · intro b b' X X'
      have e : (fun n => hessianAtTrivial (scaleFamily c h) L t n b b' X X') =
          fun n => c * hessianAtTrivial h L t n b b' X X' := by
        funext n
        exact bondDeriv_const_mul hc0 _ _ _ _
      rw [e]
      exact (hq b b' X X').const_mul c
    · intro Fm Fm' B B' h1 h2 h3 h4
      have := (hz Fm Fm' B B' h1 h2 h3 h4).mul_left c
      simpa using this
theorem hasBoundedFlatLimitForm_of_scaleFamily {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {star : Bool} {t : ℕ}
    {x c e e' : ℝ} {h : LocalFamily} (hc : 0 < c) (he : 0 ≤ e → c⁻¹ * e ≤ e')
    (hf : HasBoundedFlatLimitForm T.L t (expansionAtFrameFamily T star x (scaleFamily c h)) e) :
    HasBoundedFlatLimitForm T.L t (expansionAtFrameFamily T star x h) e' := by
  have hc0 : c ≠ 0 := hc.ne'
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  obtain ⟨q, hq, hv⟩ := hf
  refine ⟨fun b b' X X' => c⁻¹ * q b b' X X', fun b b' X X' => ?_, fun X μ ν B hX hμ hB => ?_⟩
  · have h1 := (hq b b' X X').const_mul c⁻¹
    refine h1.congr fun n => ?_
    unfold secondDerivAtUniform
    have e1 : (expansionAtFrameFamily T star x (scaleFamily c h) (cubicTorusFrame T.L t n) 0) =
        fun V => c * expansionAtFrameFamily T star x h (cubicTorusFrame T.L t n) 0 V := by
      funext V
      exact cellCentredExpansion_scaleFamily star T.a T.chainParams.ρA (frameRadius x) c h 0 0 V
    rw [e1, bondDeriv_const_mul hc0]
    field_simp
  · obtain ⟨v, hs, hb⟩ := hv X μ ν B hX hμ hB
    refine ⟨c⁻¹ * v, hs.mul_left c⁻¹, ?_⟩
    have h0 : 0 ≤ e := (abs_nonneg _).trans hb
    rw [abs_mul, abs_of_pos hci]
    exact (mul_le_mul_of_nonneg_left hb hci.le).trans (he h0)
theorem eventuallyInParameters_mono {P Q : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → Prop}
    (h : ∀ T, 1 ≤ T.E → 0 < T.η₃ → P T → Q T)
    (hP : EventuallyInParameters P) : EventuallyInParameters Q := by
  intro a ha
  obtain ⟨L₀, hL⟩ := hP a ha
  refine ⟨L₀, fun L ho hg c hc => ?_⟩
  obtain ⟨Ct₀, h1⟩ := hL L ho hg c hc
  refine ⟨Ct₀, fun Ct hCt => ?_⟩
  obtain ⟨κ₀, hκ0, h2⟩ := h1 Ct hCt
  refine ⟨κ₀, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨η₀, hη0, h3⟩ := h2 κ hκ hκ'
  refine ⟨η₀, hη0, fun η₃ a1 a2 a3 => ?_⟩
  obtain ⟨N₀, h4⟩ := h3 η₃ a1 a2 a3
  refine ⟨N₀, fun m hm => ?_⟩
  obtain ⟨σ₀, hσ0, h5⟩ := h4 m hm
  refine ⟨σ₀, hσ0, fun σ b1 b2 p hp => ?_⟩
  obtain ⟨C₀, h6⟩ := h5 σ b1 b2 p hp
  refine ⟨C₀, fun Cs hCs E hE => ?_⟩
  obtain ⟨m₀, h7⟩ := h6 Cs hCs E hE
  refine ⟨m₀, fun n₀ hn₀ => ?_⟩
  obtain ⟨C₁, h8⟩ := h7 n₀ hn₀
  refine ⟨C₁, fun CE hCE => ?_⟩
  obtain ⟨y₀, h9⟩ := h8 CE hCE
  exact ⟨y₀, fun y₁ hy => h _ hE a1 (h9 y₁ hy)⟩
theorem flatLimitOfFamily_of_aboveFrame (hF : flatLimitAboveFrameStatement) :
    flatLimitOfFamilyStatement := by
  refine eventuallyInParameters_mono ?_ hF
  intro T hE hη hT t x ε h hx hε hh
  set c : ℝ := T.E / ε with hcdef
  have hE0 : 0 < T.E := by linarith
  have hc : 0 < c := div_pos hE0 hε
  have hcε : c * ε = T.E := by
    rw [hcdef]
    field_simp
  have hrow : IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio (scaleFamily c h) := by
    have := isRegularFamily_scaleFamily (c := c) hc hh
    rwa [hcε] at this
  obtain ⟨h1, h2⟩ := hT t x (scaleFamily c h) hx hrow
  refine ⟨hasBoundedFlatLimitForm_of_scaleFamily hc (fun _ => by simp) h1,
    hasBoundedFlatLimitForm_of_scaleFamily hc (fun h0 => ?_) h2⟩
  set e := T.CE * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x)) with he
  have e1 : c⁻¹ = ε / T.E := by
    rw [hcdef]
    field_simp
  rw [e1]
  have h3 : ε / T.E ≤ ε := div_le_self hε.le hE
  calc ε / T.E * e ≤ ε * e := mul_le_mul_of_nonneg_right h3 h0
    _ = T.CE * ε * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x)) := by
      rw [he]
      ring
end Interpolation.FlatLimitOfFamily
end YangMills.Construction
end
