import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionCoefficientsAtTwoFieldsProof
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionNearTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
namespace UniformFieldComparison
theorem one_le_decayWeight (L : ℕ) {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) : 1 ≤ torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.one_le_decayWeight <;> assumption
variable {F : BlockFrame}
theorem expFlow_zero {j : ℕ} (B : F.Site j → Fin 4 → imaginaryQuaternions) (W : F.GaugeField j) :
    expFlow B W 0 = W := by
  have h1 : expUnit 0 = 1 := by
    apply Subtype.ext
    show NormedSpace.exp (((0 : imaginaryQuaternions)) : Quaternion ℝ) = 1
    simp
  funext y i
  simp [expFlow, leftTranslate, h1]
theorem bondDeriv_sub_const_sub {j k : ℕ} (G : F.GaugeField j → ℝ) (a : ℝ) (W W' : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fun V => G V - a) W c X - bondDeriv (fun V => G V - a) W' c X =
      bondDeriv G W c X - bondDeriv G W' c X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.RegularFamilyDerivs.bondDeriv_sub_const_sub <;> assumption
end UniformFieldComparison
open UniformFieldComparison
theorem uniformFieldDerivComparison_holds (hflow : DerivBoundAlongFlow) :
    UniformFieldDerivComparison := by
  obtain ⟨C₀, hC₀, hfl⟩ := hflow
  refine ⟨3 * C₀, by positivity, ?_⟩
  intro L t n₀ σ δ E E₃ f F T y W B r k h X hf hF hδ hE hEE hT hW hflc hag hk hb hX
  have hW1 := hflc 1 zero_le_one le_rfl
  have hW0 := hflc 0 le_rfl zero_le_one
  rw [expFlow_zero] at hW0
  have h1 := hf.locality F F hF hF y y W (expFlow B (uniformField F F.depth) 1) r k h X hW hW1 hag hk hb hX
  have hsm : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      ContDiffThreeAlongBonds (f F y) (expFlow B (uniformField F F.depth) u) := fun u h0 h1 =>
    hf.smooth F hF y _ (hflc u h0 h1)
  have hbd : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ (l : ℕ) (c : Fin l → F.Site F.depth × Fin 4)
      (Z : Fin l → imaginaryQuaternions),
      1 ≤ l → l ≤ 3 → AreUnitVectors Z →
        ‖bondDeriv (f F y) (expFlow B (uniformField F F.depth) u) c Z‖ ≤ E₃ := by
    intro u h0 h1 l c Z hl1 hl3 hZ
    have a := hf.decay F hF y _ l c Z (hflc u h0 h1) hl1 hl3 hZ
    rw [Real.norm_eq_abs]
    have hE3 : 0 ≤ E₃ := hE.trans hEE
    have hG := one_le_decayWeight L (x := (bondSpan y c : ℝ)) hδ (by positivity)
    have hc : 0 ≤ (if l = 3 then E₃ else E) := by split_ifs <;> assumption
    have hle : (if l = 3 then E₃ else E) ≤ E₃ := by split_ifs <;> linarith
    exact a.trans ((div_le_self hc hG).trans hle)
  have h2 := hfl ℝ F F.depth T (f F y) (uniformField F F.depth) B (fun _ => E₃) hT
    (fun _ => hE.trans hEE) hsm hbd k (bondsAt y h) X hk hX
  rw [Real.norm_eq_abs] at h2
  have e := bondDeriv_sub_const_sub (f F y) (f F y (uniformField F F.depth))
    (expFlow B (uniformField F F.depth) 1) (uniformField F F.depth) (bondsAt y h) X
  have e' : bondDeriv (subtractTrivial f F y) (expFlow B (uniformField F F.depth) 1) (bondsAt y h) X -
      bondDeriv (subtractTrivial f F y) (uniformField F F.depth) (bondsAt y h) X =
      bondDeriv (f F y) (expFlow B (uniformField F F.depth) 1) (bondsAt y h) X -
      bondDeriv (f F y) (uniformField F F.depth) (bondsAt y h) X := e
  have h3 := abs_sub_le (bondDeriv (subtractTrivial f F y) W (bondsAt y h) X)
    (bondDeriv (subtractTrivial f F y) (expFlow B (uniformField F F.depth) 1) (bondsAt y h) X)
    (bondDeriv (subtractTrivial f F y) (uniformField F F.depth) (bondsAt y h) X)
  rw [e'] at h3
  have e3 : C₀ * (E₃ + E₃ + E₃) = 3 * C₀ * E₃ := by ring
  rw [e3] at h2
  linarith
end ColdStepAtMirrorFrames
end YangMills.Construction
end
