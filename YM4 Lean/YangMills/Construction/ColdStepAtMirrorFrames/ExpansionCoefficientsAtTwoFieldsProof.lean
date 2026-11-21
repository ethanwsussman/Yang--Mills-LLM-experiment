import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionCoefficientsAtTwoFields
import YangMills.Construction.ColdStepAtMirrorFrames.SumsAgainstFlatResponsesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames.RegularFamilyDerivs
variable {F : BlockFrame}
theorem one_le_torusDecayFactor (L : ℕ) {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) : 1 ≤ torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.one_le_decayWeight <;> assumption
theorem bondDeriv_sub_const_sub {j k : ℕ} (G : F.GaugeField j → ℝ) (a : ℝ) (W W' : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fun V => G V - a) W c X - bondDeriv (fun V => G V - a) W' c X =
      bondDeriv G W c X - bondDeriv G W' c X := by
  cases k with
  | zero =>
    simp only [bondDeriv, iteratedFDeriv_zero_apply]
    ring
  | succ n =>
    have key : ∀ U : F.GaugeField j, bondDeriv (fun V => G V - a) U c X = bondDeriv G U c X := by
      intro U
      unfold bondDeriv
      have e : iteratedFDeriv ℝ (n + 1)
            (fun τ : Fin (n + 1) → ℝ => G (leftTranslate (bondSpread c X τ) U) - a) =
          iteratedFDeriv ℝ (n + 1) (fun τ : Fin (n + 1) → ℝ => G (leftTranslate (bondSpread c X τ) U)) := by
        funext x
        have e2 : (fderiv ℝ fun τ : Fin (n + 1) → ℝ => G (leftTranslate (bondSpread c X τ) U) - a) =
            fderiv ℝ fun τ : Fin (n + 1) → ℝ => G (leftTranslate (bondSpread c X τ) U) := by
          funext τ
          exact fderiv_sub_const _
        rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, e2]
      rw [e]
    rw [key W, key W']
theorem regularFamilyDerivsAtTwoFields_of_derivBound (hflow : DerivBoundAlongFlow) :
    RegularFamilyDerivsAtTwoFields := by
  obtain ⟨C₀, hC₀, hfl⟩ := hflow
  refine ⟨3 * C₀, by positivity, ?_⟩
  intro L t n₀ σ δ E E₃ f F F' T y y' W W' B r k h X hf hF hF' hδ hE hEE hT hflc hW' hag hk hb hX
  have hW1 := hflc 1 zero_le_one le_rfl
  have h1 := hf.locality F F' hF hF' y y' (expFlow B W 1) W' r k h X hW1 hW' hag hk hb hX
  have hsm : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ContDiffThreeAlongBonds (f F y) (expFlow B W u) := fun u h0 h1 =>
    hf.smooth F hF y _ (hflc u h0 h1)
  have hbd : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ (l : ℕ) (c : Fin l → F.Site F.depth × Fin 4)
      (Z : Fin l → imaginaryQuaternions),
      1 ≤ l → l ≤ 3 → AreUnitVectors Z → ‖bondDeriv (f F y) (expFlow B W u) c Z‖ ≤ E₃ := by
    intro u h0 h1 l c Z hl1 hl3 hZ
    have a := hf.decay F hF y _ l c Z (hflc u h0 h1) hl1 hl3 hZ
    rw [Real.norm_eq_abs]
    have hE3 : 0 ≤ E₃ := hE.trans hEE
    have hG := one_le_torusDecayFactor L (x := (bondSpan y c : ℝ)) hδ (by positivity)
    have hc : 0 ≤ (if l = 3 then E₃ else E) := by split_ifs <;> assumption
    have hle : (if l = 3 then E₃ else E) ≤ E₃ := by split_ifs <;> linarith
    refine a.trans ((div_le_self hc hG).trans hle)
  have h2 := hfl ℝ F F.depth T (f F y) W B (fun _ => E₃) hT (fun _ => hE.trans hEE) hsm hbd k
    (bondsAt y h) X hk hX
  rw [Real.norm_eq_abs] at h2
  have e := bondDeriv_sub_const_sub (f F y) (f F y (uniformField F F.depth)) (expFlow B W 1) W (bondsAt y h) X
  have e' : bondDeriv (subtractTrivial f F y) (expFlow B W 1) (bondsAt y h) X -
        bondDeriv (subtractTrivial f F y) W (bondsAt y h) X =
      bondDeriv (f F y) (expFlow B W 1) (bondsAt y h) X - bondDeriv (f F y) W (bondsAt y h) X := e
  have h3 : |bondDeriv (subtractTrivial f F y) W (bondsAt y h) X -
        bondDeriv (subtractTrivial f F y) (expFlow B W 1) (bondsAt y h) X| ≤
      C₀ * (E₃ + E₃ + E₃) * ∑ b ∈ T, ‖B b.1 b.2‖ := by
    rw [abs_sub_comm, e']
    exact h2
  have h4 := abs_sub_le (bondDeriv (subtractTrivial f F y) W (bondsAt y h) X)
    (bondDeriv (subtractTrivial f F y) (expFlow B W 1) (bondsAt y h) X)
    (bondDeriv (subtractTrivial f F' y') W' (bondsAt y' h) X)
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames.RegularFamilyDerivs
end
