import YangMills.Construction.ColdStepAtMirrorFrames.SlopeOfAFrameBetween
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeBetweenComparesOnTwoToriProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Interpolation
open BlockAverages ColdStepAtMirrorFrames
variable {F : BlockFrame}
private theorem bondDeriv_order_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : F.GaugeField F.top → E) (V : F.GaugeField F.top) :
    bondDeriv G V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) = G V := by apply _root_.YangMills.SharedProofs.p27916 <;> assumption
private theorem exp_decay_consequences {Ct σ δ x m : ℝ} (hCt : 0 < Ct) (hσ : 0 < σ) (hx1 : 1 ≤ x)
    (hA : (16 + Ct * 2 ^ 10 / σ + Ct ^ 2) * x ^ 2 * Real.exp (-(δ / 4 * m)) ≤ 1) :
    Ct * Real.exp (-(δ / 4 * m)) ≤ 2⁻¹ ^ 10 * σ ∧ x * (Ct * (Ct * Real.exp (-(δ / 4 * m)))) ≤ 1 := by
  set e := Real.exp (-(δ / 4 * m)) with he
  have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx1
  have hpos1 : 0 < Ct * 2 ^ 10 / σ := by positivity
  have hpos2 : 0 < Ct ^ 2 := by positivity
  have hpart : ∀ B : ℝ, 0 ≤ B → B ≤ 16 + Ct * 2 ^ 10 / σ + Ct ^ 2 → B * x ^ 2 * e ≤ 1 := by
    intro B hB0 hB
    calc B * x ^ 2 * e ≤ (16 + Ct * 2 ^ 10 / σ + Ct ^ 2) * x ^ 2 * e := by gcongr
      _ ≤ 1 := hA
  constructor
  · have h1 := hpart (Ct * 2 ^ 10 / σ) hpos1.le (by linarith)
    have h2 : Ct * 2 ^ 10 / σ * e ≤ Ct * 2 ^ 10 / σ * x ^ 2 * e := by
      have : Ct * 2 ^ 10 / σ * e * 1 ≤ Ct * 2 ^ 10 / σ * e * x ^ 2 := by gcongr
      nlinarith
    have h3 := h2.trans h1
    have e2 : Ct * 2 ^ 10 / σ * e = Ct * e * 2 ^ 10 / σ := by ring
    rw [e2, div_le_one hσ] at h3
    have h4 : (2 : ℝ)⁻¹ ^ 10 = 1 / 2 ^ 10 := by norm_num
    rw [h4]
    have h5 : Ct * e ≤ σ / 2 ^ 10 := by rw [le_div_iff₀ (by norm_num)]; exact h3
    calc _ ≤ σ / 2 ^ 10 := h5
      _ = _ := by ring
  · have h1 := hpart (Ct ^ 2) hpos2.le (by linarith)
    have hx3 : x ≤ x ^ 2 := by nlinarith
    calc x * (Ct * (Ct * e)) = Ct ^ 2 * x * e := by ring
      _ ≤ Ct ^ 2 * x ^ 2 * e := by gcongr
      _ ≤ 1 := h1
theorem interpolatedSlopeSmallOnTorus_of_bounds (hSl : interpolatedSlopeBounds)
    (hF : Estimates.frameRadiusGrowthStatement) : interpolatedSlopeSmallOnTorus := by
  intro a ha
  refine ⟨2 ^ 40, fun L hL hL0 c hc => ?_⟩
  obtain ⟨C, σ₁, hC, hσ₁, hS⟩ := hSl a L c ha hL hL0 hc
  obtain ⟨⟨hρ, hρ1, hs₀, hδ₂, hκ₂, hK, hC1, hKk⟩, -⟩ := hc.classical
  refine ⟨max (max C |frameBoundConstant c|) 1, fun Ct hCt => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨0, fun nss _ => ⟨σ₁, hσ₁, fun σ hσ hσle p _ => ⟨0, fun Cs _ E _ => ⟨64, fun n₀ hn₀ =>
    ⟨0, fun CE _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩
  have hCC : C ≤ Ct := ((le_max_left _ _).trans (le_max_left _ _)).trans hCt
  have hCf : |frameBoundConstant c| ≤ Ct := ((le_max_right _ _).trans (le_max_left _ _)).trans hCt
  have hCt1 : 1 ≤ Ct := (le_max_right _ _).trans hCt
  have hCt0 : 0 < Ct := by linarith
  obtain ⟨y, hy1, hy⟩ := hF (16 + Ct * 2 ^ 10 / σ + Ct ^ 2) (c.δ₂ / 4) (by positivity) (by positivity)
  refine ⟨y, fun y₁ hy₁ t x hx G V s ht hsmall hs0 hs1 => ?_⟩
  have hx' : y₁ ≤ x := hx
  have hyx : y ≤ x := hy₁.trans hx'
  have hx1 : 1 ≤ x := hy1.trans hyx
  obtain ⟨hA, hAm⟩ := hy x hyx
  obtain ⟨f1, f2⟩ := exp_decay_consequences hCt0 hσ hx1 hA
  have hm16 : 16 ≤ frameRadius x := by
    have h0 : 0 ≤ Ct * 2 ^ 10 / σ + Ct ^ 2 := by positivity
    have h1 : (16 : ℝ) ≤ (frameRadius x : ℝ) := by linarith
    exact_mod_cast h1
  set m := frameRadius x with hm
  set e := Real.exp (-(c.δ₂ / 4 * (m : ℝ))) with he
  have he0 : 0 < e := Real.exp_pos _
  have hgap : frameDecayBound (frameBoundConstant c) c.δ₂ m ≤ Ct * e := by
    unfold frameDecayBound
    have : frameBoundConstant c ≤ Ct := (le_abs_self _).trans hCf
    gcongr
  have htorus : IsBlockTorus L G := by
    obtain ⟨h1, -, n, hn, hn0⟩ := ht
    exact ⟨h1, n, by
      have h2 : 64 ≤ n₀ := hn₀
      have h3 : n₀ ≤ n := hn0
      omega, hn⟩
  have hall := hS σ m G V hσ hσle hm16 (hgap.trans f1) htorus hsmall s ⟨hs0, hs1⟩
  have hdecay : ∀ b ∈ chordBonds (finiteCells G), ∀ e' : imaginaryQuaternions, ‖e'‖ = 1 →
      ∀ (k : ℕ) (c' : Fin k → G.Site G.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
      AreUnitVectors X →
      |bondDeriv (interpolatedSlope s a c.ρA m b e') V c' X| ≤
        Ct * (Ct * e) * Real.exp (-(c.δ₂ / 8 * bondListDistance (enclosingCell b.1) c')) := by
    intro b hb e' he' k c' X hk hX
    refine ((hall b hb e').2.2 he' k c' X hk hX).trans ?_
    have hC0 : 0 ≤ C := by linarith
    have h1 : C * frameDecayBound (frameBoundConstant c) c.δ₂ m ≤ Ct * (Ct * e) :=
      calc C * frameDecayBound (frameBoundConstant c) c.δ₂ m ≤ C * (Ct * e) := by gcongr
        _ ≤ Ct * (Ct * e) := by gcongr
    have h2 := Real.exp_pos (-(c.δ₂ / 8 * (bondListDistance (enclosingCell b.1) c' : ℝ)))
    gcongr
  refine ⟨fun b hb e' => (hall b hb e').2.1, fun b hb e' he' => ?_, hdecay⟩
  have h1 := hdecay b hb e' he' 0 Fin.elim0 Fin.elim0 (by omega) (fun l => l.elim0)
  rw [bondDeriv_order_zero] at h1
  simp only [bondListDistance, Finset.univ_eq_empty, Finset.sup_empty, bot_eq_zero', Nat.cast_zero, mul_zero,
    neg_zero, Real.exp_zero, mul_one] at h1
  have hx0 : 0 ≤ x := by linarith
  calc x * |interpolatedSlope s a c.ρA m b e' V| ≤ x * (Ct * (Ct * e)) := by gcongr
    _ ≤ 1 := f2
end YangMills.Construction.Interpolation
end
