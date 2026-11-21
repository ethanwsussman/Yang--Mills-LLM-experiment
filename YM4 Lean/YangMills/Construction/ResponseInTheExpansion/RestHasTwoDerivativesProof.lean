import YangMills.Construction.ColdStepAtMirrorFrames.NoFirstOrderAtTheFlatField
import YangMills.Construction.ResponseInTheExpansion.CostPartIsASlot
import YangMills.Construction.ResponseInTheExpansion.ExpansionPartIsASlot
import YangMills.Construction.ResponseInTheExpansion.GapPartIsASlot
import YangMills.Construction.ResponseInTheExpansion.MeanOfTheBarrierPart
import YangMills.Construction.ResponseInTheExpansion.RestFreezesProof
import YangMills.Construction.ResponseInTheExpansion.RestIsGaugeInvariant
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open MeasureTheory
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames WeightedResponses Interpolation
namespace ResponseInTheExpansion
namespace DilationRemainderSecondOrder
private theorem ballExpectation_four_terms {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℝ → ℝ)
    (Ψ H₁ H₂ H₃ H₄ : BondField ι → ℝ)
    (h₁ : Integrable fun η => H₁ η * ballDensity r Ψ η) (h₂ : Integrable fun η => H₂ η * ballDensity r Ψ η)
    (h₃ : Integrable fun η => H₃ η * ballDensity r Ψ η) (h₄ : Integrable fun η => H₄ η * ballDensity r Ψ η) :
    ballExpectation r Ψ (fun η => - H₁ η + H₂ η + H₃ η - H₄ η) =
      - ballExpectation r Ψ H₁ + ballExpectation r Ψ H₂ + ballExpectation r Ψ H₃ - ballExpectation r Ψ H₄ := by apply _root_.YangMills.SharedProofs.p51892 <;> assumption
private theorem iteratedFDeriv_four_terms_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (w : ℝ)
    (g₁ g₂ g₃ g₄ : E → ℝ) (z : E)
    (v : Fin 2 → E) (h₁ : ContDiffAt ℝ 2 g₁ z) (h₂ : ContDiffAt ℝ 2 g₂ z) (h₃ : ContDiffAt ℝ 2 g₃ z)
    (h₄ : ContDiffAt ℝ 2 g₄ z) :
    iteratedFDeriv ℝ 2 (fun τ => w * (- g₁ τ + g₂ τ + g₃ τ - g₄ τ)) z v =
      w * (- iteratedFDeriv ℝ 2 g₁ z v + iteratedFDeriv ℝ 2 g₂ z v + iteratedFDeriv ℝ 2 g₃ z v -
        iteratedFDeriv ℝ 2 g₄ z v) := by
  have e : (fun τ => w * (- g₁ τ + g₂ τ + g₃ τ - g₄ τ)) =
      fun τ => ∑ j : Fin 4, (![- w, w, w, - w] j) * (![g₁, g₂, g₃, g₄] j) τ := by
    funext τ
    simp only [Fin.sum_univ_four]
    simp
    ring
  have hs : ∀ j ∈ (Finset.univ : Finset (Fin 4)), ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞)
      (fun τ => (![- w, w, w, - w] j) * (![g₁, g₂, g₃, g₄] j) τ) z := by
    intro j _
    have h2 : ((2 : ℕ) : WithTop ℕ∞) = 2 := rfl
    rw [h2]
    fin_cases j
    · exact contDiffAt_const.mul h₁
    · exact contDiffAt_const.mul h₂
    · exact contDiffAt_const.mul h₃
    · exact contDiffAt_const.mul h₄
  rw [e, iteratedFDeriv_finsetSum_apply Finset.univ 2 _ z hs v]
  have hc : ∀ (a : ℝ) (g : E → ℝ), ContDiffAt ℝ 2 g z →
      iteratedFDeriv ℝ 2 (fun τ => a * g τ) z v = a * iteratedFDeriv ℝ 2 g z v := by
    intro a g hg
    have := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := 2) (a := a) (f := g) (x := z) (by simpa using hg)
    have e2 : (fun τ => a * g τ) = a • g := by
      funext τ; simp
    rw [e2, this]
    simp
  simp only [Fin.sum_univ_four]
  have a0 := hc (- w) g₁ h₁
  have a1 := hc w g₂ h₂
  have a2 := hc w g₃ h₃
  have a3 := hc (- w) g₄ h₄
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [a0, a1, a2, a3]
  ring
private theorem eventually_le_CE (K : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ) :
    EventuallyInParameters fun T => K (parametersBeforeSide T) ≤ T.CE := by
  intro a _
  refine ⟨0, fun L _ _ c _ => ⟨0, fun Ct _ => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun nss _ =>
    ⟨1, one_pos, fun σ _ _ p _ => ⟨0, fun Cs _ => fun E _ => ⟨0, fun n₀ _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩
  exact ⟨K ⟨a, L, c, Ct, κ, η₃, nss, σ, p, Cs, E, 0, 0, 0⟩, fun CE h => ⟨0, fun y₁ _ => h⟩⟩
private theorem abs_le_of_expectation_bound {D M s c y E₅ E : ℝ} (hc : 0 ≤ c) (hy : 0 ≤ y)
    (hE₅ : E₅ ≤ E)
    (h₁ : |D - M| ≤ s * (c * y) * E) (h₂ : |M| ≤ c * (c * y) * E₅) : |D| ≤ (s + c) * c * y * E := by
  have h3 : c * (c * y) * E₅ ≤ c * (c * y) * E := mul_le_mul_of_nonneg_left hE₅ (by positivity)
  have h4 := abs_sub_abs_le_abs_sub D M
  calc |D| ≤ |D - M| + |M| := by linarith
    _ ≤ s * (c * y) * E + c * (c * y) * E := by linarith
    _ = (s + c) * c * y * E := by ring
private theorem abs_half_inv_four_terms_le {D₁ D₂ D₃ D₄ a b c d y E x CE z : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y)
    (hE : 0 ≤ E) (hz : z = x⁻¹ * y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hCE : a + b + c + d ≤ CE)
    (h₁ : |D₁| ≤ a * y * E) (h₂ : |D₂| ≤ b * y * E) (h₃ : |D₃| ≤ c * y * E) (h₄ : |D₄| ≤ d * y * E) :
    |1 / (2 * x) * (- D₁ + D₂ + D₃ - D₄)| ≤ CE * z * E := by
  have hs : |- D₁ + D₂ + D₃ - D₄| ≤ (a + b + c + d) * y * E := by
    have a1 := abs_le.1 h₁
    have a2 := abs_le.1 h₂
    have a3 := abs_le.1 h₃
    have a4 := abs_le.1 h₄
    refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]
  have hs2 : (a + b + c + d) * y * E ≤ CE * y * E := by gcongr
  rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * x)), hz]
  have hCE0 : 0 ≤ CE := by linarith
  calc 1 / (2 * x) * |- D₁ + D₂ + D₃ - D₄| ≤ 1 / (2 * x) * (CE * y * E) :=
        mul_le_mul_of_nonneg_left (hs.trans hs2) (by positivity)
    _ = 1 / 2 * (CE * (x⁻¹ * y) * E) := by field_simp
    _ ≤ CE * (x⁻¹ * y) * E := by
        have : 0 ≤ CE * (x⁻¹ * y) * E := by positivity
        linarith
end DilationRemainderSecondOrder
open DilationRemainderSecondOrder in
theorem dilationRemainder_secondOrder (hS : secondOrderSlotMeanStatement) (hBar : cutoffTermExpectationStatement)
    (hGap : gapTermSecondOrderStatement) (hRow : familyTermSlotStatement) (hCost : slopeTermRemainderStatement)
    (hGauge : dilationRemainderGaugeInvariantStatement) (hNo : FirstDerivVanishesAtUniform)
    (hJ : EventuallyInParametersCombines) : dilationRemainderSecondOrderStatement := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨B₁, hB₁, hB₁T⟩ := hBar
  obtain ⟨Cq₂, C₂, hq₂, hC₂, hG₂⟩ := hGap
  obtain ⟨Cq₃, C₃, hq₃, hC₃, hG₃⟩ := hRow
  obtain ⟨Cq₄, C₄, hq₄, hC₄, hG₄⟩ := hCost
  obtain ⟨S₂, hS₂, hS₂T⟩ := hS Cq₂ hq₂
  obtain ⟨S₃, hS₃, hS₃T⟩ := hS Cq₃ hq₃
  obtain ⟨S₄, hS₄, hS₄T⟩ := hS Cq₄ hq₄
  let Kc : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U => B₁ U + (S₂ U + C₂ U) * C₂ U + (S₃ U + C₃ U) * C₃ U + (S₄ U + C₄ U) * C₄ U
  have h64 : EventuallyInParameters fun T => 64 ≤ T.n₀ ∧ 1 ≤ T.coupling := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨64, fun _ h => ⟨0, fun _ _ => ⟨1, fun _ hy => ⟨h, hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine weaken _ _ ?_ (join _ _ hB₁T (join _ _ hG₂ (join _ _ hG₃ (join _ _ hG₄ (join _ _ hS₂T (join _ _ hS₃T
    (join _ _ hS₄T (join _ _ hGauge (join _ _ h64 (eventually_le_CE Kc))))))))))
  rintro T hDr ⟨bar, g₂, g₃, g₄, s₂, s₃, s₄, gau, ⟨h64', one⟩, hCE⟩
  intro t x f F V Y hst hrow
  have hx1 : 1 ≤ x := one.trans hst.coupling_le
  have hx0 : 0 < x := by linarith
  have hκ := hDr.κ_pos
  set Q := coldHalfLawAt T x f with hQ
  set U := parametersBeforeSide T with hU
  have hfin : Finite F.Cell := by
    obtain ⟨hLF, htt, n, hside, hn⟩ := hst.torus
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      rw [hper, hside]
      omega⟩
    exact Pi.finite
  have stand : ∀ W : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) W → IsAdmissibleAt T t x f F W :=
    fun W hW => ⟨hst.coupling_le, hst.family_bounded, hst.torus, hW⟩
  have split : ∀ W : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) W →
      Q.dilationRemainder Y W = 1 / (2 * x) * (- Q.expectationOf (Q.cutoffTerm Y) W + Q.expectationOf (Q.gapTerm Y) W +
        Q.expectationOf (Q.familyTerm Y) W - Q.expectationOf (Q.slopeTerm Y) W) := by
    intro W hW
    have b := (bar t x f F W Y (stand W hW) hrow).1
    have p₂ := (g₂ t x f F W Y (stand W hW) hrow).2.1
    have p₃ := (g₃ t x f F W Y (stand W hW) hrow).2.1
    have p₄ := (g₄ t x f F W Y (stand W hW) hrow).2.1
    exact congrArg (fun z => 1 / (2 * x) * z)
      (ballExpectation_four_terms Q.radialWeight (Q.exponent W) _ _ _ _ b p₂ p₃ p₄)
  have hmov : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      (fun τ : Fin k → ℝ => Q.dilationRemainder Y (leftTranslate (bondSpread c X τ) V)) =ᶠ[𝓝 0] fun τ =>
        1 / (2 * x) * (- Q.expectationOf (Q.cutoffTerm Y) (leftTranslate (bondSpread c X τ) V) +
          Q.expectationOf (Q.gapTerm Y) (leftTranslate (bondSpread c X τ) V) +
          Q.expectationOf (Q.familyTerm Y) (leftTranslate (bondSpread c X τ) V) -
          Q.expectationOf (Q.slopeTerm Y) (leftTranslate (bondSpread c X τ) V)) := by
    intro k c X
    filter_upwards [eventually_isSmallCurvature_leftTranslate hfin c X hst.small_curvature] with τ hτ
      using split _ hτ
  have hyp : ∀ {C : ℝ}, 0 < C → 0 < C * x ^ (-(1 / 2) : ℝ) := fun hC => mul_pos hC (Real.rpow_pos_of_pos hx0 _)
  have r₂ := s₂ t x (C₂ U * x ^ (-(1 / 2) : ℝ)) f F V Y _ hst hrow (hyp (hC₂ U)) (g₂ t x f F V Y hst hrow).1
  have r₃ := s₃ t x (C₃ U * x ^ (-(1 / 2) : ℝ)) f F V Y _ hst hrow (hyp (hC₃ U)) (g₃ t x f F V Y hst hrow).1
  have r₄ := s₄ t x (C₄ U * x ^ (-(1 / 2) : ℝ)) f F V Y _ hst hrow (hyp (hC₄ U)) (g₄ t x f F V Y hst hrow).1
  have r₁ := (bar t x f F V Y hst hrow).2
  refine ⟨fun k c X => ?_, fun c c' X X' hX hX' => ?_, fun c X hX => ?_⟩
  · have h := (contDiffAt_const (c := 1 / (2 * x))).mul
      ((((r₁.1 k c X).neg.add (r₂.1 k c X)).add (r₃.1 k c X)).sub (r₄.1 k c X))
    exact h.congr_of_eventuallyEq (hmov c X)
  · have hu : AreUnitVectors ![X, X'] := fun l => by
      fin_cases l
      · exact hX
      · exact hX'
    have e : bondDeriv (Q.dilationRemainder Y) V ![c, c'] ![X, X'] =
        1 / (2 * x) * (- bondDeriv (Q.expectationOf (Q.cutoffTerm Y)) V ![c, c'] ![X, X'] +
          bondDeriv (Q.expectationOf (Q.gapTerm Y)) V ![c, c'] ![X, X'] +
          bondDeriv (Q.expectationOf (Q.familyTerm Y)) V ![c, c'] ![X, X'] -
          bondDeriv (Q.expectationOf (Q.slopeTerm Y)) V ![c, c'] ![X, X']) := by
      unfold bondDeriv
      rw [((hmov ![c, c'] ![X, X']).iteratedFDeriv ℝ 2).eq_of_nhds]
      exact iteratedFDeriv_four_terms_apply _ _ _ _ _ _ _ (r₁.1 2 _ _) (r₂.1 2 _ _) (r₃.1 2 _ _) (r₄.1 2 _ _)
    rw [e]
    set E := Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y ![c, c'])) with hEd
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hE₅ : Real.exp (-(2 ^ 5 * T.κ * bondSpan Y ![c, c'])) ≤ E := by
      refine Real.exp_le_exp.2 ?_
      have hn : (0 : ℝ) ≤ bondSpan Y ![c, c'] := Nat.cast_nonneg _
      have : 0 ≤ T.κ * (bondSpan Y ![c, c'] : ℝ) := by positivity
      nlinarith
    have hy : 0 ≤ x ^ (-(1 / 2) : ℝ) := (Real.rpow_pos_of_pos hx0 _).le
    have b₂ := abs_le_of_expectation_bound (hC₂ U).le hy hE₅ (r₂.2 2 _ _ (by norm_num) le_rfl hu)
      ((g₂ t x f F V Y hst hrow).2.2 _ _ hu)
    have b₃ := abs_le_of_expectation_bound (hC₃ U).le hy hE₅ (r₃.2 2 _ _ (by norm_num) le_rfl hu)
      ((g₃ t x f F V Y hst hrow).2.2 _ _ hu)
    have b₄ := abs_le_of_expectation_bound (hC₄ U).le hy hE₅ (r₄.2 2 _ _ (by norm_num) le_rfl hu)
      ((g₄ t x f F V Y hst hrow).2.2 _ _ hu)
    have hz : x ^ (-(3 / 2) : ℝ) = x⁻¹ * x ^ (-(1 / 2) : ℝ) := by
      rw [show (-(3 / 2) : ℝ) = -1 + -(1 / 2) by norm_num, Real.rpow_add hx0, Real.rpow_neg_one]
    exact abs_half_inv_four_terms_le hx1 hy hE0 hz (hB₁ U) (mul_nonneg (add_nonneg (hS₂ U) (hC₂ U).le) (hC₂ U).le)
      (mul_nonneg (add_nonneg (hS₃ U) (hC₃ U).le) (hC₃ U).le) (mul_nonneg (add_nonneg (hS₄ U) (hC₄ U).le) (hC₄ U).le)
      (by simpa [Kc, add_assoc] using hCE) (r₁.2 _ _ hu) b₂ b₃ b₄
  · have hσ := hDr.σ_pos
    exact hNo F F.top (Q.dilationRemainder Y) (5 / 4 * T.σ) ![c] ![X] (by positivity)
      (fun W γ hW => gau t x f F W Y γ (stand W hW)) (fun l => by fin_cases l; exact hX)
end ResponseInTheExpansion
end YangMills.Construction
end
