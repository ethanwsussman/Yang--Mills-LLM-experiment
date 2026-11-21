import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionIsAdmittedProof
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfADensityOnTwoTori
import YangMills.Construction.SummableBoundsOfTheFlow.FlatFormOfTheMeanProof
import YangMills.Construction.SummableBoundsOfTheFlow.FramesVanishAtTheFlatField
import YangMills.Construction.SummableBoundsOfTheFlow.FreezingOfABlockExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation DerivativeInterpolation TorusFreezing
  SummableBounds FamilyNorms Estimates Filter Topology
namespace BlockMeans
namespace TwoTorusMean
variable {F : BlockFrame}
theorem bondDeriv_fin_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ}
    (G : F.GaugeField j → E) (W : F.GaugeField j) (c : Fin 0 → F.Site j × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p3568 <;> assumption
theorem bondSpan_fin_zero {j : ℕ} (y : F.Site j) (c : Fin 0 → F.Site j × Fin 4) :
    bondSpan y c = 0 := by
  simp [bondSpan]
theorem bondDeriv_sub_const {j k : ℕ} (G : F.GaugeField j → ℝ) (a : ℝ) (W : F.GaugeField j)
    (c : Fin (k + 1) → F.Site j × Fin 4) (X : Fin (k + 1) → imaginaryQuaternions) :
    bondDeriv (fun W' => G W' - a) W c X = bondDeriv G W c X := by
  unfold bondDeriv
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  have : (fderiv ℝ fun τ : Fin (k + 1) → ℝ => G (leftTranslate (bondSpread c X τ) W) - a) =
      fderiv ℝ fun τ : Fin (k + 1) → ℝ => G (leftTranslate (bondSpread c X τ) W) := by
    funext τ
    exact fderiv_sub_const _
  simp only [Function.comp, this]
theorem isSmallCurvature_uniformField {j : ℕ} {s : ℝ} (hs : 0 < s) :
    IsSmallCurvature s (uniformField F j) := by apply _root_.YangMills.SharedProofs.p8038 <;> assumption
theorem torusDecayFactor_pos (L : ℕ) (δ : ℝ) (r : ℕ) : 0 < torusDecayFactor L δ r :=
  mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
theorem one_le_torusDecayFactor (L : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (r : ℕ) :
    1 ≤ torusDecayFactor L δ r := by
  unfold torusDecayFactor
  exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_exp (by positivity))
theorem torusDecayFactor_mono (L : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) {r r' : ℕ} (h : r ≤ r') :
    torusDecayFactor L δ r ≤ torusDecayFactor L δ r' := by
  unfold torusDecayFactor
  have hrr : (r : ℝ) ≤ r' := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ (L : ℝ) ^ (1 / 640 : ℝ) := by positivity
  refine mul_le_mul (max_le_max le_rfl ?_) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    (le_trans zero_le_one (le_max_left _ _))
  · exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hrr h0) _
  · exact mul_le_mul_of_nonneg_left hrr hδ
theorem max_one_pow_mul_exp_neg_bounded (N : ℕ) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 ≤ y → max 1 ((y * a) ^ N) * Real.exp (-(c * y)) ≤ K := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.pow_mul_exp_bounded <;> assumption
theorem eventually_mul_exp_neg_mul_torusDecayFactor_le_one (L : ℕ) {δ c A : ℝ} (hδ : 0 ≤ δ)
    (hc : δ < c) :
    ∃ n : ℕ, ∀ r : ℕ, n ≤ r → A * Real.exp (-(c * r)) * torusDecayFactor L δ r ≤ 1 := by
  set b := (c - δ) / 2 with hb
  have hb0 : 0 < b := by
    rw [hb]
    linarith
  obtain ⟨K, hK0, hK⟩ :=
    max_one_pow_mul_exp_neg_bounded 16000 (a := ((L : ℝ) ^ (1 / 640 : ℝ))⁻¹) (by positivity) hb0
  have ht0 : Tendsto (fun r : ℕ => b * (r : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop).const_mul_atTop hb0
  have h2 : Tendsto (fun r : ℕ => Real.exp (-(b * (r : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp ht0
  have h3 : Tendsto (fun r : ℕ => |A| * K * Real.exp (-(b * (r : ℝ)))) atTop (𝓝 0) := by
    have := h2.const_mul (|A| * K)
    simpa using this
  obtain ⟨n, hn⟩ := eventually_atTop.1 (h3.eventually (gt_mem_nhds (zero_lt_one (α := ℝ))))
  refine ⟨n, fun r hr => ?_⟩
  refine le_trans ?_ (hn r hr).le
  have hy := hK r (Nat.cast_nonneg r)
  have e : Real.exp (-(c * r)) * torusDecayFactor L δ r =
      (max 1 (((r : ℝ) * ((L : ℝ) ^ (1 / 640 : ℝ))⁻¹) ^ 16000) * Real.exp (-(b * r))) *
        Real.exp (-(b * r)) := by
    unfold torusDecayFactor
    rw [div_eq_mul_inv]
    have e1 : Real.exp (-(c * r)) * Real.exp (δ * r) =
        Real.exp (-(b * r)) * Real.exp (-(b * r)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [hb]
      ring
    generalize max 1 (((r : ℝ) * ((L : ℝ) ^ (1 / 640 : ℝ))⁻¹) ^ 16000) = Mx at *
    calc Real.exp (-(c * r)) * (Mx * Real.exp (δ * r))
        = Mx * (Real.exp (-(c * r)) * Real.exp (δ * r)) := by ring
      _ = _ := by rw [e1]; ring
  have hE0 : 0 ≤ Real.exp (-(b * r)) := (Real.exp_pos _).le
  calc A * Real.exp (-(c * r)) * torusDecayFactor L δ r
      = A * (Real.exp (-(c * r)) * torusDecayFactor L δ r) := by ring
    _ ≤ |A| * (Real.exp (-(c * r)) * torusDecayFactor L δ r) :=
        mul_le_mul_of_nonneg_right (le_abs_self A)
          (mul_nonneg (Real.exp_pos _).le (torusDecayFactor_pos L δ r).le)
    _ ≤ |A| * (K * Real.exp (-(b * r))) := by
        rw [e]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hy hE0) (abs_nonneg A)
    _ = _ := by ring
theorem segmentEnd_nonneg_le_one (star : Bool) : 0 ≤ segmentEnd star ∧ segmentEnd star ≤ 1 := by
  cases star <;> simp [segmentEnd]
theorem conditionalExpansionMean_eq_ballExpectation (hE : interpolationAtEndpoints) (star : Bool)
    (a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (φ h : LocalFamily) (F : BlockFrame) (Y : F.Cell)
    (V : F.GaugeField F.top) :
    conditionalExpansionMean star a ρA ρ x m p φ h F Y V =
      ballExpectation (cutoffFactor ρ p) (familyLawExponent (segmentEnd star) a ρA x m φ V)
        (fun η => interpolatedBlockExpansion (segmentEnd star) a ρA m h Y η V) := by
  have h1 : stepExponent star a ρA x m φ 1 V =
      familyLawExponent (segmentEnd star) a ρA x m φ V :=
    funext fun η => ((hE F star a ρA 0 x 0 m V).2.2.2.2.2.1 φ η).symm
  have h2 : (fun η => cellCentredExpansion star a ρA m h Y η V) =
      fun η => interpolatedBlockExpansion (segmentEnd star) a ρA m h Y η V := by
    funext η
    unfold cellCentredExpansion interpolatedBlockExpansion
    refine Finset.sum_congr rfl fun y _ => ?_
    exact ((hE F star a ρA 0 x 0 m V).2.2.2.1 h y η).symm
  unfold conditionalExpansionMean cutoffMean
  rw [h1, h2]
  rfl
theorem cellCentredExpansion_uniformField {a ρA : ℝ} {m : ℕ} {star : Bool} (h : LocalFamily)
    (Y : F.Cell) (hf : fieldAboveFrame star a ρA m (uniformField F F.top) 0 = uniformField F F.depth) :
    cellCentredExpansion star a ρA m h Y 0 (uniformField F F.top) = 0 := by
  unfold cellCentredExpansion centredExpansion subtractTrivial
  rw [hf]
  simp
theorem IsRegularFamily.isNormBoundedLocalFamily {L t n₀ : ℕ} {σ δ ε ε₃ : ℝ} {h : LocalFamily}
    (hh : IsRegularFamily L t n₀ σ δ ε ε₃ h) : IsNormBoundedLocalFamily L t n₀ σ δ ε ε₃ h :=
  ⟨hh.smooth, hh.gauge_invariant, hh.translation_invariant, hh.decay, hh.locality⟩
def moveConstant (σ : ℝ) : ℝ := (1 + 64 / σ) ^ 2
theorem interpolatedSize_le {σ c D ε κ : ℝ} {r k : ℕ} (hσ : 0 < σ) (hc : 1 ≤ c) (hD : 1 ≤ D)
    (hε : 0 < ε) (hκ : 0 < κ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2) :
    interpolatedSize σ (c * ε * Real.exp (-(κ * r / 2 ^ 7))) (ε * D) k ≤
      ε * (c * (moveConstant σ + D)) * Real.exp (-(κ / 384 * r)) := by
  set E := Real.exp (-(κ * r / 2 ^ 7)) with hE
  set E' := Real.exp (-(κ / 384 * r)) with hE'
  have hEE : E ≤ E' := by
    refine Real.exp_le_exp.2 ?_
    have : κ / 384 * r ≤ κ * r / 2 ^ 7 := by
      have : 0 ≤ κ * r := by positivity
      norm_num
      nlinarith
    linarith
  have hE0 : 0 < E := Real.exp_pos _
  set θ : ℝ := (k : ℝ) / 3 with hθ
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk2' : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
  have part1 : c * ε * E / (σ / 64) ^ k ≤ ε * c * moveConstant σ * E' := by
    have hb : (1 : ℝ) ≤ 1 + 64 / σ := by
      have : 0 ≤ 64 / σ := by positivity
      linarith
    have h1 : (1 / (σ / 64)) ^ k ≤ moveConstant σ := by
      have e : 1 / (σ / 64) = 64 / σ := by
        field_simp
      rw [e]
      calc (64 / σ) ^ k ≤ (1 + 64 / σ) ^ k :=
            pow_le_pow_left₀ (by positivity) (by linarith) _
        _ ≤ (1 + 64 / σ) ^ 2 := pow_le_pow_right₀ hb hk2
    have h2 : c * ε * E / (σ / 64) ^ k = ε * c * E * (1 / (σ / 64)) ^ k := by
      rw [one_div, inv_pow]
      field_simp
    rw [h2]
    have hpos : 0 ≤ ε * c := by positivity
    calc ε * c * E * (1 / (σ / 64)) ^ k ≤ ε * c * E' * moveConstant σ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hEE hpos) h1 (by positivity) (by positivity)
      _ = _ := by ring
  have part2 : (c * ε * E) ^ (1 - θ) * (ε * D) ^ θ ≤ ε * c * D * E' := by
    have e1 : (c * ε * E) ^ (1 - θ) = c ^ (1 - θ) * ε ^ (1 - θ) * E ^ (1 - θ) := by
      rw [Real.mul_rpow (by positivity) hE0.le, Real.mul_rpow (by positivity) hε.le]
    have e2 : (ε * D) ^ θ = ε ^ θ * D ^ θ := Real.mul_rpow hε.le (by positivity)
    have e3 : ε ^ (1 - θ) * ε ^ θ = ε := by
      rw [← Real.rpow_add hε]
      simp
    have b1 : c ^ (1 - θ) ≤ c := by
      calc c ^ (1 - θ) ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc (by linarith)
        _ = c := Real.rpow_one c
    have b2 : D ^ θ ≤ D := by
      calc D ^ θ ≤ D ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD (by linarith)
        _ = D := Real.rpow_one D
    have b3 : E ^ (1 - θ) ≤ E' := by
      rw [hE, ← Real.exp_mul]
      refine Real.exp_le_exp.2 ?_
      have : κ / 384 * r ≤ κ * r / 2 ^ 7 * (1 - θ) := by
        have h3 : (1 : ℝ) / 3 ≤ 1 - θ := by linarith
        have : κ * r / 2 ^ 7 * (1 / 3) ≤ κ * r / 2 ^ 7 * (1 - θ) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        calc κ / 384 * r = κ * r / 2 ^ 7 * (1 / 3) := by ring
          _ ≤ _ := this
      linarith
    have p2 : 0 ≤ D ^ θ := by positivity
    have p3 : 0 ≤ E ^ (1 - θ) := by positivity
    calc (c * ε * E) ^ (1 - θ) * (ε * D) ^ θ
        = (ε ^ (1 - θ) * ε ^ θ) * (c ^ (1 - θ) * E ^ (1 - θ) * D ^ θ) := by
          rw [e1, e2]
          ring
      _ = ε * (c ^ (1 - θ) * E ^ (1 - θ) * D ^ θ) := by rw [e3]
      _ ≤ ε * (c * E' * D) := by
          refine mul_le_mul_of_nonneg_left ?_ hε.le
          exact mul_le_mul (mul_le_mul b1 b3 p3 (by positivity)) b2 p2 (by positivity)
      _ = _ := by ring
  unfold interpolatedSize
  rw [← hθ]
  calc _ ≤ ε * c * moveConstant σ * E' + ε * c * D * E' := add_le_add part1 part2
    _ = _ := by ring
theorem two_terms_le_of_floor {N' Z E' G ε : ℝ} (hN : 0 ≤ N') (hZ : 0 ≤ Z) (hE : 0 ≤ E')
    (hG : 0 < G) (hε : 0 < ε) (h : 16 * (N' + Z) * E' * G ≤ 1) :
    Z * ε * E' ≤ 2⁻¹ ^ 4 * ε / G ∧ N' * ε * E' ≤ 2⁻¹ ^ 4 * ε / G := by
  have a : 16 * Z * (E' * G) ≤ 1 := by
    have : 0 ≤ 16 * N' * (E' * G) := by positivity
    nlinarith
  have b : 16 * N' * (E' * G) ≤ 1 := by
    have : 0 ≤ 16 * Z * (E' * G) := by positivity
    nlinarith
  constructor
  · rw [le_div_iff₀ hG]
    nlinarith
  · rw [le_div_iff₀ hG]
    nlinarith
def thirdDerivConstant (η₃ c : ℝ) : ℝ := 2⁻¹ ^ 6 / η₃ + c + 1
def radiusFloorConstant (σ η₃ c C : ℝ) : ℝ :=
  16 * (2 * c + C * (c * (moveConstant σ + thirdDerivConstant η₃ c)))
set_option maxHeartbeats 1600000 in
theorem twoTorusMeanBoundsAt_of (hE : interpolationAtEndpoints)
    (hb : DensityDerivDiffLeOnTwoTori) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (ns : ℕ)
    (h1 : 1 ≤ T.CE) (hy1 : 1 ≤ T.coupling) (hσ : 0 < T.σ) (hη : 0 < T.η₃) (hκ : 0 < T.κ)
    (hone : SingleTorusMeanBoundsAt T) (hfr : BlockExpansionExpectationDecouples T)
    (htr : ∀ ε : ℝ, 0 < ε → TransportAtScale T ε) (hva : FramesVanishAtFlat T)
    (hns : ∀ r : ℕ, ns ≤ r → radiusFloorConstant T.σ T.η₃ T.CE hb.choose *
      Real.exp (-(T.κ / 384 * r)) * torusDecayFactor T.L T.decayRate r ≤ 1)
    (hy : ∀ x : ℝ, T.coupling ≤ x →
      4 * T.CE * x ^ (-(1 / 2 : ℝ)) ≤ 2⁻¹ ^ 5 / torusDecayFactor T.L T.decayRate ns) :
    TwoTorusMeanBoundsAt T := by
  obtain ⟨hC₂, hbb⟩ := hb.choose_spec
  set C₂ := hb.choose with hC₂def
  intro t x φ h ε star hx hε hφ hh
  have one := hone t x φ h ε star hx hε hφ hh
  have hx1 : 1 ≤ x := hy1.trans hx
  have hδ0 : 0 ≤ T.decayRate := by
    unfold StepParameters.decayRate
    positivity
  have xpow : x ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hfam := IsRegularFamily.isNormBoundedLocalFamily hh
  have hflat : ∀ (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F → ∀ Y : F.Cell,
      cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) h Y 0 (uniformField F F.top) = 0 :=
    fun F hF Y => cellCentredExpansion_uniformField h Y (hva t x F star hx hF).2
  have hfreeze : ∀ (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
      (Y : F.Cell) (Y' : F'.Cell) (q : ℕ), IsCubicTopTorus T.L t T.n₀ F →
      IsCubicTopTorus T.L t T.n₀ F' →
      IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
      AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q →
      |conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x) T.p φ h F Y V -
        conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x) T.p φ h F' Y' V'| ≤
      T.CE * ε * Real.exp (-(T.κ * q / 2 ^ 7)) := by
    intro F F' V V' Y Y' q hF hF' hV hV' hA
    rw [conditionalExpansionMean_eq_ballExpectation hE, conditionalExpansionMean_eq_ballExpectation hE]
    exact hfr t x (segmentEnd star) ε φ h F F' V V' Y Y' q hx (segmentEnd_nonneg_le_one star).1
      (segmentEnd_nonneg_le_one star).2 hε hφ hfam hF hF' hV hV' hA
  have hnear0 : ∀ (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell)
      (V : F.GaugeField F.top), IsSmallCurvature (5 / 4 * T.σ) V →
      |conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x) T.p φ h F Y V -
        cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) h Y 0 V| ≤
      T.CE * ε * x ^ (-(1 / 2 : ℝ)) := by
    intro F hF Y V hV
    have := one.near_block F hF Y V 0 Fin.elim0 Fin.elim0 hV (by norm_num) (fun l => l.elim0)
    rw [bondDeriv_fin_zero, bondDeriv_fin_zero, bondSpan_fin_zero] at this
    simpa using this
  have hloc : ∀ (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
      (Y : F.Cell) (Y' : F'.Cell) (r : ℕ), IsCubicTopTorus T.L t T.n₀ F →
      IsCubicTopTorus T.L t T.n₀ F' →
      IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
      AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
      ExpansionLocalAboveFrame star T.a T.chainParams.ρA T.decayRate ε T.L (frameRadius x) h V V' Y Y' r :=
    fun F F' V V' Y Y' r hF hF' hV hV' hA =>
      (htr ε hε t x h F V hx hh hF hV star).2 F' V' Y Y' r hF' hV' hA
  have hc54 : (0 : ℝ) < 5 / 4 * T.σ := by positivity
  have hcold98 : ∀ {F : BlockFrame} {V : F.GaugeField F.top}, IsSmallCurvature (9 / 8 * T.σ) V →
      IsSmallCurvature (5 / 4 * T.σ) V := by
    intro F V hV p hp
    have := hV p hp
    linarith
  have hnum : 0 ≤ moveConstant T.σ + thirdDerivConstant T.η₃ T.CE := by
    unfold moveConstant thirdDerivConstant
    positivity
  have hvalues : ∀ (F F' : BlockFrame), IsCubicTopTorus T.L t T.n₀ F →
      IsCubicTopTorus T.L t T.n₀ F' →
      ∀ (Y : F.Cell) (Y' : F'.Cell) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (r : ℕ),
      IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
      AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
      |centredFamily (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x)
          T.p φ h) F Y V -
        centredFamily (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x)
          T.p φ h) F' Y' V'| ≤
      2⁻¹ ^ 4 * ε / torusDecayFactor T.L T.decayRate r := by
    intro F F' hF hF' Y Y' V V' r hV hV' hA
    have fl : IsSmallCurvature (5 / 4 * T.σ) (uniformField F F.top) :=
      isSmallCurvature_uniformField hc54
    have fl' : IsSmallCurvature (5 / 4 * T.σ) (uniformField F' F'.top) :=
      isSmallCurvature_uniformField hc54
    unfold centredFamily
    have hGr := torusDecayFactor_pos T.L T.decayRate r
    by_cases hr : r < ns
    · have a1 := hnear0 F hF Y V hV
      have a2 := hnear0 F' hF' Y' V' hV'
      have a3 := hnear0 F hF Y _ fl
      have a4 := hnear0 F' hF' Y' _ fl'
      rw [hflat F hF Y] at a3
      rw [hflat F' hF' Y'] at a4
      have a5 := hloc F F' V V' Y Y' r hF hF' hV hV' hA 0 Fin.elim0 Fin.elim0 (by norm_num)
        (fun l => l.elim0) (fun l => l.elim0)
      rw [bondDeriv_fin_zero, bondDeriv_fin_zero] at a5
      have b := hy x hx
      have hGG : torusDecayFactor T.L T.decayRate r ≤ torusDecayFactor T.L T.decayRate ns :=
        torusDecayFactor_mono T.L hδ0 hr.le
      have b' : 2⁻¹ ^ 5 / torusDecayFactor T.L T.decayRate ns ≤
          2⁻¹ ^ 5 / torusDecayFactor T.L T.decayRate r :=
        div_le_div_of_nonneg_left (by norm_num) hGr hGG
      have b2 : 4 * (T.CE * ε * x ^ (-(1 / 2 : ℝ))) ≤
          2⁻¹ ^ 5 * ε / torusDecayFactor T.L T.decayRate r := by
        have : 4 * T.CE * x ^ (-(1 / 2 : ℝ)) * ε ≤
            2⁻¹ ^ 5 / torusDecayFactor T.L T.decayRate r * ε :=
          mul_le_mul_of_nonneg_right (b.trans b') hε.le
        calc _ = 4 * T.CE * x ^ (-(1 / 2 : ℝ)) * ε := by ring
          _ ≤ _ := this
          _ = _ := by ring
      have e5 : 2⁻¹ ^ 4 * ε / torusDecayFactor T.L T.decayRate r =
          2⁻¹ ^ 5 * ε / torusDecayFactor T.L T.decayRate r +
            2⁻¹ ^ 5 * ε / torusDecayFactor T.L T.decayRate r := by
        ring
      rw [e5]
      simp only [sub_zero] at a3 a4
      rw [abs_le] at a1 a2 a3 a4 a5 ⊢
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2, a5.1, a5.2]
    · have hr' : ns ≤ r := not_lt.1 hr
      have a1 := hfreeze F F' V V' Y Y' r hF hF' hV hV' hA
      have hAf : AgreeOnBall (finiteCells F) (uniformField F F.top) (finiteCells F')
          (uniformField F' F'.top) Y Y' r :=
        ⟨hA.1, hA.2.1, hA.2.2.1, fun b _ => rfl⟩
      have a2 := hfreeze F F' _ _ Y Y' r hF hF' fl fl' hAf
      have hfl' := hns r hr'
      set E' := Real.exp (-(T.κ / 384 * r)) with hE'
      have hEE : Real.exp (-(T.κ * r / 2 ^ 7)) ≤ E' := by
        refine Real.exp_le_exp.2 ?_
        have : 0 ≤ T.κ * r := by positivity
        norm_num
        nlinarith
      have hfb := (two_terms_le_of_floor (N' := 2 * T.CE) (Z := C₂ * (T.CE * (moveConstant T.σ +
        thirdDerivConstant T.η₃ T.CE))) (E' := E') (G := torusDecayFactor T.L T.decayRate r)
        (ε := ε) (by positivity) (by positivity) (Real.exp_pos _).le hGr hε hfl').2
      have hmul : T.CE * ε * Real.exp (-(T.κ * r / 2 ^ 7)) ≤ T.CE * ε * E' :=
        mul_le_mul_of_nonneg_left hEE (by positivity)
      rw [abs_le] at a1 a2 ⊢
      constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2]
  refine ⟨hvalues, ?_⟩
  · intro F F' hF hF' Y Y' V V' r k hs X hV hV' hA hk hbox hX
    cases k with
    | zero =>
      rw [bondDeriv_fin_zero, bondDeriv_fin_zero]
      exact hvalues F F' hF hF' Y Y' V V' r (hcold98 hV) (hcold98 hV') hA
    | succ k =>
      have e1 : bondDeriv (centredFamily (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x
          (frameRadius x) T.p φ h) F Y) V (bondsAt Y hs) X =
          bondDeriv (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x
          (frameRadius x) T.p φ h F Y) V (bondsAt Y hs) X := bondDeriv_sub_const _ _ _ _ _
      have e2 : bondDeriv (centredFamily (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x
          (frameRadius x) T.p φ h) F' Y') V' (bondsAt Y' hs) X =
          bondDeriv (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x
          (frameRadius x) T.p φ h F' Y') V' (bondsAt Y' hs) X := bondDeriv_sub_const _ _ _ _ _
      beta_reduce
      rw [e1, e2]
      have hGr := torusDecayFactor_pos T.L T.decayRate r
      by_cases hr : r < ns
      · have a1 := one.near_block F hF Y V (k + 1) (bondsAt Y hs) X (hcold98 hV) hk hX
        have a2 := one.near_block F' hF' Y' V' (k + 1) (bondsAt Y' hs) X (hcold98 hV') hk hX
        have a5 := hloc F F' V V' Y Y' r hF hF' (hcold98 hV) (hcold98 hV') hA (k + 1) hs X hk
          hbox hX
        have ex1 : Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y (bondsAt Y hs) : ℝ))) ≤ 1 :=
          Real.exp_le_one_iff.2 (by
            have : 0 ≤ T.κ / 2 ^ 6 * (bondSpan Y (bondsAt Y hs) : ℝ) := by positivity
            linarith)
        have ex2 : Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y' (bondsAt Y' hs) : ℝ))) ≤ 1 :=
          Real.exp_le_one_iff.2 (by
            have : 0 ≤ T.κ / 2 ^ 6 * (bondSpan Y' (bondsAt Y' hs) : ℝ) := by positivity
            linarith)
        have c0 : 0 ≤ T.CE * ε * x ^ (-(1 / 2 : ℝ)) := by positivity
        have a1' := a1.trans (mul_le_of_le_one_right c0 ex1)
        have a2' := a2.trans (mul_le_of_le_one_right c0 ex2)
        have b := hy x hx
        have hGG : torusDecayFactor T.L T.decayRate r ≤ torusDecayFactor T.L T.decayRate ns :=
          torusDecayFactor_mono T.L hδ0 hr.le
        have b' : 2⁻¹ ^ 5 / torusDecayFactor T.L T.decayRate ns ≤
            2⁻¹ ^ 5 / torusDecayFactor T.L T.decayRate r :=
          div_le_div_of_nonneg_left (by norm_num) hGr hGG
        have b2 : 4 * (T.CE * ε * x ^ (-(1 / 2 : ℝ))) ≤
            2⁻¹ ^ 5 * ε / torusDecayFactor T.L T.decayRate r := by
          have : 4 * T.CE * x ^ (-(1 / 2 : ℝ)) * ε ≤
              2⁻¹ ^ 5 / torusDecayFactor T.L T.decayRate r * ε :=
            mul_le_mul_of_nonneg_right (b.trans b') hε.le
          calc _ = 4 * T.CE * x ^ (-(1 / 2 : ℝ)) * ε := by ring
            _ ≤ _ := this
            _ = _ := by ring
        have e5 : 2⁻¹ ^ 4 * ε / torusDecayFactor T.L T.decayRate r =
            2⁻¹ ^ 5 * ε / torusDecayFactor T.L T.decayRate r +
              2⁻¹ ^ 5 * ε / torusDecayFactor T.L T.decayRate r := by
          ring
        rw [e5]
        rw [abs_le] at a1' a2' a5 ⊢
        constructor <;> linarith [a1'.1, a1'.2, a2'.1, a2'.2, a5.1, a5.2]
      · have hr' : ns ≤ r := not_lt.1 hr
        have hD1 : 1 ≤ thirdDerivConstant T.η₃ T.CE := by
          unfold thirdDerivConstant
          have h0 : 0 ≤ 2⁻¹ ^ 6 / T.η₃ := by positivity
          linarith only [h0, h1]
        have hthird : ∀ (F'' : BlockFrame) (Y'' : F''.Cell) (W : F''.GaugeField F''.top)
            (c : Fin 3 → F''.Site F''.top × Fin 4) (X' : Fin 3 → imaginaryQuaternions),
            IsCubicTopTorus T.L t T.n₀ F'' →
            IsSmallCurvature (5 / 4 * T.σ) W → AreUnitVectors X' →
            |bondDeriv (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x)
              T.p φ h F'' Y'') W c X'| ≤ ε * thirdDerivConstant T.η₃ T.CE := by
          intro F'' Y'' W c X' hF'' hW hX'
          have a := one.decay F'' hF'' Y'' W 3 c X' hW (by norm_num) le_rfl hX'
          refine a.trans ?_
          beta_reduce
          simp only [if_true]
          have hG1 := one_le_torusDecayFactor T.L hδ0 (bondSpan Y'' c)
          have t1 : 2⁻¹ ^ 6 * (ε / T.η₃) / torusDecayFactor T.L T.decayRate (bondSpan Y'' c) ≤
              2⁻¹ ^ 6 * (ε / T.η₃) :=
            div_le_self (by positivity) hG1
          have ex : Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y'' c : ℝ))) ≤ 1 :=
            Real.exp_le_one_iff.2 (by
              have : 0 ≤ T.κ / 2 ^ 6 * (bondSpan Y'' c : ℝ) := by positivity
              linarith)
          have t2 : T.CE * ε * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y'' c : ℝ))) ≤
              T.CE * ε := by
            have c0 : 0 ≤ T.CE * ε := by positivity
            calc _ ≤ T.CE * ε * x ^ (-(1 / 2 : ℝ)) * 1 :=
                  mul_le_mul_of_nonneg_left ex (by positivity)
              _ = T.CE * ε * x ^ (-(1 / 2 : ℝ)) := mul_one _
              _ ≤ T.CE * ε * 1 := mul_le_mul_of_nonneg_left xpow c0
              _ = T.CE * ε := mul_one _
          unfold thirdDerivConstant
          have e : ε * (2⁻¹ ^ 6 / T.η₃ + T.CE + 1) = 2⁻¹ ^ 6 * (ε / T.η₃) + T.CE * ε + ε := by
            ring
          rw [e]
          linarith
        have hM₀ : 0 < T.CE * ε * Real.exp (-(T.κ * r / 2 ^ 7)) := by positivity
        have key := hbb T.L t T.n₀ T.σ (T.CE * ε * Real.exp (-(T.κ * r / 2 ^ 7)))
          (ε * thirdDerivConstant T.η₃ T.CE)
          (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x) T.p φ h)
          F F' Y Y' V V' r (k + 1) hs X hσ hM₀ (by positivity) (by omega) hk hF hF' one.density
          hthird (fun W W' hW hW' hAW => hfreeze F F' W W' Y Y' r hF hF' hW hW' hAW) hV hV' hA
          hbox hX
        have hsz := interpolatedSize_le (σ := T.σ) (c := T.CE) (D := thirdDerivConstant T.η₃ T.CE)
          (ε := ε) (κ := T.κ) (r := r) (k := k + 1) hσ h1 hD1 hε hκ (by omega) hk
        have hfl' := hns r hr'
        set E' := Real.exp (-(T.κ / 384 * r)) with hE'
        have hfb := (two_terms_le_of_floor (N' := 2 * T.CE) (Z := C₂ * (T.CE * (moveConstant T.σ +
          thirdDerivConstant T.η₃ T.CE))) (E' := E') (G := torusDecayFactor T.L T.decayRate r)
          (ε := ε) (by positivity) (by positivity) (Real.exp_pos _).le hGr hε hfl').1
        refine key.trans ?_
        calc C₂ * interpolatedSize T.σ (T.CE * ε * Real.exp (-(T.κ * r / 2 ^ 7)))
              (ε * thirdDerivConstant T.η₃ T.CE) (k + 1)
            ≤ C₂ * (ε * (T.CE * (moveConstant T.σ + thirdDerivConstant T.η₃ T.CE)) * E') :=
              mul_le_mul_of_nonneg_left hsz hC₂.le
          _ = C₂ * (T.CE * (moveConstant T.σ + thirdDerivConstant T.η₃ T.CE)) * ε * E' := by ring
          _ ≤ _ := hfb
theorem exists_mul_rpow_neg_half_le_one {B : ℝ} (hB : 0 < B) :
    ∃ y : ℝ, 1 ≤ y ∧ ∀ x : ℝ, y ≤ x → B * x ^ (-(1 / 2 : ℝ)) ≤ 1 := by
  refine ⟨1 + B ^ 2, by nlinarith [sq_nonneg B], fun x hx => ?_⟩
  have hx0 : 0 < x := by nlinarith [sq_nonneg B]
  have hsq : B ≤ x ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  rw [Real.rpow_neg hx0.le]
  have hp : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  rw [← div_eq_mul_inv, div_le_one hp]
  exact hsq
end TwoTorusMean
open TwoTorusMean in
theorem twoTorusMeanStatement_holds (hone : singleTorusMeanStatement)
    (hfr : blockExpansionExpectationDecouples) (htr : TransportAtEveryScale)
    (hva : framesVanishAtFlatStatement) (hE : interpolationAtEndpoints)
    (hb : DensityDerivDiffLeOnTwoTori) (hj : EventuallyInParametersCombines) :
    twoTorusMeanStatement := by
  have hP := hj.1 _ _ hone (hj.1 _ _ hfr (hj.1 _ _ htr hva))
  intro a ha
  obtain ⟨L₁, p₁⟩ := hP a ha
  refine ⟨L₁, fun L ho hg c hc => ?_⟩
  obtain ⟨A₁, p₂⟩ := p₁ L ho hg c hc
  refine ⟨A₁, fun Ct hCt => ?_⟩
  obtain ⟨k₁, hk₁, p₃⟩ := p₂ Ct hCt
  refine ⟨k₁, hk₁, fun κ hκ hκ' => ?_⟩
  obtain ⟨e₁, he₁, p₄⟩ := p₃ κ hκ hκ'
  refine ⟨e₁, he₁, fun η₃ a1 a2 a3 => ?_⟩
  obtain ⟨N₁, p₅⟩ := p₄ η₃ a1 a2 a3
  refine ⟨N₁, fun nss hn => ?_⟩
  obtain ⟨s₁, hs₁, p₆⟩ := p₅ nss hn
  refine ⟨s₁, hs₁, fun σ b1 b2 q hq => ?_⟩
  obtain ⟨C₁, p₇⟩ := p₆ σ b1 b2 q hq
  refine ⟨C₁, fun Cs hCs E hE' => ?_⟩
  obtain ⟨m₁, p₈⟩ := p₇ Cs hCs E hE'
  refine ⟨m₁, fun n₀ hn₀ => ?_⟩
  obtain ⟨D₁, p₉⟩ := p₈ n₀ hn₀
  refine ⟨max 1 D₁, fun CE hCE => ?_⟩
  have hCE1 : 1 ≤ CE := (le_max_left _ _).trans hCE
  obtain ⟨y₁, p₁₀⟩ := p₉ CE ((le_max_right _ _).trans hCE)
  have hδ0 : 0 ≤ κ / 2 ^ 10 := by positivity
  have hδc : κ / 2 ^ 10 < κ / 384 := by
    norm_num
    linarith
  obtain ⟨ns, hns⟩ := eventually_mul_exp_neg_mul_torusDecayFactor_le_one L
    (A := radiusFloorConstant σ η₃ CE hb.choose) hδ0 hδc
  have hGns := torusDecayFactor_pos L (κ / 2 ^ 10) ns
  obtain ⟨Yv, hYv1, hYv⟩ := exists_mul_rpow_neg_half_le_one
    (B := 4 * CE * (torusDecayFactor L (κ / 2 ^ 10) ns / 2⁻¹ ^ 5)) (by positivity)
  refine ⟨max 1 (max y₁ Yv), fun y hy => ?_⟩
  have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
  have hy₂ : max y₁ Yv ≤ y := (le_max_right _ _).trans hy
  obtain ⟨c1, c2, c3, c4⟩ := p₁₀ y ((le_max_left _ _).trans hy₂)
  refine twoTorusMeanBoundsAt_of hE hb ⟨a, L, c, Ct, κ, η₃, nss, σ, q, Cs, E, n₀, CE, y⟩ ns hCE1 hy1
    b1 a1 hκ c1 c2 c3 c4 hns ?_
  intro x hx
  have h1 := hYv x (((le_max_right _ _).trans hy₂).trans hx)
  have e : (4 * CE * (torusDecayFactor L (κ / 2 ^ 10) ns / 2⁻¹ ^ 5)) * x ^ (-(1 / 2 : ℝ)) =
      (4 * CE * x ^ (-(1 / 2 : ℝ))) * (torusDecayFactor L (κ / 2 ^ 10) ns / 2⁻¹ ^ 5) := by ring
  rw [e] at h1
  have h2 : 0 < torusDecayFactor L (κ / 2 ^ 10) ns / 2⁻¹ ^ 5 := by positivity
  have h3 : 4 * CE * x ^ (-(1 / 2 : ℝ)) ≤ 1 / (torusDecayFactor L (κ / 2 ^ 10) ns / 2⁻¹ ^ 5) := by
    rw [le_div_iff₀ h2]
    exact h1
  have h4 : 1 / (torusDecayFactor L (κ / 2 ^ 10) ns / 2⁻¹ ^ 5) =
      2⁻¹ ^ 5 / torusDecayFactor L (κ / 2 ^ 10) ns := by
    field_simp
  rw [h4] at h3
  exact h3
end BlockMeans
end YangMills.Construction
end
