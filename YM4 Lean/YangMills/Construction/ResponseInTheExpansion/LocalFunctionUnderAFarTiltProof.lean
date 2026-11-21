import YangMills.Construction.ResponseInTheExpansion.FarVariablesSplitOverTheGasProof
import YangMills.Construction.ResponseInTheExpansion.InfluenceOfAFarTilt
import YangMills.Construction.ResponseInTheExpansion.LocalFunctionUnderAFarTilt
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction.ResponseInTheExpansion
open Dobrushin StepSettings StepGas RenormalizationStepParameters TorusFields TorusLumps CoreColumns WeightedResponses
namespace FarTiltLocalFunction
set_option linter.unusedSectionVars false
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
private theorem tilted_isActivityBounded {A : ResponseSetup R} {Q : Finset (TorusSite n)}
    {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ}
    {Yt : G.Config → ℝ} (hs : ∀ w, 0 ≤ A.score w)
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    (ht : IsGasTilt G A.score Q B e Yt) :
    G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) (fun σ => G.weight σ * Yt σ)
      fun i => 3 * G.spinActivity c i := by apply _root_.YangMills.Construction.ResponseInTheExpansion.Decorrelation.isActivityBounded_tilt <;> assumption
private theorem setGap_le_of_mem {Q : Finset (TorusSite n)} {Y : TorusSite n} (hY : Y ∈ Q) (i : G.GasSpin) :
    setGap Q i.1.core ≤ setGap {Y} i.1.core := by apply _root_.YangMills.Construction.TiltedGasResponse.setGap_le_setGap_singleton <;> assumption
private theorem coreWeightFrom_pos (Y : TorusSite n) (j : G.GasSpin) : 0 < G.coreWeightFrom Y j := by apply _root_.YangMills.Construction.GasComparison.coreWeightFrom_pos <;> assumption
private theorem tiltActivity_cases {s : R.labels.Ω → ℝ} {Q : Finset (TorusSite n)}
    {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ} {Yt : G.Config → ℝ}
    (ht : IsGasTilt G s Q B e Yt) (he : 1 ≤ e) (h8 : 8 * R.params.side ≤ R.range)
    (hz : ∀ i, 0 ≤ G.spinActivity c i) (i : G.GasSpin) :
    2 * (G.spinActivity c i + 3 * G.spinActivity c i) ≤ 2 * tiltActivity G c e Q i ∨ ∃ e' : ℝ, 0 ≤ e' ∧ e' ≤ 1 ∧
      8 * e' * G.spinActivity c i ≤ 2 * tiltActivity G c e Q i ∧
      ∀ (σ : G.Config) (v : G.SpinValue i), G.pairConstraint.IsAdmissible (Function.update σ i v) →
        v ≠ G.pairConstraint.vacant i →
        |Yt (Function.update σ i v) - Yt (Function.update σ i (G.pairConstraint.vacant i))| ≤
          e' * Yt (Function.update σ i (G.pairConstraint.vacant i)) := by
  classical
  have hz0 := hz i
  set z := G.spinActivity c i with hzd
  set l := setGap Q i.1.core with hl
  have hLpos : (0 : ℝ) < (R.params.side : ℝ) := by
    have : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
    exact_mod_cast this
  set quarter : ℝ := (R.range : ℝ) / (4 * R.params.side) with hquarter
  have hquarter2 : 2 ≤ quarter := by
    rw [hquarter, le_div_iff₀ (by positivity)]
    have : ((8 * R.params.side : ℕ) : ℝ) ≤ (R.range : ℝ) := by exact_mod_cast h8
    push_cast at this
    linarith
  have hhalf : (R.range : ℝ) / (2 * R.params.side) = 2 * quarter := by
    rw [hquarter]
    field_simp
    ring
  by_cases hfar : (R.range : ℝ) / (2 * R.params.side) ≤ (l : ℝ)
  · set E := Real.exp (-(R.params.rt * ((l : ℝ) - 2) / 2 ^ 5)) with hE
    have hb : 2 * tiltActivity G c e Q i = 8 * z * min 2 (e * E) := by
      unfold tiltActivity
      rw [if_pos hfar]
      ring
    rw [hb]
    by_cases he1 : e * E ≤ 1
    · have hmin : min 2 (e * E) = e * E := min_eq_right (by linarith)
      rw [hmin]
      have hl2r : (2 : ℝ) ≤ (l : ℝ) := by rw [hhalf] at hfar; linarith
      have hl2 : 2 ≤ l := by exact_mod_cast hl2r
      have hm : ((l - 2 : ℕ) : ℝ) = (l : ℝ) - 2 := by
        rw [Nat.cast_sub hl2]
        norm_num
      have hmr : (R.range : ℝ) / (4 * R.params.side) ≤ ((l - 2 : ℕ) : ℝ) := by
        rw [hm]
        rw [hhalf] at hfar
        linarith
      refine Or.inr ⟨e * E, mul_nonneg (by linarith) (Real.exp_pos _).le, he1, le_of_eq (by ring),
        fun σ v ha _ => ?_⟩
      have := ht.abs_update_sub_le σ i v (l - 2) ha hmr fun Y hY => by
        have hgap := setGap_le_of_mem hY i
        omega
      rw [hm] at this
      exact this
    · left
      have h1 : 1 ≤ min 2 (e * E) := le_min (by norm_num) (not_le.mp he1).le
      have : 8 * z * 1 ≤ 8 * z * min 2 (e * E) := mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
  · left
    have hb : 2 * tiltActivity G c e Q i = 16 * z := by
      unfold tiltActivity
      rw [if_neg hfar]
      ring
    rw [hb]
    linarith
private theorem tiltedGibbs_comparison_bound (hT : LinearResponse.TiltedGibbsComparison) {A : ResponseSetup R}
    {Q : Finset (TorusSite n)}
    {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ} {Yt : G.Config → ℝ} (he : 1 ≤ e)
    (h8 : 8 * R.params.side ≤ R.range)
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (cols : G.HasSmallColumns (fun j => j.1.Touches ∅) c hw)
    (ht : IsGasTilt G A.score Q B e Yt)
    (hw' : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) (fun σ => G.weight σ * Yt σ)
      fun i => 3 * G.spinActivity c i)
    (hz1 : ∀ i, G.spinActivity c i ≤ 1) {Y : TorusSite n} {H : G.Config → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hm : Measurable H)
    (hb : ∀ σ, |H σ| ≤ 2 * M)
    (hosc : G.pairConstraint.OscillationBound H fun i => 4 * M * nearBlockCost R * decayFromSet G {Y} i) :
    |∫ σ, H σ ∂(tiltedGibbsLaw G Yt) - G.expectation ∅ H| ≤
      4 * M * nearBlockCost R * (4 * ∑ i, decayFromSet G {Y} i * tiltActivity G c e Q i) := by
  have hz0 := hw.activity_nonneg
  have he0 : 0 ≤ e := by linarith
  have hp0 : ∀ i, 0 ≤ tiltActivity G c e Q i := fun i => by
    have h0 := hz0 i
    unfold tiltActivity
    refine mul_nonneg (by positivity) ?_
    split_ifs
    · exact le_min (by norm_num) (mul_nonneg he0 (Real.exp_pos _).le)
    · norm_num
  obtain ⟨a, ha0, hsum, hcmp⟩ := hT G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasure ∅) G.weight Yt
    (G.spinActivity c)
    (fun i => 3 * G.spinActivity c i) hw hw' (G.influenceMatrix c) (fun i => 2 * tiltActivity G c e Q i)
    (G.coreWeightFrom Y) ht.pos hz1
    cols.influenceMatrix_nonneg (fun i => mul_nonneg (by norm_num) (hp0 i)) (coreWeightFrom_pos Y) cols.kernel_le
    (fun j => by
      have h1 := cols.column_le Y j
      have h2 := cols.exp_le_half
      have h3 := coreWeightFrom_pos Y j
      calc _ ≤ _ := h1
        _ ≤ G.coreWeightFrom Y j * (1 / 2) := mul_le_mul_of_nonneg_left h2 h3.le
        _ = _ := by ring)
    (fun i => tiltActivity_cases ht he h8 hz0 i)
  have hres := hcmp H _ hm ⟨2 * M, hb⟩ hosc
  have hbr : 0 ≤ nearBlockCost R := (Real.exp_pos _).le
  have hsingle : ∀ i, decayFromSet G {Y} i = G.coreWeightFrom Y i := fun _ => rfl
  rw [abs_sub_comm]
  calc |G.expectation ∅ H - ∫ σ, H σ ∂(tiltedGibbsLaw G Yt)| ≤ _ := hres
    _ = 4 * M * nearBlockCost R * ∑ i, G.coreWeightFrom Y i * a i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsingle]
        ring
    _ ≤ 4 * M * nearBlockCost R * (2 * ∑ i, G.coreWeightFrom Y i * (2 * tiltActivity G c e Q i)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
        congr 1
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsingle]
        ring
private theorem nearBlockCost_exponent_le {rt r L cx : ℝ} (hrt : 0 < rt) (hr : 1 ≤ r) (hL : 1 ≤ L)
    (hcf : (2 ^ 16 + 2 ^ 7 * rt) * r ^ 4 ≤ cx) : rt / 2 ^ 6 * (10 * r / L + 8) ≤ cx := by
  have h1 : 10 * r / L ≤ 10 * r := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h2 : r ≤ r ^ 4 := by
    calc r = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ 4 := pow_le_pow_right₀ hr (by norm_num)
  have h3 : 10 * r / L + 8 ≤ 2 ^ 6 * r := by linarith
  have h4 : rt / 2 ^ 6 * (10 * r / L + 8) ≤ rt * r := by
    calc rt / 2 ^ 6 * (10 * r / L + 8) ≤ rt / 2 ^ 6 * (2 ^ 6 * r) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  have h6 : rt * r ≤ 2 ^ 7 * rt * r ^ 4 := by nlinarith
  nlinarith
set_option maxHeartbeats 1000000 in
theorem localFunctionFarTilt_of_bounds (hcols : ClusterExpansionOfAStep.GasColumnsSmall)
    (hpaid : clusterScoreIntegralBound) (hT : LinearResponse.TiltedGibbsComparison)
    (hinf : farTiltInfluenceStatement) (hcf : TorusLumps.CouplingFloorExists) :
    localFunctionFarTiltStatement := by
  classical
  obtain ⟨r₁, p₁, H₁⟩ := hcols
  obtain ⟨r₂, p₂, H₂⟩ := hpaid
  obtain ⟨r₃, p₃, H₃⟩ := hinf
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (r₃ c)), fun c => lt_min (p₁ c) (lt_min (p₂ c) (p₃ c)),
    fun T hT' hrt K => ?_⟩
  have t₁ := hrt.trans (min_le_left _ _)
  have t₂ := (hrt.trans (min_le_right _ _)).trans (min_le_left _ _)
  have t₃ := (hrt.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨y₁, H₁⟩ := H₁ T hT' t₁
  obtain ⟨y₂, H₂⟩ := H₂ T hT' t₂ K
  obtain ⟨y₃, C', hC', H₃⟩ := H₃ T hT' t₃ K
  have hrt0 := hT'.rt_pos
  have hch : 0 < T.gasRate := by
    have h1 := hT'.cE_pos
    have h2 := hT'.κ_pos
    have h3 := hT'.σ_pos
    unfold RenormalizationStepParameters.ParameterAssignment.gasRate RenormalizationStepParameters.ParameterAssignment.κ₁
    positivity
  obtain ⟨y₇, H₇⟩ := hcf T.gasRate (8 * T.side) T.rt hch
  refine ⟨max T.floorMin (max y₁ (max y₂ (max y₃ (max y₇ (200 * T.B))))), 16 * C', by positivity,
    fun y hy R A hK hAT n _ G hG Y Q B e Yt D H M hDr hQ hD he ht hm hM hb hosc => ?_⟩
  have fl : ∀ {a : ℝ}, a ≤ max y₁ (max y₂ (max y₃ (max y₇ (200 * T.B)))) → a ≤ y :=
    fun h => h.trans ((le_max_right _ _).trans hy)
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hy1 : y₁ ≤ y := fl (le_max_left _ _)
  have hy2 : y₂ ≤ y := fl ((le_max_left _ _).trans (le_max_right _ _))
  have hy3 : y₃ ≤ y := fl ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hy7 : y₇ ≤ y :=
    fl ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hy8 : 200 * T.B ≤ y :=
    fl ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hOT := hAT.onFamily
  obtain ⟨hR, hρA, hpc, hyx, hstep⟩ := id hOT
  have hx1 : 1 ≤ R.coupling := by
    have h1 : (1 : ℝ) ≤ T.floorMin := by
      have h2 := hT'.yC_ge
      exact h2.trans (le_max_left _ _)
    linarith only [h1, hy0, hyx]
  have hx0 : 0 < R.coupling := by linarith only [hx1]
  have hL : R.params.side = T.side := by rw [hR]; rfl
  have hRrt : R.params.rt = T.rt := by rw [hR]; rfl
  have hx' : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAT.abs_sub_le).2
    linarith only [h1, hy8, hyx]
  have hrtR : 0 < R.params.rt := by rw [hRrt]; exact hrt0
  obtain ⟨hw, cols⟩ := H₁ y hy1 R hOT hx' n G hG fun j => j.1.Touches ∅
  have paid := H₂ y hy2 R A hK hAT n G hG
  have hs := hAT.admissible.price.nonneg
  have hw' := tilted_isActivityBounded hs hw paid ht
  obtain ⟨c1, c2⟩ := H₇ R.coupling (hy7.trans hyx)
  have h8 : 8 * R.params.side ≤ R.range := by
    rw [hL]
    exact c1
  have hL1n : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hL1 : (1 : ℝ) ≤ (R.params.side : ℝ) := by exact_mod_cast hL1n
  have hr1 : (1 : ℝ) ≤ (R.range : ℝ) := by
    have : 1 ≤ R.range := by omega
    exact_mod_cast this
  have hz1 : ∀ i, G.spinActivity T.gasRate i ≤ 1 := fun i => by
    show Real.exp _ ≤ 1
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ 16 * T.gasRate * R.coupling * (supportUnitCount R.params.side R.range i.1 : ℝ) := by positivity
    linarith only [this]
  have hnear : nearBlockCost R ≤ Real.exp (T.gasRate * R.coupling) := by
    unfold nearBlockCost
    apply Real.exp_le_exp.mpr
    rw [← hRrt] at c2
    exact nearBlockCost_exponent_le hrtR hr1 hL1 c2
  have hcmp := tiltedGibbs_comparison_bound hT he h8 hw cols ht hw' hz1 hM hm hb hosc
  have hI := H₃ y hy3 R A hK hAT n G hG {Y} Q e D (Finset.singleton_nonempty Y) hQ he hDr fun a ha Y' hY' => by
    rw [Finset.mem_singleton.mp ha]
    exact hD Y' hY'
  have he0 : 0 ≤ e := by linarith
  have hQ0 : (0 : ℝ) ≤ (Q.card : ℝ) := Nat.cast_nonneg _
  have hbr : 0 ≤ nearBlockCost R := (Real.exp_pos _).le
  set Cn := C' * e * (Q.card : ℝ) with hCn
  have hCn0 : 0 ≤ Cn := by positivity
  have hexp : nearBlockCost R * Real.exp (-(7 * T.gasRate * R.coupling) - R.params.rt / 2 ^ 6 * D) ≤
      Real.exp (-(6 * T.gasRate * R.coupling) - R.params.rt * D / 2 ^ 6) := by
    calc nearBlockCost R * Real.exp (-(7 * T.gasRate * R.coupling) - R.params.rt / 2 ^ 6 * D)
        ≤ Real.exp (T.gasRate * R.coupling) *
            Real.exp (-(7 * T.gasRate * R.coupling) - R.params.rt / 2 ^ 6 * D) :=
          mul_le_mul_of_nonneg_right hnear (Real.exp_pos _).le
      _ = _ := by
          rw [← Real.exp_add]
          congr 1
          ring
  calc _ ≤ _ := hcmp
    _ ≤ 4 * M * nearBlockCost R *
          (4 * (Cn * Real.exp (-(7 * T.gasRate * R.coupling) - R.params.rt / 2 ^ 6 * D))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith only [hI]
    _ = 16 * M * Cn * (nearBlockCost R *
          Real.exp (-(7 * T.gasRate * R.coupling) - R.params.rt / 2 ^ 6 * D)) := by ring
    _ ≤ 16 * M * Cn * Real.exp (-(6 * T.gasRate * R.coupling) - R.params.rt * D / 2 ^ 6) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by
        rw [hCn]
        ring
end FarTiltLocalFunction
theorem localFunctionFarTiltStatement_holds (hcols : ClusterExpansionOfAStep.GasColumnsSmall)
    (hpaid : clusterScoreIntegralBound)
    (hT : LinearResponse.TiltedGibbsComparison) (hinf : farTiltInfluenceStatement)
    (hcf : TorusLumps.CouplingFloorExists) :
    localFunctionFarTiltStatement := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarTiltLocalFunction.localFunctionFarTilt_of_bounds <;> assumption
end YangMills.Construction.ResponseInTheExpansion
end
