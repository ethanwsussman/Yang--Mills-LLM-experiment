import YangMills.Construction.ColdStepAtMirrorFrames.FlatResponsesAreScalarProof
import YangMills.Construction.ColdStepAtMirrorFrames.NoFirstOrderAtTheFlatField
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAlongAMotion
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderKillsGradients
import YangMills.Construction.SummableBoundsOfTheFlow.GaugeOfAMotion
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages YangMills.Construction.Estimates YangMills.Construction.GaugeAlongMotion
namespace YangMills.Construction.ColdStepAtMirrorFrames
open BlockOffsets
variable {F : BlockFrame}
namespace GradientInvariance
theorem isSmallCurvature_leftTranslate_uniform {j : ℕ} (v : F.Site j → Fin 4 → imaginaryQuaternions) {s ε : ℝ}
    (hε : ∀ x i, ‖v x i‖ ≤ ε) (hs : 4 * ε < s) : IsSmallCurvature s (leftTranslate v (uniformField F j)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponse.isSmallCurvature_leftTranslate_uniform <;> assumption
theorem adjointAction_one (v : imaginaryQuaternions) : adjointAction (1 : UnitQuaternion) v = v := by
  apply Subtype.ext
  simp [adjointAction]
def twoFormMotion {j : ℕ} (a₀ a₁ : F.Site j → Fin 4 → ℝ) (X₀ X₁ : imaginaryQuaternions) (τ : Fin 2 → ℝ) :
    F.Site j → Fin 4 → imaginaryQuaternions :=
  fun x i => (τ 0 * a₀ x i) • X₀ + (τ 1 * a₁ x i) • X₁
def twoGaugeForms {j : ℕ} (φ₀ φ₁ : F.Site j → ℝ) (X₀ X₁ : imaginaryQuaternions) :
    Fin 2 → F.Site j → imaginaryQuaternions :=
  ![fun z => φ₀ z • X₀, fun z => φ₁ z • X₁]
theorem motionComponent_bounded {j : ℕ} (hper : ∀ i, F.period j i ≠ 0)
    (α : (Fin 2 → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions) :
    ∃ Aq : ℕ → ℝ, (∀ q, 0 ≤ Aq q) ∧ ∀ (q : ℕ) (e : Fin q → Fin 2) (x : F.Site j) (i : Fin 4),
      ‖motionComponent α e x i‖ ≤ Aq q := by
  have : ∀ i, NeZero (F.period j i) := fun i => ⟨hper i⟩
  letI : Fintype (F.Site j) := Fintype.ofFinite _
  refine ⟨fun q => ∑ x : F.Site j, ∑ i : Fin 4, ‖iteratedFDeriv ℝ q (fun τ => α τ x i) 0‖,
    fun q => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _, ?_⟩
  intro q e x i
  have h1 : ‖motionComponent α e x i‖ ≤ ‖iteratedFDeriv ℝ q (fun τ => α τ x i) 0‖ := by
    unfold motionComponent
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have : ∏ m, ‖(Pi.single (e m) 1 : Fin 2 → ℝ)‖ = 1 := by
      refine Finset.prod_eq_one fun m _ => ?_
      simp [Pi.norm_single]
    rw [this, mul_one]
  refine h1.trans ?_
  refine le_trans ?_ (Finset.single_le_sum (f := fun x => ∑ i : Fin 4, ‖iteratedFDeriv ℝ q (fun τ => α τ x i) 0‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ x))
  exact Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ q (fun τ => α τ x i) 0‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
theorem gaugeForms_bounded {j : ℕ} (hper : ∀ i, F.period j i ≠ 0) (ψ : Fin 2 → F.Site j → imaginaryQuaternions) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : F.Site j) (l : Fin 2), ‖ψ l z‖ ≤ B := by
  have : ∀ i, NeZero (F.period j i) := fun i => ⟨hper i⟩
  letI : Fintype (F.Site j) := Fintype.ofFinite _
  refine ⟨∑ l : Fin 2, ∑ z : F.Site j, ‖ψ l z‖, Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _, ?_⟩
  intro z l
  refine le_trans ?_ (Finset.single_le_sum (f := fun l => ∑ z : F.Site j, ‖ψ l z‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ l))
  exact Finset.single_le_sum (f := fun z => ‖ψ l z‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ z)
def twoFormMotionCLM {j : ℕ} (a₀ a₁ : F.Site j → Fin 4 → ℝ) (X₀ X₁ : imaginaryQuaternions) (x : F.Site j) (i : Fin 4) :
    (Fin 2 → ℝ) →L[ℝ] imaginaryQuaternions :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight (a₀ x i • X₀) +
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).smulRight (a₁ x i • X₁)
theorem twoFormMotion_eq_clm {j : ℕ} (a₀ a₁ : F.Site j → Fin 4 → ℝ) (X₀ X₁ : imaginaryQuaternions) (x : F.Site j)
    (i : Fin 4) : (fun τ => twoFormMotion a₀ a₁ X₀ X₁ τ x i) = twoFormMotionCLM a₀ a₁ X₀ X₁ x i := by
  funext τ
  simp [twoFormMotion, twoFormMotionCLM, mul_smul]
theorem motionComponent_twoFormMotion {j : ℕ} (a₀ a₁ : F.Site j → Fin 4 → ℝ) (X₀ X₁ : imaginaryQuaternions) (l : Fin 2)
    (x : F.Site j) (i : Fin 4) :
    motionComponent (twoFormMotion a₀ a₁ X₀ X₁) (fun _ : Fin 1 => l) x i =
      twoFormMotionCLM a₀ a₁ X₀ X₁ x i (Pi.single l 1) := by
  unfold motionComponent
  rw [iteratedFDeriv_one_apply, twoFormMotion_eq_clm, (twoFormMotionCLM a₀ a₁ X₀ X₁ x i).fderiv]
end GradientInvariance
open GradientInvariance in
theorem secondDerivGradientInvariant_holds (hS : SecondOrderAlongMotionFormula)
    (hN : FirstDerivVanishesAtUniform) (hG : gaugeAlongMotionStatement) :
    SecondDerivGradientInvariant := by
  intro F j T G s X₀ X₁ φ₀ φ₁ a₀ a₁ hT hper hs hsm hinv hX₀ hX₁
  classical
  set α := twoFormMotion a₀ a₁ X₀ X₁ with hαdef
  set ψ := twoGaugeForms φ₀ φ₁ X₀ X₁ with hψdef
  have hαC : ∀ x i, ContDiffAt ℝ 3 (fun τ => α τ x i) 0 := by
    intro x i
    rw [hαdef, twoFormMotion_eq_clm]
    exact (twoFormMotionCLM a₀ a₁ X₀ X₁ x i).contDiff.contDiffAt
  have hα0 : ∀ x i, α 0 x i = 0 := by
    intro x i
    simp [hαdef, twoFormMotion]
  have e0 : (![0] : Fin 1 → Fin 2) = fun _ => 0 := by
    funext m
    fin_cases m
    rfl
  have e1 : (![1] : Fin 1 → Fin 2) = fun _ => 1 := by
    funext m
    fin_cases m
    rfl
  have hp0 : ∀ x i, motionComponent α ![0] x i = a₀ x i • X₀ := by
    intro x i
    rw [e0, hαdef, motionComponent_twoFormMotion]
    simp [twoFormMotionCLM]
  have hp1 : ∀ x i, motionComponent α ![1] x i = a₁ x i • X₁ := by
    intro x i
    rw [e1, hαdef, motionComponent_twoFormMotion]
    simp [twoFormMotionCLM]
  obtain ⟨Aq, hAq, hAb⟩ := motionComponent_bounded hper α
  obtain ⟨Bn, hBn, hBb⟩ := gaugeForms_bounded hper ψ
  obtain ⟨M, hM, hall⟩ := hG 3 Aq Bn hAq hBn
  obtain ⟨α', h0', hC', hev, hp', -⟩ := hall F j 2 (uniformField F j) α ψ (fun _ _ _ => 1) hper hα0 hαC
    (fun _ _ _ => zero_le_one) (fun _ _ _ => le_rfl) (fun q e x i l _ => by rw [mul_one]; exact hAb q e x i)
    (fun x i l => ⟨by rw [mul_one]; exact hBb x l, by rw [mul_one]; exact hBb _ l⟩)
  have h1 : ∀ (c : Fin 1 → F.Site j × Fin 4) (X : Fin 1 → imaginaryQuaternions), AreUnitVectors X →
      bondDeriv G (uniformField F j) c X = 0 :=
    fun c X hX => hN F j G s c X hs hinv hX
  have hq0 : ∀ x i, motionComponent α' ![0] x i = (a₀ x i + (φ₀ x - φ₀ (x + unitStep j i))) • X₀ := by
    intro x i
    rw [e0, hp' (by norm_num) 0 x i, hαdef, motionComponent_twoFormMotion]
    simp [twoFormMotionCLM, hψdef, twoGaugeForms, uniformField, adjointAction_one, add_smul, sub_smul]
    abel
  have hq1 : ∀ x i, motionComponent α' ![1] x i = (a₁ x i + (φ₁ x - φ₁ (x + unitStep j i))) • X₁ := by
    intro x i
    rw [e1, hp' (by norm_num) 1 x i, hαdef, motionComponent_twoFormMotion]
    simp [twoFormMotionCLM, hψdef, twoGaugeForms, uniformField, adjointAction_one, add_smul, sub_smul]
    abel
  have I1 := hS F j T G (uniformField F j) α' _ _ X₀ X₁ hT hsm h1 h0' hC' hq0 hq1
  have I2 := hS F j T G (uniformField F j) α a₀ a₁ X₀ X₁ hT hsm h1 hα0 hαC hp0 hp1
  set A₀ : ℝ := ∑ b ∈ T, |a₀ b.1 b.2| with hA₀
  set A₁ : ℝ := ∑ b ∈ T, |a₁ b.1 b.2| with hA₁
  have hA₀n : 0 ≤ A₀ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hA₁n : 0 ≤ A₁ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have ha₀ : ∀ x i, |a₀ x i| ≤ A₀ := fun x i =>
    Finset.single_le_sum (f := fun b : F.Site j × Fin 4 => |a₀ b.1 b.2|) (fun _ _ => abs_nonneg _) (hT (x, i))
  have ha₁ : ∀ x i, |a₁ x i| ≤ A₁ := fun x i =>
    Finset.single_le_sum (f := fun b : F.Site j × Fin 4 => |a₁ b.1 b.2|) (fun _ _ => abs_nonneg _) (hT (x, i))
  set C : ℝ := 1 + A₀ + A₁ with hC
  have hCpos : 0 < C := by positivity
  have hball : Metric.ball (0 : Fin 2 → ℝ) (s / (8 * C)) ∈ 𝓝 (0 : Fin 2 → ℝ) :=
    Metric.ball_mem_nhds _ (by positivity)
  have hevG : (fun τ => G (leftTranslate (α' τ) (uniformField F j))) =ᶠ[𝓝 0]
      fun τ => G (leftTranslate (α τ) (uniformField F j)) := by
    filter_upwards [hev, hball] with τ hτ hb
    have hτn : ‖τ‖ < s / (8 * C) := by simpa using hb
    have hτl : ∀ l, |τ l| ≤ s / (8 * C) := by
      intro l
      have h2 : ‖τ l‖ ≤ ‖τ‖ := norm_le_pi_norm τ l
      rw [Real.norm_eq_abs] at h2
      linarith
    have hcold : IsSmallCurvature s (leftTranslate (α τ) (uniformField F j)) := by
      refine isSmallCurvature_leftTranslate_uniform _ (ε := s / 8 * ((A₀ + A₁) / C)) (fun x i => ?_) ?_
      · have h3 : ‖α τ x i‖ ≤ |τ 0 * a₀ x i| + |τ 1 * a₁ x i| := by
          show ‖(τ 0 * a₀ x i) • X₀ + (τ 1 * a₁ x i) • X₁‖ ≤ _
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, hX₀, hX₁, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
        refine h3.trans ?_
        rw [abs_mul, abs_mul]
        have h4 : |τ 0| * |a₀ x i| ≤ s / (8 * C) * A₀ :=
          mul_le_mul (hτl 0) (ha₀ x i) (abs_nonneg _) (by positivity)
        have h5 : |τ 1| * |a₁ x i| ≤ s / (8 * C) * A₁ :=
          mul_le_mul (hτl 1) (ha₁ x i) (abs_nonneg _) (by positivity)
        have h6 : s / 8 * ((A₀ + A₁) / C) = s / (8 * C) * A₀ + s / (8 * C) * A₁ := by
          field_simp
        linarith
      · have h7 : (A₀ + A₁) / C ≤ 1 := by
          rw [div_le_one hCpos, hC]
          linarith
        nlinarith
    show G _ = G _
    rw [← hτ, hinv _ _ hcold]
  have e3 : iteratedFDeriv ℝ 2 (fun τ => G (leftTranslate (α' τ) (uniformField F j))) 0 =
      iteratedFDeriv ℝ 2 (fun τ => G (leftTranslate (α τ) (uniformField F j))) 0 :=
    (Filter.EventuallyEq.iteratedFDeriv ℝ hevG 2).eq_of_nhds
  rw [← I2, ← e3, I1]
end YangMills.Construction.ColdStepAtMirrorFrames
end
