import YangMills.Construction.Continuum.FunctionsNormsBallsAndNeighbourhoods
import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.LawOnABoxOfTheFlow.DecayOfASymbolProof
import YangMills.Construction.FormsOnATorus.BoundsOfTheSymbol
import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormDefs
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
import YangMills.Construction.FormsOnATorus.OrdersOfTheInverseSymbol
import YangMills.Construction.LawOnABoxOfTheFlow.DecayOfASymbol
set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.LimitForms
open WeightedResponses
def greenColumnStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb _ => ∀ c₁ C₁ : ℝ, 0 < c₁ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (Q : IntBond → IntBond → ℝ),
    IsLimitForm Tb.coupling Tb.coercivity c₁ C₁ Tb.side k Q → ∀ r s : Fin 4, r < s → ∃ B : IntBond → ℝ,
      (∀ b : IntBond, HasSum (fun b' => Q b b' * B b') (intCurl (Pi.single b 1) (0, r, s))) ∧
      (∀ b : IntBond, |B b| ≤ C * ((1 + Real.sqrt (intNormSq b.1)) ^ 3)⁻¹) ∧
      ∀ (z : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν →
        |intCurl B (z, μ, ν)| ≤ C * ((1 + Real.sqrt (intNormSq z)) ^ 4)⁻¹ ∧
        (z ≠ 0 → |intCurl B (z, μ, ν) - maxwellKernel z μ ν r s| ≤
          C * ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹)
end YangMills.Construction.LimitForms
end

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.LimitForms
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
private def HasScaledJet (f : ℝ → ℂ) (t₀ ρ : ℝ) (m : ℤ) (B : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, ContDiffAt ℝ d f t₀ ∧ ‖iteratedDeriv d f t₀‖ ≤ B d * ρ ^ (m - (d : ℤ))
private theorem HasScaledJet.add {f g : ℝ → ℂ} {t₀ ρ : ℝ} {m : ℤ} {B B' : ℕ → ℝ} (hf : HasScaledJet f t₀ ρ m B) (hg : HasScaledJet g t₀ ρ m B') :
    HasScaledJet (fun t => f t + g t) t₀ ρ m (fun d => B d + B' d) := by
  intro d
  refine ⟨(hf d).1.add (hg d).1, ?_⟩
  have : iteratedDeriv d (fun t => f t + g t) t₀ = iteratedDeriv d f t₀ + iteratedDeriv d g t₀ :=
    iteratedDeriv_add (hf d).1 (hg d).1
  rw [this, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hf d).2 (hg d).2)
private theorem HasScaledJet.neg {f : ℝ → ℂ} {t₀ ρ : ℝ} {m : ℤ} {B : ℕ → ℝ} (hf : HasScaledJet f t₀ ρ m B) :
    HasScaledJet (fun t => -f t) t₀ ρ m B := by
  intro d
  refine ⟨(hf d).1.neg, ?_⟩
  have : iteratedDeriv d (fun t => -f t) t₀ = -iteratedDeriv d f t₀ := by
    simpa using iteratedDeriv_neg d f t₀
  rw [this, norm_neg]
  exact (hf d).2
private def binomialConv (B B' : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * B i * B' (d - i)
private theorem HasScaledJet.mul {f g : ℝ → ℂ} {t₀ ρ : ℝ} {m m' : ℤ} {B B' : ℕ → ℝ} (hρ : 0 < ρ)
    (hf : HasScaledJet f t₀ ρ m B) (hg : HasScaledJet g t₀ ρ m' B') :
    HasScaledJet (fun t => f t * g t) t₀ ρ (m + m') (binomialConv B B') := by
  intro d
  refine ⟨(hf d).1.mul (hg d).1, ?_⟩
  have e : iteratedDeriv d (fun t => f t * g t) t₀ =
      ∑ i ∈ Finset.range (d + 1), (d.choose i : ℂ) * iteratedDeriv i f t₀ * iteratedDeriv (d - i) g t₀ :=
    iteratedDeriv_mul (hf d).1 (hg d).1
  rw [e, binomialConv, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  have h1 := (hf i).2
  have h2 := (hg (d - i)).2
  have h3 : ρ ^ (m + m' - (d : ℤ)) = ρ ^ (m - (i : ℤ)) * ρ ^ (m' - ((d - i : ℕ) : ℤ)) := by
    rw [← zpow_add₀ hρ.ne']
    congr 1
    have : ((d - i : ℕ) : ℤ) = d - i := by omega
    omega
  rw [h3]
  have h4 := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  calc (d.choose i : ℝ) * ‖iteratedDeriv i f t₀‖ * ‖iteratedDeriv (d - i) g t₀‖
      = (d.choose i : ℝ) * (‖iteratedDeriv i f t₀‖ * ‖iteratedDeriv (d - i) g t₀‖) := by ring
    _ ≤ (d.choose i : ℝ) * (B i * ρ ^ (m - (i : ℤ)) * (B' (d - i) * ρ ^ (m' - ((d - i : ℕ) : ℤ)))) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring
private theorem HasScaledJet.congr {f g : ℝ → ℂ} {t₀ ρ : ℝ} {m : ℤ} {B : ℕ → ℝ} (hf : HasScaledJet f t₀ ρ m B)
    (h : g = f) : HasScaledJet g t₀ ρ m B := by
  rw [h]
  exact hf
private theorem HasScaledJet.zero {t₀ ρ : ℝ} {m : ℤ} {B : ℕ → ℝ} (hρ : 0 < ρ) (hB : ∀ d, 0 ≤ B d) :
    HasScaledJet (fun _ => 0) t₀ ρ m B := by
  intro d
  refine ⟨contDiffAt_const, ?_⟩
  rw [iteratedDeriv_const]
  have := zpow_pos hρ (m - (d : ℤ))
  have h2 := hB d
  split_ifs <;> simp <;> positivity
private theorem one_le_seven_pow_mul_inv {ρ : ℝ} (hρ : 0 < ρ) (hρ7 : ρ ≤ 7) (k : ℕ) : 1 ≤ 7 ^ k * (ρ ^ k)⁻¹ := by
  have h1 : ρ ^ k ≤ 7 ^ k := pow_le_pow_left₀ hρ.le hρ7 k
  have h2 : 0 < ρ ^ k := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ h2]
  linarith
abbrev _root_.YangMills.SharedProofs.p22065 := @one_le_seven_pow_mul_inv
private def halfAngleTrig (b c t : ℝ) : ℂ := ((b * Real.cos (t / 2) + c * Real.sin (t / 2) : ℝ) : ℂ)
private theorem hasDerivAt_halfAngleTrig (b c t : ℝ) : HasDerivAt (halfAngleTrig b c) (halfAngleTrig (c / 2) (-b / 2) t) t := by
  have h0 : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) t := by simpa using (hasDerivAt_id t).div_const 2
  have h1 : HasDerivAt (fun t : ℝ => b * Real.cos (t / 2) + c * Real.sin (t / 2))
      (c / 2 * Real.cos (t / 2) + -b / 2 * Real.sin (t / 2)) t := by
    have := ((Real.hasDerivAt_cos (t / 2)).comp t h0 |>.const_mul b).add ((Real.hasDerivAt_sin (t / 2)).comp t h0 |>.const_mul c)
    refine this.congr_deriv ?_
    ring
  exact h1.ofReal_comp
private theorem contDiff_halfAngleTrig (b c : ℝ) : ContDiff ℝ ⊤ (halfAngleTrig b c) := by
  unfold halfAngleTrig
  have h0 : ContDiff ℝ ⊤ (fun t : ℝ => t / 2) := contDiff_id.div_const 2
  exact Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul (Real.contDiff_cos.comp h0)).add
    (contDiff_const.mul (Real.contDiff_sin.comp h0)))
private theorem norm_halfAngleTrig_le (b c t : ℝ) : ‖halfAngleTrig b c t‖ ≤ |b| + |c| := by
  simp only [halfAngleTrig, Complex.norm_real, Real.norm_eq_abs]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
private theorem iteratedDeriv_halfAngleTrig (d : ℕ) : ∀ b c : ℝ, ∃ b' c' : ℝ, |b'| + |c'| ≤ |b| + |c| ∧ iteratedDeriv d (halfAngleTrig b c) = halfAngleTrig b' c' := by
  induction d with
  | zero => exact fun b c => ⟨b, c, le_refl _, by simp⟩
  | succ d ih =>
    intro b c
    obtain ⟨b', c', h1, h2⟩ := ih (c / 2) (-b / 2)
    refine ⟨b', c', ?_, ?_⟩
    · refine h1.trans ?_
      rw [abs_div, abs_div, abs_neg]
      simp only [abs_two]
      linarith [abs_nonneg b, abs_nonneg c]
    · rw [iteratedDeriv_succ']
      have : deriv (halfAngleTrig b c) = halfAngleTrig (c / 2) (-b / 2) := funext fun t => (hasDerivAt_halfAngleTrig b c t).deriv
      rw [this, h2]
private theorem sqrt_momentumNormSq_le_seven {p : Fin 4 → ℝ} (hp : p ∈ brillouinBox) : Real.sqrt (momentumNormSq p) ≤ 7 := by
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have h1 : ∀ l, p l ^ 2 ≤ Real.pi ^ 2 := fun l => by
    have := abs_le.2 ⟨hp.1 l, hp.2 l⟩
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have h2 : momentumNormSq p ≤ 4 * Real.pi ^ 2 := by
    simp only [momentumNormSq, Fin.sum_univ_four]
    linarith [h1 0, h1 1, h1 2, h1 3]
  apply Real.sqrt_le_iff.2
  constructor
  · norm_num
  · nlinarith
abbrev _root_.YangMills.SharedProofs.p34260 := @sqrt_momentumNormSq_le_seven
private theorem sqrt_momentumNormSq_pos {p : Fin 4 → ℝ} (hp : p ≠ 0) : 0 < Real.sqrt (momentumNormSq p) := by apply _root_.YangMills.Construction.TorusTransport.euclidNormVec_pos <;> assumption
abbrev _root_.YangMills.SharedProofs.p65178 := @sqrt_momentumNormSq_pos
private theorem abs_coord_le_sqrt_momentumNormSq (p : Fin 4 → ℝ) (l : Fin 4) : |p l| ≤ Real.sqrt (momentumNormSq p) := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem abs_two_mul_sin_half_le (x : ℝ) : |2 * Real.sin (x / 2)| ≤ |x| := by
  rw [abs_mul]
  simp only [abs_two]
  have := Real.abs_sin_le_abs (x := x / 2)
  rw [abs_div] at this
  simp only [abs_two] at this
  linarith
abbrev _root_.YangMills.SharedProofs.p15114 := @abs_two_mul_sin_half_le
private def sineAlongAxis (p : Fin 4 → ℝ) (l j : Fin 4) (t : ℝ) : ℂ := (latticeSine (Function.update p l t) j : ℂ)
private theorem hasScaledJet_sineAlongAxis {p : Fin 4 → ℝ} (l j : Fin 4) (hp : p ∈ brillouinBox) (hp0 : p ≠ 0) :
    HasScaledJet (sineAlongAxis p l j) (p l) (Real.sqrt (momentumNormSq p)) 1 (fun d => 3 * 7 ^ d) := by
  have hρ := sqrt_momentumNormSq_pos hp0
  have hρ7 := sqrt_momentumNormSq_le_seven hp
  set ρ := Real.sqrt (momentumNormSq p) with hρd
  have h0 : ‖sineAlongAxis p l j (p l)‖ ≤ 3 * ρ := by
    simp only [sineAlongAxis, Function.update_eq_self, Complex.norm_real, Real.norm_eq_abs, latticeSine]
    have h1 := (abs_two_mul_sin_half_le (p j)).trans (abs_coord_le_sqrt_momentumNormSq p j)
    linarith
  by_cases hj : j = l
  · subst hj
    have he : sineAlongAxis p j j = halfAngleTrig 0 2 := by
      funext t
      simp [sineAlongAxis, latticeSine, halfAngleTrig]
    rw [he] at h0 ⊢
    intro d
    refine ⟨(contDiff_halfAngleTrig 0 2).contDiffAt.of_le (by exact_mod_cast le_top), ?_⟩
    obtain ⟨b', c', h1, h2⟩ := iteratedDeriv_halfAngleTrig d 0 2
    have hb : ‖iteratedDeriv d (halfAngleTrig 0 2) (p j)‖ ≤ 2 := by
      rw [h2]
      refine (norm_halfAngleTrig_le _ _ _).trans (h1.trans ?_)
      simp
    match d with
    | 0 =>
      simpa using h0
    | 1 =>
      have e : ρ ^ ((1 : ℤ) - ((1 : ℕ) : ℤ)) = 1 := by norm_num
      rw [e]
      norm_num
      norm_num at hb
      linarith
    | k + 2 =>
      have e : ρ ^ ((1 : ℤ) - ((k + 2 : ℕ) : ℤ)) = (ρ ^ (k + 1))⁻¹ := by
        have : ((1 : ℤ) - ((k + 2 : ℕ) : ℤ)) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [this, zpow_neg, zpow_natCast]
      rw [e]
      refine hb.trans ?_
      have h2' := one_le_seven_pow_mul_inv hρ hρ7 (k + 1)
      have h5 : (7 : ℝ) ^ (k + 1) ≤ 7 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h6 : 0 ≤ (ρ ^ (k + 1))⁻¹ := by positivity
      have h7 := mul_le_mul_of_nonneg_right h5 h6
      nlinarith
  · have he : sineAlongAxis p l j = fun _ => ((latticeSine p j : ℝ) : ℂ) := by
      funext t
      simp [sineAlongAxis, latticeSine, Function.update_of_ne hj]
    rw [he] at h0 ⊢
    intro d
    refine ⟨contDiffAt_const, ?_⟩
    match d with
    | 0 =>
      simpa using h0
    | k + 1 =>
      rw [iteratedDeriv_const]
      have := zpow_pos hρ ((1 : ℤ) - ((k + 1 : ℕ) : ℤ))
      simp
      positivity
private theorem HasScaledJet.sum_fin_four {f : Fin 4 → ℝ → ℂ} {t₀ ρ : ℝ} {m : ℤ} {B : ℕ → ℝ} (hf : ∀ k, HasScaledJet (f k) t₀ ρ m B) :
    HasScaledJet (fun t => ∑ k, f k t) t₀ ρ m (fun d => B d + B d + B d + B d) := by
  have h := (((hf 0).add (hf 1)).add (hf 2)).add (hf 3)
  refine HasScaledJet.congr h ?_
  funext t
  rw [Fin.sum_univ_four]
private theorem HasScaledJet.I_mul {f : ℝ → ℂ} {t₀ ρ : ℝ} {m : ℤ} {B : ℕ → ℝ} (hf : HasScaledJet f t₀ ρ m B) :
    HasScaledJet (fun t => Complex.I * f t) t₀ ρ m B := by
  intro d
  refine ⟨contDiffAt_const.mul (hf d).1, ?_⟩
  have e : iteratedDeriv d (fun t => Complex.I * f t) t₀ = Complex.I * iteratedDeriv d f t₀ := by
    have h := iteratedDeriv_mul (n := d) (x := t₀) (f := fun _ : ℝ => Complex.I) (g := f) contDiffAt_const (hf d).1
    have h2 : iteratedDeriv d ((fun _ : ℝ => Complex.I) * f) t₀ = iteratedDeriv d (fun t => Complex.I * f t) t₀ := rfl
    rw [← h2, h, Finset.sum_range_succ']
    have hz : ∀ k ∈ Finset.range d, ((d.choose (k + 1) : ℕ) : ℂ) * iteratedDeriv (k + 1) (fun _ : ℝ => Complex.I) t₀ *
        iteratedDeriv (d - (k + 1)) f t₀ = 0 := by
      intro k _
      rw [iteratedDeriv_const]
      simp
    rw [Finset.sum_eq_zero hz]
    simp
  rw [e, norm_mul, Complex.norm_I, one_mul]
  exact (hf d).2
private def planeSineAlongAxis (p : Fin 4 → ℝ) (l m n' i : Fin 4) (t : ℝ) : ℂ := (planeSineVector (Function.update p l t) m n' i : ℂ)
private theorem hasScaledJet_planeSineAlongAxis {p : Fin 4 → ℝ} (l m n' i : Fin 4) (hp : p ∈ brillouinBox) (hp0 : p ≠ 0) :
    HasScaledJet (planeSineAlongAxis p l m n' i) (p l) (Real.sqrt (momentumNormSq p)) 1 (fun d => 3 * 7 ^ d + 3 * 7 ^ d) := by
  have hρ := sqrt_momentumNormSq_pos hp0
  have hB : ∀ d : ℕ, (0 : ℝ) ≤ 3 * 7 ^ d := fun d => by positivity
  have h1 : HasScaledJet (fun t => if i = m then sineAlongAxis p l n' t else 0) (p l) (Real.sqrt (momentumNormSq p)) 1 (fun d => 3 * 7 ^ d) := by
    by_cases h : i = m
    · simpa [h] using hasScaledJet_sineAlongAxis l n' hp hp0
    · simpa [h] using HasScaledJet.zero hρ hB
  have h2 : HasScaledJet (fun t => if i = n' then sineAlongAxis p l m t else 0) (p l) (Real.sqrt (momentumNormSq p)) 1 (fun d => 3 * 7 ^ d) := by
    by_cases h : i = n'
    · simpa [h] using hasScaledJet_sineAlongAxis l m hp hp0
    · simpa [h] using HasScaledJet.zero hρ hB
  refine HasScaledJet.congr (h1.add h2.neg) ?_
  funext t
  simp only [planeSineAlongAxis, planeSineVector, sineAlongAxis]
  push_cast
  split_ifs <;> simp [sub_eq_add_neg]
private theorem hasScaledJet_sandwich {G : Fin 4 → Fin 4 → ℝ → ℂ} {p : Fin 4 → ℝ} {l m n' r s : Fin 4} {e : ℤ} {B : ℕ → ℝ}
    (hp : p ∈ brillouinBox) (hp0 : p ≠ 0)
    (hG : ∀ i j, HasScaledJet (G i j) (p l) (Real.sqrt (momentumNormSq p)) e B) :
    HasScaledJet (fun t => ∑ i, ∑ j, planeSineAlongAxis p l m n' i t * (G i j t * planeSineAlongAxis p l r s j t)) (p l) (Real.sqrt (momentumNormSq p)) (1 + (e + 1))
      (fun d => (fun d => (fun d => binomialConv (fun d => 3 * 7 ^ d + 3 * 7 ^ d) (binomialConv B (fun d => 3 * 7 ^ d + 3 * 7 ^ d)) d +
        binomialConv (fun d => 3 * 7 ^ d + 3 * 7 ^ d) (binomialConv B (fun d => 3 * 7 ^ d + 3 * 7 ^ d)) d +
        binomialConv (fun d => 3 * 7 ^ d + 3 * 7 ^ d) (binomialConv B (fun d => 3 * 7 ^ d + 3 * 7 ^ d)) d +
        binomialConv (fun d => 3 * 7 ^ d + 3 * 7 ^ d) (binomialConv B (fun d => 3 * 7 ^ d + 3 * 7 ^ d)) d) d) d +
        (fun d => (fun d => binomialConv (fun d => 3 * 7 ^ d + 3 * 7 ^ d) (binomialConv B (fun d => 3 * 7 ^ d + 3 * 7 ^ d)) d +
        binomialConv (fun d => 3 * 7 ^ d + 3 * 7 ^ d) (binomialConv B (fun d => 3 * 7 ^ d + 3 * 7 ^ d)) d +
        binomialConv (fun d => 3 * 7 ^ d + 3 * 7 ^ d) (binomialConv B (fun d => 3 * 7 ^ d + 3 * 7 ^ d)) d +
        binomialConv (fun d => 3 * 7 ^ d + 3 * 7 ^ d) (binomialConv B (fun d => 3 * 7 ^ d + 3 * 7 ^ d)) d) d) d +
        (fun d => (fun d => binomialConv (fun d => 3 * 7 ^ d + 3 * 7 ^ d) (binomialConv B (fun d => 3 * 7 ^ d + 3 * 7 ^ d)) d +
        binomialConv (fun d => 3 * 7 ^ d + 3 * 7 ^ d) (binomialConv B (fun d => 3 * 7 ^ d + 3 * 7 ^ d)) d +
        binomialConv (fun d => 3 * 7 ^ d + 3 * 7 ^ d) (binomialConv B (fun d => 3 * 7 ^ d + 3 * 7 ^ d)) d +
        binomialConv (fun d => 3 * 7 ^ d + 3 * 7 ^ d) (binomialConv B (fun d => 3 * 7 ^ d + 3 * 7 ^ d)) d) d) d +
        (fun d => (fun d => binomialConv (fun d => 3 * 7 ^ d + 3 * 7 ^ d) (binomialConv B (fun d => 3 * 7 ^ d + 3 * 7 ^ d)) d +
        binomialConv (fun d => 3 * 7 ^ d + 3 * 7 ^ d) (binomialConv B (fun d => 3 * 7 ^ d + 3 * 7 ^ d)) d +
        binomialConv (fun d => 3 * 7 ^ d + 3 * 7 ^ d) (binomialConv B (fun d => 3 * 7 ^ d + 3 * 7 ^ d)) d +
        binomialConv (fun d => 3 * 7 ^ d + 3 * 7 ^ d) (binomialConv B (fun d => 3 * 7 ^ d + 3 * 7 ^ d)) d) d) d) := by
  have hρ := sqrt_momentumNormSq_pos hp0
  exact HasScaledJet.sum_fin_four fun i => HasScaledJet.sum_fin_four fun j =>
    (hasScaledJet_planeSineAlongAxis l m n' i hp hp0).mul hρ ((hG i j).mul hρ (hasScaledJet_planeSineAlongAxis l r s j hp hp0))
private def axisSign (l a : Fin 4) : ℝ := if a = l then -1 else 1
private theorem axisSign_mul_self (l a : Fin 4) : axisSign l a * axisSign l a = 1 := by
  simp only [axisSign]
  split_ifs <;> norm_num
private theorem exp_I_mul_axisSign (l a : Fin 4) :
    Complex.exp (Complex.I * (((if l = a then Real.pi else 0 : ℝ)) : ℂ)) = (axisSign l a : ℂ) := by
  by_cases h : l = a
  · subst h
    simp only [if_true, axisSign]
    rw [mul_comm, Complex.exp_pi_mul_I]
    simp
  · have h' : a ≠ l := fun e => h e.symm
    simp [h, axisSign, h']
private theorem exp_I_mul_two_pi_int (x : ℤ) : Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) = 1 := by
  have := Complex.exp_int_mul_two_pi_mul_I x
  rw [← this]
  congr 1
  push_cast
  ring
private theorem latticeSine_add_period (p : Fin 4 → ℝ) (l j : Fin 4) :
    latticeSine (p + Pi.single l (2 * Real.pi)) j = axisSign l j * latticeSine p j := by
  by_cases h : j = l
  · subst h
    have e : (p + Pi.single j (2 * Real.pi) : Fin 4 → ℝ) j / 2 = p j / 2 + Real.pi := by simp; ring
    simp only [latticeSine, axisSign, if_true]
    rw [e, Real.sin_add_pi]
    ring
  · simp [latticeSine, axisSign, h, Pi.single_eq_of_ne h]
abbrev _root_.YangMills.DeltaSharedProofs.p501879 := @latticeSine_add_period
private theorem planeSineVector_add_period (p : Fin 4 → ℝ) (l m n' i : Fin 4) (hmn : m ≠ n') :
    planeSineVector (p + Pi.single l (2 * Real.pi)) m n' i = axisSign l m * axisSign l n' * axisSign l i * planeSineVector p m n' i := by
  simp only [planeSineVector, latticeSine_add_period]
  by_cases h1 : i = m
  · subst h1
    simp only [if_true, if_neg hmn, sub_zero]
    have := axisSign_mul_self l i
    calc axisSign l n' * latticeSine p n' = (axisSign l i * axisSign l i) * axisSign l n' * latticeSine p n' := by rw [this]; ring
      _ = _ := by ring
  · by_cases h2 : i = n'
    · subst h2
      simp only [if_true, if_neg h1, zero_sub]
      have := axisSign_mul_self l i
      calc -(axisSign l m * latticeSine p m) = -((axisSign l i * axisSign l i) * axisSign l m * latticeSine p m) := by rw [this]; ring
        _ = _ := by ring
    · simp [h1, h2]
private theorem midpointSymbol_add_period (Q : IntBond → IntBond → ℝ) (l a b : Fin 4) (p : Fin 4 → ℝ) :
    midpointSymbol Q a b (p + Pi.single l (2 * Real.pi)) = (axisSign l a * axisSign l b : ℝ) * midpointSymbol Q a b p := by
  simp only [midpointSymbol]
  rw [← tsum_mul_left]
  refine tsum_congr fun z => ?_
  set y : Fin 4 → ℝ := fun l' => (z l' : ℝ) + (if l' = b then 1 / 2 else 0) - (if l' = a then 1 / 2 else 0) with hy
  have e1 : (∑ l', (p + Pi.single l (2 * Real.pi) : Fin 4 → ℝ) l' * y l') = (∑ l', p l' * y l') + 2 * Real.pi * y l := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single l]
    · simp
    · intro l' _ h
      simp [Pi.single_eq_of_ne h]
    · simp
  have e2 : Complex.exp (Complex.I * ((2 * Real.pi * y l : ℝ) : ℂ)) = (axisSign l a * axisSign l b : ℝ) := by
    have e3 : 2 * Real.pi * y l = 2 * Real.pi * (z l : ℝ) + (if l = b then Real.pi else 0) - (if l = a then Real.pi else 0) := by
      simp only [hy]
      split_ifs <;> ring
    rw [e3]
    push_cast
    rw [mul_sub, mul_add, Complex.exp_sub, Complex.exp_add]
    have x1 := exp_I_mul_two_pi_int (z l)
    push_cast at x1
    rw [x1, one_mul]
    have x2 := exp_I_mul_axisSign l b
    have x3 := exp_I_mul_axisSign l a
    push_cast at x2 x3
    rw [x2, x3]
    have h1 : ((axisSign l a : ℝ) : ℂ) * (axisSign l a : ℝ) = 1 := by exact_mod_cast axisSign_mul_self l a
    have h2 : ((axisSign l a : ℝ) : ℂ) ≠ 0 := fun h => by simp [h] at h1
    field_simp
    rw [show ((axisSign l a : ℝ) : ℂ) ^ 2 = ((axisSign l a : ℝ) : ℂ) * (axisSign l a : ℝ) by ring, h1]
    simp
  show _ = _ * (_ * Complex.exp (Complex.I * ((∑ l', p l' * y l' : ℝ) : ℂ)))
  rw [e1, Complex.ofReal_add, mul_add, Complex.exp_add, e2]
  ring
private theorem inv_momentumSymbolMatrix_add_period (Q : IntBond → IntBond → ℝ) (l a b : Fin 4) (p : Fin 4 → ℝ) :
    (momentumSymbolMatrix Q (p + Pi.single l (2 * Real.pi)))⁻¹ a b = (axisSign l a * axisSign l b : ℝ) * (momentumSymbolMatrix Q p)⁻¹ a b := by
  set D : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal fun k => ((axisSign l k : ℝ) : ℂ) with hD
  have hDD : D * D = 1 := by
    rw [hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact_mod_cast axisSign_mul_self l k
  have hDi : D⁻¹ = D := Matrix.inv_eq_right_inv hDD
  have hM : momentumSymbolMatrix Q (p + Pi.single l (2 * Real.pi)) = D * momentumSymbolMatrix Q p * D := by
    ext i j
    rw [hD, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [momentumSymbolMatrix, midpointSymbol_add_period]
    push_cast
    ring
  rw [hM, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hDi, hD, ← Matrix.mul_assoc, Matrix.mul_diagonal, Matrix.diagonal_mul]
  push_cast
  ring
private def InverseSymbolOrders (Cs : ℕ → ℝ) (Q : IntBond → IntBond → ℝ) : Prop :=
  ∀ (i j : Fin 4) (p : Fin 4 → ℝ), p ∈ brillouinBox → p ≠ 0 →
      IsUnit (momentumSymbolMatrix Q p).det ∧
      (∀ d : ℕ, ContDiffAt ℝ d (fun q => (momentumSymbolMatrix Q q)⁻¹ i j) p) ∧
      ∀ (l : Fin 4) (d : ℕ),
        ‖iteratedDeriv d (fun t : ℝ => (momentumSymbolMatrix Q (Function.update p l t))⁻¹ i j) (p l)‖ ≤
          Cs d * Real.sqrt (momentumNormSq p) ^ (-2 - (d : ℤ)) ∧
        ‖iteratedDeriv d (fun t : ℝ => inverseSymbolDefect Q i j (Function.update p l t)) (p l)‖ ≤
          Cs d * Real.sqrt (momentumNormSq p) ^ (-1 - (d : ℤ))
private def columnSymbol (Q : IntBond → IntBond → ℝ) (r s i : Fin 4) (p : Fin 4 → ℝ) : ℂ :=
  Complex.I * ∑ j, (momentumSymbolMatrix Q p)⁻¹ i j * (planeSineVector p r s j : ℂ)
private def curlColumnSymbol (Q : IntBond → IntBond → ℝ) (m n' r s : Fin 4) (p : Fin 4 → ℝ) : ℂ :=
  ∑ i, ∑ j, (planeSineVector p m n' i : ℂ) * ((momentumSymbolMatrix Q p)⁻¹ i j * (planeSineVector p r s j : ℂ))
private def defectSandwich (Q : IntBond → IntBond → ℝ) (m n' r s : Fin 4) (p : Fin 4 → ℝ) : ℂ :=
  ∑ i, ∑ j, (planeSineVector p m n' i : ℂ) * (inverseSymbolDefect Q i j p * (planeSineVector p r s j : ℂ))
private theorem contDiffAt_along_axis {f : (Fin 4 → ℝ) → ℂ} {p : Fin 4 → ℝ} {d : ℕ} (l : Fin 4) (h : ContDiffAt ℝ d f p) :
    ContDiffAt ℝ d (fun t : ℝ => f (Function.update p l t)) (p l) := by
  have h2 : ContDiffAt ℝ d (fun t : ℝ => Function.update p l t) (p l) := (contDiff_update d p l).contDiffAt
  have h1 : ContDiffAt ℝ d f (Function.update p l (p l)) := by simpa using h
  exact h1.comp (p l) h2
private theorem contDiff_latticeSine (l : Fin 4) : ContDiff ℝ ⊤ (fun q : Fin 4 → ℝ => latticeSine q l) := by
  unfold latticeSine
  have h0 : ContDiff ℝ ⊤ (fun q : Fin 4 → ℝ => q l / 2) := (contDiff_apply ℝ ℝ l).div_const 2
  exact contDiff_const.mul (Real.contDiff_sin.comp h0)
private theorem contDiff_planeSineVector (m n' i : Fin 4) : ContDiff ℝ ⊤ (fun q : Fin 4 → ℝ => (planeSineVector q m n' i : ℂ)) := by
  have h0 : ContDiff ℝ ⊤ (fun q : Fin 4 → ℝ => planeSineVector q m n' i) := by
    unfold planeSineVector
    refine ContDiff.sub ?_ ?_
    · by_cases h : i = m
      · simpa [h] using contDiff_latticeSine n'
      · simpa [h] using contDiff_const
    · by_cases h : i = n'
      · simpa [h] using contDiff_latticeSine m
      · simpa [h] using contDiff_const
  exact Complex.ofRealCLM.contDiff.comp h0
private theorem contDiff_latticeSineNormSq : ContDiff ℝ ⊤ (fun q : Fin 4 → ℝ => (latticeSineNormSq q : ℂ)) := by
  have h0 : ContDiff ℝ ⊤ (fun q : Fin 4 → ℝ => latticeSineNormSq q) := by
    unfold latticeSineNormSq
    exact ContDiff.sum fun l _ => (contDiff_latticeSine l).pow 2
  exact Complex.ofRealCLM.contDiff.comp h0
private theorem latticeSineNormSq_ne_zero {p : Fin 4 → ℝ} (hp : p ∈ brillouinBox) (hp0 : p ≠ 0) : (latticeSineNormSq p : ℂ) ≠ 0 := by
  have hne : latticeSineNormSq p ≠ 0 := by
    intro h0
    apply hp0
    funext l
    have h1 : latticeSine p l ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h0 l (Finset.mem_univ l)
    have h2 : Real.sin (p l / 2) = 0 := by
      have := pow_eq_zero_iff (two_ne_zero) |>.1 h1
      simp only [latticeSine] at this
      linarith
    have hpi := Real.pi_pos
    have h3 := (Real.sin_eq_zero_iff_of_lt_of_lt (x := p l / 2) (by linarith [hp.1 l]) (by linarith [hp.2 l])).1 h2
    simp only [Pi.zero_apply]
    linarith
  exact_mod_cast hne
private theorem contDiffAt_inverseSymbolDefect {Cs : ℕ → ℝ} {Q : IntBond → IntBond → ℝ} (hO : InverseSymbolOrders Cs Q) (i j : Fin 4)
    {p : Fin 4 → ℝ} (hp : p ∈ brillouinBox) (hp0 : p ≠ 0) (d : ℕ) : ContDiffAt ℝ d (inverseSymbolDefect Q i j) p := by
  unfold inverseSymbolDefect
  refine ((hO i j p hp hp0).2.1 d).sub ?_
  by_cases h : i = j
  · simp only [h, if_true]
    exact (contDiff_latticeSineNormSq.contDiffAt.of_le (by exact_mod_cast le_top)).inv (latticeSineNormSq_ne_zero hp hp0)
  · simp only [h, if_false]
    exact contDiffAt_const
private theorem hasScaledJet_inverseSymbol {Cs : ℕ → ℝ} {Q : IntBond → IntBond → ℝ} (hO : InverseSymbolOrders Cs Q) (l i j : Fin 4)
    {p : Fin 4 → ℝ} (hp : p ∈ brillouinBox) (hp0 : p ≠ 0) :
    HasScaledJet (fun t => (momentumSymbolMatrix Q (Function.update p l t))⁻¹ i j) (p l) (Real.sqrt (momentumNormSq p)) (-2) Cs :=
  fun d => ⟨contDiffAt_along_axis l ((hO i j p hp hp0).2.1 d), ((hO i j p hp hp0).2.2 l d).1⟩
private theorem hasScaledJet_inverseSymbolDefect {Cs : ℕ → ℝ} {Q : IntBond → IntBond → ℝ} (hO : InverseSymbolOrders Cs Q) (l i j : Fin 4)
    {p : Fin 4 → ℝ} (hp : p ∈ brillouinBox) (hp0 : p ≠ 0) :
    HasScaledJet (fun t => inverseSymbolDefect Q i j (Function.update p l t)) (p l) (Real.sqrt (momentumNormSq p)) (-1) Cs :=
  fun d => ⟨contDiffAt_along_axis l (contDiffAt_inverseSymbolDefect hO i j hp hp0 d), ((hO i j p hp hp0).2.2 l d).2⟩
private def planeSineBounds : ℕ → ℝ := fun d => 3 * 7 ^ d + 3 * 7 ^ d
private def columnBounds (Cs : ℕ → ℝ) : ℕ → ℝ := fun d => binomialConv Cs planeSineBounds d + binomialConv Cs planeSineBounds d + binomialConv Cs planeSineBounds d + binomialConv Cs planeSineBounds d
private theorem hasScaledJet_columnSymbol {Cs : ℕ → ℝ} {Q : IntBond → IntBond → ℝ} (hO : InverseSymbolOrders Cs Q) (r s i l : Fin 4)
    {p : Fin 4 → ℝ} (hp : p ∈ brillouinBox) (hp0 : p ≠ 0) :
    HasScaledJet (fun t => columnSymbol Q r s i (Function.update p l t)) (p l) (Real.sqrt (momentumNormSq p)) (-1) (columnBounds Cs) := by
  have hρ := sqrt_momentumNormSq_pos hp0
  have h := (HasScaledJet.sum_fin_four fun j => (hasScaledJet_inverseSymbol hO l i j hp hp0).mul hρ (hasScaledJet_planeSineAlongAxis l r s j hp hp0)).I_mul
  exact h
private def sandwichBounds (B : ℕ → ℝ) : ℕ → ℝ := fun d =>
  (fun d => (fun d => binomialConv planeSineBounds (binomialConv B planeSineBounds) d + binomialConv planeSineBounds (binomialConv B planeSineBounds) d + binomialConv planeSineBounds (binomialConv B planeSineBounds) d + binomialConv planeSineBounds (binomialConv B planeSineBounds) d) d) d +
  (fun d => (fun d => binomialConv planeSineBounds (binomialConv B planeSineBounds) d + binomialConv planeSineBounds (binomialConv B planeSineBounds) d + binomialConv planeSineBounds (binomialConv B planeSineBounds) d + binomialConv planeSineBounds (binomialConv B planeSineBounds) d) d) d +
  (fun d => (fun d => binomialConv planeSineBounds (binomialConv B planeSineBounds) d + binomialConv planeSineBounds (binomialConv B planeSineBounds) d + binomialConv planeSineBounds (binomialConv B planeSineBounds) d + binomialConv planeSineBounds (binomialConv B planeSineBounds) d) d) d +
  (fun d => (fun d => binomialConv planeSineBounds (binomialConv B planeSineBounds) d + binomialConv planeSineBounds (binomialConv B planeSineBounds) d + binomialConv planeSineBounds (binomialConv B planeSineBounds) d + binomialConv planeSineBounds (binomialConv B planeSineBounds) d) d) d
private theorem hasScaledJet_curlColumnSymbol {Cs : ℕ → ℝ} {Q : IntBond → IntBond → ℝ} (hO : InverseSymbolOrders Cs Q) (m n' r s l : Fin 4)
    {p : Fin 4 → ℝ} (hp : p ∈ brillouinBox) (hp0 : p ≠ 0) :
    HasScaledJet (fun t => curlColumnSymbol Q m n' r s (Function.update p l t)) (p l) (Real.sqrt (momentumNormSq p)) 0 (sandwichBounds Cs) :=
  hasScaledJet_sandwich (m := m) (n' := n') (r := r) (s := s) hp hp0 fun i j => hasScaledJet_inverseSymbol hO l i j hp hp0
private theorem hasScaledJet_defectSandwich {Cs : ℕ → ℝ} {Q : IntBond → IntBond → ℝ} (hO : InverseSymbolOrders Cs Q) (m n' r s l : Fin 4)
    {p : Fin 4 → ℝ} (hp : p ∈ brillouinBox) (hp0 : p ≠ 0) :
    HasScaledJet (fun t => defectSandwich Q m n' r s (Function.update p l t)) (p l) (Real.sqrt (momentumNormSq p)) 1 (sandwichBounds Cs) :=
  hasScaledJet_sandwich (m := m) (n' := n') (r := r) (s := s) hp hp0 fun i j => hasScaledJet_inverseSymbolDefect hO l i j hp hp0
private theorem contDiffAt_columnSymbol {Cs : ℕ → ℝ} {Q : IntBond → IntBond → ℝ} (hO : InverseSymbolOrders Cs Q) (r s i : Fin 4)
    {p : Fin 4 → ℝ} (hp : p ∈ brillouinBox) (hp0 : p ≠ 0) (d : ℕ) : ContDiffAt ℝ d (columnSymbol Q r s i) p := by
  unfold columnSymbol
  refine contDiffAt_const.mul (ContDiffAt.sum fun j _ => ((hO i j p hp hp0).2.1 d).mul ?_)
  exact (contDiff_planeSineVector r s j).contDiffAt.of_le (by exact_mod_cast le_top)
private theorem contDiffAt_curlColumnSymbol {Cs : ℕ → ℝ} {Q : IntBond → IntBond → ℝ} (hO : InverseSymbolOrders Cs Q) (m n' r s : Fin 4)
    {p : Fin 4 → ℝ} (hp : p ∈ brillouinBox) (hp0 : p ≠ 0) (d : ℕ) : ContDiffAt ℝ d (curlColumnSymbol Q m n' r s) p := by
  unfold curlColumnSymbol
  refine ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => ?_
  exact ((contDiff_planeSineVector m n' i).contDiffAt.of_le (by exact_mod_cast le_top)).mul (((hO i j p hp hp0).2.1 d).mul
    ((contDiff_planeSineVector r s j).contDiffAt.of_le (by exact_mod_cast le_top)))
private theorem contDiffAt_defectSandwich {Cs : ℕ → ℝ} {Q : IntBond → IntBond → ℝ} (hO : InverseSymbolOrders Cs Q) (m n' r s : Fin 4)
    {p : Fin 4 → ℝ} (hp : p ∈ brillouinBox) (hp0 : p ≠ 0) (d : ℕ) : ContDiffAt ℝ d (defectSandwich Q m n' r s) p := by
  unfold defectSandwich
  refine ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => ?_
  exact ((contDiff_planeSineVector m n' i).contDiffAt.of_le (by exact_mod_cast le_top)).mul ((contDiffAt_inverseSymbolDefect hO i j hp hp0 d).mul
    ((contDiff_planeSineVector r s j).contDiffAt.of_le (by exact_mod_cast le_top)))
private theorem latticeSineNormSq_add_period (p : Fin 4 → ℝ) (l : Fin 4) : latticeSineNormSq (p + Pi.single l (2 * Real.pi)) = latticeSineNormSq p := by
  simp only [latticeSineNormSq, latticeSine_add_period]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := axisSign_mul_self l j
  calc (axisSign l j * latticeSine p j) ^ 2 = (axisSign l j * axisSign l j) * latticeSine p j ^ 2 := by ring
    _ = _ := by rw [this, one_mul]
abbrev _root_.YangMills.SharedProofs.p30766 := @latticeSineNormSq_add_period
private theorem inverseSymbolDefect_add_period (Q : IntBond → IntBond → ℝ) (l a b : Fin 4) (p : Fin 4 → ℝ) :
    inverseSymbolDefect Q a b (p + Pi.single l (2 * Real.pi)) = (axisSign l a * axisSign l b : ℝ) * inverseSymbolDefect Q a b p := by
  simp only [inverseSymbolDefect, inv_momentumSymbolMatrix_add_period, latticeSineNormSq_add_period]
  by_cases h : a = b
  · subst h
    have h1 : ((axisSign l a : ℝ) : ℂ) * (axisSign l a : ℝ) = 1 := by exact_mod_cast axisSign_mul_self l a
    simp only [if_true]
    push_cast
    rw [h1]
    ring
  · simp [h]
private theorem axisSign_ofReal_mul_self (l a : Fin 4) : ((axisSign l a : ℝ) : ℂ) * (axisSign l a : ℝ) = 1 := by exact_mod_cast axisSign_mul_self l a
private theorem columnSymbol_add_period (Q : IntBond → IntBond → ℝ) {r s : Fin 4} (hrs : r ≠ s) (i l : Fin 4) (p : Fin 4 → ℝ) :
    columnSymbol Q r s i (p + Pi.single l (2 * Real.pi)) = (axisSign l i * axisSign l r * axisSign l s : ℝ) * columnSymbol Q r s i p := by
  simp only [columnSymbol, inv_momentumSymbolMatrix_add_period, planeSineVector_add_period _ _ _ _ _ hrs]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  linear_combination (Complex.I * (axisSign l i : ℂ) * (axisSign l r : ℂ) * (axisSign l s : ℂ) * (momentumSymbolMatrix Q p)⁻¹ i j * (planeSineVector p r s j : ℂ)) * axisSign_ofReal_mul_self l j
private theorem curlColumnSymbol_add_period (Q : IntBond → IntBond → ℝ) {m n' r s : Fin 4} (hmn : m ≠ n') (hrs : r ≠ s) (l : Fin 4) (p : Fin 4 → ℝ) :
    curlColumnSymbol Q m n' r s (p + Pi.single l (2 * Real.pi)) = (axisSign l m * axisSign l n' * axisSign l r * axisSign l s : ℝ) * curlColumnSymbol Q m n' r s p := by
  simp only [curlColumnSymbol, inv_momentumSymbolMatrix_add_period, planeSineVector_add_period _ _ _ _ _ hrs, planeSineVector_add_period _ _ _ _ _ hmn]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  have h1 := axisSign_ofReal_mul_self l i
  have h2 := axisSign_ofReal_mul_self l j
  set A := (axisSign l m : ℂ) * (axisSign l n' : ℂ) * (axisSign l r : ℂ) * (axisSign l s : ℂ) * (planeSineVector p m n' i : ℂ) *
    ((momentumSymbolMatrix Q p)⁻¹ i j * (planeSineVector p r s j : ℂ)) with hA
  calc _ = ((axisSign l i : ℂ) * (axisSign l i : ℂ)) * ((axisSign l j : ℂ) * (axisSign l j : ℂ)) * A := by rw [hA]; ring
    _ = A := by rw [h1, h2]; ring
    _ = _ := by rw [hA]; ring
private theorem defectSandwich_add_period (Q : IntBond → IntBond → ℝ) {m n' r s : Fin 4} (hmn : m ≠ n') (hrs : r ≠ s) (l : Fin 4) (p : Fin 4 → ℝ) :
    defectSandwich Q m n' r s (p + Pi.single l (2 * Real.pi)) = (axisSign l m * axisSign l n' * axisSign l r * axisSign l s : ℝ) * defectSandwich Q m n' r s p := by
  simp only [defectSandwich, inverseSymbolDefect_add_period, planeSineVector_add_period _ _ _ _ _ hrs, planeSineVector_add_period _ _ _ _ _ hmn]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  have h1 := axisSign_ofReal_mul_self l i
  have h2 := axisSign_ofReal_mul_self l j
  set A := (axisSign l m : ℂ) * (axisSign l n' : ℂ) * (axisSign l r : ℂ) * (axisSign l s : ℂ) * (planeSineVector p m n' i : ℂ) *
    (inverseSymbolDefect Q i j p * (planeSineVector p r s j : ℂ)) with hA
  calc _ = ((axisSign l i : ℂ) * (axisSign l i : ℂ)) * ((axisSign l j : ℂ) * (axisSign l j : ℂ)) * A := by rw [hA]; ring
    _ = A := by rw [h1, h2]; ring
    _ = _ := by rw [hA]; ring
private def bondOffset (r s : Fin 4) (b : IntBond) (l : Fin 4) : ℝ :=
  (b.1 l : ℝ) + (if l = b.2 then 1 / 2 else 0) - (if l = r then 1 / 2 else 0) - (if l = s then 1 / 2 else 0)
private theorem exp_two_pi_bondOffset (r s : Fin 4) (b : IntBond) (l : Fin 4) :
    Complex.exp (Complex.I * ((2 * Real.pi * bondOffset r s b l : ℝ) : ℂ)) = (axisSign l b.2 * axisSign l r * axisSign l s : ℝ) := by
  have e : 2 * Real.pi * bondOffset r s b l = 2 * Real.pi * (b.1 l : ℝ) + (if l = b.2 then Real.pi else 0) -
      (if l = r then Real.pi else 0) - (if l = s then Real.pi else 0) := by
    simp only [bondOffset]
    split_ifs <;> ring
  rw [e, Complex.ofReal_sub, Complex.ofReal_sub, Complex.ofReal_add, mul_sub, mul_sub, mul_add, Complex.exp_sub, Complex.exp_sub,
    Complex.exp_add, exp_I_mul_two_pi_int, one_mul, exp_I_mul_axisSign, exp_I_mul_axisSign, exp_I_mul_axisSign]
  have h1 := axisSign_ofReal_mul_self l r
  have h2 := axisSign_ofReal_mul_self l s
  have g1 : ((axisSign l r : ℝ) : ℂ) ≠ 0 := fun h => by simp [h] at h1
  have g2 : ((axisSign l s : ℝ) : ℂ) ≠ 0 := fun h => by simp [h] at h2
  push_cast
  field_simp
  linear_combination (-(axisSign l b.2 : ℂ) * (axisSign l r : ℂ) ^ 2 ) * h2 + (-(axisSign l b.2 : ℂ)) * h1
private theorem exp_two_pi_plaquetteBarycentreShift (z : Fin 4 → ℤ) (m n' r s l : Fin 4) :
    Complex.exp (Complex.I * ((2 * Real.pi * plaquetteBarycentreShift z m n' r s l : ℝ) : ℂ)) =
      (axisSign l m * axisSign l n' * axisSign l r * axisSign l s : ℝ) := by
  have e : 2 * Real.pi * plaquetteBarycentreShift z m n' r s l = 2 * Real.pi * (z l : ℝ) + (if l = m then Real.pi else 0) +
      (if l = n' then Real.pi else 0) - (if l = r then Real.pi else 0) - (if l = s then Real.pi else 0) := by
    simp only [plaquetteBarycentreShift]
    split_ifs <;> ring
  rw [e, Complex.ofReal_sub, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_add, mul_sub, mul_sub, mul_add, mul_add,
    Complex.exp_sub, Complex.exp_sub, Complex.exp_add, Complex.exp_add, exp_I_mul_two_pi_int, one_mul, exp_I_mul_axisSign, exp_I_mul_axisSign, exp_I_mul_axisSign, exp_I_mul_axisSign]
  have h1 := axisSign_ofReal_mul_self l r
  have h2 := axisSign_ofReal_mul_self l s
  have g1 : ((axisSign l r : ℝ) : ℂ) ≠ 0 := fun h => by simp [h] at h1
  have g2 : ((axisSign l s : ℝ) : ℂ) ≠ 0 := fun h => by simp [h] at h2
  push_cast
  field_simp
  linear_combination (-(axisSign l m : ℂ) * (axisSign l n' : ℂ) * (axisSign l r : ℂ) ^ 2) * h2 + (-(axisSign l m : ℂ) * (axisSign l n' : ℂ)) * h1
private def planeWave (w p : Fin 4 → ℝ) : ℂ := Complex.exp (Complex.I * ((∑ l, p l * w l : ℝ) : ℂ))
private theorem norm_planeWave (w p : Fin 4 → ℝ) : ‖planeWave w p‖ = 1 := by apply _root_.YangMills.DeltaSharedProofs.p501034 <;> assumption
private theorem continuous_planeWave (w : Fin 4 → ℝ) : Continuous (planeWave w) := by
  unfold planeWave
  fun_prop
private theorem planeWave_add (w v p : Fin 4 → ℝ) : planeWave (w + v) p = planeWave w p * planeWave v p := by
  simp only [planeWave]
  rw [← Complex.exp_add, ← mul_add, ← Complex.ofReal_add, ← Finset.sum_add_distrib]
  congr 3
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.add_apply]
  ring
private theorem fourierKernelAt_eq (a : (Fin 4 → ℝ) → ℂ) (w : Fin 4 → ℝ) :
    fourierKernelAt a w = ((2 * Real.pi : ℝ) : ℂ)⁻¹ ^ 4 * ∫ p in brillouinBox, a p * planeWave w p := rfl
private theorem brillouinBox_subset_closedBall : brillouinBox ⊆ Metric.closedBall (0 : Fin 4 → ℝ) Real.pi := by
  intro p hp
  rw [mem_closedBall_zero_iff]
  exact (pi_norm_le_iff_of_nonneg Real.pi_pos.le).2 fun l => abs_le.2 ⟨hp.1 l, hp.2 l⟩
private theorem integrableOn_norm_inv_closedBall : IntegrableOn (fun q : Fin 4 → ℝ => ‖q‖⁻¹) (Metric.closedBall 0 Real.pi) := by
  set f : ℝ → ℝ := (Set.Iic Real.pi).indicator (fun y => y⁻¹) with hf
  have h1 : (fun q : Fin 4 → ℝ => f ‖q‖) =
      (Metric.closedBall (0 : Fin 4 → ℝ) Real.pi).indicator (fun q => ‖q‖⁻¹) := by
    ext q
    by_cases hq : ‖q‖ ≤ Real.pi
    · simp [hf, hq]
    · simp [hf, hq]
  have hk : ∀ y ∈ Set.Ioi (0 : ℝ), y ^ 3 • f y = (Set.Ioc 0 Real.pi).indicator (fun y => y ^ 2) y := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    by_cases hq : y ≤ Real.pi
    · have : y ^ 3 * y⁻¹ = y ^ 2 := by field_simp
      simp [hf, hq, hy', this]
    · simp [hf, hq, hy']
  have hint : IntegrableOn (Set.Ioc 0 Real.pi |>.indicator (fun y : ℝ => y ^ 2)) (Set.Ioi 0) :=
    (((continuous_pow 2).integrableOn_Ioc (a := 0) (b := Real.pi)).integrable_indicator
      measurableSet_Ioc).integrableOn
  have hint' : Integrable (fun q : Fin 4 → ℝ => f ‖q‖) volume := by
    rw [integrable_fun_norm_addHaar volume]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact hint.congr_fun (fun y hy => (hk y hy).symm) measurableSet_Ioi
  rw [h1] at hint'
  exact (integrable_indicator_iff measurableSet_closedBall).1 hint'
private theorem integrableOn_of_norm_inv_bound {a : (Fin 4 → ℝ) → ℂ} {B₀ : ℝ}
    (hc : ∀ p : Fin 4 → ℝ, p ∈ brillouinBox → p ≠ 0 → ContinuousAt a p)
    (hb : ∀ p : Fin 4 → ℝ, p ∈ brillouinBox → p ≠ 0 → ‖a p‖ ≤ B₀ * ‖p‖⁻¹) : IntegrableOn a brillouinBox := by
  have hg := (integrableOn_norm_inv_closedBall.mono_set brillouinBox_subset_closedBall).const_mul B₀
  have hbox : MeasurableSet brillouinBox := measurableSet_Icc
  have hc' : ContinuousOn a (brillouinBox \ {0}) := fun p hp => (hc p hp.1 hp.2).continuousWithinAt
  have hm : AEStronglyMeasurable a (volume.restrict brillouinBox) := by
    have h1 : AEStronglyMeasurable a (volume.restrict (brillouinBox \ {0})) :=
      hc'.aestronglyMeasurable (hbox.diff (measurableSet_singleton 0))
    rwa [Measure.restrict_congr_set (sdiff_null_ae_eq_self (measure_singleton (0 : Fin 4 → ℝ)))] at h1
  refine Integrable.mono' hg hm ?_
  rw [ae_restrict_iff' hbox]
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : Fin 4 → ℝ))] with q hq hqs
  exact hb q hqs hq
private theorem integrableOn_mul_planeWave {a : (Fin 4 → ℝ) → ℂ} (h : IntegrableOn a brillouinBox) (w : Fin 4 → ℝ) :
    IntegrableOn (fun p => a p * planeWave w p) brillouinBox := by
  refine Integrable.mono h (h.aestronglyMeasurable.mul (continuous_planeWave w).aestronglyMeasurable) (ae_of_all _ fun p => ?_)
  simp [norm_mul, norm_planeWave]
private theorem norm_le_of_hasScaledJet {a : (Fin 4 → ℝ) → ℂ} {p : Fin 4 → ℝ} {l : Fin 4} {m : ℤ} {B : ℕ → ℝ} (hp : p ∈ brillouinBox) (hp0 : p ≠ 0)
    (hJ : HasScaledJet (fun t => a (Function.update p l t)) (p l) (Real.sqrt (momentumNormSq p)) m B) (h1 : -1 ≤ m) (h2 : m ≤ 1) :
    ‖a p‖ ≤ (49 * |B 0|) * ‖p‖⁻¹ := by
  have hρ := sqrt_momentumNormSq_pos hp0
  have hρ7 := sqrt_momentumNormSq_le_seven hp
  have hJ0 := (hJ 0).2
  simp only [iteratedDeriv_zero, Function.update_eq_self] at hJ0
  set ρ := Real.sqrt (momentumNormSq p) with hρd
  have hn0 : 0 < ‖p‖ := norm_pos_iff.2 hp0
  have hnρ : ‖p‖ ≤ ρ := (pi_norm_le_iff_of_nonneg hρ.le).2 fun l => by
    rw [Real.norm_eq_abs]
    exact abs_coord_le_sqrt_momentumNormSq p l
  have hpow : ρ ^ (m - ((0 : ℕ) : ℤ)) ≤ 49 * ρ⁻¹ := by
    have hρi : 0 < ρ⁻¹ := inv_pos.2 hρ
    have e : m = -1 ∨ m = 0 ∨ m = 1 := by omega
    rcases e with rfl | rfl | rfl
    · norm_num
      linarith
    · norm_num
      rw [← div_eq_mul_inv, le_div_iff₀ hρ]
      linarith
    · norm_num
      rw [← div_eq_mul_inv, le_div_iff₀ hρ]
      nlinarith
  have hinv : ρ⁻¹ ≤ ‖p‖⁻¹ := inv_anti₀ hn0 hnρ
  have hzp : 0 < ρ ^ (m - ((0 : ℕ) : ℤ)) := zpow_pos hρ _
  calc ‖a p‖ ≤ B 0 * ρ ^ (m - ((0 : ℕ) : ℤ)) := hJ0
    _ ≤ |B 0| * ρ ^ (m - ((0 : ℕ) : ℤ)) := mul_le_mul_of_nonneg_right (le_abs_self _) hzp.le
    _ ≤ |B 0| * (49 * ‖p‖⁻¹) := by
      refine mul_le_mul_of_nonneg_left (hpow.trans ?_) (abs_nonneg _)
      linarith
    _ = _ := by ring
private theorem integral_exp_I_mul_int (n : ℤ) :
    ∫ t in Set.Icc (-Real.pi) Real.pi, Complex.exp (Complex.I * ((t * n : ℝ) : ℂ)) = if n = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  by_cases h : n = 0
  · subst h
    simp
    ring
  · simp only [h, if_false]
    have hc : Complex.I * (n : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast h)
    have e : ∀ t : ℝ, Complex.exp (Complex.I * ((t * n : ℝ) : ℂ)) = Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)) := by
      intro t
      congr 1
      push_cast
      ring
    simp only [e]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ)) = Complex.exp (Complex.I * (n : ℂ) * ((-Real.pi : ℝ) : ℂ)) := by
      have h2 := Complex.exp_int_mul_two_pi_mul_I n
      have e2 : Complex.I * (n : ℂ) * (Real.pi : ℂ) = Complex.I * (n : ℂ) * ((-Real.pi : ℝ) : ℂ) + (n : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        ring
      rw [e2, Complex.exp_add, h2, mul_one]
    rw [h1]
    simp
private theorem normalized_integral_planeWave_int (x : Fin 4 → ℤ) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ ^ 4 * ∫ p in brillouinBox, planeWave (fun l => (x l : ℝ)) p = if x = 0 then 1 else 0 := by
  have hm : (volume : Measure (Fin 4 → ℝ)).restrict brillouinBox =
      Measure.pi fun _ : Fin 4 => (volume : Measure ℝ).restrict (Set.Icc (-Real.pi) Real.pi) := by
    have e : brillouinBox = Set.pi Set.univ fun _ : Fin 4 => Set.Icc (-Real.pi) Real.pi := by
      rw [Set.pi_univ_Icc]
      rfl
    rw [e, volume_pi, Measure.restrict_pi_pi]
  have hph : ∀ p : Fin 4 → ℝ, planeWave (fun l => (x l : ℝ)) p = ∏ l, Complex.exp (Complex.I * ((p l * x l : ℝ) : ℂ)) := by
    intro p
    rw [planeWave, ← Complex.exp_sum, ← Finset.mul_sum]
    push_cast
    rfl
  simp only [hph]
  rw [hm, integral_fintype_prod_eq_prod (fun l t => Complex.exp (Complex.I * ((t * x l : ℝ) : ℂ)))]
  simp only [integral_exp_I_mul_int]
  by_cases h : x = 0
  · subst h
    have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    simp only [Pi.zero_apply, if_true, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp
  · obtain ⟨l, hl⟩ := Function.ne_iff.1 h
    have hl' : x l ≠ 0 := by simpa using hl
    rw [Finset.prod_eq_zero (Finset.mem_univ l) (by simp [hl']), if_neg h, mul_zero]
private def symbolPhase (i j : Fin 4) (p : Fin 4 → ℝ) (z : Fin 4 → ℤ) : ℂ :=
  Complex.exp (Complex.I * ((∑ l, p l * ((z l : ℝ) + (if l = j then 1 / 2 else 0) - (if l = i then 1 / 2 else 0)) : ℝ) : ℂ))
private theorem norm_symbolPhase (i j : Fin 4) (p : Fin 4 → ℝ) (z : Fin 4 → ℤ) : ‖symbolPhase i j p z‖ = 1 := by
  rw [symbolPhase, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _
private theorem symbolPhase_exponent (i j : Fin 4) (p : Fin 4 → ℝ) (z : Fin 4 → ℤ) :
    (∑ l, p l * ((z l : ℝ) + (if l = j then 1 / 2 else 0) - (if l = i then 1 / 2 else 0))) =
      (∑ l, p l * (z l : ℝ)) + p j / 2 - p i / 2 := by
  have h1 : ∑ l, p l * (if l = j then (1 / 2 : ℝ) else 0) = p j / 2 := by simp; ring
  have h2 : ∑ l, p l * (if l = i then (1 / 2 : ℝ) else 0) = p i / 2 := by simp; ring
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2]
private theorem four_phases_eq_sin_mul_sin (a b : ℝ) :
    Complex.exp (Complex.I * ((b - a : ℝ) : ℂ)) - Complex.exp (Complex.I * ((-b - a : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((a + b : ℝ) : ℂ)) + Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) =
      ((4 * Real.sin a * Real.sin b : ℝ) : ℂ) := by
  set A := Complex.exp ((a : ℂ) * Complex.I) with hA
  set B := Complex.exp ((b : ℂ) * Complex.I) with hB
  have s1 : Complex.sin (a : ℂ) = (A⁻¹ - A) * Complex.I / 2 := by
    rw [Complex.sin, hA, ← Complex.exp_neg]
    congr 3
    ring_nf
  have s2 : Complex.sin (b : ℂ) = (B⁻¹ - B) * Complex.I / 2 := by
    rw [Complex.sin, hB, ← Complex.exp_neg]
    congr 3
    ring_nf
  have e1 : Complex.exp (Complex.I * ((b - a : ℝ) : ℂ)) = B * A⁻¹ := by
    rw [hA, hB, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e2 : Complex.exp (Complex.I * ((-b - a : ℝ) : ℂ)) = B⁻¹ * A⁻¹ := by
    rw [hA, hB, ← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e3 : Complex.exp (Complex.I * ((a + b : ℝ) : ℂ)) = A * B := by
    rw [hA, hB, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e4 : Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) = A * B⁻¹ := by
    rw [hA, hB, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e1, e2, e3, e4]
  push_cast
  rw [s1, s2]
  have hI := Complex.I_sq
  linear_combination (-(A⁻¹ - A) * (B⁻¹ - B)) * hI
abbrev _root_.YangMills.SharedProofs.p9881 := @four_phases_eq_sin_mul_sin
private theorem midpointSymbol_split {Q : IntBond → IntBond → ℝ} (i j : Fin 4) (p : Fin 4 → ℝ)
    (hs : Summable fun z : Fin 4 → ℤ => (Q (0, i) (z, j) : ℂ) * symbolPhase i j p z) :
    midpointSymbol Q i j p = (∑' z : Fin 4 → ℤ, (Q (0, i) (z, j) : ℂ) * symbolPhase i j p z) +
      ((4 * Real.sin (p i / 2) * Real.sin (p j / 2) : ℝ) : ℂ) := by
  have hone : ∀ z₀ : Fin 4 → ℤ, HasSum (fun z : Fin 4 → ℤ => (if z = z₀ then symbolPhase i j p z₀ else 0)) (symbolPhase i j p z₀) :=
    fun z₀ => hasSum_ite_eq z₀ _
  have hsum := ((hs.hasSum.add (hone 0)).sub (hone (-Pi.single j 1))).sub (hone (Pi.single i 1)) |>.add (hone (Pi.single i 1 - Pi.single j 1))
  have hval : symbolPhase i j p 0 - symbolPhase i j p (-Pi.single j 1) - symbolPhase i j p (Pi.single i 1) + symbolPhase i j p (Pi.single i 1 - Pi.single j 1) =
      ((4 * Real.sin (p i / 2) * Real.sin (p j / 2) : ℝ) : ℂ) := by
    rw [← four_phases_eq_sin_mul_sin]
    have hs1 : ∀ (c : Fin 4 → ℤ) (e : ℝ), (∑ l, p l * (c l : ℝ)) = e → symbolPhase i j p c = Complex.exp (Complex.I * ((e + p j / 2 - p i / 2 : ℝ) : ℂ)) := by
      intro c e h
      rw [symbolPhase, symbolPhase_exponent, h]
    have v1 := hs1 0 0 (by simp)
    have v2 := hs1 (-Pi.single j 1) (-p j) (by simp [Pi.single_apply])
    have v3 := hs1 (Pi.single i 1) (p i) (by simp [Pi.single_apply])
    have v4 := hs1 (Pi.single i 1 - Pi.single j 1) (p i - p j) (by simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib])
    have a1 : (0 + p j / 2 - p i / 2 : ℝ) = p j / 2 - p i / 2 := by ring
    have a2 : (-p j + p j / 2 - p i / 2 : ℝ) = -(p j / 2) - p i / 2 := by ring
    have a3 : (p i + p j / 2 - p i / 2 : ℝ) = p i / 2 + p j / 2 := by ring
    have a4 : (p i - p j + p j / 2 - p i / 2 : ℝ) = p i / 2 - p j / 2 := by ring
    rw [v1, v2, v3, v4, a1, a2, a3, a4]
  have hval' : (∑' z : Fin 4 → ℤ, (Q (0, i) (z, j) : ℂ) * symbolPhase i j p z) + symbolPhase i j p 0 - symbolPhase i j p (-Pi.single j 1) -
      symbolPhase i j p (Pi.single i 1) + symbolPhase i j p (Pi.single i 1 - Pi.single j 1) =
      (∑' z : Fin 4 → ℤ, (Q (0, i) (z, j) : ℂ) * symbolPhase i j p z) + ((4 * Real.sin (p i / 2) * Real.sin (p j / 2) : ℝ) : ℂ) := by
    rw [← hval]
    ring
  rw [hval'] at hsum
  rw [← hsum.tsum_eq]
  simp only [midpointSymbol]
  refine tsum_congr fun z => ?_
  simp only [gaugeFixedKernel]
  have c1 : ((0 : Fin 4 → ℤ) = z) = (z = 0) := propext eq_comm
  have c2 : ((0 : Fin 4 → ℤ) = z + Pi.single j 1) = (z = -Pi.single j 1) := propext ⟨fun h => by
    rw [eq_neg_iff_add_eq_zero]; exact h.symm, fun h => by rw [h]; simp⟩
  have c3 : ((0 : Fin 4 → ℤ) + Pi.single i 1 = z) = (z = Pi.single i 1) := propext ⟨fun h => by
    rw [← h]; simp, fun h => by rw [h]; simp⟩
  have c4 : ((0 : Fin 4 → ℤ) + Pi.single i 1 = z + Pi.single j 1) = (z = Pi.single i 1 - Pi.single j 1) := propext ⟨fun h => by
    rw [eq_sub_iff_add_eq, ← h]; simp, fun h => by rw [h]; simp⟩
  simp only [c1, c2, c3, c4]
  have ez : ∀ z₀ : Fin 4 → ℤ, (if z = z₀ then symbolPhase i j p z₀ else 0) = ((if z = z₀ then (1 : ℝ) else 0 : ℝ) : ℂ) * symbolPhase i j p z := by
    intro z₀
    by_cases h : z = z₀
    · subst h
      simp
    · simp [h]
  rw [ez, ez, ez, ez]
  show ((Q (0, i) (z, j) + ((if z = 0 then (1 : ℝ) else 0) - (if z = -Pi.single j 1 then (1 : ℝ) else 0) -
      (if z = Pi.single i 1 then (1 : ℝ) else 0) + (if z = Pi.single i 1 - Pi.single j 1 then (1 : ℝ) else 0)) : ℝ) : ℂ) * symbolPhase i j p z = _
  simp only [Complex.ofReal_add, Complex.ofReal_sub]
  ring
private theorem hasSum_of_fibres {f : IntBond → ℂ} {S : Fin 4 → ℂ} (h : ∀ j, HasSum (fun y => f (y, j)) (S j)) :
    HasSum f (∑ j, S j) := by
  classical
  have hj : ∀ j, HasSum (fun b : IntBond => if b.2 = j then f b else 0) (S j) := by
    intro j
    have inj : Function.Injective (fun y : Fin 4 → ℤ => ((y, j) : IntBond)) := fun a b e => (Prod.mk.inj e).1
    refine (inj.hasSum_iff ?_).1 ?_
    · intro x hx
      have : x.2 ≠ j := fun e => hx ⟨x.1, by ext <;> simp [e]⟩
      simp [this]
    · simpa [Function.comp_def] using h j
  have h2 := hasSum_sum (s := Finset.univ) fun j _ => hj j
  simpa using h2
set_option maxHeartbeats 2000000 in
private theorem hasSum_row_columnSymbol {Cs : ℕ → ℝ} {Q : IntBond → IntBond → ℝ} (hO : InverseSymbolOrders Cs Q)
    (hsym : ∀ (i j : Fin 4) (p : Fin 4 → ℝ), midpointSymbol Q i j p = midpointSymbol Q j i p)
    (hblind : ∀ (i : Fin 4) (p : Fin 4 → ℝ),
      ∑ j, (midpointSymbol Q i j p - ((4 * Real.sin (p i / 2) * Real.sin (p j / 2) : ℝ) : ℂ)) *
        ((2 * Real.sin (p j / 2) : ℝ) : ℂ) = 0)
    (hQsum : ∀ b, Summable fun b' => |Q b b'|)
    (hshift : ∀ (t : Fin 4 → ℤ) (b b' : IntBond), Q (b.1 + t, b.2) (b'.1 + t, b'.2) = Q b b')
    {r s : Fin 4} (hrs : r ≠ s) {p : Fin 4 → ℝ} (hp : p ∈ brillouinBox) (hp0 : p ≠ 0) (b : IntBond) :
    HasSum (fun b' : IntBond => (Q b b' : ℂ) * (columnSymbol Q r s b'.2 p * planeWave (bondOffset r s b') p))
      (planeWave (bondOffset r s b) p * (Complex.I * (planeSineVector p r s b.2 : ℂ))) := by
  classical
  obtain ⟨x, i⟩ := b
  have hs : ∀ j, Summable fun z : Fin 4 → ℤ => (Q (0, i) (z, j) : ℂ) * symbolPhase i j p z := by
    intro j
    have inj : Function.Injective (fun y : Fin 4 → ℤ => ((y, j) : IntBond)) := fun a b e => (Prod.mk.inj e).1
    refine Summable.of_norm ?_
    have := (hQsum (0, i)).comp_injective inj
    refine this.congr fun z => ?_
    simp [norm_mul, norm_symbolPhase]
  set Qs : Fin 4 → ℂ := fun j => ∑' z : Fin 4 → ℤ, (Q (0, i) (z, j) : ℂ) * symbolPhase i j p z with hQs
  have hstep : ∀ j, HasSum (fun y => (Q (x, i) (y, j) : ℂ) * (columnSymbol Q r s j p * planeWave (bondOffset r s (y, j)) p))
      (planeWave (bondOffset r s (x, i)) p * columnSymbol Q r s j p * Qs j) := by
    intro j
    have h1 := (hs j).hasSum.mul_left (planeWave (bondOffset r s (x, i)) p * columnSymbol Q r s j p)
    have h2 := ((Equiv.subRight x).hasSum_iff).2 h1
    have hfun : (fun y => (Q (x, i) (y, j) : ℂ) * (columnSymbol Q r s j p * planeWave (bondOffset r s (y, j)) p)) =
        (fun z => planeWave (bondOffset r s (x, i)) p * columnSymbol Q r s j p * ((Q (0, i) (z, j) : ℂ) * symbolPhase i j p z)) ∘ (Equiv.subRight x) := by
      funext y
      simp only [Function.comp, Equiv.subRight_apply]
      have hq : Q (x, i) (y, j) = Q (0, i) (y - x, j) := by
        have := hshift x (0, i) (y - x, j)
        simpa using this
      have hph : planeWave (bondOffset r s (y, j)) p = planeWave (bondOffset r s (x, i)) p * symbolPhase i j p (y - x) := by
        simp only [planeWave, symbolPhase]
        rw [← Complex.exp_add, ← mul_add, ← Complex.ofReal_add, ← Finset.sum_add_distrib]
        congr 3
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [bondOffset, Pi.sub_apply]
        push_cast
        ring
      rw [hq, hph]
      ring
    rw [hfun]
    exact h2
  have hv := hasSum_of_fibres (f := fun b' : IntBond => (Q (x, i) b' : ℂ) * (columnSymbol Q r s b'.2 p * planeWave (bondOffset r s b') p)) hstep
  have hunit := (hO 0 0 p hp hp0).1
  set M := momentumSymbolMatrix Q p with hM
  set σ : Fin 4 → ℂ := fun k => (latticeSine p k : ℂ) with hσ
  set ν : Fin 4 → ℂ := fun k => (planeSineVector p r s k : ℂ) with hν
  set v : Fin 4 → ℂ := M⁻¹.mulVec ν with hvd
  have hcol : ∀ j, columnSymbol Q r s j p = Complex.I * v j := by
    intro j
    simp only [columnSymbol, hvd, Matrix.mulVec, dotProduct, hν, hM]
  have hMv : M.mulVec v = ν := by
    rw [hvd, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hsig : ∀ a b : Fin 4, ((4 * Real.sin (p a / 2) * Real.sin (p b / 2) : ℝ) : ℂ) = σ a * σ b := by
    intro a b
    simp only [hσ, latticeSine]
    push_cast
    ring
  have hsplit : ∀ j, Qs j = M i j - σ i * σ j := by
    intro j
    have h1 := midpointSymbol_split (Q := Q) i j p (hs j)
    rw [hsig] at h1
    have h2 : M i j = midpointSymbol Q i j p := rfl
    rw [h2, h1]
    simp only [hQs]
    ring
  set S : ℂ := (latticeSineNormSq p : ℂ) with hS
  have hS0 : S ≠ 0 := latticeSineNormSq_ne_zero hp hp0
  have hSσ : S = ∑ k, σ k * σ k := by
    simp only [hS, hσ, latticeSineNormSq]
    push_cast
    exact Finset.sum_congr rfl fun k _ => by ring
  have hMσ : M.mulVec σ = S • σ := by
    funext a
    have h1 := hblind a p
    simp only [hsig] at h1
    have h2 : ∀ j, ((2 * Real.sin (p j / 2) : ℝ) : ℂ) = σ j := fun j => by simp only [hσ, latticeSine]
    simp only [h2] at h1
    have h3 : ∑ j, (midpointSymbol Q a j p - σ a * σ j) * σ j = (M.mulVec σ) a - S * σ a := by
      simp only [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
      congr 1
      rw [hSσ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h3] at h1
    simp only [Pi.smul_apply, smul_eq_mul]
    exact sub_eq_zero.1 h1
  have hNσ : M⁻¹.mulVec σ = S⁻¹ • σ := by
    have h1 : M⁻¹.mulVec (M.mulVec σ) = σ := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
    rw [hMσ, Matrix.mulVec_smul] at h1
    have h2 : S⁻¹ • (S • M⁻¹.mulVec σ) = S⁻¹ • σ := by rw [h1]
    rwa [smul_smul, inv_mul_cancel₀ hS0, one_smul] at h2
  have hTr : M.transpose = M := by
    ext a b
    exact hsym b a p
  have hNT : (M⁻¹).transpose = M⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hTr]
  have hσν : ∑ k, σ k * ν k = 0 := by
    have h0 : ∑ k, latticeSine p k * planeSineVector p r s k = 0 := by
      simp only [planeSineVector, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    simp only [hν, hσ]
    exact_mod_cast h0
  have hσv : ∑ j, σ j * v j = 0 := by
    have h1 : ∑ j, σ j * v j = (M⁻¹.mulVec σ) ⬝ᵥ ν := by
      have h2 : σ ⬝ᵥ (M⁻¹.mulVec ν) = (Matrix.vecMul σ M⁻¹) ⬝ᵥ ν := Matrix.dotProduct_mulVec _ _ _
      have h3 : Matrix.vecMul σ M⁻¹ = M⁻¹.mulVec σ := by
        conv_lhs => rw [← hNT]
        exact Matrix.vecMul_transpose _ _
      rw [h3] at h2
      exact h2
    rw [h1, hNσ]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
    have : ∑ k, S⁻¹ * σ k * ν k = S⁻¹ * ∑ k, σ k * ν k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, hσν, mul_zero]
  have hval : ∑ j, planeWave (bondOffset r s (x, i)) p * columnSymbol Q r s j p * Qs j =
      planeWave (bondOffset r s (x, i)) p * (Complex.I * ν i) := by
    have h1 : ∀ j, planeWave (bondOffset r s (x, i)) p * columnSymbol Q r s j p * Qs j =
        planeWave (bondOffset r s (x, i)) p * Complex.I * (M i j * v j - σ i * (σ j * v j)) := by
      intro j
      rw [hcol, hsplit]
      ring
    simp only [h1]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hσv, mul_zero, sub_zero]
    have h2 : ∑ j, M i j * v j = ν i := congrFun hMv i
    rw [h2]
    ring
  rw [hval] at hv
  exact hv
private theorem integrableOn_planeWave (w : Fin 4 → ℝ) : IntegrableOn (planeWave w) brillouinBox :=
  (continuous_planeWave w).continuousOn.integrableOn_compact isCompact_Icc
private theorem I_mul_latticeSine (p : Fin 4 → ℝ) (k : Fin 4) :
    Complex.I * (latticeSine p k : ℂ) = planeWave (Pi.single k (1 / 2)) p - planeWave (-Pi.single k (1 / 2)) p := by
  have h1 : (∑ l, p l * (Pi.single k (1 / 2) : Fin 4 → ℝ) l) = p k / 2 := by
    simp [Pi.single_apply]
    ring
  have h2 : (∑ l, p l * (-Pi.single k (1 / 2) : Fin 4 → ℝ) l) = -(p k / 2) := by
    simp [Pi.single_apply]
    ring
  simp only [planeWave, h1, h2, latticeSine]
  push_cast
  rw [show Complex.sin ((p k : ℂ) / 2) = (Complex.exp (-((p k : ℂ) / 2) * Complex.I) - Complex.exp (((p k : ℂ) / 2) * Complex.I)) * Complex.I / 2 from rfl]
  have e1 : Complex.I * ((p k : ℂ) / 2) = ((p k : ℂ) / 2) * Complex.I := mul_comm _ _
  have e2 : Complex.I * -((p k : ℂ) / 2) = -((p k : ℂ) / 2) * Complex.I := by ring
  rw [e1, e2]
  have hI := Complex.I_sq
  linear_combination (Complex.exp (-((p k : ℂ) / 2) * Complex.I) - Complex.exp (((p k : ℂ) / 2) * Complex.I)) * hI
private theorem normalized_integral_unit_curl {r s : Fin 4} (hrs : r ≠ s) (b : IntBond) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ ^ 4 * ∫ p in brillouinBox, planeWave (bondOffset r s b) p * (Complex.I * (planeSineVector p r s b.2 : ℂ)) =
      ((intCurl (Pi.single b 1) (0, r, s) : ℝ) : ℂ) := by
  classical
  obtain ⟨x, i⟩ := b
  set c₀ : ℂ := ((2 * Real.pi : ℝ) : ℂ)⁻¹ ^ 4 with hc₀
  set X : Fin 4 → ℝ := fun l => (x l : ℝ) with hX
  have hdiff : ∀ k : Fin 4, c₀ * ∫ p in brillouinBox, planeWave (X - Pi.single k (1 / 2)) p * (Complex.I * (latticeSine p k : ℂ)) =
      (if x = 0 then 1 else 0) - (if x = Pi.single k 1 then 1 else 0) := by
    intro k
    have h1 : ∀ p, planeWave (X - Pi.single k (1 / 2)) p * (Complex.I * (latticeSine p k : ℂ)) =
        planeWave (fun l => (x l : ℝ)) p - planeWave (fun l => (((x - Pi.single k 1 : Fin 4 → ℤ) l : ℤ) : ℝ)) p := by
      intro p
      rw [I_mul_latticeSine, mul_sub, ← planeWave_add, ← planeWave_add]
      congr 2
      · funext l
        simp [hX]
      · funext l
        by_cases h : l = k
        · subst h
          simp [hX]
          ring
        · simp [hX, h]
    simp only [h1]
    rw [integral_sub (integrableOn_planeWave _) (integrableOn_planeWave _), mul_sub, normalized_integral_planeWave_int x]
    have h2 := normalized_integral_planeWave_int (x - Pi.single k 1)
    rw [h2]
    congr 1
    have : (x - Pi.single k 1 = 0) = (x = Pi.single k 1) := propext sub_eq_zero
    simp only [this]
  have hv : ∀ (y : Fin 4 → ℤ) (j : Fin 4), (Pi.single (x, i) (1 : ℝ) : IntBond → ℝ) (y, j) = if j = i ∧ y = x then 1 else 0 := by
    intro y j
    rw [Pi.single_apply]
    refine if_congr ?_ rfl rfl
    simp only [Prod.mk.injEq]
    tauto
  have hzero : ∀ (y : Fin 4 → ℤ), (0 + y = x) = (x = y) := fun y => propext ⟨fun h => by rw [← h]; simp, fun h => by rw [h]; simp⟩
  simp only [intCurl, hv]
  by_cases h1 : i = r
  · subst h1
    have hw : bondOffset i s (x, i) = X - Pi.single s (1 / 2) := by
      funext l
      by_cases h2 : l = s
      · subst h2
        simp [bondOffset, hX, Ne.symm hrs]
      · by_cases h3 : l = i
        · subst h3
          simp [bondOffset, hX, h2]
        · simp [bondOffset, hX, h2, h3]
    have hpl : ∀ p, (planeSineVector p i s i : ℂ) = (latticeSine p s : ℂ) := fun p => by simp [planeSineVector, hrs]
    simp only [hw, hpl]
    rw [hdiff s]
    simp only [hzero, true_and, (Ne.symm hrs : s ≠ i), false_and, if_false, add_zero, sub_zero]
    have e0 : ((0 : Fin 4 → ℤ) = x) = (x = 0) := propext eq_comm
    simp only [e0]
    split_ifs <;> simp
  · by_cases h2 : i = s
    · subst h2
      have hw : bondOffset r i (x, i) = X - Pi.single r (1 / 2) := by
        funext l
        by_cases h3 : l = r
        · subst h3
          simp [bondOffset, hX, hrs]
        · by_cases h4 : l = i
          · subst h4
            simp [bondOffset, hX, h3]
          · simp [bondOffset, hX, h3, h4]
      have hpl : ∀ p, (planeSineVector p r i i : ℂ) = -(latticeSine p r : ℂ) := fun p => by simp [planeSineVector, Ne.symm hrs]
      have hneg : ∀ p, planeWave (X - Pi.single r (1 / 2)) p * (Complex.I * -(latticeSine p r : ℂ)) =
          -(planeWave (X - Pi.single r (1 / 2)) p * (Complex.I * (latticeSine p r : ℂ))) := fun p => by ring
      simp only [hw, hpl, hneg]
      rw [integral_neg, mul_neg, hdiff r]
      simp only [hzero]
      simp only [true_and, hrs, false_and, if_false, zero_add, add_zero, sub_zero]
      have e0 : ((0 : Fin 4 → ℤ) = x) = (x = 0) := propext eq_comm
      simp only [e0]
      split_ifs <;> simp
    · have hpl : ∀ p, (planeSineVector p r s i : ℂ) = 0 := fun p => by simp [planeSineVector, h1, h2]
      simp only [hpl, mul_zero, integral_zero]
      have g1 : ¬ (r = i) := fun e => h1 e.symm
      have g2 : ¬ (s = i) := fun e => h2 e.symm
      simp [g1, g2]
private theorem summable_exp_neg_mul_natAbs {c : ℝ} (hc : 0 < c) : Summable fun z : ℤ => Real.exp (-(c * z.natAbs)) := by
  have h : Summable fun m : ℕ => Real.exp (-(c * m)) := by
    have h1 : Real.exp (-c) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    have := summable_geometric_of_lt_one (Real.exp_pos (-c)).le h1
    refine this.congr fun m => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  exact Summable.of_nat_of_neg (by simpa using h) (by simpa using h)
abbrev _root_.YangMills.SharedProofs.p17292 := @summable_exp_neg_mul_natAbs
private theorem summable_exp_neg_bondSupDist {c : ℝ} (hc : 0 < c) (b₀ : IntBond) :
    Summable (fun b => Real.exp (-(c * bondSupDist b₀ b))) := by
  classical
  set A := ∑' z : ℤ, Real.exp (-(c / 4 * z.natAbs)) with hA
  have hsum := summable_exp_neg_mul_natAbs (c := c / 4) (by positivity)
  set e : Fin 4 → ℤ → ℝ := fun i t => Real.exp (-(c / 4 * ((b₀.1 i - t).natAbs : ℝ))) with he
  have he0 : ∀ i t, 0 ≤ e i t := fun i t => (Real.exp_pos _).le
  have hes : ∀ i, Summable (e i) := fun i => hsum.comp_injective (Equiv.subLeft (b₀.1 i)).injective
  have het : ∀ i, ∑' t, e i t = A := fun i => (Equiv.subLeft (b₀.1 i)).tsum_eq fun z : ℤ => Real.exp (-(c / 4 * (z.natAbs : ℝ)))
  set Ψ : IntBond → ℝ := fun b => ∏ i, e i (b.1 i) with hΨ
  have hΨ0 : ∀ b, 0 ≤ Ψ b := fun b => Finset.prod_nonneg fun i _ => he0 i _
  have hfin : ∀ s : Finset IntBond, ∑ b ∈ s, Ψ b ≤ 4 * A ^ 4 := by
    intro s
    set U : Fin 4 → Finset ℤ := fun i => s.image fun b => b.1 i with hU
    have hsub : s ⊆ (Fintype.piFinset U) ×ˢ (Finset.univ : Finset (Fin 4)) := by
      intro b hb
      simp only [Finset.mem_product, Fintype.mem_piFinset, Finset.mem_univ, and_true]
      intro i
      exact Finset.mem_image_of_mem _ hb
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => hΨ0 b).trans ?_
    rw [Finset.sum_product]
    simp only [hΨ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 : ∑ z ∈ Fintype.piFinset U, ∏ i, e i (z i) = ∏ i, ∑ t ∈ U i, e i t :=
      (Finset.prod_univ_sum U (fun i t => e i t)).symm
    rw [← Finset.mul_sum, h1]
    have h2 : ∏ i, ∑ t ∈ U i, e i t ≤ ∏ _i : Fin 4, A := by
      refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun t _ => he0 i t) fun i _ => ?_
      rw [← het i]
      exact (hes i).sum_le_tsum _ (fun t _ => he0 i t)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    push_cast
    linarith
  have hbound : ∀ b, Real.exp (-(c * bondSupDist b₀ b)) ≤ Ψ b := by
    intro b
    simp only [hΨ, he]
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    have h1 : ∀ i, ((b₀.1 i - b.1 i).natAbs : ℝ) ≤ bondSupDist b₀ b := fun i => by
      exact_mod_cast Finset.le_sup (f := fun i => (b₀.1 i - b.1 i).natAbs) (Finset.mem_univ i)
    have h2 : ∑ i, -(c / 4 * ((b₀.1 i - b.1 i).natAbs : ℝ)) ≥ ∑ _i : Fin 4, -(c / 4 * (bondSupDist b₀ b : ℝ)) :=
      Finset.sum_le_sum fun i _ => by nlinarith [h1 i]
    have h3 : ∑ _i : Fin 4, -(c / 4 * (bondSupDist b₀ b : ℝ)) = -(c * bondSupDist b₀ b) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    linarith
  have hΨs : Summable Ψ := summable_of_sum_le hΨ0 hfin
  exact Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hbound hΨs
private theorem hasSum_column_equation {Cs : ℕ → ℝ} {Q : IntBond → IntBond → ℝ} (hO : InverseSymbolOrders Cs Q)
    (hsym : ∀ (i j : Fin 4) (p : Fin 4 → ℝ), midpointSymbol Q i j p = midpointSymbol Q j i p)
    (hblind : ∀ (i : Fin 4) (p : Fin 4 → ℝ),
      ∑ j, (midpointSymbol Q i j p - ((4 * Real.sin (p i / 2) * Real.sin (p j / 2) : ℝ) : ℂ)) *
        ((2 * Real.sin (p j / 2) : ℝ) : ℂ) = 0)
    (hQsum : ∀ b, Summable fun b' => |Q b b'|)
    (hshift : ∀ (t : Fin 4 → ℤ) (b b' : IntBond), Q (b.1 + t, b.2) (b'.1 + t, b'.2) = Q b b')
    {r s : Fin 4} (hrs : r ≠ s) (hint : ∀ j, IntegrableOn (columnSymbol Q r s j) brillouinBox) (b : IntBond) :
    HasSum (fun b' : IntBond => (Q b b' : ℂ) * fourierKernelAt (columnSymbol Q r s b'.2) (bondOffset r s b'))
      ((intCurl (Pi.single b 1) (0, r, s) : ℝ) : ℂ) := by
  set μ := (volume : Measure (Fin 4 → ℝ)).restrict brillouinBox with hμ
  set F : IntBond → (Fin 4 → ℝ) → ℂ := fun b' p => (Q b b' : ℂ) * (columnSymbol Q r s b'.2 p * planeWave (bondOffset r s b') p) with hF
  have hFint : ∀ b', Integrable (F b') μ := fun b' => (integrableOn_mul_planeWave (hint b'.2) _).const_mul _
  set A : ℝ := ∑ j, ∫ p, ‖columnSymbol Q r s j p‖ ∂μ with hA
  have hA0 : ∀ j, ∫ p, ‖columnSymbol Q r s j p‖ ∂μ ≤ A := by
    intro j
    exact Finset.single_le_sum (f := fun j => ∫ p, ‖columnSymbol Q r s j p‖ ∂μ)
      (fun j _ => integral_nonneg fun _ => norm_nonneg _) (Finset.mem_univ j)
  have hFn : ∀ b', ∫ p, ‖F b' p‖ ∂μ ≤ |Q b b'| * A := by
    intro b'
    have e : ∀ p, ‖F b' p‖ = |Q b b'| * ‖columnSymbol Q r s b'.2 p‖ := fun p => by
      simp only [hF, norm_mul, norm_planeWave, mul_one, Complex.norm_real, Real.norm_eq_abs]
    simp only [e]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hA0 _) (abs_nonneg _)
  have hsumF : Summable fun b' => ∫ p, ‖F b' p‖ ∂μ :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hFn ((hQsum b).mul_right A)
  have hs := hasSum_integral_of_summable_integral_norm hFint hsumF
  have hv : ∫ p, (∑' b', F b' p) ∂μ = ∫ p, planeWave (bondOffset r s b) p * (Complex.I * (planeSineVector p r s b.2 : ℂ)) ∂μ := by
    refine integral_congr_ae ?_
    have hbox : MeasurableSet brillouinBox := measurableSet_Icc
    rw [Filter.EventuallyEq, hμ, ae_restrict_iff' hbox]
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : Fin 4 → ℝ))] with q hq hqs
    exact (hasSum_row_columnSymbol hO hsym hblind hQsum hshift hrs hqs hq b).tsum_eq
  rw [hv] at hs
  have h2 := hs.mul_left (((2 * Real.pi : ℝ) : ℂ)⁻¹ ^ 4)
  rw [normalized_integral_unit_curl hrs b] at h2
  have hfun : (fun b' : IntBond => (Q b b' : ℂ) * fourierKernelAt (columnSymbol Q r s b'.2) (bondOffset r s b')) =
      fun b' => ((2 * Real.pi : ℝ) : ℂ)⁻¹ ^ 4 * ∫ p, F b' p ∂μ := by
    funext b'
    simp only [hF, fourierKernelAt_eq]
    rw [integral_const_mul]
    ring
  rw [hfun]
  exact h2
private theorem isLimitForm_translate {a cK c C : ℝ} {L k : ℕ} {Q : IntBond → IntBond → ℝ}
    (hQ : IsLimitForm a cK c C L k Q) (t : Fin 4 → ℤ) (b b' : IntBond) :
    Q (b.1 + t, b.2) (b'.1 + t, b'.2) = Q b b' := by
  have h := hQ.invariant ⟨Equiv.refl _, fun _ => 1, t, fun _ => Or.inl rfl⟩ b b'
  simp [bondImage] at h
  exact h
private theorem one_add_sqrt_intNormSq_le (x : Fin 4 → ℤ) (w : Fin 4 → ℝ) (h : ∀ l, |w l - x l| ≤ 1) :
    1 + Real.sqrt (intNormSq x) ≤ 4 * (1 + Real.sqrt (∑ l, w l ^ 2)) := by
  set W := Real.sqrt (∑ l, w l ^ 2) with hW
  have hS : 0 ≤ ∑ l, w l ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hW2 : W ^ 2 = ∑ l, w l ^ 2 := Real.sq_sqrt hS
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have h1 : ∀ l, ((x l : ℝ)) ^ 2 ≤ 2 * w l ^ 2 + 2 := by
    intro l
    have a := abs_le.1 (h l)
    nlinarith [sq_nonneg ((x l : ℝ) - 2 * w l), sq_nonneg (w l - x l), a.1, a.2]
  have h2 : intNormSq x ≤ 2 * W ^ 2 + 8 := by
    rw [hW2]
    simp only [intNormSq, Fin.sum_univ_four]
    linarith [h1 0, h1 1, h1 2, h1 3]
  have h3 : Real.sqrt (intNormSq x) ≤ 2 * W + 3 := by
    apply Real.sqrt_le_iff.2
    constructor
    · positivity
    · nlinarith
  linarith
private theorem zpow_neg_le_four_pow_mul_inv {u v : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) (h : u ≤ 4 * v) (k : ℕ) :
    v ^ (-(k : ℤ)) ≤ 4 ^ k * (u ^ k)⁻¹ := by
  rw [zpow_neg, zpow_natCast]
  have h1 : u ^ k ≤ (4 * v) ^ k := pow_le_pow_left₀ (by linarith) h k
  rw [mul_pow] at h1
  have hu' : 0 < u ^ k := by positivity
  have hv' : 0 < v ^ k := by positivity
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hv' hu']
  linarith
private theorem fourierKernelAt_add {a b : (Fin 4 → ℝ) → ℂ} (ha : IntegrableOn a brillouinBox) (hb : IntegrableOn b brillouinBox)
    (w : Fin 4 → ℝ) : fourierKernelAt (fun p => a p + b p) w = fourierKernelAt a w + fourierKernelAt b w := by
  simp only [fourierKernelAt_eq, add_mul]
  rw [integral_add (integrableOn_mul_planeWave ha w) (integrableOn_mul_planeWave hb w), mul_add]
private theorem columnSymbol_curl_eq {Q : IntBond → IntBond → ℝ} {m n' r s : Fin 4} (hmn : m ≠ n') (p : Fin 4 → ℝ) :
    columnSymbol Q r s m p * (-(Complex.I * (latticeSine p n' : ℂ))) + columnSymbol Q r s n' p * (Complex.I * (latticeSine p m : ℂ)) =
      curlColumnSymbol Q m n' r s p := by
  set v : Fin 4 → ℂ := fun i => ∑ j, (momentumSymbolMatrix Q p)⁻¹ i j * (planeSineVector p r s j : ℂ) with hv
  have h1 : ∀ i, columnSymbol Q r s i p = Complex.I * v i := fun i => rfl
  have h2 : curlColumnSymbol Q m n' r s p = ∑ i, (planeSineVector p m n' i : ℂ) * v i := by
    simp only [curlColumnSymbol, hv, Finset.mul_sum]
  have e : ∀ i, (planeSineVector p m n' i : ℂ) = (if i = m then (latticeSine p n' : ℂ) else 0) - (if i = n' then (latticeSine p m : ℂ) else 0) := by
    intro i
    simp only [planeSineVector]
    split_ifs <;> simp
  rw [h1, h1, h2]
  simp only [e, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hI := Complex.I_sq
  linear_combination (-(latticeSine p n' : ℂ) * v m + (latticeSine p m : ℂ) * v n') * hI
private theorem curlColumnSymbol_eq_add {Q : IntBond → IntBond → ℝ} (m n' r s : Fin 4) (p : Fin 4 → ℝ) :
    curlColumnSymbol Q m n' r s p = defectSandwich Q m n' r s p + curlProjectionSymbol m n' r s p := by
  simp only [curlColumnSymbol, defectSandwich, curlProjectionSymbol, inverseSymbolDefect]
  push_cast
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∑ j, (planeSineVector p m n' i : ℂ) * (((momentumSymbolMatrix Q p)⁻¹ i j - if i = j then (latticeSineNormSq p : ℂ)⁻¹ else 0) * (planeSineVector p r s j : ℂ)) =
      ∑ j, (planeSineVector p m n' i : ℂ) * ((momentumSymbolMatrix Q p)⁻¹ i j * (planeSineVector p r s j : ℂ)) -
        (planeSineVector p m n' i : ℂ) * (latticeSineNormSq p : ℂ)⁻¹ * (planeSineVector p r s i : ℂ) := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
    congr 1
    simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  rw [h1, div_eq_mul_inv]
  ring
private theorem mul_zpow_le_four_pow_mul_inv {C v u : ℝ} {e : ℤ} (k : ℕ) (he : e = -(k : ℤ)) (hu : 1 ≤ u) (hv : 1 ≤ v) (h : u ≤ 4 * v) :
    C * v ^ e ≤ (4 ^ k * |C|) * (u ^ k)⁻¹ := by
  subst he
  have h1 := zpow_neg_le_four_pow_mul_inv hu hv h k
  have h2 : 0 < v ^ (-(k : ℤ)) := zpow_pos (by linarith) _
  calc C * v ^ (-(k : ℤ)) ≤ |C| * v ^ (-(k : ℤ)) := mul_le_mul_of_nonneg_right (le_abs_self _) h2.le
    _ ≤ |C| * (4 ^ k * (u ^ k)⁻¹) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = _ := by ring
private theorem mul_of_periodic_twist {a : (Fin 4 → ℝ) → ℂ} {p q : Fin 4 → ℝ} {x : ℂ} {e : ℝ} (he : e * e = 1)
    (h1 : a q = (e : ℂ) * a p) (h2 : x = (e : ℂ)) : a q * x = a p := by
  have h3 : ((e : ℝ) : ℂ) * (e : ℂ) = 1 := by exact_mod_cast he
  rw [h1, h2]
  linear_combination (a p) * h3
private theorem axisSign_four_mul_self (l a b c d : Fin 4) : (axisSign l a * axisSign l b * axisSign l c * axisSign l d) * (axisSign l a * axisSign l b * axisSign l c * axisSign l d) = 1 := by
  have h1 := axisSign_mul_self l a
  have h2 := axisSign_mul_self l b
  have h3 := axisSign_mul_self l c
  have h4 := axisSign_mul_self l d
  calc _ = (axisSign l a * axisSign l a) * (axisSign l b * axisSign l b) * (axisSign l c * axisSign l c) * (axisSign l d * axisSign l d) := by ring
    _ = 1 := by rw [h1, h2, h3, h4]; norm_num
private theorem axisSign_three_mul_self (l a b c : Fin 4) : (axisSign l a * axisSign l b * axisSign l c) * (axisSign l a * axisSign l b * axisSign l c) = 1 := by
  have h1 := axisSign_mul_self l a
  have h2 := axisSign_mul_self l b
  have h3 := axisSign_mul_self l c
  calc _ = (axisSign l a * axisSign l a) * (axisSign l b * axisSign l b) * (axisSign l c * axisSign l c) := by ring
    _ = 1 := by rw [h1, h2, h3]; norm_num
private theorem one_le_one_add_sqrt_sum_sq (w : Fin 4 → ℝ) : 1 ≤ 1 + Real.sqrt (∑ l, w l ^ 2) := by
  have := Real.sqrt_nonneg (∑ l, w l ^ 2)
  linarith
private theorem one_le_one_add_sqrt_intNormSq (z : Fin 4 → ℤ) : 1 ≤ 1 + Real.sqrt (intNormSq z) := by
  have := Real.sqrt_nonneg (intNormSq z)
  linarith
abbrev _root_.YangMills.DeltaSharedProofs.p500919 := @one_le_one_add_sqrt_intNormSq
set_option maxHeartbeats 4000000 in
private theorem greenColumn_of_bounds (Tb : RenormalizationStepParameters.ParameterAssignment)
    (hO : ∀ c₁ C₁ : ℝ, 0 < c₁ → ∃ Cs : ℕ → ℝ, ∀ (k : ℕ) (Q : IntBond → IntBond → ℝ),
      IsLimitForm Tb.coupling Tb.coercivity c₁ C₁ Tb.side k Q → InverseSymbolOrders Cs Q)
    (hB : ∀ c₁ C₁ : ℝ, 0 < c₁ → ∃ D : ℕ → ℝ, ∀ (k : ℕ) (Q : IntBond → IntBond → ℝ),
      IsLimitForm Tb.coupling Tb.coercivity c₁ C₁ Tb.side k Q →
      (∀ (i j l : Fin 4) (d : ℕ) (p : Fin 4 → ℝ),
        ‖iteratedDeriv d (fun t : ℝ => midpointSymbol Q i j (Function.update p l t)) (p l)‖ ≤ D d) ∧
      (∀ (i j : Fin 4) (p : Fin 4 → ℝ), (midpointSymbol Q i j p).im = 0) ∧
      (∀ (i j : Fin 4) (p : Fin 4 → ℝ), midpointSymbol Q i j p = midpointSymbol Q j i p) ∧
      ∀ (i : Fin 4) (p : Fin 4 → ℝ),
        ∑ j, (midpointSymbol Q i j p - ((4 * Real.sin (p i / 2) * Real.sin (p j / 2) : ℝ) : ℂ)) *
          ((2 * Real.sin (p j / 2) : ℝ) : ℂ) = 0)
    (hDec : symbolKernelDecayStatement) (hK : curlProjectionKernelStatement) :
    ∀ c₁ C₁ : ℝ, 0 < c₁ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (Q : IntBond → IntBond → ℝ),
    IsLimitForm Tb.coupling Tb.coercivity c₁ C₁ Tb.side k Q → ∀ r s : Fin 4, r < s → ∃ B : IntBond → ℝ,
      (∀ b : IntBond, HasSum (fun b' => Q b b' * B b') (intCurl (Pi.single b 1) (0, r, s))) ∧
      (∀ b : IntBond, |B b| ≤ C * ((1 + Real.sqrt (intNormSq b.1)) ^ 3)⁻¹) ∧
      ∀ (z : Fin 4 → ℤ) (m n' : Fin 4), m < n' →
        |intCurl B (z, m, n')| ≤ C * ((1 + Real.sqrt (intNormSq z)) ^ 4)⁻¹ ∧
        (z ≠ 0 → |intCurl B (z, m, n') - maxwellKernel z m n' r s| ≤
          C * ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹) := by
  intro c₁ C₁ hc₁
  obtain ⟨Cs, hOs⟩ := hO c₁ C₁ hc₁
  obtain ⟨D, hBs⟩ := hB c₁ C₁ hc₁
  obtain ⟨Ca, hCa⟩ := hDec (-1) (columnBounds Cs) (by norm_num)
  obtain ⟨Cb, hCb⟩ := hDec 0 (sandwichBounds Cs) (by norm_num)
  obtain ⟨Cc, hCc⟩ := hDec 1 (sandwichBounds Cs) (by norm_num)
  obtain ⟨Ck, hCk⟩ := hK
  refine ⟨64 * |Ca| + 256 * |Cb| + 1024 * |Cc| + |Ck|, by positivity, fun k Q hQ r s hrs => ?_⟩
  set Cf : ℝ := 64 * |Ca| + 256 * |Cb| + 1024 * |Cc| + |Ck| with hCf
  have hOQ := hOs k Q hQ
  obtain ⟨-, -, hsym, hbl⟩ := hBs k Q hQ
  have hrs' : r ≠ s := hrs.ne
  have hQsum : ∀ b, Summable fun b' => |Q b b'| := by
    intro b
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun b' => hQ.decay b b') ?_
    exact (summable_exp_neg_bondSupDist hc₁ b).mul_left C₁
  have hshift := isLimitForm_translate hQ
  have hcolI : ∀ j, IntegrableOn (columnSymbol Q r s j) brillouinBox := fun j =>
    integrableOn_of_norm_inv_bound (B₀ := 49 * |columnBounds Cs 0|) (fun p hp hp0 => (contDiffAt_columnSymbol hOQ r s j hp hp0 0).continuousAt)
      (fun p hp hp0 => norm_le_of_hasScaledJet (l := 0) hp hp0 (hasScaledJet_columnSymbol hOQ r s j 0 hp hp0) (by norm_num) (by norm_num))
  have hcurlI : ∀ m n', IntegrableOn (curlColumnSymbol Q m n' r s) brillouinBox := fun m n' =>
    integrableOn_of_norm_inv_bound (B₀ := 49 * |sandwichBounds Cs 0|) (fun p hp hp0 => (contDiffAt_curlColumnSymbol hOQ m n' r s hp hp0 0).continuousAt)
      (fun p hp hp0 => norm_le_of_hasScaledJet (l := 0) hp hp0 (hasScaledJet_curlColumnSymbol hOQ m n' r s 0 hp hp0) (by norm_num) (by norm_num))
  have hdefI : ∀ m n', IntegrableOn (defectSandwich Q m n' r s) brillouinBox := fun m n' =>
    integrableOn_of_norm_inv_bound (B₀ := 49 * |sandwichBounds Cs 0|) (fun p hp hp0 => (contDiffAt_defectSandwich hOQ m n' r s hp hp0 0).continuousAt)
      (fun p hp hp0 => norm_le_of_hasScaledJet (l := 0) hp hp0 (hasScaledJet_defectSandwich hOQ m n' r s 0 hp hp0) (by norm_num) (by norm_num))
  set Bf : IntBond → ℝ := fun b => (fourierKernelAt (columnSymbol Q r s b.2) (bondOffset r s b)).re with hBf
  refine ⟨Bf, fun b => ?_, fun b => ?_, fun z m n' hmn => ?_⟩
  · have h1 := Complex.reCLM.hasSum (hasSum_column_equation hOQ hsym hbl hQsum hshift hrs' hcolI b)
    simp only [Complex.reCLM_apply, Complex.ofReal_re, Complex.re_ofReal_mul] at h1
    exact h1
  · have hk := hCa (columnSymbol Q r s b.2) (bondOffset r s b)
      (fun l p => mul_of_periodic_twist (axisSign_three_mul_self l b.2 r s) (columnSymbol_add_period Q hrs' b.2 l p) (exp_two_pi_bondOffset r s b l))
      (fun j p hp hp0 => contDiffAt_columnSymbol hOQ r s b.2 hp hp0 j)
      (fun l j p hp hp0 => (hasScaledJet_columnSymbol hOQ r s b.2 l hp hp0 j).2)
    have hnear : 1 + Real.sqrt (intNormSq b.1) ≤ 4 * (1 + Real.sqrt (∑ l, bondOffset r s b l ^ 2)) := by
      refine one_add_sqrt_intNormSq_le b.1 _ fun l => ?_
      simp only [bondOffset]
      rw [abs_le]
      split_ifs <;> constructor <;> linarith
    have hc := mul_zpow_le_four_pow_mul_inv (C := Ca) (e := -4 - (-1)) 3 (by norm_num) (one_le_one_add_sqrt_intNormSq b.1) (one_le_one_add_sqrt_sum_sq _) hnear
    have h1 : |Bf b| ≤ ‖fourierKernelAt (columnSymbol Q r s b.2) (bondOffset r s b)‖ := Complex.abs_re_le_norm _
    have h2 : (4 ^ 3 * |Ca|) * ((1 + Real.sqrt (intNormSq b.1)) ^ 3)⁻¹ ≤ Cf * ((1 + Real.sqrt (intNormSq b.1)) ^ 3)⁻¹ := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      simp only [hCf]
      have := abs_nonneg Cb
      have := abs_nonneg Cc
      have := abs_nonneg Ck
      norm_num
      linarith
    exact h1.trans ((hk.trans hc).trans h2)
  · set W := plaquetteBarycentreShift z m n' r s with hW
    have hhalf : ∀ l, |W l - z l| ≤ 1 := by
      intro l
      simp only [hW, plaquetteBarycentreShift]
      rw [abs_le]
      split_ifs <;> constructor <;> linarith
    have hnear := one_add_sqrt_intNormSq_le z W hhalf
    have hmn' : m ≠ n' := hmn.ne
    have w1 : bondOffset r s (z, m) = W + -Pi.single n' (1 / 2) := by
      funext l
      simp only [bondOffset, hW, plaquetteBarycentreShift, Pi.add_apply, Pi.neg_apply, Pi.single_apply]
      split_ifs <;> ring
    have w2 : bondOffset r s (z + Pi.single m 1, n') = W + Pi.single m (1 / 2) := by
      funext l
      simp only [bondOffset, hW, plaquetteBarycentreShift, Pi.add_apply, Pi.single_apply]
      push_cast
      split_ifs <;> ring
    have w3 : bondOffset r s (z + Pi.single n' 1, m) = W + Pi.single n' (1 / 2) := by
      funext l
      simp only [bondOffset, hW, plaquetteBarycentreShift, Pi.add_apply, Pi.single_apply]
      push_cast
      split_ifs <;> ring
    have w4 : bondOffset r s (z, n') = W + -Pi.single m (1 / 2) := by
      funext l
      simp only [bondOffset, hW, plaquetteBarycentreShift, Pi.add_apply, Pi.neg_apply, Pi.single_apply]
      split_ifs <;> ring
    have key : ∀ p, columnSymbol Q r s m p * planeWave (bondOffset r s (z, m)) p + columnSymbol Q r s n' p * planeWave (bondOffset r s (z + Pi.single m 1, n')) p -
        columnSymbol Q r s m p * planeWave (bondOffset r s (z + Pi.single n' 1, m)) p - columnSymbol Q r s n' p * planeWave (bondOffset r s (z, n')) p =
        curlColumnSymbol Q m n' r s p * planeWave W p := by
      intro p
      rw [w1, w2, w3, w4, planeWave_add, planeWave_add, planeWave_add, planeWave_add, ← columnSymbol_curl_eq hmn' p, I_mul_latticeSine, I_mul_latticeSine]
      ring
    have hid : intCurl Bf (z, m, n') = (fourierKernelAt (curlColumnSymbol Q m n' r s) W).re := by
      have h1 : fourierKernelAt (columnSymbol Q r s m) (bondOffset r s (z, m)) + fourierKernelAt (columnSymbol Q r s n') (bondOffset r s (z + Pi.single m 1, n')) -
          fourierKernelAt (columnSymbol Q r s m) (bondOffset r s (z + Pi.single n' 1, m)) - fourierKernelAt (columnSymbol Q r s n') (bondOffset r s (z, n')) =
          fourierKernelAt (curlColumnSymbol Q m n' r s) W := by
        have i1 := integrableOn_mul_planeWave (hcolI m) (bondOffset r s (z, m))
        have i2 := integrableOn_mul_planeWave (hcolI n') (bondOffset r s (z + Pi.single m 1, n'))
        have i3 := integrableOn_mul_planeWave (hcolI m) (bondOffset r s (z + Pi.single n' 1, m))
        have i4 := integrableOn_mul_planeWave (hcolI n') (bondOffset r s (z, n'))
        have e1 : ∫ p in brillouinBox, curlColumnSymbol Q m n' r s p * planeWave W p =
            (∫ p in brillouinBox, columnSymbol Q r s m p * planeWave (bondOffset r s (z, m)) p) +
            (∫ p in brillouinBox, columnSymbol Q r s n' p * planeWave (bondOffset r s (z + Pi.single m 1, n')) p) -
            (∫ p in brillouinBox, columnSymbol Q r s m p * planeWave (bondOffset r s (z + Pi.single n' 1, m)) p) -
            ∫ p in brillouinBox, columnSymbol Q r s n' p * planeWave (bondOffset r s (z, n')) p := by
          have x12 : IntegrableOn (fun p => columnSymbol Q r s m p * planeWave (bondOffset r s (z, m)) p +
              columnSymbol Q r s n' p * planeWave (bondOffset r s (z + Pi.single m 1, n')) p) brillouinBox := i1.add i2
          have x123 : IntegrableOn (fun p => columnSymbol Q r s m p * planeWave (bondOffset r s (z, m)) p +
              columnSymbol Q r s n' p * planeWave (bondOffset r s (z + Pi.single m 1, n')) p -
              columnSymbol Q r s m p * planeWave (bondOffset r s (z + Pi.single n' 1, m)) p) brillouinBox := x12.sub i3
          simp only [← key]
          rw [integral_sub x123 i4, integral_sub x12 i3, integral_add i1 i2]
        simp only [fourierKernelAt_eq]
        rw [e1]
        ring
      rw [← h1]
      simp only [intCurl, hBf, Complex.add_re, Complex.sub_re]
    have hk := hCb (curlColumnSymbol Q m n' r s) W
      (fun l p => mul_of_periodic_twist (axisSign_four_mul_self l m n' r s) (curlColumnSymbol_add_period Q hmn' hrs' l p) (exp_two_pi_plaquetteBarycentreShift z m n' r s l))
      (fun j p hp hp0 => contDiffAt_curlColumnSymbol hOQ m n' r s hp hp0 j)
      (fun l j p hp hp0 => (hasScaledJet_curlColumnSymbol hOQ m n' r s l hp hp0 j).2)
    have hc := mul_zpow_le_four_pow_mul_inv (C := Cb) (e := -4 - 0) 4 (by norm_num) (one_le_one_add_sqrt_intNormSq z) (one_le_one_add_sqrt_sum_sq _) hnear
    refine ⟨?_, fun hz => ?_⟩
    · rw [hid]
      have h1 : |(fourierKernelAt (curlColumnSymbol Q m n' r s) W).re| ≤ ‖fourierKernelAt (curlColumnSymbol Q m n' r s) W‖ := Complex.abs_re_le_norm _
      have h2 : (4 ^ 4 * |Cb|) * ((1 + Real.sqrt (intNormSq z)) ^ 4)⁻¹ ≤ Cf * ((1 + Real.sqrt (intNormSq z)) ^ 4)⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        simp only [hCf]
        have := abs_nonneg Ca
        have := abs_nonneg Cc
        have := abs_nonneg Ck
        norm_num
        linarith
      exact h1.trans ((hk.trans hc).trans h2)
    · rw [hid]
      have hl := hCk z m n' r s hmn hrs hz
      have hlatI : IntegrableOn (curlProjectionSymbol m n' r s) brillouinBox := by
        have h3 := (hcurlI m n').sub (hdefI m n')
        refine h3.congr (ae_of_all _ fun p => ?_)
        simp only [Pi.sub_apply, curlColumnSymbol_eq_add (Q := Q) m n' r s p]
        ring
      have hsp : fourierKernelAt (curlColumnSymbol Q m n' r s) W =
          fourierKernelAt (defectSandwich Q m n' r s) W + fourierKernelAt (curlProjectionSymbol m n' r s) W := by
        rw [← fourierKernelAt_add (hdefI m n') hlatI W]
        congr 1
        funext p
        exact curlColumnSymbol_eq_add m n' r s p
      have hd := hCc (defectSandwich Q m n' r s) W
        (fun l p => mul_of_periodic_twist (axisSign_four_mul_self l m n' r s) (defectSandwich_add_period Q hmn' hrs' l p) (exp_two_pi_plaquetteBarycentreShift z m n' r s l))
        (fun j p hp hp0 => contDiffAt_defectSandwich hOQ m n' r s hp hp0 j)
        (fun l j p hp hp0 => (hasScaledJet_defectSandwich hOQ m n' r s l hp hp0 j).2)
      have hc5 := mul_zpow_le_four_pow_mul_inv (C := Cc) (e := -4 - 1) 5 (by norm_num) (one_le_one_add_sqrt_intNormSq z) (one_le_one_add_sqrt_sum_sq _) hnear
      have h1 : |(fourierKernelAt (curlColumnSymbol Q m n' r s) W).re - maxwellKernel z m n' r s| ≤
          ‖fourierKernelAt (curlColumnSymbol Q m n' r s) W - (maxwellKernel z m n' r s : ℂ)‖ := by
        have := Complex.abs_re_le_norm (fourierKernelAt (curlColumnSymbol Q m n' r s) W - (maxwellKernel z m n' r s : ℂ))
        simpa using this
      refine h1.trans ?_
      rw [hsp, add_sub_assoc]
      refine (norm_add_le _ _).trans ?_
      have hu5 : 0 ≤ ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹ := by
        have := one_le_one_add_sqrt_intNormSq z
        positivity
      have h5 : |Ck| * ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹ ≥ Ck * ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hu5
      have h6 : (4 ^ 5 * |Cc|) * ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹ + |Ck| * ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹ ≤
          Cf * ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹ := by
        rw [← add_mul]
        refine mul_le_mul_of_nonneg_right ?_ hu5
        simp only [hCf]
        have := abs_nonneg Ca
        have := abs_nonneg Cb
        norm_num
        linarith
      have h7 : ‖fourierKernelAt (defectSandwich Q m n' r s) W‖ ≤ (4 ^ 5 * |Cc|) * ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹ := hd.trans hc5
      linarith
theorem greenColumnStatement_holds (h1 : inverseSymbolOrdersStatement) (h2 : symbolDerivBoundsStatement)
    (h3 : symbolKernelDecayStatement) (h4 : curlProjectionKernelStatement) : greenColumnStatement := by
  intro a ha
  obtain ⟨L₁, r₁, hr₁, H₁⟩ := h1 a ha
  obtain ⟨L₂, r₂, hr₂, H₂⟩ := h2 a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hL hLL T hTa hTL hD hrt
  obtain ⟨y₁, G₁⟩ := H₁ L hL (le_trans (le_max_left _ _) hLL) T hTa hTL hD (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, G₂⟩ := H₂ L hL (le_trans (le_max_right _ _) hLL) T hTa hTL hD (hrt.trans (min_le_right _ _))
  refine ⟨max y₁ y₂, fun y hy hret hrow => ?_⟩
  exact greenColumn_of_bounds T (G₁ y (le_trans (le_max_left _ _) hy) hret hrow) (G₂ y (le_trans (le_max_right _ _) hy) hret hrow) h3 h4
end YangMills.Construction.LimitForms
end
