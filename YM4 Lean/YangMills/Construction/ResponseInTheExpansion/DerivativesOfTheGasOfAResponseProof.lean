import YangMills.Construction.ClusterExpansionOfAStep.ColdAlongAMove
import YangMills.Construction.ClusterExpansionOfAStep.JetsOfAMarkedFamilyProof
import YangMills.Construction.ResponseInTheExpansion.DerivativesOfTheGasOfAResponse
import YangMills.Construction.ResponseInTheExpansion.KernelsAtBasesAlongAMove
import YangMills.Construction.ResponseInTheExpansion.MarkedMeansAlongAMove
import YangMills.Construction.ResponseInTheExpansion.PartsOfTheGasAreColdMeans
import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open MeasureTheory
namespace YangMills.Construction
open BlockAverages WeightedResponses StepSettings StepGas StepCosts RenormalizationStepParameters TorusFields TorusLumps ParametricIntegral
namespace ResponseInTheExpansion
namespace GasJets
section Calculus
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem norm_iteratedFDeriv_sum_le {ι : Type} (s : Finset ι) (f : ι → E → ℝ) (x : E) (j : ℕ)
    (h : ∀ i ∈ s, ContDiffAt ℝ j (f i) x) :
    ‖iteratedFDeriv ℝ j (fun y => ∑ i ∈ s, f i y) x‖ ≤ ∑ i ∈ s, ‖iteratedFDeriv ℝ j (f i) x‖ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : (fun y : E => ∑ i ∈ (∅ : Finset ι), f i y) = fun _ => (0 : ℝ) := by simp
    rw [e]
    have : iteratedFDeriv ℝ j (fun _ : E => (0 : ℝ)) x = 0 := by
      have := iteratedFDeriv_fun_zero (𝕜 := ℝ) (E := E) (F := ℝ) (n := j)
      exact congrFun this x
    simp [this]
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, ContDiffAt ℝ j (f i) x := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have e : (fun y : E => ∑ i ∈ insert a s, f i y) = f a + fun y => ∑ i ∈ s, f i y := by
      funext y
      rw [Finset.sum_insert ha]
      rfl
    rw [e, iteratedFDeriv_add_apply (h a (Finset.mem_insert_self _ _)) (ContDiffAt.sum hs), Finset.sum_insert ha]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (ih hs))
theorem add_le_two_mul_mul {Q P : ℝ} (hQ : 1 ≤ Q) (hP : 1 ≤ P) : Q + P ≤ 2 * Q * P := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hQ) (sub_nonneg.mpr hP)]
theorem norm_iteratedFDeriv_mul_le_pow {f g : E → ℝ} {x : E} (hf : ContDiff ℝ 40 f) (hg : ContDiff ℝ 40 g) {Q P Bf Bg : ℝ}
    (hQ : 1 ≤ Q) (hP : 1 ≤ P) (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg) (hfj : ∀ i ≤ 40, ‖iteratedFDeriv ℝ i f x‖ ≤ Q ^ i * Bf)
    (hgj : ∀ i ≤ 40, ‖iteratedFDeriv ℝ i g x‖ ≤ P ^ i * Bg) {j : ℕ} (hj : j ≤ 40) :
    ‖iteratedFDeriv ℝ j (fun y => f y * g y) x‖ ≤ (2 * Q * P) ^ j * (Bf * Bg) := by
  have hj' : ((j : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast hj
  refine (norm_iteratedFDeriv_mul_le hf hg x hj').trans ?_
  calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (Q ^ i * Bf) * (P ^ (j - i) * Bg) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        refine mul_le_mul (mul_le_mul_of_nonneg_left (hfj i (hi'.trans hj)) (Nat.cast_nonneg _))
          (hgj _ ((Nat.sub_le _ _).trans hj)) (norm_nonneg _) (by positivity)
    _ = (Q + P) ^ j * (Bf * Bg) := by
        rw [add_pow, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ (2 * Q * P) ^ j * (Bf * Bg) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (add_le_two_mul_mul hQ hP) j) (by positivity)
theorem norm_iteratedFDeriv_const_mul {c : ℝ} (hc : 0 ≤ c) {f : E → ℝ} {j : ℕ} {τ : E} (hf : ContDiffAt ℝ j f τ) :
    ‖iteratedFDeriv ℝ j (fun σ => c * f σ) τ‖ = c * ‖iteratedFDeriv ℝ j f τ‖ := by apply _root_.YangMills.Construction.PolymerCumulant.norm_iteratedFDeriv_const_mul <;> assumption
theorem norm_iteratedFDeriv_const_le (c : ℝ) (τ : E) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun _ : E => c) τ‖ ≤ 1 ^ i * |c| := by
  rcases Nat.eq_zero_or_pos i with rfl | h
  · simp [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne (by omega)]
    simp
def quotientConstant : ℝ :=
  2 ^ 40 * ((Nat.factorial 40 : ℝ) * ∑ i ∈ Finset.range 41, ‖iteratedFDerivWithin ℝ i (fun y : ℝ => y⁻¹) (Set.Ioi 0) 1‖)
theorem quotientConstant_nonneg : 0 ≤ quotientConstant := by
  unfold quotientConstant
  positivity
theorem norm_iteratedFDeriv_div_le {k : ℕ} {U : Set (Fin k → ℝ)} (hU : IsOpen U) {x₀ : Fin k → ℝ} (hx₀ : x₀ ∈ U)
    {u z : (Fin k → ℝ) → ℝ} (hu : ContDiffOn ℝ 40 u U) (hz : ContDiffOn ℝ 40 z U) (hzp : ∀ x ∈ U, 0 < z x) {D B : ℝ}
    (hD : 1 ≤ D) (hB : 0 ≤ B) (huj : ∀ i ≤ 40, ‖iteratedFDeriv ℝ i u x₀‖ ≤ D ^ i * (B * z x₀))
    (hzj : ∀ i ≤ 40, ‖iteratedFDeriv ℝ i z x₀‖ ≤ D ^ i * z x₀) :
    ContDiffAt ℝ 40 (fun x => u x / z x) x₀ ∧
      ‖iteratedFDeriv ℝ 40 (fun x => u x / z x) x₀‖ ≤ quotientConstant * B * D ^ 40 := by
  have hud : UniqueDiffOn ℝ U := hU.uniqueDiffOn
  have hz₀ : 0 < z x₀ := hzp x₀ hx₀
  set z₀ := z x₀ with hz₀d
  have hnh : U ∈ 𝓝 x₀ := hU.mem_nhds hx₀
  have hcat : ContDiffAt ℝ 40 (fun x => u x / z x) x₀ :=
    (hu.contDiffAt hnh).div (hz.contDiffAt hnh) hz₀.ne'
  refine ⟨hcat, ?_⟩
  set w : (Fin k → ℝ) → ℝ := fun x => z₀⁻¹ * z x with hw
  set v : (Fin k → ℝ) → ℝ := (fun y : ℝ => y⁻¹) ∘ w with hv
  set u' : (Fin k → ℝ) → ℝ := fun x => z₀⁻¹ * u x with hu'
  have hz₀i : 0 ≤ z₀⁻¹ := (inv_pos.mpr hz₀).le
  have hws : ContDiffOn ℝ 40 w U := contDiffOn_const.mul hz
  have hu's : ContDiffOn ℝ 40 u' U := contDiffOn_const.mul hu
  have hw1 : w x₀ = 1 := inv_mul_cancel₀ hz₀.ne'
  have hmaps : Set.MapsTo w U (Set.Ioi 0) := fun x hx => mul_pos (inv_pos.mpr hz₀) (hzp x hx)
  have hinv : ContDiffOn ℝ 40 (fun y : ℝ => y⁻¹) (Set.Ioi 0) := fun y hy =>
    (contDiffAt_inv ℝ (ne_of_gt hy)).contDiffWithinAt
  have hvs : ContDiffOn ℝ 40 v U := hinv.comp hws hmaps
  set Ci : ℝ := ∑ i ∈ Finset.range 41, ‖iteratedFDerivWithin ℝ i (fun y : ℝ => y⁻¹) (Set.Ioi 0) 1‖ with hCi
  have hCi0 : 0 ≤ Ci := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hwj : ∀ i, i ≤ 40 → ‖iteratedFDeriv ℝ i w x₀‖ ≤ D ^ i := by
    intro i hi
    have hi' : ((i : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast hi
    have hat : ContDiffAt ℝ i z x₀ := (hz.of_le hi').contDiffAt hnh
    rw [hw, norm_iteratedFDeriv_const_mul hz₀i hat]
    calc z₀⁻¹ * ‖iteratedFDeriv ℝ i z x₀‖ ≤ z₀⁻¹ * (D ^ i * z₀) := mul_le_mul_of_nonneg_left (hzj i hi) hz₀i
      _ = D ^ i := by field_simp
  have hvj : ∀ i, i ≤ 40 → ‖iteratedFDeriv ℝ i v x₀‖ ≤ (Nat.factorial 40 : ℝ) * Ci * D ^ i := by
    intro i hi
    have hi' : ((i : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast hi
    rw [← iteratedFDerivWithin_of_isOpen i hU hx₀]
    have h1 := norm_iteratedFDerivWithin_comp_le (g := fun y : ℝ => y⁻¹) (f := w) (n := i) (s := U) (t := Set.Ioi 0)
      (x := x₀) (N := 40) (C := Ci) (D := D) hinv hws hi' isOpen_Ioi.uniqueDiffOn hud hmaps hx₀
      (fun j hj => by
        rw [hw1]
        exact Finset.single_le_sum (f := fun i => ‖iteratedFDerivWithin ℝ i (fun y : ℝ => y⁻¹) (Set.Ioi 0) 1‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega)))
      (fun j _ hj => by
        rw [iteratedFDerivWithin_of_isOpen j hU hx₀]
        exact hwj j (hj.trans hi))
    refine h1.trans ?_
    have hf1 : (Nat.factorial i : ℝ) ≤ Nat.factorial 40 := by exact_mod_cast Nat.factorial_le hi
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf1 hCi0) (by positivity)
  have hu'j : ∀ i, i ≤ 40 → ‖iteratedFDeriv ℝ i u' x₀‖ ≤ D ^ i * B := by
    intro i hi
    have hi' : ((i : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast hi
    have hat : ContDiffAt ℝ i u x₀ := (hu.of_le hi').contDiffAt hnh
    rw [hu', norm_iteratedFDeriv_const_mul hz₀i hat]
    calc z₀⁻¹ * ‖iteratedFDeriv ℝ i u x₀‖ ≤ z₀⁻¹ * (D ^ i * (B * z₀)) := mul_le_mul_of_nonneg_left (huj i hi) hz₀i
      _ = D ^ i * B := by field_simp
  have heq : (fun x => u x / z x) = fun x => u' x * v x := by
    funext x
    simp only [hu', hv, hw, Function.comp, mul_inv, inv_inv]
    field_simp
  rw [heq, ← iteratedFDerivWithin_of_isOpen 40 hU hx₀]
  refine (norm_iteratedFDerivWithin_mul_le hu's hvs hud hx₀ (n := 40) (by norm_num)).trans ?_
  calc ∑ i ∈ Finset.range 41, ((40 : ℕ).choose i : ℝ) * ‖iteratedFDerivWithin ℝ i u' U x₀‖ *
        ‖iteratedFDerivWithin ℝ (40 - i) v U x₀‖
      ≤ ∑ i ∈ Finset.range 41, ((40 : ℕ).choose i : ℝ) * (D ^ i * B) *
          ((Nat.factorial 40 : ℝ) * Ci * D ^ (40 - i)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ 40 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [iteratedFDerivWithin_of_isOpen i hU hx₀, iteratedFDerivWithin_of_isOpen _ hU hx₀]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hu'j i hi') (Nat.cast_nonneg _))
          (hvj _ (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = ∑ i ∈ Finset.range 41, ((40 : ℕ).choose i : ℝ) * ((Nat.factorial 40 : ℝ) * Ci * B * D ^ 40) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i ≤ 40 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have e : D ^ 40 = D ^ i * D ^ (40 - i) := by rw [← pow_add]; congr 1; omega
        rw [e]
        ring
    _ = quotientConstant * B * D ^ 40 := by
        rw [← Finset.sum_mul]
        have h2 : ∑ i ∈ Finset.range 41, ((40 : ℕ).choose i : ℝ) = 2 ^ 40 := by
          have := Nat.sum_range_choose 40
          exact_mod_cast this
        rw [h2]
        unfold quotientConstant
        ring
end Calculus
section Configurations
variable {R : StepSetup} {n : ℕ} [NeZero n]
abbrev ConfigFunction (R : StepSetup) (n : ℕ) : Type :=
  (Yt : Finset (TorusSite (n * R.params.side))) → BaseChoice R.params.side n →
    TorusField (n * R.params.side) × (Yt → R.labels.Ω) → ℝ
structure KernelProductBounds {k : ℕ} (R : StepSetup) (Vt : (Fin k → ℝ) → TorusField n) (τ₀ : Fin k → ℝ) (P κ : ℝ) :
    Prop where
  contDiff : ∀ (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n),
    ContDiff ℝ 40 (fun τ => kernelProduct R.params R.coupling W (Vt τ) b)
  pos : ∀ (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) τ,
    0 < kernelProduct R.params R.coupling W (Vt τ) b
  jets_le : ∀ (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) τ, ∀ i ≤ 40,
    ‖iteratedFDeriv ℝ i (fun τ' => kernelProduct R.params R.coupling W (Vt τ') b) τ‖ ≤
      P ^ i * kernelProduct R.params R.coupling W (Vt τ) b
  ratio_le : ∀ (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) τ,
    kernelProduct R.params R.coupling W (Vt τ) b ≤ κ * kernelProduct R.params R.coupling W (Vt τ₀) b
  one_le_rate : 1 ≤ P
  ratio_nonneg : 0 ≤ κ
theorem coldWeightedIntegral_jets (hD : ContDiffOnIntegralStatement) {k : ℕ} {Vt : (Fin k → ℝ) → TorusField n}
    {U : Set (Fin k → ℝ)} (hU : IsOpen U) {τ₀ : Fin k → ℝ} (hτ₀ : τ₀ ∈ U) {P κ Q : ℝ}
    (hK : KernelProductBounds R Vt τ₀ P κ) (hQ : 1 ≤ Q)
    (hd : ∀ (Yt : Finset (TorusSite (n * R.params.side))) b p, 0 ≤ hullBaseDensity R Yt b p)
    {f : (Fin k → ℝ) → ConfigFunction R n} {Bf : ConfigFunction R n}
    (hf : ∀ Yt b p, ContDiff ℝ 40 (fun τ => f τ Yt b p))
    (hfj : ∀ Yt b p τ, ∀ i ≤ 40, ‖iteratedFDeriv ℝ i (fun τ' => f τ' Yt b p) τ‖ ≤ Q ^ i * Bf Yt b p)
    (hB0 : ∀ Yt b p, 0 ≤ Bf Yt b p)
    (hint : ∀ τ ∈ U, ∀ Yt b, Integrable (coldIntegrand R (Vt τ) (f τ) Yt b) (fieldLabelMeasure R n Yt))
    (hBint : ∀ Yt b, Integrable (coldIntegrand R (Vt τ₀) Bf Yt b) (fieldLabelMeasure R n Yt)) :
    ContDiffOn ℝ 40 (fun τ => coldWeightedIntegral R (Vt τ) (f τ)) U ∧
      ∀ i ≤ 40, ‖iteratedFDeriv ℝ i (fun τ => coldWeightedIntegral R (Vt τ) (f τ)) τ₀‖ ≤
        (2 * Q * P) ^ i * coldWeightedIntegral R (Vt τ₀) Bf := by
  have hP := hK.one_le_rate
  have hD1 : 1 ≤ 2 * Q * P := by nlinarith
  have hpiece : ∀ Yt b, ContDiffOn ℝ 40
      (fun τ => ∫ p, coldIntegrand R (Vt τ) (f τ) Yt b p ∂fieldLabelMeasure R n Yt) U ∧
      ∀ i ≤ 40, ‖iteratedFDeriv ℝ i
        (fun τ => ∫ p, coldIntegrand R (Vt τ) (f τ) Yt b p ∂fieldLabelMeasure R n Yt) τ₀‖ ≤
        (2 * Q * P) ^ i * ∫ p, coldIntegrand R (Vt τ₀) Bf Yt b p ∂fieldLabelMeasure R n Yt := by
    intro Yt b
    have hsm : ∀ p, ContDiff ℝ 40 (fun τ => coldIntegrand R (Vt τ) (f τ) Yt b p) := fun p =>
      (hf Yt b p).mul (contDiff_const.mul (hK.contDiff p.1 b))
    have hjet : ∀ p τ, ∀ j ≤ 40, ‖iteratedFDeriv ℝ j (fun τ' => coldIntegrand R (Vt τ') (f τ') Yt b p) τ‖ ≤
        (2 * Q * P) ^ j * coldIntegrand R (Vt τ) Bf Yt b p := by
      intro p τ j hj
      have hg : ContDiff ℝ 40
          (fun τ' => hullBaseDensity R Yt b p * kernelProduct R.params R.coupling p.1 (Vt τ') b) :=
        contDiff_const.mul (hK.contDiff p.1 b)
      have hgj : ∀ i ≤ 40, ‖iteratedFDeriv ℝ i
          (fun τ' => hullBaseDensity R Yt b p * kernelProduct R.params R.coupling p.1 (Vt τ') b) τ‖ ≤
          P ^ i * (hullBaseDensity R Yt b p * kernelProduct R.params R.coupling p.1 (Vt τ) b) := by
        intro i hi
        have hi' : ((i : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast hi
        rw [norm_iteratedFDeriv_const_mul (hd Yt b p) ((hK.contDiff p.1 b).of_le hi').contDiffAt]
        calc hullBaseDensity R Yt b p *
              ‖iteratedFDeriv ℝ i (fun τ' => kernelProduct R.params R.coupling p.1 (Vt τ') b) τ‖
            ≤ hullBaseDensity R Yt b p * (P ^ i * kernelProduct R.params R.coupling p.1 (Vt τ) b) :=
              mul_le_mul_of_nonneg_left (hK.jets_le p.1 b τ i hi) (hd Yt b p)
          _ = _ := by ring
      exact norm_iteratedFDeriv_mul_le_pow (hf Yt b p) hg hQ hP (hB0 Yt b p)
        (mul_nonneg (hd Yt b p) (hK.pos p.1 b τ).le) (hfj Yt b p τ) hgj hj
    have hg : Integrable (fun p => (2 * Q * P) ^ 40 * (κ * coldIntegrand R (Vt τ₀) Bf Yt b p))
        (fieldLabelMeasure R n Yt) :=
      ((hBint Yt b).const_mul κ).const_mul _
    obtain ⟨c1, c2⟩ := hD (fieldLabelMeasure R n Yt) k 40 U (fun p τ => coldIntegrand R (Vt τ) (f τ) Yt b p)
      (fun p => (2 * Q * P) ^ 40 * (κ * coldIntegrand R (Vt τ₀) Bf Yt b p)) hU hg (fun p => (hsm p).contDiffOn)
      (fun τ hτ => (hint τ hτ Yt b).aestronglyMeasurable) (fun p j hj τ _ => by
        refine (hjet p τ j hj).trans ?_
        have h1 : coldIntegrand R (Vt τ) Bf Yt b p ≤ κ * coldIntegrand R (Vt τ₀) Bf Yt b p := by
          unfold coldIntegrand
          have h2 := mul_le_mul_of_nonneg_left (hK.ratio_le p.1 b τ) (mul_nonneg (hB0 Yt b p) (hd Yt b p))
          calc _ = Bf Yt b p * hullBaseDensity R Yt b p * kernelProduct R.params R.coupling p.1 (Vt τ) b := by ring
            _ ≤ _ := h2
            _ = _ := by ring
        have h3 : 0 ≤ coldIntegrand R (Vt τ) Bf Yt b p := mul_nonneg (hB0 Yt b p)
          (mul_nonneg (hd Yt b p) (hK.pos p.1 b τ).le)
        calc (2 * Q * P) ^ j * coldIntegrand R (Vt τ) Bf Yt b p ≤
              (2 * Q * P) ^ 40 * coldIntegrand R (Vt τ) Bf Yt b p :=
              mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD1 hj) h3
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity))
    refine ⟨c1, fun i hi => ?_⟩
    have h := c2 i hi τ₀ hτ₀ (fun p => (2 * Q * P) ^ i * coldIntegrand R (Vt τ₀) Bf Yt b p)
      ((hBint Yt b).const_mul _) fun p => hjet p τ₀ i hi
    rwa [integral_const_mul] at h
  have hin : ∀ Yt b, ContDiffOn ℝ 40
      (fun τ => ∫ p, coldIntegrand R (Vt τ) (f τ) Yt b p ∂fieldLabelMeasure R n Yt) U :=
    fun Yt b => (hpiece Yt b).1
  have hnh : U ∈ 𝓝 τ₀ := hU.mem_nhds hτ₀
  refine ⟨ContDiffOn.sum fun Yt _ => ContDiffOn.sum fun b _ => hin Yt b, fun i hi => ?_⟩
  have hi' : ((i : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast hi
  have hat : ∀ Yt b, ContDiffAt ℝ i
      (fun τ => ∫ p, coldIntegrand R (Vt τ) (f τ) Yt b p ∂fieldLabelMeasure R n Yt) τ₀ :=
    fun Yt b => ((hin Yt b).of_le hi').contDiffAt hnh
  have e1 : (fun τ => coldWeightedIntegral R (Vt τ) (f τ)) = fun τ => ∑ Yt : Finset (TorusSite (n * R.params.side)),
      ∑ b : BaseChoice R.params.side n, ∫ p, coldIntegrand R (Vt τ) (f τ) Yt b p ∂fieldLabelMeasure R n Yt := rfl
  rw [e1]
  refine (norm_iteratedFDeriv_sum_le _ _ τ₀ i fun Yt _ => ContDiffAt.sum fun b _ => hat Yt b).trans ?_
  unfold coldWeightedIntegral
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun Yt _ => ?_
  refine (norm_iteratedFDeriv_sum_le _ _ τ₀ i fun b _ => hat Yt b).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun b _ => (hpiece Yt b).2 i hi
theorem coldExpectation_jets (hD : ContDiffOnIntegralStatement) {k : ℕ} {Vt : (Fin k → ℝ) → TorusField n}
    {U : Set (Fin k → ℝ)} (hU : IsOpen U) {τ₀ : Fin k → ℝ} (hτ₀ : τ₀ ∈ U) {P κ Q Eb : ℝ}
    (hK : KernelProductBounds R Vt τ₀ P κ) (hQ : 1 ≤ Q)
    (hd : ∀ (Yt : Finset (TorusSite (n * R.params.side))) b p, 0 ≤ hullBaseDensity R Yt b p)
    {f : (Fin k → ℝ) → ConfigFunction R n} {Bf : ConfigFunction R n}
    (hf : ∀ Yt b p, ContDiff ℝ 40 (fun τ => f τ Yt b p))
    (hfj : ∀ Yt b p τ, ∀ i ≤ 40, ‖iteratedFDeriv ℝ i (fun τ' => f τ' Yt b p) τ‖ ≤ Q ^ i * Bf Yt b p)
    (hB0 : ∀ Yt b p, 0 ≤ Bf Yt b p)
    (hint : ∀ τ ∈ U, ∀ Yt b, Integrable (coldIntegrand R (Vt τ) (f τ) Yt b) (fieldLabelMeasure R n Yt))
    (hBint : ∀ Yt b, Integrable (coldIntegrand R (Vt τ₀) Bf Yt b) (fieldLabelMeasure R n Yt))
    (hone : ∀ τ ∈ U, ∀ Yt b, Integrable (coldIntegrand R (Vt τ) (fun _ _ _ => 1) Yt b) (fieldLabelMeasure R n Yt))
    (hpos : ∀ τ ∈ U, 0 < coldWeightedIntegral R (Vt τ) (fun _ _ _ => 1)) (hE0 : 0 ≤ Eb)
    (hE : coldWeightedIntegral R (Vt τ₀) Bf ≤ Eb * coldWeightedIntegral R (Vt τ₀) (fun _ _ _ => 1)) :
    ContDiffAt ℝ 40 (fun τ => coldExpectation R (Vt τ) (f τ)) τ₀ ∧
      ‖iteratedFDeriv ℝ 40 (fun τ => coldExpectation R (Vt τ) (f τ)) τ₀‖ ≤
        quotientConstant * Eb * (2 * Q * P) ^ 40 := by
  have hP := hK.one_le_rate
  have hD1 : 1 ≤ 2 * Q * P := by nlinarith
  obtain ⟨s1, j1⟩ := coldWeightedIntegral_jets hD hU hτ₀ hK hQ hd hf hfj hB0 hint hBint
  obtain ⟨s2, j2⟩ := coldWeightedIntegral_jets hD hU hτ₀ hK (Q := 1) le_rfl hd (f := fun _ _ _ _ => 1)
    (Bf := fun _ _ _ => 1) (fun _ _ _ => contDiff_const)
    (fun _ _ _ τ i _ => by simpa using norm_iteratedFDeriv_const_le (1 : ℝ) τ i)
    (fun _ _ _ => zero_le_one) hone (fun Yt b => hone τ₀ hτ₀ Yt b)
  have hz₀ := hpos τ₀ hτ₀
  refine norm_iteratedFDeriv_div_le hU hτ₀ s1 s2 hpos hD1 hE0 (fun i hi => (j1 i hi).trans ?_)
    (fun i hi => (j2 i hi).trans ?_)
  · exact mul_le_mul_of_nonneg_left hE (by positivity)
  · refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ i) hz₀.le
    nlinarith
end Configurations
section Responses
variable {R : StepSetup} {n : ℕ} [NeZero n] {A : ResponseSetup R}
theorem weightNorm_nonneg (L t : ℕ) {m : ℕ} (h : PlaquetteWeight m) : 0 ≤ weightNorm L t h :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
theorem hullBaseDensity_nonneg (hrow : R.HasExpansions) (hbs : IsBlockTorusSide R.params (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (p : TorusField (n * R.params.side) × (Yt → R.labels.Ω)) : 0 ≤ hullBaseDensity R Yt b p := by
  classical
  unfold hullBaseDensity
  split_ifs with hh
  · refine mul_nonneg (hrow.2.nonneg _ hbs p.1 Yt p.2 hh) ?_
    unfold baseLaw
    split_ifs
    · positivity
    · exact le_rfl
  · exact le_rfl
theorem abs_liveCenteredResponse_empty_le
    (hA : ResponseBounds R.params A.responseParams R.depth R.coupling A.coeff R.labels R.labelWeight A.score A.cold
      A.hull A.siteRemainder A.totalRemainder)
    (hbs : IsBlockTorusSide R.params (n * R.params.side)) (hC : 0 ≤ A.responseParams.C₀)
    (y : TorusSite (n * R.params.side)) (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)))
    (W : TorusField (n * R.params.side)) :
    |liveCenteredResponse A y h ∅ (W, emptyLabeling R)| ≤
      A.responseParams.C₀ * weightNorm R.params.side R.depth h := by
  classical
  unfold liveCenteredResponse
  split_ifs with hl
  · have h1 := hA.size_hull (n * R.params.side) hbs y W ∅ (emptyLabeling R) hl h
    have h2 : siteScore A.score ∅ (emptyLabeling R) y = 0 := by simp [siteScore]
    rwa [h2, add_zero] at h1
  · rw [abs_zero]
    exact mul_nonneg hC (weightNorm_nonneg _ _ _)
theorem measurable_liveCenteredResponse_empty (hrow : R.HasExpansions)
    (hA : ResponseBounds R.params A.responseParams R.depth R.coupling A.coeff R.labels R.labelWeight A.score A.cold
      A.hull A.siteRemainder A.totalRemainder)
    (hbs : IsBlockTorusSide R.params (n * R.params.side)) (y : TorusSite (n * R.params.side))
    (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))) :
    Measurable fun W : TorusField (n * R.params.side) => liveCenteredResponse A y h ∅ (W, emptyLabeling R) := by
  classical
  have h1 := hA.hull_borel (n * R.params.side) hbs y ∅ h
  have h2 := (hrow.2.borel (n * R.params.side) hbs ∅).1
  have hlive : MeasurableSet {p : TorusField (n * R.params.side) ×
      ((∅ : Finset (TorusSite (n * R.params.side))) → R.labels.Ω) |
      IsLiveState R.params R.coupling R.labelWeight p.1 ∅ p.2} := by
    have e : {p : TorusField (n * R.params.side) × ((∅ : Finset (TorusSite (n * R.params.side))) → R.labels.Ω) |
        IsLiveState R.params R.coupling R.labelWeight p.1 ∅ p.2} =
        (fun p : TorusField (n * R.params.side) × ((∅ : Finset (TorusSite (n * R.params.side))) → R.labels.Ω) =>
          if IsHullState R.params (clusterRange R.coupling) p.1 ∅ then
            R.labelWeight (n * R.params.side) p.1 ∅ p.2 else 0) ⁻¹' Set.Ioi 0 := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi, IsLiveState]
      split_ifs with hh
      · simp [hh]
      · simp [hh]
    rw [e]
    exact (by convert h2 : Measurable _) measurableSet_Ioi
  have h3 : Measurable fun p : TorusField (n * R.params.side) ×
      ((∅ : Finset (TorusSite (n * R.params.side))) → R.labels.Ω) => liveCenteredResponse A y h ∅ p := by
    have e : (fun p : TorusField (n * R.params.side) × ((∅ : Finset (TorusSite (n * R.params.side))) → R.labels.Ω) =>
        liveCenteredResponse A y h ∅ p) =
        fun p => (if IsLiveState R.params R.coupling R.labelWeight p.1 ∅ p.2 then
            A.hull (n * R.params.side) y p.1 ∅ p.2 h else 0) -
          (if IsLiveState R.params R.coupling R.labelWeight p.1 ∅ p.2 then
            A.cold (n * R.params.side) y (trivialField (n * R.params.side)) h else 0) := by
      funext p
      unfold liveCenteredResponse centeredHullResponse
      split_ifs
      · rfl
      · simp
    rw [e]
    exact (by convert h1 : Measurable _).sub (Measurable.ite hlive measurable_const measurable_const)
  exact h3.comp (measurable_id.prodMk measurable_const)
theorem coupling_power_bound {x m B C : ℝ} (hx : 2 ≤ x) (hm : m ≤ x) (hB : B ≤ x) (hC : 0 ≤ C) :
    m * x ^ 40 + x ^ C * B ≤ x ^ (C + 42) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have e : x ^ (C + 42) = x ^ C * x ^ 42 := by
    rw [Real.rpow_add hx0]
    congr 1
    exact_mod_cast Real.rpow_natCast x 42
  have hc1 : 1 ≤ x ^ C := Real.one_le_rpow hx1 hC
  have h41 : 0 < x ^ 41 := by positivity
  have h1 : m * x ^ 40 ≤ x ^ C * x ^ 41 := by
    calc m * x ^ 40 ≤ x * x ^ 40 := mul_le_mul_of_nonneg_right hm (by positivity)
      _ = 1 * x ^ 41 := by ring
      _ ≤ x ^ C * x ^ 41 := mul_le_mul_of_nonneg_right hc1 h41.le
  have h2 : x ^ C * B ≤ x ^ C * x ^ 41 := by
    refine mul_le_mul_of_nonneg_left (hB.trans ?_) (by positivity)
    exact le_self_pow₀ hx1 (by norm_num)
  have h3 : 2 * (x ^ C * x ^ 41) ≤ x * (x ^ C * x ^ 41) :=
    mul_le_mul_of_nonneg_right hx (by positivity)
  rw [e]
  calc m * x ^ 40 + x ^ C * B ≤ 2 * (x ^ C * x ^ 41) := by linarith
    _ ≤ x * (x ^ C * x ^ 41) := h3
    _ = x ^ C * x ^ 42 := by ring
theorem pow_forty_le_of_le_nine {Cp : ℝ} (hCp0 : 0 ≤ Cp) (k' : ℕ) (hk' : k' ≤ 9) :
    (Cp * ((k' : ℝ) + 1)) ^ 40 ≤ (10 * Cp) ^ 40 := by
  have h9 : (k' : ℝ) ≤ 9 := by exact_mod_cast hk'
  have h1 : Cp * ((k' : ℝ) + 1) ≤ 10 * Cp := by nlinarith
  exact pow_le_pow_left₀ (by positivity) h1 40
end Responses
end GasJets
open GasJets in
theorem gasTermsOfResponseSmooth_of (hP : GasShiftsAreColdExpectations)
    (hW : FullyMarkedExpectationAlongPerturbation) (hK : KernelProductAlongPerturbation)
    (hD : ContDiffOnIntegralStatement) (hC : ColdNearStatement) (hSc : BondScoreProperties) :
    GasTermsOfResponseSmooth := by
  obtain ⟨r₁, p₁, g₁⟩ := hP
  obtain ⟨r₂, p₂, g₂⟩ := hW
  obtain ⟨Cp, hCp, hKer⟩ := hK
  refine ⟨fun c => min (r₁ c) (r₂ c), fun c => lt_min (p₁ c) (p₂ c), fun T hT hrt K => ?_⟩
  obtain ⟨y₁, G₁⟩ := g₁ T hT (hrt.trans (min_le_left _ _)) K
  obtain ⟨C₂, y₂, hC₂, G₂⟩ := g₂ T hT (hrt.trans (min_le_right _ _))
  have hCp0 : 0 ≤ Cp := by linarith
  have hq0 := quotientConstant_nonneg
  have ha1 : 1 ≤ T.coupling := hT.a_ge
  have hBs2 : (2 : ℝ) ≤ (10 * Cp) ^ 40 := by
    have h1 : (2 : ℝ) ≤ 10 * Cp := by linarith
    exact h1.trans (le_self_pow₀ (by linarith) (by norm_num))
  refine ⟨C₂ + 42, max (max y₁ y₂) (max T.floorMin (max 2 (max K.C₀
    (max (quotientConstant * (K.C₀ + 1) * (96 * Cp * T.coupling) ^ 40)
    (max (quotientConstant * 2 * (2 * (Cp * 3) * (48 * Cp * T.coupling)) ^ 40) ((10 * Cp) ^ 40)))))), by linarith,
    fun y hy R A hKA hAt hArr => ?_⟩
  have hb1 := (le_max_left _ _).trans hy
  have hb2 := (le_max_right _ _).trans hy
  have hb3 := (le_max_right _ _).trans hb2
  have hb4 := (le_max_right _ _).trans hb3
  have hb5 := (le_max_right _ _).trans hb4
  have hb6 := (le_max_right _ _).trans hb5
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans hb1
  have hy2 : y₂ ≤ y := (le_max_right _ _).trans hb1
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans hb2
  have hOn := hAt.onFamily
  have hxy : y ≤ R.coupling := hOn.le_coupling
  have hx2 : 2 ≤ R.coupling := ((le_max_left _ _).trans hb3).trans hxy
  have hxC₀ : K.C₀ ≤ R.coupling := ((le_max_left _ _).trans hb4).trans hxy
  have hxm₁ : quotientConstant * (K.C₀ + 1) * (96 * Cp * T.coupling) ^ 40 ≤ R.coupling :=
    ((le_max_left _ _).trans hb5).trans hxy
  have hxm₂ : quotientConstant * 2 * (2 * (Cp * 3) * (48 * Cp * T.coupling)) ^ 40 ≤ R.coupling :=
    ((le_max_left _ _).trans hb6).trans hxy
  have hxBs : (10 * Cp) ^ 40 ≤ R.coupling := ((le_max_right _ _).trans hb6).trans hxy
  have hx1 : 1 ≤ R.coupling := by linarith
  have hx0 : 0 ≤ R.coupling := by linarith
  have hfit : R.params.Admissible := hOn.params_eq ▸ hT.fits y hy0
  have hae : R.params.coupling = T.coupling := by rw [hOn.params_eq]; rfl
  have ha : 1 ≤ R.params.coupling := hae ▸ ha1
  have hrow : R.HasExpansions := hOn.isStep.1
  have hAr := hAt.admissible
  have hC₀ : 0 ≤ K.C₀ := by
    have h1 := hAr.params_admissible.C₀_eq
    have h2 := hAr.params_admissible.N₀_nonneg
    have h3 := hAr.params_admissible.Kc_ge
    rw [hKA] at h1 h2 h3
    rw [h1]
    linarith [hfit.a_ge]
  intro n _ hn V k c X τ hcold
  have hbs : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hd := hullBaseDensity_nonneg (n := n) hrow hbs
  set S : ℝ := max 1 (∑ l, ‖X l‖) with hSd
  have hS1 : 1 ≤ S := le_max_left _ _
  have hSX : ∑ l, ‖X l‖ ≤ S := le_max_right _ _
  have ker := fun (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) =>
    hKer R.params R.coupling hfit ha hx1 n W V b k c X S hS1 hSX
  set Pk : ℝ := Cp * (R.params.coupling * R.coupling) * ((k : ℝ) + 1) ^ 2 * S with hPk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hP1 : 1 ≤ Pk := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hCp (one_le_mul_of_one_le_of_one_le ha hx1)) (one_le_pow₀ hk1)) hS1
  have hKal : KernelProductBounds R (fun τ' => perturb c X τ' V) τ Pk
      (Real.exp (2 * (R.params.coupling * R.coupling) * k)) :=
    ⟨fun W b => (ker W b).1, fun W b τ' => (ker W b).2.1 τ', fun W b τ' i hi => (ker W b).2.2.1 τ' i hi,
      fun W b τ' => (ker W b).2.2.2.1 τ' τ, hP1, (Real.exp_pos _).le⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hC n V k c X τ _ hcold)
  have hU : IsOpen (Metric.ball τ ε) := Metric.isOpen_ball
  have hτU : τ ∈ Metric.ball τ ε := Metric.mem_ball_self hε
  have hparts := fun (τ' : Fin k → ℝ) (h' : τ' ∈ Metric.ball τ ε) =>
    G₁ y hy1 R A hKA hAt hArr n hn (perturb c X τ' V) (hball τ' h')
  have hone := fun (τ' : Fin k → ℝ) (h' : τ' ∈ Metric.ball τ ε) => (hparts τ' h').1
  have hpos := fun (τ' : Fin k → ℝ) (h' : τ' ∈ Metric.ball τ ε) => (hparts τ' h').2.1
  have hnh : Metric.ball τ ε ∈ 𝓝 τ := Metric.ball_mem_nhds τ hε
  have hPle : k ≤ 3 → AreUnitVectors X → S ≤ 3 ∧ Pk ≤ 48 * Cp * T.coupling * R.coupling := by
    intro hk hu
    have hk3 : (k : ℝ) ≤ 3 := by exact_mod_cast hk
    have hs : ∑ l, ‖X l‖ = k := by simp [hu _]
    have hS3 : S ≤ 3 := by
      rw [hSd, hs]
      exact max_le (by norm_num) hk3
    refine ⟨hS3, ?_⟩
    have h16 : ((k : ℝ) + 1) ^ 2 ≤ 16 := by nlinarith
    rw [hPk, hae]
    have hax : 0 ≤ Cp * (T.coupling * R.coupling) := by positivity
    calc Cp * (T.coupling * R.coupling) * ((k : ℝ) + 1) ^ 2 * S ≤ Cp * (T.coupling * R.coupling) * 16 * 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h16 hax) hS3 (by linarith) (by positivity)
      _ = 48 * Cp * T.coupling * R.coupling := by ring
  refine ⟨fun y' h => ?_, fun bd => ?_⟩
  · set sz : ℝ := weightNorm R.params.side R.depth h with hsz
    have hsz0 : 0 ≤ sz := weightNorm_nonneg _ _ _
    have hcm := coldExpectation_jets (Q := 1) (Eb := (K.C₀ + 1) * sz) hD hU hτU hKal le_rfl hd
      (f := fun _ Yt _ p => liveCenteredResponse A y' h Yt p) (Bf := fun Yt _ p => |liveCenteredResponse A y' h Yt p|)
      (fun _ _ _ => contDiff_const) (fun Yt b p τ' i _ => norm_iteratedFDeriv_const_le _ τ' i)
      (fun _ _ _ => abs_nonneg _)
      (fun τ' h' Yt b => ((hparts τ' h').2.2.1 y' h).1 Yt b)
      (fun Yt b => by
        refine (((hparts τ hτU).2.2.1 y' h).1 Yt b).abs.congr (Filter.Eventually.of_forall fun p => ?_)
        show |coldIntegrand _ _ _ _ _ _| = coldIntegrand _ _ _ _ _ _
        unfold coldIntegrand
        rw [abs_mul, abs_of_nonneg (mul_nonneg (hd Yt b p) ((ker p.1 b).2.1 τ).le)])
      hone hpos (by positivity)
      (by
        have := ((hparts τ hτU).2.2.1 y' h).2.1
        rwa [hKA] at this)
    have hmk := G₂ y hy2 R hOn hArr n hn (fun _ W => liveCenteredResponse A y' h ∅ (W, emptyLabeling R)) (K.C₀ * sz)
      (fun _ => 0)
      (by positivity) (fun _ W => by
        have := abs_liveCenteredResponse_empty_le (A := A) hAr.bounds hbs (hKA ▸ hC₀) y' h W
        rwa [hKA] at this)
      (fun _ => measurable_liveCenteredResponse_empty hrow hAr.bounds hbs y' h)
      (fun k' c' X' _ V' W => ⟨contDiff_const, fun τ' i h1 _ => by
        rw [iteratedFDeriv_const_of_ne (by omega)]
        simp⟩) (fun _ _ => by positivity) V k c X τ hcold
    have hev : (fun τ' => gasResponseShift A (coldCaseGround R (perturb c X τ' V)) y' h) =ᶠ[𝓝 τ]
        (fun τ' => coldExpectation R (perturb c X τ' V) (fun Yt _ p => liveCenteredResponse A y' h Yt p)) -
          fun τ' => fullyMarkedExpectation R (perturb c X τ' V)
            (fun W => liveCenteredResponse A y' h ∅ (W, emptyLabeling R)) :=
      Filter.eventually_of_mem hnh fun τ' h' => ((hparts τ' h').2.2.1 y' h).2.2
    refine ⟨(hcm.1.sub hmk.1).congr_of_eventuallyEq hev, fun hk hu => ?_⟩
    rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev 40).eq_of_nhds, iteratedFDeriv_sub_apply hcm.1 hmk.1]
    refine (norm_sub_le _ _).trans ?_
    have b1 := hcm.2
    have b2 := hmk.2 hk hu
    obtain ⟨-, hPb⟩ := hPle hk hu
    have h96 : (2 * 1 * Pk) ^ 40 ≤ (96 * Cp * T.coupling) ^ 40 * R.coupling ^ 40 := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ 40
      calc 2 * 1 * Pk ≤ 2 * 1 * (48 * Cp * T.coupling * R.coupling) := by linarith
        _ = 96 * Cp * T.coupling * R.coupling := by ring
    have hnum := coupling_power_bound (x := R.coupling)
      (m := quotientConstant * (K.C₀ + 1) * (96 * Cp * T.coupling) ^ 40) (B := K.C₀) (C := C₂) hx2 hxm₁ hxC₀ hC₂
    calc _ ≤ quotientConstant * ((K.C₀ + 1) * sz) * (2 * 1 * Pk) ^ 40 + R.coupling ^ C₂ * (K.C₀ * sz) :=
          add_le_add b1 b2
      _ ≤ quotientConstant * ((K.C₀ + 1) * sz) * ((96 * Cp * T.coupling) ^ 40 * R.coupling ^ 40) +
            R.coupling ^ C₂ * (K.C₀ * sz) := by
          gcongr
      _ = (quotientConstant * (K.C₀ + 1) * (96 * Cp * T.coupling) ^ 40 * R.coupling ^ 40 +
            R.coupling ^ C₂ * K.C₀) * sz := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hnum hsz0
  · have hQ1 : 1 ≤ Cp * S := one_le_mul_of_one_le_of_one_le hCp hS1
    have hsc2 : ∀ (W : TorusField (n * R.params.side)) (V' : TorusField n) (b : BaseChoice R.params.side n),
        |bondScore R.params R.coupling W V' b bd| ≤ 2 := fun W V' b =>
      (hSc R.params hfit R.coupling n b bd).2.2.1 W V'
    have hcm := coldExpectation_jets (Q := Cp * S) (Eb := 2) hD hU hτU hKal hQ1 hd
      (f := fun τ' _ b p => bondScore R.params R.coupling p.1 (perturb c X τ' V) b bd) (Bf := fun _ _ _ => 2)
      (fun _ b p => ((ker p.1 b).2.2.2.2 bd).1)
      (fun Yt b p τ' i hi => by
        rcases Nat.eq_zero_or_pos i with rfl | h1
        · rw [norm_iteratedFDeriv_zero, pow_zero, one_mul, Real.norm_eq_abs]
          exact hsc2 _ _ _
        · refine (((ker p.1 b).2.2.2.2 bd).2 τ' i h1 hi).trans ?_
          exact le_mul_of_one_le_right (by positivity) (by norm_num))
      (fun _ _ _ => by norm_num)
      (fun τ' h' Yt b => ((hparts τ' h').2.2.2 bd).1 Yt b)
      (fun Yt b => by
        refine ((hone τ hτU Yt b).const_mul 2).congr (Filter.Eventually.of_forall fun p => ?_)
        show 2 * coldIntegrand _ _ _ _ _ _ = coldIntegrand _ _ _ _ _ _
        unfold coldIntegrand
        ring)
      hone hpos (by norm_num)
      (by
        refine le_of_eq ?_
        unfold coldWeightedIntegral
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun Yt _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        show coldIntegrand _ _ _ _ _ _ = 2 * coldIntegrand _ _ _ _ _ _
        unfold coldIntegrand
        ring)
    have hq9 := pow_forty_le_of_le_nine hCp0
    have hms : ∀ V' : TorusField n, Measurable fun W : TorusField (n * R.params.side) =>
        bondScore R.params R.coupling W V' (centreBases R.params.side n) bd := by
      intro V'
      have h1 := (hSc R.params hfit R.coupling n (centreBases R.params.side n) bd).2.2.2.2
      have h2 : Measurable fun W : TorusField (n * R.params.side) => (W, V') := measurable_id.prodMk measurable_const
      have h3 := h1.comp h2
      exact h3
    have hmk := G₂ y hy2 R hOn hArr n hn
      (fun V' W => bondScore R.params R.coupling W V' (centreBases R.params.side n) bd) ((10 * Cp) ^ 40)
      (fun k' => (Cp * ((k' : ℝ) + 1)) ^ 40) (by positivity) (fun V' W => (hsc2 W V' _).trans hBs2)
      hms
      (fun k' c' X' hu V' W => by
        have hk'1 : (1 : ℝ) ≤ (k' : ℝ) + 1 := by
          have : (0 : ℝ) ≤ k' := Nat.cast_nonneg k'
          linarith
        have kk := hKer R.params R.coupling hfit ha hx1 n W V' (centreBases R.params.side n) k' c' X'
          ((k' : ℝ) + 1) hk'1 (by simp [hu _])
        refine ⟨(kk.2.2.2.2 bd).1, fun τ' i h1 hi => ((kk.2.2.2.2 bd).2 τ' i h1 hi).trans ?_⟩
        exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hCp hk'1) hi)
      hq9 V k c X τ hcold
    have hev : (fun τ' => gasBondScoreShift (coldCaseGround R (perturb c X τ' V)) bd) =ᶠ[𝓝 τ]
        (fun τ' => coldExpectation R (perturb c X τ' V)
          (fun _ b p => bondScore R.params R.coupling p.1 (perturb c X τ' V) b bd)) -
          fun τ' => fullyMarkedExpectation R (perturb c X τ' V)
            (fun W => bondScore R.params R.coupling W (perturb c X τ' V) (centreBases R.params.side n) bd) :=
      Filter.eventually_of_mem hnh fun τ' h' => ((hparts τ' h').2.2.2 bd).2
    refine ⟨(hcm.1.sub hmk.1).congr_of_eventuallyEq hev, fun hk hu => ?_⟩
    rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev 40).eq_of_nhds, iteratedFDeriv_sub_apply hcm.1 hmk.1]
    refine (norm_sub_le _ _).trans ?_
    have b1 := hcm.2
    have b2 := hmk.2 hk hu
    obtain ⟨hS3, hPb⟩ := hPle hk hu
    have hpw : (2 * (Cp * S) * Pk) ^ 40 ≤ (2 * (Cp * 3) * (48 * Cp * T.coupling)) ^ 40 * R.coupling ^ 40 := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ 40
      have h1 : Cp * S ≤ Cp * 3 := mul_le_mul_of_nonneg_left hS3 hCp0
      calc 2 * (Cp * S) * Pk ≤ 2 * (Cp * 3) * (48 * Cp * T.coupling * R.coupling) :=
            mul_le_mul (by linarith) hPb (by linarith) (by positivity)
        _ = _ := by ring
    have hnum := coupling_power_bound (x := R.coupling)
      (m := quotientConstant * 2 * (2 * (Cp * 3) * (48 * Cp * T.coupling)) ^ 40)
      (B := (10 * Cp) ^ 40) (C := C₂) hx2 hxm₂ hxBs hC₂
    calc _ ≤ quotientConstant * 2 * (2 * (Cp * S) * Pk) ^ 40 + R.coupling ^ C₂ * (10 * Cp) ^ 40 := add_le_add b1 b2
      _ ≤ quotientConstant * 2 * ((2 * (Cp * 3) * (48 * Cp * T.coupling)) ^ 40 * R.coupling ^ 40) +
            R.coupling ^ C₂ * (10 * Cp) ^ 40 := by
          gcongr
      _ = quotientConstant * 2 * (2 * (Cp * 3) * (48 * Cp * T.coupling)) ^ 40 * R.coupling ^ 40 +
            R.coupling ^ C₂ * (10 * Cp) ^ 40 := by ring
      _ ≤ _ := hnum
end ResponseInTheExpansion
end YangMills.Construction
end
