import YangMills.Construction.ColdStepAtMirrorFrames.MomentOfASquareBound
import YangMills.Construction.ColdStepAtMirrorFrames.MomentsOfAConvexMeasure
import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACut
import YangMills.Construction.SummableBoundsOfTheFlow.LawOfACutIsAProbability
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages YangMills.Construction.Interpolation YangMills.Construction.ConvexObservables
namespace QuadraticBoundMoment
variable {ι : Type} [Fintype ι]
private theorem pow_weighted_sum_le (w z : ι → ℝ) (hw : ∀ b, 0 ≤ w b) (hz : ∀ b, 0 ≤ z b) {q : ℕ} (hq : 1 ≤ q) :
    (∑ b, w b * z b) ^ q ≤ (∑ b, w b) ^ (q - 1) * ∑ b, w b * z b ^ q := by
  set S := ∑ b, w b with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun b _ => hw b
  rcases hS0.eq_or_lt with h0 | hpos
  · have hw0 : ∀ b, w b = 0 := fun b =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hw b)).mp h0.symm b (Finset.mem_univ b)
    have : q ≠ 0 := by omega
    simp [hw0, this]
  · have hj := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun b => w b / S) z
      (fun b _ => div_nonneg (hw b) hS0) (by rw [← Finset.sum_div, ← hS, div_self hpos.ne'])
      (fun b _ => hz b) q
    have e1 : ∑ b, w b / S * z b = (∑ b, w b * z b) / S := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun b _ => by ring
    have e2 : ∑ b, w b / S * z b ^ q = (∑ b, w b * z b ^ q) / S := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e1, e2, div_pow, div_le_div_iff₀ (pow_pos hpos q) hpos] at hj
    have hq' : S ^ q = S ^ (q - 1) * S := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hq'] at hj
    have := le_of_mul_le_mul_right (a := S) (by
      calc (∑ b, w b * z b) ^ q * S ≤ (∑ b, w b * z b ^ q) * (S ^ (q - 1) * S) := hj.trans_eq rfl |>.trans_eq' rfl |> fun h => by
            nlinarith [h]
        _ = (S ^ (q - 1) * ∑ b, w b * z b ^ q) * S := by ring) hpos
    exact this
abbrev _root_.YangMills.SharedProofs.p74209 := @pow_weighted_sum_le
private theorem pow_mul_pow_mul_div_eq (x S D m : ℝ) (q : ℕ) (hm : m ≠ 0) :
    x ^ q * (S ^ q * (D / m ^ q)) = (x / m * S) ^ q * D := by
  rw [mul_pow, div_pow]
  field_simp
private theorem two_pow_pred_mul_le {t D : ℝ} (ht : 0 ≤ t) (hD : 0 ≤ D) {q : ℕ} (hq : 1 ≤ q) :
    2 ^ (q - 1) * (t ^ q * D + 1) ≤ (2 * (1 + t * (1 + D))) ^ q := by
  have hy : 0 ≤ t * (1 + D) := by positivity
  have h1 : 1 + (t * (1 + D)) ^ q ≤ (1 + t * (1 + D)) ^ q := by
    have := pow_add_pow_le (zero_le_one' ℝ) hy (n := q) (by omega)
    simpa using this
  have h2 : t ^ q * D ≤ (t * (1 + D)) ^ q := by
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht q)
    calc D ≤ 1 + D := by linarith
      _ = (1 + D) ^ 1 := (pow_one _).symm
      _ ≤ (1 + D) ^ q := pow_le_pow_right₀ (by linarith) hq
  rw [mul_pow]
  have h3 : (2 : ℝ) ^ (q - 1) ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) (by omega)
  have h4 : 0 ≤ t ^ q * D + 1 := by positivity
  calc 2 ^ (q - 1) * (t ^ q * D + 1) ≤ 2 ^ q * (t ^ q * D + 1) :=
        mul_le_mul_of_nonneg_right h3 h4
    _ ≤ 2 ^ q * (1 + t * (1 + D)) ^ q := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
end QuadraticBoundMoment
open QuadraticBoundMoment in
theorem momentBoundOfQuadraticBound_holds (hM : GaussianMomentBound) (hRim : CutoffFactorIsRadialCutoff)
    (hLaw : normalizedBallLawIsProbabilityStatement) : momentBoundOfQuadraticBound := by
  intro ι _ _ ρ x lam κ W W₀ d Ψ K p hρ hx hlam hκ hW hW₀ hcut hd hconv hsum hslope H B A w q hq hB hA
    hw hSw hcont hbound
  set r := cutoffFactor ρ p with hr
  have hΨc : Continuous Ψ := hconv.smooth.continuous
  obtain ⟨hprob, hmean, hint, hball, -, hdens0, hdensI, hZ, -, -, -⟩ := hLaw ι ρ p Ψ hρ hcut hΨc
  set P := normalizedBallLaw r Ψ with hP
  set m := x * lam / 4 with hm
  have hmpos : 0 < m := by positivity
  set D := ∏ k ∈ Finset.range q, (4 * (k : ℝ) + 8 * W) with hD
  have hD0 : 0 ≤ D := Finset.prod_nonneg fun k _ => by positivity
  have hmom : ∀ b : ι, ballExpectation r Ψ (fun η => ‖η b‖ ^ (2 * q)) ≤ D / m ^ q := by
    intro b
    have h := hM ι ρ m κ W d Ψ K (fun u => cutoffFactor ρ p (max u 0)) hρ hmpos hκ (hRim ρ p hρ hcut) hd hconv
      hsum hslope q b
    have e : ballExpectation (fun u => cutoffFactor ρ p (max u 0)) Ψ (fun η => ‖η b‖ ^ (2 * q)) =
        ballExpectation r Ψ (fun η => ‖η b‖ ^ (2 * q)) := by
      have : ballDensity (fun u => cutoffFactor ρ p (max u 0)) Ψ = ballDensity r Ψ := by
        funext η
        simp [ballDensity, radialWeightProd, hr]
      simp only [ballExpectation, this]
    rwa [e] at h
  set U : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ} with hU
  have hUo : IsOpen U := by
    have : U = ⋂ b, {η : BondField ι | ‖η b‖ < ρ} := by
      ext η
      simp [hU]
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt ((continuous_apply b).norm) continuous_const
  have hPU : ∀ᵐ η ∂P, η ∈ U := hball
  have hrestr : P.restrict U = P := Measure.restrict_eq_self_of_ae_mem hPU
  have hHm : AEStronglyMeasurable H P := by
    rw [← hrestr]
    exact hcont.aestronglyMeasurable hUo.measurableSet
  set S := ∑ b, w b with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun b _ => hw b
  set f : BondField ι → ℝ := fun η => ∑ b, w b * ‖η b‖ ^ 2 with hf
  have hf0 : ∀ η, 0 ≤ f η := fun η => Finset.sum_nonneg fun b _ => mul_nonneg (hw b) (by positivity)
  have hqb : ∀ b : ι, Integrable (fun η : BondField ι => ‖η b‖ ^ (2 * q)) P := by
    intro b
    refine Integrable.of_bound (C := ρ ^ (2 * q)) ?_ ?_
    · exact ((continuous_apply b).norm.pow _).aestronglyMeasurable
    · filter_upwards [hPU] with η hη
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hη b).le _
  set g : BondField ι → ℝ := fun η =>
    (B) ^ q * (2 ^ (q - 1) * (x ^ q * (S ^ (q - 1) * ∑ b, w b * ‖η b‖ ^ (2 * q)) + A ^ q)) with hg
  have hle : ∀ η ∈ U, |H η| ^ q ≤ g η := by
    intro η hη
    have h1 := hbound η hη
    have h2 : |H η| ^ q ≤ (B * (x * f η + A)) ^ q := pow_le_pow_left₀ (abs_nonneg _) h1 q
    refine h2.trans ?_
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hB q)
    have h3 := add_pow_le (mul_nonneg hx.le (hf0 η)) hA q
    refine h3.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h4 := pow_weighted_sum_le w (fun b => ‖η b‖ ^ 2) hw (fun b => by positivity) hq
    have h5 : (∑ b, w b * (‖η b‖ ^ 2) ^ q) = ∑ b, w b * ‖η b‖ ^ (2 * q) :=
      Finset.sum_congr rfl fun b _ => by rw [pow_mul]
    rw [h5] at h4
    rw [mul_pow]
    have := mul_le_mul_of_nonneg_left h4 (pow_nonneg hx.le q)
    linarith
  have hgI : Integrable g P := by
    have h1 : Integrable (fun η => ∑ b, w b * ‖η b‖ ^ (2 * q)) P :=
      integrable_finset_sum _ fun b _ => (hqb b).const_mul _
    exact ((((h1.const_mul _).const_mul _).add (integrable_const _)).const_mul _).const_mul _
  have hHq : Integrable (fun η => |H η| ^ q) P := by
    refine Integrable.mono' hgI ((hHm.norm.pow q).congr ?_) ?_
    · exact Filter.Eventually.of_forall fun η => by simp
    · filter_upwards [hPU] with η hη
      rw [Real.norm_of_nonneg (by positivity)]
      exact hle η hη
  refine ⟨(hint _).mp hHq, ?_⟩
  rw [← hmean]
  have hmain : ∫ η, |H η| ^ q ∂P ≤ ∫ η, g η ∂P :=
    integral_mono_ae hHq hgI (by filter_upwards [hPU] with η hη using hle η hη)
  refine hmain.trans ?_
  have hgval : ∫ η, g η ∂P = B ^ q * (2 ^ (q - 1) * (x ^ q * (S ^ (q - 1) *
      ∑ b, w b * ∫ η, ‖η b‖ ^ (2 * q) ∂P) + A ^ q)) := by
    have h1 : ∫ η, ∑ b, w b * ‖η b‖ ^ (2 * q) ∂P = ∑ b, w b * ∫ η, ‖η b‖ ^ (2 * q) ∂P := by
      rw [integral_finset_sum _ fun b _ => (hqb b).const_mul _]
      exact Finset.sum_congr rfl fun b _ => integral_const_mul _ _
    have h2 : Integrable (fun η => ∑ b, w b * ‖η b‖ ^ (2 * q)) P :=
      integrable_finset_sum _ fun b _ => (hqb b).const_mul _
    simp only [hg]
    rw [integral_const_mul, integral_const_mul,
      integral_add ((h2.const_mul _).const_mul _) (integrable_const _), integral_const_mul,
      integral_const_mul, h1]
    simp
  rw [hgval]
  have hsumle : ∑ b, w b * ∫ η, ‖η b‖ ^ (2 * q) ∂P ≤ S * (D / m ^ q) := by
    rw [hS, Finset.sum_mul]
    refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (hw b)
    rw [hmean]
    exact hmom b
  set t := 4 * W₀ / lam with ht
  have ht0 : 0 ≤ t := by positivity
  have hxm : x / m = 4 / lam := by
    rw [hm]
    field_simp
  have hfirst : x ^ q * (S ^ (q - 1) * ∑ b, w b * ∫ η, ‖η b‖ ^ (2 * q) ∂P) ≤ (t * A) ^ q * D := by
    have hSq : S ^ (q - 1) * S = S ^ q := by
      rw [← pow_succ]
      congr 1
      omega
    have hSle : S ≤ W₀ * A := hSw
    calc x ^ q * (S ^ (q - 1) * ∑ b, w b * ∫ η, ‖η b‖ ^ (2 * q) ∂P)
        ≤ x ^ q * (S ^ (q - 1) * (S * (D / m ^ q))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hsumle (by positivity)
      _ = (4 / lam * S) ^ q * D := by
          rw [← mul_assoc (S ^ (q - 1)), hSq, ← hxm]
          exact pow_mul_pow_mul_div_eq x S D m q hmpos.ne'
      _ ≤ (t * A) ^ q * D := by
          apply mul_le_mul_of_nonneg_right _ hD0
          apply pow_le_pow_left₀ (by positivity)
          rw [ht]
          have : 4 / lam * S ≤ 4 / lam * (W₀ * A) :=
            mul_le_mul_of_nonneg_left hSle (by positivity)
          calc 4 / lam * S ≤ 4 / lam * (W₀ * A) := this
            _ = 4 * W₀ / lam * A := by ring
  have hnum := two_pow_pred_mul_le ht0 hD0 hq
  have hfin : B ^ q * (2 ^ (q - 1) * ((t * A) ^ q * D + A ^ q)) ≤
      (lpMomentConstant lam W₀ W q * (B * A)) ^ q := by
    have e : lpMomentConstant lam W₀ W q = 2 * (1 + t * (1 + D)) := rfl
    rw [e]
    have e2 : B ^ q * (2 ^ (q - 1) * ((t * A) ^ q * D + A ^ q)) =
        2 ^ (q - 1) * (t ^ q * D + 1) * (B ^ q * A ^ q) := by
      rw [mul_pow]
      ring
    rw [e2, mul_pow, mul_pow (B) A]
    exact mul_le_mul_of_nonneg_right hnum (by positivity)
  refine le_trans ?_ hfin
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hB q)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
