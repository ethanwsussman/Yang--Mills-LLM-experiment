import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfTheGasProof
import YangMills.Construction.ResponseInTheExpansion.FarVariableUnderATiltProof
import YangMills.Construction.ResponseInTheExpansion.FarVariablesSplitOverTheGas
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction
open Dobrushin StepGas StepSettings RenormalizationStepParameters TorusLumps TorusFields CoreColumns BlockAverages FreeEnergies WeightedResponses
namespace ResponseInTheExpansion
namespace Decorrelation
set_option linter.unusedSectionVars false
section Laws
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)] {A : PairConstraint S}
  {m : ∀ i, Measure (S i)} [∀ i, SigmaFinite (m i)] {W Y : (∀ i, S i) → ℝ} {z z' : I → ℝ}
theorem lintegral_ne_zero_ne_top (μ : Measure (∀ i, S i)) (d : (∀ i, S i) → ℝ≥0∞) (hd : Measurable d)
    (hp : IsProbabilityMeasure ((∫⁻ σ, d σ ∂μ)⁻¹ • μ.withDensity d)) :
    (∫⁻ σ, d σ ∂μ) ≠ 0 ∧ (∫⁻ σ, d σ ∂μ) ≠ ⊤ := by
  have h1 := hp.measure_univ
  simp only [Measure.smul_apply, smul_eq_mul] at h1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  constructor
  · intro h0
    rw [h0] at h1
    simp at h1
  · intro ht
    rw [ht] at h1
    simp at h1
theorem integral_mul_eq_of_tilt (hW : A.IsActivityBounded m W z) (hWY : A.IsActivityBounded m (fun σ => W σ * Y σ) z')
    (hY : Measurable Y) (hpos : ∀ σ, A.IsAdmissible σ → 0 < Y σ) [p1 : IsProbabilityMeasure (A.gibbsLaw m W)]
    [p2 : IsProbabilityMeasure (A.gibbsLaw m fun σ => W σ * Y σ)] (hadm : ∀ᵐ σ ∂A.gibbsLaw m W, A.IsAdmissible σ) :
    Integrable Y (A.gibbsLaw m W) ∧ 0 < ∫ σ, Y σ ∂A.gibbsLaw m W ∧ ∀ F : (∀ i, S i) → ℝ,
      Integrable F (A.gibbsLaw m fun σ => W σ * Y σ) → Integrable (fun σ => F σ * Y σ) (A.gibbsLaw m W) ∧
        ∫ σ, F σ * Y σ ∂A.gibbsLaw m W = (∫ σ, Y σ ∂A.gibbsLaw m W) * ∫ σ, F σ ∂A.gibbsLaw m fun σ => W σ * Y σ := by
  classical
  set π := Measure.pi m with hπ
  set d := A.weightDensity W with hd
  set dY := A.weightDensity fun σ => W σ * Y σ with hdY
  have md : Measurable d := hW.measurable_weightDensity
  have mdY : Measurable dY := hWY.measurable_weightDensity
  set g : (∀ i, S i) → ℝ≥0∞ := fun σ => ENNReal.ofReal (Y σ) with hg
  have mg : Measurable g := hY.ennreal_ofReal
  obtain ⟨a0, at'⟩ := lintegral_ne_zero_ne_top π d md p1
  obtain ⟨b0, bt⟩ := lintegral_ne_zero_ne_top π dY mdY p2
  set a := ∫⁻ σ, d σ ∂π with ha
  set b := ∫⁻ σ, dY σ ∂π with hb
  have hprod : dY = d * g := by
    funext σ
    simp only [hdY, hd, hg, Pi.mul_apply, PairConstraint.weightDensity]
    by_cases h : A.IsAdmissible σ
    · rw [if_pos h, if_pos h, ENNReal.ofReal_mul (hW.pos_of_admissible σ h).le]
    · rw [if_neg h, if_neg h, zero_mul]
  have e1 : π.withDensity d = a • A.gibbsLaw m W := by
    show π.withDensity d = a • (a⁻¹ • π.withDensity d)
    rw [smul_smul, ENNReal.mul_inv_cancel a0 at', one_smul]
  set c : ℝ≥0∞ := b⁻¹ * a with hc
  have hc0 : c ≠ 0 := mul_ne_zero (ENNReal.inv_ne_zero.mpr bt) a0
  have hct : c ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr b0) at'
  have e2 : A.gibbsLaw m (fun σ => W σ * Y σ) = c • (A.gibbsLaw m W).withDensity g := by
    show b⁻¹ • π.withDensity dY = _
    rw [hprod, withDensity_mul _ md mg, e1, withDensity_smul_measure, smul_smul]
  set μ := A.gibbsLaw m W with hμ
  have hYnn : 0 ≤ᵐ[μ] Y := by
    filter_upwards [hadm] with σ hσ
    exact (hpos σ hσ).le
  have hone : c * ∫⁻ σ, g σ ∂μ = 1 := by
    have h1 : (A.gibbsLaw m fun σ => W σ * Y σ) Set.univ = 1 := measure_univ
    rw [e2] at h1
    simp only [Measure.smul_apply, smul_eq_mul] at h1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    exact h1
  have hgt : ∫⁻ σ, g σ ∂μ ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top hc0] at hone
    exact ENNReal.top_ne_one hone
  have hg0 : ∫⁻ σ, g σ ∂μ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hone
    exact zero_ne_one hone
  have iY : Integrable Y μ :=
    ⟨hY.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hYnn).mpr (lt_top_iff_ne_top.mpr hgt)⟩
  have eY : ∫ σ, Y σ ∂μ = (∫⁻ σ, g σ ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hYnn hY.aestronglyMeasurable
  have hpos' : 0 < ∫ σ, Y σ ∂μ := by
    rw [eY]
    exact ENNReal.toReal_pos hg0 hgt
  have hcY : c.toReal * ∫ σ, Y σ ∂μ = 1 := by
    rw [eY, ← ENNReal.toReal_mul, hone]
    simp
  have hlt : ∀ᵐ σ ∂μ, g σ < ⊤ := Filter.Eventually.of_forall fun σ => ENNReal.ofReal_lt_top
  have htoY : ∀ᵐ σ ∂μ, (g σ).toReal = Y σ := by
    filter_upwards [hadm] with σ hσ
    exact ENNReal.toReal_ofReal (hpos σ hσ).le
  refine ⟨iY, hpos', fun F hF => ?_⟩
  have hF' : Integrable F (μ.withDensity g) := by
    rw [e2] at hF
    exact (integrable_smul_measure hc0 hct).mp hF
  have hF2 : Integrable (fun σ => (g σ).toReal • F σ) μ :=
    (integrable_withDensity_iff_integrable_smul' mg hlt).mp hF'
  have hcongr : (fun σ => (g σ).toReal • F σ) =ᵐ[μ] fun σ => F σ * Y σ := by
    filter_upwards [htoY] with σ hσ
    rw [hσ, smul_eq_mul, mul_comm]
  refine ⟨hF2.congr hcongr, ?_⟩
  have e3 : ∫ σ, F σ ∂(A.gibbsLaw m fun σ => W σ * Y σ) = c.toReal * ∫ σ, F σ * Y σ ∂μ := by
    rw [e2, integral_smul_measure, integral_withDensity_eq_integral_toReal_smul mg hlt, integral_congr_ae hcongr]
    rfl
  rw [e3, ← mul_assoc, mul_comm (∫ σ, Y σ ∂μ), hcY, one_mul]
theorem abs_covariance_le {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {u Y₁ Y₂ Yy : Ω → ℝ} {n₁ n₂ Uq Δ : ℝ}
    (i1 : Integrable Y₁ μ) (i2 : Integrable Y₂ μ) (iu1 : Integrable (fun σ => u σ * Y₁ σ) μ)
    (iu2 : Integrable (fun σ => u σ * Y₂ σ) μ) (r1 : ∫ σ, u σ * Y₁ σ ∂μ = (∫ σ, Y₁ σ ∂μ) * n₁)
    (r2 : ∫ σ, u σ * Y₂ σ ∂μ = (∫ σ, Y₂ σ ∂μ) * n₂) (hY : Yy =ᵐ[μ] fun σ => Y₁ σ - Y₂ σ)
    (d1 : |n₁ - ∫ σ, u σ ∂μ| ≤ Δ) (d2 : |n₂ - ∫ σ, u σ ∂μ| ≤ Δ) (h0 : 0 ≤ ∫ σ, Y₁ σ ∂μ)
    (h1 : ∫ σ, Y₁ σ ∂μ ≤ 3 * Uq) (h2 : ∫ σ, Y₂ σ ∂μ = 2 * Uq) (hU : 0 ≤ Uq) :
    Integrable Yy μ ∧ Integrable (fun σ => u σ * Yy σ) μ ∧
      |∫ σ, u σ * Yy σ ∂μ - (∫ σ, u σ ∂μ) * ∫ σ, Yy σ ∂μ| ≤ 5 * Uq * Δ := by
  have iy : Integrable Yy μ := (i1.sub i2).congr hY.symm
  have hcg : (fun σ => u σ * Yy σ) =ᵐ[μ] fun σ => u σ * Y₁ σ - u σ * Y₂ σ := by
    filter_upwards [hY] with σ hσ
    rw [hσ]
    ring
  have iuy : Integrable (fun σ => u σ * Yy σ) μ := (iu1.sub iu2).congr hcg.symm
  refine ⟨iy, iuy, ?_⟩
  rw [integral_congr_ae hcg, integral_congr_ae hY, integral_sub iu1 iu2, integral_sub i1 i2, r1, r2, h2]
  set mm := ∫ σ, u σ ∂μ with hmm
  set Z := ∫ σ, Y₁ σ ∂μ with hZ
  have e : Z * n₁ - 2 * Uq * n₂ - mm * (Z - 2 * Uq) = Z * (n₁ - mm) - 2 * Uq * (n₂ - mm) := by ring
  rw [e]
  calc _ ≤ |Z * (n₁ - mm)| + |2 * Uq * (n₂ - mm)| := abs_sub _ _
    _ = Z * |n₁ - mm| + 2 * Uq * |n₂ - mm| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg (by positivity : 0 ≤ 2 * Uq)]
    _ ≤ 3 * Uq * Δ + 2 * Uq * Δ := by
        have a1 : Z * |n₁ - mm| ≤ 3 * Uq * Δ := mul_le_mul h1 d1 (abs_nonneg _) (by positivity)
        have a2 : 2 * Uq * |n₂ - mm| ≤ 2 * Uq * Δ := mul_le_mul_of_nonneg_left d2 (by positivity)
        exact add_le_add a1 a2
    _ = _ := by ring
end Laws
section Preliminaries
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
theorem spinLabelScore_nonneg {s : R.labels.Ω → ℝ} (hs : ∀ w, 0 ≤ s w) (i : G.GasSpin) (y : TorusSite (n * R.params.side))
    (v : G.SpinValue i) : 0 ≤ spinLabelScore s G i y v := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.spinLabelScore_nonneg <;> assumption
theorem measurable_spinLabelScore {s : R.labels.Ω → ℝ} (hb : Measurable s) (i : G.GasSpin)
    (y : TorusSite (n * R.params.side)) : Measurable (spinLabelScore s G i y) := by apply _root_.YangMills.Construction.TiltedGasResponse.measurable_spinLabelScore <;> assumption
theorem spinLabelScore_of_not_mem {s : R.labels.Ω → ℝ} {i : G.GasSpin} {y : TorusSite (n * R.params.side)}
    (hy : y ∉ i.1.2) (v : G.SpinValue i) : spinLabelScore s G i y v = 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.spinLabelScore_eq_zero_of_not_mem <;> assumption
theorem sum_spinLabelScore_update (s : R.labels.Ω → ℝ) (σ : G.Config) (i : G.GasSpin) (v : G.SpinValue i)
    (y : TorusSite (n * R.params.side)) :
    ∑ k, spinLabelScore s G k y (Function.update σ i v k) =
      ∑ k, spinLabelScore s G k y (Function.update σ i (G.pairConstraint.vacant i) k) + spinLabelScore s G i y v := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  have h0 : spinLabelScore s G i y (G.pairConstraint.vacant i) = 0 := rfl
  have h1 : ∑ k ∈ Finset.univ.erase i, spinLabelScore s G k y (Function.update σ i v k) =
      ∑ k ∈ Finset.univ.erase i, spinLabelScore s G k y (Function.update σ i (G.pairConstraint.vacant i) k) :=
    Finset.sum_congr rfl fun k hk => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hk), Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [h0, h1]
  ring
theorem recordedSiteScore_nonneg {A : ResponseSetup R} (hs : ∀ w, 0 ≤ A.score w) (y : TorusSite (n * R.params.side)) :
    0 ≤ recordedSiteScore A G y :=
  siteScore_nonneg hs _ _ _
theorem one_le_spinScore {A : ResponseSetup R} (hs : ∀ w, 0 ≤ A.score w) (S : Finset (TorusSite (n * R.params.side)))
    (σ : G.Config) : 1 ≤ ResponseInTheExpansion.spinScore A G S σ := by
  unfold ResponseInTheExpansion.spinScore
  have : 0 ≤ (S.card : ℝ)⁻¹ * ∑ y ∈ S, (recordedSiteScore A G y + ∑ i, spinLabelScore A.score G i y (σ i)) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => add_nonneg (recordedSiteScore_nonneg hs y)
      (Finset.sum_nonneg fun i _ => spinLabelScore_nonneg hs i y _))
  linarith
theorem measurable_spinScore {A : ResponseSetup R} (hb : Measurable A.score)
    (S : Finset (TorusSite (n * R.params.side))) : Measurable (ResponseInTheExpansion.spinScore A G S) := by
  unfold ResponseInTheExpansion.spinScore
  refine measurable_const.add (Measurable.const_mul (Finset.measurable_fun_sum _ fun y _ => ?_) _)
  exact measurable_const.add (Finset.measurable_fun_sum _ fun i _ =>
    (measurable_spinLabelScore hb i y).comp (measurable_pi_apply i))
theorem spinScore_update_le {A : ResponseSetup R} (hs : ∀ w, 0 ≤ A.score w)
    (S : Finset (TorusSite (n * R.params.side))) (σ : G.Config) (i : G.GasSpin) (v : G.SpinValue i) :
    ResponseInTheExpansion.spinScore A G S (Function.update σ i v) ≤
      ResponseInTheExpansion.spinScore A G S (Function.update σ i (G.pairConstraint.vacant i)) *
        Real.exp (∑ y ∈ S, spinLabelScore A.score G i y v) := by
  set N₀ := ResponseInTheExpansion.spinScore A G S (Function.update σ i (G.pairConstraint.vacant i)) with hN₀
  set Lv := ∑ y ∈ S, spinLabelScore A.score G i y v with hLv
  have hL0 : 0 ≤ Lv := Finset.sum_nonneg fun y _ => spinLabelScore_nonneg hs i y v
  have h1 : 1 ≤ N₀ := one_le_spinScore hs _ _
  have e : ResponseInTheExpansion.spinScore A G S (Function.update σ i v) = N₀ + (S.card : ℝ)⁻¹ * Lv := by
    simp only [hN₀, hLv, ResponseInTheExpansion.spinScore, sum_spinLabelScore_update A.score σ i v]
    have : ∀ y, recordedSiteScore A G y + (∑ k, spinLabelScore A.score G k y
        (Function.update σ i (G.pairConstraint.vacant i) k) + spinLabelScore A.score G i y v) =
        (recordedSiteScore A G y + ∑ k, spinLabelScore A.score G k y
          (Function.update σ i (G.pairConstraint.vacant i) k)) + spinLabelScore A.score G i y v := fun y => by ring
    simp only [this, Finset.sum_add_distrib]
    ring
  rw [e]
  have hinv : (S.card : ℝ)⁻¹ ≤ 1 := by
    rcases Nat.eq_zero_or_pos S.card with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ S.card := by exact_mod_cast h
      exact inv_le_one_of_one_le₀ this
  have h2 : (S.card : ℝ)⁻¹ * Lv ≤ Lv := by nlinarith
  have h3 : 1 + Lv ≤ Real.exp Lv := by linarith [Real.add_one_le_exp Lv]
  nlinarith
end Preliminaries
section Tilts
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n} {ι : Type} [DecidableEq ι]
theorem abs_prod_sub_prod_le {a b P : ι → ℝ} {e : ℝ} (he : 0 ≤ e) (J : Finset ι) (hP : ∀ i ∈ J, 0 ≤ P i)
    (ha : ∀ i ∈ J, |a i| ≤ P i) (hb : ∀ i ∈ J, |b i| ≤ P i) (hab : ∀ i ∈ J, |a i - b i| ≤ e * P i) :
    |∏ i ∈ J, a i - ∏ i ∈ J, b i| ≤ J.card * e * ∏ i ∈ J, P i := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hs : ∀ j, j ∈ s → j ∈ insert i s := fun j hj => Finset.mem_insert_of_mem hj
    have h1 := ih (fun j hj => hP j (hs j hj)) (fun j hj => ha j (hs j hj)) (fun j hj => hb j (hs j hj))
      (fun j hj => hab j (hs j hj))
    have hi' := Finset.mem_insert_self i s
    have hA : |∏ j ∈ s, a j| ≤ ∏ j ∈ s, P j := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun j hj => ha j (hs j hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have e1 : a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j =
        (a i - b i) * ∏ j ∈ s, a j + b i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) := by ring
    rw [e1]
    calc _ ≤ |a i - b i| * |∏ j ∈ s, a j| + |b i| * |∏ j ∈ s, a j - ∏ j ∈ s, b j| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ (e * P i) * (∏ j ∈ s, P j) + P i * (s.card * e * ∏ j ∈ s, P j) :=
          add_le_add (mul_le_mul (hab i hi') hA (abs_nonneg _) (mul_nonneg he (hP i hi')))
            (mul_le_mul (hb i hi') h1 (abs_nonneg _) (hP i hi'))
      _ = _ := by push_cast; ring
theorem isAdmissible_update_vacant {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ) (i : G.GasSpin) :
    G.pairConstraint.IsAdmissible (Function.update σ i (G.pairConstraint.vacant i)) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.isAdmissible_update_vacant <;> assumption
theorem isAdmissible_vacant_of_update {σ : G.Config} {i : G.GasSpin} {v : G.SpinValue i}
    (h : G.pairConstraint.IsAdmissible (Function.update σ i v)) :
    G.pairConstraint.IsAdmissible (Function.update σ i (G.pairConstraint.vacant i)) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasColumns.isAdmissible_update_vacant <;> assumption
variable (A : ι → ResponseSetup R) (f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (G)
def bound (j : ι) (σ : G.Config) : ℝ :=
  4 * lowerSizeConst (A j) (f j) * ResponseInTheExpansion.spinScore (A j) G (lowerSites (f j)) σ
def meanOnAdmissible (j : ι) (σ : G.Config) : ℝ :=
  open Classical in if G.pairConstraint.IsAdmissible σ then gasSupportMean (A j) G (f j) σ else 0
def boundProd (J : Finset ι) (σ : G.Config) : ℝ := ∏ j ∈ J, bound G A f j σ
def meanProd (J : Finset ι) (σ : G.Config) : ℝ := ∏ j ∈ J, meanOnAdmissible G A f j σ
def blocksOfFamily (J : Finset ι) : Finset (TorusSite n) := J.biUnion fun j => upperSites (f j)
def sitesOfFamily (J : Finset ι) : Finset (TorusSite (n * R.params.side)) := J.biUnion fun j => lowerSites (f j)
structure FamilyHyp (s : R.labels.Ω → ℝ) (J : Finset ι) : Prop where
  score_eq : ∀ j ∈ J, (A j).score = s
  score_nonneg : ∀ w, 0 ≤ s w
  measurable_score : Measurable s
  measurable_mean : ∀ j ∈ J, Measurable (meanOnAdmissible G A f j)
  abs_le_bound : ∀ j ∈ J, ∀ σ, G.pairConstraint.IsAdmissible σ → |gasSupportMean (A j) G (f j) σ| ≤ bound G A f j σ
  abs_sub_vacant_le : ∀ j ∈ J, ∀ (σ : G.Config) (i : G.GasSpin) (v : G.SpinValue i) (m : ℕ),
    G.pairConstraint.IsAdmissible (Function.update σ i v) → (R.range : ℝ) / (4 * R.params.side) ≤ m →
    (∀ Y ∈ upperSites (f j), m + 2 ≤ setGap {Y} i.1.core) →
    |gasSupportMean (A j) G (f j) (Function.update σ i v) -
        gasSupportMean (A j) G (f j) (Function.update σ i (G.pairConstraint.vacant i))| ≤
      bound G A f j (Function.update σ i (G.pairConstraint.vacant i)) * Real.exp (-(R.params.rt * m / 2 ^ 5))
  lowerSizeConst_pos : ∀ j ∈ J, 0 < lowerSizeConst (A j) (f j)
  parentBlock_mem : ∀ j ∈ J, ∀ y ∈ lowerSites (f j), parentBlock R.params.side y ∈ upperSites (f j)
  disjoint_lowerSites : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → Disjoint (lowerSites (f j)) (lowerSites (f k))
variable {A f G} {s : R.labels.Ω → ℝ} {J : Finset ι}
theorem FamilyHyp.mono {J' : Finset ι} (h : FamilyHyp G A f s J) (hJ : J' ⊆ J) : FamilyHyp G A f s J' where
  score_eq j hj := h.score_eq j (hJ hj)
  score_nonneg := h.score_nonneg
  measurable_score := h.measurable_score
  measurable_mean j hj := h.measurable_mean j (hJ hj)
  abs_le_bound j hj := h.abs_le_bound j (hJ hj)
  abs_sub_vacant_le j hj := h.abs_sub_vacant_le j (hJ hj)
  lowerSizeConst_pos j hj := h.lowerSizeConst_pos j (hJ hj)
  parentBlock_mem j hj := h.parentBlock_mem j (hJ hj)
  disjoint_lowerSites j hj k hk := h.disjoint_lowerSites j (hJ hj) k (hJ hk)
theorem FamilyHyp.score_nonneg_of_mem (h : FamilyHyp G A f s J) {j : ι} (hj : j ∈ J) : ∀ w, 0 ≤ (A j).score w := by
  rw [h.score_eq j hj]
  exact h.score_nonneg
theorem FamilyHyp.bound_pos (h : FamilyHyp G A f s J) {j : ι} (hj : j ∈ J) (σ : G.Config) : 0 < bound G A f j σ := by
  have h1 := one_le_spinScore (G := G) (h.score_nonneg_of_mem hj) (lowerSites (f j)) σ
  have h2 := h.lowerSizeConst_pos j hj
  unfold bound
  positivity
theorem FamilyHyp.boundProd_pos (h : FamilyHyp G A f s J) (σ : G.Config) : 0 < boundProd G A f J σ :=
  Finset.prod_pos fun j hj => h.bound_pos hj σ
theorem FamilyHyp.measurable_bound (h : FamilyHyp G A f s J) {j : ι} (hj : j ∈ J) : Measurable (bound G A f j) := by
  have hb : Measurable (A j).score := by
    rw [h.score_eq j hj]
    exact h.measurable_score
  exact (measurable_spinScore hb _).const_mul _
theorem FamilyHyp.measurable_boundProd (h : FamilyHyp G A f s J) : Measurable (boundProd G A f J) :=
  Finset.measurable_fun_prod _ fun j hj => h.measurable_bound hj
theorem FamilyHyp.measurable_meanProd (h : FamilyHyp G A f s J) : Measurable (meanProd G A f J) :=
  Finset.measurable_fun_prod _ fun j hj => h.measurable_mean j hj
theorem FamilyHyp.abs_meanOnAdmissible_le (h : FamilyHyp G A f s J) {j : ι} (hj : j ∈ J) {σ : G.Config}
    (hσ : G.pairConstraint.IsAdmissible σ) : |meanOnAdmissible G A f j σ| ≤ bound G A f j σ := by
  classical
  unfold meanOnAdmissible
  rw [if_pos hσ]
  exact h.abs_le_bound j hj σ hσ
theorem FamilyHyp.abs_meanProd_le (h : FamilyHyp G A f s J) {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ) :
    |meanProd G A f J σ| ≤ boundProd G A f J σ := by
  unfold meanProd boundProd
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun j hj => h.abs_meanOnAdmissible_le hj hσ
theorem FamilyHyp.boundProd_update_le (h : FamilyHyp G A f s J) (σ : G.Config) (i : G.GasSpin) (v : G.SpinValue i) :
    boundProd G A f J (Function.update σ i v) ≤ boundProd G A f J (Function.update σ i (G.pairConstraint.vacant i)) *
      Real.exp (∑ y ∈ sitesOfFamily f J, spinLabelScore s G i y v) := by
  classical
  have hdis : (J : Set ι).PairwiseDisjoint fun j => lowerSites (f j) := fun j hj k hk hjk =>
    h.disjoint_lowerSites j hj k hk hjk
  have e1 : ∑ y ∈ sitesOfFamily f J, spinLabelScore s G i y v =
      ∑ j ∈ J, ∑ y ∈ lowerSites (f j), spinLabelScore s G i y v :=
    Finset.sum_biUnion hdis
  rw [e1, Real.exp_sum]
  unfold boundProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun j hj => (h.bound_pos hj _).le) fun j hj => ?_
  have h1 := spinScore_update_le (G := G) (h.score_nonneg_of_mem hj) (lowerSites (f j)) σ i v
  rw [h.score_eq j hj] at h1
  have h2 := (h.lowerSizeConst_pos j hj).le
  unfold bound
  calc _ ≤ 4 * lowerSizeConst (A j) (f j) * (ResponseInTheExpansion.spinScore (A j) G (lowerSites (f j))
        (Function.update σ i (G.pairConstraint.vacant i)) *
        Real.exp (∑ y ∈ lowerSites (f j), spinLabelScore s G i y v)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring
theorem spinScore_update_eq {B : ResponseSetup R} {S : Finset (TorusSite (n * R.params.side))} {σ : G.Config}
    {i : G.GasSpin} (v : G.SpinValue i) (hS : ∀ y ∈ S, y ∉ i.1.2) :
    ResponseInTheExpansion.spinScore B G S (Function.update σ i v) =
      ResponseInTheExpansion.spinScore B G S (Function.update σ i (G.pairConstraint.vacant i)) := by
  unfold ResponseInTheExpansion.spinScore
  congr 2
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [sum_spinLabelScore_update B.score σ i v y, spinLabelScore_of_not_mem (hS y hy), add_zero]
theorem setGap_le_supDist {X X' : Finset (TorusSite n)} {y y' : TorusSite n} (hy : y ∈ X) (hy' : y' ∈ X') :
    setGap X X' ≤ supDist y y' :=
  Nat.sInf_le ⟨y, hy, y', hy', rfl⟩
theorem FamilyHyp.not_mem_support (h : FamilyHyp G A f s J) {j : ι} (hj : j ∈ J) {i : G.GasSpin} {m : ℕ}
    (hg : ∀ Y ∈ blocksOfFamily f J, m + 2 ≤ setGap {Y} i.1.core) : ∀ y ∈ lowerSites (f j), y ∉ i.1.2 := by
  intro y hy hyi
  have h1 : parentBlock R.params.side y ∈ i.1.core := GasSupport.parentBlock_mem_core (Finset.mem_union_right _ hyi)
  have h2 := setGap_le_supDist (Finset.mem_singleton_self (parentBlock R.params.side y)) h1
  rw [supDist_self] at h2
  have h3 := hg _ (Finset.mem_biUnion.mpr ⟨j, hj, h.parentBlock_mem j hj y hy⟩)
  omega
theorem FamilyHyp.boundProd_update_eq (h : FamilyHyp G A f s J) {i : G.GasSpin} {m : ℕ}
    (hg : ∀ Y ∈ blocksOfFamily f J, m + 2 ≤ setGap {Y} i.1.core) (σ : G.Config) (v : G.SpinValue i) :
    boundProd G A f J (Function.update σ i v) = boundProd G A f J (Function.update σ i (G.pairConstraint.vacant i)) := by
  unfold boundProd bound
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [spinScore_update_eq v (h.not_mem_support hj hg)]
theorem FamilyHyp.isGasTilt_boundProd (h : FamilyHyp G A f s J) {e : ℝ} (he : 0 ≤ e) :
    IsGasTilt G s (blocksOfFamily f J) (sitesOfFamily f J) e fun σ => 2 * boundProd G A f J σ where
  measurable := h.measurable_boundProd.const_mul 2
  pos σ _ := by
    have := h.boundProd_pos σ
    positivity
  update_le σ i v _ := by
    have h1 := h.boundProd_update_le σ i v
    have h0 := (h.boundProd_pos (Function.update σ i (G.pairConstraint.vacant i))).le
    have hE := Real.exp_pos (∑ y ∈ sitesOfFamily f J, spinLabelScore s G i y v)
    nlinarith [mul_nonneg h0 hE.le]
  abs_update_sub_le σ i v m _ _ hg := by
    rw [h.boundProd_update_eq hg σ v, sub_self, abs_zero]
    have h0 := (h.boundProd_pos (Function.update σ i (G.pairConstraint.vacant i))).le
    positivity
theorem FamilyHyp.isGasTilt_boundProd_add (h : FamilyHyp G A f s J) {e : ℝ} (he : (J.card : ℝ) ≤ e) :
    IsGasTilt G s (blocksOfFamily f J) (sitesOfFamily f J) e fun σ => 2 * boundProd G A f J σ + meanProd G A f J σ where
  measurable := (h.measurable_boundProd.const_mul 2).add h.measurable_meanProd
  pos σ hσ := by
    have h1 := h.abs_meanProd_le hσ
    have h2 := h.boundProd_pos σ
    have h3 := (abs_le.mp h1).1
    linarith
  update_le σ i v hv := by
    have h₀ := isAdmissible_vacant_of_update hv
    have h1 := h.boundProd_update_le σ i v
    have h2 := (abs_le.mp (h.abs_meanProd_le hv)).2
    have h3 := (abs_le.mp (h.abs_meanProd_le h₀)).1
    have hU := h.boundProd_pos (Function.update σ i (G.pairConstraint.vacant i))
    set Ex := Real.exp (∑ y ∈ sitesOfFamily f J, spinLabelScore s G i y v) with hEx
    have hE : 0 < Ex := Real.exp_pos _
    set Y₀ := 2 * boundProd G A f J (Function.update σ i (G.pairConstraint.vacant i)) +
      meanProd G A f J (Function.update σ i (G.pairConstraint.vacant i)) with hY₀
    have h4 : boundProd G A f J (Function.update σ i (G.pairConstraint.vacant i)) ≤ Y₀ := by
      rw [hY₀]
      linarith
    calc _ ≤ 3 * boundProd G A f J (Function.update σ i v) := by linarith
      _ ≤ 3 * (boundProd G A f J (Function.update σ i (G.pairConstraint.vacant i)) * Ex) := by linarith
      _ ≤ 3 * (Y₀ * Ex) := by
          have := mul_le_mul_of_nonneg_right h4 hE.le
          linarith
      _ = _ := by ring
  abs_update_sub_le σ i v m hv hm hg := by
    have h₀ := isAdmissible_vacant_of_update hv
    set σ₁ := Function.update σ i v with hσ₁
    set σ₀ := Function.update σ i (G.pairConstraint.vacant i) with hσ₀
    set E := Real.exp (-(R.params.rt * m / 2 ^ 5)) with hE
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hUe : boundProd G A f J σ₁ = boundProd G A f J σ₀ := h.boundProd_update_eq hg σ v
    have hbe : ∀ j ∈ J, bound G A f j σ₁ = bound G A f j σ₀ := fun j hj => by
      unfold bound
      rw [hσ₁, spinScore_update_eq v (h.not_mem_support hj hg)]
    have key := abs_prod_sub_prod_le (a := fun j => meanOnAdmissible G A f j σ₁)
      (b := fun j => meanOnAdmissible G A f j σ₀)
      (P := fun j => bound G A f j σ₀) hE0 J (fun j hj => (h.bound_pos hj _).le)
      (fun j hj => (h.abs_meanOnAdmissible_le hj hv).trans (hbe j hj).le)
      (fun j hj => h.abs_meanOnAdmissible_le hj h₀)
      (fun j hj => by
        classical
        simp only [meanOnAdmissible, if_pos hv, if_pos h₀]
        have h1 := h.abs_sub_vacant_le j hj σ i v m hv hm fun Y hY => hg Y (Finset.mem_biUnion.mpr ⟨j, hj, hY⟩)
        rw [mul_comm E]
        exact h1)
    have e1 : (2 * boundProd G A f J σ₁ + meanProd G A f J σ₁) - (2 * boundProd G A f J σ₀ + meanProd G A f J σ₀) =
        ∏ j ∈ J, meanOnAdmissible G A f j σ₁ - ∏ j ∈ J, meanOnAdmissible G A f j σ₀ := by
      rw [hUe]
      simp only [meanProd]
      ring
    rw [e1]
    refine key.trans ?_
    have hU := h.boundProd_pos σ₀
    have h3 := (abs_le.mp (h.abs_meanProd_le h₀)).1
    have h4 : boundProd G A f J σ₀ ≤ 2 * boundProd G A f J σ₀ + meanProd G A f J σ₀ := by linarith
    have hc0 : (0 : ℝ) ≤ J.card := Nat.cast_nonneg _
    calc (J.card : ℝ) * E * ∏ j ∈ J, bound G A f j σ₀ = (J.card : ℝ) * E * boundProd G A f J σ₀ := rfl
      _ ≤ e * E * boundProd G A f J σ₀ := by gcongr
      _ ≤ e * E * (2 * boundProd G A f J σ₀ + meanProd G A f J σ₀) :=
          mul_le_mul_of_nonneg_left h4 (mul_nonneg (hc0.trans he) hE0)
theorem exp_mul_le_convex {t S : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.exp (t * S) ≤ 1 - t + t * Real.exp S := by
  have := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ S) (by linarith : 0 ≤ 1 - t) h0 (by ring)
  simpa using this
theorem exp_sub_one_le {a S t c : ℝ} (ht : 0 ≤ t) (hS : 0 ≤ S) (h1 : a ≤ S) (h2 : a ≤ t * S) (hc : S ≤ c) :
    Real.exp a - 1 ≤ t * Real.exp c := by
  have hE : Real.exp S ≤ Real.exp c := Real.exp_le_exp.mpr hc
  have hE1 : 1 ≤ Real.exp S := Real.one_le_exp hS
  by_cases h : 1 ≤ t
  · have a1 : Real.exp a ≤ Real.exp S := Real.exp_le_exp.mpr h1
    nlinarith
  · have ht1 : t ≤ 1 := (not_le.mp h).le
    have a1 : Real.exp a ≤ Real.exp (t * S) := Real.exp_le_exp.mpr h2
    have a2 := exp_mul_le_convex (S := S) ht ht1
    nlinarith
theorem sum_spinLabelScore_le {B₀ : ResponseSetup R} (hs : ∀ w, 0 ≤ B₀.score w)
    (B : Finset (TorusSite (n * R.params.side))) (i : G.GasSpin) (v : G.SpinValue i) :
    ∑ y ∈ B, spinLabelScore B₀.score G i y v ≤ WeightedResponses.spinScore B₀ i v := by apply _root_.YangMills.Construction.TiltedGasResponse.sum_spinLabelScore_le_spinScore <;> assumption
theorem FamilyHyp.expectation_boundProd_le {A₀ : ResponseSetup R} (hA₀ : A₀.score = s) (hP : MeanOfProductStatement)
    (h : FamilyHyp G A f s J) {z : G.GasSpin → ℝ}
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight z)
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A₀ i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (z i) * G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsum : ∀ y : TorusSite (n * R.params.side), (open Classical in ∑ i : G.GasSpin, if y ∈ i.1.2 then z i else 0) ≤ δ)
    {Nn : ι → ℝ} (hNn : ∀ j ∈ J, 1 + ((lowerSites (f j)).card : ℝ)⁻¹ *
      ∑ y ∈ lowerSites (f j), recordedSiteScore (A j) G y ≤ Nn j) (hN1 : ∀ j ∈ J, 1 ≤ Nn j) :
    G.expectation ∅ (boundProd G A f J) ≤
      (∏ j ∈ J, 4 * lowerSizeConst (A j) (f j)) * (∏ j ∈ J, Nn j) * Real.exp (J.card * δ) := by
  classical
  have hs := h.score_nonneg
  have hb := h.measurable_score
  have hz0 := hw.activity_nonneg
  set cA : ι → ℝ := fun j => ((lowerSites (f j)).card : ℝ)⁻¹ with hcA
  have hcA0 : ∀ j, 0 ≤ cA j := fun j => by simp only [hcA]; positivity
  have hcard : ∀ j ∈ J, (0 : ℝ) < ((lowerSites (f j)).card : ℝ) := by
    intro j hj
    have h1 := h.lowerSizeConst_pos j hj
    unfold lowerSizeConst at h1
    rcases Nat.eq_zero_or_pos (lowerSites (f j)).card with h0 | h0
    · rw [h0] at h1
      simp at h1
    · exact_mod_cast h0
  have hcA1 : ∀ j ∈ J, cA j ≤ 1 := fun j hj => by
    have : (1 : ℝ) ≤ ((lowerSites (f j)).card : ℝ) := by
      have h1 := hcard j hj
      have h2 : 0 < (lowerSites (f j)).card := by exact_mod_cast h1
      exact_mod_cast h2
    exact inv_le_one_of_one_le₀ this
  set La : ∀ i : G.GasSpin, G.SpinValue i → ℝ := fun i v =>
    ∑ j ∈ J, cA j * ∑ y ∈ lowerSites (f j), spinLabelScore s G i y v with hLa
  set gf : ∀ i : G.GasSpin, G.SpinValue i → ℝ := fun i v => Real.exp (La i v) with hgf
  set tt : G.GasSpin → ℝ := fun i =>
    ∑ j ∈ J, cA j * ∑ y ∈ lowerSites (f j), (if y ∈ i.1.2 then (1 : ℝ) else 0) with htt
  have htt0 : ∀ i, 0 ≤ tt i := fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hcA0 j)
    (Finset.sum_nonneg fun y _ => by split_ifs <;> norm_num)
  have hLa0 : ∀ i v, 0 ≤ La i v := fun i v => Finset.sum_nonneg fun j _ => mul_nonneg (hcA0 j)
    (Finset.sum_nonneg fun y _ => spinLabelScore_nonneg hs i y v)
  have hdis : (J : Set ι).PairwiseDisjoint fun j => lowerSites (f j) := fun j hj k hk hjk =>
    h.disjoint_lowerSites j hj k hk hjk
  have hone : ∀ i v, Real.exp (La i v) - 1 ≤ tt i * Real.exp (WeightedResponses.spinScore A₀ i v) := by
    intro i v
    set S := ∑ y ∈ sitesOfFamily f J, spinLabelScore s G i y v with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun y _ => spinLabelScore_nonneg hs i y v
    have hSsum : S = ∑ j ∈ J, ∑ y ∈ lowerSites (f j), spinLabelScore s G i y v := Finset.sum_biUnion hdis
    have a1 : La i v ≤ S := by
      rw [hSsum]
      refine Finset.sum_le_sum fun j hj => ?_
      have : 0 ≤ ∑ y ∈ lowerSites (f j), spinLabelScore s G i y v :=
        Finset.sum_nonneg fun y _ => spinLabelScore_nonneg hs i y v
      nlinarith [hcA1 j hj]
    have a2 : La i v ≤ tt i * S := by
      simp only [hLa, htt, Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (hcA0 j)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun y hy => ?_
      by_cases hyi : y ∈ i.1.2
      · rw [if_pos hyi, one_mul]
        exact Finset.single_le_sum (f := fun y => spinLabelScore s G i y v) (fun y _ => spinLabelScore_nonneg hs i y v)
          (Finset.mem_biUnion.mpr ⟨j, hj, hy⟩)
      · rw [if_neg hyi, zero_mul, spinLabelScore_of_not_mem hyi]
    have a3 : S ≤ WeightedResponses.spinScore A₀ i v := by
      have := sum_spinLabelScore_le (G := G) (B₀ := A₀) (by rw [hA₀]; exact hs) (sitesOfFamily f J) i v
      rwa [hA₀] at this
    exact exp_sub_one_le (htt0 i) hS0 a1 a2 a3
  have hm : ∀ i, Measurable (gf i) := fun i => by
    refine Real.measurable_exp.comp (Finset.measurable_fun_sum _ fun j _ => Measurable.const_mul
      (Finset.measurable_fun_sum _ fun y _ => measurable_spinLabelScore hb i y) _)
  have hx : G.pairConstraint.HasSmallExcess (G.referenceMeasure ∅) G.weight gf (fun i => tt i * z i) := by
    intro i σ hσ
    have pt : ∀ v, ENNReal.ofReal (gf i v - 1) * G.pairConstraint.weightDensity G.weight (Function.update σ i v) ≤
        ENNReal.ofReal (tt i) * (ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A₀ i v)) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i v)) := by
      intro v
      rw [← mul_assoc, ← ENNReal.ofReal_mul (htt0 i)]
      gcongr
      exact hone i v
    calc _ ≤ ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (tt i) *
          (ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A₀ i v)) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i v)) ∂(G.referenceMeasure ∅ i) := lintegral_mono pt
      _ = ENNReal.ofReal (tt i) * ∫⁻ v in {G.pairConstraint.vacant i}ᶜ,
          ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A₀ i v)) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (tt i) * (ENNReal.ofReal (z i) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i))) := by
          gcongr
          exact paid i σ hσ
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (htt0 i)]
  have hc : 0 ≤ (∏ j ∈ J, 4 * lowerSizeConst (A j) (f j)) * ∏ j ∈ J, Nn j :=
    mul_nonneg (Finset.prod_nonneg fun j hj => by have := h.lowerSizeConst_pos j hj; positivity)
      (Finset.prod_nonneg fun j hj => by linarith [hN1 j hj])
  have hH : ∀ σ, boundProd G A f J σ ≤
      ((∏ j ∈ J, 4 * lowerSizeConst (A j) (f j)) * ∏ j ∈ J, Nn j) * ∏ i, gf i (σ i) := by
    intro σ
    set aa : ι → ℝ := fun j => cA j * ∑ y ∈ lowerSites (f j), ∑ i, spinLabelScore s G i y (σ i) with haa
    have e1 : ∏ i, gf i (σ i) = Real.exp (∑ j ∈ J, aa j) := by
      simp only [hgf]
      rw [← Real.exp_sum]
      congr 1
      simp only [hLa, haa]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.mul_sum, Finset.sum_comm]
    have hj1 : ∀ j ∈ J, ResponseInTheExpansion.spinScore (A j) G (lowerSites (f j)) σ ≤ Nn j * Real.exp (aa j) := by
      intro j hj
      have e2 : ResponseInTheExpansion.spinScore (A j) G (lowerSites (f j)) σ =
          (1 + cA j * ∑ y ∈ lowerSites (f j), recordedSiteScore (A j) G y) + aa j := by
        simp only [ResponseInTheExpansion.spinScore, haa, hcA, h.score_eq j hj, Finset.sum_add_distrib]
        ring
      have a0 : 0 ≤ aa j := mul_nonneg (hcA0 j) (Finset.sum_nonneg fun y _ =>
        Finset.sum_nonneg fun i _ => spinLabelScore_nonneg hs i y _)
      have a1 := hNn j hj
      have a2 : 1 + aa j ≤ Real.exp (aa j) := by linarith [Real.add_one_le_exp (aa j)]
      have a3 := hN1 j hj
      rw [e2]
      nlinarith
    rw [e1, Real.exp_sum, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun j hj => (h.bound_pos hj σ).le) fun j hj => ?_
    have hK : 0 ≤ 4 * lowerSizeConst (A j) (f j) := by have := h.lowerSizeConst_pos j hj; positivity
    calc bound G A f j σ ≤ 4 * lowerSizeConst (A j) (f j) * (Nn j * Real.exp (aa j)) :=
          mul_le_mul_of_nonneg_left (hj1 j hj) hK
      _ = _ := by ring
  have hres := FreeEnergies.expectation_le_mul_prod hP hw gf (fun i => tt i * z i) hm
    (fun i v => Real.one_le_exp (hLa0 i v))
    (fun i => by
      have : La i (G.pairConstraint.vacant i) = 0 := Finset.sum_eq_zero fun j _ => by
        have : ∑ y ∈ lowerSites (f j), spinLabelScore s G i y (G.pairConstraint.vacant i) = 0 :=
          Finset.sum_eq_zero fun y _ => rfl
        rw [this, mul_zero]
      simp only [hgf, this, Real.exp_zero])
    (fun i => mul_nonneg (htt0 i) (hz0 i)) hx hc (fun σ => ?_) hH
  · have hsumE : ∑ i, tt i * z i ≤ J.card * δ := by
      have e1 : ∑ i, tt i * z i =
          ∑ j ∈ J, cA j * ∑ y ∈ lowerSites (f j), ∑ i : G.GasSpin, if y ∈ i.1.2 then z i else 0 := by
        simp only [htt, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
      rw [e1]
      calc _ ≤ ∑ _j ∈ J, δ := Finset.sum_le_sum fun j hj => by
            have h1 : ∑ y ∈ lowerSites (f j), (∑ i : G.GasSpin, if y ∈ i.1.2 then z i else 0) ≤
                ((lowerSites (f j)).card : ℝ) * δ := by
              calc _ ≤ ∑ _y ∈ lowerSites (f j), δ := Finset.sum_le_sum fun y _ => hsum y
                _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
            have hc' := hcard j hj
            calc cA j * _ ≤ cA j * (((lowerSites (f j)).card : ℝ) * δ) := mul_le_mul_of_nonneg_left h1 (hcA0 j)
              _ = δ := by
                  simp only [hcA]
                  field_simp
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hprod : ∏ i, (1 + tt i * z i) ≤ Real.exp (J.card * δ) := by
      calc ∏ i, (1 + tt i * z i) ≤ ∏ i, Real.exp (tt i * z i) :=
            Finset.prod_le_prod (fun i _ => by have := mul_nonneg (htt0 i) (hz0 i); linarith) fun i _ => by
              linarith [Real.add_one_le_exp (tt i * z i)]
        _ = Real.exp (∑ i, tt i * z i) := (Real.exp_sum _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr hsumE
    exact hres.trans (mul_le_mul_of_nonneg_left hprod hc)
  · exact (h.boundProd_pos σ).le
end Tilts
section Weights
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n}
theorem parentBlock_mem_weightSupportSites {L t n : ℕ} [NeZero L] [NeZero n] (f : PlaquetteWeight (fineSide L (t + 1) n))
    {y : TorusSite (n * L)} (hy : y ∈ weightSupportSites L t (n * L) f) :
    parentBlock L y ∈ weightSupportSites L (t + 1) n f := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.parentBlock_mem_weightSupportSites <;> assumption
theorem image_parentBlock_weightSupportSites {L t n : ℕ} [NeZero L] [NeZero n]
    (f : PlaquetteWeight (fineSide L (t + 1) n)) :
    (open Classical in (weightSupportSites L t (n * L) f).image (parentBlock L)) = weightSupportSites L (t + 1) n f := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.image_parentBlock_weightSupportSites <;> assumption
theorem isActivityBounded_tilt {A₀ : ResponseSetup R} {Q : Finset (TorusSite n)}
    {B : Finset (TorusSite (n * R.params.side))} {e c : ℝ}
    {Yt : G.Config → ℝ} (hs : ∀ w, 0 ≤ A₀.score w)
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A₀ i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    (ht : IsGasTilt G A₀.score Q B e Yt) :
    G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) (fun σ => G.weight σ * Yt σ)
      fun i => 3 * G.spinActivity c i := by
  classical
  refine ⟨hw.measurableSet_admissible, hw.measurable.mul ht.measurable,
    fun σ h => mul_pos (hw.pos_of_admissible σ h) (ht.pos σ h),
    hw.measurableSet_vacant, hw.measure_vacant, fun i => by have := hw.activity_nonneg i; positivity,
    fun i σ hσ => ?_⟩
  have hadm := isAdmissible_update_vacant hσ i
  set σ₀ := Function.update σ i (G.pairConstraint.vacant i) with hσ₀
  set y₀ := Yt σ₀ with hy₀
  have hy0 : 0 < y₀ := ht.pos _ hadm
  have hz0 : 0 ≤ G.spinActivity c i := hw.activity_nonneg i
  have hwt0 : 0 < G.weight σ₀ := hw.pos_of_admissible _ hadm
  have point : ∀ v, G.pairConstraint.weightDensity (fun σ => G.weight σ * Yt σ) (Function.update σ i v) ≤
      ENNReal.ofReal (3 * y₀) * (ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A₀ i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v)) := by
    intro v
    unfold PairConstraint.weightDensity
    by_cases ha : G.pairConstraint.IsAdmissible (Function.update σ i v)
    · rw [if_pos ha, if_pos ha]
      have hwt := hw.pos_of_admissible _ ha
      have hr := ht.update_le σ i v ha
      have hl := sum_spinLabelScore_le (G := G) hs B i v
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have k1 : Yt (Function.update σ i v) ≤ 3 * y₀ * Real.exp (WeightedResponses.spinScore A₀ i v) := by
        have hE : Real.exp (∑ y ∈ B, spinLabelScore A₀.score G i y v) ≤
            Real.exp (WeightedResponses.spinScore A₀ i v) := Real.exp_le_exp.mpr hl
        calc _ ≤ 3 * Real.exp (∑ y ∈ B, spinLabelScore A₀.score G i y v) * y₀ := hr
          _ ≤ 3 * Real.exp (WeightedResponses.spinScore A₀ i v) * y₀ := by gcongr
          _ = _ := by ring
      calc G.weight (Function.update σ i v) * Yt (Function.update σ i v)
          ≤ G.weight (Function.update σ i v) * (3 * y₀ * Real.exp (WeightedResponses.spinScore A₀ i v)) :=
            mul_le_mul_of_nonneg_left k1 hwt.le
        _ = _ := by ring
    · rw [if_neg ha, if_neg ha]
      simp
  calc _ ≤ ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (3 * y₀) *
          (ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A₀ i v)) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i v)) ∂(G.referenceMeasure ∅ i) :=
        lintegral_mono point
    _ = ENNReal.ofReal (3 * y₀) * ∫⁻ v in {G.pairConstraint.vacant i}ᶜ,
          ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A₀ i v)) *
          G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (3 * y₀) * (ENNReal.ofReal (G.spinActivity c i) * G.pairConstraint.weightDensity G.weight σ₀) := by
        gcongr
        exact paid i σ hσ
    _ = _ := by
        unfold PairConstraint.weightDensity
        rw [if_pos hadm, if_pos hadm, ← ENNReal.ofReal_mul hz0, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
theorem sum_spinActivity_le (hgas : GasSumNearBlockBound) {c : ℝ} (hfit : R.params.Admissible) (hc0 : 0 < c)
    (hcf : R.params.RangeFloor c) (hy : R.params.y₁ ≤ R.coupling) (hrt : 0 < R.params.rt)
    (hz0 : ∀ i, 0 ≤ G.spinActivity c i) (y : TorusSite (n * R.params.side)) :
    (open Classical in ∑ i : G.GasSpin, if y ∈ i.1.2 then G.spinActivity c i else 0) ≤
      Real.exp (-(8 * c * R.coupling)) * (2 / (1 - Real.exp (-(1 / 4)))) ^ 4 := by
  classical
  have := hgas R n G c 1 1 (parentBlock R.params.side y) (Finset.univ.filter fun i : G.GasSpin => y ∈ i.1.2)
    (fun i => G.spinActivity c i) hfit hc0 hcf hy one_pos zero_le_one (fun i hi => by
      have hyi : y ∈ i.1.2 := (Finset.mem_filter.mp hi).2
      have h1 : parentBlock R.params.side y ∈ i.1.core :=
        GasSupport.parentBlock_mem_core (Finset.mem_union_right _ hyi)
      have h2 : setGap {parentBlock R.params.side y} i.1.core = 0 := by
        have := setGap_le_supDist (Finset.mem_singleton_self (parentBlock R.params.side y)) h1
        rw [supDist_self] at this
        omega
      rw [h2]
      have hN : (1 : ℝ) ≤ (i.1.core.card : ℝ) := by
        have : 0 < i.1.core.card := Finset.card_pos.mpr ⟨_, h1⟩
        exact_mod_cast this
      have hN4 : (1 : ℝ) ≤ (i.1.core.card : ℝ) ^ 4 := one_le_pow₀ hN
      have hE : 1 ≤ Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ)) := Real.one_le_exp (by positivity)
      have hz := hz0 i
      simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one, one_mul]
      have : 1 ≤ (i.1.core.card : ℝ) ^ 4 * Real.exp (2 * R.params.rt * (i.1.coreDiam : ℝ)) := by nlinarith
      nlinarith)
  rw [← Finset.sum_filter]
  simpa using this
theorem coarseSiteScore_nonneg {A : ResponseSetup R} (hs : ∀ w, 0 ≤ A.score w) (h₁ : 0 ≤ A.responseParams.s₁)
    (Y : TorusSite n) : 0 ≤ coarseSiteScore A G.state Y :=
  siteScore_nonneg (fun w => by
    rcases w with u | st
    · exact h₁
    · show 0 ≤ coarseLabelScore A.responseParams.s₁ A.score (Sum.inr st)
      simp only [coarseLabelScore]
      refine add_nonneg h₁ (Finset.sum_nonneg fun o _ => ?_)
      rcases st.siteLabel o with u | a
      · simp
      · exact hs a) _ _ _
theorem meanSiteScore_bounds {A : ResponseSetup R} (hs : ∀ w, 0 ≤ A.score w) (h₁ : 0 ≤ A.responseParams.s₁)
    (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (hne : (upperSites f).Nonempty) :
    1 ≤ meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites f) G.state.1 G.state.2 ∧
    1 + ((lowerSites f).card : ℝ)⁻¹ * ∑ y ∈ lowerSites f, recordedSiteScore A G y ≤
      meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites f) G.state.1 G.state.2 := by
  classical
  have h0 := sum_recordedSiteScore_le_parentBlocks (G := G) hs h₁ (lowerSites f)
  have hpar : parentBlocks (lowerSites f) = upperSites f := image_parentBlock_weightSupportSites f
  rw [hpar] at h0
  set Sa := ∑ Y ∈ upperSites f, coarseSiteScore A G.state Y with hSa
  have hSa0 : 0 ≤ Sa := Finset.sum_nonneg fun Y _ => coarseSiteScore_nonneg hs h₁ Y
  have hcp : ((upperSites f).card : ℝ) ≤ ((lowerSites f).card : ℝ) := by
    have : (upperSites f).card ≤ (lowerSites f).card := by
      rw [← hpar]
      exact Finset.card_image_le
    exact_mod_cast this
  have hc1 : (0 : ℝ) < ((upperSites f).card : ℝ) := by exact_mod_cast hne.card_pos
  have hc2 : (0 : ℝ) < ((lowerSites f).card : ℝ) := by linarith
  have e1 : meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score) (upperSites f) G.state.1 G.state.2 =
      1 + ((upperSites f).card : ℝ)⁻¹ * Sa := rfl
  rw [e1]
  refine ⟨by have : 0 ≤ ((upperSites f).card : ℝ)⁻¹ * Sa := by positivity
             linarith, ?_⟩
  have h2 : ((lowerSites f).card : ℝ)⁻¹ * ∑ y ∈ lowerSites f, recordedSiteScore A G y ≤
      ((lowerSites f).card : ℝ)⁻¹ * Sa :=
    mul_le_mul_of_nonneg_left h0 (by positivity)
  have h3 : ((lowerSites f).card : ℝ)⁻¹ * Sa ≤ ((upperSites f).card : ℝ)⁻¹ * Sa :=
    mul_le_mul_of_nonneg_right (inv_anti₀ hc1 hcp) hSa0
  linarith
end Weights
section Split
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n} {ι : Type} [DecidableEq ι]
  {A : ι → ResponseSetup R} {f : ι → PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)} {s : R.labels.Ω → ℝ}
  {J : Finset ι} {c : ℝ} {A₀ : ResponseSetup R}
theorem tilt_integral_facts (hC : ActivityConditionalLawsStatement) (a₀ : A₀.score = s)
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A₀ i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    [hp : IsProbabilityMeasure (G.gibbsLaw ∅)] (hadm : ∀ᵐ σ ∂(G.gibbsLaw ∅), G.pairConstraint.IsAdmissible σ)
    (hs : ∀ w, 0 ≤ s w) {Q : Finset (TorusSite n)} {B : Finset (TorusSite (n * R.params.side))} {e : ℝ}
    {Yt : G.Config → ℝ} (ht : IsGasTilt G s Q B e Yt) :
    Integrable Yt (G.gibbsLaw ∅) ∧ 0 < ∫ σ, Yt σ ∂(G.gibbsLaw ∅) ∧ ∀ F : G.Config → ℝ,
      Integrable F (tiltedGibbsLaw G Yt) → Integrable (fun σ => F σ * Yt σ) (G.gibbsLaw ∅) ∧
        ∫ σ, F σ * Yt σ ∂(G.gibbsLaw ∅) = (∫ σ, Yt σ ∂(G.gibbsLaw ∅)) * ∫ σ, F σ ∂(tiltedGibbsLaw G Yt) := by
  subst a₀
  have hw' := isActivityBounded_tilt hs hw paid ht
  obtain ⟨p2, -, -, -⟩ := hC G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasure ∅) _ _ hw'
  have q1 : IsProbabilityMeasure (G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight) := hp
  exact @integral_mul_eq_of_tilt G.GasSpin _ _ G.SpinValue _ G.pairConstraint (G.referenceMeasure ∅) _ G.weight Yt _ _
    hw hw' ht.measurable ht.pos q1 p2 hadm
theorem integrable_boundProd (h : FamilyHyp G A f s J) (hC : ActivityConditionalLawsStatement) (a₀ : A₀.score = s)
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A₀ i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    [IsProbabilityMeasure (G.gibbsLaw ∅)] (hadm : ∀ᵐ σ ∂(G.gibbsLaw ∅), G.pairConstraint.IsAdmissible σ) :
    Integrable (boundProd G A f J) (G.gibbsLaw ∅) := by
  have h1 := (tilt_integral_facts hC a₀ hw paid hadm h.score_nonneg (h.isGasTilt_boundProd (e := 0) le_rfl)).1
  refine (h1.const_mul (1 / 2)).congr (Filter.Eventually.of_forall fun σ => ?_)
  simp only
  ring
theorem abs_covariance_meanProd_le (h : FamilyHyp G A f s J) (hC : ActivityConditionalLawsStatement)
    (a₀ : A₀.score = s)
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A₀ i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    [IsProbabilityMeasure (G.gibbsLaw ∅)] (hadm : ∀ᵐ σ ∂(G.gibbsLaw ∅), G.pairConstraint.IsAdmissible σ)
    {u : G.Config → ℝ} {Δ : ℝ}
    (hfar : ∀ {Yt : G.Config → ℝ}, IsGasTilt G s (blocksOfFamily f J) (sitesOfFamily f J) (J.card : ℝ) Yt →
      Integrable u (tiltedGibbsLaw G Yt) ∧ Integrable u (G.gibbsLaw ∅) ∧
      |∫ σ, u σ ∂(tiltedGibbsLaw G Yt) - G.expectation ∅ u| ≤ Δ) :
    Integrable (meanProd G A f J) (G.gibbsLaw ∅) ∧ Integrable (fun σ => u σ * meanProd G A f J σ) (G.gibbsLaw ∅) ∧
      |∫ σ, u σ * meanProd G A f J σ ∂(G.gibbsLaw ∅) -
          (∫ σ, u σ ∂(G.gibbsLaw ∅)) * ∫ σ, meanProd G A f J σ ∂(G.gibbsLaw ∅)| ≤
        5 * (∫ σ, boundProd G A f J σ ∂(G.gibbsLaw ∅)) * Δ := by
  have hs := h.score_nonneg
  have t₂ := h.isGasTilt_boundProd (e := (J.card : ℝ)) (Nat.cast_nonneg _)
  have t₁ := h.isGasTilt_boundProd_add (e := (J.card : ℝ)) le_rfl
  obtain ⟨i1, -, r1⟩ := tilt_integral_facts hC a₀ hw paid hadm hs t₁
  obtain ⟨i2, -, r2⟩ := tilt_integral_facts hC a₀ hw paid hadm hs t₂
  obtain ⟨f1, -, d1⟩ := hfar t₁
  obtain ⟨f2, -, d2⟩ := hfar t₂
  obtain ⟨iu1, e1⟩ := r1 u f1
  obtain ⟨iu2, e2⟩ := r2 u f2
  have iU : Integrable (boundProd G A f J) (G.gibbsLaw ∅) := integrable_boundProd h hC a₀ hw paid hadm
  have hU0 : 0 ≤ ∫ σ, boundProd G A f J σ ∂(G.gibbsLaw ∅) := integral_nonneg fun σ => (h.boundProd_pos σ).le
  have h2 : ∫ σ, 2 * boundProd G A f J σ ∂(G.gibbsLaw ∅) = 2 * ∫ σ, boundProd G A f J σ ∂(G.gibbsLaw ∅) :=
    integral_const_mul _ _
  have h1 : ∫ σ, (2 * boundProd G A f J σ + meanProd G A f J σ) ∂(G.gibbsLaw ∅) ≤
      3 * ∫ σ, boundProd G A f J σ ∂(G.gibbsLaw ∅) := by
    rw [← integral_const_mul]
    refine integral_mono_ae i1 (iU.const_mul 3) ?_
    filter_upwards [hadm] with σ hσ
    have := (abs_le.mp (h.abs_meanProd_le hσ)).2
    linarith
  have h0 : 0 ≤ ∫ σ, (2 * boundProd G A f J σ + meanProd G A f J σ) ∂(G.gibbsLaw ∅) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hadm] with σ hσ
    exact (t₁.pos σ hσ).le
  exact abs_covariance_le i1 i2 iu1 iu2 e1 e2 (Filter.Eventually.of_forall fun σ => by simp) d1 d2 h0 h1 h2 hU0
theorem induction_step_bound {cc δ Cf E7 V P D₁ D₂ mu Uq : ℝ} (hc : 0 ≤ cc) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hCf : 0 ≤ Cf)
    (hE7 : 0 ≤ E7) (hV : 0 ≤ V) (hP : 0 ≤ P) (hUq0 : 0 ≤ Uq) (hUq : Uq ≤ P * Real.exp (cc * δ))
    (hD₁ : D₁ ≤ 5 * Uq * (Cf * cc * (V / 4) * E7)) (hmu : |mu| ≤ V * Real.exp δ)
    (hD₂ : D₂ ≤ 2 * Cf * cc ^ 2 * Real.exp (2 * cc) * E7 * P) (hD₂0 : 0 ≤ D₂) :
    D₁ + |mu| * D₂ ≤ 2 * Cf * (cc + 1) ^ 2 * Real.exp (2 * (cc + 1)) * E7 * (V * P) := by
  set X := Cf * E7 * V * P with hX
  set T := Real.exp (2 * (cc + 1)) with hT
  have e1 : Real.exp (cc * δ) ≤ T := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have e2 : Real.exp δ * Real.exp (2 * cc) ≤ T := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have a1 : D₁ ≤ 5 / 4 * cc * T * X := by
    have b1 : Uq ≤ P * T := hUq.trans (mul_le_mul_of_nonneg_left e1 hP)
    calc D₁ ≤ 5 * Uq * (Cf * cc * (V / 4) * E7) := hD₁
      _ ≤ 5 * (P * T) * (Cf * cc * (V / 4) * E7) := by gcongr
      _ = _ := by rw [hX]; ring
  have a2 : |mu| * D₂ ≤ 2 * cc ^ 2 * T * X := by
    calc |mu| * D₂ ≤ (V * Real.exp δ) * (2 * Cf * cc ^ 2 * Real.exp (2 * cc) * E7 * P) :=
          mul_le_mul hmu hD₂ hD₂0 (by positivity)
      _ = (2 * cc ^ 2 * X) * (Real.exp δ * Real.exp (2 * cc)) := by rw [hX]; ring
      _ ≤ (2 * cc ^ 2 * X) * T := mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = _ := by ring
  have e3 : 2 * Cf * (cc + 1) ^ 2 * T * E7 * (V * P) = 2 * (cc + 1) ^ 2 * T * X := by
    rw [hX]
    ring
  rw [e3]
  have hTX : 0 ≤ T * X := by positivity
  have : 5 / 4 * cc + 2 * cc ^ 2 ≤ 2 * (cc + 1) ^ 2 := by nlinarith
  calc D₁ + |mu| * D₂ ≤ (5 / 4 * cc + 2 * cc ^ 2) * (T * X) := by
        have := add_le_add a1 a2
        calc _ ≤ _ := this
          _ = _ := by ring
    _ ≤ 2 * (cc + 1) ^ 2 * (T * X) := mul_le_mul_of_nonneg_right this hTX
    _ = _ := by ring
theorem abs_expectation_prod_sub_le {I : Finset ι} (h : FamilyHyp G A f s I) (hC : ActivityConditionalLawsStatement)
    (hP : MeanOfProductStatement) (a₀ : A₀.score = s)
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity c))
    (paid : ∀ (i : G.GasSpin) (σ : G.Config), G.pairConstraint.IsAdmissible σ →
      ∫⁻ v in {G.pairConstraint.vacant i}ᶜ, ENNReal.ofReal (Real.exp (WeightedResponses.spinScore A₀ i v)) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i v) ∂(G.referenceMeasure ∅ i) ≤
      ENNReal.ofReal (G.spinActivity c i) *
        G.pairConstraint.weightDensity G.weight (Function.update σ i (G.pairConstraint.vacant i)))
    [IsProbabilityMeasure (G.gibbsLaw ∅)] (hadm : ∀ᵐ σ ∂(G.gibbsLaw ∅), G.pairConstraint.IsAdmissible σ) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hsum : ∀ y : TorusSite (n * R.params.side),
      (open Classical in ∑ i : G.GasSpin, if y ∈ i.1.2 then G.spinActivity c i else 0) ≤ δ)
    {Nn : ι → ℝ} (hNn : ∀ j ∈ I, 1 + ((lowerSites (f j)).card : ℝ)⁻¹ *
      ∑ y ∈ lowerSites (f j), recordedSiteScore (A j) G y ≤ Nn j) (hN1 : ∀ j ∈ I, 1 ≤ Nn j) {Cf E7 : ℝ}
    (hCf : 0 ≤ Cf) (hE7 : 0 ≤ E7)
    (hfar : ∀ i ∈ I, ∀ J, J ⊆ I → i ∉ J → J.Nonempty → ∀ {Yt : G.Config → ℝ},
      IsGasTilt G s (blocksOfFamily f J) (sitesOfFamily f J) (J.card : ℝ) Yt →
      Integrable (gasSupportMean (A i) G (f i)) (tiltedGibbsLaw G Yt) ∧
      Integrable (gasSupportMean (A i) G (f i)) (G.gibbsLaw ∅) ∧
      |∫ σ, gasSupportMean (A i) G (f i) σ ∂(tiltedGibbsLaw G Yt) - G.expectation ∅ (gasSupportMean (A i) G (f i))| ≤
        Cf * J.card * (lowerSizeConst (A i) (f i) * Nn i) * E7) :
    (∀ J, J ⊆ I → Integrable (fun σ => ∏ j ∈ J, gasSupportMean (A j) G (f j) σ) (G.gibbsLaw ∅)) ∧
    (∀ i ∈ I, Integrable (gasSupportMean (A i) G (f i)) (G.gibbsLaw ∅)) ∧
    ∀ J, J ⊆ I → J.Nonempty →
      |G.expectation ∅ (fun σ => ∏ j ∈ J, gasSupportMean (A j) G (f j) σ) -
          ∏ j ∈ J, G.expectation ∅ (gasSupportMean (A j) G (f j))| ≤
        2 * Cf * (J.card : ℝ) ^ 2 * Real.exp (2 * J.card) * E7 * ∏ j ∈ J, (4 * lowerSizeConst (A j) (f j) * Nn j) := by
  classical
  have hpr : ∀ J, J ⊆ I →
      (fun σ => ∏ j ∈ J, gasSupportMean (A j) G (f j) σ) =ᵐ[G.gibbsLaw ∅] meanProd G A f J := by
    intro J _
    filter_upwards [hadm] with σ hσ
    simp only [meanProd, meanOnAdmissible, if_pos hσ]
  have intP : ∀ J, J ⊆ I → Integrable (fun σ => ∏ j ∈ J, gasSupportMean (A j) G (f j) σ) (G.gibbsLaw ∅) := by
    intro J hJ
    have hf := h.mono hJ
    have iU : Integrable (boundProd G A f J) (G.gibbsLaw ∅) := integrable_boundProd hf hC a₀ hw paid hadm
    have hb : ∀ᵐ σ ∂(G.gibbsLaw ∅), ‖meanProd G A f J σ‖ ≤ boundProd G A f J σ := by
      filter_upwards [hadm] with σ hσ
      rw [Real.norm_eq_abs]
      exact hf.abs_meanProd_le hσ
    exact (iU.mono' hf.measurable_meanProd.aestronglyMeasurable hb).congr (hpr J hJ).symm
  have intU : ∀ i ∈ I, Integrable (gasSupportMean (A i) G (f i)) (G.gibbsLaw ∅) := by
    intro i hi
    have := intP {i} (Finset.singleton_subset_iff.mpr hi)
    simpa using this
  have meanU : ∀ i ∈ I, |G.expectation ∅ (gasSupportMean (A i) G (f i))| ≤
      4 * lowerSizeConst (A i) (f i) * Nn i * Real.exp δ := by
    intro i hi
    have hsub : ({i} : Finset ι) ⊆ I := Finset.singleton_subset_iff.mpr hi
    have hf := h.mono hsub
    have iU : Integrable (boundProd G A f {i}) (G.gibbsLaw ∅) := integrable_boundProd hf hC a₀ hw paid hadm
    have hm := hf.expectation_boundProd_le a₀ hP hw paid hδ0 hsum (Nn := Nn) (fun j hj => hNn j (hsub hj))
      (fun j hj => hN1 j (hsub hj))
    have hb : ∀ᵐ σ ∂(G.gibbsLaw ∅), ‖gasSupportMean (A i) G (f i) σ‖ ≤ boundProd G A f {i} σ := by
      filter_upwards [hadm] with σ hσ
      rw [Real.norm_eq_abs]
      simpa [boundProd] using h.abs_le_bound i hi σ hσ
    have := norm_integral_le_of_norm_le iU hb
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    simpa [GasGround.expectation] using hm
  refine ⟨intP, intU, fun J => ?_⟩
  induction J using Finset.induction_on with
  | empty => exact fun _ hne => absurd hne (by simp)
  | insert i J hi ih =>
    intro hsub _
    have hiI : i ∈ I := hsub (Finset.mem_insert_self i J)
    have hJI : J ⊆ I := fun j hj => hsub (Finset.mem_insert_of_mem hj)
    have hV0 : 0 ≤ 4 * lowerSizeConst (A i) (f i) * Nn i := by
      have := h.lowerSizeConst_pos i hiI
      have := hN1 i hiI
      positivity
    have hP0 : 0 ≤ ∏ j ∈ J, (4 * lowerSizeConst (A j) (f j) * Nn j) := Finset.prod_nonneg fun j hj => by
      have := h.lowerSizeConst_pos j (hJI hj)
      have := hN1 j (hJI hj)
      positivity
    rcases J.eq_empty_or_nonempty with hJ | hJ
    · subst hJ
      simp only [insert_empty_eq, Finset.prod_singleton, sub_self, abs_zero, Finset.card_singleton]
      positivity
    · have ihJ := ih hJI hJ
      have hf := h.mono hJI
      obtain ⟨iy, iuy, hcov⟩ := abs_covariance_meanProd_le hf hC a₀ hw paid hadm (hfar i hiI J hJI hi hJ)
      have hmu := meanU i hiI
      have hUq := hf.expectation_boundProd_le a₀ hP hw paid hδ0 hsum (Nn := Nn) (fun j hj => hNn j (hJI hj))
        (fun j hj => hN1 j (hJI hj))
      have e1 : G.expectation ∅ (fun σ => ∏ j ∈ insert i J, gasSupportMean (A j) G (f j) σ) =
          ∫ σ, gasSupportMean (A i) G (f i) σ * meanProd G A f J σ ∂(G.gibbsLaw ∅) := by
        refine integral_congr_ae ?_
        filter_upwards [hpr J hJI] with σ hσ
        rw [Finset.prod_insert hi, hσ]
      have e2 : ∫ σ, meanProd G A f J σ ∂(G.gibbsLaw ∅) =
          G.expectation ∅ (fun σ => ∏ j ∈ J, gasSupportMean (A j) G (f j) σ) :=
        (integral_congr_ae (hpr J hJI)).symm
      set mu := G.expectation ∅ (gasSupportMean (A i) G (f i)) with hmud
      set D₂ := |G.expectation ∅ (fun σ => ∏ j ∈ J, gasSupportMean (A j) G (f j) σ) -
        ∏ j ∈ J, G.expectation ∅ (gasSupportMean (A j) G (f j))| with hD₂
      set D₁ := |∫ σ, gasSupportMean (A i) G (f i) σ * meanProd G A f J σ ∂(G.gibbsLaw ∅) -
        (∫ σ, gasSupportMean (A i) G (f i) σ ∂(G.gibbsLaw ∅)) * ∫ σ, meanProd G A f J σ ∂(G.gibbsLaw ∅)| with hD₁
      have hfin := induction_step_bound (cc := (J.card : ℝ)) (δ := δ) (Cf := Cf) (E7 := E7)
        (V := 4 * lowerSizeConst (A i) (f i) * Nn i)
        (P := ∏ j ∈ J, (4 * lowerSizeConst (A j) (f j) * Nn j)) (D₁ := D₁) (D₂ := D₂) (mu := mu)
        (Uq := ∫ σ, boundProd G A f J σ ∂(G.gibbsLaw ∅)) (Nat.cast_nonneg _) hδ0 hδ1 hCf hE7 hV0 hP0
        (integral_nonneg fun σ => (hf.boundProd_pos σ).le)
        (by
          have := hUq
          rw [Finset.prod_mul_distrib]
          exact this)
        (by
          refine hcov.trans (le_of_eq ?_)
          ring)
        hmu ihJ (abs_nonneg _)
      have e3 : (∏ j ∈ insert i J, G.expectation ∅ (gasSupportMean (A j) G (f j))) =
          mu * ∏ j ∈ J, G.expectation ∅ (gasSupportMean (A j) G (f j)) := Finset.prod_insert hi
      have e4 : G.expectation ∅ (fun σ => ∏ j ∈ insert i J, gasSupportMean (A j) G (f j) σ) -
          ∏ j ∈ insert i J, G.expectation ∅ (gasSupportMean (A j) G (f j)) =
          (∫ σ, gasSupportMean (A i) G (f i) σ * meanProd G A f J σ ∂(G.gibbsLaw ∅) -
            (∫ σ, gasSupportMean (A i) G (f i) σ ∂(G.gibbsLaw ∅)) * ∫ σ, meanProd G A f J σ ∂(G.gibbsLaw ∅)) +
          mu * (G.expectation ∅ (fun σ => ∏ j ∈ J, gasSupportMean (A j) G (f j) σ) -
            ∏ j ∈ J, G.expectation ∅ (gasSupportMean (A j) G (f j))) := by
        rw [e1, e3, e2]
        show _ = _ - mu * _ + _
        ring
      rw [e4, Finset.card_insert_of_notMem hi, Finset.prod_insert hi]
      push_cast
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      exact hfin
end Split
section Main
set_option maxHeartbeats 4000000 in
theorem decorrelate (hfar : GasSupportMeanUnderTilt) (hmv : GasSupportMeanFarSpinBound)
    (hcols : ClusterExpansionOfAStep.GasColumnsSmall) (hpaid : clusterScoreIntegralBound) (hgas : GasSumNearBlockBound)
    (hcf : CouplingFloorExists) (hC : ActivityConditionalLawsStatement)
    (hP : MeanOfProductStatement) : GasSupportMeansDecorrelate := by
  classical
  obtain ⟨r₁, p₁, H₁⟩ := hfar
  obtain ⟨r₂, p₂, H₂⟩ := hmv
  obtain ⟨r₃, p₃, H₃⟩ := hcols
  obtain ⟨r₄, p₄, H₄⟩ := hpaid
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (r₄ c))),
    fun c => lt_min (p₁ c) (lt_min (p₂ c) (lt_min (p₃ c) (p₄ c))), fun T hT' hrt K => ?_⟩
  have t₁ := hrt.trans (min_le_left _ _)
  have t₂ := (hrt.trans (min_le_right _ _)).trans (min_le_left _ _)
  have t₃ := ((hrt.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have t₄ := ((hrt.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨y₁, Cf, hCf, H₁⟩ := H₁ T hT' t₁ K
  obtain ⟨y₂, H₂⟩ := H₂ T hT' t₂ K
  obtain ⟨y₃, H₃⟩ := H₃ T hT' t₃
  obtain ⟨y₄, H₄⟩ := H₄ T hT' t₄ K
  have hrt0 := hT'.rt_pos
  have hch : 0 < T.gasRate := by
    have h1 := hT'.cE_pos
    have h2 := hT'.κ_pos
    have h3 := hT'.σ_pos
    unfold ParameterAssignment.gasRate ParameterAssignment.κ₁
    positivity
  obtain ⟨y₅, H₅⟩ := hcf T.gasRate T.side T.rt hch
  obtain ⟨W, hWd⟩ : ∃ W : ℝ, W = (2 / (1 - Real.exp (-(1 / 4)))) ^ 4 := ⟨_, rfl⟩
  have hW0 : 0 < W := by
    rw [hWd]
    have : Real.exp (-(1 / 4)) < 1 := by
      have := Real.exp_lt_exp.mpr (by norm_num : (-(1 / 4) : ℝ) < 0)
      simpa using this
    have h2 : 0 < 1 - Real.exp (-(1 / 4)) := by linarith
    positivity
  refine ⟨max T.floorMin (max y₁ (max y₂ (max y₃ (max y₄ (max y₅ (max (200 * T.B)
    (Real.log W / (8 * T.gasRate)))))))), 2 * Cf,
    by positivity, fun y hy R n _ G hG s ι I A f D hne hK hs hAT hSA => ?_⟩
  have fl : ∀ {a : ℝ}, a ≤ max y₁ (max y₂ (max y₃ (max y₄ (max y₅ (max (200 * T.B)
      (Real.log W / (8 * T.gasRate))))))) → a ≤ y :=
    fun h => h.trans ((le_max_right _ _).trans hy)
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hy1 : y₁ ≤ y := fl (le_max_left _ _)
  have hy2 : y₂ ≤ y := fl ((le_max_left _ _).trans (le_max_right _ _))
  have hy3 : y₃ ≤ y := fl ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hy4 : y₄ ≤ y := fl ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hy5 : y₅ ≤ y := fl ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))))
  have hy6 : 200 * T.B ≤ y := fl ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))))
  have hy7 : Real.log W / (8 * T.gasRate) ≤ y := fl ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))))
  obtain ⟨i₀, hi₀⟩ := hne
  have hAT₀ := hAT i₀ hi₀
  have hOT := hAT₀.onFamily
  obtain ⟨hR, hρA, hpc, hyx, hstep⟩ := id hOT
  have hx1 : 1 ≤ R.coupling := by
    have h1 : (1 : ℝ) ≤ T.floorMin := hT'.yC_ge.trans (le_max_left _ _)
    linarith only [h1, hy0, hyx]
  have hx0 : 0 < R.coupling := by linarith only [hx1]
  have hL : R.params.side = T.side := by rw [hR]; rfl
  have hRrt : R.params.rt = T.rt := by rw [hR]; rfl
  have hRy : R.params.y₁ = y := by rw [hR]; rfl
  have hfit : R.params.Admissible := by rw [hR]; exact hT'.fits y hy0
  have hrtR : 0 < R.params.rt := by rw [hRrt]; exact hrt0
  have hx' : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAT₀.abs_sub_le).2
    linarith only [h1, hy6, hyx]
  obtain ⟨hw, cols⟩ := H₃ y hy3 R hOT hx' n G hG fun j => j.1.Touches ∅
  have paid := H₄ y hy4 R (A i₀) (hK i₀ hi₀) hAT₀ n G hG
  have hcfR : R.params.RangeFloor T.gasRate := by
    intro x hx
    have := H₅ x (hy5.trans (hRy ▸ hx))
    rw [hL, hRrt]
    exact this
  have hyR : R.params.y₁ ≤ R.coupling := by rw [hRy]; exact hyx
  have a₀ : (A i₀).score = s := hs i₀ hi₀
  have hs0 : ∀ w, 0 ≤ s w := by
    rw [← a₀]
    exact hAT₀.admissible.price.nonneg
  have hsb : Measurable s := by
    rw [← a₀]
    exact hAT₀.admissible.price.borel
  obtain ⟨p1, g1, -, -⟩ := hC G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasure ∅) _ _ hw
  have hprob : IsProbabilityMeasure (G.gibbsLaw ∅) := p1
  have hadm : ∀ᵐ σ ∂(G.gibbsLaw ∅), G.pairConstraint.IsAdmissible σ := g1.ae_admissible
  have hmv := fun i (hi : i ∈ I) => H₂ y hy2 R (A i) (hK i hi) (hAT i hi) n G hG (f i) (hSA.norm_le i hi) (by
    exact hSA.nonempty i hi)
  have hC₀ : 1 ≤ K.C₀ := by
    have hl := hAT₀.admissible.params_admissible
    rw [hK i₀ hi₀] at hl
    have h1 := hl.C₀_eq
    have h2 := hl.N₀_nonneg
    have h3 := hl.Kc_ge
    have h4 : 1 ≤ R.params.coupling := by
      have : R.params.coupling = T.coupling := by rw [hR]; rfl
      rw [this]
      exact hT'.a_ge
    linarith only [h1, h2, h3, h4]
  have hself : ∀ {S : Finset (TorusSite n)} {Y : TorusSite n}, Y ∈ S → Y ∈ thickening 2 S := fun {S Y} h => by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Y, h, ?_⟩
    rw [supDist_self]
    omega
  have hblock : ∀ j, ∀ y ∈ lowerSites (f j), parentBlock R.params.side y ∈ upperSites (f j) := fun j y hy =>
    parentBlock_mem_weightSupportSites (f j) hy
  have hF : FamilyHyp G A f s I := {
    score_eq := hs
    score_nonneg := hs0
    measurable_score := hsb
    measurable_mean := fun j hj => (hmv j hj).1
    abs_le_bound := fun j hj => (hmv j hj).2.1
    abs_sub_vacant_le := fun j hj => (hmv j hj).2.2
    lowerSizeConst_pos := fun j hj => by
      have hc : (0 : ℝ) < ((lowerSites (f j)).card : ℝ) := by
        obtain ⟨Y, hY⟩ := hSA.nonempty j hj
        have hpar : (open Classical in (lowerSites (f j)).image (parentBlock R.params.side)) = upperSites (f j) :=
          image_parentBlock_weightSupportSites (f j)
        rw [← hpar] at hY
        obtain ⟨y', hy', -⟩ := Finset.mem_image.mp hY
        exact_mod_cast Finset.card_pos.mpr ⟨y', hy'⟩
      unfold lowerSizeConst
      rw [hK j hj]
      have h0 : 0 < K.C₀ := by linarith only [hC₀]
      exact mul_pos h0 hc
    parentBlock_mem := fun j _ => hblock j
    disjoint_lowerSites := fun j hj k hk hjk => by
      refine Finset.disjoint_left.mpr fun y h1 h2 => ?_
      have := hSA.separated j hj k hk hjk _ (hself (hblock j y h1)) _ (hself (hblock k y h2))
      rw [supDist_self] at this
      have := hSA.eight_lt
      omega }
  have hl₀ := hAT₀.admissible.params_admissible
  have hs₁ : 0 ≤ K.s₁ := by
    rw [hK i₀ hi₀] at hl₀
    have h1 := hl₀.s₁_eq
    have h2 : 0 ≤ K.C₀ + 2 := by linarith only [hC₀]
    have h3 : 0 ≤ R.params.coupling := by
      have : R.params.coupling = T.coupling := by rw [hR]; rfl
      rw [this]
      linarith only [hT'.a_ge]
    rw [h1]
    positivity
  set Nn : ι → ℝ := fun j => meanSiteScore (coarseLabelScore K.s₁ s) (upperSites (f j)) G.state.1 G.state.2 with hNnd
  have hst : ∀ j ∈ I, 1 ≤ Nn j ∧ 1 + ((lowerSites (f j)).card : ℝ)⁻¹ *
      ∑ y ∈ lowerSites (f j), recordedSiteScore (A j) G y ≤ Nn j := by
    intro j hj
    have := meanSiteScore_bounds (G := G) (A := A j) (hF.score_nonneg_of_mem hj) (by rw [hK j hj]; exact hs₁) (f j)
      (hSA.nonempty j hj)
    rw [hK j hj, hs j hj] at this
    exact this
  set δ := Real.exp (-(8 * T.gasRate * R.coupling)) * W with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 := by
    have h1 : Real.log W ≤ 8 * T.gasRate * R.coupling := by
      have h2 : Real.log W / (8 * T.gasRate) ≤ R.coupling := hy7.trans hyx
      rw [div_le_iff₀ (by positivity)] at h2
      linarith only [h2]
    have h3 : W ≤ Real.exp (8 * T.gasRate * R.coupling) := by
      calc W = Real.exp (Real.log W) := (Real.exp_log hW0).symm
        _ ≤ _ := Real.exp_le_exp.mpr h1
    have h4 : Real.exp (-(8 * T.gasRate * R.coupling)) * Real.exp (8 * T.gasRate * R.coupling) = 1 := by
      rw [← Real.exp_add]
      simp
    calc δ ≤ Real.exp (-(8 * T.gasRate * R.coupling)) * Real.exp (8 * T.gasRate * R.coupling) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
      _ = 1 := h4
  have hsum : ∀ y' : TorusSite (n * R.params.side),
      (∑ i : G.GasSpin, if y' ∈ i.1.2 then G.spinActivity T.gasRate i else 0) ≤ δ := by
    intro y'
    have := sum_spinActivity_le (G := G) hgas hfit hch hcfR hyR hrtR hw.activity_nonneg y'
    rw [hδ, hWd]
    exact this
  set E7 := Real.exp (-(R.params.rt * D / 2 ^ 7)) with hE7
  have hE70 : 0 ≤ E7 := (Real.exp_pos _).le
  have hfar' : ∀ i ∈ I, ∀ J, J ⊆ I → i ∉ J → J.Nonempty → ∀ {Yt : G.Config → ℝ},
      IsGasTilt G s (blocksOfFamily f J) (sitesOfFamily f J) (J.card : ℝ) Yt →
      Integrable (gasSupportMean (A i) G (f i)) (tiltedGibbsLaw G Yt) ∧
      Integrable (gasSupportMean (A i) G (f i)) (G.gibbsLaw ∅) ∧
      |∫ σ, gasSupportMean (A i) G (f i) σ ∂(tiltedGibbsLaw G Yt) - G.expectation ∅ (gasSupportMean (A i) G (f i))| ≤
        Cf * J.card * (lowerSizeConst (A i) (f i) * Nn i) * E7 := by
    intro i hi J hJ hiJ hJne Yt ht
    obtain ⟨j₀, hj₀⟩ := hJne
    have hQ : (blocksOfFamily f J).Nonempty := by
      obtain ⟨Y, hY⟩ := hSA.nonempty j₀ (hJ hj₀)
      exact ⟨Y, Finset.mem_biUnion.mpr ⟨j₀, hj₀, hY⟩⟩
    have hDap : ∀ Y ∈ upperSites (f i), ∀ Y' ∈ blocksOfFamily f J, D ≤ supDist Y Y' := by
      intro Y hY Y' hY'
      obtain ⟨j, hj, hYj⟩ := Finset.mem_biUnion.mp hY'
      exact hSA.separated i hi j (hJ hj) (fun e => hiJ (e ▸ hj)) Y (hself hY) Y' (hself hYj)
    have hB : ∀ y' ∈ lowerSites (f i), y' ∉ sitesOfFamily f J := by
      intro y' hy' hyJ
      obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.mp hyJ
      exact Finset.disjoint_left.mp (hF.disjoint_lowerSites i hi j (hJ hj) (fun e => hiJ (e ▸ hj))) hy' hyj
    have he : (1 : ℝ) ≤ (J.card : ℝ) := by
      have : 0 < J.card := Finset.card_pos.mpr ⟨j₀, hj₀⟩
      exact_mod_cast this
    have ht' : IsGasTilt G (A i).score (blocksOfFamily f J) (sitesOfFamily f J) (J.card : ℝ) Yt := by
      rw [hs i hi]
      exact ht
    obtain ⟨a1, a2, a3⟩ := H₁ y hy1 R (A i) (hK i hi) (hAT i hi) n G hG (f i) (blocksOfFamily f J)
      (sitesOfFamily f J) (J.card : ℝ) Yt D
      (hSA.norm_le i hi) (hSA.nonempty i hi) hSA.range_le hSA.eight_lt hQ hDap hB he ht'
    refine ⟨a1, a2, a3.trans (le_of_eq ?_)⟩
    simp only [lowerSizeConst, hNnd, hE7, hK i hi, hs i hi]
    ring
  have hprob' := hprob
  obtain ⟨i1, i2, i3⟩ := abs_expectation_prod_sub_le hF hC hP a₀ hw paid hadm hδ0 hδ1 hsum (fun j hj => (hst j hj).2)
    (fun j hj => (hst j hj).1) hCf hE70 hfar'
  refine ⟨i1 I (Finset.Subset.refl I), i2, ?_⟩
  refine (i3 I (Finset.Subset.refl I) ⟨i₀, hi₀⟩).trans (le_of_eq ?_)
  have e1 : ∏ j ∈ I, (4 * lowerSizeConst (A j) (f j) * Nn j) =
      (∏ j ∈ I, 4 * (K.C₀ * ((lowerSites (f j)).card : ℝ))) * ∏ j ∈ I, Nn j := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    simp only [lowerSizeConst, hK j hj]
  rw [e1]
  ring
end Main
end Decorrelation
theorem gasSupportMeansDecorrelate_holds (hfar : GasSupportMeanUnderTilt) (hmv : GasSupportMeanFarSpinBound)
    (hcols : ClusterExpansionOfAStep.GasColumnsSmall) (hpaid : clusterScoreIntegralBound) (hgas : GasSumNearBlockBound)
    (hcf : CouplingFloorExists) (hC : Dobrushin.ActivityConditionalLawsStatement)
    (hP : Dobrushin.MeanOfProductStatement) : GasSupportMeansDecorrelate := by apply _root_.YangMills.Construction.ResponseInTheExpansion.Decorrelation.decorrelate <;> assumption
end ResponseInTheExpansion
end YangMills.Construction
end
