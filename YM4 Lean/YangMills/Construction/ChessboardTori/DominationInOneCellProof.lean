import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivityProof
import YangMills.Construction.ChessboardTori.DominationInOneCell
import YangMills.Construction.ChessboardTori.JensenAgainstTheChessboard
import YangMills.Construction.ChessboardTori.JensenForPeriodicGibbsStates
import YangMills.Construction.ChessboardTori.LimitingSeminormIsAFiniteSeminorm
import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori.CellDomination
theorem abs_log_one_add_sub_self_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -x) (by rw [abs_neg]; linarith) 1
  simp only [Finset.sum_range_one, abs_neg, sub_neg_eq_add] at h
  have h1 : |(-x) ^ (0 + 1) / (((0 : ℕ) : ℝ) + 1) + Real.log (1 + x)| =
      |Real.log (1 + x) - x| := by
    congr 1
    simp
    ring
  rw [h1] at h
  refine h.trans ?_
  have hpos : 0 < 1 - |x| := by linarith
  rw [div_le_iff₀ hpos]
  have h2 : |x| ^ (1 + 1) = x ^ 2 := by
    rw [show 1 + 1 = 2 from rfl, sq_abs]
  rw [h2]
  nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1 / 2 - |x| by linarith)]
variable {D : ChessboardSetup}
theorem smul_mem_cellObservables {S : Set InfiniteLattice.AmbientSpace} {F : D.GaugeField → ℂ}
    (a : ℂ) (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    a • F ∈ ReflectionGrid.cellObservables (D := D) S := by
  obtain ⟨f, hf, ⟨C, hC⟩, rfl⟩ := hF
  refine ⟨fun u => a * f u, hf.const_mul a, ⟨‖a‖ * C, fun u => ?_⟩, rfl⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC u) (norm_nonneg a)
theorem conj_mem_cellObservables {S : Set InfiniteLattice.AmbientSpace}
    {F : D.GaugeField → ℂ} (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    (fun U => starRingEnd ℂ (F U)) ∈ ReflectionGrid.cellObservables (D := D) S := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.conj_mem_cellObservables <;> assumption
theorem norm_integral_le_of_jensen
    (hsem : LimChessboardNormIsSeminorm.Statement)
    (hdep : MeasurableObservablesAndLifts.Statement)
    (D : ChessboardSetup) (g : ReflectionGrid D) (hg : g.IsCoarse)
    (ν : Measure D.GaugeField) [IsProbabilityMeasure ν]
    (hJ : ∀ H : D.GaugeField → ℝ,
      (fun U => (H U : ℂ)) ∈ ReflectionGrid.cellObservables (D := D) g.baseCell →
      ∫ U, H U ∂ν ≤ Real.log (g.limChessboardNorm fun U => Complex.exp (H U)))
    (F : D.GaugeField → ℂ) (hF : F ∈ ReflectionGrid.cellObservables (D := D) g.baseCell) :
    ‖∫ U, F U ∂ν‖ ≤ g.limChessboardNorm F := by
  obtain ⟨hfin, hone⟩ := hsem D g hg
  have hobs : InfiniteLattice.IsBoundedObservable F := by
    have hS : g.baseCell ∈ g.cellSet := ⟨0, rfl⟩
    obtain ⟨-, -, hcell, -⟩ := hdep D
    have h0 := hF
    rw [hcell g hg _ hS] at h0
    exact h0.1
  have hF0 := hF
  obtain ⟨f, hf, ⟨C, hC⟩, hFf⟩ := hF0
  set z : ℂ := ∫ U, F U ∂ν with hz
  set c : ℂ := Complex.exp (((-Complex.arg z : ℝ) : ℂ) * Complex.I) with hc
  have hcnorm : ‖c‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hcz : c * z = (‖z‖ : ℂ) := by
    have h1 : c * Complex.exp ((Complex.arg z : ℂ) * Complex.I) = 1 := by
      rw [hc, ← Complex.exp_add]
      simp
    calc c * z = c * ((‖z‖ : ℂ) * Complex.exp ((Complex.arg z : ℂ) * Complex.I)) := by
          rw [Complex.norm_mul_exp_arg_mul_I]
      _ = (‖z‖ : ℂ) * (c * Complex.exp ((Complex.arg z : ℂ) * Complex.I)) := by ring
      _ = (‖z‖ : ℂ) := by rw [h1, mul_one]
  set B : ℝ := |C| + 1 with hB
  have hBpos : 0 < B := by positivity
  have hbound : ∀ u, |(c * f u).re| ≤ B := fun u => by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, hcnorm, one_mul]
    exact (hC u).trans ((le_abs_self C).trans (by linarith))
  have hFeq : ∀ U, F U = f (ReflectionGrid.restrictField g.baseCell U) := fun U => by
    rw [hFf]
    rfl
  let G : D.GaugeField → ℝ := fun U => (c * F U).re
  have hGb : ∀ U, |G U| ≤ B := fun U => by
    show |(c * F U).re| ≤ B
    rw [hFeq]
    exact hbound _
  have hmem : ∀ φ : ℝ → ℝ, Measurable φ → ∀ A : ℝ, (∀ u, |φ (c * f u).re| ≤ A) →
      (fun U => ((φ (G U) : ℝ) : ℂ)) ∈ ReflectionGrid.cellObservables (D := D) g.baseCell := by
    intro φ hφ A hA
    refine ⟨fun u => ((φ (c * f u).re : ℝ) : ℂ),
      Complex.measurable_ofReal.comp (hφ.comp (Complex.measurable_re.comp (hf.const_mul c))),
      ⟨A, fun u => ?_⟩, ?_⟩
    · simpa using hA u
    · funext U
      show ((φ (c * F U).re : ℝ) : ℂ) = _
      rw [hFeq]
      rfl
  let Gc : D.GaugeField → ℂ := fun U => (G U : ℂ)
  have hGc : Gc ∈ ReflectionGrid.cellObservables (D := D) g.baseCell :=
    hmem id measurable_id B hbound
  have hGmeas : Measurable G :=
    Complex.measurable_re.comp (hobs.1.const_mul c)
  have hGint : Integrable G ν :=
    Integrable.of_bound hGmeas.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun U => by simpa using hGb U)
  have hFint : Integrable F ν := by
    obtain ⟨hm, C', hC'⟩ := hobs
    exact Integrable.of_bound hm.aestronglyMeasurable C' (Filter.Eventually.of_forall hC')
  have hGval : ∫ U, G U ∂ν = ‖z‖ := by
    have h1 : ∫ U, c * F U ∂ν = c * z := integral_const_mul c F
    have h2 := Complex.reCLM.integral_comp_comm (hFint.const_mul c)
    have h3 : ∫ U, G U ∂ν = (∫ U, c * F U ∂ν).re := h2
    rw [h3, h1, hcz]
    simp
  obtain ⟨-, -, hN0G, hsmG, haddG, -, -⟩ := hfin Gc hGc
  have hone_mem : (fun _ => (1 : ℂ)) ∈ ReflectionGrid.cellObservables (D := D) g.baseCell :=
    ⟨fun _ => 1, measurable_const, ⟨1, fun _ => by simp⟩, rfl⟩
  obtain ⟨-, -, -, -, hadd1, -, -⟩ := hfin _ hone_mem
  have hGF : g.limChessboardNorm Gc ≤ g.limChessboardNorm F := by
    obtain ⟨-, -, -, hsmF, -, hconjF, -⟩ := hfin F hF
    have hFc := conj_mem_cellObservables hF
    obtain ⟨-, -, -, hsmFc, -, -, -⟩ := hfin _ hFc
    have h1 := smul_mem_cellObservables ((c / 2)) hF
    have h2 := smul_mem_cellObservables (starRingEnd ℂ c / 2) hFc
    obtain ⟨-, -, -, -, hadd2, -, -⟩ := hfin _ h1
    have hsplit : Gc = (c / 2) • F + (starRingEnd ℂ c / 2) • fun U => starRingEnd ℂ (F U) := by
      funext U
      show (((c * F U).re : ℝ) : ℂ) = (c / 2) * F U + (starRingEnd ℂ c / 2) * starRingEnd ℂ (F U)
      rw [Complex.re_eq_add_conj, map_mul]
      ring
    have hn1 : ‖c / 2‖ = 1 / 2 := by simp [hcnorm]
    have hn2 : ‖starRingEnd ℂ c / 2‖ = 1 / 2 := by simp [hcnorm]
    rw [hsplit]
    refine (hadd2 _ h2).trans ?_
    rw [hsmF, hsmFc, hconjF, hn1, hn2]
    linarith
  have hstep : ∀ t : ℝ, 0 < t → t * B ≤ 1 / 2 →
      t * ‖z‖ - 2 * t ^ 2 * B ^ 2 ≤ t * g.limChessboardNorm F := by
    intro t ht htB
    have hy : ∀ x : ℝ, |x| ≤ B → |t * x| ≤ 1 / 2 := fun x hx => by
      rw [abs_mul, abs_of_pos ht]
      exact (mul_le_mul_of_nonneg_left hx ht.le).trans htB
    have hlog : ∀ x : ℝ, |x| ≤ B → t * x - 2 * t ^ 2 * B ^ 2 ≤ Real.log (1 + t * x) := by
      intro x hx
      have h1 := abs_log_one_add_sub_self_le (hy x hx)
      have h2 := (abs_le.1 h1).1
      have h3 : (t * x) ^ 2 ≤ t ^ 2 * B ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left (sq_le_sq' (by linarith [(abs_le.1 hx).1])
          (abs_le.1 hx).2) (sq_nonneg t)
      linarith
    have habs : ∀ x : ℝ, |x| ≤ B → |Real.log (1 + t * x)| ≤ 1 := by
      intro x hx
      have h0 := hy x hx
      have h1 := abs_log_one_add_sub_self_le h0
      have h2 : (t * x) ^ 2 ≤ 1 / 4 := by
        have := sq_le_sq' (by linarith [(abs_le.1 h0).1]) (abs_le.1 h0).2
        nlinarith
      have h3 : |Real.log (1 + t * x)| ≤ |Real.log (1 + t * x) - t * x| + |t * x| := by
        simpa using abs_add_le (Real.log (1 + t * x) - t * x) (t * x)
      linarith
    let φ : ℝ → ℝ := fun x => Real.log (1 + t * x)
    have hφ : Measurable φ :=
      Real.measurable_log.comp (measurable_const.add (measurable_const.mul measurable_id))
    let h : D.GaugeField → ℝ := fun U => φ (G U)
    have hh : (fun U => (h U : ℂ)) ∈ ReflectionGrid.cellObservables (D := D) g.baseCell :=
      hmem φ hφ 1 fun u => habs _ (hbound u)
    have hpos : ∀ U, 0 < 1 + t * G U := fun U => by
      have := (abs_le.1 (hy _ (hGb U))).1
      linarith
    have hexp : (fun U => Complex.exp (h U)) = (fun _ => (1 : ℂ)) + (t : ℂ) • Gc := by
      funext U
      show Complex.exp ((Real.log (1 + t * G U) : ℝ) : ℂ) = 1 + (t : ℂ) * (G U : ℂ)
      rw [← Complex.ofReal_exp, Real.exp_log (hpos U)]
      push_cast
      rfl
    have htG := smul_mem_cellObservables (t : ℂ) hGc
    have hsum_mem : (fun U => Complex.exp (h U)) ∈
        ReflectionGrid.cellObservables (D := D) g.baseCell := by
      have h0 := hmem (fun x => 1 + t * x)
        (measurable_const.add (measurable_const.mul measurable_id)) (1 + t * B) fun u => by
          refine (abs_add_le _ _).trans ?_
          rw [abs_one, abs_mul, abs_of_pos ht]
          exact add_le_add_right (mul_le_mul_of_nonneg_left (hbound u) ht.le) _
      convert h0 using 1
      rw [hexp]
      funext U
      show 1 + (t : ℂ) * (G U : ℂ) = _
      push_cast
      rfl
    obtain ⟨-, -, hN0e, -, -, -, -⟩ := hfin _ hsum_mem
    have hup : g.limChessboardNorm (fun U => Complex.exp (h U)) ≤
        1 + t * g.limChessboardNorm Gc := by
      rw [hexp]
      refine (hadd1 _ htG).trans ?_
      rw [hone, hsmG]
      simp [abs_of_pos ht]
    have hlogN : Real.log (g.limChessboardNorm fun U => Complex.exp (h U)) ≤
        t * g.limChessboardNorm Gc := by
      rcases hN0e.eq_or_lt with h0 | h0
      · rw [← h0, Real.log_zero]
        exact mul_nonneg ht.le hN0G
      · have := Real.log_le_sub_one_of_pos h0
        linarith
    have hupper : ∫ U, h U ∂ν ≤ t * g.limChessboardNorm F :=
      ((hJ h hh).trans hlogN).trans (mul_le_mul_of_nonneg_left hGF ht.le)
    have hhint : Integrable h ν :=
      Integrable.of_bound (hφ.comp hGmeas).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun U => by simpa using habs _ (hGb U))
    have hlower : t * ‖z‖ - 2 * t ^ 2 * B ^ 2 ≤ ∫ U, h U ∂ν := by
      have h1 : ∫ U, (t * G U - 2 * t ^ 2 * B ^ 2) ∂ν = t * ‖z‖ - 2 * t ^ 2 * B ^ 2 := by
        rw [integral_sub (hGint.const_mul t) (integrable_const _), integral_const_mul, hGval]
        simp
      rw [← h1]
      exact integral_mono ((hGint.const_mul t).sub (integrable_const _)) hhint
        fun U => hlog _ (hGb U)
    exact hlower.trans hupper
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set t : ℝ := min (1 / (2 * B)) (ε / (2 * B ^ 2)) with ht
  have htpos : 0 < t := lt_min (by positivity) (by positivity)
  have htB : t * B ≤ 1 / 2 := by
    have h1 : t ≤ 1 / (2 * B) := min_le_left _ _
    calc t * B ≤ 1 / (2 * B) * B := mul_le_mul_of_nonneg_right h1 hBpos.le
      _ = 1 / 2 := by field_simp
  have htε : 2 * t * B ^ 2 ≤ ε := by
    have h1 : t ≤ ε / (2 * B ^ 2) := min_le_right _ _
    calc 2 * t * B ^ 2 = t * (2 * B ^ 2) := by ring
      _ ≤ ε / (2 * B ^ 2) * (2 * B ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ε := by field_simp
  have h1 := hstep t htpos htB
  have h2 : t * (‖z‖ - 2 * t * B ^ 2) ≤ t * g.limChessboardNorm F := by
    calc t * (‖z‖ - 2 * t * B ^ 2) = t * ‖z‖ - 2 * t ^ 2 * B ^ 2 := by ring
      _ ≤ _ := h1
  have h3 := le_of_mul_le_mul_left h2 htpos
  linarith
theorem cellDomination
    (hjen : JensenChessboardBound.Statement)
    (hper : PeriodicJensen.Statement)
    (hsem : LimChessboardNormIsSeminorm.Statement)
    (hdep : MeasurableObservablesAndLifts.Statement) :
    CellDomination.Statement := by
  intro D g hg F hF
  refine ⟨fun ν hν hinv => ?_, fun ν hν => ?_⟩
  · have : IsProbabilityMeasure ν := hν.1
    exact norm_integral_le_of_jensen hsem hdep D g hg ν
      (fun H hH => (hjen D g hg ν hν hinv H hH).2) F hF
  · have : IsProbabilityMeasure ν := hν.1.1
    exact norm_integral_le_of_jensen hsem hdep D g hg ν
      (fun H hH => ((hper D ν hν).1 g hg H hH).2) F hF
end YangMills.Construction.ChessboardTori.CellDomination
end
