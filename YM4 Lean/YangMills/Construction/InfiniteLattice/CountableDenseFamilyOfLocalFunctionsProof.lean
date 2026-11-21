import YangMills.Construction.InfiniteLattice.CountableDenseFamilyOfLocalFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Filter MeasureTheory InfiniteLattice GibbsAtFixedSpacing
open GibbsAtFixedSpacing.SpacesOfFieldsAndMeasures
namespace PeriodicGibbsStateSpace.DenseLocalFamily
variable {a : ℝ}
def rePart (F : GaugeField a → ℂ) : GaugeField a → ℂ := fun U => ((F U).re : ℂ)
def imPart (F : GaugeField a → ℂ) : GaugeField a → ℂ := fun U => ((F U).im : ℂ)
theorem isRealValued_rePart (F : GaugeField a → ℂ) : IsRealValued (rePart F) :=
  fun _ => Complex.ofReal_im _
theorem isRealValued_imPart (F : GaugeField a → ℂ) :
    IsRealValued (imPart F) :=
  fun _ => Complex.ofReal_im _
theorem continuous_rePart {F : GaugeField a → ℂ} (hF : Continuous F) :
    Continuous (rePart F) :=
  Complex.continuous_ofReal.comp (Complex.continuous_re.comp hF)
theorem continuous_imPart {F : GaugeField a → ℂ} (hF : Continuous F) :
    Continuous (imPart F) :=
  Complex.continuous_ofReal.comp (Complex.continuous_im.comp hF)
theorem rePart_mem_continuousLocal (hB : LocalFnsDenseStarSubalgebra a) {F : GaugeField a → ℂ}
    (hF : F ∈ GibbsAtFixedSpacing.continuousLocal a) :
    rePart F ∈ GibbsAtFixedSpacing.continuousLocal a := by
  obtain ⟨-, ⟨A, hA⟩, -, hconj, -, -⟩ := hB
  have h₁ : F ∈ A := by rw [← SetLike.mem_coe, hA]; exact hF
  have h₂ : (fun U => starRingEnd ℂ (F U)) ∈ A := by
    rw [← SetLike.mem_coe, hA]; exact hconj F hF
  have h₃ : ((1 / 2 : ℂ)) • (F + fun U => starRingEnd ℂ (F U)) ∈ A :=
    A.smul_mem (A.add_mem h₁ h₂) _
  have e : rePart F = ((1 / 2 : ℂ)) • (F + fun U => starRingEnd ℂ (F U)) := by
    funext U
    simp only [rePart, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.add_conj]
    push_cast
    ring
  rw [e, ← hA]
  exact h₃
theorem norm_apply_le_supNorm [CompactSpace (GaugeField a)] {G : GaugeField a → ℂ}
    (hG : Continuous G) (U : GaugeField a) : ‖G U‖ ≤ observableSupNorm G :=
  le_ciSup (f := fun U => ‖G U‖) (isCompact_range hG.norm).bddAbove U
theorem norm_sub_rePart_le {F : GaugeField a → ℂ} (hF : IsRealValued F)
    (H : GaugeField a → ℂ) (U : GaugeField a) :
    ‖F U - rePart H U‖ ≤ ‖F U - H U‖ := by
  have e : F U - rePart H U = (((F U - H U).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [rePart]
    · simp [rePart, hF U]
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _
theorem exists_isCountableRealDense [CompactSpace (GaugeField a)]
    (hB : LocalFnsDenseStarSubalgebra a) (hE : LocalFnsSeparable a) :
    ∃ 𝒟 : Set (GaugeField a → ℂ), IsCountableRealDense 𝒟 := by
  obtain ⟨𝒟₀, hsub, hcount, hdense⟩ := hE
  let S : Set (GaugeField a → ℂ) := insert (fun _ => (1 : ℂ)) (rePart '' 𝒟₀)
  have hS : S.Countable := (hcount.image _).insert _
  let M : Submodule ℚ (GaugeField a → ℂ) := Submodule.span ℚ S
  have hsmul : ∀ (q : ℚ) (F : GaugeField a → ℂ), q • F = (q : ℂ) • F := by
    intro q F
    funext U
    simp [Rat.smul_def]
  have hAlg := hB
  obtain ⟨-, ⟨A, hA⟩, hconst, -, -, -⟩ := hAlg
  have hmem : ∀ {F : GaugeField a → ℂ}, F ∈ M →
      F ∈ GibbsAtFixedSpacing.continuousLocal a ∧ IsRealValued F := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF =>
      rcases hF with rfl | ⟨H, hH, rfl⟩
      · exact ⟨hconst 1, fun U => by simp⟩
      · exact ⟨rePart_mem_continuousLocal hB (hsub hH), isRealValued_rePart H⟩
    | zero => exact ⟨hconst 0, fun U => by simp⟩
    | add F F' _ _ hF hF' =>
      refine ⟨?_, fun U => by simp [hF.2 U, hF'.2 U]⟩
      have h₁ : F ∈ A := by rw [← SetLike.mem_coe, hA]; exact hF.1
      have h₂ : F' ∈ A := by rw [← SetLike.mem_coe, hA]; exact hF'.1
      rw [← hA]
      exact A.add_mem h₁ h₂
    | smul q F _ hF =>
      refine ⟨?_, fun U => by simp [Rat.smul_def, hF.2 U]⟩
      have h₁ : F ∈ A := by rw [← SetLike.mem_coe, hA]; exact hF.1
      rw [hsmul, ← hA]
      exact A.smul_mem h₁ _
  refine ⟨(M : Set (GaugeField a → ℂ)), ?_, fun F hF => (hmem hF).1, fun F hF => (hmem hF).2,
    Submodule.subset_span (Set.mem_insert _ _), ?_, ?_⟩
  · have : Countable S := hS.to_subtype
    have e : (M : Set (GaugeField a → ℂ)) =
        Set.range (Finsupp.linearCombination ℚ ((↑) : S → (GaugeField a → ℂ))) := by
      rw [← LinearMap.coe_range, Finsupp.range_linearCombination, Subtype.range_coe]
    rw [e]
    exact Set.countable_range _
  · intro F hF F' hF' q
    have h₁ : F + q • F' ∈ M := M.add_mem hF (M.smul_mem q hF')
    have e : (fun U => F U + (q : ℂ) * F' U) = F + q • F' := by
      funext U
      simp [Rat.smul_def]
    rw [e]
    exact h₁
  · intro F hF hreal
    have hnear : ∀ n : ℕ, ∃ H ∈ 𝒟₀, observableSupNorm (F - H) < 1 / ((n : ℝ) + 1) :=
      fun n => hdense F hF _ Nat.one_div_pos_of_nat
    choose H hH hn using hnear
    refine ⟨fun n => rePart (H n), fun n => ?_, ?_⟩
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨H n, hH n, rfl⟩)
    · rw [Metric.tendstoUniformly_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      filter_upwards [eventually_ge_atTop N] with n hnN U
      have hc : Continuous (F - H n) := Continuous.sub hF (hsub (hH n)).1
      have h₁ : ‖F U - H n U‖ ≤ observableSupNorm (F - H n) := norm_apply_le_supNorm hc U
      have h₂ : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (N : ℝ) ≤ n := by exact_mod_cast hnN
        linarith
      rw [dist_eq_norm]
      calc ‖F U - rePart (H n) U‖ ≤ ‖F U - H n U‖ := norm_sub_rePart_le hreal _ U
        _ < ε := by linarith [hn n]
theorem IsCountableRealDense.exists_near {𝒟 : Set (GaugeField a → ℂ)}
    (h𝒟 : IsCountableRealDense 𝒟) {G : GaugeField a → ℂ} (hc : Continuous G)
    (hr : IsRealValued G) {ε : ℝ} (hε : 0 < ε) :
    ∃ H ∈ 𝒟, ∀ U, ‖G U - H U‖ < ε := by
  obtain ⟨H, hH, hlim⟩ := h𝒟.2.2.2.2.2 G hc hr
  rw [Metric.tendstoUniformly_iff] at hlim
  obtain ⟨n, hn⟩ := (hlim ε hε).exists
  exact ⟨H n, hH n, fun U => by simpa [dist_eq_norm] using hn U⟩
theorem IsCountableRealDense.isSupNormDense_complexSpan {𝒟 : Set (GaugeField a → ℂ)}
    (h𝒟 : IsCountableRealDense 𝒟) : IsSupNormDense (complexSpan 𝒟) := by
  intro F hF ε hε
  have hc : Continuous F := hF
  obtain ⟨H, hH, hn⟩ := IsCountableRealDense.exists_near h𝒟 (continuous_rePart hc)
    (isRealValued_rePart F) (half_pos (half_pos hε))
  obtain ⟨H', hH', hn'⟩ := IsCountableRealDense.exists_near h𝒟 (continuous_imPart hc)
    (isRealValued_imPart F) (half_pos (half_pos hε))
  refine ⟨_, ⟨H, hH, H', hH', rfl⟩, ?_⟩
  have hle : observableSupNorm (F - fun U => H U + Complex.I * H' U) ≤ ε / 2 := by
    refine Real.iSup_le (fun U => ?_) (half_pos hε).le
    have e : (F - fun U => H U + Complex.I * H' U) U =
        (rePart F U - H U) + Complex.I * (imPart F U - H' U) := by
      simp only [Pi.sub_apply, rePart, imPart]
      conv_lhs => rw [← Complex.re_add_im (F U)]
      ring
    rw [e]
    calc ‖(rePart F U - H U) + Complex.I * (imPart F U - H' U)‖
        ≤ ‖rePart F U - H U‖ + ‖Complex.I * (imPart F U - H' U)‖ := norm_add_le _ _
      _ = ‖rePart F U - H U‖ + ‖imPart F U - H' U‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ ε / 2 := by linarith [hn U, hn' U]
  linarith
theorem integrable_of_continuous [CompactSpace (GaugeField a)] (ν : BorelProb a)
    {F : GaugeField a → ℂ} (hF : Continuous F) : Integrable F ν.1 := by
  have : IsProbabilityMeasure ν.1 := ν.2
  obtain ⟨C, hC⟩ := (isCompact_range hF).isBounded.exists_norm_le
  exact Integrable.of_bound hF.aestronglyMeasurable C
    (ae_of_all _ fun U => hC _ (Set.mem_range_self U))
theorem norm_integral_sub_integral_le [CompactSpace (GaugeField a)] (ν : BorelProb a)
    {F G : GaugeField a → ℂ} (hF : Continuous F) (hG : Continuous G) {c : ℝ}
    (h : ∀ U, ‖F U - G U‖ ≤ c) : ‖ν.integral F - ν.integral G‖ ≤ c := by
  have : IsProbabilityMeasure ν.1 := ν.2
  have e : ν.integral F - ν.integral G = ∫ U, (F U - G U) ∂ν.1 :=
    (integral_sub (integrable_of_continuous ν hF) (integrable_of_continuous ν hG)).symm
  rw [e]
  have := norm_integral_le_of_norm_le_const (μ := ν.1) (ae_of_all _ h)
  simpa using this
theorem integral_add_I_mul [CompactSpace (GaugeField a)] (ν : BorelProb a)
    {F F' : GaugeField a → ℂ} (hF : Continuous F) (hF' : Continuous F') :
    ν.integral (fun U => F U + Complex.I * F' U) =
      ν.integral F + Complex.I * ν.integral F' := by
  have h₁ : Integrable (fun U => Complex.I * F' U) ν.1 :=
    (integrable_of_continuous ν hF').const_mul _
  have e₁ : ν.integral (fun U => F U + Complex.I * F' U) =
      ∫ U, F U ∂ν.1 + ∫ U, Complex.I * F' U ∂ν.1 :=
    integral_add (integrable_of_continuous ν hF) h₁
  rw [e₁, integral_const_mul]
  rfl
theorem IsCountableRealDense.ext_prob [CompactSpace (GaugeField a)]
    (hD : LocalFnsSeparateProb a) {𝒟 : Set (GaugeField a → ℂ)} (h𝒟 : IsCountableRealDense 𝒟)
    (ν ν' : BorelProb a) (h : ∀ F ∈ 𝒟, ν.integral F = ν'.integral F) : ν = ν' := by
  refine hD ν ν' fun F hF => ?_
  have hFc : Continuous F := hF.1
  have hcont : ∀ H ∈ 𝒟, Continuous H := fun H hH => (h𝒟.2.1 hH).1
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨G, ⟨H, hH, H', hH', rfl⟩, hn⟩ :=
    IsCountableRealDense.isSupNormDense_complexSpan h𝒟 F hFc (ε / 2) (half_pos hε)
  have hGc : Continuous (fun U => H U + Complex.I * H' U) :=
    (hcont H hH).add (continuous_const.mul (hcont H' hH'))
  have hb : ∀ U, ‖F U - (H U + Complex.I * H' U)‖ ≤ ε / 2 := fun U =>
    (norm_apply_le_supNorm (G := F - fun U => H U + Complex.I * H' U) (hFc.sub hGc) U).trans hn.le
  have hsame : ν.integral (fun U => H U + Complex.I * H' U) =
      ν'.integral (fun U => H U + Complex.I * H' U) := by
    rw [integral_add_I_mul ν (hcont H hH) (hcont H' hH'),
      integral_add_I_mul ν' (hcont H hH) (hcont H' hH'), h H hH, h H' hH']
  have h₁ := norm_integral_sub_integral_le ν hFc hGc hb
  have h₂ := norm_integral_sub_integral_le ν' hFc hGc hb
  rw [hsame] at h₁
  rw [dist_eq_norm]
  calc ‖ν.integral F - ν'.integral F‖
      = ‖(ν.integral F - ν'.integral (fun U => H U + Complex.I * H' U)) -
          (ν'.integral F - ν'.integral (fun U => H U + Complex.I * H' U))‖ := by
        congr 1
        ring
    _ ≤ ‖ν.integral F - ν'.integral (fun U => H U + Complex.I * H' U)‖ +
          ‖ν'.integral F - ν'.integral (fun U => H U + Complex.I * H' U)‖ := norm_sub_le _ _
    _ ≤ ε := by linarith
theorem denseFamilyStatement_of_fieldAndMeasureSpaceProperties
    (h : GibbsAtFixedSpacing.SpacesOfFieldsAndMeasures.FieldAndMeasureSpaceProperties) :
    PeriodicGibbsStateSpace.DenseLocalFamily.denseFamilyStatement := by
  intro D
  obtain ⟨⟨-, hcomp, -⟩, hB, -, hD, hE⟩ := h D.mesh D.mesh_pos
  have := hcomp
  refine ⟨exists_isCountableRealDense hB hE, fun 𝒟 h𝒟 => ⟨?_, ?_,
    IsCountableRealDense.isSupNormDense_complexSpan h𝒟,
    fun ν ν' hνν' => IsCountableRealDense.ext_prob hD h𝒟 ν ν' hνν'⟩⟩
  · refine (h𝒟.1.image2 h𝒟.1 (fun F F' U => F U + Complex.I * F' U)).mono ?_
    rintro H ⟨F, hF, F', hF', rfl⟩
    exact ⟨F, hF, F', hF', rfl⟩
  · rintro H ⟨F, hF, F', hF', rfl⟩
    obtain ⟨-, ⟨A, hA⟩, -, -, -, -⟩ := hB
    have h₁ : F ∈ A := by rw [← SetLike.mem_coe, hA]; exact h𝒟.2.1 hF
    have h₂ : F' ∈ A := by rw [← SetLike.mem_coe, hA]; exact h𝒟.2.1 hF'
    have h₃ : F + Complex.I • F' ∈ A := A.add_mem h₁ (A.smul_mem h₂ _)
    rw [← hA]
    exact h₃
end PeriodicGibbsStateSpace.DenseLocalFamily
end YangMills.Construction
