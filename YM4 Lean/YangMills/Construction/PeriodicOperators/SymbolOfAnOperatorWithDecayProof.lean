import YangMills.Construction.PeriodicOperators.BoundOfTheKernelOfAMatrixFunctionProof
import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.SeriesOfTheSymbolProof
import YangMills.Construction.PeriodicOperators.SymbolOfAnOperatorWithDecay
import YangMills.Construction.PeriodicOperators.SymbolOnClassesAndPlaneWaves
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators.ExpDecaySymbol
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec l1NormVec)
variable {P P' : PeriodicData}
theorem euclidNormVec_le_l1NormVec (v : AmbientSpace) : euclidNormVec v ≤ l1NormVec v := by apply _root_.YangMills.Construction.PeriodicOperators.MatrixFunctionKernel.euclidNormVec_le_l1NormVec <;> assumption
theorem l1NormVec_sub_comm (a b : AmbientSpace) : l1NormVec (a - b) = l1NormVec (b - a) := by
  unfold l1NormVec
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Pi.sub_apply]
  exact abs_sub_comm _ _
theorem isOpen_openImStrip (υ : ℝ) : IsOpen (openImStrip υ) := by
  have hset : openImStrip υ = ⋂ μ : Fin 4, {κ : Fin 4 → ℂ | |(κ μ).im| < υ} := by
    ext κ
    simp [openImStrip]
  rw [hset]
  exact isOpen_iInter_of_finite fun μ => isOpen_lt (by fun_prop) continuous_const
theorem norm_cexp_I_mul_le {κ : Fin 4 → ℂ} {r : ℝ} (hκ : ∀ μ, |(κ μ).im| ≤ r) (v : AmbientSpace) :
    ‖Complex.exp (Complex.I * bilinDot κ (toComplexVec v))‖ ≤ Real.exp (r * l1NormVec v) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have hre : (Complex.I * bilinDot κ (toComplexVec v)).re = ∑ μ, (-(κ μ).im) * v μ := by
    simp [bilinDot, toComplexVec, Complex.mul_re, Complex.mul_im]
  rw [hre, l1NormVec, Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => ?_
  calc (-(κ μ).im) * v μ ≤ |(-(κ μ).im) * v μ| := le_abs_self _
    _ = |(κ μ).im| * |v μ| := by rw [abs_mul, abs_neg]
    _ ≤ r * |v μ| := mul_le_mul_of_nonneg_right (hκ μ) (abs_nonneg _)
theorem norm_symbolSummand_le (hP : IsPeriodic P) {T : P'.Carrier → P.Carrier → ℂ} {C υ r : ℝ}
    (hT : ∀ i' i, ‖T i' i‖ ≤ C * Real.exp (-υ * l1NormVec (P'.pos i' - P.pos i)))
    (hr : r < υ) {κ : Fin 4 → ℂ} (hκ : ∀ μ, |(κ μ).im| ≤ r) (i' : P'.Carrier) (i : P.Carrier)
    (n : Fin 4 → ℤ) :
    ‖symbolSummand P P' T κ i' i n‖ ≤
      |C| * Real.exp (-(υ - r) * euclidNormVec (P.pos i - P'.pos i' + castVec n)) := by
  have hv : P.pos (P.translate n i) - P'.pos i' =
      P.pos i - P'.pos i' + castVec n := by
    rw [hP.pos_translate]
    abel
  set v : AmbientSpace := P.pos i - P'.pos i' + castVec n with hvdef
  have hbd : ‖T i' (P.translate n i)‖ ≤ |C| * Real.exp (-υ * l1NormVec v) := by
    have := hT i' (P.translate n i)
    rw [l1NormVec_sub_comm, hv] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
  have hex := norm_cexp_I_mul_le hκ v
  unfold symbolSummand
  rw [hv, norm_mul]
  calc ‖T i' (P.translate n i)‖ * ‖Complex.exp (Complex.I * bilinDot κ (toComplexVec v))‖
      ≤ (|C| * Real.exp (-υ * l1NormVec v)) * Real.exp (r * l1NormVec v) :=
        mul_le_mul hbd hex (norm_nonneg _) (by positivity)
    _ = |C| * Real.exp (-(υ - r) * l1NormVec v) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
    _ ≤ |C| * Real.exp (-(υ - r) * euclidNormVec v) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
        have := mul_le_mul_of_nonneg_left (euclidNormVec_le_l1NormVec v) (sub_pos.mpr hr).le
        linarith
theorem exists_im_bound_of_isCompact {υ : ℝ} (hυ : 0 < υ) {K : Set (Fin 4 → ℂ)}
    (hK : K ⊆ openImStrip υ) (hKc : IsCompact K) :
    ∃ r < υ, ∀ κ ∈ K, ∀ μ, |(κ μ).im| ≤ r := by
  have hμ : ∀ μ : Fin 4, ∃ r < υ, ∀ κ ∈ K, |(κ μ).im| ≤ r := by
    intro μ
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, hυ, by simp⟩
    · have hc : Continuous fun κ : Fin 4 → ℂ => |(κ μ).im| := by fun_prop
      obtain ⟨κ₀, hκ₀, hmax⟩ := hKc.exists_isMaxOn hne hc.continuousOn
      exact ⟨_, hK hκ₀ μ, fun κ hκ => hmax hκ⟩
  choose r hr hb using hμ
  refine ⟨Finset.univ.sup' Finset.univ_nonempty r, ?_, fun κ hκ μ => ?_⟩
  · exact (Finset.sup'_lt_iff _).mpr fun μ _ => hr μ
  · exact (hb μ κ hκ).trans (Finset.le_sup' r (Finset.mem_univ μ))
theorem exists_summable_majorant (hsum : ExponentialSums.Bounds) (hP : IsPeriodic P)
    {T : P'.Carrier → P.Carrier → ℂ} {C υ : ℝ} (hυ : 0 < υ)
    (hT : ∀ i' i, ‖T i' i‖ ≤ C * Real.exp (-υ * l1NormVec (P'.pos i' - P.pos i)))
    (i' : P'.Carrier) (i : P.Carrier) {K : Set (Fin 4 → ℂ)} (hK : K ⊆ openImStrip υ)
    (hKc : IsCompact K) :
    ∃ u : (Fin 4 → ℤ) → ℝ, Summable u ∧ ∀ n, ∀ κ ∈ K, ‖symbolSummand P P' T κ i' i n‖ ≤ u n := by
  obtain ⟨r, hr, hKr⟩ := exists_im_bound_of_isCompact hυ hK hKc
  refine ⟨fun n => |C| * Real.exp (-(υ - r) *
    euclidNormVec (P.pos i - P'.pos i' + castVec n)), ?_, fun n κ hκ => ?_⟩
  · exact (((hsum (υ - r) (sub_pos.mpr hr)).2.1 _).1).mul_left |C|
  · exact norm_symbolSummand_le hP hT hr (hKr κ hκ) i' i n
theorem continuous_symbolSummand (T : P'.Carrier → P.Carrier → ℂ) (i' : P'.Carrier) (i : P.Carrier)
    (n : Fin 4 → ℤ) : Continuous fun κ => symbolSummand P P' T κ i' i n := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolSeriesProof.continuous_symbolSummand <;> assumption
theorem linearMapEntry_linearMapOfEntries {J J' : Type} [Finite J] (A : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries A) = A := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
theorem holomorphicOnStrip_holds (hsum : ExponentialSums.Bounds)
    (hq : SymbolOnQuotients.Claim) : HolomorphicOnStrip := by
  intro P P' hP hP' υ hυ C T hper hT
  have hO := isOpen_openImStrip υ
  have hform : SymbolSummableOn P P' T (openImStrip υ) := by
    intro κ hκ i' i
    obtain ⟨u, hu, hb⟩ := exists_summable_majorant hsum hP hυ hT i' i
      (K := {κ}) (by simpa using hκ) isCompact_singleton
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => hb n κ (mem_singleton κ)) hu
  refine ⟨hform, by norm_num, hO, ?_⟩
  rintro ⟨c', c⟩
  obtain ⟨i', rfl⟩ : ∃ i', P'.mkQuot 1 i' = c' := Quot.exists_rep c'
  obtain ⟨i, rfl⟩ : ∃ i, P.mkQuot 1 i = c := Quot.exists_rep c
  have hfin : Finite P.UnitQuot := hP.finite_quot
  have hent : ∀ κ ∈ openImStrip υ,
      quotHomEntries (symbolHom P P' T κ) (P'.mkQuot 1 i', P.mkQuot 1 i) =
        fourierSymbol P P' T κ i' i := by
    intro κ hκ
    have e := (hq P P' hP hP' T hper).quotSymbol_mkQuot κ (hform κ hκ) i' i
    simp only [quotHomEntries, symbolHom]
    rw [linearMapEntry_linearMapOfEntries]
    exact e
  have hlu : SummableLocallyUniformlyOn (fun n κ => symbolSummand P P' T κ i' i n)
      (openImStrip υ) :=
    SummableLocallyUniformlyOn_of_locally_bounded hO
      fun K hK hKc => exists_summable_majorant hsum hP hυ hT i' i hK hKc
  refine ⟨hO, ?_, ?_⟩
  · refine continuousOn_pi.mpr fun _ => ?_
    obtain ⟨g, hg⟩ := hlu
    have hc : ContinuousOn g (openImStrip υ) :=
      (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).continuousOn
        (Eventually.of_forall fun s => (continuous_finsetSum s fun n _ =>
          continuous_symbolSummand T i' i n).continuousOn).frequently
    exact hc.congr fun κ hκ => (hent κ hκ).trans (hg.tsum_eqOn hκ)
  · intro a ha j
    let line : ℂ → Fin 4 → ℂ := fun ζ =>
      a + ζ • YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector j
    have hline : Continuous line := by
      simp only [line]
      fun_prop
    have hU : IsOpen (line ⁻¹' openImStrip υ) := hO.preimage hline
    have h0 : (0 : ℂ) ∈ line ⁻¹' openImStrip υ := by simpa [line] using ha
    have hl : SummableLocallyUniformlyOn (fun n ζ => symbolSummand P P' T (line ζ) i' i n)
        (line ⁻¹' openImStrip υ) := by
      refine SummableLocallyUniformlyOn_of_locally_bounded hU fun K hK hKc => ?_
      obtain ⟨u, hu, hb⟩ := exists_summable_majorant hsum hP hυ hT i' i
        (K := line '' K) (image_subset_iff.mpr hK) (hKc.image hline)
      exact ⟨u, hu, fun n ζ hζ => hb n _ (mem_image_of_mem line hζ)⟩
    have hd : DifferentiableOn ℂ (fun ζ => ∑' n, symbolSummand P P' T (line ζ) i' i n)
        (line ⁻¹' openImStrip υ) := by
      refine hl.differentiableOn hU fun n ζ _ => ?_
      simp only [symbolSummand, bilinDot, line, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    filter_upwards [hU.mem_nhds h0] with ζ hζ
    refine differentiableAt_pi.mpr fun _ => ?_
    refine (hd.differentiableAt (hU.mem_nhds hζ)).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hζ] with ζ' hζ'
    exact hent _ hζ'
end YangMills.Construction.PeriodicOperators.ExpDecaySymbol
end
