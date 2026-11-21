import YangMills.Construction.LawInAState.FromSixteenCopiesToOneBoxProof
import YangMills.Construction.PeriodicOperators.SeriesOfTheSymbol
import YangMills.Construction.PeriodicOperators.SumsOfExponentials
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SymbolSeriesProof
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
variable {P Q : PeriodicData}
theorem euclidNormVec_sub_comm (a b : AmbientSpace) :
    euclidNormVec (a - b) = euclidNormVec (b - a) := by apply _root_.YangMills.SharedProofs.p26380 <;> assumption
theorem continuous_euclidNormVec_imVec :
    Continuous fun κ : Fin 4 → ℂ => euclidNormVec (imVec κ) := by
  unfold euclidNormVec imVec
  fun_prop
theorem isOpen_imStrip (δ : ℝ) : IsOpen (strictImStrip δ) :=
  isOpen_lt continuous_euclidNormVec_imVec continuous_const
theorem norm_cexp_I_mul_bilinDot_le (κ : Fin 4 → ℂ) (y : AmbientSpace) :
    ‖Complex.exp (Complex.I * bilinDot κ (toComplexVec y))‖ ≤
      Real.exp (euclidNormVec (imVec κ) * euclidNormVec y) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have hre : (Complex.I * bilinDot κ (toComplexVec y)).re = ∑ μ, (-(imVec κ μ)) * y μ := by
    simp [bilinDot, toComplexVec, imVec, Complex.mul_re, Complex.mul_im]
  rw [hre]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun μ => -(imVec κ μ)) y
  simpa [euclidNormVec] using hcs
theorem norm_symbolSummand_le (hP : IsPeriodic P) {T : Q.Carrier → P.Carrier → ℂ} {C δ r : ℝ}
    (hC : 0 < C) (hT : ExpDecay P Q T C δ) {κ : Fin 4 → ℂ}
    (hκ : euclidNormVec (imVec κ) ≤ r) (j : Q.Carrier) (i : P.Carrier) (m : Fin 4 → ℤ) :
    ‖symbolSummand P Q T κ j i m‖ ≤
      C * Real.exp (-(δ - r) * euclidNormVec (P.pos i - Q.pos j + castVec m)) := by
  have hy : P.pos (P.translate m i) - Q.pos j = P.pos i - Q.pos j + castVec m := by
    rw [hP.pos_translate]
    abel
  set y : AmbientSpace := P.pos i - Q.pos j + castVec m with hydef
  have hy0 : 0 ≤ euclidNormVec y := Real.sqrt_nonneg _
  have h1 : ‖T j (P.translate m i)‖ ≤ C * Real.exp (-δ * euclidNormVec y) := by
    have := hT j (P.translate m i)
    rwa [euclidNormVec_sub_comm, hy] at this
  have h2 : ‖Complex.exp (Complex.I * bilinDot κ (toComplexVec y))‖ ≤
      Real.exp (r * euclidNormVec y) :=
    (norm_cexp_I_mul_bilinDot_le κ y).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hκ hy0))
  unfold symbolSummand
  rw [hy, norm_mul]
  calc ‖T j (P.translate m i)‖ * ‖Complex.exp (Complex.I * bilinDot κ (toComplexVec y))‖
      ≤ (C * Real.exp (-δ * euclidNormVec y)) * Real.exp (r * euclidNormVec y) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = C * Real.exp (-(δ - r) * euclidNormVec y) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
theorem exists_lt_bound_of_isCompact {δ : ℝ} (hδ : 0 < δ) {K : Set (Fin 4 → ℂ)}
    (hK : K ⊆ strictImStrip δ) (hKc : IsCompact K) :
    ∃ r < δ, ∀ κ ∈ K, euclidNormVec (imVec κ) ≤ r := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, hδ, by simp⟩
  · obtain ⟨κ₀, hκ₀, hmax⟩ :=
      hKc.exists_isMaxOn hne continuous_euclidNormVec_imVec.continuousOn
    exact ⟨_, hK hκ₀, fun κ hκ => hmax hκ⟩
theorem exists_summable_majorant (hsum : ExponentialSums.Bounds) (hP : IsPeriodic P)
    {T : Q.Carrier → P.Carrier → ℂ} {δ : ℝ} (hrate : IsDecayRate P Q T δ) (j : Q.Carrier)
    (i : P.Carrier) {K : Set (Fin 4 → ℂ)} (hK : K ⊆ strictImStrip δ) (hKc : IsCompact K) :
    ∃ u : (Fin 4 → ℤ) → ℝ, Summable u ∧ ∀ m, ∀ κ ∈ K, ‖symbolSummand P Q T κ j i m‖ ≤ u m := by
  obtain ⟨hδ, C, hC, hT⟩ := hrate
  obtain ⟨r, hr, hKr⟩ := exists_lt_bound_of_isCompact hδ hK hKc
  refine ⟨fun m => C * Real.exp (-(δ - r) *
    euclidNormVec (P.pos i - Q.pos j + castVec m)), ?_, fun m κ hκ => ?_⟩
  · exact (((hsum (δ - r) (sub_pos.mpr hr)).2.1 _).1).mul_left C
  · exact norm_symbolSummand_le hP hC hT (hKr κ hκ) j i m
theorem continuous_symbolSummand (T : Q.Carrier → P.Carrier → ℂ) (j : Q.Carrier) (i : P.Carrier)
    (m : Fin 4 → ℤ) : Continuous fun κ => symbolSummand P Q T κ j i m := by
  unfold symbolSummand bilinDot
  fun_prop
theorem symbolSeriesClaim_holds (hsum : ExponentialSums.Bounds) : SymbolSeriesClaim := by
  intro P Q hP _ T δ hrate
  have hlu : ∀ j i,
      SummableLocallyUniformlyOn (fun m κ => symbolSummand P Q T κ j i m) (strictImStrip δ) :=
    fun j i => SummableLocallyUniformlyOn_of_locally_bounded (isOpen_imStrip δ)
      fun K hK hKc => exists_summable_majorant hsum hP hrate j i hK hKc
  refine ⟨?_, hlu, ?_, ?_⟩
  · intro κ hκ j i
    obtain ⟨u, hu, hb⟩ := exists_summable_majorant hsum hP hrate j i
      (K := {κ}) (by simpa using hκ) isCompact_singleton
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun m => hb m κ (mem_singleton κ)) hu
  · intro j i
    refine SummableLocallyUniformlyOn_of_locally_bounded (isOpen_imStrip δ)
      fun K hK hKc => ?_
    obtain ⟨u, hu, hb⟩ := exists_summable_majorant hsum hP hrate j i hK hKc
    exact ⟨u, hu, fun m κ hκ => by simpa using hb m κ hκ⟩
  · intro j i
    refine ⟨isOpen_imStrip δ, ?_, ?_⟩
    · refine continuousOn_pi.mpr fun _ => ?_
      obtain ⟨g, hg⟩ := hlu j i
      have hc : ContinuousOn g (strictImStrip δ) :=
        (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).continuousOn
          (Eventually.of_forall fun s => (continuous_finsetSum s fun m _ =>
            continuous_symbolSummand T j i m).continuousOn).frequently
      exact hc.congr fun κ hκ => hg.tsum_eqOn hκ
    · intro a ha k
      let line : ℂ → Fin 4 → ℂ := fun ζ =>
        a + ζ • YangMills.Construction.Coordinates.ComplexCoordinates.stdBasisVector k
      have hline : Continuous line := by
        simp only [line]
        fun_prop
      have hU : IsOpen (line ⁻¹' strictImStrip δ) := (isOpen_imStrip δ).preimage hline
      have h0 : (0 : ℂ) ∈ line ⁻¹' strictImStrip δ := by simpa [line] using ha
      have hl : SummableLocallyUniformlyOn (fun m ζ => symbolSummand P Q T (line ζ) j i m)
          (line ⁻¹' strictImStrip δ) := by
        refine SummableLocallyUniformlyOn_of_locally_bounded hU fun K hK hKc => ?_
        obtain ⟨u, hu, hb⟩ := exists_summable_majorant hsum hP hrate j i
          (K := line '' K) (image_subset_iff.mpr hK) (hKc.image hline)
        exact ⟨u, hu, fun m ζ hζ => hb m _ (mem_image_of_mem line hζ)⟩
      have hd : DifferentiableOn ℂ (fun ζ => ∑' m, symbolSummand P Q T (line ζ) j i m)
          (line ⁻¹' strictImStrip δ) := by
        refine hl.differentiableOn hU fun m ζ _ => ?_
        simp only [symbolSummand, bilinDot, line, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        fun_prop
      filter_upwards [hU.mem_nhds h0] with ζ hζ
      exact differentiableAt_pi.mpr fun _ => hd.differentiableAt (hU.mem_nhds hζ)
end YangMills.Construction.PeriodicOperators.SymbolSeriesProof
end
