import YangMills.Construction.Towers.BoundOfTheChainsOfLocalKernels
import YangMills.Construction.Towers.ChainsOfBoundedOperators
import YangMills.Construction.Towers.DecayOfTheResolventOfAKernelOfRangeAtMostTwoProof
import YangMills.Construction.Towers.ResolventAlongAFieldToTheSecondOrder
import YangMills.Construction.Towers.SumsInsideTheChainsOfLocalKernels
import YangMills.Construction.Towers.TaylorExpansionOfTheEntriesAlongAField
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
open YangMills.Construction.Tower.AbelianFieldDensity YangMills.Construction.Tower.ResolventDecay
open YangMills.Construction.Tower.LocalFamilies YangMills.Construction.OneLoopNotation
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
namespace SecondOrderResolvent
variable {J B : Type}
private lemma second_resolvent_thrice {A : Type} [Ring A] (R Rf V A₀ : A) (h₁ : R * A₀ = 1)
    (h₂ : (A₀ + V) * Rf = 1) :
    R = Rf + R * (V * R) - R * (V * (R * (V * R))) + R * (V * (R * (V * (R * (V * Rf))))) := by
  have hE : R - Rf - R * V * Rf = 0 := by
    have h : R = R * ((A₀ + V) * Rf) := by rw [h₂, mul_one]
    have h' : R * ((A₀ + V) * Rf) = (R * A₀) * Rf + R * V * Rf := by noncomm_ring
    rw [h', h₁, one_mul] at h
    rw [sub_sub, sub_eq_zero]
    exact h
  have hT : R - (Rf + R * (V * R) - R * (V * (R * (V * R))) + R * (V * (R * (V * (R * (V * Rf)))))) =
      (R - Rf - R * V * Rf) - R * V * (R - Rf - R * V * Rf) +
        R * V * R * V * (R - Rf - R * V * Rf) := by
    noncomm_ring
  rw [hE] at hT
  simpa [sub_eq_zero] using hT
private lemma matrixEntry_sub (S S' : BddOp (IndexL2 J)) (i j : J) :
    matrixEntry (S - S') i j = matrixEntry S i j - matrixEntry S' i j := by
  simp [matrixEntry]
private lemma cubicGrowth_add {pos : J → InfiniteLattice.AmbientSpace} {A A' : ℝ} {X Y : J → J → ℂ}
    (a : ℂ) (hX : IsCubicGrowthLocalKernel pos A X) (hY : IsCubicGrowthLocalKernel pos A' Y) :
    IsCubicGrowthLocalKernel pos (A + ‖a‖ * A') (fun i j => X i j + a * Y i j) := by
  refine ⟨fun i j h => by simp [hX.1 i j h, hY.1 i j h], fun i j => ?_⟩
  have hnorm : ‖a * Y i j‖ ≤
      ‖a‖ * (A' * (1 + TorusMetric.euclidNormVec (pos i)) ^ 3) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hY.2 i j) (norm_nonneg _)
  calc ‖X i j + a * Y i j‖ ≤ ‖X i j‖ + ‖a * Y i j‖ := norm_add_le _ _
    _ ≤ A * (1 + TorusMetric.euclidNormVec (pos i)) ^ 3 +
        ‖a‖ * (A' * (1 + TorusMetric.euclidNormVec (pos i)) ^ 3) :=
      add_le_add (hX.2 i j) hnorm
    _ = (A + ‖a‖ * A') * (1 + TorusMetric.euclidNormVec (pos i)) ^ 3 := by ring
private lemma norm_tsum_le_of_summable_le {P : Type} {g : P → ℂ} {b : ℝ}
    (h : Summable (fun p => ‖g p‖) ∧ ∑' p, ‖g p‖ ≤ b) : ‖∑' p, g p‖ ≤ b :=
  (norm_tsum_le_tsum_norm h.1).trans h.2
private lemma norm_matrixEntry_le {pos : J → InfiniteLattice.AmbientSpace}
    {src : B → InfiniteLattice.AmbientSpace} {C : ℝ} {T : (B → ℝ) → BddOp (IndexL2 J)}
    (h : IsLocallySmoothFamily pos src C T) (θ : B → ℝ) (i j : J) :
    ‖matrixEntry (T θ) i j‖ ≤ C := by
  obtain ⟨E, Q, -, -, hb, hq⟩ := h.entry_smooth i j
  rw [hq]
  have := hb 0 (by norm_num) (fun b => θ b.1)
  simpa [norm_iteratedFDeriv_zero] using this
private lemma resolventDecayRate_pos {z C : ℝ} (hz : 0 < z) (hC : 0 < C) :
    0 < resolventDecayRate z C := by apply _root_.YangMills.Construction.Tower.ResolventDecay.resolventDecayRate_pos <;> assumption
private lemma shifted_inverse_facts {pos : J → InfiniteLattice.AmbientSpace}
    {src : B → InfiniteLattice.AmbientSpace} {m m' : ℕ} {z C : ℝ}
    {T : (B → ℝ) → BddOp (IndexL2 J)} (h : IsLocalExpansionSetting pos src m m' z C T)
    (θ : B → ℝ) (hθ : IsBoundedBelowBy (addScalar (T θ) z) (z / 2)) (w : ℝ) (hw : 0 ≤ w) :
    IsExpDecayKernel pos (resolventDecayRate z C) (z / 4 + w)⁻¹
        (matrixEntry (inverseOp (addScalar (addScalar (T θ) z) w))) ∧
      IsTwoSidedInverse (addScalar (addScalar (T θ) z) w)
        (inverseOp (addScalar (addScalar (T θ) z) w)) := by
  refine ⟨fun i j => ?_, ?_⟩
  · exact h.space.resolventDecay (T θ) (h.family.selfAdjoint θ) hθ (norm_matrixEntry_le h.family θ)
      (h.family.finite_range θ) w hw i j
  · exact ((h.space.logShifted (T θ) ⟨h.family.selfAdjoint θ, hθ⟩).1 w hw).1
private lemma four_terms_le {Mb C a s D AW AV n₁ n₂ n₃ n₄ : ℝ} (hMb : 0 ≤ Mb) (hC : 0 < C)
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hD : s ≤ D) (hAV0 : 0 ≤ AV)
    (hAW : AW ≤ 72 * C * a ^ 2) (hAV : AV ≤ 76 * C * a)
    (h₁ : n₁ ≤ Mb * (64 * C * a ^ 3) * s ^ 2)
    (h₂ : n₂ ≤ a * (Mb * (4 * C) * AW * s ^ 3))
    (h₃ : n₃ ≤ Mb * AW * AV * s ^ 3)
    (h₄ : n₄ ≤ Mb * AV * AV * AV * s ^ 4) :
    n₁ + n₂ + n₃ + n₄ ≤
      Mb * (64 * C + 288 * C ^ 2 * D + 5472 * C ^ 2 * D + 438976 * C ^ 3 * D ^ 2) * a ^ 3 * s ^ 2 := by
  have hs3 : s ^ 3 ≤ s ^ 2 * D := by
    calc s ^ 3 = s ^ 2 * s := by ring
      _ ≤ s ^ 2 * D := mul_le_mul_of_nonneg_left hD (by positivity)
  have hs4 : s ^ 4 ≤ s ^ 2 * D ^ 2 := by
    calc s ^ 4 = s ^ 2 * s ^ 2 := by ring
      _ ≤ s ^ 2 * D ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hD 2) (by positivity)
  have b₂ : a * (Mb * (4 * C) * AW * s ^ 3) ≤
      Mb * (288 * C ^ 2 * D) * a ^ 3 * s ^ 2 := by
    calc a * (Mb * (4 * C) * AW * s ^ 3)
        ≤ a * (Mb * (4 * C) * (72 * C * a ^ 2) * (s ^ 2 * D)) := by gcongr
      _ = Mb * (288 * C ^ 2 * D) * a ^ 3 * s ^ 2 := by ring
  have b₃ : Mb * AW * AV * s ^ 3 ≤ Mb * (5472 * C ^ 2 * D) * a ^ 3 * s ^ 2 := by
    calc Mb * AW * AV * s ^ 3
        ≤ Mb * (72 * C * a ^ 2) * (76 * C * a) * (s ^ 2 * D) := by gcongr
      _ = Mb * (5472 * C ^ 2 * D) * a ^ 3 * s ^ 2 := by ring
  have b₄ : Mb * AV * AV * AV * s ^ 4 ≤ Mb * (438976 * C ^ 3 * D ^ 2) * a ^ 3 * s ^ 2 := by
    calc Mb * AV * AV * AV * s ^ 4
        ≤ Mb * (76 * C * a) * (76 * C * a) * (76 * C * a) * (s ^ 2 * D ^ 2) := by gcongr
      _ = Mb * (438976 * C ^ 3 * D ^ 2) * a ^ 3 * s ^ 2 := by ring
  nlinarith [h₁, h₂.trans b₂, h₃.trans b₃, h₄.trans b₄]
end SecondOrderResolvent
open SecondOrderResolvent in
theorem resolventSecondOrderExpansion_holds
    (hbound : LoopTermsBound)
    (hoperators : LoopSumsAsTraces)
    (hsums : loopSums_linear_and_tsum)
    (htaylor : taylorKernels_cubicGrowth) :
    ResolventSecondOrderExpansion := by
  intro z C m m' hz hC
  have hc := resolventDecayRate_pos hz hC
  obtain ⟨Mb, hMb, hb⟩ := hbound (resolventDecayRate z C) m hc
  obtain ⟨Ms, -, hsum⟩ := hsums (resolventDecayRate z C) m hc
  refine ⟨Mb * (64 * C + 288 * C ^ 2 * (4 / z) + 5472 * C ^ 2 * (4 / z) +
      438976 * C ^ 3 * (4 / z) ^ 2), by positivity, ?_⟩
  intro J B pos src T hset ξ hξ f hf hTf w hw
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = (z / 4 + w)⁻¹ := ⟨_, rfl⟩
  have hzw : 0 < z / 4 + w := by positivity
  have hs0 : 0 ≤ s := by rw [hs_def]; positivity
  have hsD : s ≤ 4 / z := by
    rw [hs_def, inv_eq_one_div, div_le_div_iff₀ hzw hz]
    linarith
  obtain ⟨r, hr, hsmall⟩ := hset.lower_bound
  have hT0 : IsBoundedBelowBy (addScalar (T fun _ => 0) z) (z / 2) :=
    hsmall _ (fun _ => by simpa using hr.le)
  obtain ⟨hdR, hiR⟩ := shifted_inverse_facts hset (fun _ => 0) hT0 w hw
  obtain ⟨hdF, hiF⟩ := shifted_inverse_facts hset (fun b => f * ξ b) hTf w hw
  rw [← hs_def] at hdR hdF
  obtain ⟨R, hRdef⟩ : ∃ R, R = baseResolvent T z w := ⟨_, rfl⟩
  obtain ⟨Rf, hRfdef⟩ : ∃ Rf, Rf = shiftedResolventAlong T ξ z f w := ⟨_, rfl⟩
  have hdR' : IsExpDecayKernel pos (resolventDecayRate z C) s (matrixEntry R) := by
    rw [hRdef]; exact hdR
  have hdF' : IsExpDecayKernel pos (resolventDecayRate z C) s (matrixEntry Rf) := by
    rw [hRfdef]; exact hdF
  have hiR' : R * addScalar (addScalar (T fun _ => 0) z) w = 1 := by rw [hRdef]; exact hiR.2
  have hiF' : addScalar (addScalar (T fun b => f * ξ b) z) w * Rf = 1 := by
    rw [hRfdef]; exact hiF.1
  obtain ⟨V, hVdef⟩ : ∃ V : BddOp (IndexL2 J),
      V = (T fun b => f * ξ b) - T fun _ => 0 := ⟨_, rfl⟩
  have hsumop : addScalar (addScalar (T fun _ => 0) z) w + V =
      addScalar (addScalar (T fun b => f * ξ b) z) w := by
    rw [hVdef]; simp only [addScalar]; abel
  have hI := second_resolvent_thrice R Rf V _ hiR' (by rw [hsumop]; exact hiF')
  obtain ⟨hK1, hK2, hEf⟩ := htaylor J B pos src m m' z C T hz hC hset ξ hξ
  have hE := hEf f
  obtain ⟨K₁, hK₁def⟩ : ∃ K, K = firstVariationKernel T ξ := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂def⟩ : ∃ K, K = secondVariationKernel T ξ := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ K, K = taylorRemainderKernel T ξ f := ⟨_, rfl⟩
  rw [← hK₁def] at hK1
  rw [← hK₂def] at hK2
  rw [← hEdef] at hE
  obtain ⟨a₂, ha₂⟩ : ∃ a : ℂ, a = ((1 / 2 * f ^ 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : J → J → ℂ, W = fun i j => E i j + a₂ * K₂ i j := ⟨_, rfl⟩
  have hVker : matrixEntry V = fun i j => W i j + (f : ℂ) * K₁ i j := by
    funext i j
    have h0 : entryAlong T ξ i j 0 = matrixEntry (T fun _ => 0) i j := by simp [entryAlong]
    have h1 : entryAlong T ξ i j f = matrixEntry (T fun b => f * ξ b) i j := rfl
    rw [hVdef, matrixEntry_sub, hWdef, hEdef, ha₂, hK₁def, hK₂def]
    simp only [taylorRemainderKernel, h0, h1]
    ring
  obtain ⟨AW, hAWdef⟩ : ∃ A : ℝ, A = 64 * C * |f| ^ 3 + ‖a₂‖ * (16 * C) := ⟨_, rfl⟩
  obtain ⟨AV, hAVdef⟩ : ∃ A : ℝ, A = AW + ‖(f : ℂ)‖ * (4 * C) := ⟨_, rfl⟩
  have hW : IsCubicGrowthLocalKernel pos AW W := by
    rw [hAWdef, hWdef]; exact cubicGrowth_add a₂ hE hK2
  have hV : IsCubicGrowthLocalKernel pos AV (matrixEntry V) := by
    rw [hAVdef, hVker]; exact cubicGrowth_add (f : ℂ) hW hK1
  have hVsum : IsCubicGrowthLocalKernel pos AV (fun i j => W i j + (f : ℂ) * K₁ i j) := by
    rw [← hVker]; exact hV
  have hna : ‖a₂‖ = 1 / 2 * |f| ^ 2 := by
    rw [ha₂, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), sq_abs]
  have hnf : ‖(f : ℂ)‖ = |f| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have ha0 : 0 ≤ |f| := abs_nonneg f
  have hE0 : 0 ≤ 64 * C * |f| ^ 3 := by positivity
  have hK10 : 0 ≤ 4 * C := by positivity
  have hK20 : 0 ≤ 16 * C := by positivity
  have hAW0 : 0 ≤ AW := by rw [hAWdef]; positivity
  have hAV0 : 0 ≤ AV := by rw [hAVdef]; positivity
  have ha3 : |f| ^ 3 ≤ |f| ^ 2 := by
    calc |f| ^ 3 = |f| ^ 2 * |f| := by ring
      _ ≤ |f| ^ 2 * 1 := mul_le_mul_of_nonneg_left hf (by positivity)
      _ = |f| ^ 2 := mul_one _
  have ha2 : |f| ^ 2 ≤ |f| := by
    calc |f| ^ 2 = |f| * |f| := by ring
      _ ≤ |f| * 1 := mul_le_mul_of_nonneg_left hf ha0
      _ = |f| := mul_one _
  have hAW : AW ≤ 72 * C * |f| ^ 2 := by
    rw [hAWdef, hna]
    nlinarith [mul_le_mul_of_nonneg_left ha3 hC.le]
  have hAV : AV ≤ 76 * C * |f| := by
    rw [hAVdef, hnf]
    nlinarith [mul_le_mul_of_nonneg_left ha2 hC.le]
  have hl := hset.space.placement
  obtain ⟨hb1, hb2, hb3⟩ := hb J pos hl s hs0
  obtain ⟨hs1, hs2, -, -⟩ := hsum J pos hl s hs0
  obtain ⟨ho1, ho2, ho3⟩ :=
    hoperators (resolventDecayRate z C) m hc J pos hl hset.space.entryFacts s hs0
  have hP1 : traceAt pos (R * (V * R)) 0 =
      loopSumOne pos (matrixEntry R) (matrixEntry V) (matrixEntry R) :=
    ho1 R R V AV hAV0 hdR' hdR' hV
  have hP2 : traceAt pos (R * (V * (R * (V * R)))) 0 =
      loopSumTwo pos (matrixEntry R) (matrixEntry V) (matrixEntry R) (matrixEntry V)
        (matrixEntry R) :=
    ho2 R R R V V AV AV hAV0 hAV0 hdR' hdR' hdR' hV hV
  have hP3 : traceAt pos (R * (V * (R * (V * (R * (V * Rf)))))) 0 =
      loopSumThree pos (matrixEntry R) (matrixEntry V) (matrixEntry R) (matrixEntry V)
        (matrixEntry R) (matrixEntry V) (matrixEntry Rf) :=
    ho3 R R R Rf V V V AV AV AV hAV0 hAV0 hAV0 hdR' hdR' hdR' hdF' hV hV hV
  have hc1V : loopSumOne pos (matrixEntry R) (matrixEntry V) (matrixEntry R) =
      loopSumOne pos (matrixEntry R) W (matrixEntry R) +
        (f : ℂ) * loopSumOne pos (matrixEntry R) K₁ (matrixEntry R) := by
    rw [hVker]
    exact (hs1 (matrixEntry R) (matrixEntry R) W K₁ AW (4 * C) (f : ℂ) hAW0 hK10 hdR' hdR' hW hK1)
  have hc1W : loopSumOne pos (matrixEntry R) W (matrixEntry R) =
      loopSumOne pos (matrixEntry R) E (matrixEntry R) +
        a₂ * loopSumOne pos (matrixEntry R) K₂ (matrixEntry R) := by
    rw [hWdef]
    exact hs1 (matrixEntry R) (matrixEntry R) E K₂ _ (16 * C) a₂ hE0 hK20 hdR' hdR' hE hK2
  have hc2V : loopSumTwo pos (matrixEntry R) (matrixEntry V) (matrixEntry R) (matrixEntry V)
        (matrixEntry R) =
      loopSumTwo pos (matrixEntry R) W (matrixEntry R) (matrixEntry V) (matrixEntry R) +
        (f : ℂ) * loopSumTwo pos (matrixEntry R) K₁ (matrixEntry R) (matrixEntry V)
          (matrixEntry R) := by
    have h := (hs2 (matrixEntry R) (matrixEntry R) (matrixEntry R) W K₁ (matrixEntry V) AW (4 * C)
      AV (f : ℂ) hAW0 hK10 hAV0 hdR' hdR' hdR' hW hK1 hV).1
    rwa [← hVker] at h
  have hc2K : loopSumTwo pos (matrixEntry R) K₁ (matrixEntry R) (matrixEntry V) (matrixEntry R) =
      loopSumTwo pos (matrixEntry R) K₁ (matrixEntry R) W (matrixEntry R) +
        (f : ℂ) * loopSumTwo pos (matrixEntry R) K₁ (matrixEntry R) K₁ (matrixEntry R) := by
    have h := (hs2 (matrixEntry R) (matrixEntry R) (matrixEntry R) W K₁ K₁ AW (4 * C) (4 * C)
      (f : ℂ) hAW0 hK10 hK10 hdR' hdR' hdR' hW hK1 hK1).2
    rwa [← hVker] at h
  have h0 : PeriodicOperators.castVec (0 : Fin 4 → ℤ) = 0 := by
    funext μ; simp [PeriodicOperators.castVec]
  have hτ := (hset.space.trace_bounded 0).1
  simp only [h0] at hτ
  have hτR : traceAt pos R 0 = traceAt pos Rf 0 +
      traceAt pos (R * (V * R)) 0 - traceAt pos (R * (V * (R * (V * R)))) 0 +
      traceAt pos (R * (V * (R * (V * (R * (V * Rf)))))) 0 := by
    have e : R = ((Rf + (1 : ℂ) • (R * (V * R))) + (-1 : ℂ) • (R * (V * (R * (V * R))))) +
        (1 : ℂ) • (R * (V * (R * (V * (R * (V * Rf)))))) := by
      rw [one_smul, one_smul, neg_one_smul, ← sub_eq_add_neg]
      exact hI
    calc traceAt pos R 0 = traceAt pos
          (((Rf + (1 : ℂ) • (R * (V * R))) + (-1 : ℂ) • (R * (V * (R * (V * R))))) +
            (1 : ℂ) • (R * (V * (R * (V * (R * (V * Rf))))))) 0 :=
          congrArg (fun X => traceAt pos X 0) e
      _ = _ := by rw [hτ, hτ, hτ]; ring
  simp only [resolventFirstCoeff, resolventSecondCoeff, ← hRdef, ← hRfdef, ← hK₁def,
    ← hK₂def, ← ha₂, ← hs_def]
  have hr' : traceAt pos R 0 - traceAt pos Rf 0 -
        (f : ℂ) * loopSumOne pos (matrixEntry R) K₁ (matrixEntry R) -
        a₂ * (loopSumOne pos (matrixEntry R) K₂ (matrixEntry R) -
          2 * loopSumTwo pos (matrixEntry R) K₁ (matrixEntry R) K₁ (matrixEntry R)) =
      loopSumOne pos (matrixEntry R) E (matrixEntry R) +
        -(f : ℂ) * loopSumTwo pos (matrixEntry R) K₁ (matrixEntry R) W (matrixEntry R) +
        -loopSumTwo pos (matrixEntry R) W (matrixEntry R) (matrixEntry V) (matrixEntry R) +
        loopSumThree pos (matrixEntry R) (matrixEntry V) (matrixEntry R) (matrixEntry V)
          (matrixEntry R) (matrixEntry V) (matrixEntry Rf) := by
    rw [hτR, hP1, hP2, hP3, hc1V, hc1W, hc2V, hc2K]
    have h2 : 2 * a₂ = (f : ℂ) ^ 2 := by rw [ha₂]; push_cast; ring
    linear_combination loopSumTwo pos (matrixEntry R) K₁ (matrixEntry R) K₁ (matrixEntry R) * h2
  rw [hr']
  have n1 : ‖loopSumOne pos (matrixEntry R) E (matrixEntry R)‖ ≤ Mb * (64 * C * |f| ^ 3) * s ^ 2 :=
    norm_tsum_le_of_summable_le (hb1 _ _ E _ hE0 hdR' hdR' hE)
  have n2 : ‖-(f : ℂ) * loopSumTwo pos (matrixEntry R) K₁ (matrixEntry R) W (matrixEntry R)‖ ≤
      |f| * (Mb * (4 * C) * AW * s ^ 3) := by
    rw [norm_mul, norm_neg, hnf]
    exact mul_le_mul_of_nonneg_left
      (norm_tsum_le_of_summable_le (hb2 _ _ _ K₁ W _ _ hK10 hAW0 hdR' hdR' hdR' hK1 hW)) ha0
  have n3 : ‖-loopSumTwo pos (matrixEntry R) W (matrixEntry R) (matrixEntry V) (matrixEntry R)‖ ≤
      Mb * AW * AV * s ^ 3 := by
    rw [norm_neg]
    exact norm_tsum_le_of_summable_le (hb2 _ _ _ W _ _ _ hAW0 hAV0 hdR' hdR' hdR' hW hV)
  have n4 : ‖loopSumThree pos (matrixEntry R) (matrixEntry V) (matrixEntry R) (matrixEntry V)
      (matrixEntry R) (matrixEntry V) (matrixEntry Rf)‖ ≤ Mb * AV * AV * AV * s ^ 4 :=
    norm_tsum_le_of_summable_le
      (hb3 _ _ _ _ _ _ _ _ _ _ hAV0 hAV0 hAV0 hdR' hdR' hdR' hdF' hV hV hV)
  have hfin := four_terms_le hMb hC ha0 hs0 hsD hAV0 hAW hAV n1 n2 n3 n4
  have t1 := norm_add_le (loopSumOne pos (matrixEntry R) E (matrixEntry R) +
      -(f : ℂ) * loopSumTwo pos (matrixEntry R) K₁ (matrixEntry R) W (matrixEntry R) +
      -loopSumTwo pos (matrixEntry R) W (matrixEntry R) (matrixEntry V) (matrixEntry R))
    (loopSumThree pos (matrixEntry R) (matrixEntry V) (matrixEntry R) (matrixEntry V)
      (matrixEntry R) (matrixEntry V) (matrixEntry Rf))
  have t2 := norm_add_le (loopSumOne pos (matrixEntry R) E (matrixEntry R) +
      -(f : ℂ) * loopSumTwo pos (matrixEntry R) K₁ (matrixEntry R) W (matrixEntry R))
    (-loopSumTwo pos (matrixEntry R) W (matrixEntry R) (matrixEntry V) (matrixEntry R))
  have t3 := norm_add_le (loopSumOne pos (matrixEntry R) E (matrixEntry R))
    (-(f : ℂ) * loopSumTwo pos (matrixEntry R) K₁ (matrixEntry R) W (matrixEntry R))
  linarith
end YangMills.Construction.Tower.LocalFamilies
end
