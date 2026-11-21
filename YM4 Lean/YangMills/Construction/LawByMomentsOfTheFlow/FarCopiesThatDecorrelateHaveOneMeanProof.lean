import YangMills.Construction.LawByMomentsOfTheFlow.FarCopiesThatDecorrelateHaveOneMean
import YangMills.Construction.LawByMomentsOfTheFlow.ScoresInALimitFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentMethod
private theorem integral_sub_sub_add {α : Type} [MeasurableSpace α] {μ : Measure α} (f g h k : α → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (hh : Integrable h μ) (hk : Integrable k μ) :
    ∫ ω, (f ω - g ω - h ω + k ω) ∂μ = (∫ ω, f ω ∂μ) - (∫ ω, g ω ∂μ) - (∫ ω, h ω ∂μ) + ∫ ω, k ω ∂μ := by
  have e : (fun ω => f ω - g ω - h ω + k ω) = f - g - h + k := rfl
  rw [e, integral_add' ((hf.sub hg).sub hh) hk, integral_sub' (hf.sub hg) hh, integral_sub' hf hg]
section Ergodic
variable {Ω : Type} [m0 : MeasurableSpace Ω] {P : Measure Ω} {S : Ω → Ω}
private abbrev invariantEvents (S : Ω → Ω) : MeasurableSpace Ω := MeasurableSpace.invariants S ⊓ m0
private theorem integral_comp_iterate (hS : MeasurePreserving S P P) {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) (k : ℕ) :
    ∫ v, f (S^[k] v) ∂P = ∫ v, f v ∂P := by
  have hp := hS.iterate k
  have h := integral_map (μ := P) hp.aemeasurable (f := f) (by rw [hp.map_eq]; exact hf)
  rw [hp.map_eq] at h
  exact h.symm
private theorem apply_eq_of_stronglyMeasurable_invariantEvents {Z : Ω → ℝ} (hZ : StronglyMeasurable[invariantEvents S] Z) (v : Ω) :
    Z (S v) = Z v := by
  have hset : MeasurableSet[invariantEvents S] (Z ⁻¹' {Z v}) := hZ.measurable (measurableSet_singleton _)
  have hinv : MeasurableSet[MeasurableSpace.invariants S] (Z ⁻¹' {Z v}) :=
    (inf_le_left : invariantEvents S ≤ MeasurableSpace.invariants S) _ hset
  have h2 : S ⁻¹' (Z ⁻¹' {Z v}) = Z ⁻¹' {Z v} := (MeasurableSpace.measurableSet_invariants.1 hinv).2
  exact show v ∈ S ⁻¹' (Z ⁻¹' {Z v}) from by
    rw [h2]
    rfl
private theorem condExp_invariantEvents_eq_zero_of_correlation_decay [IsProbabilityMeasure P] (hS : MeasurePreserving S P P) {Y : Ω → ℝ} (hY : MemLp Y 2 P)
    (hcor : ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → |∫ v, Y v * Y (S^[k] v) ∂P| ≤ ε) :
    P[Y | invariantEvents S] =ᵐ[P] 0 := by
  have hm : invariantEvents S ≤ m0 := inf_le_right
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = P[Y | invariantEvents S] := ⟨_, rfl⟩
  rw [← hZdef]
  have hZs : StronglyMeasurable[invariantEvents S] Z := hZdef ▸ stronglyMeasurable_condExp
  have hZinv : ∀ v, Z (S v) = Z v := apply_eq_of_stronglyMeasurable_invariantEvents hZs
  have hZit : ∀ (k : ℕ) (v : Ω), Z (S^[k] v) = Z v := by
    intro k v
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', hZinv, ih]
  have hZ2 : MemLp Z 2 P := hZdef ▸ hY.condExp one_le_two
  have hYk : ∀ k : ℕ, MemLp (fun v => Y (S^[k] v)) 2 P := fun k => hY.comp_measurePreserving (hS.iterate k)
  obtain ⟨I, hI⟩ : ∃ I, I = ∫ v, Z v * Z v ∂P := ⟨_, rfl⟩
  have hZY : ∫ v, Z v * Y v ∂P = I := by
    have hpull : P[Z * Y | invariantEvents S] =ᵐ[P] Z * P[Y | invariantEvents S] :=
      condExp_mul_of_stronglyMeasurable_left hZs (hZ2.integrable_mul hY) (hY.integrable one_le_two)
    calc ∫ v, Z v * Y v ∂P = ∫ v, (P[Z * Y | invariantEvents S]) v ∂P := (integral_condExp hm).symm
      _ = ∫ v, (Z * P[Y | invariantEvents S]) v ∂P := integral_congr_ae hpull
      _ = I := by
        rw [hI, ← hZdef]
        rfl
  have hZYk : ∀ k : ℕ, ∫ v, Y (S^[k] v) * Z v ∂P = I := by
    intro k
    have h := integral_comp_iterate hS (f := fun v => Z v * Y v) (hZ2.integrable_mul hY).aestronglyMeasurable k
    simp only [hZit] at h
    rw [← hZY, ← h]
    exact integral_congr_ae (Eventually.of_forall fun v => mul_comm _ _)
  have hgap : ∀ a b : ℕ, a ≤ b → ∫ v, Y (S^[a] v) * Y (S^[b] v) ∂P = ∫ v, Y v * Y (S^[b - a] v) ∂P := by
    intro a b hab
    have h := integral_comp_iterate hS (f := fun v => Y v * Y (S^[b - a] v)) (hY.integrable_mul (hYk _)).aestronglyMeasurable a
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    show _ = Y (S^[a] v) * Y (S^[b - a] (S^[a] v))
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab]
  obtain ⟨C, hC⟩ : ∃ C, C = ∫ v, Y v * Y v ∂P := ⟨_, rfl⟩
  have hdiag : ∀ a : ℕ, ∫ v, Y (S^[a] v) * Y (S^[a] v) ∂P = C := by
    intro a
    rw [hC]
    exact integral_comp_iterate hS (f := fun v => Y v * Y v) (hY.integrable_mul hY).aestronglyMeasurable a
  have hbound : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, 0 < N → (N : ℝ) * (I - ε) ≤ C := by
    intro ε hε N hN
    obtain ⟨k₀, hk₀⟩ := hcor ε hε
    obtain ⟨g, hgdef⟩ : ∃ g, g = k₀ + 1 := ⟨_, rfl⟩
    have hoff : ∀ a b : ℕ, a ≠ b → ∫ v, Y (S^[a * g] v) * Y (S^[b * g] v) ∂P ≤ ε := by
      have hlt : ∀ a b : ℕ, a < b → ∫ v, Y (S^[a * g] v) * Y (S^[b * g] v) ∂P ≤ ε := by
        intro a b hab
        have hle : a * g ≤ b * g := Nat.mul_le_mul_right _ hab.le
        rw [hgap _ _ hle]
        refine (le_abs_self _).trans (hk₀ _ ?_)
        have : (a + 1) * g ≤ b * g := Nat.mul_le_mul_right _ hab
        rw [add_mul, one_mul] at this
        omega
      intro a b hab
      rcases lt_or_gt_of_ne hab with h | h
      · exact hlt a b h
      · have := hlt b a h
        refine le_of_eq_of_le (integral_congr_ae (Eventually.of_forall fun v => mul_comm _ _)) this
    have hW : ∀ a : ℕ, MemLp (fun v => Y (S^[a * g] v) - Z v) 2 P := fun a => (hYk _).sub hZ2
    have hpair : ∀ a b : ℕ, ∫ v, (Y (S^[a * g] v) - Z v) * (Y (S^[b * g] v) - Z v) ∂P =
        (∫ v, Y (S^[a * g] v) * Y (S^[b * g] v) ∂P) - I := by
      intro a b
      have e : (fun v => (Y (S^[a * g] v) - Z v) * (Y (S^[b * g] v) - Z v)) =
          fun v => Y (S^[a * g] v) * Y (S^[b * g] v) - Y (S^[a * g] v) * Z v - Y (S^[b * g] v) * Z v + Z v * Z v := by
        funext v
        ring
      have hYY : Integrable (fun v => Y (S^[a * g] v) * Y (S^[b * g] v)) P := (hYk _).integrable_mul (hYk _)
      have hYZ : ∀ c : ℕ, Integrable (fun v => Y (S^[c] v) * Z v) P := fun c => (hYk c).integrable_mul hZ2
      have hZZ : Integrable (fun v => Z v * Z v) P := hZ2.integrable_mul hZ2
      rw [e, integral_sub_sub_add _ _ _ _ hYY (hYZ _) (hYZ _) hZZ, hZYk, hZYk, ← hI]
      ring
    have hsq : 0 ≤ ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ((∫ v, Y (S^[a * g] v) * Y (S^[b * g] v) ∂P) - I) := by
      have h0 : 0 ≤ ∫ v, (∑ a ∈ Finset.range N, (Y (S^[a * g] v) - Z v)) * (∑ b ∈ Finset.range N, (Y (S^[b * g] v) - Z v)) ∂P :=
        integral_nonneg fun v => mul_self_nonneg _
      refine h0.trans (le_of_eq ?_)
      have hWW : ∀ a b : ℕ, Integrable (fun v => (Y (S^[a * g] v) - Z v) * (Y (S^[b * g] v) - Z v)) P :=
        fun a b => (hW a).integrable_mul (hW b)
      simp only [Finset.sum_mul_sum]
      rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hWW a b]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ fun b _ => hWW a b]
      exact Finset.sum_congr rfl fun b _ => hpair a b
    have hterm : ∀ a ∈ Finset.range N, ∀ b ∈ Finset.range N,
        (∫ v, Y (S^[a * g] v) * Y (S^[b * g] v) ∂P) - I ≤ (ε - I) + if a = b then C else 0 := by
      intro a _ b _
      have hCnn : 0 ≤ C := hC ▸ integral_nonneg fun v => mul_self_nonneg _
      by_cases hab : a = b
      · subst hab
        rw [hdiag, if_pos rfl]
        linarith
      · rw [if_neg hab]
        linarith [hoff a b hab]
    have hsum : ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ((∫ v, Y (S^[a * g] v) * Y (S^[b * g] v) ∂P) - I) ≤
        (N : ℝ) * ((N : ℝ) * (ε - I)) + (N : ℝ) * C := by
      refine (Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb).trans (le_of_eq ?_)
      have hin : ∀ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ((ε - I) + if a = b then C else 0) = (N : ℝ) * (ε - I) + C := by
        intro a ha
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_ite_eq, if_pos ha]
      rw [Finset.sum_congr rfl hin, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : 0 ≤ (N : ℝ) * ((N : ℝ) * (ε - I) + C) := by
      have := hsq.trans hsum
      linarith
    have h2 : 0 ≤ (N : ℝ) * (ε - I) + C := nonneg_of_mul_nonneg_right h1 hNpos
    linarith
  have hInn : 0 ≤ I := hI ▸ integral_nonneg fun v => mul_self_nonneg _
  have hI0 : I = 0 := by
    by_contra hne
    have hpos : 0 < I := lt_of_le_of_ne hInn (Ne.symm hne)
    obtain ⟨n, hn⟩ := exists_nat_gt (C / (I / 2))
    have h1 := hbound (I / 2) (by positivity) (n + 1) (Nat.succ_pos n)
    rw [div_lt_iff₀ (by positivity)] at hn
    push_cast at h1
    nlinarith
  have hae : (fun v => Z v * Z v) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun v => mul_self_nonneg _) (hZ2.integrable_mul hZ2)).1 (hI ▸ hI0)
  filter_upwards [hae] with v hv
  simpa using hv
end Ergodic
section Spaces
variable {T : TranslatedLaws}
private theorem mul_four_le_sum_pow_four (x y z w : ℝ) : x * y * z * w ≤ x ^ 4 + y ^ 4 + z ^ 4 + w ^ 4 := by
  nlinarith [sq_nonneg (x * y - z * w), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (z ^ 2 - w ^ 2), sq_nonneg (x * y), sq_nonneg (z * w)]
private theorem integrable_mul_four_of_integrable_abs_pow_four {α : Type} [MeasurableSpace α] {μ : Measure α} {a b c d : α → ℝ}
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ) (hc : AEStronglyMeasurable c μ) (hd : AEStronglyMeasurable d μ)
    (ha4 : Integrable (fun ω => |a ω| ^ 4) μ) (hb4 : Integrable (fun ω => |b ω| ^ 4) μ)
    (hc4 : Integrable (fun ω => |c ω| ^ 4) μ) (hd4 : Integrable (fun ω => |d ω| ^ 4) μ) :
    Integrable (fun ω => a ω * b ω * c ω * d ω) μ := by
  refine Integrable.mono' (((ha4.add hb4).add hc4).add hd4) (((ha.mul hb).mul hc).mul hd) (Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_mul, Pi.add_apply]
  exact mul_four_le_sum_pow_four _ _ _ _
private theorem aemeasurable_translate (hT : T.IsPreserving) {Y : T.Family} (hY : TranslatedLaws.HasBoundedMoments Y) (k i : ℕ) :
    AEMeasurable (TranslatedLaws.translate Y k i) (T.μ i) :=
  (hY.aemeasurable i).comp_quasiMeasurePreserving ((hT.measurePreserving i).iterate k).quasiMeasurePreserving
private theorem integrable_abs_translate_pow_four (hT : T.IsPreserving) {Y : T.Family} (hY : TranslatedLaws.HasBoundedMoments Y) (k i : ℕ) :
    Integrable (fun ω => |TranslatedLaws.translate Y k i ω| ^ 4) (T.μ i) := by
  have hb : Integrable (fun ω => |Y i ω| ^ 4) (T.μ i) := by
    obtain ⟨C, hC⟩ := hY.moment_bound 4
    refine ⟨((continuous_abs.measurable.comp_aemeasurable (hY.aemeasurable i)).pow_const 4).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => show (0 : ℝ) ≤ |Y i ω| ^ 4 by positivity)]
    exact (hC i).trans_lt ENNReal.ofReal_lt_top
  exact ((hT.measurePreserving i).iterate k).integrable_comp_of_integrable hb
end Spaces
section Residual
variable {J : Type}
private theorem translateShift_iterate_apply (k : ℕ) (v : TranslateValues J) (j : J) (n : ℕ) :
    ((translateShift (J := J))^[k] v) (j, n) = v (j, n + k) := by apply _root_.YangMills.SharedProofs.p49195 <;> assumption
private def weightedResidual (jR jX jE : J) (v : TranslateValues J) : ℝ := v (jR, 0) * (v (jX, 0) - v (jE, 0))
private theorem measurable_weightedResidual (jR jX jE : J) : Measurable (weightedResidual jR jX jE) :=
  (measurable_pi_apply _).mul ((measurable_pi_apply _).sub (measurable_pi_apply _))
end Residual
theorem decorrelatedTranslatesMean_of_jointLimitProperties (hM : jointLimitPropertiesStatement) :
    decorrelatedTranslatesMeanStatement := by
  intro T J _ X P hT hX hP jR jX jE hdec
  have := hP.isProbability
  obtain ⟨hS, hmono, -⟩ := hM T J X P hT hX hP
  have m4 : ∀ p q r s : J × ℕ, Integrable (fun v : TranslateValues J => v p * v q * v r * v s) P ∧
      Tendsto (fun i => ∫ ω, TranslatedLaws.translate (X p.1) p.2 i ω * TranslatedLaws.translate (X q.1) q.2 i ω *
        TranslatedLaws.translate (X r.1) r.2 i ω * TranslatedLaws.translate (X s.1) s.2 i ω ∂(T.μ i)) atTop
        (𝓝 (∫ v : TranslateValues J, v p * v q * v r * v s ∂P)) := by
    intro p q r s
    simpa [Fin.prod_univ_four] using hmono 4 ![p, q, r, s]
  have m2 : ∀ p q : J × ℕ, Integrable (fun v : TranslateValues J => v p * v q) P := by
    intro p q
    simpa [Fin.prod_univ_two] using (hmono 2 ![p, q]).1
  have s4 : ∀ (p q r s : J × ℕ) (i : ℕ), Integrable (fun ω => TranslatedLaws.translate (X p.1) p.2 i ω * TranslatedLaws.translate (X q.1) q.2 i ω *
      TranslatedLaws.translate (X r.1) r.2 i ω * TranslatedLaws.translate (X s.1) s.2 i ω) (T.μ i) := fun p q r s i =>
    integrable_mul_four_of_integrable_abs_pow_four (aemeasurable_translate hT (hX _) _ _).aestronglyMeasurable (aemeasurable_translate hT (hX _) _ _).aestronglyMeasurable
      (aemeasurable_translate hT (hX _) _ _).aestronglyMeasurable (aemeasurable_translate hT (hX _) _ _).aestronglyMeasurable
      (integrable_abs_translate_pow_four hT (hX _) _ _) (integrable_abs_translate_pow_four hT (hX _) _ _) (integrable_abs_translate_pow_four hT (hX _) _ _) (integrable_abs_translate_pow_four hT (hX _) _ _)
  have hY2 : MemLp (weightedResidual jR jX jE) 2 P := by
    refine (memLp_two_iff_integrable_sq (measurable_weightedResidual jR jX jE).aestronglyMeasurable).2 ?_
    have h := ((m4 (jR, 0) (jR, 0) (jX, 0) (jX, 0)).1.sub ((m4 (jR, 0) (jR, 0) (jX, 0) (jE, 0)).1.const_mul 2)).add
      (m4 (jR, 0) (jR, 0) (jE, 0) (jE, 0)).1
    refine h.congr (Eventually.of_forall fun v => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, weightedResidual]
    ring
  have hcor : ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      |∫ v, weightedResidual jR jX jE v * weightedResidual jR jX jE ((translateShift (J := J))^[k] v) ∂P| ≤ ε := by
    intro ε hε
    obtain ⟨k₀, hk⟩ := hdec ε hε
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨i₀, hi⟩ := hk k hk'
    have e1 : ∫ v, weightedResidual jR jX jE v * weightedResidual jR jX jE ((translateShift (J := J))^[k] v) ∂P =
        (∫ v : TranslateValues J, v (jR, 0) * v (jX, 0) * v (jR, k) * v (jX, k) ∂P) - (∫ v : TranslateValues J, v (jR, 0) * v (jX, 0) * v (jR, k) * v (jE, k) ∂P) - (∫ v : TranslateValues J, v (jR, 0) * v (jE, 0) * v (jR, k) * v (jX, k) ∂P) + (∫ v : TranslateValues J, v (jR, 0) * v (jE, 0) * v (jR, k) * v (jE, k) ∂P) := by
      refine Eq.trans (integral_congr_ae (Eventually.of_forall fun v => ?_))
        (integral_sub_sub_add _ _ _ _ (m4 ((jR, 0)) ((jX, 0)) ((jR, k)) ((jX, k))).1 (m4 ((jR, 0)) ((jX, 0)) ((jR, k)) ((jE, k))).1 (m4 ((jR, 0)) ((jE, 0)) ((jR, k)) ((jX, k))).1 (m4 ((jR, 0)) ((jE, 0)) ((jR, k)) ((jE, k))).1)
      simp only [weightedResidual, translateShift_iterate_apply, zero_add]
      ring
    have hlim := (((m4 ((jR, 0)) ((jX, 0)) ((jR, k)) ((jX, k))).2.sub (m4 ((jR, 0)) ((jX, 0)) ((jR, k)) ((jE, k))).2).sub (m4 ((jR, 0)) ((jE, 0)) ((jR, k)) ((jX, k))).2).add (m4 ((jR, 0)) ((jE, 0)) ((jR, k)) ((jE, k))).2
    rw [e1]
    refine le_of_tendsto hlim.abs (eventually_atTop.2 ⟨i₀, fun i hii => ?_⟩)
    refine le_of_eq_of_le (congrArg abs (Eq.symm (Eq.trans (integral_congr_ae (Eventually.of_forall fun ω => ?_))
      (integral_sub_sub_add _ _ _ _ (s4 ((jR, 0)) ((jX, 0)) ((jR, k)) ((jX, k)) i) (s4 ((jR, 0)) ((jX, 0)) ((jR, k)) ((jE, k)) i) (s4 ((jR, 0)) ((jE, 0)) ((jR, k)) ((jX, k)) i) (s4 ((jR, 0)) ((jE, 0)) ((jR, k)) ((jE, k)) i))))) (hi i hii)
    have hz : ∀ Y : T.Family, TranslatedLaws.translate Y 0 i ω = Y i ω := fun _ => rfl
    simp only [hz]
    ring
  have hZ : invariantCondExp P (weightedResidual jR jX jE) =ᵐ[P] 0 := condExp_invariantEvents_eq_zero_of_correlation_decay hS hY2 hcor
  have hsub := condExp_sub (m2 (jR, 0) (jX, 0)) (m2 (jR, 0) (jE, 0)) (shiftInvariantSigma J)
  have hEq : (fun v : TranslateValues J => v (jR, 0) * v (jX, 0)) - (fun v : TranslateValues J => v (jR, 0) * v (jE, 0)) = weightedResidual jR jX jE := by
    funext v
    simp only [Pi.sub_apply, weightedResidual]
    ring
  rw [hEq] at hsub
  filter_upwards [hsub, hZ] with v h1 h2
  exact sub_eq_zero.1 (h1.symm.trans h2)
end YangMills.Construction.MomentMethod
end
