import YangMills.Construction.ClusterExpansionOfAStep.ComparisonOfHeldGasesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.Dobrushin
section TotalVariation
variable {X : Type} [MeasurableSpace X]
theorem exists_measurableSet_restrict_le_restrict (ν ν' : Measure X) [IsFiniteMeasure ν]
    [IsFiniteMeasure ν'] :
    ∃ P, MeasurableSet P ∧ ν'.restrict P ≤ ν.restrict P ∧ ν.restrict Pᶜ ≤ ν'.restrict Pᶜ := by
  obtain ⟨P, hP, hpos, hneg⟩ := (ν.toSignedMeasure - ν'.toSignedMeasure).exists_compl_positive_negative
  have hinside : ∀ B, MeasurableSet B → ν'.real (B ∩ P) ≤ ν.real (B ∩ P) := by
    intro B hB
    have h := hpos B hB
    rw [VectorMeasure.restrict_apply _ hP hB, VectorMeasure.restrict_apply _ hP hB] at h
    simp only [VectorMeasure.sub_apply, Measure.toSignedMeasure_apply_measurable (hB.inter hP)] at h
    simpa using h
  have houtside : ∀ B, MeasurableSet B → ν.real (B ∩ Pᶜ) ≤ ν'.real (B ∩ Pᶜ) := by
    intro B hB
    have h := hneg B hB
    rw [VectorMeasure.restrict_apply _ hP.compl hB, VectorMeasure.restrict_apply _ hP.compl hB] at h
    simp only [VectorMeasure.sub_apply,
      Measure.toSignedMeasure_apply_measurable (hB.inter hP.compl)] at h
    simpa using h
  refine ⟨P, hP, ?_, ?_⟩
  · refine Measure.le_iff.mpr fun B hB => ?_
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB]
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp (hinside B hB)
  · refine Measure.le_iff.mpr fun B hB => ?_
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB]
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp (houtside B hB)
theorem integrable_of_abs_le (m : Measure X) [IsFiniteMeasure m] {f : X → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ s, |f s| ≤ C) : Integrable f m :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
theorem abs_integral_sub_integral_le (ν ν' : Measure X) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] {f f' : X → ℝ}
    (hf : Measurable f) (hf' : Measurable f') {C : ℝ} (hC : ∀ s, |f s| ≤ C) (hC' : ∀ s, |f' s| ≤ C)
    {u t e : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (s₀ : X) {E E' : Set X} (hνE : ∀ᵐ s ∂ν, s ∈ E)
    (hνE' : ∀ᵐ s ∂ν', s ∈ E') (h1 : ∀ s ∈ E, |f s - f s₀| ≤ t) (h2 : ∀ s ∈ E', |f' s - f' s₀| ≤ t)
    (h3 : |f s₀ - f' s₀| ≤ u) (h4 : ∀ s ∈ E, s ∈ E' → |f s - f' s| ≤ u)
    (hTV : ∀ B, MeasurableSet B → ν.real B ≤ ν'.real B + e) :
    |∫ s, f s ∂ν - ∫ s, f' s ∂ν'| ≤ u + 2 * e * t := by
  obtain ⟨P, hP, hle1, hle2⟩ := exists_measurableSet_restrict_le_restrict ν ν'
  set a := ν'.restrict P with ha
  set b := ν.restrict Pᶜ with hb
  set α := ν.restrict P - a with hα
  set α' := ν'.restrict Pᶜ - b with hα'
  have dν : ν = α + a + b := by
    rw [hα, Measure.sub_add_cancel_of_le hle1, hb, Measure.restrict_add_restrict_compl hP]
  have dν' : ν' = a + (α' + b) := by
    rw [hα', Measure.sub_add_cancel_of_le hle2, ha, Measure.restrict_add_restrict_compl hP]
  have fa : IsFiniteMeasure a := by rw [ha]; infer_instance
  have fb : IsFiniteMeasure b := by rw [hb]; infer_instance
  have fα : IsFiniteMeasure α := by rw [hα]; infer_instance
  have fα' : IsFiniteMeasure α' := by rw [hα']; infer_instance
  have la : a ≤ ν := hle1.trans Measure.restrict_le_self
  have la' : a ≤ ν' := Measure.restrict_le_self
  have lb : b ≤ ν := Measure.restrict_le_self
  have lb' : b ≤ ν' := hle2.trans Measure.restrict_le_self
  have lα : α ≤ ν := Measure.sub_le.trans Measure.restrict_le_self
  have lα' : α' ≤ ν' := Measure.sub_le.trans Measure.restrict_le_self
  have I (m : Measure X) [IsFiniteMeasure m] : Integrable f m := integrable_of_abs_le m hf hC
  have I' (m : Measure X) [IsFiniteMeasure m] : Integrable f' m := integrable_of_abs_le m hf' hC'
  have e1 : ∫ s, f s ∂ν = ∫ s, f s ∂α + ∫ s, f s ∂a + ∫ s, f s ∂b := by
    conv_lhs => rw [dν]
    rw [integral_add_measure (I _) (I _), integral_add_measure (I _) (I _)]
  have e2 : ∫ s, f' s ∂ν' = ∫ s, f' s ∂a + (∫ s, f' s ∂α' + ∫ s, f' s ∂b) := by
    conv_lhs => rw [dν']
    rw [integral_add_measure (I' _) (I' _), integral_add_measure (I' _) (I' _)]
  have mass1 : α.real Set.univ + a.real Set.univ + b.real Set.univ = 1 := by
    have := congrArg (fun m : Measure X => m.real Set.univ) dν
    simp only [probReal_univ] at this
    rw [this]
    simp [measureReal_add_apply]
  have mass2 : a.real Set.univ + (α'.real Set.univ + b.real Set.univ) = 1 := by
    have := congrArg (fun m : Measure X => m.real Set.univ) dν'
    simp only [probReal_univ] at this
    rw [this]
    simp [measureReal_add_apply]
  have heps : α.real Set.univ ≤ e := by
    have h5 := hTV P hP
    have h6 : ν.real P = α.real Set.univ + a.real Set.univ := by
      have h7 : ν.restrict P = α + a := by rw [hα, Measure.sub_add_cancel_of_le hle1]
      have h8 : ν.real P = (α + a).real Set.univ := by rw [← h7, measureReal_restrict_apply_univ]
      rw [h8]
      simp [measureReal_add_apply]
    have h9 : ν'.real P = a.real Set.univ := by
      rw [ha, measureReal_restrict_apply_univ]
    linarith
  have ae1 : ∀ᵐ s ∂a, s ∈ E ∧ s ∈ E' :=
    (hνE.filter_mono (ae_mono la)).and (hνE'.filter_mono (ae_mono la'))
  have ae2 : ∀ᵐ s ∂b, s ∈ E ∧ s ∈ E' :=
    (hνE.filter_mono (ae_mono lb)).and (hνE'.filter_mono (ae_mono lb'))
  have b1 : |∫ s, (f s - f' s) ∂a| ≤ u * a.real Set.univ := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le_const (ae1.mono fun s hs => ?_)
    exact h4 s hs.1 hs.2
  have b2 : |∫ s, (f s - f' s) ∂b| ≤ u * b.real Set.univ := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le_const (ae2.mono fun s hs => ?_)
    exact h4 s hs.1 hs.2
  have b3 : |∫ s, (f s - f s₀) ∂α| ≤ t * α.real Set.univ := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le_const ((hνE.filter_mono (ae_mono lα)).mono fun s hs => ?_)
    exact h1 s hs
  have b4 : |∫ s, (f' s - f' s₀) ∂α'| ≤ t * α'.real Set.univ := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le_const ((hνE'.filter_mono (ae_mono lα')).mono fun s hs => ?_)
    exact h2 s hs
  have i1 : ∫ s, (f s - f' s) ∂a = ∫ s, f s ∂a - ∫ s, f' s ∂a := integral_sub (I _) (I' _)
  have i2 : ∫ s, (f s - f' s) ∂b = ∫ s, f s ∂b - ∫ s, f' s ∂b := integral_sub (I _) (I' _)
  have i3 : ∫ s, (f s - f s₀) ∂α = ∫ s, f s ∂α - f s₀ * α.real Set.univ := by
    rw [integral_sub (I _) (integrable_const _), integral_const]
    simp [mul_comm]
  have i4 : ∫ s, (f' s - f' s₀) ∂α' = ∫ s, f' s ∂α' - f' s₀ * α'.real Set.univ := by
    rw [integral_sub (I' _) (integrable_const _), integral_const]
    simp [mul_comm]
  have heq : α'.real Set.univ = α.real Set.univ := by linarith
  have hnn : 0 ≤ α.real Set.univ := measureReal_nonneg
  have hD : ∫ s, f s ∂ν - ∫ s, f' s ∂ν' = ∫ s, (f s - f' s) ∂a + ∫ s, (f s - f' s) ∂b +
      ∫ s, (f s - f s₀) ∂α - ∫ s, (f' s - f' s₀) ∂α' + (f s₀ - f' s₀) * α.real Set.univ := by
    rw [e1, e2, i1, i2, i3, i4, heq]
    ring
  rw [hD]
  have hlast : |(f s₀ - f' s₀) * α.real Set.univ| ≤ u * α.real Set.univ := by
    rw [abs_mul, abs_of_nonneg hnn]
    gcongr
  rw [heq] at b4
  have hsum : u * a.real Set.univ + u * b.real Set.univ + t * α.real Set.univ + t * α.real Set.univ +
      u * α.real Set.univ ≤ u + 2 * e * t := by
    have h5 : u * (α.real Set.univ + a.real Set.univ + b.real Set.univ) = u := by rw [mass1, mul_one]
    nlinarith
  refine le_trans ?_ hsum
  rw [abs_le] at b1 b2 b3 b4 hlast ⊢
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, hlast.1, hlast.2]
end TotalVariation
section SingleSite
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
  {A : PairConstraint S}
theorem isAdmissible_update_vacant {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) (i : I) :
    A.IsAdmissible (Function.update σ i (A.vacant i)) := by apply _root_.YangMills.Construction.Dobrushin.VacantSpin.isAdmissible_update_vacant <;> assumption
def ControlsDifference (A : PairConstraint S) (μ μ' : Measure (∀ i, S i)) (a : I → ℝ) : Prop :=
  ∀ (F : (∀ i, S i) → ℝ) (o : I → ℝ), Measurable F → (∃ C, ∀ σ, |F σ| ≤ C) →
    A.OscillationBound F o → |∫ σ, F σ ∂μ - ∫ σ, F σ ∂μ'| ≤ ∑ i, a i * o i
theorem abs_sub_vacant_le_sum {F : (∀ i, S i) → ℝ} {o : I → ℝ} (ho : A.OscillationBound F o)
    {σ : ∀ i, S i} (hσ : A.IsAdmissible σ) : |F σ - F A.vacant| ≤ ∑ i, o i := by
  have key : ∀ T : Finset I, A.IsAdmissible (fun i => if i ∈ T then A.vacant i else σ i) ∧
      |F σ - F (fun i => if i ∈ T then A.vacant i else σ i)| ≤ ∑ i ∈ T, o i := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using hσ
    | insert i T hi ih =>
      have hu : (fun k => if k ∈ insert i T then A.vacant k else σ k) =
          Function.update (fun k => if k ∈ T then A.vacant k else σ k) i (A.vacant i) := by
        funext k
        by_cases hk : k = i
        · subst hk
          simp
        · simp [hk, Function.update_of_ne hk]
      have h1 := isAdmissible_update_vacant ih.1 i
      rw [hu]
      refine ⟨h1, ?_⟩
      rw [Finset.sum_insert hi]
      have h2 := ho.2 i _ _ ih.1 h1 fun j hj => by rw [Function.update_of_ne hj]
      have h3 := abs_sub_le (F σ) (F fun k => if k ∈ T then A.vacant k else σ k)
        (F (Function.update (fun k => if k ∈ T then A.vacant k else σ k) i (A.vacant i)))
      linarith [ih.2]
  have := (key Finset.univ).2
  simpa using this
theorem controlsDifference_two {μ μ' : Measure (∀ i, S i)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ']
    (ha : ∀ᵐ σ ∂μ, A.IsAdmissible σ) (ha' : ∀ᵐ σ ∂μ', A.IsAdmissible σ) :
    ControlsDifference A μ μ' fun _ => 2 := by
  intro F o hF ⟨C, hC⟩ ho
  have hint : ∀ (m : Measure (∀ i, S i)) [IsProbabilityMeasure m], (∀ᵐ σ ∂m, A.IsAdmissible σ) →
      |∫ σ, F σ ∂m - F A.vacant| ≤ ∑ i, o i := by
    intro m _ hm
    have h1 : ∫ σ, F σ ∂m - F A.vacant = ∫ σ, (F σ - F A.vacant) ∂m := by
      rw [integral_sub (integrable_of_abs_le m hF hC) (integrable_const _)]
      simp
    rw [h1, ← Real.norm_eq_abs]
    have h2 := norm_integral_le_of_norm_le_const (μ := m) (f := fun σ => F σ - F A.vacant)
      (C := ∑ i, o i) (hm.mono fun σ hσ => abs_sub_vacant_le_sum ho hσ)
    simpa using h2
  have h1 := hint μ ha
  have h2 := hint μ' ha'
  rw [← Finset.mul_sum]
  have := abs_sub_le (∫ σ, F σ ∂μ) (F A.vacant) (∫ σ, F σ ∂μ')
  rw [abs_sub_comm (F A.vacant)] at this
  linarith
def condMean (K : ∀ i, Kernel (∀ j, S j) (S i)) (i : I) (F : (∀ j, S j) → ℝ) (σ : ∀ j, S j) : ℝ :=
  ∫ s, F (Function.update σ i s) ∂(K i σ)
theorem measurable_condMean {K : ∀ i, Kernel (∀ j, S j) (S i)} (hK : ∀ i, IsMarkovKernel (K i))
    (i : I) {F : (∀ j, S j) → ℝ} (hF : Measurable F) : Measurable (condMean K i F) := by
  have := hK i
  have hm : Measurable fun p : (∀ j, S j) × S i => F (Function.update p.1 i p.2) :=
    hF.comp measurable_update'
  exact hm.stronglyMeasurable.integral_kernel_prod_right'.measurable
theorem abs_condMean_le {K : ∀ i, Kernel (∀ j, S j) (S i)} (hK : ∀ i, IsMarkovKernel (K i))
    (i : I) {F : (∀ j, S j) → ℝ} {C : ℝ} (hC : ∀ σ, |F σ| ≤ C) (σ : ∀ j, S j) :
    |condMean K i F σ| ≤ C := by
  have := hK i
  have h := norm_integral_le_of_norm_le_const (μ := K i σ) (f := fun s => F (Function.update σ i s))
    (C := C) (Filter.Eventually.of_forall fun s => hC _)
  unfold condMean
  simpa using h
theorem oscillationBound_condMean {K : ∀ i, Kernel (∀ j, S j) (S i)} {μ : Measure (∀ i, S i)}
    (hG : A.IsSpecification μ K)
    {c : I → I → ℝ} (hc0 : ∀ i j, 0 ≤ c i j)
    (hc : ∀ i j, i ≠ j → ∀ σ σ', A.IsAdmissible σ → A.IsAdmissible σ' →
      (∀ k, k ≠ j → σ k = σ' k) →
      ∀ B, MeasurableSet B → (K i σ).real B ≤ (K i σ').real B + c i j / 2)
    (i : I) {F : (∀ j, S j) → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ σ, |F σ| ≤ C) {o : I → ℝ}
    (ho : A.OscillationBound F o) :
    A.OscillationBound (condMean K i F) fun j => if j = i then 0 else o j + c i j * o i := by
  refine ⟨fun j => ?_, fun j σ σ' hσ hσ' hd => ?_⟩
  · beta_reduce
    split_ifs
    · exact le_rfl
    · exact add_nonneg (ho.1 j) (mul_nonneg (hc0 _ _) (ho.1 i))
  · beta_reduce
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl]
      have hu : ∀ s, Function.update σ j s = Function.update σ' j s := by
        intro s
        funext k
        by_cases hk : k = j
        · subst hk
          simp
        · simp [Function.update_of_ne hk, hd k hk]
      have hK : K j σ = K j σ' := by
        have h1 := hG.update_eq j σ (σ' j)
        have h2 : Function.update σ j (σ' j) = σ' := by
          rw [hu]
          simp
        rw [h2] at h1
        exact h1.symm
      unfold condMean
      simp only [hu, hK, sub_self, abs_zero, le_refl]
    · rw [if_neg hj]
      have := hG.isMarkovKernel i
      have hf : ∀ τ : ∀ j, S j, Measurable fun s => F (Function.update τ i s) := fun τ =>
        hF.comp (measurable_update τ)
      have hsame : ∀ τ τ' : ∀ k, S k, (∀ k, k ≠ j → τ k = τ' k) → ∀ s k, k ≠ j →
          Function.update τ i s k = Function.update τ' i s k := by
        intro τ τ' h s k hk
        by_cases hki : k = i
        · subst hki
          simp
        · simp [Function.update_of_ne hki, h k hk]
      have h0 : ∀ τ : ∀ k, S k, ∀ s, ∀ k, k ≠ i →
          Function.update τ i s k = Function.update τ i (A.vacant i) k := by
        intro τ s k hk
        simp [Function.update_of_ne hk]
      have key := abs_integral_sub_integral_le (K i σ) (K i σ') (hf σ) (hf σ')
        (fun s => hC _) (fun s => hC _)
        (ho.1 j) (ho.1 i) (e := c i j / 2) (A.vacant i)
        (E := {s | A.IsAdmissible (Function.update σ i s)})
        (E' := {s | A.IsAdmissible (Function.update σ' i s)})
        (hG.ae_admissible_update i σ hσ) (hG.ae_admissible_update i σ' hσ')
        (fun s hs => ho.2 i _ _ hs (isAdmissible_update_vacant hσ i) (h0 σ s))
        (fun s hs => ho.2 i _ _ hs (isAdmissible_update_vacant hσ' i) (h0 σ' s))
        (ho.2 j _ _ (isAdmissible_update_vacant hσ i) (isAdmissible_update_vacant hσ' i)
          (hsame σ σ' hd _))
        (fun s hs hs' => ho.2 j _ _ hs hs' (hsame σ σ' hd s))
        (hc i j (Ne.symm hj) σ σ' hσ hσ' hd)
      unfold condMean
      calc _ ≤ o j + 2 * (c i j / 2) * o i := key
        _ = o j + c i j * o i := by ring
end SingleSite
section Comparison
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
  {A : PairConstraint S}
theorem controlsDifference_update {μ μ' : Measure (∀ i, S i)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ']
    {K K' : ∀ i, Kernel (∀ j, S j) (S i)} {c : I → I → ℝ} {b : I → ℝ}
    (hG : A.IsSpecification μ K) (hG' : A.IsSpecification μ' K') (hc0 : ∀ i j, 0 ≤ c i j)
    (hc : ∀ i j, i ≠ j → ∀ σ σ', A.IsAdmissible σ → A.IsAdmissible σ' →
      (∀ k, k ≠ j → σ k = σ' k) →
      ∀ B, MeasurableSet B → (K i σ).real B ≤ (K i σ').real B + c i j / 2)
    (hb : ∀ i σ, A.IsAdmissible σ → ∀ B, MeasurableSet B →
      (K i σ).real B ≤ (K' i σ).real B + b i / 2)
    {a : I → ℝ} (hs : ControlsDifference A μ μ' a) (i : I) :
    ControlsDifference A μ μ'
      (Function.update a i (∑ j ∈ Finset.univ.erase i, c i j * a j + b i)) := by
  intro F o hF ⟨C, hC⟩ ho
  have hosc := oscillationBound_condMean hG hc0 hc i hF hC ho
  have hmeas := measurable_condMean hG.isMarkovKernel i hF
  have hmeas' := measurable_condMean hG'.isMarkovKernel i hF
  have hbd := abs_condMean_le hG.isMarkovKernel i hC
  have hbd' := abs_condMean_le hG'.isMarkovKernel i hC
  have h1 := hG.integral_eq i F hF ⟨C, hC⟩
  have h2 := hG'.integral_eq i F hF ⟨C, hC⟩
  have hfirst := hs (condMean K i F) _ hmeas ⟨C, hbd⟩ hosc
  have hsecond : |∫ σ, condMean K i F σ ∂μ' - ∫ σ, condMean K' i F σ ∂μ'| ≤ b i * o i := by
    rw [← integral_sub (integrable_of_abs_le μ' hmeas hbd) (integrable_of_abs_le μ' hmeas' hbd'),
      ← Real.norm_eq_abs]
    have h3 := norm_integral_le_of_norm_le_const (μ := μ')
      (f := fun σ => condMean K i F σ - condMean K' i F σ)
      (C := b i * o i) (hG'.ae_admissible.mono fun σ hσ => ?_)
    · simpa using h3
    · have := hG.isMarkovKernel i
      have := hG'.isMarkovKernel i
      have hf : Measurable fun s => F (Function.update σ i s) := hF.comp (measurable_update σ)
      have h0 : ∀ s, ∀ k, k ≠ i →
          Function.update σ i s k = Function.update σ i (A.vacant i) k := by
        intro s k hk
        simp [Function.update_of_ne hk]
      have key := abs_integral_sub_integral_le (K i σ) (K' i σ) hf hf (fun s => hC _)
        (fun s => hC _)
        le_rfl (ho.1 i) (e := b i / 2) (A.vacant i)
        (E := {s | A.IsAdmissible (Function.update σ i s)})
        (E' := {s | A.IsAdmissible (Function.update σ i s)})
        (hG.ae_admissible_update i σ hσ) (hG'.ae_admissible_update i σ hσ)
        (fun s hs => ho.2 i _ _ hs (isAdmissible_update_vacant hσ i) (h0 s))
        (fun s hs => ho.2 i _ _ hs (isAdmissible_update_vacant hσ i) (h0 s))
        (by simp) (fun s _ _ => by simp) (hb i σ hσ)
      unfold condMean
      rw [Real.norm_eq_abs]
      calc _ ≤ 0 + 2 * (b i / 2) * o i := key
        _ = b i * o i := by ring
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun j => a j * (if j = i then 0 else o j + c i j * o i)) (Finset.mem_univ i)
  have hsplit2 := Finset.add_sum_erase Finset.univ
    (fun j => Function.update a i (∑ j ∈ Finset.univ.erase i, c i j * a j + b i) j * o j)
    (Finset.mem_univ i)
  have hterm : ∑ j ∈ Finset.univ.erase i, a j * (if j = i then 0 else o j + c i j * o i) =
      ∑ j ∈ Finset.univ.erase i, a j * o j + (∑ j ∈ Finset.univ.erase i, c i j * a j) * o i := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [if_neg (Finset.ne_of_mem_erase hj)]
    ring
  have hterm2 : ∑ j ∈ Finset.univ.erase i,
      Function.update a i (∑ j ∈ Finset.univ.erase i, c i j * a j + b i) j * o j =
      ∑ j ∈ Finset.univ.erase i, a j * o j :=
    Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  simp only [if_true, mul_zero, zero_add, Function.update_self] at hsplit hsplit2
  rw [← hsplit2, hterm2]
  rw [← hsplit, hterm] at hfirst
  rw [h1, h2]
  show |∫ σ, condMean K i F σ ∂μ - ∫ σ, condMean K' i F σ ∂μ'| ≤ _
  have h4 := abs_sub_le (∫ σ, condMean K i F σ ∂μ) (∫ σ, condMean K i F σ ∂μ')
    (∫ σ, condMean K' i F σ ∂μ')
  nlinarith [h4, hfirst, hsecond]
theorem comparisonStatement_holds : ComparisonStatement := by
  intro I _ _ S _ A μ μ' _ _ K K' c b w hAd hG hG' hc0 hb0 hw0 hc hb hcol
  have hclosed : IsClosed {a : I → ℝ | ControlsDifference A μ μ' a} := by
    simp only [ControlsDifference, Set.setOf_forall]
    refine isClosed_iInter fun F => isClosed_iInter fun o => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    exact isClosed_le continuous_const (by fun_prop)
  let 𝒮 : Set (I → ℝ) := Set.Icc 0 (fun _ => 2) ∩ {a | ControlsDifference A μ μ' a}
  have hK : IsCompact 𝒮 := isCompact_Icc.inter_right hclosed
  have hne : 𝒮.Nonempty := ⟨fun _ => 2, ⟨fun _ => by norm_num, le_rfl⟩,
    controlsDifference_two hG.ae_admissible hG'.ae_admissible⟩
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne
    (f := fun a : I → ℝ => ∑ i, w i * a i) (by fun_prop)
  have ha0 : ∀ i, 0 ≤ a i := fun i => ha.1.1 i
  have hle : ∀ i, a i ≤ ∑ j ∈ Finset.univ.erase i, c i j * a j + b i := by
    intro i
    by_contra hcon
    push_neg at hcon
    set v := ∑ j ∈ Finset.univ.erase i, c i j * a j + b i with hv
    have hv0 : 0 ≤ v := add_nonneg
      (Finset.sum_nonneg fun j _ => mul_nonneg (hc0 _ _) (ha0 j)) (hb0 i)
    have hmem : Function.update a i v ∈ 𝒮 := by
      refine ⟨⟨fun k => ?_, fun k => ?_⟩, controlsDifference_update hG hG' hc0 hc hb ha.2 i⟩
      · by_cases hk : k = i
        · subst hk
          simpa using hv0
        · simpa [Function.update_of_ne hk] using ha0 k
      · by_cases hk : k = i
        · subst hk
          simp only [Function.update_self]
          exact hcon.le.trans (ha.1.2 k)
        · simpa [Function.update_of_ne hk] using ha.1.2 k
    have h1 : ∑ k, w k * a k ≤ ∑ k, w k * Function.update a i v k := hmin hmem
    have h2 := Finset.add_sum_erase Finset.univ (fun k => w k * a k) (Finset.mem_univ i)
    have h3 := Finset.add_sum_erase Finset.univ
      (fun k => w k * Function.update a i v k) (Finset.mem_univ i)
    have h4 : ∑ k ∈ Finset.univ.erase i, w k * Function.update a i v k =
        ∑ k ∈ Finset.univ.erase i, w k * a k :=
      Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    simp only [Function.update_self] at h3
    have h5 := mul_lt_mul_of_pos_left hcon (hw0 i)
    linarith
  refine ⟨a, ha0, ?_, fun F o hF hbd ho => ha.2 F o hF hbd ho⟩
  have h1 : ∑ i, w i * a i ≤ ∑ i, w i * (∑ j, c i j * a j) + ∑ i, w i * b i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have h2 : ∑ j ∈ Finset.univ.erase i, c i j * a j ≤ ∑ j, c i j * a j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ =>
        mul_nonneg (hc0 _ _) (ha0 j)
    have h3 := hle i
    have h4 := hw0 i
    nlinarith
  have h2 : ∑ i, w i * (∑ j, c i j * a j) ≤ (∑ j, w j * a j) / 2 := by
    calc ∑ i, w i * (∑ j, c i j * a j) = ∑ j, (∑ i, w i * c i j) * a j := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ j, w j / 2 * a j := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hcol j) (ha0 j)
      _ = (∑ j, w j * a j) / 2 := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun j _ => by ring
  linarith
end Comparison
end YangMills.Construction.Dobrushin
end
