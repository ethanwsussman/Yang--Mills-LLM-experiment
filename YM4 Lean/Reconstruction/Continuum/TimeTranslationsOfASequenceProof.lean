import YangMills.Construction.Continuum.DistributionsOffTheDiagonalsAndTranslationsInSpaceProof
import YangMills.Construction.Continuum.ClusteringFromTuplesToSchwartzFunctionsProof
import YangMills.Construction.Continuum.CoefficientsOfAFunctionOfASystemDecayProof
import YangMills.Construction.Continuum.RulesOfThePartialDerivatives
import Reconstruction.Continuum.TwoApproximationsAtOrderedTimes
import Reconstruction.MinkowskiSpace.OperatorOfAFormOnTheSubspaceAtOrderedPositiveTimesProof
import Reconstruction.MinkowskiSpace.TimeTranslationOfTheVectorsOfSmoothSequencesProof
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace ConfigSpace.TimeShiftProof
theorem le_of_sq_le_mul_succ {a : ℕ → ℝ} {A b : ℝ} {K : ℕ} (hA : 0 ≤ A)
    (h1 : ∀ j, a j ^ 2 ≤ A * a (j + 1)) (h2 : ∀ j, a j ^ 2 ≤ b * ((2 : ℝ) ^ j) ^ K) :
    a 0 ≤ A := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  have hApos : 0 < A := by
    rcases hA.eq_or_lt with h | h
    · exfalso
      have h0 := h1 0
      rw [← h, zero_mul] at h0
      have h3 : 0 < a 0 := by linarith
      nlinarith [sq_pos_of_pos h3]
    · exact h
  have hr : 1 < a 0 / A := (one_lt_div hApos).2 hlt
  set r := a 0 / A with hrdef
  have hlow : ∀ j, A * r ^ (2 ^ j) ≤ a j := by
    intro j
    induction j with
    | zero =>
      have : A * r = a 0 := by rw [hrdef]; field_simp
      simpa using this.le
    | succ j ih =>
      have h := h1 j
      have h0 : 0 ≤ A * r ^ (2 ^ j) := by positivity
      have h3 : (A * r ^ (2 ^ j)) ^ 2 ≤ a j ^ 2 := pow_le_pow_left₀ h0 ih 2
      have e : (A * r ^ (2 ^ j)) ^ 2 = A * (A * r ^ (2 ^ (j + 1))) := by
        rw [pow_succ 2 j, pow_mul]
        ring
      rw [e] at h3
      exact le_of_mul_le_mul_left (h3.trans h) hApos
  have hb : ∀ j, A ^ 2 * r ^ (2 ^ (j + 1)) ≤ b * ((2 : ℝ) ^ j) ^ K := by
    intro j
    have h0 : 0 ≤ A * r ^ (2 ^ j) := by positivity
    have h3 : (A * r ^ (2 ^ j)) ^ 2 ≤ a j ^ 2 := pow_le_pow_left₀ h0 (hlow j) 2
    have e : (A * r ^ (2 ^ j)) ^ 2 = A ^ 2 * r ^ (2 ^ (j + 1)) := by
      rw [pow_succ 2 j, pow_mul]
      ring
    rw [e] at h3
    exact h3.trans (h2 j)
  have hbpos : 0 < b := by
    have h0 := hb 0
    have h3 : 0 < A ^ 2 * r ^ (2 ^ (0 + 1)) := by positivity
    have h4 := h3.trans_le h0
    simpa using h4
  have ht : Tendsto (fun j : ℕ => (((2 ^ (j + 1) : ℕ) : ℝ)) ^ K / r ^ (2 ^ (j + 1))) atTop (𝓝 0) := by
    have h3 := tendsto_pow_const_div_const_pow_of_one_lt K hr
    have h4 : Tendsto (fun j : ℕ => 2 ^ (j + 1)) atTop atTop :=
      tendsto_atTop_mono (fun j => (Nat.lt_two_pow_self (n := j + 1)).le) (tendsto_add_atTop_nat 1)
    exact h3.comp h4
  have hc : 0 < A ^ 2 / b := by positivity
  obtain ⟨j, hj⟩ := (ht.eventually (gt_mem_nhds hc)).exists
  have h5 := hb j
  have hrp : 0 < r ^ (2 ^ (j + 1)) := by positivity
  have h6 : ((2 : ℝ) ^ j) ^ K ≤ (((2 ^ (j + 1) : ℕ) : ℝ)) ^ K := by
    refine pow_le_pow_left₀ (by positivity) ?_ K
    push_cast
    rw [pow_succ]
    have : (0 : ℝ) < 2 ^ j := by positivity
    linarith
  have h7 : A ^ 2 * r ^ (2 ^ (j + 1)) ≤ b * (((2 ^ (j + 1) : ℕ) : ℝ)) ^ K :=
    h5.trans (mul_le_mul_of_nonneg_left h6 hbpos.le)
  rw [div_lt_div_iff₀ hrp hbpos] at hj
  nlinarith
section Abstract
variable {V H : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {cl : V →ₗ[ℂ] H} {τ : ℝ≥0 → V →ₗ[ℂ] V} {B : ℝ≥0 → H →L[ℂ] H}
theorem mul_eq_of_dense (hd : DenseRange cl) (hB : ∀ t x, B t (cl x) = cl (τ t x))
    (hτ : ∀ s t x, τ s (τ t x) = τ (s + t) x) (s t : ℝ≥0) : B s * B t = B (s + t) := by
  refine ContinuousLinearMap.coeFn_injective (hd.equalizer (B s * B t).continuous
    (B (s + t)).continuous (funext fun x => ?_))
  show B s (B t (cl x)) = B (s + t) (cl x)
  simp only [hB, hτ]
theorem eq_id_of_dense (hd : DenseRange cl) (hB : ∀ t x, B t (cl x) = cl (τ t x))
    (hτ : ∀ x, τ 0 x = x) : B 0 = ContinuousLinearMap.id ℂ H := by
  refine ContinuousLinearMap.coeFn_injective (hd.equalizer (B 0).continuous
    (ContinuousLinearMap.id ℂ H).continuous (funext fun x => ?_))
  simp only [Function.comp, ContinuousLinearMap.id_apply, hB, hτ]
theorem inner_symm_of_dense (hd : DenseRange cl) (hB : ∀ t x, B t (cl x) = cl (τ t x))
    (t : ℝ≥0) (hs : ∀ x y, ⟪cl x, cl (τ t y)⟫_ℂ = ⟪cl (τ t x), cl y⟫_ℂ) (φ ψ : H) :
    ⟪φ, B t ψ⟫_ℂ = ⟪B t φ, ψ⟫_ℂ := by
  refine hd.induction_on₂ (p := fun φ ψ => ⟪φ, B t ψ⟫_ℂ = ⟪B t φ, ψ⟫_ℂ) ?_ ?_ φ ψ
  · exact isClosed_eq (continuous_fst.inner ((B t).continuous.comp continuous_snd))
      (((B t).continuous.comp continuous_fst).inner continuous_snd)
  · intro x y
    simp only [hB]
    exact hs x y
theorem tendsto_nhds_zero_of_dense (hd : DenseRange cl) (hB : ∀ t x, B t (cl x) = cl (τ t x))
    (hn : ∀ t, ‖B t‖ ≤ 1) (h0 : ∀ x, Tendsto (fun t => cl (τ t x)) (𝓝 0) (𝓝 (cl x))) (χ : H) :
    Tendsto (fun t => B t χ) (𝓝 0) (𝓝 χ) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x, hx⟩ := DenseRange.exists_dist_lt hd χ (ε := ε / 3) (by positivity)
  have hx' : ‖χ - cl x‖ < ε / 3 := by simpa [dist_eq_norm] using hx
  filter_upwards [(Metric.tendsto_nhds.1 (h0 x)) (ε / 3) (by positivity)] with t ht
  rw [dist_eq_norm] at ht ⊢
  have e : B t χ - χ = B t (χ - cl x) + (cl (τ t x) - cl x) - (χ - cl x) := by
    rw [map_sub, hB]
    abel
  have hb : ‖B t (χ - cl x)‖ ≤ ‖χ - cl x‖ := by
    refine ((B t).le_opNorm _).trans ?_
    have := mul_le_mul_of_nonneg_right (hn t) (norm_nonneg (χ - cl x))
    simpa using this
  rw [e]
  refine (norm_sub_le _ _).trans_lt ?_
  have := norm_add_le (B t (χ - cl x)) (cl (τ t x) - cl x)
  linarith
theorem continuous_of_dense (hd : DenseRange cl) (hB : ∀ t x, B t (cl x) = cl (τ t x))
    (hn : ∀ t, ‖B t‖ ≤ 1) (hτ : ∀ s t x, τ s (τ t x) = τ (s + t) x)
    (hτ0 : ∀ x, τ 0 x = x)
    (h0 : ∀ x, Tendsto (fun t => cl (τ t x)) (𝓝 0) (𝓝 (cl x))) (χ : H) :
    Continuous fun t => B t χ := by
  have hz := tendsto_nhds_zero_of_dense hd hB hn h0
  have hone := eq_id_of_dense hd hB hτ0
  have hsg := mul_eq_of_dense hd hB hτ
  have hc : ∀ (s u : ℝ≥0), ‖B (s + u) χ - B s χ‖ ≤ ‖B u χ - χ‖ := fun s u => by
    have e : B (s + u) χ - B s χ = B s (B u χ - χ) := by
      rw [← hsg, map_sub]
      rfl
    rw [e]
    refine ((B s).le_opNorm _).trans ?_
    have := mul_le_mul_of_nonneg_right (hn s) (norm_nonneg (B u χ - χ))
    simpa using this
  rw [continuous_iff_continuousAt]
  intro t₀
  have hg : Tendsto (fun t : ℝ≥0 => ‖B (t - t₀) χ - χ‖ + ‖B (t₀ - t) χ - χ‖) (𝓝 t₀) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ≥0 => t - t₀) (𝓝 t₀) (𝓝 0) := by
      have : Continuous fun t : ℝ≥0 => t - t₀ := by fun_prop
      simpa using this.tendsto t₀
    have h2 : Tendsto (fun t : ℝ≥0 => t₀ - t) (𝓝 t₀) (𝓝 0) := by
      have : Continuous fun t : ℝ≥0 => t₀ - t := by fun_prop
      simpa using this.tendsto t₀
    have h3 : Tendsto (fun t => ‖B t χ - χ‖) (𝓝 (0 : ℝ≥0)) (𝓝 0) := by
      simpa using (tendsto_iff_norm_sub_tendsto_zero.1 (hz χ))
    simpa using (h3.comp h1).add (h3.comp h2)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_) hg)
  rcases le_total t₀ t with h | h
  · have e1 : t = t₀ + (t - t₀) := (add_tsub_cancel_of_le h).symm
    have e2 : t₀ - t = 0 := tsub_eq_zero_of_le h
    have h3 := hc t₀ (t - t₀)
    rw [← e1] at h3
    rw [e2, hone]
    simpa using h3
  · have e1 : t₀ = t + (t₀ - t) := (add_tsub_cancel_of_le h).symm
    have e2 : t - t₀ = 0 := tsub_eq_zero_of_le h
    have h3 := hc t (t₀ - t)
    rw [← e1] at h3
    rw [e2, hone, norm_sub_rev]
    simpa using h3
end Abstract
end ConfigSpace.TimeShiftProof
namespace TestSpaces.ShiftEstimates
variable {n : ℕ}
def shiftBy (w : Fin 4 → ℝ) (g : PointTuple n → ℂ) : PointTuple n → ℂ := fun x => g fun i => x i - w
theorem coordDeriv_shiftBy (w : Fin 4 → ℝ) (i : Fin n) (μ : Fin 4) (g : PointTuple n → ℂ) :
    coordDeriv i μ (shiftBy w g) = shiftBy w (coordDeriv i μ g) := by
  funext x
  simp only [coordDeriv, shiftBy, lineDeriv]
  congr 1
  funext t
  congr 1
  funext j
  simp only [Pi.add_apply, Pi.smul_apply]
  abel
theorem multiDeriv_shiftBy (w : Fin 4 → ℝ) (α : MultiIdx4 n) (g : PointTuple n → ℂ) :
    multiDeriv α (shiftBy w g) = shiftBy w (multiDeriv α g) := by
  have hit : ∀ (i : Fin n) (μ : Fin 4) (m : ℕ) (h : PointTuple n → ℂ),
      (coordDeriv i μ)^[m] (shiftBy w h) =
        shiftBy w ((coordDeriv i μ)^[m] h) := fun i μ m h => by
    have hc : Function.Commute (coordDeriv (F := ℂ) i μ) (shiftBy w) :=
      fun h => coordDeriv_shiftBy w i μ h
    exact (hc.iterate_left m) h
  have inner : ∀ (i : Fin n) (l : List (Fin 4)) (h : PointTuple n → ℂ),
      l.foldr (fun μ h' => (coordDeriv i μ)^[α i μ] h') (shiftBy w h) =
        shiftBy w (l.foldr (fun μ h' => (coordDeriv i μ)^[α i μ] h') h) := by
    intro i l h
    induction l with
    | nil => rfl
    | cons μ l ih => rw [List.foldr_cons, List.foldr_cons, ih, hit]
  have outer : ∀ l : List (Fin n),
      l.foldr (fun i h => (List.finRange 4).foldr
        (fun μ h' => (coordDeriv i μ)^[α i μ] h') h) (shiftBy w g) =
      shiftBy w (l.foldr (fun i h => (List.finRange 4).foldr
        (fun μ h' => (coordDeriv i μ)^[α i μ] h') h) g) := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih => rw [List.foldr_cons, List.foldr_cons, ih, inner]
  exact outer _
theorem foldr_eq_of_forall_eq_id {ι X : Type*} (F : ι → X → X) (h : X) (l : List ι)
    (hF : ∀ b ∈ l, F b = id) : l.foldr F h = h := by apply _root_.YangMills.Construction.ConfigSpace.FourierDecay.foldr_eq_of_forall_eq_id <;> assumption
theorem foldr_eq_of_single {ι X : Type*} (F : ι → X → X) (h : X) (l : List ι) (hl : l.Nodup) (a : ι)
    (ha : a ∈ l) (hF : ∀ b ∈ l, b ≠ a → F b = id) : l.foldr F h = F a h := by apply _root_.YangMills.Construction.ConfigSpace.FourierDecay.foldr_eq_of_forall_ne_eq_id <;> assumption
theorem multiDeriv_single (i₀ : Fin n) (μ₀ : Fin 4) (g : PointTuple n → ℂ) :
    multiDeriv (Pi.single i₀ (Pi.single μ₀ 1) : MultiIdx4 n) g =
      coordDeriv i₀ μ₀ g := by
  unfold multiDeriv
  rw [foldr_eq_of_single _ g (List.finRange n) (List.nodup_finRange n) i₀ (List.mem_finRange _)]
  · rw [foldr_eq_of_single _ g (List.finRange 4) (List.nodup_finRange 4) μ₀ (List.mem_finRange _)]
    · simp
    · intro μ _ hμ
      funext h'
      simp [hμ]
  · intro i _ hi
    funext h
    refine foldr_eq_of_forall_eq_id _ h _ fun μ _ => ?_
    funext h'
    simp [hi]
theorem idxOrder_single_add (i₀ : Fin n) (μ₀ : Fin 4) (α : MultiIdx4 n) :
    idxOrder ((Pi.single i₀ (Pi.single μ₀ 1) : MultiIdx4 n) + α) = idxOrder α + 1 := by
  have h1 : idxOrder (Pi.single i₀ (Pi.single μ₀ 1) : MultiIdx4 n) = 1 := by
    unfold idxOrder
    rw [Finset.sum_eq_single i₀, Finset.sum_eq_single μ₀]
    · simp
    · intro μ _ hμ
      simp [hμ]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  have h2 : ∀ a b : MultiIdx4 n, idxOrder (a + b) = idxOrder a + idxOrder b := fun a b => by
    unfold idxOrder
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [h2, h1, add_comm]
open DerivRules in
theorem weight_mul_coordDeriv_le (hR : RulesOver ℂ) {φ : PointTuple n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    {k : ℕ} (hfin : weightedSeminorm (k + 1) φ ≠ ⊤) {α : MultiIdx4 n} (hα : idxOrder α ≤ k)
    (i : Fin n) (μ : Fin 4) (y : PointTuple n) :
    (1 + tupleNorm y ^ 2) ^ (((k + 1 : ℕ) : ℝ) / 2) *
        ‖coordDeriv i μ (multiDeriv α φ) y‖ ≤
      (weightedSeminorm (k + 1) φ).toReal := by
  have e : coordDeriv i μ (multiDeriv α φ) =
      multiDeriv ((Pi.single i (Pi.single μ 1) : MultiIdx4 n) + α) φ := by
    rw [← multiDeriv_single]
    exact (hR n φ hφ).2.2.2.2.1 _ _
  rw [e]
  have hβ : idxOrder ((Pi.single i (Pi.single μ 1) : MultiIdx4 n) + α) ≤ k + 1 := by
    rw [idxOrder_single_add]
    omega
  refine (ENNReal.ofReal_le_iff_le_toReal hfin).1 ?_
  unfold weightedSeminorm
  exact le_iSup_of_le y (le_iSup_of_le _ (le_iSup_of_le hβ le_rfl))
theorem one_add_sq_le_mul (μ₀ : Fin 4) (x : PointTuple n) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    1 + tupleNorm x ^ 2 ≤
      (2 + 2 * (n : ℝ)) * (1 + tupleNorm (fun i => x i - s • Pi.single μ₀ (1 : ℝ)) ^ 2) := by
  have hsq : ∀ z : PointTuple n, tupleNorm z ^ 2 = ∑ i, ∑ μ, z i μ ^ 2 := fun z =>
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun μ _ => sq_nonneg _)
  rw [hsq, hsq]
  set y : PointTuple n := fun i => x i - s • Pi.single μ₀ (1 : ℝ) with hy
  have hterm : ∀ i, ∑ μ, x i μ ^ 2 ≤ 2 * ∑ μ, y i μ ^ 2 + 2 := by
    intro i
    have h1 : ∀ μ, x i μ ^ 2 ≤ 2 * y i μ ^ 2 + 2 * (Pi.single μ₀ (1 : ℝ) : Fin 4 → ℝ) μ ^ 2 := by
      intro μ
      have hx : x i μ = y i μ + s * (Pi.single μ₀ (1 : ℝ) : Fin 4 → ℝ) μ := by
        simp [hy]
      rw [hx]
      set a := y i μ
      set b := (Pi.single μ₀ (1 : ℝ) : Fin 4 → ℝ) μ
      have hs2 : s ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (a - s * b), sq_nonneg b, mul_le_mul_of_nonneg_right hs2 (sq_nonneg b)]
    have h2 : ∑ μ, (Pi.single μ₀ (1 : ℝ) : Fin 4 → ℝ) μ ^ 2 = 1 := by
      rw [Finset.sum_eq_single μ₀]
      · simp
      · intro μ _ hμ
        simp [hμ]
      · simp
    calc ∑ μ, x i μ ^ 2
        ≤ ∑ μ, (2 * y i μ ^ 2 + 2 * (Pi.single μ₀ (1 : ℝ) : Fin 4 → ℝ) μ ^ 2) :=
          Finset.sum_le_sum fun μ _ => h1 μ
      _ = 2 * ∑ μ, y i μ ^ 2 + 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h2]
          ring
  have h3 : ∑ i, ∑ μ, x i μ ^ 2 ≤ 2 * ∑ i, ∑ μ, y i μ ^ 2 + 2 * (n : ℝ) := by
    calc ∑ i, ∑ μ, x i μ ^ 2 ≤ ∑ i : Fin n, (2 * ∑ μ, y i μ ^ 2 + 2) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = 2 * ∑ i, ∑ μ, y i μ ^ 2 + 2 * (n : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp
          ring
  have h4 : 0 ≤ ∑ i, ∑ μ, y i μ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun μ _ => sq_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg hn h4]
open DerivRules in
theorem weightedSeminorm_shiftBy_sub_le (hR : RulesOver ℂ) {φ : PointTuple n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (μ₀ : Fin 4) {k : ℕ} (hfin : weightedSeminorm (k + 1) φ ≠ ⊤) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    weightedSeminorm k (shiftBy (t • Pi.single μ₀ (1 : ℝ)) φ - φ) ≤
      ENNReal.ofReal (t * ((n : ℝ) * ((2 + 2 * (n : ℝ)) ^ ((k : ℝ) / 2) *
        (weightedSeminorm (k + 1) φ).toReal))) := by
  set Mr := (weightedSeminorm (k + 1) φ).toReal with hMr
  set c₀ := (2 + 2 * (n : ℝ)) ^ ((k : ℝ) / 2) * Mr with hc₀
  unfold weightedSeminorm
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ENNReal.ofReal_le_ofReal ?_
  set w : Fin 4 → ℝ := t • Pi.single μ₀ (1 : ℝ) with hw
  have hsh : ContDiff ℝ ∞ (shiftBy w φ) := by
    unfold shiftBy
    exact hφ.comp (contDiff_pi.2 fun i => (contDiff_apply ℝ (Fin 4 → ℝ) i).sub contDiff_const)
  set g := multiDeriv α φ with hgdef
  have hg : ContDiff ℝ ∞ g := (hR n φ hφ).2.2.1 α
  have e1 : multiDeriv α (shiftBy w φ - φ) x = g (fun i => x i - w) - g x := by
    have e2 : shiftBy w φ - φ = shiftBy w φ + fun y => (-1 : ℂ) * φ y := by
      funext y
      simp [sub_eq_add_neg]
    have hm : ContDiff ℝ ∞ (fun y => (-1 : ℂ) * φ y) := contDiff_const.mul hφ
    rw [e2, (hR n _ hsh).2.2.2.2.2.1 _ hm α, (hR n φ hφ).2.2.2.2.2.2.1 (-1) α,
      multiDeriv_shiftBy]
    simp [shiftBy, hgdef, sub_eq_add_neg]
  rw [e1]
  set W := (1 + tupleNorm x ^ 2) ^ ((k : ℝ) / 2) with hW
  have hbase : 0 < 1 + tupleNorm x ^ 2 := by positivity
  have hWpos : 0 < W := Real.rpow_pos_of_pos hbase _
  set E : PointTuple n := fun _ => Pi.single μ₀ (1 : ℝ) with hE
  set f : ℝ → ℂ := fun s => g (fun i => x i - s • Pi.single μ₀ (1 : ℝ)) with hf
  set f' : ℝ → ℂ := fun s => -(fderiv ℝ g (x - s • E) E) with hf'
  have hpath : ∀ s : ℝ, (fun i => x i - s • Pi.single μ₀ (1 : ℝ)) = x - s • E := fun s => rfl
  have hder : ∀ s : ℝ, HasDerivAt f (f' s) s := by
    intro s
    have hγ : HasDerivAt (fun s : ℝ => x - s • E) (-E) s := by
      simpa using ((hasDerivAt_id s).smul_const E).const_sub x
    have hd : HasFDerivAt g (fderiv ℝ g (x - s • E)) (x - s • E) :=
      ((hg.differentiable (by simp)) _).hasFDerivAt
    have := hd.comp_hasDerivAt s hγ
    simpa [hf, hf', hpath, Function.comp_def] using this
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f' s‖ ≤ (n : ℝ) * (c₀ / W) := by
    intro s hs
    have hs0 := hs.1
    have hs1 := hs.2.trans ht1
    set y : PointTuple n := x - s • E with hy
    have hsum : f' s = -∑ i, coordDeriv i μ₀ g y := by
      have hEs : E = ∑ i, Pi.single i (Pi.single μ₀ (1 : ℝ)) := (Finset.univ_sum_single E).symm
      have h1 : fderiv ℝ g y E = ∑ i, coordDeriv i μ₀ g y := by
        calc fderiv ℝ g y E = fderiv ℝ g y (∑ i, Pi.single i (Pi.single μ₀ (1 : ℝ))) :=
              congrArg _ hEs
          _ = ∑ i, coordDeriv i μ₀ g y := by
              rw [map_sum]
              exact Finset.sum_congr rfl fun i _ => ((hR n g hg).1 i μ₀ y).symm
      show -(fderiv ℝ g y E) = _
      rw [h1]
    have hone : ∀ i, ‖coordDeriv i μ₀ g y‖ ≤ c₀ / W := by
      intro i
      rw [le_div_iff₀ hWpos]
      have h1 := weight_mul_coordDeriv_le hR hφ hfin hα i μ₀ y
      have h2 := one_add_sq_le_mul μ₀ x hs0 hs1
      rw [hpath s] at h2
      have hyb : 1 ≤ 1 + tupleNorm y ^ 2 := by nlinarith [sq_nonneg (tupleNorm y)]
      have hk0 : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
      have h3 : W ≤ (2 + 2 * (n : ℝ)) ^ ((k : ℝ) / 2) * (1 + tupleNorm y ^ 2) ^ ((k : ℝ) / 2) := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        exact Real.rpow_le_rpow hbase.le h2 hk0
      have h4 : (1 + tupleNorm y ^ 2) ^ ((k : ℝ) / 2) ≤
          (1 + tupleNorm y ^ 2) ^ (((k + 1 : ℕ) : ℝ) / 2) := by
        refine Real.rpow_le_rpow_of_exponent_le hyb ?_
        push_cast
        linarith
      have hp := norm_nonneg (coordDeriv i μ₀ g y)
      have hA : 0 ≤ (2 + 2 * (n : ℝ)) ^ ((k : ℝ) / 2) := by positivity
      calc ‖coordDeriv i μ₀ g y‖ * W
          ≤ ‖coordDeriv i μ₀ g y‖ * ((2 + 2 * (n : ℝ)) ^ ((k : ℝ) / 2) *
              (1 + tupleNorm y ^ 2) ^ (((k + 1 : ℕ) : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left h4 hA)) hp
        _ = (2 + 2 * (n : ℝ)) ^ ((k : ℝ) / 2) * ((1 + tupleNorm y ^ 2) ^ (((k + 1 : ℕ) : ℝ) / 2) *
              ‖coordDeriv i μ₀ g y‖) := by ring
        _ ≤ c₀ := mul_le_mul_of_nonneg_left h1 hA
    rw [hsum, norm_neg]
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_sum (s := Finset.univ) fun i (_ : i ∈ Finset.univ) => hone i
    simpa using this
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (G := ℂ) (f := f)
    (f' := f') (s := Set.Icc (0 : ℝ) t) (C := (n : ℝ) * (c₀ / W)) (x := 0) (y := t)
    (fun s _ => (hder s).hasDerivWithinAt) hbound (convex_Icc _ _) ⟨le_rfl, ht0⟩ ⟨ht0, le_rfl⟩
  have hf0 : f 0 = g x := by simp [hf]
  have hft : f t = g (fun i => x i - w) := rfl
  rw [hf0, hft, sub_zero, Real.norm_of_nonneg ht0] at hmv
  calc W * ‖g (fun i => x i - w) - g x‖ ≤ W * ((n : ℝ) * (c₀ / W) * t) :=
        mul_le_mul_of_nonneg_left hmv hWpos.le
    _ = t * ((n : ℝ) * c₀) := by
        field_simp
open DerivRules in
theorem tendsto_weightedSeminorm_shiftBy (hR : RulesOver ℂ) {φ : PointTuple n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (μ₀ : Fin 4) {k : ℕ} (hfin : weightedSeminorm (k + 1) φ ≠ ⊤) :
    Tendsto (fun t : ℝ≥0 => weightedSeminorm k (shiftBy ((t : ℝ) • Pi.single μ₀ (1 : ℝ)) φ - φ))
      (𝓝 0) (𝓝 0) := by
  set C := (n : ℝ) * ((2 + 2 * (n : ℝ)) ^ ((k : ℝ) / 2) * (weightedSeminorm (k + 1) φ).toReal)
  have hup : Tendsto (fun t : ℝ≥0 => ENNReal.ofReal ((t : ℝ) * C)) (𝓝 0) (𝓝 0) := by
    have h1 : Continuous fun t : ℝ≥0 => ENNReal.ofReal ((t : ℝ) * C) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa using h1.tendsto 0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Iic_mem_nhds (show (0 : ℝ≥0) < 1 by norm_num)] with t ht
  exact weightedSeminorm_shiftBy_sub_le hR hφ μ₀ hfin t.2 (by exact_mod_cast ht)
end TestSpaces.ShiftEstimates
namespace ConfigSpace.TimeShiftProof
section Orders
theorem shiftAct_shiftAct (w w' : Fin 4 → ℝ) {n : ℕ} (φ : Config n → ℂ) :
    shiftAct w (shiftAct w' φ) = shiftAct (w' + w) φ := by
  funext x
  simp only [shiftAct_apply]
  congr 1
  funext i
  rw [sub_sub, add_comm]
theorem shiftAct_zero {n : ℕ} (φ : Config n → ℂ) : shiftAct 0 φ = φ := by
  funext x
  simp only [shiftAct_apply, sub_zero]
theorem shiftAct_tensorFn (w : Fin 4 → ℝ) {q q' : ℕ} (φ : Config q → ℂ)
    (ψ : Config q' → ℂ) :
    shiftAct w (tensorFn φ ψ) =
      tensorFn (shiftAct w φ) (shiftAct w ψ) := by
  funext z
  simp only [shiftAct_apply, tensorFn]
  rfl
theorem shiftActAt_shiftActAt (w w' : Fin 4 → ℝ) {n : ℕ} (f : FnOrScalar n) :
    shiftActAt w (shiftActAt w' f) = shiftActAt (w' + w) f := by
  cases n with
  | zero => rfl
  | succ n => exact shiftAct_shiftAct w w' (show Config (n + 1) → ℂ from f)
theorem shiftActAt_zero {n : ℕ} (f : FnOrScalar n) : shiftActAt 0 f = f := by
  cases n with
  | zero => rfl
  | succ n => exact shiftAct_zero (show Config (n + 1) → ℂ from f)
theorem shiftActAt_zeroOfDegree (w : Fin 4 → ℝ) (n : ℕ) :
    shiftActAt w (zeroOfDegree n) = zeroOfDegree n := by apply _root_.YangMills.Construction.ConditionDomains.shiftActAt_zeroOfDegree <;> assumption
theorem shiftActAt_add (w : Fin 4 → ℝ) {n : ℕ} (f g : FnOrScalar n) :
    shiftActAt w (f + g) = shiftActAt w f + shiftActAt w g := by
  cases n <;> rfl
theorem shiftActAt_smul (w : Fin 4 → ℝ) {n : ℕ} (c : ℂ) (f : FnOrScalar n) :
    shiftActAt w (c • f) = c • shiftActAt w f := by
  cases n <;> rfl
theorem shiftActAt_smulAt (w : Fin 4 → ℝ) (c : ℂ) {n : ℕ} (f : FnOrScalar n) :
    shiftActAt w (smulAt c f) = smulAt c (shiftActAt w f) := by
  cases n <;> rfl
theorem shiftActAt_cast (w : Fin 4 → ℝ) {a b : ℕ} (h : a = b) (f : FnOrScalar a) :
    shiftActAt w (h ▸ f : FnOrScalar b) = h ▸ shiftActAt w f := by apply _root_.YangMills.Construction.AdmissibleClustering.shiftActAt_cast <;> assumption
theorem shiftActAt_tensorAt (w : Fin 4 → ℝ) {q q' : ℕ} (f : FnOrScalar q)
    (g : FnOrScalar q') :
    shiftActAt w (tensorAt f g) =
      tensorAt (shiftActAt w f) (shiftActAt w g) := by
  cases q with
  | zero =>
    show shiftActAt w ((Nat.zero_add q').symm ▸ smulAt (show ℂ from f) g) =
      (Nat.zero_add q').symm ▸ smulAt (show ℂ from f) (shiftActAt w g)
    rw [shiftActAt_cast, shiftActAt_smulAt]
  | succ m =>
    cases q' with
    | zero => exact shiftActAt_smulAt w _ f
    | succ k =>
      exact shiftAct_tensorFn w (show Config (m + 1) → ℂ from f)
        (show Config (k + 1) → ℂ from g)
theorem timeFlip_sub_neg_smul (t : ℝ) (u : Fin 4 → ℝ) :
    timeFlip (u - (-t) • SchwartzAxioms.timeUnitVector) =
      timeFlip u - t • SchwartzAxioms.timeUnitVector := by
  funext μ
  fin_cases μ <;> simp [timeFlip, SchwartzAxioms.timeUnitVector, TimeAxis.timeIdx]
  ring
theorem flipConj_shiftAct (t : ℝ) {n : ℕ} (φ : Config n → ℂ) :
    flipConj (shiftAct (t • SchwartzAxioms.timeUnitVector) φ) =
      shiftAct ((-t) • SchwartzAxioms.timeUnitVector) (flipConj φ) := by
  funext x
  simp only [shiftAct_apply, flipConj, timeFlip_sub_neg_smul]
theorem flipConjAt_shiftActAt (t : ℝ) {n : ℕ} (f : FnOrScalar n) :
    flipConjAt (shiftActAt (t • SchwartzAxioms.timeUnitVector) f) =
      shiftActAt ((-t) • SchwartzAxioms.timeUnitVector)
        (flipConjAt f) := by
  cases n with
  | zero => rfl
  | succ n => exact flipConj_shiftAct t (show Config (n + 1) → ℂ from f)
theorem smulAt_zeroOfDegree (c : ℂ) (n : ℕ) : smulAt c (zeroOfDegree n) = zeroOfDegree n := by apply _root_.YangMills.Construction.ConditionDomains.smulAt_zero_right <;> assumption
theorem smulAt_zero_left {n : ℕ} (f : FnOrScalar n) : smulAt 0 f = zeroOfDegree n := by apply _root_.YangMills.Construction.ConditionDomains.smulAt_zero_left <;> assumption
theorem cast_zeroOfDegree {a b : ℕ} (h : a = b) :
    (h ▸ zeroOfDegree a : FnOrScalar b) = zeroOfDegree b := by apply _root_.YangMills.Construction.ConditionDomains.cast_zeroOfDegree <;> assumption
theorem flipConjAt_zeroOfDegree (n : ℕ) : flipConjAt (zeroOfDegree n) = zeroOfDegree n := by apply _root_.YangMills.Construction.ConditionDomains.flipConjAt_zeroOfDegree <;> assumption
theorem tensorAt_zeroOfDegree_left (q : ℕ) {q' : ℕ} (g : FnOrScalar q') :
    tensorAt (zeroOfDegree q) g = zeroOfDegree (q + q') := by apply _root_.YangMills.Construction.ConditionDomains.tensorAt_zero_left <;> assumption
theorem tensorAt_zeroOfDegree_right {q : ℕ} (f : FnOrScalar q) (q' : ℕ) :
    tensorAt f (zeroOfDegree q') = zeroOfDegree (q + q') := by
  cases q with
  | zero =>
    show (Nat.zero_add q').symm ▸ smulAt (show ℂ from f) (zeroOfDegree q') = _
    rw [smulAt_zeroOfDegree, cast_zeroOfDegree]
  | succ m =>
    cases q' with
    | zero => exact smulAt_zero_left f
    | succ k =>
      funext z
      exact mul_zero (M₀ := ℂ) _
end Orders
open SchwartzAxioms (timeUnitVector)
section Sequences
variable {S : FlatSequence}
theorem shiftActAt_mem (hT : MotionComposition.CompositionTranslationStatement) {t : ℝ} (ht : 0 ≤ t)
    {n : ℕ} {f : FnOrScalar n} (hf : f ∈ flatOffPosTimeAt n) :
    shiftActAt (t • timeUnitVector) f ∈ flatOffPosTimeAt n := by apply _root_.YangMills.Construction.MinkowskiSpace.WickTimeShift.shiftActAt_mem_flatOffPosTimeAt <;> assumption
def shiftSeq (hT : MotionComposition.CompositionTranslationStatement) (t : ℝ≥0)
    (Φ : AdmissibleSeq) : AdmissibleSeq :=
  ⟨fun q => ⟨shiftActAt ((t : ℝ) • timeUnitVector) (Φ.1 q).1,
      shiftActAt_mem hT t.2 (Φ.1 q).2⟩, by
    refine Set.Finite.subset Φ.2 fun q hq h0 => hq ?_
    show shiftActAt _ (Φ.1 q).1 = zeroOfDegree q
    rw [h0, shiftActAt_zeroOfDegree]⟩
theorem evalAt_eq_of_shift (hI : S.IsTranslationInvariant) (w : Fin 4 → ℝ) {n : ℕ}
    {f g : FnOrScalar n} (hf : f ∈ flatOffDiagonalAt n)
    (hg : g ∈ flatOffDiagonalAt n) (h : g = shiftActAt w f) :
    S.evalAt g = S.evalAt f := by
  cases n with
  | zero => exact congrArg S.evalAt h
  | succ m =>
    subst h
    rw [S.evalAt_of_mem hf, S.evalAt_of_mem hg]
    exact hI m w ⟨f, hf⟩ hg
theorem reflectionForm_shiftSeq (hT : MotionComposition.CompositionTranslationStatement)
    (hs : S.IsSesquilinear) (hI : S.IsTranslationInvariant) (t : ℝ≥0)
    (Φ Ψ : AdmissibleSeq) :
    S.reflectionForm Φ (shiftSeq hT t Ψ) =
      S.reflectionForm (shiftSeq hT t Φ) Ψ := by
  refine finsum_congr fun p => ?_
  symm
  refine evalAt_eq_of_shift hI ((-(t : ℝ)) • timeUnitVector) (hs.1 Φ (shiftSeq hT t Ψ) p.1 p.2)
    (hs.1 (shiftSeq hT t Φ) Ψ p.1 p.2) ?_
  show tensorAt (flipConjAt
        (shiftActAt ((t : ℝ) • timeUnitVector) (Φ.1 p.1).1)) (Ψ.1 p.2).1 =
    shiftActAt ((-(t : ℝ)) • timeUnitVector)
      (tensorAt (flipConjAt (Φ.1 p.1).1)
        (shiftActAt ((t : ℝ) • timeUnitVector) (Ψ.1 p.2).1))
  rw [shiftActAt_tensorAt, shiftActAt_shiftActAt, ← flipConjAt_shiftActAt]
  have e : (t : ℝ) • timeUnitVector + (-(t : ℝ)) • timeUnitVector = 0 := by
    rw [neg_smul, add_neg_cancel]
  rw [e, shiftActAt_zero]
def shiftLin (hT : MotionComposition.CompositionTranslationStatement)
    (hV : SpanOfAdmissible.Statement) (t : ℝ≥0) :
    admissibleSpan →ₗ[ℂ] admissibleSpan where
  toFun x := ⟨timeShift t x.1, by
    obtain ⟨Φ, h⟩ := (hV x.1).1 x.2
    rw [h]
    exact (toAdmissibleSpan (shiftSeq hT t Φ)).2⟩
  map_add' x y := Subtype.ext (funext fun q => shiftActAt_add _ (x.1 q) (y.1 q))
  map_smul' c x := Subtype.ext (funext fun q => shiftActAt_smul _ c (x.1 q))
variable {hT : MotionComposition.CompositionTranslationStatement}
  {hV : SpanOfAdmissible.Statement}
theorem shiftLin_shiftLin (s t : ℝ≥0) (x : admissibleSpan) :
    shiftLin hT hV s (shiftLin hT hV t x) = shiftLin hT hV (s + t) x := by
  refine Subtype.ext (funext fun q => ?_)
  show shiftActAt ((s : ℝ) • timeUnitVector)
      (shiftActAt ((t : ℝ) • timeUnitVector) (x.1 q)) =
    shiftActAt (((s + t : ℝ≥0) : ℝ) • timeUnitVector) (x.1 q)
  rw [shiftActAt_shiftActAt, NNReal.coe_add, add_smul, add_comm]
theorem shiftLin_zero (x : admissibleSpan) : shiftLin hT hV 0 x = x := by
  refine Subtype.ext (funext fun q => ?_)
  show shiftActAt (((0 : ℝ≥0) : ℝ) • timeUnitVector) (x.1 q) = x.1 q
  rw [NNReal.coe_zero, zero_smul, shiftActAt_zero]
theorem exists_eq_toAdmissibleSpan (hV : SpanOfAdmissible.Statement)
    (x : admissibleSpan) : ∃ Φ, x = toAdmissibleSpan Φ := by apply _root_.YangMills.Construction.MinkowskiSpace.IsometryConstruction.exists_toAdmissibleSpan_eq <;> assumption
theorem spanForm_isPosSemidef (hV : SpanOfAdmissible.Statement)
    (hs : S.IsSesquilinear) (hp : S.IsPosSemidef) :
    FormCompletion.IsPosSemidefHermitianForm S.spanForm := by apply _root_.YangMills.Construction.MinkowskiSpace.IsometryConstruction.spanForm_isPosSemidefHermitian <;> assumption
end Sequences
section Classes
variable {S : FlatSequence}
open FormCompletion in
def classLin (hC : FormCompletion.FormCompletionIsHilbertSpace)
    (hq : IsPosSemidefHermitianForm S.spanForm) :
    admissibleSpan →ₗ[ℂ] S.HilbertCompletion where
  toFun := S.spanClass
  map_add' x y := by
    obtain ⟨⟨-, -, -, -, hadd, -, -, -⟩, ⟨-, -, -, -, -, hm, -⟩, -⟩ := hC _ _ hq
    apply asMap_injective
    rw [asMap_add]
    show asMap (classVec _ _) = asMap (classVec _ _) + asMap (classVec _ _)
    rw [hm, hm, hm, hadd]
  map_smul' c x := by
    obtain ⟨⟨-, -, -, -, -, hsm, -, -⟩, ⟨-, -, -, -, -, hm, -⟩, -⟩ := hC _ _ hq
    apply asMap_injective
    rw [RingHom.id_apply, asMap_smul]
    show asMap (classVec _ _) = c • asMap (classVec _ _)
    rw [hm, hm, hsm]
variable {hC : FormCompletion.FormCompletionIsHilbertSpace}
  {hq : FormCompletion.IsPosSemidefHermitianForm S.spanForm}
theorem inner_classLin (x y : admissibleSpan) :
    ⟪classLin hC hq x, classLin hC hq y⟫_ℂ = S.spanForm x y := by
  obtain ⟨-, ⟨-, -, -, -, -, -, hi, -⟩, -⟩ := hC _ _ hq
  exact hi x y
theorem denseRange_classLin : DenseRange (classLin hC hq) := by
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, hd⟩, -⟩ := hC _ _ hq
  exact hd
theorem norm_classLin_sq (x : admissibleSpan) :
    ‖classLin hC hq x‖ ^ 2 = (S.spanForm x x).re := by
  rw [← inner_classLin (hC := hC) (hq := hq)]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
theorem norm_classLin_eq (x : admissibleSpan) :
    ‖classLin hC hq x‖ = FormCompletion.seminormOfForm S.spanForm x := by
  rw [FormCompletion.seminormOfForm, ← norm_classLin_sq (hC := hC) (hq := hq),
    Real.sqrt_sq (norm_nonneg _)]
end Classes
open SchwartzAxioms (seminormAt)
section Bound
variable {S : FlatSequence}
theorem evalAt_cast {a b : ℕ} (h : a = b) (f : FnOrScalar a) :
    S.evalAt (h ▸ f : FnOrScalar b) = S.evalAt f := by apply _root_.YangMills.Construction.AdmissibleClustering.evalAt_cast <;> assumption
theorem mem_flatOffDiagonalAt_of_cast {a b : ℕ} (h : a = b) {f : FnOrScalar a}
    (hf : (h ▸ f : FnOrScalar b) ∈ flatOffDiagonalAt b) :
    f ∈ flatOffDiagonalAt a := by
  subst h
  exact hf
theorem evalAt_eq_zero (hseq : IsCLMSequence S) {n : ℕ}
    {f : FnOrScalar n} (hf : f ∈ flatOffDiagonalAt n) (h0 : f = zeroOfDegree n) :
    S.evalAt f = 0 := by
  cases n with
  | zero =>
    rw [S.evalAt_of_mem hf]
    exact (hseq.1 ⟨f, hf⟩).trans h0
  | succ m =>
    rw [S.evalAt_of_mem hf]
    have h := (hseq.2 m).1 0 0 ⟨f, hf⟩ ⟨f, hf⟩ ⟨f, hf⟩ (by
      subst h0
      funext y
      show (0 : ℂ) = _
      simp [zeroOfDegree])
    exact show S.atSucc m ⟨f, hf⟩ = 0 from by simpa using h
theorem exists_uniform_atSucc_bound (hF : TestSpaces.Elementary.BasicProperties)
    (hE : IsContinuousSeq S) (N : ℕ) :
    ∃ (k : ℕ) (D : ℝ≥0∞), 0 < k ∧ D ≠ ⊤ ∧ 1 ≤ D ∧ ∀ m < N, ∀ (f : Config (m + 1) → ℂ)
      (hf : f ∈ schwartzFlatOffDiagonal (m + 1)),
      ENNReal.ofReal ‖S.atSucc m ⟨f, hf⟩‖ ≤ D * TestSpaces.weightedSeminorm k f := by
  choose kk C h1 hC hb using fun m => (hE m).2
  refine ⟨1 + ∑ m ∈ Finset.range N, kk m, 1 + ∑ m ∈ Finset.range N, ENNReal.ofReal (C m),
    by omega, ?_, le_self_add, ?_⟩
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      (ENNReal.sum_lt_top.2 fun _ _ => ENNReal.ofReal_lt_top).ne⟩
  intro m hm f hf
  have hkm : kk m ≤ 1 + ∑ m ∈ Finset.range N, kk m := by
    have := Finset.single_le_sum (f := kk) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hm)
    omega
  have hfin : ConfigSpace.schwartzSeminorm (kk m) f ≠ ⊤ := (hf.1.2 (kk m) (h1 m)).ne
  have h2 := hb m ⟨f, hf⟩
  have h3 : ENNReal.ofReal ‖S.atSucc m ⟨f, hf⟩‖ ≤
      ENNReal.ofReal (C m) * ConfigSpace.schwartzSeminorm (kk m) f := by
    have h4 := ENNReal.ofReal_le_ofReal h2
    rw [ENNReal.ofReal_mul (hC m)] at h4
    have e : ENNReal.ofReal (bracketNorm (kk m) (toSchwartzFn ⟨f, hf⟩)) =
        ConfigSpace.schwartzSeminorm (kk m) f := ENNReal.ofReal_toReal hfin
    rwa [e] at h4
  have hs : f ∈ TestSpaces.schwartzSet (m + 1) := hf.1
  have hmono : TestSpaces.weightedSeminorm (kk m) f ≤
      TestSpaces.weightedSeminorm (1 + ∑ m ∈ Finset.range N, kk m) f :=
    ((hF (m + 1) (Nat.succ_pos m)).1.1 f hs f hs 1 1).2.1 _ _ (h1 m) hkm |>.1
  have hCle : ENNReal.ofReal (C m) ≤ 1 + ∑ m ∈ Finset.range N, ENNReal.ofReal (C m) :=
    (Finset.single_le_sum (f := fun m => ENNReal.ofReal (C m)) (fun _ _ => bot_le)
      (Finset.mem_range.2 hm)).trans le_add_self
  exact h3.trans (mul_le_mul' hCle hmono)
theorem flipConj_mem_and_seminorm (hO : TestFunctionOps.OperationsStatement) {m k : ℕ} (hk : 0 < k)
    {φ : Config (m + 1) → ℂ} (hφ : φ ∈ TestSpaces.schwartzSet (m + 1)) :
    flipConj φ ∈ TestSpaces.schwartzSet (m + 1) ∧
      TestSpaces.weightedSeminorm k (flipConj φ) = TestSpaces.weightedSeminorm k φ := by
  obtain ⟨-, h, -, -⟩ := hO.1 (m + 1) k (Nat.succ_pos m) hk 1
    (SmoothSeparatedTuples.pureTranslation 0)
  obtain ⟨hk1, hk2, -⟩ := h φ hφ
  exact ⟨hk1.2.2.1, hk2.2.1⟩
theorem evalAt_tensorAt_le (hB : TestSpaces.TestSpaceFacts.Statement)
    (hO : TestFunctionOps.OperationsStatement) (hseq : IsCLMSequence S)
    {k N : ℕ} {D : ℝ≥0∞} (hk : 0 < k) (hD : 1 ≤ D)
    (hb : ∀ m < N, ∀ (f : Config (m + 1) → ℂ) (hf : f ∈ schwartzFlatOffDiagonal (m + 1)),
      ENNReal.ofReal ‖S.atSucc m ⟨f, hf⟩‖ ≤ D * TestSpaces.weightedSeminorm k f)
    {q q' : ℕ} (hqq : q + q' ≤ N) {f : FnOrScalar q} {g : FnOrScalar q'}
    (hf : f ∈ flatOffPosTimeAt q) (hg : g ∈ flatOffPosTimeAt q')
    (hfl : tensorAt (flipConjAt f) g ∈ flatOffDiagonalAt (q + q')) :
    ENNReal.ofReal ‖S.evalAt (tensorAt (flipConjAt f) g)‖ ≤
      D * seminormAt k f * seminormAt k g := by
  cases q with
  | zero =>
    have hfl' := mem_flatOffDiagonalAt_of_cast (Nat.zero_add q').symm
      (f := smulAt (conj (show ℂ from f)) g) hfl
    have e : S.evalAt (tensorAt (flipConjAt (n := 0) f) g) =
        S.evalAt (smulAt (conj (show ℂ from f)) g) :=
      evalAt_cast (Nat.zero_add q').symm _
    rw [e]
    cases q' with
    | zero =>
      rw [S.evalAt_of_mem hfl', hseq.1]
      show ENNReal.ofReal ‖conj (show ℂ from f) * (show ℂ from g)‖ ≤
        D * ENNReal.ofReal ‖(show ℂ from f)‖ * ENNReal.ofReal ‖(show ℂ from g)‖
      rw [norm_mul, RCLike.norm_conj, ENNReal.ofReal_mul (norm_nonneg _), mul_assoc]
      exact le_mul_of_one_le_left' hD
    | succ m' =>
      have hgs : g ∈ TestSpaces.schwartzSet (m' + 1) := hg.1
      rw [S.evalAt_of_mem hfl']
      have h1 := hb m' (by omega) _ hfl'
      have h2 := hB.2.1 (m' + 1) k (Nat.succ_pos m') hk (conj (show ℂ from f)) g hgs
      refine h1.trans ?_
      have e2 : TestSpaces.weightedSeminorm k (smulAt (conj (show ℂ from f)) g) =
          ENNReal.ofReal ‖conj (show ℂ from f)‖ * TestSpaces.weightedSeminorm k g := h2
      rw [e2, RCLike.norm_conj, mul_assoc]
      rfl
  | succ m =>
    have hfs : f ∈ TestSpaces.schwartzSet (m + 1) := hf.1
    obtain ⟨hΘ, hΘn⟩ := flipConj_mem_and_seminorm hO hk hfs
    cases q' with
    | zero =>
      have hfl' : smulAt (show ℂ from g) (flipConjAt f) ∈
          flatOffDiagonalAt (m + 1) := hfl
      show ENNReal.ofReal ‖S.evalAt (smulAt (show ℂ from g)
        (flipConjAt f))‖ ≤ D * seminormAt k f * seminormAt k g
      rw [S.evalAt_of_mem hfl']
      have h1 := hb m (by omega) _ hfl'
      have h2 := hB.2.1 (m + 1) k (Nat.succ_pos m) hk (show ℂ from g) _ hΘ
      refine h1.trans ?_
      have e2 : TestSpaces.weightedSeminorm k (smulAt (show ℂ from g)
          (flipConjAt f)) =
          ENNReal.ofReal ‖(show ℂ from g)‖ * TestSpaces.weightedSeminorm k (flipConj f) := h2
      rw [e2, hΘn]
      show D * (ENNReal.ofReal ‖(show ℂ from g)‖ * TestSpaces.weightedSeminorm k f) ≤
        D * TestSpaces.weightedSeminorm k f * ENNReal.ofReal ‖(show ℂ from g)‖
      rw [mul_comm (ENNReal.ofReal _), mul_assoc]
    | succ m' =>
      have hgs : g ∈ TestSpaces.schwartzSet (m' + 1) := hg.1
      have hfl' : tensorFn (p := m + 1) (p' := m' + 1) (flipConj f) g ∈
          flatOffDiagonalAt (m + 1 + m' + 1) := hfl
      show ENNReal.ofReal ‖S.evalAt (n := m + 1 + m' + 1)
        (tensorFn (p := m + 1) (p' := m' + 1) (flipConj f) g)‖ ≤
        D * seminormAt k f * seminormAt k g
      rw [S.evalAt_of_mem hfl']
      have h1 := hb (m + 1 + m') (by omega) _ hfl'
      have h2 := (hB.1 (m + 1) (m' + 1) k (Nat.succ_pos m) (Nat.succ_pos m') hk _ hΘ g hgs).2.1
      refine h1.trans ?_
      have e2 : TestSpaces.weightedSeminorm k
          (tensorFn (p := m + 1) (p' := m' + 1) (flipConj f) g) ≤
          TestSpaces.weightedSeminorm k (flipConj f) * TestSpaces.weightedSeminorm k g := h2
      rw [hΘn] at e2
      rw [mul_assoc]
      exact mul_le_mul_right e2 D
def normSum (k N : ℕ) (x : GradedSeq) : ℝ≥0∞ :=
  ∑ q ∈ Finset.range N, seminormAt k (x q)
theorem spanForm_le_normSum (hV : SpanOfAdmissible.Statement)
    (hF : TestSpaces.Elementary.BasicProperties)
    (hB : TestSpaces.TestSpaceFacts.Statement)
    (hO : TestFunctionOps.OperationsStatement) (hseq : IsCLMSequence S)
    (hE : IsContinuousSeq S) (hs : S.IsSesquilinear) (N : ℕ) :
    ∃ (k : ℕ) (D : ℝ≥0∞), 0 < k ∧ D ≠ ⊤ ∧ ∀ x y : admissibleSpan,
      (∀ q, N ≤ q → x.1 q = zeroOfDegree q) → (∀ q, N ≤ q → y.1 q = zeroOfDegree q) →
      ENNReal.ofReal ‖S.spanForm x y‖ ≤
        D * normSum k N x.1 * normSum k N y.1 := by
  obtain ⟨k, D, hk, hD, h1, hb⟩ := exists_uniform_atSucc_bound hF hE (2 * N)
  refine ⟨k, D, hk, hD, fun x y hx hy => ?_⟩
  obtain ⟨Φ, rfl⟩ := exists_eq_toAdmissibleSpan hV x
  obtain ⟨Ψ, rfl⟩ := exists_eq_toAdmissibleSpan hV y
  set a : ℕ × ℕ → ℂ := fun p => S.evalAt
    (tensorAt (flipConjAt (Φ.1 p.1).1) (Ψ.1 p.2).1) with ha
  have hsupp : Function.support a ⊆ ↑(Finset.range N ×ˢ Finset.range N) := by
    rintro ⟨q, q'⟩ hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    apply hp
    have hfl := hs.1 Φ Ψ q q'
    refine evalAt_eq_zero hseq hfl ?_
    rcases not_and_or.1 hcon with h | h
    · have h0 : (Φ.1 q).1 = zeroOfDegree q := hx q (not_lt.1 h)
      show tensorAt (flipConjAt (Φ.1 q).1) (Ψ.1 q').1 = _
      rw [h0, flipConjAt_zeroOfDegree, tensorAt_zeroOfDegree_left]
    · have h0 : (Ψ.1 q').1 = zeroOfDegree q' := hy q' (not_lt.1 h)
      show tensorAt (flipConjAt (Φ.1 q).1) (Ψ.1 q').1 = _
      rw [h0, tensorAt_zeroOfDegree_right]
  have e : S.spanForm (toAdmissibleSpan Φ) (toAdmissibleSpan Ψ) =
      ∑ p ∈ Finset.range N ×ˢ Finset.range N, a p :=
    finsum_eq_sum_of_support_subset a hsupp
  rw [e, ofReal_norm]
  refine (enorm_sum_le _ _).trans ?_
  have hterm : ∀ p ∈ Finset.range N ×ˢ Finset.range N,
      ‖a p‖ₑ ≤ D * seminormAt k (Φ.1 p.1).1 * seminormAt k (Ψ.1 p.2).1 := by
    rintro ⟨q, q'⟩ hp
    obtain ⟨hq, hq'⟩ := Finset.mem_product.1 hp
    have hq1 := Finset.mem_range.1 hq
    have hq2 := Finset.mem_range.1 hq'
    rw [← ofReal_norm]
    exact evalAt_tensorAt_le hB hO hseq hk h1 hb (by simp only at hq1 hq2; omega) (Φ.1 q).2
      (Ψ.1 q').2 (hs.1 Φ Ψ q q')
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_product, mul_assoc, normSum, normSum, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q' _ => ?_
  rw [mul_assoc]
  rfl
theorem exists_degree_bound (hV : SpanOfAdmissible.Statement)
    (x : admissibleSpan) : ∃ N, ∀ q, N ≤ q → x.1 q = zeroOfDegree q := by
  obtain ⟨Φ, rfl⟩ := exists_eq_toAdmissibleSpan hV x
  obtain ⟨b, hb⟩ := Set.Finite.bddAbove Φ.2
  refine ⟨b + 1, fun q hq => ?_⟩
  by_contra hne
  have := hb hne
  omega
end Bound
section Contractions
variable {S : FlatSequence}
structure Standing (S : FlatSequence) : Prop where
  comp : MotionComposition.CompositionTranslationStatement
  span : SpanOfAdmissible.Statement
  completion : FormCompletion.FormCompletionIsHilbertSpace
  basic : TestSpaces.Elementary.BasicProperties
  bounds : TestSpaces.TestSpaceFacts.Statement
  ops : TestFunctionOps.OperationsStatement
  rules : TestSpaces.DerivRules.RulesOver ℂ
  clm : IsCLMSequence S
  cont : IsContinuousSeq S
  sesq : S.IsSesquilinear
  posSemidef : S.IsPosSemidef
  invariant : S.IsTranslationInvariant
theorem Standing.isPSD (h : Standing S) :
    FormCompletion.IsPosSemidefHermitianForm S.spanForm :=
  spanForm_isPosSemidef h.span h.sesq h.posSemidef
abbrev Standing.cls (h : Standing S) : admissibleSpan →ₗ[ℂ] S.HilbertCompletion :=
  classLin h.completion h.isPSD
abbrev Standing.shift (h : Standing S) (t : ℝ≥0) :
    admissibleSpan →ₗ[ℂ] admissibleSpan :=
  shiftLin h.comp h.span t
theorem Standing.form_shift_symm (h : Standing S) (t : ℝ≥0) (x y : admissibleSpan) :
    S.spanForm x (h.shift t y) = S.spanForm (h.shift t x) y := by
  obtain ⟨Φ, rfl⟩ := exists_eq_toAdmissibleSpan h.span x
  obtain ⟨Ψ, rfl⟩ := exists_eq_toAdmissibleSpan h.span y
  exact reflectionForm_shiftSeq h.comp h.sesq h.invariant t Φ Ψ
theorem sq_euclidNormVec_smul_time (t : ℝ) :
    TorusMetric.euclidNormVec (t • timeUnitVector) ^ 2 = t ^ 2 := by
  unfold TorusMetric.euclidNormVec
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [timeUnitVector, TimeAxis.timeIdx, Pi.single_apply]
theorem seminormAt_shiftActAt_le (hT : MotionComposition.CompositionTranslationStatement)
    {k N n : ℕ} (hk : 0 < k) (hn : n ≤ N) {f : FnOrScalar n}
    (hf : f ∈ flatOffPosTimeAt n) (t : ℝ) :
    seminormAt k (shiftActAt (t • timeUnitVector) f) ≤
      ENNReal.ofReal ((2 + 2 * (N : ℝ) * t ^ 2) ^ k) * seminormAt k f := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : 1 ≤ 2 + 2 * (N : ℝ) * t ^ 2 := by nlinarith [mul_nonneg hN0 (sq_nonneg t)]
  cases n with
  | zero =>
    refine le_mul_of_one_le_left' ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_pow₀ h1)
  | succ m =>
    have hs : f ∈ TestSpaces.schwartzSet (m + 1) := hf.1
    have h2 := (hT.1 (m + 1) k (Nat.succ_pos m) hk f hs).2 (t • timeUnitVector)
    have h3 : TestSpaces.weightedSeminorm k
        (shiftAct (t • timeUnitVector) (show Config (m + 1) → ℂ from f)) ≤
        ENNReal.ofReal (MotionComposition.translationFactor (m + 1) k
          (t • timeUnitVector)) * TestSpaces.weightedSeminorm k f := by
      rw [← SmoothSeparatedTuples.translateFun_eq_shiftAct]
      exact h2
    refine h3.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    unfold MotionComposition.translationFactor
    rw [sq_euclidNormVec_smul_time]
    have h4 : 2 + 2 * ((m + 1 : ℕ) : ℝ) * t ^ 2 ≤ 2 + 2 * (N : ℝ) * t ^ 2 := by
      have h5 : ((m + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hn
      nlinarith [sq_nonneg t]
    have hb0 : 0 ≤ 2 + 2 * ((m + 1 : ℕ) : ℝ) * t ^ 2 := by positivity
    calc (2 + 2 * ((m + 1 : ℕ) : ℝ) * t ^ 2) ^ ((k : ℝ) / 2)
        ≤ (2 + 2 * (N : ℝ) * t ^ 2) ^ ((k : ℝ) / 2) :=
          Real.rpow_le_rpow hb0 h4 (by positivity)
      _ ≤ (2 + 2 * (N : ℝ) * t ^ 2) ^ (k : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by
            have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
            linarith)
      _ = (2 + 2 * (N : ℝ) * t ^ 2) ^ k := Real.rpow_natCast _ _
theorem normSum_shiftLin_le {hT : MotionComposition.CompositionTranslationStatement}
    {hV : SpanOfAdmissible.Statement} {k N : ℕ} (hk : 0 < k) (t : ℝ≥0)
    (x : admissibleSpan) :
    normSum k N (shiftLin hT hV t x).1 ≤
      ENNReal.ofReal ((2 + 2 * (N : ℝ) * (t : ℝ) ^ 2) ^ k) * normSum k N x.1 := by
  obtain ⟨Φ, rfl⟩ := exists_eq_toAdmissibleSpan hV x
  rw [normSum, normSum, Finset.mul_sum]
  exact Finset.sum_le_sum fun q hq =>
    seminormAt_shiftActAt_le hT hk (Finset.mem_range.1 hq).le (Φ.1 q).2 t
theorem seminormAt_ne_top {k n : ℕ} (hk : 0 < k) {f : FnOrScalar n}
    (hf : f ∈ flatOffPosTimeAt n) : seminormAt k f ≠ ⊤ := by
  cases n with
  | zero => exact ENNReal.ofReal_ne_top
  | succ m => exact (hf.1.2 k hk).ne
theorem normSum_ne_top {hV : SpanOfAdmissible.Statement} {k : ℕ} (N : ℕ)
    (hk : 0 < k) (x : admissibleSpan) : normSum k N x.1 ≠ ⊤ := by
  obtain ⟨Φ, rfl⟩ := exists_eq_toAdmissibleSpan hV x
  exact (ENNReal.sum_lt_top.2 fun q _ => (seminormAt_ne_top hk (Φ.1 q).2).lt_top).ne
theorem norm_cls_shift_le (h : Standing S) (t : ℝ≥0) (x : admissibleSpan) :
    ‖h.cls (h.shift t x)‖ ≤ ‖h.cls x‖ := by
  obtain ⟨N, hN⟩ := exists_degree_bound h.span x
  obtain ⟨k, D, hk, hD, hb⟩ := spanForm_le_normSum h.span h.basic h.bounds h.ops h.clm h.cont h.sesq N
  set P := normSum k N x.1 with hPdef
  have hP : P ≠ ⊤ := normSum_ne_top (hV := h.span) N hk x
  have hsupp : ∀ (u : ℝ≥0) (q : ℕ), N ≤ q → (h.shift u x).1 q = zeroOfDegree q := by
    intro u q hq
    show shiftActAt _ (x.1 q) = _
    rw [hN q hq, shiftActAt_zeroOfDegree]
  have key : ∀ u : ℝ≥0, ‖h.cls (h.shift u x)‖ ^ 2 ≤
      ‖S.spanForm x (h.shift (u + u) x)‖ := by
    intro u
    rw [norm_classLin_sq]
    have e : S.spanForm (h.shift u x) (h.shift u x) =
        S.spanForm x (h.shift (u + u) x) := by
      rw [← shiftLin_shiftLin]
      exact (h.form_shift_symm u x (h.shift u x)).symm
    rw [e]
    exact Complex.re_le_norm _
  have hin : ∀ u : ℝ≥0, ‖S.spanForm x (h.shift u x)‖ ≤
      ‖h.cls x‖ * ‖h.cls (h.shift u x)‖ := by
    intro u
    rw [← inner_classLin (hC := h.completion) (hq := h.isPSD)]
    exact norm_inner_le_norm _ _
  have hbound : ∀ u : ℝ≥0, ‖S.spanForm x (h.shift u x)‖ ≤
      D.toReal * P.toReal * ((2 + 2 * (N : ℝ) * (u : ℝ) ^ 2) ^ k * P.toReal) := by
    intro u
    have hG : (0 : ℝ) ≤ (2 + 2 * (N : ℝ) * (u : ℝ) ^ 2) ^ k := by positivity
    have h1 := (hb x (h.shift u x) hN (hsupp u)).trans
      (mul_le_mul' le_rfl (normSum_shiftLin_le (hT := h.comp) (hV := h.span) hk u x))
    have hfin : D * P * (ENNReal.ofReal ((2 + 2 * (N : ℝ) * (u : ℝ) ^ 2) ^ k) * P) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top hD hP)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP)
    have h2 := (ENNReal.ofReal_le_iff_le_toReal hfin).1 h1
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hG] using h2
  set a : ℕ → ℝ := fun j => ‖h.cls (h.shift ((2 : ℝ≥0) ^ j * t) x)‖ with ha
  have hdouble : ∀ j : ℕ, (2 : ℝ≥0) ^ j * t + (2 : ℝ≥0) ^ j * t = (2 : ℝ≥0) ^ (j + 1) * t := by
    intro j
    rw [pow_succ]
    ring
  have h1 : ∀ j, a j ^ 2 ≤ ‖h.cls x‖ * a (j + 1) := by
    intro j
    have e := key ((2 : ℝ≥0) ^ j * t)
    rw [hdouble] at e
    exact e.trans (hin _)
  have h2 : ∀ j, a j ^ 2 ≤ (D.toReal * P.toReal * P.toReal *
      (2 + 8 * (N : ℝ) * (t : ℝ) ^ 2) ^ k) * ((2 : ℝ) ^ j) ^ (2 * k) := by
    intro j
    have e := (key ((2 : ℝ≥0) ^ j * t)).trans (hbound _)
    refine e.trans ?_
    have hDP : 0 ≤ D.toReal * P.toReal * P.toReal := by positivity
    have hu : (((2 : ℝ≥0) ^ j * t + (2 : ℝ≥0) ^ j * t : ℝ≥0) : ℝ) = 2 * ((2 : ℝ) ^ j * (t : ℝ)) := by
      push_cast
      ring
    rw [hu]
    have h4 : (1 : ℝ) ≤ ((2 : ℝ) ^ j) ^ 2 := one_le_pow₀ (one_le_pow₀ (by norm_num))
    have hbase : 2 + 2 * (N : ℝ) * (2 * ((2 : ℝ) ^ j * (t : ℝ))) ^ 2 ≤
        ((2 : ℝ) ^ j) ^ 2 * (2 + 8 * (N : ℝ) * (t : ℝ) ^ 2) := by
      have e5 : 2 + 2 * (N : ℝ) * (2 * ((2 : ℝ) ^ j * (t : ℝ))) ^ 2 =
          2 + ((2 : ℝ) ^ j) ^ 2 * (8 * (N : ℝ) * (t : ℝ) ^ 2) := by ring
      rw [e5, mul_add]
      nlinarith
    have hpow : (2 + 2 * (N : ℝ) * (2 * ((2 : ℝ) ^ j * (t : ℝ))) ^ 2) ^ k ≤
        ((2 : ℝ) ^ j) ^ (2 * k) * (2 + 8 * (N : ℝ) * (t : ℝ) ^ 2) ^ k := by
      rw [pow_mul, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hbase k
    calc D.toReal * P.toReal * ((2 + 2 * (N : ℝ) * (2 * ((2 : ℝ) ^ j * (t : ℝ))) ^ 2) ^ k * P.toReal)
        = (D.toReal * P.toReal * P.toReal) *
            (2 + 2 * (N : ℝ) * (2 * ((2 : ℝ) ^ j * (t : ℝ))) ^ 2) ^ k := by ring
      _ ≤ (D.toReal * P.toReal * P.toReal) *
            (((2 : ℝ) ^ j) ^ (2 * k) * (2 + 8 * (N : ℝ) * (t : ℝ) ^ 2) ^ k) :=
          mul_le_mul_of_nonneg_left hpow hDP
      _ = _ := by ring
  have h3 := le_of_sq_le_mul_succ (norm_nonneg (h.cls x)) h1 h2
  simpa [ha] using h3
theorem tendsto_zero_of_ofReal_sq_le {ι : Type*} {l : Filter ι} {u : ι → ℝ} {g : ι → ℝ≥0∞}
    (hu : ∀ i, 0 ≤ u i) (hg : Tendsto g l (𝓝 0))
    (h : ∀ i, ENNReal.ofReal (u i ^ 2) ≤ g i) : Tendsto u l (𝓝 0) := by
  have h1 : Tendsto (fun i => ENNReal.ofReal (u i ^ 2)) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg (fun _ => bot_le) h
  have h2 : Tendsto (fun i => u i ^ 2) l (𝓝 0) := by
    have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _)] using h3
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  simpa [Function.comp_def, Real.sqrt_sq (hu _)] using h3
theorem tendsto_cls (h : Standing S) {ι : Type*} {l : Filter ι}
    {y : ι → admissibleSpan} {x : admissibleSpan} {k N : ℕ} {D : ℝ≥0∞}
    (hD : D ≠ ⊤)
    (hb : ∀ x y : admissibleSpan,
      (∀ q, N ≤ q → x.1 q = zeroOfDegree q) → (∀ q, N ≤ q → y.1 q = zeroOfDegree q) →
      ENNReal.ofReal ‖S.spanForm x y‖ ≤
        D * normSum k N x.1 * normSum k N y.1)
    (hsupp : ∀ i q, N ≤ q → (y i - x).1 q = zeroOfDegree q)
    (hsum : Tendsto (fun i => normSum k N (y i - x).1) l (𝓝 0)) :
    Tendsto (fun i => h.cls (y i)) l (𝓝 (h.cls x)) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hg : Tendsto (fun i => D * normSum k N (y i - x).1 * normSum k N (y i - x).1) l
      (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (a := D) hsum (Or.inr hD)
    rw [mul_zero] at h1
    have h2 := ENNReal.Tendsto.mul h1 (Or.inr ENNReal.zero_ne_top) hsum
      (Or.inr ENNReal.zero_ne_top)
    rwa [mul_zero] at h2
  refine tendsto_zero_of_ofReal_sq_le (fun _ => norm_nonneg _) hg fun i => ?_
  rw [← map_sub, norm_classLin_sq]
  exact (ENNReal.ofReal_le_ofReal (Complex.re_le_norm _)).trans
    (hb _ _ (hsupp i) (hsupp i))
theorem tendsto_seminormAt_shiftActAt_sub
    (hR : TestSpaces.DerivRules.RulesOver ℂ) {k n : ℕ}
    {f : FnOrScalar n} (hf : f ∈ flatOffPosTimeAt n) :
    Tendsto (fun t : ℝ≥0 => seminormAt k (shiftActAt ((t : ℝ) • timeUnitVector) f - f))
      (𝓝 0) (𝓝 0) := by
  cases n with
  | zero =>
    have e : ∀ t : ℝ≥0, seminormAt k (shiftActAt ((t : ℝ) • timeUnitVector) f - f) = 0 :=
      fun t => by
        show ENNReal.ofReal ‖(show ℂ from f) - (show ℂ from f)‖ = 0
        rw [sub_self (G := ℂ)]
        simp
    simp only [e]
    exact tendsto_const_nhds
  | succ m =>
    have h1 := TestSpaces.ShiftEstimates.tendsto_weightedSeminorm_shiftBy hR hf.1.1
      TimeAxis.timeIdx (k := k) (hf.1.2 (k + 1) (Nat.succ_pos k)).ne
    refine h1.congr fun t => ?_
    have e1 : ∀ φ : Config (m + 1) → ℂ,
        TestSpaces.ShiftEstimates.shiftBy ((t : ℝ) • Pi.single TimeAxis.timeIdx (1 : ℝ)) φ =
          shiftAct ((t : ℝ) • timeUnitVector) φ := fun φ => by
      funext x
      rw [shiftAct_apply]
      rfl
    exact congrArg (fun g : Config (m + 1) → ℂ =>
      TestSpaces.weightedSeminorm k (g - (show Config (m + 1) → ℂ from f))) (e1 f)
theorem tendsto_cls_shift (h : Standing S) (x : admissibleSpan) :
    Tendsto (fun t => h.cls (h.shift t x)) (𝓝 0) (𝓝 (h.cls x)) := by
  obtain ⟨N, hN⟩ := exists_degree_bound h.span x
  obtain ⟨k, D, hk, hD, hb⟩ := spanForm_le_normSum h.span h.basic h.bounds h.ops h.clm h.cont h.sesq N
  obtain ⟨Φ, rfl⟩ := exists_eq_toAdmissibleSpan h.span x
  refine tendsto_cls h hD hb (fun t q hq => ?_) ?_
  · show shiftActAt _ (Φ.1 q).1 - (Φ.1 q).1 = _
    have h0 : (Φ.1 q).1 = zeroOfDegree q := hN q hq
    rw [h0, shiftActAt_zeroOfDegree, sub_self, zero_eq_zeroOfDegree]
  · have h1 := tendsto_finsetSum (Finset.range N) fun q (_ : q ∈ Finset.range N) =>
      tendsto_seminormAt_shiftActAt_sub (k := k) h.rules (Φ.1 q).2
    simp only [Finset.sum_const_zero] at h1
    exact h1
theorem exists_contractive_extension (h : Standing S) (t : ℝ≥0) :
    ∃ B : S.HilbertCompletion →L[ℂ] S.HilbertCompletion,
      (∀ x, B (h.cls x) = h.cls (h.shift t x)) ∧ ‖B‖ ≤ 1 := by
  obtain ⟨-, -, hM⟩ := h.completion _ _ h.isPSD
  have hR : ∀ F, ‖(h.cls ∘ₗ h.shift t) F‖ ≤ 1 *
      FormCompletion.seminormOfForm S.spanForm F := by
    intro F
    rw [one_mul, ← norm_classLin_eq (hC := h.completion) (hq := h.isPSD)]
    exact norm_cls_shift_le h t F
  obtain ⟨⟨B, hB, -⟩, hall⟩ := hM S.HilbertCompletion 1 (h.cls ∘ₗ h.shift t) zero_le_one hR
  exact ⟨B, hB, (hall B hB).1⟩
end Contractions
open ProjectionMeasures OneLoopNotation
section Family
variable {S : FlatSequence}
theorem isTimeShiftContraction_of (h : Standing S) {t : ℝ≥0}
    {B : S.HilbertCompletion →L[ℂ] S.HilbertCompletion}
    (hB : ∀ x, B (h.cls x) = h.cls (h.shift t x)) (hn : ‖B‖ ≤ 1) :
    S.IsTimeShiftContraction t B :=
  ⟨hn, fun Φ _ => hB (toAdmissibleSpan Φ)⟩
theorem timeShiftFamily_spec (h : Standing S) (t : ℝ≥0) :
    S.IsTimeShiftContraction t (S.timeShiftFamily t) := by
  obtain ⟨B, hB, hn⟩ := exists_contractive_extension h t
  exact Classical.epsilon_spec (p := S.IsTimeShiftContraction t)
    ⟨B, isTimeShiftContraction_of h hB hn⟩
theorem timeShiftFamily_cls (h : Standing S) (t : ℝ≥0) (x : admissibleSpan) :
    S.timeShiftFamily t (h.cls x) = h.cls (h.shift t x) := by
  obtain ⟨Φ, rfl⟩ := exists_eq_toAdmissibleSpan h.span x
  exact (timeShiftFamily_spec h t).apply_admClass Φ (h.shift t (toAdmissibleSpan Φ)).2
theorem norm_timeShiftFamily_le (h : Standing S) (t : ℝ≥0) : ‖S.timeShiftFamily t‖ ≤ 1 :=
  (timeShiftFamily_spec h t).contractive
end Family
section Ordered
variable {S : FlatSequence}
theorem mem_increasingPositiveTimes_of_sub {n : ℕ} {t : ℝ} (ht : 0 ≤ t) {x : Config n}
    (hx : (fun i => x i - t • timeUnitVector) ∈ TestSpaces.increasingPositiveTimes n) :
    x ∈ TestSpaces.increasingPositiveTimes n := by
  have htime : ∀ i, TestSpaces.timeCoord (fun i => x i - t • timeUnitVector) i =
      TestSpaces.timeCoord x i - t := fun i => by
    simp [TestSpaces.timeCoord, timeUnitVector, TimeAxis.timeIdx]
  refine ⟨fun i j hij => ?_, fun hn => ?_⟩
  · have h1 : TestSpaces.timeCoord (fun i => x i - t • timeUnitVector) i <
        TestSpaces.timeCoord (fun i => x i - t • timeUnitVector) j := hx.1 hij
    rw [htime, htime] at h1
    linarith
  · have h1 := hx.2 hn
    rw [htime] at h1
    linarith
theorem shiftSeq_isIncreasing (hT : MotionComposition.CompositionTranslationStatement) (t : ℝ≥0)
    {Φ : AdmissibleSeq}
    (hΦ : TestSpaces.IsIncreasingPositiveTimeSeq (gradedMembers (seqValues Φ))) :
    TestSpaces.IsIncreasingPositiveTimeSeq
      (gradedMembers (seqValues (shiftSeq hT t Φ))) := by
  refine ⟨hΦ.1.subset fun q hq h0 => hq ?_, fun q => ⟨((shiftSeq hT t Φ).1 (q + 1)).2.1, ?_⟩⟩
  · have h1 : (Φ.1 (q + 1)).1 = zeroOfDegree (q + 1) := h0
    show shiftActAt _ (Φ.1 (q + 1)).1 = _
    rw [h1, shiftActAt_zeroOfDegree]
    rfl
  · intro x hx
    have h1 := (hΦ.2 q).2 (fun i => x i - (t : ℝ) • timeUnitVector)
      (fun h2 => hx (mem_increasingPositiveTimes_of_sub t.2 h2))
    exact show shiftAct ((t : ℝ) • timeUnitVector)
        (show Config (q + 1) → ℂ from (Φ.1 (q + 1)).1) x = 0 from by
      rw [shiftAct_apply]
      exact h1
theorem mem_schwartzOnIncreasing_of_smooth (hF : TestSpaces.Elementary.BasicProperties) {q : ℕ}
    {φ : Config (q + 1) → ℂ}
    (hφ : φ ∈ (TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes (q + 1)) :
      Set (Config (q + 1) → ℂ))) : φ ∈ TestSpaces.schwartzOnIncreasingPositiveTimes (q + 1) :=
  ⟨((hF (q + 1) (Nat.succ_pos q)).2.2.1 _ (TestSpaces.isOpen_increasingPositiveTimes _) φ hφ).1,
    fun _ hx => image_eq_zero_of_notMem_tsupport fun hh => hx (hφ.2.2 hh)⟩
theorem mem_flatOffPosTimeAt_of_smooth (hF : TestSpaces.Elementary.BasicProperties) {q : ℕ}
    {φ : Config (q + 1) → ℂ}
    (hφ : φ ∈ (TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes (q + 1)) :
      Set (Config (q + 1) → ℂ))) : φ ∈ flatOffPosTimeAt (q + 1) := by
  obtain ⟨h1, ⟨h2, -, h3⟩, -⟩ :=
    (hF (q + 1) (Nat.succ_pos q)).2.2.1 _ (TestSpaces.isOpen_increasingPositiveTimes _) φ hφ
  have hopen : IsOpen (TestSpaces.positiveTimeLocus (q + 1)) :=
    (hF (q + 1) (Nat.succ_pos q)).2.1.2.1
  have h4 : φ ∈ SchwartzAxioms.positiveTimeSchwartz (q + 1) :=
    ⟨h1, h2, hopen, fun x hx => h3 x fun hV =>
      hx (TestSpaces.increasingPositiveTimes_subset_positiveTimeLocus _ hV)⟩
  rw [SchwartzAxioms.positiveTimeSchwartz_eq] at h4
  exact h4
theorem smoothCompactSupp_add {n : ℕ} {V : Set (Config n)} {φ ψ : Config n → ℂ}
    (hφ : φ ∈ (TestSpaces.smoothCompactSupp V : Set (Config n → ℂ)))
    (hψ : ψ ∈ (TestSpaces.smoothCompactSupp V : Set (Config n → ℂ))) :
    φ + ψ ∈ (TestSpaces.smoothCompactSupp V : Set (Config n → ℂ)) :=
  ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, (tsupport_add _ _).trans (Set.union_subset hφ.2.2 hψ.2.2)⟩
theorem smoothCompactSupp_smul {n : ℕ} {V : Set (Config n)} (c : ℂ) {φ : Config n → ℂ}
    (hφ : φ ∈ (TestSpaces.smoothCompactSupp V : Set (Config n → ℂ))) :
    c • φ ∈ (TestSpaces.smoothCompactSupp V : Set (Config n → ℂ)) :=
  ⟨contDiff_const.smul hφ.1, hφ.2.1.smul_left,
    (tsupport_smul_subset_right (fun _ => c) _).trans hφ.2.2⟩
theorem smoothCompactSupp_zero {n : ℕ} {V : Set (Config n)} :
    (0 : Config n → ℂ) ∈ (TestSpaces.smoothCompactSupp V : Set (Config n → ℂ)) := by apply _root_.YangMills.Construction.TestSpaces.OffDiagonal.smoothCompactSupp_zero_mem <;> assumption
def componentFn (x : admissibleSpan) (q : ℕ) : Config (q + 1) → ℂ := x.1 (q + 1)
theorem componentFn_add (x y : admissibleSpan) (q : ℕ) :
    componentFn (x + y) q = componentFn x q + componentFn y q := rfl
theorem componentFn_smul (c : ℂ) (x : admissibleSpan) (q : ℕ) :
    componentFn (c • x) q = c • componentFn x q := rfl
theorem componentFn_zero (q : ℕ) :
    componentFn (0 : admissibleSpan) q = 0 := rfl
def smoothSubmodule : Submodule ℂ admissibleSpan where
  carrier := {x | ∀ q : ℕ, componentFn x q ∈
    (TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes (q + 1)) :
      Set (Config (q + 1) → ℂ))}
  add_mem' := fun {x y} hx hy q => by
    rw [componentFn_add]
    exact smoothCompactSupp_add (hx q) (hy q)
  zero_mem' := fun q => by
    rw [componentFn_zero]
    exact smoothCompactSupp_zero
  smul_mem' := fun c x hx q => by
    rw [componentFn_smul]
    exact smoothCompactSupp_smul c (hx q)
def approxSeq (Φ Φ₀ : AdmissibleSeq) (N : ℕ)
    (b : (q : ℕ) → flatOffPosTimeAt (q + 1)) : PosTimeSeq
  | 0 => Φ.1 0
  | q + 1 => if q + 1 < N then b q else Φ₀.1 (q + 1)
theorem eq_zeroOfDegree_of_zero {Φ₀ : AdmissibleSeq} (h0 : (0 : admissibleSpan) =
    toAdmissibleSpan Φ₀) (q : ℕ) : (Φ₀.1 q).1 = zeroOfDegree q := by
  have h1 := congrArg (fun x : admissibleSpan => x.1 q) h0
  exact h1.symm.trans (zero_eq_zeroOfDegree q)
theorem approxSeq_isFinitelySupported {Φ Φ₀ : AdmissibleSeq}
    (h0 : ∀ q, (Φ₀.1 q).1 = zeroOfDegree q) (N : ℕ)
    (b : (q : ℕ) → flatOffPosTimeAt (q + 1)) :
    PosTimeSeq.IsFinitelySupported (approxSeq Φ Φ₀ N b) := by
  refine (Set.finite_Iic N).subset fun q hq => ?_
  by_contra hN
  have hN' : N < q := not_le.1 hN
  apply hq
  cases q with
  | zero => omega
  | succ m =>
    have e : approxSeq Φ Φ₀ N b (m + 1) = Φ₀.1 (m + 1) := if_neg (by omega)
    rw [e]
    exact h0 _
theorem cls_mem_closure_smooth (h : Standing S) (hA : TestSpaces.OrderedApprox.Statement)
    {Φ : AdmissibleSeq}
    (hΦ : TestSpaces.IsIncreasingPositiveTimeSeq (gradedMembers (seqValues Φ))) :
    h.cls (toAdmissibleSpan Φ) ∈ closure (h.cls '' (smoothSubmodule : Set admissibleSpan)) := by
  obtain ⟨N, hN⟩ := exists_degree_bound h.span (toAdmissibleSpan Φ)
  obtain ⟨k, D, hk, hD, hb⟩ := spanForm_le_normSum h.span h.basic h.bounds h.ops h.clm h.cont h.sesq N
  obtain ⟨Φ₀, h0⟩ := exists_eq_toAdmissibleSpan h.span 0
  have hz := eq_zeroOfDegree_of_zero h0
  have hap := fun q => (hA (q + 1) k (Nat.succ_pos q) hk).1 _ (hΦ.2 q)
  choose a ha hlim using hap
  set Ψ : ℕ → AdmissibleSeq := fun j => ⟨approxSeq Φ Φ₀ N
    (fun q => ⟨a q j, mem_flatOffPosTimeAt_of_smooth h.basic (ha q j)⟩),
      approxSeq_isFinitelySupported hz N _⟩ with hΨ
  set y : ℕ → admissibleSpan := fun j => toAdmissibleSpan (Ψ j) with hy
  set x := toAdmissibleSpan Φ with hx
  have hmem : ∀ j, y j ∈ smoothSubmodule := by
    intro j q
    by_cases hq : q + 1 < N
    · have e : (approxSeq Φ Φ₀ N
          (fun q => ⟨a q j, mem_flatOffPosTimeAt_of_smooth h.basic (ha q j)⟩) (q + 1)) =
          ⟨a q j, mem_flatOffPosTimeAt_of_smooth h.basic (ha q j)⟩ := if_pos hq
      have e2 : componentFn (y j) q = a q j := by
        show ((Ψ j).1 (q + 1)).1 = _
        simp only [hΨ]
        rw [e]
      rw [e2]
      exact ha q j
    · have e : (approxSeq Φ Φ₀ N
          (fun q => ⟨a q j, mem_flatOffPosTimeAt_of_smooth h.basic (ha q j)⟩) (q + 1)) =
          Φ₀.1 (q + 1) := if_neg hq
      have e2 : componentFn (y j) q = 0 := by
        show ((Ψ j).1 (q + 1)).1 = _
        simp only [hΨ]
        rw [e, hz]
        rfl
      rw [e2]
      exact smoothCompactSupp_zero
  have hlimit : Tendsto (fun j => h.cls (x - y j)) atTop (𝓝 (h.cls 0)) := by
    refine tendsto_cls h (x := 0) (y := fun j => x - y j) hD hb ?_ ?_
    · intro j q hq
      rw [sub_zero]
      show x.1 q - (y j).1 q = _
      rw [hN q hq]
      cases q with
      | zero =>
        have e : (y j).1 0 = x.1 0 := rfl
        rw [e, hN 0 hq, sub_self, zero_eq_zeroOfDegree]
      | succ m =>
        have e : (approxSeq Φ Φ₀ N
            (fun q => ⟨a q j, mem_flatOffPosTimeAt_of_smooth h.basic (ha q j)⟩) (m + 1)) =
            Φ₀.1 (m + 1) := if_neg (by omega)
        have e2 : (y j).1 (m + 1) = zeroOfDegree (m + 1) := by
          show ((Ψ j).1 (m + 1)).1 = _
          simp only [hΨ]
          rw [e, hz]
        rw [e2, sub_self, zero_eq_zeroOfDegree]
    · have hterm : ∀ q ∈ Finset.range N, Tendsto
          (fun j => seminormAt k ((x - y j - 0).1 q)) atTop (𝓝 0) := by
        intro q hq
        have hq' := Finset.mem_range.1 hq
        cases q with
        | zero =>
          have e : ∀ j, seminormAt k ((x - y j - 0).1 0) = 0 := fun j => by
            rw [sub_zero]
            show ENNReal.ofReal ‖(show ℂ from x.1 0) - (show ℂ from x.1 0)‖ = 0
            rw [sub_self (G := ℂ)]
            simp
          simp only [e]
          exact tendsto_const_nhds
        | succ m =>
          refine (hlim m).congr fun j => ?_
          have e : (approxSeq Φ Φ₀ N
              (fun q => ⟨a q j, mem_flatOffPosTimeAt_of_smooth h.basic (ha q j)⟩) (m + 1)) =
              ⟨a m j, mem_flatOffPosTimeAt_of_smooth h.basic (ha m j)⟩ := if_pos hq'
          have e2 : (y j).1 (m + 1) = a m j := by
            show ((Ψ j).1 (m + 1)).1 = _
            simp only [hΨ]
            rw [e]
          rw [sub_zero]
          show _ = TestSpaces.weightedSeminorm k (x.1 (m + 1) - (y j).1 (m + 1))
          rw [e2]
          rfl
      have h1 := tendsto_finsetSum (Finset.range N) hterm
      simp only [Finset.sum_const_zero] at h1
      exact h1
  rw [map_zero] at hlimit
  have hconv : Tendsto (fun j => h.cls (y j)) atTop (𝓝 (h.cls x)) := by
    have h2 := (tendsto_const_nhds (x := h.cls x)).sub hlimit
    rw [sub_zero] at h2
    refine h2.congr fun j => ?_
    rw [map_sub]
    abel
  exact mem_closure_of_tendsto hconv (Eventually.of_forall fun j => ⟨y j, hmem j, rfl⟩)
end Ordered
section One
variable {S : FlatSequence}
def oneSeq (Φ₀ : AdmissibleSeq) : PosTimeSeq
  | 0 => ⟨(1 : ℂ), Set.mem_univ _⟩
  | q + 1 => Φ₀.1 (q + 1)
theorem oneSeq_isFinitelySupported {Φ₀ : AdmissibleSeq}
    (hz : ∀ q, (Φ₀.1 q).1 = zeroOfDegree q) : PosTimeSeq.IsFinitelySupported (oneSeq Φ₀) := by
  refine (Set.finite_singleton 0).subset fun q hq => ?_
  cases q with
  | zero => exact rfl
  | succ m => exact absurd (hz (m + 1)) hq
def admissibleOneSeq {Φ₀ : AdmissibleSeq} (hz : ∀ q, (Φ₀.1 q).1 = zeroOfDegree q) :
    AdmissibleSeq :=
  ⟨oneSeq Φ₀, oneSeq_isFinitelySupported hz⟩
theorem seqValues_admissibleOneSeq {Φ₀ : AdmissibleSeq} (hz : ∀ q, (Φ₀.1 q).1 = zeroOfDegree q) :
    seqValues (admissibleOneSeq hz) = vacuumSeq := by
  funext q
  cases q with
  | zero => rfl
  | succ m => exact hz (m + 1)
theorem admissibleOneSeq_isIncreasing {Φ₀ : AdmissibleSeq}
    (hz : ∀ q, (Φ₀.1 q).1 = zeroOfDegree q) :
    TestSpaces.IsIncreasingPositiveTimeSeq
      (gradedMembers (seqValues (admissibleOneSeq hz))) := by
  have hzero : ∀ q, TestSpaces.succComponent
      (gradedMembers (seqValues (admissibleOneSeq hz))) q = 0 := fun q => hz (q + 1)
  refine ⟨Set.finite_empty.subset fun q hq => hq (hzero q), fun q => ⟨?_, fun x _ => ?_⟩⟩
  · exact (Φ₀.1 (q + 1)).2.1
  · rw [hzero]
    rfl
theorem reflectionForm_admissibleOneSeq (hseq : IsCLMSequence S)
    (hs : S.IsSesquilinear) {Φ₀ : AdmissibleSeq}
    (hz : ∀ q, (Φ₀.1 q).1 = zeroOfDegree q) :
    S.reflectionForm (admissibleOneSeq hz) (admissibleOneSeq hz) = 1 := by
  have h1 : S.reflectionForm (admissibleOneSeq hz) (admissibleOneSeq hz) =
      S.evalAt (tensorAt (flipConjAt ((admissibleOneSeq hz).1 0).1)
        ((admissibleOneSeq hz).1 0).1) := by
    refine finsum_eq_single (fun p : ℕ × ℕ => S.evalAt (tensorAt
      (flipConjAt ((admissibleOneSeq hz).1 p.1).1) ((admissibleOneSeq hz).1 p.2).1))
      (0, 0) ?_
    rintro ⟨q, q'⟩ hp
    refine evalAt_eq_zero hseq (hs.1 _ _ q q') ?_
    cases q with
    | succ m =>
      have e : ((admissibleOneSeq hz).1 (m + 1)).1 = zeroOfDegree (m + 1) := hz (m + 1)
      show tensorAt (flipConjAt ((admissibleOneSeq hz).1 (m + 1)).1) _ = _
      rw [e, flipConjAt_zeroOfDegree, tensorAt_zeroOfDegree_left]
    | zero =>
      cases q' with
      | zero => exact absurd rfl hp
      | succ m =>
        have e : ((admissibleOneSeq hz).1 (m + 1)).1 = zeroOfDegree (m + 1) := hz (m + 1)
        show tensorAt _ ((admissibleOneSeq hz).1 (m + 1)).1 = _
        rw [e, tensorAt_zeroOfDegree_right]
  rw [h1]
  have e1 : S.evalAt (tensorAt (flipConjAt ((admissibleOneSeq hz).1 0).1)
      ((admissibleOneSeq hz).1 0).1) = S.evalAt (n := 0)
        (smulAt (conj (1 : ℂ)) (show FnOrScalar 0 from (1 : ℂ))) :=
    evalAt_cast (Nat.zero_add 0).symm _
  rw [e1, S.evalAt_of_mem (Set.mem_univ _), hseq.1]
  show conj (1 : ℂ) * (1 : ℂ) = 1
  simp
theorem shiftLin_admissibleOneSeq {hT : MotionComposition.CompositionTranslationStatement}
    {hV : SpanOfAdmissible.Statement} {Φ₀ : AdmissibleSeq}
    (hz : ∀ q, (Φ₀.1 q).1 = zeroOfDegree q) (t : ℝ≥0) :
    shiftLin hT hV t (toAdmissibleSpan (admissibleOneSeq hz)) =
      toAdmissibleSpan (admissibleOneSeq hz) := by
  refine Subtype.ext (funext fun q => ?_)
  cases q with
  | zero => rfl
  | succ m =>
    have e : ((admissibleOneSeq hz).1 (m + 1)).1 = zeroOfDegree (m + 1) := hz (m + 1)
    show shiftActAt _ ((admissibleOneSeq hz).1 (m + 1)).1 = ((admissibleOneSeq hz).1 (m + 1)).1
    rw [e, shiftActAt_zeroOfDegree]
end One
section Lemma
variable {S : FlatSequence}
theorem image_smoothSubmodule (h : Standing S) :
    h.cls '' (smoothSubmodule : Set admissibleSpan) = S.smoothPositiveTimeClasses := by
  ext χ
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨Φ, rfl⟩ := exists_eq_toAdmissibleSpan h.span x
    exact ⟨Φ, hx, rfl⟩
  · rintro ⟨Φ, hΦ, rfl⟩
    exact ⟨toAdmissibleSpan Φ, hΦ, rfl⟩
theorem smoothPositiveTimeClasses_subset (h : Standing S) :
    S.smoothPositiveTimeClasses ⊆ S.positiveTimeClasses := by
  rintro χ ⟨Φ, hΦ, rfl⟩
  refine ⟨Φ, ⟨?_, fun q => mem_schwartzOnIncreasing_of_smooth h.basic (hΦ q)⟩, rfl⟩
  refine (Set.Finite.preimage (Nat.succ_injective.injOn) Φ.2).subset fun q hq h0 => hq ?_
  exact h0
theorem hasTimeShiftSemigroup (h : Standing S) (hA : TestSpaces.OrderedApprox.Statement) :
    S.HasTimeShiftSemigroup := by
  have hd : DenseRange h.cls := denseRange_classLin
  have hB := timeShiftFamily_cls h
  have hn := norm_timeShiftFamily_le h
  have hτ : ∀ s t x, h.shift s (h.shift t x) = h.shift (s + t) x := shiftLin_shiftLin
  have hτ0 : ∀ x, h.shift 0 x = x := shiftLin_zero
  obtain ⟨Φ₀, h0⟩ := exists_eq_toAdmissibleSpan h.span 0
  have hz := eq_zeroOfDegree_of_zero h0
  refine
    { hermitian :=
        { add_left := h.isPSD.add_left
          smul_left := h.isPSD.smul_left
          add_right := h.isPSD.add_right
          smul_right := h.isPSD.smul_right
          conj_symm := h.isPSD.hermitian }
      shift_symm := fun Φ Ψ t ht =>
        reflectionForm_shiftSeq h.comp h.sesq h.invariant ⟨t, ht⟩ Φ Ψ
      nonexpanding := fun Φ t ht => ?_
      shiftOp_spec := fun t ht => timeShiftFamily_spec h ⟨t, ht⟩
      semigroup := fun s t => mul_eq_of_dense hd hB hτ s t
      strongCont := fun χ =>
        continuous_of_dense hd hB hn hτ hτ0 (tendsto_cls_shift h) χ
      symmetric := fun t φ ψ => inner_symm_of_dense hd hB t (fun x y => ?_) φ ψ
      contractive := hn
      family_zero := eq_id_of_dense hd hB hτ0
      vacuum := ?_
      mapsTo_positiveTimeSubspace := ?_
      positiveTimeSubspace_eq_closure := ?_ }
  · have h1 := norm_cls_shift_le h ⟨t, ht⟩ (toAdmissibleSpan Φ)
    rw [norm_classLin_eq, norm_classLin_eq] at h1
    exact h1
  · rw [inner_classLin, inner_classLin]
    exact h.form_shift_symm t x y
  · refine ⟨admissibleOneSeq hz, seqValues_admissibleOneSeq hz, ?_, ?_, fun t => ?_⟩
    · exact Submodule.le_topologicalClosure _
        (Submodule.subset_span ⟨_, admissibleOneSeq_isIncreasing hz, rfl⟩)
    · have h1 : ‖h.cls (toAdmissibleSpan (admissibleOneSeq hz))‖ ^ 2 = 1 := by
        rw [norm_classLin_sq]
        have e : S.spanForm (toAdmissibleSpan (admissibleOneSeq hz))
            (toAdmissibleSpan (admissibleOneSeq hz)) = 1 :=
          reflectionForm_admissibleOneSeq h.clm h.sesq hz
        rw [e]
        rfl
      have h2 := (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (h1.trans (one_pow 2).symm)
      exact h2
    · have e := hB t (toAdmissibleSpan (admissibleOneSeq hz))
      rw [shiftLin_admissibleOneSeq] at e
      exact e
  · intro t χ hχ
    have hmap : (Submodule.span ℂ S.positiveTimeClasses).map
        (S.timeShiftFamily t : S.HilbertCompletion →ₗ[ℂ] S.HilbertCompletion) ≤
        Submodule.span ℂ S.positiveTimeClasses := by
      refine Submodule.map_span_le _ _ _ |>.2 ?_
      rintro _ ⟨Φ, hΦ, rfl⟩
      refine Submodule.subset_span ⟨shiftSeq h.comp t Φ, shiftSeq_isIncreasing h.comp t hΦ, ?_⟩
      exact hB t (toAdmissibleSpan Φ)
    have hχ' : χ ∈ closure ((Submodule.span ℂ S.positiveTimeClasses :
        Submodule ℂ S.HilbertCompletion) : Set S.HilbertCompletion) := hχ
    exact map_mem_closure (S.timeShiftFamily t).continuous hχ'
      (fun y hy => hmap ⟨y, hy, rfl⟩)
  · rw [ComplexHilbert.seqClosureOf_eq_closure, ← image_smoothSubmodule h]
    set W := smoothSubmodule.map h.cls with hW
    have hWc : (W : Set S.HilbertCompletion) =
        h.cls '' (smoothSubmodule : Set admissibleSpan) := Submodule.map_coe _ _
    refine Set.Subset.antisymm ?_ ?_
    · have hspan : Submodule.span ℂ S.positiveTimeClasses ≤ W.topologicalClosure := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨Φ, hΦ, rfl⟩
        have h1 := cls_mem_closure_smooth h hA hΦ
        rw [← hWc] at h1
        exact h1
      have h2 : (S.positiveTimeSubspace : Set S.HilbertCompletion) =
          closure (Submodule.span ℂ S.positiveTimeClasses : Set S.HilbertCompletion) :=
        Submodule.topologicalClosure_coe _
      rw [h2, ← hWc]
      refine closure_minimal (fun y hy => hspan hy) ?_
      exact isClosed_closure
    · refine closure_minimal ?_ (Submodule.isClosed_topologicalClosure _)
      rw [image_smoothSubmodule h]
      exact fun y hy => Submodule.le_topologicalClosure _
        (Submodule.subset_span (smoothPositiveTimeClasses_subset h hy))
theorem timeShiftSemigroupStatement_holds (hK : SesquilinearPosSemidefStatement)
    (hV : SpanOfAdmissible.Statement) (hC : FormCompletion.FormCompletionIsHilbertSpace)
    (hT : MotionComposition.CompositionTranslationStatement)
    (hF : TestSpaces.Elementary.BasicProperties)
    (hO : TestFunctionOps.OperationsStatement)
    (hB : TestSpaces.TestSpaceFacts.Statement)
    (hA : TestSpaces.OrderedApprox.Statement)
    (hR : TestSpaces.DerivRules.Combined) :
    TimeShiftSemigroupStatement := fun S h1 h2 h3 h4 =>
  hasTimeShiftSemigroup ⟨hT, hV, hC, hF, hB, hO, hR.2.1, ⟨h1.1, h2⟩, h2, (hK S ⟨h1.1, h2⟩).1,
    (hK S ⟨h1.1, h2⟩).2 h3, h4⟩ hA
end Lemma
end ConfigSpace.TimeShiftProof
end YangMills.Construction
end
