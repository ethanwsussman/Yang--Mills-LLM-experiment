import YangMills.Construction.ColdStepAtMirrorFrames.SumsAgainstFlatResponsesProof
import YangMills.Construction.ReflectionPositivity.CountingAgainstTheRate
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
namespace ShellCount
open Finset
open scoped Real
variable {μ : Fin 4}
def supIdx (w : EnergyMomentum.orthLattice μ) : ℕ :=
  Finset.univ.sup fun l => (w.1 l).natAbs
theorem supNormCoord_eq_supIdx (w : EnergyMomentum.orthLattice μ) :
    EnergyMomentum.supNormCoord (fun l => (w.1 l : ℝ)) = (supIdx w : ℝ) := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun l _ => ?_
    have h : (w.1 l).natAbs ≤ supIdx w :=
      Finset.le_sup (f := fun l => (w.1 l).natAbs) (Finset.mem_univ l)
    have h' : ((w.1 l).natAbs : ℝ) ≤ (supIdx w : ℝ) := by exact_mod_cast h
    have h2 : |(w.1 l : ℝ)| = ((w.1 l).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2]
    exact h'
  · obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun l => (w.1 l).natAbs)
    have h2 : |(w.1 l : ℝ)| = ((w.1 l).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have h3 : (supIdx w : ℝ) = |(w.1 l : ℝ)| := by
      rw [h2]
      exact_mod_cast hl
    rw [h3]
    exact Finset.le_sup' (fun l => |(w.1 l : ℝ)|) (Finset.mem_univ l)
def insertAxis (μ : Fin 4) (v : Fin 3 → ℤ) : EnergyMomentum.orthLattice μ :=
  ⟨Fin.insertNth (α := fun _ => ℤ) μ 0 v, by simp [EnergyMomentum.mem_orthLattice]⟩
theorem insertAxis_injective (μ : Fin 4) : Function.Injective (insertAxis μ) := by
  intro v v' h
  funext j
  have h' := congrArg (fun w : EnergyMomentum.orthLattice μ => w.1 (μ.succAbove j)) h
  simpa [insertAxis] using h'
def supBall (μ : Fin 4) (k : ℕ) : Finset (EnergyMomentum.orthLattice μ) :=
  (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(k : ℤ)) k).image (insertAxis μ)
theorem mem_supBall {k : ℕ} {w : EnergyMomentum.orthLattice μ} :
    w ∈ supBall μ k ↔ supIdx w ≤ k := by
  constructor
  · intro h
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    rw [Fintype.mem_piFinset] at hv
    refine Finset.sup_le fun l _ => ?_
    rcases Fin.eq_self_or_eq_succAbove μ l with rfl | ⟨j, rfl⟩
    · simp [insertAxis]
    · have := Finset.mem_Icc.1 (hv j)
      simp only [insertAxis, Fin.insertNth_apply_succAbove]
      omega
  · intro h
    refine Finset.mem_image.2 ⟨fun j => w.1 (μ.succAbove j), ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro j
      have h1 : (w.1 (μ.succAbove j)).natAbs ≤ supIdx w :=
        Finset.le_sup (f := fun l => (w.1 l).natAbs) (Finset.mem_univ _)
      refine Finset.mem_Icc.2 ?_
      omega
    · apply Subtype.ext
      funext l
      rcases Fin.eq_self_or_eq_succAbove μ l with rfl | ⟨j, rfl⟩
      · have : w.1 l = 0 := w.2
        simp [insertAxis, this]
      · simp [insertAxis]
theorem card_supBall (μ : Fin 4) (k : ℕ) : (supBall μ k).card = (2 * k + 1) ^ 3 := by
  rw [supBall, Finset.card_image_of_injective _ (insertAxis_injective μ), Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega
theorem supBall_subset_succ (μ : Fin 4) (k : ℕ) : supBall μ k ⊆ supBall μ (k + 1) := by
  intro w hw
  rw [mem_supBall] at hw ⊢
  omega
theorem card_sdiff_supBall_le (μ : Fin 4) (k : ℕ) :
    (((supBall μ (k + 1) \ supBall μ k).card : ℕ) : ℝ) ≤ 26 * ((k : ℝ) + 1) ^ 2 := by
  have h := Finset.card_sdiff_add_card_eq_card (supBall_subset_succ μ k)
  rw [card_supBall, card_supBall] at h
  have h' : (((supBall μ (k + 1) \ supBall μ k).card : ℕ) : ℝ) + (2 * (k : ℝ) + 1) ^ 3 =
      (2 * ((k : ℝ) + 1) + 1) ^ 3 := by exact_mod_cast h
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [sq_nonneg ((k : ℝ) + 1), mul_nonneg hk hk]
theorem sum_supBall_le (f : EnergyMomentum.orthLattice μ → ℝ) (m : ℕ) (A : ℝ) (b : ℕ → ℝ)
    (hb : ∀ n, 0 ≤ b n) (hin : ∀ w, supIdx w ≤ m → f w ≤ A)
    (hout : ∀ n w, supIdx w = m + 1 + n → f w ≤ b n) (N : ℕ) :
    ∑ w ∈ supBall μ (m + N), f w ≤
      (2 * (m : ℝ) + 1) ^ 3 * A +
        ∑ n ∈ Finset.range N, 26 * ((m : ℝ) + 1 + n) ^ 2 * b n := by
  induction N with
  | zero =>
    have h := Finset.sum_le_card_nsmul (supBall μ (m + 0)) f A
      (fun w hw => hin w (by simpa using mem_supBall.1 hw))
    rw [card_supBall, nsmul_eq_mul] at h
    simpa using h
  | succ N ih =>
    have hsplit := Finset.sum_sdiff (f := f) (supBall_subset_succ μ (m + N))
    have hshell : ∑ w ∈ supBall μ (m + N + 1) \ supBall μ (m + N), f w ≤
        26 * ((m : ℝ) + 1 + N) ^ 2 * b N := by
      have h := Finset.sum_le_card_nsmul (supBall μ (m + N + 1) \ supBall μ (m + N)) f (b N)
        (fun w hw => by
          obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hw
          rw [mem_supBall] at h1 h2
          exact hout N w (by omega))
      rw [nsmul_eq_mul] at h
      have h2 := card_sdiff_supBall_le μ (m + N)
      push_cast at h2
      have h3 := mul_le_mul_of_nonneg_right h2 (hb N)
      have e : (26 * ((m : ℝ) + N + 1) ^ 2) = 26 * ((m : ℝ) + 1 + N) ^ 2 := by ring
      rw [e] at h3
      exact h.trans h3
    rw [Finset.sum_range_succ, ← add_assoc m N 1, ← hsplit]
    linarith
theorem sum_range_geom_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, q ^ n ≤ (1 - q)⁻¹ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.sum_range_geometric_le <;> assumption
theorem sum_range_sq_mul_geom_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, (n : ℝ) ^ 2 * q ^ n ≤ 2 * (1 / (1 - q) ^ 3) := by
  have hnorm : ‖q‖ < 1 := by rwa [Real.norm_of_nonneg h0]
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hnorm).mul_left 2
  refine le_trans ?_ (sum_le_hasSum (Finset.range N)
    (fun n _ => by positivity) hs)
  refine Finset.sum_le_sum fun n _ => ?_
  have hq : 0 ≤ q ^ n := pow_nonneg h0 n
  have hch : (((n + 2).choose 2 : ℕ) : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  rw [hch]
  have : (n : ℝ) ^ 2 ≤ 2 * (((n : ℝ) + 2) * ((n : ℝ) + 1) / 2) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  calc (n : ℝ) ^ 2 * q ^ n ≤ (2 * (((n : ℝ) + 2) * ((n : ℝ) + 1) / 2)) * q ^ n :=
        mul_le_mul_of_nonneg_right this hq
    _ = 2 * (((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 * q ^ n) := by ring
theorem log_one_add_sqrt_two_mem : 0 < Real.log (1 + √2) ∧ Real.log (1 + √2) < 1 := by
  have h2 : √2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h1 : 0 < √2 := by positivity
  refine ⟨Real.log_pos (by linarith), ?_⟩
  rw [Real.log_lt_iff_lt_exp (by linarith)]
  have := Real.exp_one_gt_d9
  linarith
theorem correlationDecayRate_eq (r : ℕ+) :
    Autocorrelation.correlationDecayRate r = Real.log (1 + √2) / (4 * (r : ℝ)) := by
  have hr : (r : ℝ) ≠ 0 := by exact_mod_cast r.pos.ne'
  unfold Autocorrelation.correlationDecayRate DirectionPictures.slopeConstant
  field_simp
  ring
theorem correlationDecayRate_mem (r : ℕ+) :
    0 < Autocorrelation.correlationDecayRate r ∧ Autocorrelation.correlationDecayRate r < 1 / 4 := by
  have hr : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.2 r.pos
  obtain ⟨h0, h1⟩ := log_one_add_sqrt_two_mem
  rw [correlationDecayRate_eq]
  refine ⟨by positivity, ?_⟩
  rw [div_lt_iff₀ (by positivity)]
  nlinarith
theorem half_le_one_sub_exp_neg {α : ℝ} (h0 : 0 < α) (h1 : α ≤ 1) :
    α / 2 ≤ 1 - Real.exp (-α) := by
  have h := Real.add_one_le_exp α
  rw [Real.exp_neg]
  have hinv : (Real.exp α)⁻¹ ≤ (α + 1)⁻¹ := inv_anti₀ (by linarith) h
  have : (α + 1)⁻¹ ≤ 1 - α / 2 := by
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    nlinarith
  linarith
end ShellCount
open scoped Real
open ShellCount in
theorem TransverseCounting.transverseSumBound : TransverseCounting.TransverseSumBound := by
  intro μ r ϱ hϱ
  refine ⟨correlationDecayRate_mem r, fun κ hin hout => ?_⟩
  obtain ⟨hα0, hα1⟩ := correlationDecayRate_mem r
  set α := Autocorrelation.correlationDecayRate r with hαdef
  have hR : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.2 r.pos
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 1 = 2 * (r : ℕ) := ⟨2 * (r : ℕ) - 1, by have := r.pos; omega⟩
  have hmR : (m : ℝ) + 1 = 2 * (r : ℝ) := by exact_mod_cast hm
  set q := Real.exp (-α) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    have h := Real.exp_lt_exp.2 (by linarith : -α < 0)
    rwa [Real.exp_zero] at h
  have hhalf : α / 2 ≤ 1 - q := half_le_one_sub_exp_neg hα0 (by linarith)
  have hin' : ∀ w : EnergyMomentum.orthLattice μ, supIdx w ≤ m →
      ‖κ w‖ ≤ SmearingFilter.absCoeffSum * ϱ := by
    intro w hw
    refine hin w ?_
    rw [supNormCoord_eq_supIdx]
    have : (supIdx w : ℝ) ≤ m := by exact_mod_cast hw
    linarith
  have hout' : ∀ (n : ℕ) (w : EnergyMomentum.orthLattice μ), supIdx w = m + 1 + n →
      ‖κ w‖ ≤ 8 * q ^ n * ϱ := by
    intro n w hw
    have hcast : (supIdx w : ℝ) = 2 * (r : ℝ) + n := by
      rw [hw]
      push_cast
      rw [hmR]
    have h := hout w (by rw [supNormCoord_eq_supIdx, hcast]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    rw [supNormCoord_eq_supIdx, hcast] at h
    have e : Real.exp (-(α * (2 * (r : ℝ) + n - 2 * (r : ℝ)))) = q ^ n := by
      rw [hq, ← Real.exp_nat_mul]
      congr 1
      ring
    rwa [e] at h
  have hCzϱ : 0 ≤ SmearingFilter.absCoeffSum * ϱ := by
    have h := hin' 0 (by simp [supIdx])
    exact (norm_nonneg _).trans h
  have hαx : α = DirectionPictures.slopeConstant * π / (8 * (r : ℝ)) := rfl
  have hinv : (1 - q)⁻¹ ≤ 2 / α := by
    have h := inv_anti₀ (by positivity : 0 < α / 2) hhalf
    rwa [inv_div] at h
  have hcube : 1 / (1 - q) ^ 3 ≤ 8 / α ^ 3 := by
    have h := pow_le_pow_left₀ (inv_nonneg.2 (by linarith : 0 ≤ 1 - q)) hinv 3
    have e1 : ((1 - q)⁻¹) ^ 3 = 1 / (1 - q) ^ 3 := by rw [inv_pow, one_div]
    have e2 : (2 / α) ^ 3 = 8 / α ^ 3 := by rw [div_pow]; norm_num
    rwa [e1, e2] at h
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = (2 * (m : ℝ) + 1) ^ 3 * (SmearingFilter.absCoeffSum * ϱ) +
      208 * ϱ * (8 * (r : ℝ) ^ 2 * (2 / α) + 2 * (2 * (8 / α ^ 3))) := ⟨_, rfl⟩
  have hseries : ∀ N : ℕ, ∑ n ∈ Finset.range N, 26 * ((m : ℝ) + 1 + n) ^ 2 * (8 * q ^ n * ϱ) ≤
      208 * ϱ * (8 * (r : ℝ) ^ 2 * (2 / α) + 2 * (2 * (8 / α ^ 3))) := by
    intro N
    calc ∑ n ∈ Finset.range N, 26 * ((m : ℝ) + 1 + n) ^ 2 * (8 * q ^ n * ϱ)
        ≤ ∑ n ∈ Finset.range N, 208 * ϱ * (8 * (r : ℝ) ^ 2 * q ^ n + 2 * ((n : ℝ) ^ 2 * q ^ n)) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [hmR]
          have key : (2 * (r : ℝ) + n) ^ 2 ≤ 8 * (r : ℝ) ^ 2 + 2 * (n : ℝ) ^ 2 := by
            nlinarith [sq_nonneg (2 * (r : ℝ) - n)]
          have hqn : 0 ≤ 208 * (q ^ n * ϱ) := by positivity
          have h := mul_le_mul_of_nonneg_right key hqn
          calc 26 * (2 * (r : ℝ) + n) ^ 2 * (8 * q ^ n * ϱ)
              = (2 * (r : ℝ) + n) ^ 2 * (208 * (q ^ n * ϱ)) := by ring
            _ ≤ (8 * (r : ℝ) ^ 2 + 2 * (n : ℝ) ^ 2) * (208 * (q ^ n * ϱ)) := h
            _ = _ := by ring
      _ = 208 * ϱ * (8 * (r : ℝ) ^ 2 * ∑ n ∈ Finset.range N, q ^ n +
            2 * ∑ n ∈ Finset.range N, (n : ℝ) ^ 2 * q ^ n) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
          · exact mul_le_mul_of_nonneg_left ((sum_range_geom_le hq0 hq1 N).trans hinv)
              (by positivity)
          · refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact (sum_range_sq_mul_geom_le hq0 hq1 N).trans
              (mul_le_mul_of_nonneg_left hcube (by norm_num))
  have hball : ∀ N : ℕ, ∑ w ∈ supBall μ (m + N), ‖κ w‖ ≤ T := by
    intro N
    have h := sum_supBall_le (fun w => ‖κ w‖) m (SmearingFilter.absCoeffSum * ϱ)
      (fun n => 8 * q ^ n * ϱ) (fun n => by positivity) hin' hout' N
    rw [hT]
    exact h.trans (add_le_add_right (hseries N) _)
  have hall : ∀ u : Finset (EnergyMomentum.orthLattice μ), ∑ w ∈ u, ‖κ w‖ ≤ T := by
    intro u
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := supBall μ (m + u.sup supIdx)) ?_
      (fun _ _ _ => norm_nonneg _)) (hball _)
    intro w hw
    rw [mem_supBall]
    have : supIdx w ≤ u.sup supIdx := Finset.le_sup hw
    omega
  have hnn : (0 : EnergyMomentum.orthLattice μ → ℝ) ≤ fun w => ‖κ w‖ := fun w => norm_nonneg _
  have hTle : T ≤ (2 * π) ^ 3 * SmearingFilter.spectralDensityConst * (r : ℝ) ^ 3 * ϱ := by
    have h2m : 2 * (m : ℝ) + 1 = 4 * (r : ℝ) - 1 := by linarith
    have hpow : (4 * (r : ℝ) - 1) ^ 3 ≤ (4 * (r : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 3
    have hfirst := mul_le_mul_of_nonneg_right hpow hCzϱ
    have hpi : (2 * π) ^ 3 * (2 * π) ^ (-3 : ℤ) = 1 := by
      have : (2 * π) ≠ 0 := by positivity
      rw [zpow_neg, zpow_ofNat]
      exact mul_inv_cancel₀ (pow_ne_zero 3 this)
    have htarget : (2 * π) ^ 3 * SmearingFilter.spectralDensityConst * (r : ℝ) ^ 3 * ϱ =
        (64 * SmearingFilter.absCoeffSum + 26624 / (DirectionPictures.slopeConstant * π) +
          3407872 / (DirectionPictures.slopeConstant * π) ^ 3) * (r : ℝ) ^ 3 * ϱ := by
      unfold SmearingFilter.spectralDensityConst
      rw [← mul_assoc ((2 * π) ^ 3), hpi, one_mul]
    have hsecond : 208 * ϱ * (8 * (r : ℝ) ^ 2 * (2 / α) + 2 * (2 * (8 / α ^ 3))) =
        (26624 / (DirectionPictures.slopeConstant * π) +
          3407872 / (DirectionPictures.slopeConstant * π) ^ 3) * (r : ℝ) ^ 3 * ϱ := by
      rw [hαx]
      field_simp
      ring
    rw [hT, h2m, hsecond, htarget]
    nlinarith [hfirst]
  exact ⟨summable_of_sum_le hnn hall, (Real.tsum_le_of_sum_le hnn hall).trans hTle⟩
end YangMills.Construction.ReflectionPositivity
