import YangMills.Construction.Lattice.SumsOverTheScales
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TorusBound.ScaleSums
def scaledDist (c : ConstantParameters) (d : ℝ) (s : ℕ) : ℝ := d * (c.L : ℝ) ^ s / (c.cubeSide : ℝ)
def compTerm (c : ConstantParameters) (d : ℝ) (s : ℕ) : ℝ :=
  (2 * scaledDist c d s + 4) ^ 4 * c.decayFactor d s
def uvBracket (c : ConstantParameters) : ℝ≥0∞ :=
  ENNReal.ofReal (44 ^ 4 * (1 + Real.log (20 * (c.cubeSide : ℝ)))) +
    c.decaySup * ENNReal.ofReal (Real.exp (5 * c.rateGap) - 1)⁻¹
theorem thirteen_le_L (c : ConstantParameters) : (13 : ℝ) ≤ (c.L : ℝ) := by
  have h := c.isAdmissible.2
  exact_mod_cast h
theorem cubeSide_cast_pos (c : ConstantParameters) : (0 : ℝ) < (c.cubeSide : ℝ) :=
  lt_of_lt_of_le one_pos c.one_le_cubeSide
theorem scaledDist_nonneg (c : ConstantParameters) {d : ℝ} (hd : 0 < d) (s : ℕ) :
    0 ≤ scaledDist c d s := by
  have hM := cubeSide_cast_pos c
  unfold scaledDist
  positivity
theorem decayFactor_le_one (c : ConstantParameters) (d : ℝ) (s : ℕ) : c.decayFactor d s ≤ 1 := by
  unfold ConstantParameters.decayFactor
  apply Real.exp_le_one_iff.2
  have h₁ := c.rateGap_pos
  have h₂ : 0 ≤ plusPart (d * (c.L : ℝ) ^ s / (c.cubeSide : ℝ) - 10) := le_max_right _ _
  nlinarith [mul_nonneg h₁.le h₂]
theorem decayFactor_antitone (c : ConstantParameters) {a b : ℝ} (hab : a ≤ b) (s : ℕ) :
    c.decayFactor b s ≤ c.decayFactor a s := by
  unfold ConstantParameters.decayFactor
  apply Real.exp_le_exp.2
  have hM := cubeSide_cast_pos c
  have h : a * (c.L : ℝ) ^ s / (c.cubeSide : ℝ) ≤ b * (c.L : ℝ) ^ s / (c.cubeSide : ℝ) := by
    gcongr
  have h' : plusPart (a * (c.L : ℝ) ^ s / (c.cubeSide : ℝ) - 10) ≤
      plusPart (b * (c.L : ℝ) ^ s / (c.cubeSide : ℝ) - 10) :=
    max_le_max (by linarith) le_rfl
  have h₁ := c.rateGap_pos
  nlinarith [mul_le_mul_of_nonneg_left h' h₁.le]
theorem compTerm_le_of_lt (c : ConstantParameters) {d : ℝ} (hd : 0 < d) {s : ℕ}
    (hs : scaledDist c d s < 20) : compTerm c d s ≤ 44 ^ 4 := by
  have ht := scaledDist_nonneg c hd s
  have h₁ : (2 * scaledDist c d s + 4) ^ 4 ≤ (44 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  have h₂ := decayFactor_le_one c d s
  have h₃ : 0 ≤ c.decayFactor d s := (Real.exp_pos _).le
  unfold compTerm
  calc (2 * scaledDist c d s + 4) ^ 4 * c.decayFactor d s
      ≤ (44 : ℝ) ^ 4 * 1 := mul_le_mul h₁ h₂ h₃ (by positivity)
    _ = 44 ^ 4 := mul_one _
theorem compTerm_le_of_le (c : ConstantParameters) (d : ℝ) {s : ℕ}
    (hs : 20 ≤ scaledDist c d s) :
    ENNReal.ofReal (compTerm c d s) ≤
      c.decaySup *
        ENNReal.ofReal (Real.exp (-c.rateGap * scaledDist c d s / 4)) := by
  set t := scaledDist c d s with ht
  have hc := c.rateGap_pos
  have hdecay : c.decayFactor d s ≤
      Real.exp (-c.rateGap * t / 4) * Real.exp (-c.rateGap * t / 4) := by
    rw [← Real.exp_add]
    unfold ConstantParameters.decayFactor
    apply Real.exp_le_exp.2
    have h₁ : t / 2 ≤ plusPart (d * (c.L : ℝ) ^ s / (c.cubeSide : ℝ) - 10) := by
      have : t - 10 ≤ plusPart (d * (c.L : ℝ) ^ s / (c.cubeSide : ℝ) - 10) := le_max_left _ _
      linarith
    nlinarith [mul_le_mul_of_nonneg_left h₁ hc.le]
  have hreal : compTerm c d s ≤ c.supTerm t * Real.exp (-c.rateGap * t / 4) := by
    unfold compTerm ConstantParameters.supTerm
    rw [← ht, mul_assoc]
    exact mul_le_mul_of_nonneg_left hdecay (Even.pow_nonneg (by decide) _)
  calc ENNReal.ofReal (compTerm c d s)
      ≤ ENNReal.ofReal (c.supTerm t * Real.exp (-c.rateGap * t / 4)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (c.supTerm t) * ENNReal.ofReal (Real.exp (-c.rateGap * t / 4)) :=
        ENNReal.ofReal_mul (c.supTerm_nonneg t)
    _ ≤ c.decaySup * ENNReal.ofReal (Real.exp (-c.rateGap * t / 4)) := by
        gcongr
        exact le_iSup₂ (f := fun (t : ℝ) (_ : 0 ≤ t) => ENNReal.ofReal (c.supTerm t)) t
          (by linarith)
theorem tsum_exp_geometric (x : ℝ) (hx : 0 < x) :
    ∑' u : ℕ, ENNReal.ofReal (Real.exp (-(5 * x)) ^ (u + 1)) =
      ENNReal.ofReal (Real.exp (5 * x) - 1)⁻¹ := by
  set r := Real.exp (-(5 * x)) with hr
  have hr₀ : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := by
    rw [hr, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  have hsum : Summable fun u : ℕ => r ^ (u + 1) := by
    simp_rw [pow_succ']
    exact (summable_geometric_of_lt_one hr₀.le hr₁).mul_left r
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsum]
  congr 1
  simp_rw [pow_succ']
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr₀.le hr₁]
  have he : Real.exp (5 * x) = r⁻¹ := by rw [hr, Real.exp_neg, inv_inv]
  rw [he]
  have h₁ : 1 - r ≠ 0 := by linarith
  field_simp
theorem exists_twenty_le (c : ConstantParameters) {d : ℝ} (hd : 0 < d) :
    ∃ s, 20 ≤ scaledDist c d s := by
  have hL : (1 : ℝ) < (c.L : ℝ) := by linarith [thirteen_le_L c]
  have hM := cubeSide_cast_pos c
  obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt (20 * (c.cubeSide : ℝ) / d) hL
  refine ⟨s, ?_⟩
  unfold scaledDist
  rw [le_div_iff₀ hM]
  rw [div_lt_iff₀ hd] at hs
  linarith
theorem index_le_logPos (c : ConstantParameters) {d : ℝ} (hd : 0 < d) {s : ℕ}
    (hs : scaledDist c d s < 20) :
    (s : ℝ) ≤ logPos (20 * (c.cubeSide : ℝ) / d) := by
  have hM := cubeSide_cast_pos c
  have hY : 0 < 20 * (c.cubeSide : ℝ) / d := by positivity
  have hpow : (c.L : ℝ) ^ s < 20 * (c.cubeSide : ℝ) / d := by
    unfold scaledDist at hs
    rw [div_lt_iff₀ hM] at hs
    rw [lt_div_iff₀ hd]
    linarith
  have hexp : Real.exp (s : ℝ) ≤ (c.L : ℝ) ^ s := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le
      (by linarith [Real.exp_one_lt_d9, thirteen_le_L c]) s
  have hlt : (s : ℝ) < Real.log (20 * (c.cubeSide : ℝ) / d) :=
    (Real.lt_log_iff_exp_lt hY).2 (hexp.trans_lt hpow)
  exact hlt.le.trans (le_max_left _ _)
theorem zero_le_logPos (t : ℝ) : 0 ≤ logPos t := le_max_right _ _
theorem log_twenty_cubeSide_nonneg (c : ConstantParameters) :
    0 ≤ Real.log (20 * (c.cubeSide : ℝ)) :=
  Real.log_nonneg (by linarith [c.one_le_cubeSide])
theorem one_add_logPos_le (c : ConstantParameters) {d : ℝ} (hd : 0 < d) :
    1 + logPos (20 * (c.cubeSide : ℝ) / d) ≤
      (1 + Real.log (20 * (c.cubeSide : ℝ))) * logFactor d := by
  have hM := cubeSide_cast_pos c
  have h₀ := log_twenty_cubeSide_nonneg c
  have h₁ := zero_le_logPos (1 / d)
  have h₂ : Real.log (20 * (c.cubeSide : ℝ) / d) =
      Real.log (20 * (c.cubeSide : ℝ)) + Real.log (1 / d) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    ring
  have h₃ : Real.log (1 / d) ≤ logPos (1 / d) := le_max_left _ _
  have h₄ : logPos (20 * (c.cubeSide : ℝ) / d) ≤
      Real.log (20 * (c.cubeSide : ℝ)) + logPos (1 / d) :=
    max_le (by linarith) (by linarith)
  unfold logFactor
  nlinarith [mul_nonneg h₀ h₁]
theorem one_le_logFactor (d : ℝ) : 1 ≤ logFactor d := by
  have := zero_le_logPos (1 / d)
  unfold logFactor
  linarith
theorem tsum_tail_le (c : ConstantParameters) {d : ℝ} {s₀ : ℕ}
    (hs₀ : 20 ≤ scaledDist c d s₀) :
    ∑' u : ℕ, ENNReal.ofReal (compTerm c d (u + s₀)) ≤
      c.decaySup * ENNReal.ofReal (Real.exp (5 * c.rateGap) - 1)⁻¹ := by
  have hc := c.rateGap_pos
  have hterm : ∀ u : ℕ, ENNReal.ofReal (compTerm c d (u + s₀)) ≤
      c.decaySup * ENNReal.ofReal (Real.exp (-(5 * c.rateGap)) ^ (u + 1)) := by
    intro u
    have hshift : scaledDist c d (u + s₀) = scaledDist c d s₀ * (c.L : ℝ) ^ u := by
      unfold scaledDist
      rw [pow_add]
      ring
    have hpow : ((u : ℝ) + 1) ≤ (c.L : ℝ) ^ u := by
      have hL : 1 < c.L := by
        have := c.isAdmissible.2
        omega
      have h : u + 1 ≤ c.L ^ u := Nat.lt_pow_self hL
      exact_mod_cast h
    have hfar : 20 * ((u : ℝ) + 1) ≤ scaledDist c d (u + s₀) := by
      rw [hshift]
      exact mul_le_mul hs₀ hpow (by positivity) (by linarith)
    have hfar' : 20 ≤ scaledDist c d (u + s₀) := by
      have : (0 : ℝ) ≤ u := Nat.cast_nonneg _
      linarith
    refine (compTerm_le_of_le c d hfar').trans ?_
    gcongr
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hfar hc.le]
  calc ∑' u : ℕ, ENNReal.ofReal (compTerm c d (u + s₀))
      ≤ ∑' u : ℕ, c.decaySup *
          ENNReal.ofReal (Real.exp (-(5 * c.rateGap)) ^ (u + 1)) :=
        ENNReal.tsum_le_tsum hterm
    _ = c.decaySup * ENNReal.ofReal (Real.exp (5 * c.rateGap) - 1)⁻¹ := by
        rw [ENNReal.tsum_mul_left, tsum_exp_geometric _ hc]
theorem tsum_compTerm_le (c : ConstantParameters) {d : ℝ} (hd : 0 < d) :
    ∑' s : ℕ, ENNReal.ofReal (compTerm c d s) ≤
      uvBracket c * ENNReal.ofReal (logFactor d) := by
  classical
  have hex := exists_twenty_le c hd
  set s₀ := Nat.find hex with hs₀
  have hfar : 20 ≤ scaledDist c d s₀ := Nat.find_spec hex
  have hnear : ∀ s < s₀, scaledDist c d s < 20 := fun s hs =>
    not_le.1 (Nat.find_min hex hs)
  have hcount : (s₀ : ℝ) ≤ 1 + logPos (20 * (c.cubeSide : ℝ) / d) := by
    rcases Nat.eq_zero_or_pos s₀ with h | h
    · rw [h]
      have := zero_le_logPos (20 * (c.cubeSide : ℝ) / d)
      simpa using (by linarith : (0 : ℝ) ≤ 1 + logPos (20 * (c.cubeSide : ℝ) / d))
    · have h₁ := index_le_logPos c hd (hnear (s₀ - 1) (by omega))
      have h₂ : ((s₀ - 1 : ℕ) : ℝ) = (s₀ : ℝ) - 1 := by
        rw [Nat.cast_sub h]
        simp
      rw [h₂] at h₁
      linarith
  have hsplit := Summable.sum_add_tsum_nat_add' (k := s₀)
    (f := fun s => ENNReal.ofReal (compTerm c d s)) ENNReal.summable
  have hfirst : ∑ s ∈ Finset.range s₀, ENNReal.ofReal (compTerm c d s) ≤
      ENNReal.ofReal ((s₀ : ℝ) * 44 ^ 4) := by
    calc ∑ s ∈ Finset.range s₀, ENNReal.ofReal (compTerm c d s)
        ≤ ∑ _s ∈ Finset.range s₀, ENNReal.ofReal (44 ^ 4) :=
          Finset.sum_le_sum fun s hs => ENNReal.ofReal_le_ofReal
            (compTerm_le_of_lt c hd (hnear s (Finset.mem_range.1 hs)))
      _ = ENNReal.ofReal ((s₀ : ℝ) * 44 ^ 4) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hlog := one_le_logFactor d
  have hfirst' : ENNReal.ofReal ((s₀ : ℝ) * 44 ^ 4) ≤
      ENNReal.ofReal (44 ^ 4 * (1 + Real.log (20 * (c.cubeSide : ℝ)))) *
        ENNReal.ofReal (logFactor d) := by
    rw [← ENNReal.ofReal_mul (by have := log_twenty_cubeSide_nonneg c; positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := hcount.trans (one_add_logPos_le c hd)
    nlinarith
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (logFactor d) :=
    ENNReal.one_le_ofReal.2 hlog
  rw [← hsplit]
  unfold uvBracket
  rw [add_mul]
  refine add_le_add (hfirst.trans hfirst') ((tsum_tail_le c hfar).trans ?_)
  exact le_mul_of_one_le_right' hone
theorem decaySup_lt_top (c : ConstantParameters) : c.decaySup < ⊤ := by
  have hc := c.rateGap_pos
  have hbound : ∀ t : ℝ, 0 ≤ t →
      c.supTerm t ≤ 24 * (8 / c.rateGap) ^ 4 * Real.exp (c.rateGap / 2) := by
    intro t ht
    set x := c.rateGap * (2 * t + 4) / 8 with hx
    have hx₀ : 0 ≤ x := by positivity
    have h₁ : x ^ 4 / 24 ≤ Real.exp x := by
      have := Real.pow_div_factorial_le_exp x hx₀ 4
      simpa [Nat.factorial] using this
    have h₂ : Real.exp x = Real.exp (c.rateGap / 2) * Real.exp (c.rateGap * t / 4) := by
      rw [← Real.exp_add, hx]
      congr 1
      ring
    have h₃ : (2 * t + 4) ^ 4 = (8 / c.rateGap) ^ 4 * x ^ 4 := by
      rw [hx]
      field_simp
    have h₄ : Real.exp (-c.rateGap * t / 4) * Real.exp (c.rateGap * t / 4) = 1 := by
      rw [← Real.exp_add, ← Real.exp_zero]
      congr 1
      ring
    have h₅ : x ^ 4 ≤ 24 * (Real.exp (c.rateGap / 2) * Real.exp (c.rateGap * t / 4)) := by
      rw [← h₂]
      linarith
    unfold ConstantParameters.supTerm
    calc (2 * t + 4) ^ 4 * Real.exp (-c.rateGap * t / 4)
        = (8 / c.rateGap) ^ 4 * x ^ 4 * Real.exp (-c.rateGap * t / 4) := by rw [h₃]
      _ ≤ (8 / c.rateGap) ^ 4 *
            (24 * (Real.exp (c.rateGap / 2) * Real.exp (c.rateGap * t / 4))) *
            Real.exp (-c.rateGap * t / 4) := by gcongr
      _ = 24 * (8 / c.rateGap) ^ 4 * Real.exp (c.rateGap / 2) *
            (Real.exp (-c.rateGap * t / 4) * Real.exp (c.rateGap * t / 4)) := by ring
      _ = 24 * (8 / c.rateGap) ^ 4 * Real.exp (c.rateGap / 2) := by rw [h₄, mul_one]
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top
    (r := 24 * (8 / c.rateGap) ^ 4 * Real.exp (c.rateGap / 2)))
  exact iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal (hbound t ht)
theorem uvBracket_lt_top (c : ConstantParameters) : uvBracket c < ⊤ := by
  unfold uvBracket
  exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top,
    ENNReal.mul_lt_top (decaySup_lt_top c) ENNReal.ofReal_lt_top⟩
theorem uvBound_eq (c : ConstantParameters) :
    c.uvBound = ENNReal.ofReal c.prefactor * uvBracket c := rfl
theorem uvBound_lt_top (c : ConstantParameters) : c.uvBound < ⊤ := by
  rw [uvBound_eq]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (uvBracket_lt_top c)
theorem volumeTerm_le_compTerm (c : ConstantParameters) {d : ℝ} (hd : 0 < d) (s : ℕ) :
    c.volumeTerm d s ≤ d ^ (-4 : ℤ) * compTerm c d s := by
  have ht := scaledDist_nonneg c hd s
  have hdecay : 0 ≤ c.decayFactor d s := (Real.exp_pos _).le
  have h₁ : (c.L : ℝ) ^ s / (c.cubeSide : ℝ) = d⁻¹ * scaledDist c d s := by
    unfold scaledDist
    field_simp
  have h₂ : scaledDist c d s ^ 4 ≤ (2 * scaledDist c d s + 4) ^ 4 :=
    pow_le_pow_left₀ ht (by linarith) 4
  have h₃ : d ^ (-4 : ℤ) = d⁻¹ ^ 4 := by
    rw [zpow_neg, inv_pow]
    norm_cast
  unfold ConstantParameters.volumeTerm compTerm
  rw [h₁, h₃, mul_pow, mul_assoc]
  gcongr
theorem ballTerm_le_compTerm (c : ConstantParameters) {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (s : ℕ) : c.ballTerm d R s ≤ (1 + (R + 1) / d) ^ 4 * compTerm c d s := by
  have ht := scaledDist_nonneg c hd s
  have hdecay : 0 ≤ c.decayFactor d s := (Real.exp_pos _).le
  have hl : 0 < (R + 1) / d := by positivity
  have h₁ : 2 * (R + 1) * (c.L : ℝ) ^ s / (c.cubeSide : ℝ) =
      2 * ((R + 1) / d) * scaledDist c d s := by
    unfold scaledDist
    field_simp
  have h₂ : 2 * ((R + 1) / d) * scaledDist c d s + 4 ≤
      (1 + (R + 1) / d) * (2 * scaledDist c d s + 4) := by
    nlinarith
  have h₃ : (2 * ((R + 1) / d) * scaledDist c d s + 4) ^ 4 ≤
      ((1 + (R + 1) / d) * (2 * scaledDist c d s + 4)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) h₂ 4
  unfold ConstantParameters.ballTerm ConstantParameters.ballCubeCount compTerm
  rw [h₁, ← mul_assoc, ← mul_pow]
  gcongr
theorem tsum_volumeTerm_le (c : ConstantParameters) {d : ℝ} (hd : 0 < d) :
    ∑' s : ℕ, ENNReal.ofReal (c.volumeTerm d s) ≤
      ENNReal.ofReal (d ^ (-4 : ℤ)) * (uvBracket c * ENNReal.ofReal (logFactor d)) := by
  have h₀ : 0 ≤ d ^ (-4 : ℤ) := by positivity
  calc ∑' s : ℕ, ENNReal.ofReal (c.volumeTerm d s)
      ≤ ∑' s : ℕ, ENNReal.ofReal (d ^ (-4 : ℤ)) * ENNReal.ofReal (compTerm c d s) :=
        ENNReal.tsum_le_tsum fun s => by
          rw [← ENNReal.ofReal_mul h₀]
          exact ENNReal.ofReal_le_ofReal (volumeTerm_le_compTerm c hd s)
    _ = ENNReal.ofReal (d ^ (-4 : ℤ)) * ∑' s : ℕ, ENNReal.ofReal (compTerm c d s) :=
        ENNReal.tsum_mul_left
    _ ≤ _ := by
        gcongr
        exact tsum_compTerm_le c hd
theorem tsum_ballTerm_le (c : ConstantParameters) {d R : ℝ} (hd : 0 < d) (hR : 0 < R) :
    ∑' s : ℕ, ENNReal.ofReal (c.ballTerm d R s) ≤
      ENNReal.ofReal ((1 + (R + 1) / d) ^ 4) *
        (uvBracket c * ENNReal.ofReal (logFactor d)) := by
  have h₀ : 0 ≤ (1 + (R + 1) / d) ^ 4 := by positivity
  calc ∑' s : ℕ, ENNReal.ofReal (c.ballTerm d R s)
      ≤ ∑' s : ℕ, ENNReal.ofReal ((1 + (R + 1) / d) ^ 4) *
          ENNReal.ofReal (compTerm c d s) :=
        ENNReal.tsum_le_tsum fun s => by
          rw [← ENNReal.ofReal_mul h₀]
          exact ENNReal.ofReal_le_ofReal (ballTerm_le_compTerm c hd hR s)
    _ = ENNReal.ofReal ((1 + (R + 1) / d) ^ 4) *
          ∑' s : ℕ, ENNReal.ofReal (compTerm c d s) :=
        ENNReal.tsum_mul_left
    _ ≤ _ := by
        gcongr
        exact tsum_compTerm_le c hd
theorem summable_of_tsum_ofReal_lt_top {f : ℕ → ℝ} (hf : ∀ s, 0 ≤ f s)
    (h : ∑' s, ENNReal.ofReal (f s) < ⊤) : Summable f := by
  have := ENNReal.summable_toReal h.ne
  simpa [ENNReal.toReal_ofReal (hf _)] using this
theorem uvConstant_le (c : ConstantParameters) {d : ℝ} (hd : 0 < d) :
    c.uvConstant d ≤ c.uvBound * ENNReal.ofReal (d ^ (-4 : ℤ) * logFactor d) := by
  have h₀ : 0 ≤ d ^ (-4 : ℤ) := by positivity
  unfold ConstantParameters.uvConstant
  rw [uvBound_eq, ENNReal.ofReal_mul h₀]
  calc ENNReal.ofReal c.prefactor * ∑' s : ℕ, ENNReal.ofReal (c.volumeTerm d s)
      ≤ ENNReal.ofReal c.prefactor *
          (ENNReal.ofReal (d ^ (-4 : ℤ)) *
            (uvBracket c * ENNReal.ofReal (logFactor d))) := by
        gcongr
        exact tsum_volumeTerm_le c hd
    _ = _ := by ring
theorem uvConstantInBall_le (c : ConstantParameters) {d R : ℝ} (hd : 0 < d) (hR : 0 < R) :
    c.uvConstantInBall d R ≤
      c.uvBound * ENNReal.ofReal ((1 + (R + 1) / d) ^ 4 * logFactor d) := by
  have h₀ : 0 ≤ (1 + (R + 1) / d) ^ 4 := by positivity
  have hpre : c.Ce * PolymerActivities.DomainCounting.rateSum c.κe ≤ c.prefactor := by
    have := c.rateSum_pos
    unfold ConstantParameters.prefactor
    nlinarith
  unfold ConstantParameters.uvConstantInBall
  rw [uvBound_eq, ENNReal.ofReal_mul h₀]
  calc ENNReal.ofReal (c.Ce * PolymerActivities.DomainCounting.rateSum c.κe) *
        ∑' s : ℕ, ENNReal.ofReal (c.ballTerm d R s)
      ≤ ENNReal.ofReal c.prefactor *
          (ENNReal.ofReal ((1 + (R + 1) / d) ^ 4) *
            (uvBracket c * ENNReal.ofReal (logFactor d))) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hpre) (tsum_ballTerm_le c hd hR)
    _ = _ := by ring
theorem uvConstant_pos (c : ConstantParameters) (d : ℝ) : 0 < c.uvConstant d := by
  have hM := cubeSide_cast_pos c
  have hterm : 0 < c.volumeTerm d 0 := by
    unfold ConstantParameters.volumeTerm ConstantParameters.decayFactor
    have : (0 : ℝ) < (c.L : ℝ) ^ 0 / (c.cubeSide : ℝ) := by positivity
    positivity
  have h₁ : 0 < ENNReal.ofReal (c.volumeTerm d 0) := ENNReal.ofReal_pos.2 hterm
  have h₂ : 0 < ∑' s : ℕ, ENNReal.ofReal (c.volumeTerm d s) :=
    h₁.trans_le (ENNReal.le_tsum 0)
  unfold ConstantParameters.uvConstant
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 c.prefactor_pos).ne' h₂.ne'
theorem antitoneOn_uvConstant (c : ConstantParameters) :
    AntitoneOn c.uvConstant (Set.Ioi 0) := by
  intro a _ b _ hab
  unfold ConstantParameters.uvConstant
  gcongr with s
  unfold ConstantParameters.volumeTerm
  exact mul_le_mul_of_nonneg_left (decayFactor_antitone c hab s) (Even.pow_nonneg (by decide) _)
theorem antitoneOn_uvConstantInBall (c : ConstantParameters) (R : ℝ) :
    AntitoneOn (fun d => c.uvConstantInBall d R) (Set.Ioi 0) := by
  intro a _ b _ hab
  change c.uvConstantInBall b R ≤ c.uvConstantInBall a R
  unfold ConstantParameters.uvConstantInBall
  gcongr with s
  unfold ConstantParameters.ballTerm
  exact mul_le_mul_of_nonneg_left (decayFactor_antitone c hab s) (Even.pow_nonneg (by decide) _)
theorem Q_mem_Ico (c : ConstantParameters) (n : ℕ) {R : ℝ} (hR : 0 < R) :
    1 ≤ c.Q n R ∧ c.Q n R < ⊤ := by
  have hd : 0 < 2 * R + 4 := by linarith
  have hball : c.uvConstantInBall (2 * R + 4) R < ⊤ :=
    (uvConstantInBall_le c hd hR).trans_lt
      (ENNReal.mul_lt_top (uvBound_lt_top c) ENNReal.ofReal_lt_top)
  have hexp : c.qExponent n R ≠ ⊤ := by
    unfold ConstantParameters.qExponent
    exact (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hball,
      ENNReal.ofReal_lt_top⟩).ne
  have hQ := c.Q_eq_ofReal_exp (n := n) (R := R) ENNReal.toReal_nonneg
    (ENNReal.ofReal_toReal hexp).symm
  rw [hQ]
  exact ⟨ENNReal.one_le_ofReal.2 (Real.one_le_exp ENNReal.toReal_nonneg), ENNReal.ofReal_lt_top⟩
theorem scaleSumsHold (c : ConstantParameters) : ScaleSumsHold c := by
  refine ⟨decaySup_lt_top c, ?_, ?_, fun d _ => uvConstant_pos c d,
    antitoneOn_uvConstant c, fun R _ => antitoneOn_uvConstantInBall c R, ?_,
    fun d R hd hR => uvConstantInBall_le c hd hR, uvBound_lt_top c,
    fun n R _ hR => Q_mem_Ico c n hR⟩
  · intro d hd
    refine summable_of_tsum_ofReal_lt_top (c.volumeTerm_nonneg d) ?_
    exact (tsum_volumeTerm_le c hd).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (uvBracket_lt_top c) ENNReal.ofReal_lt_top))
  · intro d R hd hR
    refine summable_of_tsum_ofReal_lt_top (c.ballTerm_nonneg d R) ?_
    exact (tsum_ballTerm_le c hd hR).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (uvBracket_lt_top c) ENNReal.ofReal_lt_top))
  · intro d hd
    refine ⟨uvConstant_le c hd, ?_⟩
    have h₁ := one_le_logFactor d
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by linarith) (by linarith))) _
theorem rateGap_congr {c c' : ConstantParameters} (h : c.κe = c'.κe) :
    c.rateGap = c'.rateGap := by
  simp only [ConstantParameters.rateGap, h]
theorem prefactor_congr {c c' : ConstantParameters} (hCe : c.Ce = c'.Ce) (hκ : c.κe = c'.κe) :
    c.prefactor = c'.prefactor := by
  simp only [ConstantParameters.prefactor, hCe, hκ]
theorem decaySup_congr {c c' : ConstantParameters} (h : c.κe = c'.κe) :
    c.decaySup = c'.decaySup := by
  simp only [ConstantParameters.decaySup, ConstantParameters.supTerm, rateGap_congr h]
theorem decayFactor_congr {c c' : ConstantParameters} (hL : c.L = c'.L)
    (hM : c.cubeSide = c'.cubeSide) (hκ : c.κe = c'.κe) (d : ℝ) (s : ℕ) :
    c.decayFactor d s = c'.decayFactor d s := by
  simp only [ConstantParameters.decayFactor, hL, hM, rateGap_congr hκ]
theorem scaleSumBounds_holds : ScaleSumBounds := by
  refine ⟨scaleSumsHold, ?_, ?_, ?_⟩
  · intro c c' hM hCe hκ
    simp only [ConstantParameters.uvBound, prefactor_congr hCe hκ, decaySup_congr hκ,
      rateGap_congr hκ, hM]
  · intro c c' hL hM hCe hκ d _
    have hterm : ∀ s, c.volumeTerm d s = c'.volumeTerm d s := fun s => by
      simp only [ConstantParameters.volumeTerm, decayFactor_congr hL hM hκ, hL, hM]
    simp only [ConstantParameters.uvConstant, prefactor_congr hCe hκ, hterm]
  · intro c c' hL hM hCe hκ d R _ _
    have hterm : ∀ s, c.ballTerm d R s = c'.ballTerm d R s := fun s => by
      simp only [ConstantParameters.ballTerm, ConstantParameters.ballCubeCount,
        decayFactor_congr hL hM hκ, hL, hM]
    simp only [ConstantParameters.uvConstantInBall, hCe, hκ, hterm]
end YangMills.Construction.TorusBound.ScaleSums
end
