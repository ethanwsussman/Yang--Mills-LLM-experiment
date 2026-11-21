import YangMills.Construction.FormsOnATorus.ColumnOfTheLimitFormProof
import YangMills.Construction.FormsOnATorus.RiemannSumOfAPeriodicFunction
import YangMills.Construction.ResponseInTheExpansion.CurvatureKernelVariesSlowly
import YangMills.Construction.ResponseInTheExpansion.KernelOfALowSymbol
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
namespace YangMills.Construction.LimitForms
open YangMills.Construction.ResponseInTheExpansion YangMills.Construction.LinearResponse YangMills.Construction.RiemannSums
private def transverseSymbol (p : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  ((latticeSineNormSq p * (if μ = ν then 1 else 0) - latticeSine p μ * latticeSine p ν : ℝ) : ℂ)
private theorem contDiff_latticeSine (r : ℕ) (l : Fin 4) : ContDiff ℝ r fun p : Fin 4 → ℝ => latticeSine p l := by
  unfold latticeSine
  fun_prop
private theorem contDiff_latticeSineNormSq (r : ℕ) : ContDiff ℝ r latticeSineNormSq := by
  unfold latticeSineNormSq
  exact ContDiff.sum fun l _ => (contDiff_latticeSine r l).pow 2
private theorem contDiff_transverseSymbol (r : ℕ) (μ ν : Fin 4) : ContDiff ℝ r fun p => transverseSymbol p μ ν := by
  unfold transverseSymbol
  exact Complex.ofRealCLM.contDiff.comp (((contDiff_latticeSineNormSq r).mul contDiff_const).sub
    ((contDiff_latticeSine r μ).mul (contDiff_latticeSine r ν)))
private theorem latticeSine_add_two_pi (p : Fin 4 → ℝ) (i l : Fin 4) :
    latticeSine (p + Pi.single i (2 * Real.pi)) l = (if l = i then -1 else 1) * latticeSine p l := by apply _root_.YangMills.DeltaSharedProofs.p501879 <;> assumption
private theorem latticeSineNormSq_add_two_pi (p : Fin 4 → ℝ) (i : Fin 4) :
    latticeSineNormSq (p + Pi.single i (2 * Real.pi)) = latticeSineNormSq p := by apply _root_.YangMills.SharedProofs.p30766 <;> assumption
private theorem transverseSymbol_add_two_pi (p : Fin 4 → ℝ) (i μ ν : Fin 4) :
    transverseSymbol (p + Pi.single i (2 * Real.pi)) μ ν = periodShiftSign i μ ν * transverseSymbol p μ ν := by
  unfold transverseSymbol periodShiftSign
  rw [latticeSineNormSq_add_two_pi, latticeSine_add_two_pi, latticeSine_add_two_pi]
  by_cases h1 : i = μ <;> by_cases h2 : i = ν
  · subst h1; subst h2; simp
  · subst h1
    have : ν ≠ i := fun h => h2 h.symm
    simp [this, h2]
  · subst h2
    have : μ ≠ i := fun h => h1 h.symm
    simp [this, h1]
  · have a1 : μ ≠ i := fun h => h1 h.symm
    have a2 : ν ≠ i := fun h => h2 h.symm
    simp [a1, a2, h1, h2]
private theorem exists_norm_bound_of_periodic {E : Type} [NormedAddCommGroup E] (f : (Fin 4 → ℝ) → E)
    (hc : Continuous f) (T : ℝ) (hT : 0 < T) (hper : ∀ (i : Fin 4) (p : Fin 4 → ℝ), f (p + Pi.single i T) = f p) :
    ∃ b : ℝ, ∀ p, ‖f p‖ ≤ b := by
  classical
  obtain ⟨b, hb⟩ := (isCompact_Icc (a := (fun _ => 0 : Fin 4 → ℝ)) (b := fun _ => T)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨b, fun p => ?_⟩
  have single : ∀ (i : Fin 4) (k : ℤ) (q : Fin 4 → ℝ), f (q + Pi.single i ((k : ℝ) * T)) = f q := by
    intro i k q
    have hp : Function.Periodic (fun t : ℝ => f (q + Pi.single i t)) T := by
      intro t
      have e : q + Pi.single i (t + T) = (q + Pi.single i t) + Pi.single i T := by
        rw [Pi.single_add, add_assoc]
      show f (q + Pi.single i (t + T)) = f (q + Pi.single i t)
      rw [e, hper]
    have h := hp.int_mul k 0
    simpa using h
  have several : ∀ (s : Finset (Fin 4)) (k : Fin 4 → ℤ) (q : Fin 4 → ℝ),
      f (q + fun i => if i ∈ s then (k i : ℝ) * T else 0) = f q := by
    intro s k q
    induction s using Finset.induction_on with
    | empty =>
      have e : (q + fun i : Fin 4 => if i ∈ (∅ : Finset (Fin 4)) then (k i : ℝ) * T else 0) = q := by
        funext i; simp
      rw [e]
    | insert a s ha ih =>
      have e : (q + fun i => if i ∈ insert a s then (k i : ℝ) * T else 0) =
          (q + fun i => if i ∈ s then (k i : ℝ) * T else 0) + Pi.single a ((k a : ℝ) * T) := by
        funext i
        by_cases hi : i = a
        · subst hi; simp [ha]
        · simp [hi, Finset.mem_insert]
      rw [e, single, ih]
  set k : Fin 4 → ℤ := fun i => -⌊p i / T⌋ with hk
  have hq := several Finset.univ k p
  have hmem : (p + fun i => if i ∈ (Finset.univ : Finset (Fin 4)) then (k i : ℝ) * T else 0) ∈
      Set.Icc (fun _ => 0 : Fin 4 → ℝ) (fun _ => T) := by
    constructor
    · intro i
      simp only [Pi.add_apply, Finset.mem_univ, if_true, hk]
      push_cast
      have := Int.floor_le (p i / T)
      rw [le_div_iff₀ hT] at this
      linarith
    · intro i
      simp only [Pi.add_apply, Finset.mem_univ, if_true, hk]
      push_cast
      have := Int.lt_floor_add_one (p i / T)
      rw [div_lt_iff₀ hT] at this
      nlinarith
  rw [← hq]
  exact hb _ hmem
private theorem abs_sin_sub_self_le (x : ℝ) : |Real.sin x - x| ≤ 2 * |x| ^ 3 := by
  by_cases hx : |x| ≤ 1
  · have h := Real.sin_bound hx
    have h3 : |x ^ 3 / 6| = |x| ^ 3 / 6 := by
      rw [abs_div, abs_pow]; norm_num
    have e : Real.sin x - x = (Real.sin x - (x - x ^ 3 / 6)) - x ^ 3 / 6 := by ring
    have hp : |x| ^ 5 ≤ |x| ^ 3 := pow_le_pow_of_le_one (abs_nonneg x) hx (by norm_num)
    have hp0 : 0 ≤ |x| ^ 3 := by positivity
    calc |Real.sin x - x| ≤ |Real.sin x - (x - x ^ 3 / 6)| + |x ^ 3 / 6| := by
          rw [e]; exact abs_sub _ _
      _ ≤ 2 * |x| ^ 3 := by rw [h3]; nlinarith
  · have hx' : 1 < |x| := not_le.1 hx
    have h1 : |Real.sin x - x| ≤ 1 + |x| := by
      calc |Real.sin x - x| ≤ |Real.sin x| + |x| := abs_sub _ _
        _ ≤ 1 + |x| := by linarith [Real.abs_sin_le_one x]
    have h2 : |x| ≤ |x| ^ 3 := by
      have : (1 : ℝ) ≤ |x| ^ 2 := one_le_pow₀ hx'.le
      nlinarith
    linarith
abbrev _root_.YangMills.SharedProofs.p58168 := @abs_sin_sub_self_le
private theorem abs_two_sin_half_sub_le (t : ℝ) : |2 * Real.sin (t / 2) - t| ≤ |t| ^ 3 := by
  have h := abs_sin_sub_self_le (t / 2)
  have e : 2 * Real.sin (t / 2) - t = 2 * (Real.sin (t / 2) - t / 2) := by ring
  have e2 : |t / 2| ^ 3 = |t| ^ 3 / 8 := by
    rw [abs_div, div_pow]; norm_num
  rw [e2] at h
  rw [e, abs_mul, abs_two]
  linarith [pow_nonneg (abs_nonneg t) 3]
private theorem abs_two_sin_half_le (t : ℝ) : |2 * Real.sin (t / 2)| ≤ |t| := by apply _root_.YangMills.SharedProofs.p15114 <;> assumption
private theorem symbolWithGradient_transverse (p : Fin 4 → ℝ) :
    symbolWithGradient transverseSymbol p = ((latticeSineNormSq p : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext μ ν
  by_cases h : μ = ν
  · subst h
    simp only [symbolWithGradient, transverseSymbol, latticeMomentum, latticeSine, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, if_true]
    push_cast
    ring
  · simp only [symbolWithGradient, transverseSymbol, latticeMomentum, latticeSine, Matrix.smul_apply,
      Matrix.one_apply_ne h, smul_eq_mul, if_neg h]
    push_cast
    ring
private theorem transverse_isLowMomentumSymbol : ∃ B : ℕ → ℝ, IsLowMomentumSymbol B 10 1 0 transverseSymbol := by
  have hb : ∀ (r : ℕ) (μ ν : Fin 4), ∃ b : ℝ, ∀ p,
      ‖iteratedFDeriv ℝ r (fun p => transverseSymbol p μ ν) p‖ ≤ b := by
    intro r μ ν
    refine exists_norm_bound_of_periodic _ ((contDiff_transverseSymbol r μ ν).continuous_iteratedFDeriv le_rfl)
      (4 * Real.pi) (by positivity) ?_
    intro i p
    have hg : (fun q => transverseSymbol (q + Pi.single i (4 * Real.pi)) μ ν) = fun q => transverseSymbol q μ ν := by
      funext q
      have e : q + Pi.single i (4 * Real.pi) = (q + Pi.single i (2 * Real.pi)) + Pi.single i (2 * Real.pi) := by
        rw [add_assoc, ← Pi.single_add]
        congr 2
        ring
      rw [e, transverseSymbol_add_two_pi, transverseSymbol_add_two_pi, ← mul_assoc]
      have h1 : periodShiftSign i μ ν * periodShiftSign i μ ν = 1 := by
        unfold periodShiftSign
        rw [← mul_pow]
        simp
      rw [h1, one_mul]
    have h2 := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun q => transverseSymbol q μ ν) r
      (Pi.single i (4 * Real.pi)) p
    rw [hg] at h2
    exact h2.symm
  choose b hb using hb
  refine ⟨fun r => ∑ μ, ∑ ν, |b r μ ν|, ?_⟩
  refine ⟨contDiff_transverseSymbol, transverseSymbol_add_two_pi, ?_, ?_, ?_⟩
  · intro r μ ν p
    refine (hb r μ ν p).trans ((le_abs_self _).trans ?_)
    calc |b r μ ν| ≤ ∑ ν', |b r μ ν'| :=
          Finset.single_le_sum (f := fun ν' => |b r μ ν'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ν)
      _ ≤ ∑ μ', ∑ ν', |b r μ' ν'| :=
          Finset.single_le_sum (f := fun μ' => ∑ ν', |b r μ' ν'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ μ)
  · intro p μ ν
    have e : transverseSymbol p μ ν - ((sqNorm p * (if μ = ν then 1 else 0) - p μ * p ν : ℝ) : ℂ) =
        (((latticeSineNormSq p - sqNorm p) * (if μ = ν then 1 else 0) -
          (latticeSine p μ * latticeSine p ν - p μ * p ν) : ℝ) : ℂ) := by
      unfold transverseSymbol
      push_cast
      ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, add_zero]
    set S := sqNorm p with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hi : ∀ l, p l ^ 2 ≤ S := fun l =>
      Finset.single_le_sum (f := fun i => p i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ l)
    have hprod : ∀ a b : Fin 4, |latticeSine p a * latticeSine p b - p a * p b| ≤ 2 * S ^ 2 := by
      intro a b
      have ea : |latticeSine p a - p a| ≤ |p a| ^ 3 := abs_two_sin_half_sub_le (p a)
      have eb : |latticeSine p b - p b| ≤ |p b| ^ 3 := abs_two_sin_half_sub_le (p b)
      have sb : |latticeSine p b| ≤ |p b| := abs_two_sin_half_le (p b)
      have e1 : latticeSine p a * latticeSine p b - p a * p b =
          (latticeSine p a - p a) * latticeSine p b + p a * (latticeSine p b - p b) := by ring
      have ua : |p a| ^ 2 ≤ S := by rw [sq_abs]; exact hi a
      have ub : |p b| ^ 2 ≤ S := by rw [sq_abs]; exact hi b
      set u := |p a| with hu
      set v := |p b| with hv
      have hu0 : 0 ≤ u := abs_nonneg _
      have huv : u * v ≤ S := by nlinarith [sq_nonneg (u - v)]
      have b1 : u ^ 3 * v ≤ S ^ 2 := by
        have : u ^ 3 * v = u ^ 2 * (u * v) := by ring
        rw [this, sq S]
        exact mul_le_mul ua huv (by positivity) hS0
      have b2 : u * v ^ 3 ≤ S ^ 2 := by
        have : u * v ^ 3 = v ^ 2 * (u * v) := by ring
        rw [this, sq S]
        exact mul_le_mul ub huv (by positivity) hS0
      calc |latticeSine p a * latticeSine p b - p a * p b|
          ≤ |(latticeSine p a - p a) * latticeSine p b| + |p a * (latticeSine p b - p b)| := by
            rw [e1]; exact abs_add_le _ _
        _ = |latticeSine p a - p a| * |latticeSine p b| + u * |latticeSine p b - p b| := by
            rw [abs_mul, abs_mul]
        _ ≤ u ^ 3 * v + u * v ^ 3 := by
            have t1 := mul_le_mul ea sb (abs_nonneg _) (by positivity)
            have t2 := mul_le_mul_of_nonneg_left eb hu0
            linarith
        _ ≤ 2 * S ^ 2 := by linarith
    have hsum : |latticeSineNormSq p - S| ≤ 8 * S ^ 2 := by
      have e2 : latticeSineNormSq p - S = ∑ l, (latticeSine p l * latticeSine p l - p l * p l) := by
        unfold latticeSineNormSq
        rw [hS]
        unfold sqNorm
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [e2]
      calc |∑ l, (latticeSine p l * latticeSine p l - p l * p l)|
            ≤ ∑ l : Fin 4, |latticeSine p l * latticeSine p l - p l * p l| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _l : Fin 4, 2 * S ^ 2 := Finset.sum_le_sum fun l _ => hprod l l
        _ = 8 * S ^ 2 := by simp; ring
    have h1 : |(latticeSineNormSq p - S) * (if μ = ν then 1 else 0)| ≤ 8 * S ^ 2 := by
      split_ifs
      · simpa using hsum
      · simp; positivity
    calc _ ≤ |(latticeSineNormSq p - S) * (if μ = ν then 1 else 0)| +
          |latticeSine p μ * latticeSine p ν - p μ * p ν| :=
          abs_sub _ _
      _ ≤ 10 * S ^ 2 := by linarith [hprod μ ν]
  · intro p v
    have e : (∑ m, ∑ m', (starRingEnd ℂ) (v m) * symbolWithGradient transverseSymbol p m m' * v m') =
        ((latticeSineNormSq p * ∑ m, ‖v m‖ ^ 2 : ℝ) : ℂ) := by
      rw [symbolWithGradient_transverse]
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.sum_eq_single m]
      · rw [if_pos rfl, mul_one, ← Complex.conj_mul' (v m)]
        ring
      · intro b _ hb
        rw [if_neg (fun h => hb h.symm)]
        simp
      · intro h; exact absurd (Finset.mem_univ m) h
    rw [e, Complex.ofReal_re]
    have e2 : sqNorm (latticeMomentum p) = latticeSineNormSq p := rfl
    rw [e2]
    simp
private theorem transverse_inverse_bracket {p : Fin 4 → ℝ} (h : latticeSineNormSq p ≠ 0) (r s m n' : Fin 4) :
    (∑ a, ∑ a', (starRingEnd ℂ) (curlSymbol p r s a) * (symbolWithGradient transverseSymbol p)⁻¹ a a' *
      curlSymbol p m n' a') = curlProjectionSymbol m n' r s p := by
  have hc : ((latticeSineNormSq p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
  have hinv : (symbolWithGradient transverseSymbol p)⁻¹ =
      ((latticeSineNormSq p : ℝ) : ℂ)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [symbolWithGradient_transverse, smul_mul_smul_comm, mul_inv_cancel₀ hc, one_smul, one_mul]
  have hcurl : ∀ (μ ν a : Fin 4), curlSymbol p μ ν a = -(Complex.I * ((planeSineVector p μ ν a : ℝ) : ℂ)) := by
    intro μ ν a
    unfold curlSymbol planeSineVector latticeMomentum latticeSine
    push_cast
    split_ifs <;> ring
  rw [hinv]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hcurl, map_neg, map_mul, Complex.conj_I,
    Complex.conj_ofReal]
  unfold curlProjectionSymbol
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · rw [if_pos rfl]
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    field_simp
    linear_combination (-(planeSineVector p r s a : ℂ) * (planeSineVector p m n' a : ℂ)) * hI
  · intro b _ hb
    rw [if_neg (fun h => hb h.symm)]
    simp
  · intro h; exact absurd (Finset.mem_univ a) h
private theorem latticeSineNormSq_ne_zero {p : Fin 4 → ℝ} (hp0 : p ≠ 0)
    (hbox : ∀ i, -Real.pi ≤ p i ∧ p i ≤ Real.pi) : latticeSineNormSq p ≠ 0 := by
  have hpi := Real.pi_pos
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
    by_contra h
    push Not at h
    exact hp0 (funext h)
  have hs : Real.sin (p i / 2) ≠ 0 := by
    intro h0
    have := (Real.sin_eq_zero_iff_of_lt_of_lt (x := p i / 2) (by linarith [(hbox i).1])
      (by linarith [(hbox i).2])).1 h0
    exact hi (by linarith)
  have h1 : latticeSine p i ^ 2 ≤ latticeSineNormSq p :=
    Finset.single_le_sum (f := fun l => latticeSine p l ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : 0 < latticeSine p i ^ 2 := by
    unfold latticeSine
    have : 2 * Real.sin (p i / 2) ≠ 0 := by simpa using hs
    positivity
  intro h0
  linarith
private theorem abs_planeSineVector_mul_le (p : Fin 4 → ℝ) (m n' r s i : Fin 4) :
    |planeSineVector p m n' i * planeSineVector p r s i| ≤ 4 * latticeSineNormSq p := by
  have hT : ∀ a b : Fin 4, |latticeSine p a * latticeSine p b| ≤ latticeSineNormSq p := by
    intro a b
    have h1 : latticeSine p a ^ 2 ≤ latticeSineNormSq p :=
      Finset.single_le_sum (f := fun l => latticeSine p l ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
    have h2 : latticeSine p b ^ 2 ≤ latticeSineNormSq p :=
      Finset.single_le_sum (f := fun l => latticeSine p l ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ b)
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (latticeSine p a - latticeSine p b),
      sq_nonneg (latticeSine p a + latticeSine p b)]
  have hv : ∀ a b : Fin 4, |planeSineVector p a b i| ≤ |latticeSine p b| + |latticeSine p a| := by
    intro a b
    unfold planeSineVector
    refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> split_ifs <;> simp
  have t1 := hT n' s
  have t2 := hT n' r
  have t3 := hT m s
  have t4 := hT m r
  rw [abs_mul] at t1 t2 t3 t4
  rw [abs_mul]
  calc |planeSineVector p m n' i| * |planeSineVector p r s i|
      ≤ (|latticeSine p n'| + |latticeSine p m|) * (|latticeSine p s| + |latticeSine p r|) :=
        mul_le_mul (hv m n') (hv r s) (abs_nonneg _) (by positivity)
    _ ≤ 4 * latticeSineNormSq p := by nlinarith
private theorem norm_curlProjectionSymbol_le (m n' r s : Fin 4) (p : Fin 4 → ℝ) :
    ‖curlProjectionSymbol m n' r s p‖ ≤ 16 := by
  unfold curlProjectionSymbol
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases h : latticeSineNormSq p = 0
  · rw [h]; simp
  have hS : 0 < latticeSineNormSq p := lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm h)
  rw [abs_div, abs_of_pos hS, div_le_iff₀ hS]
  calc |∑ i, planeSineVector p m n' i * planeSineVector p r s i|
      ≤ ∑ i : Fin 4, |planeSineVector p m n' i * planeSineVector p r s i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, 4 * latticeSineNormSq p :=
        Finset.sum_le_sum fun i _ => abs_planeSineVector_mul_le p m n' r s i
    _ = 16 * latticeSineNormSq p := by simp; ring
private theorem measurable_curlProjectionSymbol (m n' r s : Fin 4) :
    Measurable (curlProjectionSymbol m n' r s) := by
  have h1 : ∀ l, Measurable fun p : Fin 4 → ℝ => latticeSine p l := fun l => by
    unfold latticeSine
    exact (Real.measurable_sin.comp ((measurable_pi_apply l).div_const 2)).const_mul 2
  have h2 : Measurable latticeSineNormSq := by
    unfold latticeSineNormSq
    exact Finset.measurable_sum _ fun l _ => (h1 l).pow_const 2
  have h3 : ∀ a b i : Fin 4, Measurable fun p => planeSineVector p a b i := by
    intro a b i
    unfold planeSineVector
    split_ifs
    · exact (h1 b).sub (h1 a)
    · exact (h1 b).sub measurable_const
    · exact measurable_const.sub (h1 a)
    · exact measurable_const.sub measurable_const
  unfold curlProjectionSymbol
  exact Complex.measurable_ofReal.comp ((Finset.measurable_sum _ fun i _ => (h3 m n' i).mul (h3 r s i)).div h2)
private theorem continuousAt_curlProjectionSymbol (m n' r s : Fin 4) {p : Fin 4 → ℝ}
    (h : latticeSineNormSq p ≠ 0) : ContinuousAt (curlProjectionSymbol m n' r s) p := by
  have h1 : ∀ l, Continuous fun p : Fin 4 → ℝ => latticeSine p l := fun l => by
    unfold latticeSine
    fun_prop
  have h2 : Continuous latticeSineNormSq := by
    unfold latticeSineNormSq
    exact continuous_finsetSum _ fun l _ => (h1 l).pow 2
  have h3 : ∀ a b i : Fin 4, Continuous fun p => planeSineVector p a b i := by
    intro a b i
    unfold planeSineVector
    split_ifs
    · exact (h1 b).sub (h1 a)
    · exact (h1 b).sub continuous_const
    · exact continuous_const.sub (h1 a)
    · exact continuous_const.sub continuous_const
  unfold curlProjectionSymbol
  refine Complex.continuous_ofReal.continuousAt.comp ?_
  exact (continuous_finsetSum _ fun i _ => (h3 m n' i).mul (h3 r s i)).continuousAt.div h2.continuousAt h
private def axisFlipSign (i l : Fin 4) : ℝ := if l = i then -1 else 1
private theorem axisFlipSign_mul_self (i l : Fin 4) : axisFlipSign i l * axisFlipSign i l = 1 := by
  unfold axisFlipSign
  split_ifs <;> norm_num
private theorem planeSineVector_add_two_pi (p : Fin 4 → ℝ) (i : Fin 4) {m n' : Fin 4} (hmn : m < n') (a : Fin 4) :
    planeSineVector (p + Pi.single i (2 * Real.pi)) m n' a =
      axisFlipSign i a * axisFlipSign i m * axisFlipSign i n' * planeSineVector p m n' a := by
  have hne : m ≠ n' := hmn.ne
  have h1 := axisFlipSign_mul_self i m
  have h2 := axisFlipSign_mul_self i n'
  unfold planeSineVector
  rw [latticeSine_add_two_pi, latticeSine_add_two_pi]
  change (if a = m then axisFlipSign i n' * latticeSine p n' else 0) -
    (if a = n' then axisFlipSign i m * latticeSine p m else 0) = _
  by_cases e1 : a = m
  · subst e1
    simp only [if_true, if_neg hne]
    linear_combination (-(axisFlipSign i n' * latticeSine p n')) * h1
  · by_cases e2 : a = n'
    · subst e2
      simp only [if_true, if_neg e1]
      linear_combination (axisFlipSign i m * latticeSine p m) * h2
    · simp [e1, e2]
private theorem curlProjectionSymbol_add_two_pi (p : Fin 4 → ℝ) (i : Fin 4) {m n' r s : Fin 4} (hmn : m < n')
    (hrs : r < s) :
    curlProjectionSymbol m n' r s (p + Pi.single i (2 * Real.pi)) =
      ((axisFlipSign i m * axisFlipSign i n' * axisFlipSign i r * axisFlipSign i s : ℝ) : ℂ) *
        curlProjectionSymbol m n' r s p := by
  unfold curlProjectionSymbol
  rw [latticeSineNormSq_add_two_pi, ← Complex.ofReal_mul]
  congr 1
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [planeSineVector_add_two_pi p i hmn, planeSineVector_add_two_pi p i hrs]
  linear_combination (axisFlipSign i m * axisFlipSign i n' * axisFlipSign i r * axisFlipSign i s *
    planeSineVector p m n' a * planeSineVector p r s a) * axisFlipSign_mul_self i a
private theorem exp_I_pi_indicator (b : Prop) [Decidable b] :
    Complex.exp (Complex.I * (Real.pi : ℂ) * (((if b then 1 else 0 : ℝ)) : ℂ)) =
      ((if b then -1 else 1 : ℝ) : ℂ) := by
  split_ifs
  · simp [mul_comm Complex.I, Complex.exp_pi_mul_I]
  · simp
private theorem exp_two_pi_I_halfInteger {w : ℝ} {i m n' r s : Fin 4}
    (hw : ∃ u : ℤ, w = u + ((if i = m then 1 else 0) + (if i = n' then 1 else 0) - (if i = r then 1 else 0) -
      (if i = s then 1 else 0)) / 2) :
    Complex.exp (Complex.I * ((2 * Real.pi * w : ℝ) : ℂ)) =
      ((axisFlipSign i m * axisFlipSign i n' * axisFlipSign i r * axisFlipSign i s : ℝ) : ℂ) := by
  obtain ⟨u, hu⟩ := hw
  have e : Complex.I * ((2 * Real.pi * w : ℝ) : ℂ) = (u : ℂ) * (2 * Real.pi * Complex.I) +
      (Complex.I * (Real.pi : ℂ) * (((if i = m then 1 else 0 : ℝ)) : ℂ) +
        Complex.I * (Real.pi : ℂ) * (((if i = n' then 1 else 0 : ℝ)) : ℂ) -
        Complex.I * (Real.pi : ℂ) * (((if i = r then 1 else 0 : ℝ)) : ℂ) -
        Complex.I * (Real.pi : ℂ) * (((if i = s then 1 else 0 : ℝ)) : ℂ)) := by
    rw [hu]
    push_cast
    ring
  have t : ∀ a b : Fin 4, ((if a = b then -1 else 1 : ℝ) : ℂ) = ((axisFlipSign a b : ℝ) : ℂ) := by
    intro a b
    unfold axisFlipSign
    by_cases h : a = b
    · simp [h]
    · have : b ≠ a := fun e => h e.symm
      simp [h, this]
  have inv : ∀ a b : Fin 4, ((axisFlipSign a b : ℝ) : ℂ)⁻¹ = ((axisFlipSign a b : ℝ) : ℂ) := by
    intro a b
    unfold axisFlipSign
    split_ifs <;> norm_num
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_sub, Complex.exp_sub,
    Complex.exp_add, exp_I_pi_indicator, exp_I_pi_indicator, exp_I_pi_indicator, exp_I_pi_indicator, t, t, t, t,
    div_eq_mul_inv, div_eq_mul_inv, inv, inv]
  push_cast
  ring
private def fourierIntegrand (m n' r s : Fin 4) (w : Fin 4 → ℝ) (p : Fin 4 → ℝ) : ℂ :=
  curlProjectionSymbol m n' r s p * Complex.exp (Complex.I * ((∑ l, p l * w l : ℝ) : ℂ))
private theorem norm_fourierIntegrand_le (m n' r s : Fin 4) (w p : Fin 4 → ℝ) :
    ‖fourierIntegrand m n' r s w p‖ ≤ 16 := by
  unfold fourierIntegrand
  rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact norm_curlProjectionSymbol_le m n' r s p
private theorem measurable_fourierIntegrand (m n' r s : Fin 4) (w : Fin 4 → ℝ) :
    Measurable (fourierIntegrand m n' r s w) := by
  unfold fourierIntegrand
  refine (measurable_curlProjectionSymbol m n' r s).mul (Complex.measurable_exp.comp ?_)
  refine measurable_const.mul (Complex.measurable_ofReal.comp ?_)
  exact Finset.measurable_sum _ fun l _ => (measurable_pi_apply l).mul_const _
private theorem fourierIntegrand_add_two_pi {m n' r s : Fin 4} (hmn : m < n') (hrs : r < s) {w : Fin 4 → ℝ}
    (hw : ∀ i, ∃ u : ℤ, w i = u + ((if i = m then 1 else 0) + (if i = n' then 1 else 0) -
      (if i = r then 1 else 0) - (if i = s then 1 else 0)) / 2) (i : Fin 4) (p : Fin 4 → ℝ) :
    fourierIntegrand m n' r s w (p + Pi.single i (2 * Real.pi)) = fourierIntegrand m n' r s w p := by
  unfold fourierIntegrand
  have e : (∑ l, (p + Pi.single i (2 * Real.pi) : Fin 4 → ℝ) l * w l) =
      (∑ l, p l * w l) + 2 * Real.pi * w i := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [curlProjectionSymbol_add_two_pi p i hmn hrs, e, Complex.ofReal_add, mul_add, Complex.exp_add,
    exp_two_pi_I_halfInteger (hw i)]
  have hall : ((axisFlipSign i m * axisFlipSign i n' * axisFlipSign i r * axisFlipSign i s : ℝ) : ℂ) *
      ((axisFlipSign i m * axisFlipSign i n' * axisFlipSign i r * axisFlipSign i s : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    have : axisFlipSign i m * axisFlipSign i n' * axisFlipSign i r * axisFlipSign i s *
        (axisFlipSign i m * axisFlipSign i n' * axisFlipSign i r * axisFlipSign i s) = 1 := by
      calc _ = (axisFlipSign i m * axisFlipSign i m) * (axisFlipSign i n' * axisFlipSign i n') *
            (axisFlipSign i r * axisFlipSign i r) * (axisFlipSign i s * axisFlipSign i s) := by ring
        _ = 1 := by
          rw [axisFlipSign_mul_self, axisFlipSign_mul_self, axisFlipSign_mul_self, axisFlipSign_mul_self]
          norm_num
    rw [this]
    simp
  linear_combination (curlProjectionSymbol m n' r s p *
    Complex.exp (Complex.I * ((∑ l, p l * w l : ℝ) : ℂ))) * hall
private theorem continuousAt_fourierIntegrand (m n' r s : Fin 4) (w : Fin 4 → ℝ) {p : Fin 4 → ℝ}
    (h : latticeSineNormSq p ≠ 0) : ContinuousAt (fourierIntegrand m n' r s w) p := by
  unfold fourierIntegrand
  refine (continuousAt_curlProjectionSymbol m n' r s h).mul (Continuous.continuousAt ?_)
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact continuous_finsetSum _ fun l _ => (continuous_apply l).mul continuous_const
private theorem dualMomentum_mem_box {N : ℕ} (hN : 0 < N) [NeZero N] (j : Fin 4 → ZMod N) (i : Fin 4) :
    -Real.pi ≤ dualMomentum j i ∧ dualMomentum j i ≤ Real.pi := by
  have hpi := Real.pi_pos
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := ZMod.natAbs_valMinAbs_le (j i)
  have h2 : (|((j i).valMinAbs : ℝ)|) * 2 ≤ N := by
    have h3 : ((j i).valMinAbs.natAbs) * 2 ≤ N := by omega
    have h4 : (((j i).valMinAbs.natAbs : ℕ) : ℝ) * 2 ≤ N := by exact_mod_cast h3
    rwa [Nat.cast_natAbs, Int.cast_abs] at h4
  have h5 := abs_le.1 (show |((j i).valMinAbs : ℝ)| ≤ (N : ℝ) / 2 by linarith)
  unfold dualMomentum
  constructor
  · rw [le_div_iff₀ hN']; nlinarith [h5.1]
  · rw [div_le_iff₀ hN']; nlinarith [h5.2]
private theorem dualMomentum_ne_zero {N : ℕ} (hN : 0 < N) [NeZero N] {j : Fin 4 → ZMod N} (hj : j ≠ 0) :
    dualMomentum j ≠ 0 := by
  have hpi := Real.pi_pos
  intro h0
  apply hj
  funext i
  have h1 := congrFun h0 i
  unfold dualMomentum at h1
  simp only [Pi.zero_apply, div_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, Int.cast_eq_zero,
    Nat.cast_eq_zero] at h1
  rcases h1 with (h1 | h1) | h1
  · exact absurd h1 hpi.ne'
  · exact (ZMod.valMinAbs_eq_zero _).1 h1
  · omega
private theorem inverseSymbolFourierSum_eq_mean (n : ℕ) (r s m n' : Fin 4) (w : Fin 4 → ℝ) :
    inverseSymbolFourierSum (2 * (n + 1)) transverseSymbol r s m n' w =
      (((2 * (n + 1) : ℕ) : ℂ) ^ 4)⁻¹ *
        ∑ j : Fin 4 → ZMod (2 * (n + 1)), fourierIntegrand m n' r s w (dualTorusMomentum j) := by
  unfold inverseSymbolFourierSum
  congr 1
  have h0 : fourierIntegrand m n' r s w (dualTorusMomentum (0 : Fin 4 → ZMod (2 * (n + 1)))) = 0 := by
    have e : dualTorusMomentum (0 : Fin 4 → ZMod (2 * (n + 1))) = 0 := by
      funext i
      simp [dualTorusMomentum]
    rw [e]
    unfold fourierIntegrand curlProjectionSymbol
    have e2 : latticeSineNormSq (0 : Fin 4 → ℝ) = 0 := by
      simp [latticeSineNormSq, latticeSine]
    rw [e2]
    simp
  rw [← Finset.sum_erase (s := Finset.univ)
    (f := fun j : Fin 4 → ZMod (2 * (n + 1)) => fourierIntegrand m n' r s w (dualTorusMomentum j)) (a := 0) h0]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
  have hpos : 0 < 2 * (n + 1) := by omega
  have hS := latticeSineNormSq_ne_zero (dualMomentum_ne_zero hpos hj0) (dualMomentum_mem_box hpos j)
  rw [transverse_inverse_bracket hS]
  rfl
private theorem fourierKernel_near_curvatureKernel (hR : TendstoRiemannSumOfPeriodic) {B : ℕ → ℝ} {C' N₀ : ℝ}
    (hlow : IsLowMomentumSymbol B 10 1 0 transverseSymbol)
    (hC : ∀ (N : ℕ) [NeZero N] (ε : ℝ) (S : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (μ ν ρ τ : Fin 4) (z : Fin 4 → ℝ),
      N₀ ≤ N → 0 ≤ ε → ε ≤ Real.exp (-(1 * (N : ℝ))) → IsLowMomentumSymbol B 10 1 ε S → μ < ν → ρ < τ →
      (∀ i, ∃ w : ℤ, z i = w + ((if i = ρ then 1 else 0) + (if i = τ then 1 else 0) - (if i = μ then 1 else 0) -
        (if i = ν then 1 else 0)) / 2) → 1 ≤ sqNorm z → sqNorm z ≤ ((N : ℝ) / 8) ^ 2 →
      ‖inverseSymbolFourierSum N S μ ν ρ τ z - (continuumCurvatureKernel z μ ν ρ τ : ℂ)‖ ≤
        C' * (sqNorm z ^ (-(5 / 2 : ℝ)) + (N : ℝ) ^ (-(4 : ℤ))))
    {m n' r s : Fin 4} (hmn : m < n') (hrs : r < s) {w : Fin 4 → ℝ}
    (hw : ∀ i, ∃ u : ℤ, w i = u + ((if i = m then 1 else 0) + (if i = n' then 1 else 0) -
      (if i = r then 1 else 0) - (if i = s then 1 else 0)) / 2) (h1 : 1 ≤ sqNorm w) :
    ‖fourierKernelAt (curlProjectionSymbol m n' r s) w - (continuumCurvatureKernel w r s m n' : ℂ)‖ ≤
      C' * sqNorm w ^ (-(5 / 2 : ℝ)) := by
  have hT := hR (fourierIntegrand m n' r s w) 16 (measurable_fourierIntegrand m n' r s w)
    (norm_fourierIntegrand_le m n' r s w)
    (fun i p => fourierIntegrand_add_two_pi hmn hrs hw i p)
    (fun p hp hbox => continuousAt_fourierIntegrand m n' r s w (latticeSineNormSq_ne_zero hp hbox))
  have hker : ((2 * Real.pi : ℝ) : ℂ)⁻¹ ^ 4 *
      ∫ p in Set.Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), fourierIntegrand m n' r s w p =
      fourierKernelAt (curlProjectionSymbol m n' r s) w := rfl
  rw [hker] at hT
  have hlim1 : Tendsto (fun n : ℕ => ‖inverseSymbolFourierSum (2 * (n + 1)) transverseSymbol r s m n' w -
      (continuumCurvatureKernel w r s m n' : ℂ)‖) atTop
      (𝓝 ‖fourierKernelAt (curlProjectionSymbol m n' r s) w - (continuumCurvatureKernel w r s m n' : ℂ)‖) := by
    refine ((hT.congr fun n => ?_).sub_const _).norm
    rw [inverseSymbolFourierSum_eq_mean]
  have hN : Tendsto (fun n : ℕ => ((2 * (n + 1) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun n => (by show n ≤ 2 * (n + 1); omega)) tendsto_id)
  have hlim2 : Tendsto (fun n : ℕ => C' * (sqNorm w ^ (-(5 / 2 : ℝ)) + ((2 * (n + 1) : ℕ) : ℝ) ^ (-(4 : ℤ))))
      atTop (𝓝 (C' * (sqNorm w ^ (-(5 / 2 : ℝ)) + 0))) := by
    refine (tendsto_const_nhds.add ?_).const_mul _
    have : Tendsto (fun x : ℝ => x ^ (-(4 : ℤ))) atTop (𝓝 0) := by
      simp only [zpow_neg]
      exact (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).inv_tendsto_atTop |>.congr fun x => by simp
    exact this.comp hN
  rw [add_zero] at hlim2
  refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
  have hev := hN.eventually_ge_atTop (max N₀ (8 * (1 + sqNorm w)))
  filter_upwards [hev] with n hn
  have hN₀ : N₀ ≤ ((2 * (n + 1) : ℕ) : ℝ) := (le_max_left _ _).trans hn
  have hN₁ : 8 * (1 + sqNorm w) ≤ ((2 * (n + 1) : ℕ) : ℝ) := (le_max_right _ _).trans hn
  have hsq : sqNorm w ≤ (((2 * (n + 1) : ℕ) : ℝ) / 8) ^ 2 := by
    nlinarith
  exact hC (2 * (n + 1)) 0 transverseSymbol r s m n' w hN₀ le_rfl (Real.exp_pos _).le hlow hrs hmn hw h1 hsq
private theorem norm_fourierKernelAt_le (m n' r s : Fin 4) (w : Fin 4 → ℝ) :
    ‖fourierKernelAt (curlProjectionSymbol m n' r s) w‖ ≤ 16 := by
  have hpi := Real.pi_pos
  have hfin : (volume : Measure (Fin 4 → ℝ)) brillouinBox < ⊤ := isCompact_Icc.measure_lt_top
  have hb : ‖∫ p in brillouinBox, fourierIntegrand m n' r s w p‖ ≤
      16 * (volume : Measure (Fin 4 → ℝ)).real brillouinBox :=
    norm_setIntegral_le_of_norm_le_const_ae hfin (Eventually.of_forall fun p => norm_fourierIntegrand_le m n' r s w p)
  have hv : (volume : Measure (Fin 4 → ℝ)).real brillouinBox = (2 * Real.pi) ^ 4 := by
    unfold brillouinBox
    rw [Measure.real, Real.volume_Icc_pi_toReal (fun i => by simp only []; linarith)]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    ring
  rw [hv] at hb
  have e : fourierKernelAt (curlProjectionSymbol m n' r s) w =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ ^ 4 * ∫ p in brillouinBox, fourierIntegrand m n' r s w p := rfl
  rw [e, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc _ ≤ (2 * Real.pi)⁻¹ ^ 4 * (16 * (2 * Real.pi) ^ 4) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 16 := by field_simp
theorem curlProjectionKernel_holds (hR : TendstoRiemannSumOfPeriodic)
    (hK : lowSymbolKernelStatement) (hV : ContinuumCurvatureKernelBoundAndLipschitz) :
    curlProjectionKernelStatement := by
  obtain ⟨B, hlow⟩ := transverse_isLowMomentumSymbol
  obtain ⟨C', N₀, hC⟩ := hK B 10 1 1 one_pos one_pos
  refine ⟨32 * (32 * |C'| + 12800) + 34 * 3125, ?_⟩
  intro z m n' r s hmn hrs hz
  set zc : Fin 4 → ℝ := fun i => (z i : ℝ) with hzc
  set w : Fin 4 → ℝ := plaquetteBarycentreShift z m n' r s with hwd
  have hLsq : intNormSq z = sqNorm zc := rfl
  have hmax : maxwellKernel z m n' r s = continuumCurvatureKernel zc r s m n' := by
    unfold maxwellKernel continuumCurvatureKernel reflectionEntry hyperplaneReflection
    rw [hLsq]
    have e : ∀ a b : Fin 4, (if a = b then (1 : ℝ) else 0) = if b = a then 1 else 0 := by
      intro a b
      by_cases h : a = b
      · simp [h]
      · have : b ≠ a := fun e => h e.symm
        simp [h, this]
    simp only [hzc]
    rw [e m r, e n' s, e m s, e n' r]
    ring
  have hz1 : 1 ≤ intNormSq z := by
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext h)
    have h1 : ((z i : ℝ)) ^ 2 ≤ intNormSq z :=
      Finset.single_le_sum (f := fun l => ((z l : ℝ)) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : (1 : ℤ) ≤ z i ^ 2 := by
      have : 0 < z i ^ 2 := by positivity
      omega
    have h3 : (1 : ℝ) ≤ ((z i : ℝ)) ^ 2 := by exact_mod_cast h2
    linarith
  set R := Real.sqrt (intNormSq z) with hRd
  have hR2 : R ^ 2 = intNormSq z := Real.sq_sqrt (by linarith)
  have hR1 : 1 ≤ R := by
    rw [hRd]
    exact Real.one_le_sqrt.2 hz1
  have hden : 0 < (1 + R) ^ 5 := by positivity
  by_cases hbig : 16 ≤ intNormSq z
  · have hw : ∀ i, ∃ u : ℤ, w i = u + ((if i = m then 1 else 0) + (if i = n' then 1 else 0) -
        (if i = r then 1 else 0) - (if i = s then 1 else 0)) / 2 := by
      intro i
      refine ⟨z i, ?_⟩
      simp only [hwd, plaquetteBarycentreShift]
      split_ifs <;> ring
    have hδ : ∀ l, (w l - zc l) ^ 2 ≤ 1 := by
      intro l
      simp only [hwd, hzc, plaquetteBarycentreShift]
      split_ifs <;> norm_num
    have hδs : sqNorm (w - zc) ≤ 4 := by
      unfold sqNorm
      calc ∑ i, (w - zc) i ^ 2 ≤ ∑ _i : Fin 4, (1 : ℝ) := Finset.sum_le_sum fun i _ => hδ i
        _ = 4 := by simp
    have hwl : R ^ 2 / 4 ≤ sqNorm w := by
      have h1 : sqNorm zc / 2 - sqNorm (w - zc) ≤ sqNorm w := by
        unfold sqNorm
        rw [Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        simp only [Pi.sub_apply]
        nlinarith [sq_nonneg (zc i + 2 * (w i - zc i))]
      rw [hR2, hLsq]
      rw [hLsq] at hbig
      linarith
    have h1w : 1 ≤ sqNorm w := by
      rw [hR2] at hwl
      linarith
    have hr : 0 < R / 2 := by positivity
    have hrw : (R / 2) ^ 2 ≤ sqNorm w := by
      have : (R / 2) ^ 2 = R ^ 2 / 4 := by ring
      rw [this]; exact hwl
    have hrz : (R / 2) ^ 2 ≤ sqNorm zc := by
      rw [← hLsq, ← hR2]; nlinarith
    have hv := (hV (R / 2) w zc r s m n' hr hrw hrz).2
    have hnear := fourierKernel_near_curvatureKernel hR hlow hC hmn hrs hw h1w
    have hA : sqNorm w ^ (-(5 / 2 : ℝ)) ≤ ((R / 2) ^ 5)⁻¹ := by
      have e : ((R / 2) ^ 2) ^ (-(5 / 2 : ℝ)) = ((R / 2) ^ 5)⁻¹ := by
        rw [← Real.rpow_natCast (R / 2) 2, ← Real.rpow_mul hr.le,
          show ((2 : ℕ) : ℝ) * -(5 / 2 : ℝ) = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg hr.le, Real.rpow_natCast]
      rw [← e]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hrw (by norm_num)
    have hA0 : 0 ≤ sqNorm w ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have hsq2 : Real.sqrt (sqNorm (w - zc)) ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt hδs
    have hC400 : |continuumCurvatureKernel w r s m n' - continuumCurvatureKernel zc r s m n'| ≤
        400 * ((R / 2) ^ 5)⁻¹ := by
      refine hv.trans ?_
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hinv : ((R / 2) ^ 5)⁻¹ ≤ 1024 * ((1 + R) ^ 5)⁻¹ := by
      have h1 : ((1 + R) / 4) ^ 5 ≤ (R / 2) ^ 5 := by
        refine pow_le_pow_left₀ (by positivity) ?_ 5
        linarith
      have h2 := inv_anti₀ (by positivity) h1
      refine h2.trans (le_of_eq ?_)
      rw [div_pow, inv_div]
      norm_num
      ring
    have hnear' : ‖fourierKernelAt (curlProjectionSymbol m n' r s) w - (continuumCurvatureKernel w r s m n' : ℂ)‖ ≤
        |C'| * ((R / 2) ^ 5)⁻¹ := by
      refine hnear.trans ?_
      calc C' * sqNorm w ^ (-(5 / 2 : ℝ)) ≤ |C'| * sqNorm w ^ (-(5 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hA0
        _ ≤ |C'| * ((R / 2) ^ 5)⁻¹ := mul_le_mul_of_nonneg_left hA (abs_nonneg _)
    have hmid : ‖(continuumCurvatureKernel w r s m n' : ℂ) - (continuumCurvatureKernel zc r s m n' : ℂ)‖ ≤
        400 * ((R / 2) ^ 5)⁻¹ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hC400
    rw [hmax]
    have hadd : fourierKernelAt (curlProjectionSymbol m n' r s) (plaquetteBarycentreShift z m n' r s) -
        (continuumCurvatureKernel zc r s m n' : ℂ) =
        (fourierKernelAt (curlProjectionSymbol m n' r s) w - (continuumCurvatureKernel w r s m n' : ℂ)) +
          ((continuumCurvatureKernel w r s m n' : ℂ) - (continuumCurvatureKernel zc r s m n' : ℂ)) := by
      rw [hwd]; ring
    rw [hadd]
    have hI : 0 ≤ ((1 + R) ^ 5)⁻¹ := by positivity
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ |C'| * ((R / 2) ^ 5)⁻¹ + 400 * ((R / 2) ^ 5)⁻¹ := add_le_add hnear' hmid
      _ = (|C'| + 400) * ((R / 2) ^ 5)⁻¹ := by ring
      _ ≤ (|C'| + 400) * (1024 * ((1 + R) ^ 5)⁻¹) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ (32 * (32 * |C'| + 12800) + 34 * 3125) * ((1 + R) ^ 5)⁻¹ := by
          have : (|C'| + 400) * (1024 * ((1 + R) ^ 5)⁻¹) =
              (32 * (32 * |C'| + 12800)) * ((1 + R) ^ 5)⁻¹ := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right (by norm_num) hI
  · have hk := norm_fourierKernelAt_le m n' r s (plaquetteBarycentreShift z m n' r s)
    have hone : (1 : ℝ) ^ 2 ≤ sqNorm zc := by rw [← hLsq]; simpa using hz1
    have hc := (hV 1 zc zc r s m n' one_pos hone hone).1
    have hc' : ‖(continuumCurvatureKernel zc r s m n' : ℂ)‖ ≤ 18 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      simpa using hc
    have hR4 : R < 4 := by
      have : R ^ 2 < 16 := by rw [hR2]; exact not_le.1 hbig
      nlinarith
    have hI : 1 ≤ 3125 * ((1 + R) ^ 5)⁻¹ := by
      have h1 : (1 + R) ^ 5 ≤ 5 ^ 5 := pow_le_pow_left₀ (by positivity) (by linarith) 5
      rw [← div_eq_mul_inv, le_div_iff₀ hden]
      norm_num at h1 ⊢
      linarith
    rw [hmax]
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ (34 : ℝ) := by linarith
      _ ≤ 34 * (3125 * ((1 + R) ^ 5)⁻¹) := by linarith
      _ ≤ (32 * (32 * |C'| + 12800) + 34 * 3125) * ((1 + R) ^ 5)⁻¹ := by
          have h2 : 0 ≤ 32 * (32 * |C'| + 12800) * ((1 + R) ^ 5)⁻¹ := by positivity
          nlinarith
end YangMills.Construction.LimitForms
end
