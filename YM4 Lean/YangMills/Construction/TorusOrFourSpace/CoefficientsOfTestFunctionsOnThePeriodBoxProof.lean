import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes.FifthPartProof
import YangMills.Construction.TorusOrFourSpace.CoefficientsOfTestFunctionsOnThePeriodBox
import YangMills.Construction.TorusOrFourSpace.DistanceOpenSetsDerivativesAndTensorsOfSeveralPoints
import Mathlib
set_option autoImplicit false
open scoped ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PeriodCell.Fourier
def ballPoints (p : ℕ+) (n : ℕ) : Finset (IntCoords p) :=
  Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) (n : ℤ)
theorem mem_ballPoints {p : ℕ+} (n : ℕ) (k : IntCoords p) :
    k ∈ ballPoints p n ↔ k.maxAbs ≤ n := by
  simp only [ballPoints, IntCoords.maxAbs, Fintype.mem_piFinset, Finset.mem_Icc,
    Finset.sup_le_iff, Finset.mem_univ, true_implies]
  exact forall_congr' fun j => by omega
theorem card_ballPoints {p : ℕ+} (n : ℕ) :
    (ballPoints p n).card = (2 * n + 1) ^ (4 * (p : ℕ)) := by
  simp only [ballPoints, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  omega
theorem add_pow_succ_le_pow_add (b c n : ℕ) :
    (b + c) ^ (n + 1) ≤ b ^ (n + 1) + (n + 1) * c * (b + c) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (b + c) ^ (n + 1 + 1) = b * (b + c) ^ (n + 1) + c * (b + c) ^ (n + 1) := by ring
    have h2 : b * (b + c) ^ (n + 1) ≤ b * (b ^ (n + 1) + (n + 1) * c * (b + c) ^ n) :=
      Nat.mul_le_mul_left _ ih
    have h3 : b * ((n + 1) * c * (b + c) ^ n) ≤ (n + 1) * c * (b + c) ^ (n + 1) := by
      calc b * ((n + 1) * c * (b + c) ^ n) = (n + 1) * c * (b * (b + c) ^ n) := by ring
        _ ≤ (n + 1) * c * ((b + c) * (b + c) ^ n) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
        _ = (n + 1) * c * (b + c) ^ (n + 1) := by ring
    have h4 : b * (b ^ (n + 1) + (n + 1) * c * (b + c) ^ n) =
        b ^ (n + 1 + 1) + b * ((n + 1) * c * (b + c) ^ n) := by ring
    have h5 : (n + 1 + 1) * c * (b + c) ^ (n + 1) =
        (n + 1) * c * (b + c) ^ (n + 1) + c * (b + c) ^ (n + 1) := by ring
    rw [h1, h5]
    omega
def shellPoints (p : ℕ+) (s : ℕ) : Finset (IntCoords p) :=
  ballPoints p s \ ballPoints p (s - 1)
theorem mem_shellPoints {p : ℕ+} {s : ℕ} (hs : 1 ≤ s) (k : IntCoords p) :
    k ∈ shellPoints p s ↔ k.maxAbs = s := by
  simp only [shellPoints, Finset.mem_sdiff, mem_ballPoints]
  omega
theorem card_shellPoints_le {p : ℕ+} {s : ℕ} (hs : 1 ≤ s) :
    (shellPoints p s).card ≤ 2 * (4 * (p : ℕ)) * (3 * s) ^ (4 * (p : ℕ) - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, 4 * (p : ℕ) = m + 1 := ⟨4 * (p : ℕ) - 1, by have := p.pos; omega⟩
  have hsub : ballPoints p (s - 1) ⊆ ballPoints p s := fun k hk => by
    rw [mem_ballPoints] at hk ⊢
    omega
  rw [shellPoints, Finset.card_sdiff_of_subset hsub, card_ballPoints, card_ballPoints, hm]
  simp only [Nat.add_sub_cancel]
  have e : 2 * s + 1 = (2 * (s - 1) + 1) + 2 := by omega
  have h := add_pow_succ_le_pow_add (2 * (s - 1) + 1) 2 m
  rw [← e] at h
  have h3 : (2 * s + 1) ^ m ≤ (3 * s) ^ m := Nat.pow_le_pow_left (by omega) m
  have h4 : (m + 1) * 2 * (2 * s + 1) ^ m ≤ 2 * (m + 1) * (3 * s) ^ m := by
    calc (m + 1) * 2 * (2 * s + 1) ^ m = 2 * (m + 1) * (2 * s + 1) ^ m := by ring
      _ ≤ 2 * (m + 1) * (3 * s) ^ m := Nat.mul_le_mul_left _ h3
  omega
theorem encard_maxAbs_eq_le {p : ℕ+} (s : ℕ+) :
    Set.encard {k' : IntCoords p | k'.maxAbs = (s : ℕ)} ≤
      ((2 * (4 * (p : ℕ)) * (3 * (s : ℕ)) ^ (4 * (p : ℕ) - 1) : ℕ) : ℕ∞) := by
  have h : {k' : IntCoords p | k'.maxAbs = (s : ℕ)} = ↑(shellPoints p (s : ℕ)) := by
    ext k
    simp [mem_shellPoints (p := p) (s := (s : ℕ)) s.pos k]
  rw [h, Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast card_shellPoints_le (p := p) (s := (s : ℕ)) s.pos
theorem pi_sq_div_six_le_two : Real.pi ^ 2 / 6 ≤ 2 := by
  have h1 := Real.pi_lt_d2
  have h2 := Real.pi_pos
  nlinarith
theorem hasSum_inv_sq_pnat :
    HasSum (fun s : ℕ+ => (((s : ℕ) : ℝ) ^ 2)⁻¹) (Real.pi ^ 2 / 6) := by
  have h := hasSum_zeta_two
  have hinj : Function.Injective (fun s : ℕ+ => (s : ℕ)) := PNat.coe_injective
  have hz : ∀ x ∉ Set.range (fun s : ℕ+ => (s : ℕ)), (1 / (x : ℝ) ^ 2) = 0 := by
    intro x hx
    have : x = 0 := by
      by_contra h0
      exact hx ⟨⟨x, Nat.pos_of_ne_zero h0⟩, rfl⟩
    simp [this]
  have h' := (hinj.hasSum_iff hz).2 h
  simpa [Function.comp_def, one_div] using h'
theorem summable_tsum_inv_sq_pnat_le :
    Summable (fun s : ℕ+ => (((s : ℕ) : ℝ) ^ 2)⁻¹) ∧
      ∑' s : ℕ+, (((s : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2 :=
  ⟨hasSum_inv_sq_pnat.summable, hasSum_inv_sq_pnat.tsum_eq ▸ pi_sq_div_six_le_two⟩
theorem one_le_maxAbs {p : ℕ+} {k : IntCoords p} (hk : k ≠ 0) : 1 ≤ k.maxAbs := by
  by_contra h
  apply hk
  funext j
  have hj : (k j).natAbs ≤ k.maxAbs :=
    Finset.le_sup (f := fun j => (k j).natAbs) (Finset.mem_univ j)
  have : (k j).natAbs = 0 := by omega
  simpa using this
theorem sum_shellPoints_inv_pow_le {p : ℕ+} {s : ℕ} (hs : 1 ≤ s) :
    ∑ k ∈ shellPoints p s, ((k.maxAbs : ℝ) ^ (4 * (p : ℕ) + 1))⁻¹ ≤
      2 * (4 * ((p : ℕ) : ℝ)) * 3 ^ (4 * (p : ℕ) - 1) * (1 / (s : ℝ) ^ 2) := by
  obtain ⟨m, hm⟩ : ∃ m, 4 * (p : ℕ) = m + 1 := ⟨4 * (p : ℕ) - 1, by have := p.pos; omega⟩
  have hsum : ∑ k ∈ shellPoints p s, ((k.maxAbs : ℝ) ^ (4 * (p : ℕ) + 1))⁻¹ =
      ((shellPoints p s).card : ℝ) * ((s : ℝ) ^ (4 * (p : ℕ) + 1))⁻¹ := by
    rw [Finset.sum_congr rfl (g := fun _ => ((s : ℝ) ^ (4 * (p : ℕ) + 1))⁻¹)
      (fun k hk => by rw [(mem_shellPoints hs k).1 hk])]
    simp
  have hcard : ((shellPoints p s).card : ℝ) ≤
      2 * (4 * ((p : ℕ) : ℝ)) * (3 * (s : ℝ)) ^ (4 * (p : ℕ) - 1) := by
    exact_mod_cast card_shellPoints_le (p := p) hs
  rw [hsum]
  calc ((shellPoints p s).card : ℝ) * ((s : ℝ) ^ (4 * (p : ℕ) + 1))⁻¹
      ≤ (2 * (4 * ((p : ℕ) : ℝ)) * (3 * (s : ℝ)) ^ (4 * (p : ℕ) - 1)) *
          ((s : ℝ) ^ (4 * (p : ℕ) + 1))⁻¹ :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * (4 * ((p : ℕ) : ℝ)) * 3 ^ (4 * (p : ℕ) - 1) * (1 / (s : ℝ) ^ 2) := by
        rw [hm]
        simp only [Nat.add_sub_cancel]
        rw [mul_pow]
        field_simp
        ring
theorem sum_inv_maxAbs_pow_le {p : ℕ+} (U : Finset (IntCoords p)) (hU : ∀ k ∈ U, k ≠ 0) :
    ∑ k ∈ U, ((k.maxAbs : ℝ) ^ (4 * (p : ℕ) + 1))⁻¹ ≤
      4 * (4 * ((p : ℕ) : ℝ)) * 3 ^ (4 * (p : ℕ) - 1) := by
  classical
  set N : ℕ := U.sup fun k => k.maxAbs with hN
  have hsub : U ⊆ (Finset.Icc 1 N).biUnion (shellPoints p) := by
    intro k hk
    have h1 := one_le_maxAbs (hU k hk)
    have h2 : k.maxAbs ≤ N := Finset.le_sup (f := fun k : IntCoords p => k.maxAbs) hk
    exact Finset.mem_biUnion.2 ⟨k.maxAbs, Finset.mem_Icc.2 ⟨h1, h2⟩, (mem_shellPoints h1 k).2 rfl⟩
  have hdisj : ((Finset.Icc 1 N : Finset ℕ) : Set ℕ).PairwiseDisjoint (shellPoints p) := by
    intro a ha b hb hab
    have ha1 : 1 ≤ a := (Finset.mem_Icc.1 (Finset.mem_coe.1 ha)).1
    have hb1 : 1 ≤ b := (Finset.mem_Icc.1 (Finset.mem_coe.1 hb)).1
    refine Finset.disjoint_left.2 fun k hka hkb => hab ?_
    rw [← (mem_shellPoints ha1 k).1 hka, ← (mem_shellPoints hb1 k).1 hkb]
  have hc : (0 : ℝ) ≤ 2 * (4 * ((p : ℕ) : ℝ)) * 3 ^ (4 * (p : ℕ) - 1) := by positivity
  calc ∑ k ∈ U, ((k.maxAbs : ℝ) ^ (4 * (p : ℕ) + 1))⁻¹
      ≤ ∑ k ∈ (Finset.Icc 1 N).biUnion (shellPoints p),
          ((k.maxAbs : ℝ) ^ (4 * (p : ℕ) + 1))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∑ s ∈ Finset.Icc 1 N, ∑ k ∈ shellPoints p s, ((k.maxAbs : ℝ) ^ (4 * (p : ℕ) + 1))⁻¹ :=
        Finset.sum_biUnion hdisj
    _ ≤ ∑ s ∈ Finset.Icc 1 N,
          2 * (4 * ((p : ℕ) : ℝ)) * 3 ^ (4 * (p : ℕ) - 1) * (1 / (s : ℝ) ^ 2) :=
        Finset.sum_le_sum fun s hs => sum_shellPoints_inv_pow_le (Finset.mem_Icc.1 hs).1
    _ = 2 * (4 * ((p : ℕ) : ℝ)) * 3 ^ (4 * (p : ℕ) - 1) *
          ∑ s ∈ Finset.Icc 1 N, 1 / (s : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * (4 * ((p : ℕ) : ℝ)) * 3 ^ (4 * (p : ℕ) - 1) * 2 :=
        mul_le_mul_of_nonneg_left
          ((sum_le_hasSum _ (fun _ _ => by positivity) hasSum_zeta_two).trans
            pi_sq_div_six_le_two) hc
    _ = 4 * (4 * ((p : ℕ) : ℝ)) * 3 ^ (4 * (p : ℕ) - 1) := by ring
theorem summable_tsum_inv_maxAbs_pow_le (p : ℕ+) :
    Summable (fun k' : {k' : IntCoords p // k' ≠ 0} =>
        ((k'.1.maxAbs : ℝ) ^ (4 * (p : ℕ) + 1))⁻¹) ∧
      ∑' k' : {k' : IntCoords p // k' ≠ 0}, ((k'.1.maxAbs : ℝ) ^ (4 * (p : ℕ) + 1))⁻¹ ≤
        4 * (4 * ((p : ℕ) : ℝ)) * 3 ^ (4 * (p : ℕ) - 1) := by
  classical
  have hb : ∀ T : Finset {k' : IntCoords p // k' ≠ 0},
      ∑ k' ∈ T, ((k'.1.maxAbs : ℝ) ^ (4 * (p : ℕ) + 1))⁻¹ ≤
        4 * (4 * ((p : ℕ) : ℝ)) * 3 ^ (4 * (p : ℕ) - 1) := by
    intro T
    have := sum_inv_maxAbs_pow_le (T.map (Function.Embedding.subtype _)) (by
      intro k hk
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hk
      exact a.2)
    simpa [Finset.sum_map] using this
  have hs : Summable (fun k' : {k' : IntCoords p // k' ≠ 0} =>
      ((k'.1.maxAbs : ℝ) ^ (4 * (p : ℕ) + 1))⁻¹) :=
    summable_of_sum_le (fun _ => by positivity) hb
  exact ⟨hs, hasSum_le_of_sum_le hs.hasSum hb⟩
open MeasureTheory Filter Topology
def freq {p : ℕ+} (P : ℝ) (k : IntCoords p) (j : Fin (4 * (p : ℕ))) : ℂ :=
  2 * Real.pi * Complex.I * (k j : ℂ) / (P : ℂ)
theorem pairing_add_smul_single {p : ℕ+} (k : IntCoords p) (u : Coords p)
    (j : Fin (4 * (p : ℕ))) (t : ℝ) :
    k.pairing (u + t • Pi.single j (1 : ℝ)) = k.pairing u + t * (k j : ℝ) := by
  simp only [IntCoords.pairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
    ring
  · intro b _ hb
    simp [hb]
  · simp
theorem hasDerivAt_fourierChar_line {p : ℕ+} (P : ℝ) (k : IntCoords p) (u : Coords p)
    (j : Fin (4 * (p : ℕ))) :
    HasDerivAt (fun t : ℝ => fourierChar P k (u + t • Pi.single j (1 : ℝ)))
      (freq P k j * fourierChar P k u) 0 := by
  have h0 : HasDerivAt (fun t : ℝ => k.pairing u + t * (k j : ℝ)) ((k j : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (k j : ℝ)).const_add (k.pairing u)
  have h1 : HasDerivAt (fun t : ℝ => ((k.pairing u + t * (k j : ℝ) : ℝ) : ℂ)) (((k j : ℝ)) : ℂ) 0 :=
    h0.ofReal_comp
  have h2 := ((h1.const_mul (2 * (Real.pi : ℂ) * Complex.I)).div_const (P : ℂ)).cexp
  have e : (fun t : ℝ => fourierChar P k (u + t • Pi.single j (1 : ℝ))) =
      fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((k.pairing u + t * (k j : ℝ) : ℝ) : ℂ) / (P : ℂ)) := by
    funext t
    rw [fourierChar, pairing_add_smul_single]
  rw [e]
  convert h2 using 1
  simp only [freq, fourierChar, zero_mul, add_zero]
  push_cast
  ring
theorem hasLineDerivAt_fourierChar {p : ℕ+} (P : ℝ) (k : IntCoords p) (u : Coords p)
    (j : Fin (4 * (p : ℕ))) :
    HasLineDerivAt ℝ (fourierChar P k) (freq P k j * fourierChar P k u) u
      (Pi.single j (1 : ℝ)) :=
  hasDerivAt_fourierChar_line P k u j
theorem conj_fourierChar {p : ℕ+} (P : ℝ) (k : IntCoords p) (u : Coords p) :
    conj (fourierChar P k u) = fourierChar P (-k) u := by
  have hd : (-k).pairing u = -k.pairing u := by
    simp [IntCoords.pairing, Finset.sum_neg_distrib]
  rw [fourierChar, fourierChar, ← Complex.exp_conj, hd]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  ring
theorem freq_neg {p : ℕ+} (P : ℝ) (k : IntCoords p) (j : Fin (4 * (p : ℕ))) :
    freq P (-k) j = -freq P k j := by
  simp only [freq, Pi.neg_apply]
  push_cast
  ring
theorem norm_fourierChar {p : ℕ+} (P : ℝ) (k : IntCoords p) (u : Coords p) :
    ‖fourierChar P k u‖ = 1 := by
  have : 2 * (Real.pi : ℂ) * Complex.I * ((k.pairing u : ℝ) : ℂ) / (P : ℂ) =
      ((2 * Real.pi * k.pairing u / P : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [fourierChar, this, Complex.norm_exp_ofReal_mul_I]
theorem continuous_fourierChar {p : ℕ+} (P : ℝ) (k : IntCoords p) :
    Continuous (fourierChar P k) := by
  have hd : Continuous fun u : Coords p => k.pairing u :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  have : Continuous fun u : Coords p => (2 * (Real.pi : ℂ) * Complex.I *
      ((k.pairing u : ℝ) : ℂ) / (P : ℂ)) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hd)).div_const _
  exact Complex.continuous_exp.comp this
theorem partialAlong_sum {p : ℕ+} (P : ℝ) (S : Finset (IntCoords p))
    (c : IntCoords p → ℂ) (j : Fin (4 * (p : ℕ))) :
    Coords.partialAlong j (fun u => ∑ k ∈ S, c k * fourierChar P k u) =
      fun u => ∑ k ∈ S, (c k * freq P k j) * fourierChar P k u := by
  funext u
  have h : HasDerivAt
      (fun t : ℝ => ∑ k ∈ S, c k * fourierChar P k (u + t • Pi.single j (1 : ℝ)))
      (∑ k ∈ S, c k * (freq P k j * fourierChar P k u)) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_fourierChar_line P k u j).const_mul (c k)
  have h2 : HasLineDerivAt ℝ (fun u => ∑ k ∈ S, c k * fourierChar P k u)
      (∑ k ∈ S, c k * (freq P k j * fourierChar P k u)) u (Pi.single j (1 : ℝ)) := h
  rw [Coords.partialAlong, h2.lineDeriv]
  exact Finset.sum_congr rfl fun k _ => by ring
theorem iterate_partialAlong_sum {p : ℕ+} (P : ℝ) (S : Finset (IntCoords p))
    (j : Fin (4 * (p : ℕ))) (n : ℕ) (c : IntCoords p → ℂ) :
    (Coords.partialAlong j)^[n] (fun u => ∑ k ∈ S, c k * fourierChar P k u) =
      fun u => ∑ k ∈ S, (c k * freq P k j ^ n) * fourierChar P k u := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, partialAlong_sum, ih]
    funext u
    exact Finset.sum_congr rfl fun k _ => by ring
theorem foldr_partialAlong_sum {p : ℕ+} (P : ℝ) (S : Finset (IntCoords p))
    (α : CoordIndex p) (c : IntCoords p → ℂ) (l : List (Fin (4 * (p : ℕ)))) :
    l.foldr (fun j H => (Coords.partialAlong j)^[α j] H)
        (fun u => ∑ k ∈ S, c k * fourierChar P k u) =
      fun u => ∑ k ∈ S,
        (c k * (l.map fun j => freq P k j ^ α j).prod) * fourierChar P k u := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, ih]
    have := iterate_partialAlong_sum P S a (α a)
      (fun k => c k * (l.map fun j => freq P k j ^ α j).prod)
    rw [this]
    funext u
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [List.map_cons, List.prod_cons]
    ring
theorem fourierMultiplier_eq_prod {p : ℕ+} (P : ℝ) (k : IntCoords p) (α : CoordIndex p) :
    fourierMultiplier P k α =
      ((List.finRange (4 * (p : ℕ))).map fun j => freq P k j ^ α j).prod := by
  rw [fourierMultiplier, Fin.prod_univ_def]
  rfl
theorem iterPartial_sum {p : ℕ+} (P : ℝ) (S : Finset (IntCoords p))
    (α : CoordIndex p) (c : IntCoords p → ℂ) :
    Coords.iterPartial α (fun u => ∑ k ∈ S, c k * fourierChar P k u) =
      fun u => ∑ k ∈ S, (c k * fourierMultiplier P k α) * fourierChar P k u := by
  rw [Coords.iterPartial, foldr_partialAlong_sum]
  funext u
  exact Finset.sum_congr rfl fun k _ => by rw [fourierMultiplier_eq_prod]
theorem iterPartial_fourierChar {p : ℕ+} (P : ℝ) (α : CoordIndex p)
    (k : IntCoords p) :
    Coords.iterPartial α (fourierChar P k) =
      fun u => fourierMultiplier P k α * fourierChar P k u := by
  have h := iterPartial_sum P {k} α (fun _ => 1)
  simpa using h
def SmoothInCube {p : ℕ+} (P : ℝ) (G : Coords p → ℂ) : Prop :=
  (∀ ν, Coords.ContPartialsUpTo ν G) ∧
    ∃ K : Set (Coords p), IsCompact K ∧ K ⊆ coordCube p P ∧ ∀ u ∉ K, G u = 0
def cubeIntegral {p : ℕ+} (P : ℝ) (k : IntCoords p) (G : Coords p → ℂ) : ℂ :=
  ∫ u in coordCube p P, G u * conj (fourierChar P k u)
theorem SmoothInCube.continuous {p : ℕ+} {P : ℝ} {G : Coords p → ℂ}
    (hG : SmoothInCube P G) : Continuous G :=
  hG.1 0
theorem SmoothInCube.hasCompactSupport {p : ℕ+} {P : ℝ} {G : Coords p → ℂ}
    (hG : SmoothInCube P G) : HasCompactSupport G := by
  obtain ⟨-, K, hK, -, h0⟩ := hG
  exact HasCompactSupport.intro hK h0
theorem SmoothInCube.zero_off {p : ℕ+} {P : ℝ} {G : Coords p → ℂ}
    (hG : SmoothInCube P G) (u : Coords p) (hu : u ∉ coordCube p P) : G u = 0 := by
  obtain ⟨-, K, -, hKb, h0⟩ := hG
  exact h0 u fun h => hu (hKb h)
theorem SmoothInCube.integrable_mul {p : ℕ+} {P : ℝ} {G : Coords p → ℂ}
    (hG : SmoothInCube P G) (k : IntCoords p) :
    Integrable fun u => G u * fourierChar P k u :=
  (hG.continuous.mul (continuous_fourierChar P k)).integrable_of_hasCompactSupport
    hG.hasCompactSupport.mul_right
theorem SmoothInCube.partialAlong {p : ℕ+} {P : ℝ} {G : Coords p → ℂ}
    (hG : SmoothInCube P G) (j : Fin (4 * (p : ℕ))) :
    SmoothInCube P (Coords.partialAlong j G) := by
  obtain ⟨hs, K, hK, hKb, h0⟩ := hG
  refine ⟨fun ν => ((hs (ν + 1)).2 j).2, K, hK, hKb, fun u hu => ?_⟩
  have hev : ∀ᶠ v in 𝓝 u, v ∉ K := hK.isClosed.isOpen_compl.mem_nhds hu
  have hc : ContinuousAt (fun t : ℝ => u + t • Pi.single j (1 : ℝ)) 0 := by fun_prop
  have hc0 : Tendsto (fun t : ℝ => u + t • Pi.single j (1 : ℝ)) (𝓝 0) (𝓝 u) := by
    simpa [ContinuousAt] using hc
  have hz : (fun t : ℝ => G (u + t • Pi.single j (1 : ℝ))) =ᶠ[𝓝 0] fun _ => 0 :=
    (hc0.eventually hev).mono fun t ht => h0 _ ht
  rw [Coords.partialAlong, lineDeriv, hz.deriv_eq]
  simp
theorem cubeIntegral_partialAlong {p : ℕ+} {P : ℝ} {G : Coords p → ℂ}
    (hG : SmoothInCube P G) (j : Fin (4 * (p : ℕ))) (k : IntCoords p) :
    cubeIntegral P k (Coords.partialAlong j G) =
      freq P k j * cubeIntegral P k G := by
  have hG' := hG.partialAlong j
  have e1 : cubeIntegral P k G = ∫ u, G u * fourierChar P (-k) u := by
    rw [cubeIntegral, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · simp only [conj_fourierChar]
    · intro u hu
      rw [hG.zero_off u hu, zero_mul]
  have e2 : cubeIntegral P k (Coords.partialAlong j G) =
      ∫ u, Coords.partialAlong j G u * fourierChar P (-k) u := by
    rw [cubeIntegral, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · simp only [conj_fourierChar]
    · intro u hu
      rw [hG'.zero_off u hu, zero_mul]
  have hline : ∀ x, HasLineDerivAt ℝ G (Coords.partialAlong j G x) x
      (Pi.single j (1 : ℝ)) := fun x => (((hG.1 1).2 j).1 x).hasLineDerivAt
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Coords p)))
    (f := G) (f' := Coords.partialAlong j G) (g := fourierChar P (-k))
    (g' := fun u => freq P (-k) j * fourierChar P (-k) u) (v := Pi.single j (1 : ℝ))
    (B := ContinuousLinearMap.mul ℝ ℂ)
    (by simpa using hG'.integrable_mul (-k))
    (by
      have := (hG.integrable_mul (-k)).const_mul (freq P (-k) j)
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp only [ContinuousLinearMap.mul_apply']
      ring)
    (by simpa using hG.integrable_mul (-k))
    (fun x _ => hline x) (fun x _ => hasLineDerivAt_fourierChar P (-k) x j)
  simp only [ContinuousLinearMap.mul_apply'] at key
  have e3 : ∫ u, G u * (freq P (-k) j * fourierChar P (-k) u) =
      freq P (-k) j * ∫ u, G u * fourierChar P (-k) u := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun u => by simp only []; ring)
  rw [e3, freq_neg] at key
  rw [e1, e2]
  linear_combination key
theorem smoothInCube_cubeIntegral_iterate {p : ℕ+} {P : ℝ} (j : Fin (4 * (p : ℕ))) (n : ℕ)
    (k : IntCoords p) {G : Coords p → ℂ} (hG : SmoothInCube P G) :
    SmoothInCube P ((Coords.partialAlong j)^[n] G) ∧
      cubeIntegral P k ((Coords.partialAlong j)^[n] G) =
        freq P k j ^ n * cubeIntegral P k G := by
  induction n generalizing G with
  | zero => simpa using hG
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨h1, h2⟩ := ih (hG.partialAlong j)
    refine ⟨h1, ?_⟩
    rw [h2, cubeIntegral_partialAlong hG, pow_succ]
    ring
theorem smoothInCube_cubeIntegral_foldr {p : ℕ+} {P : ℝ} (α : CoordIndex p)
    (k : IntCoords p) {G : Coords p → ℂ} (hG : SmoothInCube P G)
    (l : List (Fin (4 * (p : ℕ)))) :
    SmoothInCube P (l.foldr (fun j H => (Coords.partialAlong j)^[α j] H) G) ∧
      cubeIntegral P k (l.foldr (fun j H => (Coords.partialAlong j)^[α j] H) G) =
        (l.map fun j => freq P k j ^ α j).prod * cubeIntegral P k G := by
  induction l with
  | nil => simpa using hG
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := smoothInCube_cubeIntegral_iterate a (α a) k h1
    refine ⟨h3, ?_⟩
    rw [List.foldr_cons, h4, h2, List.map_cons, List.prod_cons]
    ring
theorem cubeIntegral_iterPartial {p : ℕ+} {P : ℝ} {G : Coords p → ℂ}
    (hG : SmoothInCube P G) (α : CoordIndex p) (k : IntCoords p) :
    cubeIntegral P k (Coords.iterPartial α G) =
      fourierMultiplier P k α * cubeIntegral P k G := by
  rw [fourierMultiplier_eq_prod]
  exact (smoothInCube_cubeIntegral_foldr α k hG _).2
theorem iterPartial_zero {p : ℕ+} (G : Coords p → ℂ) :
    Coords.iterPartial (0 : CoordIndex p) G = G := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading.iterPartial_zero <;> assumption
theorem coordCube_eq_pi (p : ℕ+) (P : ℝ) :
    coordCube p P = Set.pi Set.univ fun _ => Set.Ioo (-P / 2) (P / 2) := by
  ext u
  simp [coordCube]
theorem measurableSet_coordCube (p : ℕ+) (P : ℝ) : MeasurableSet (coordCube p P) := by
  rw [coordCube_eq_pi]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioo
theorem volume_coordCube (p : ℕ+) {P : ℝ} (hP : 0 < P) :
    volume (coordCube p P) = ENNReal.ofReal (P ^ (4 * (p : ℕ))) := by
  rw [coordCube_eq_pi, Real.volume_pi_Ioo]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hP.le]
  congr 2
  ring
theorem fourierCoeff_eq (D : Params) {p : ℕ+} (P : ℝ)
    (F : Kind.euclidean.Tuple D p → ℂ) (k : IntCoords p) :
    fourierCoeff D P F k = ((P : ℂ) ^ (4 * (p : ℕ)))⁻¹ *
      cubeIntegral P k (F ∘ Kind.Tuple.proj D Kind.euclidean) :=
  rfl
theorem fourierCoeff_norm_le (D : Params) {p : ℕ+} {P : ℝ} (hP : 0 < P)
    (F : Kind.euclidean.Tuple D p → ℂ) (B : ℝ≥0∞)
    (hB : ∀ y, ENNReal.ofReal ‖F y‖ ≤ B) (k : IntCoords p) :
    ENNReal.ofReal ‖fourierCoeff D P F k‖ ≤ B := by
  by_cases hinf : B = ∞
  · simp [hinf]
  have hb : ∀ y, ‖F y‖ ≤ B.toReal := fun y => (ENNReal.ofReal_le_iff_le_toReal hinf).1 (hB y)
  have hvol : volume (coordCube p P) < ∞ := by
    rw [volume_coordCube p hP]
    exact ENNReal.ofReal_lt_top
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := coordCube p P)
    (f := fun u => F (Kind.Tuple.proj D Kind.euclidean u) *
      conj (fourierChar P k u)) (C := B.toReal) hvol (fun u _ => by
        rw [norm_mul, RCLike.norm_conj, norm_fourierChar, mul_one]
        exact hb _)
  have hreal : volume.real (coordCube p P) = P ^ (4 * (p : ℕ)) := by
    rw [Measure.real, volume_coordCube p hP, ENNReal.toReal_ofReal (by positivity)]
  rw [hreal] at hint
  have hpos : 0 < P ^ (4 * (p : ℕ)) := by positivity
  have hc : ‖fourierCoeff D P F k‖ ≤ B.toReal := by
    rw [fourierCoeff, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hP.le,
      inv_mul_le_iff₀ hpos, mul_comm (P ^ _)]
    exact hint
  calc ENNReal.ofReal ‖fourierCoeff D P F k‖ ≤ ENNReal.ofReal B.toReal :=
        ENNReal.ofReal_le_ofReal hc
    _ = B := ENNReal.ofReal_toReal hinf
def blockIndexEquiv (p : ℕ+) : Fin (p : ℕ) × Fin 4 ≃ Fin (4 * (p : ℕ)) where
  toFun x := ⟨4 * (x.1 : ℕ) + (x.2 : ℕ), by have := x.1.2; have := x.2.2; omega⟩
  invFun j := (⟨(j : ℕ) / 4, by have := j.2; omega⟩, ⟨(j : ℕ) % 4, by omega⟩)
  left_inv x := by
    have h1 := x.1.2
    have h2 := x.2.2
    ext <;> simp <;> omega
  right_inv j := by
    ext
    simp only
    omega
abbrev unfoldMap (D : Params) (p : ℕ+) : Coords p → Kind.euclidean.Tuple D p :=
  Kind.Tuple.proj D Kind.euclidean
theorem unfoldMap_injective (D : Params) (p : ℕ+) : Function.Injective (unfoldMap D p) := by
  intro x x' h
  funext j
  obtain ⟨⟨i, μ⟩, rfl⟩ := (blockIndexEquiv p).surjective j
  exact congrFun (congrFun h i) μ
theorem unfoldMap_surjective (D : Params) (p : ℕ+) : Function.Surjective (unfoldMap D p) := by
  intro y
  refine ⟨fun j => y ((blockIndexEquiv p).symm j).1 ((blockIndexEquiv p).symm j).2, ?_⟩
  funext i
  funext μ
  have h : (blockIndexEquiv p).symm (blockIndexEquiv p (i, μ)) = (i, μ) :=
    Equiv.symm_apply_apply _ _
  change y ((blockIndexEquiv p).symm (blockIndexEquiv p (i, μ))).1
    ((blockIndexEquiv p).symm (blockIndexEquiv p (i, μ))).2 = y i μ
  rw [h]
theorem isCompact_unfoldMap_preimage (D : Params) (p : ℕ+)
    (hopen : TupleFacts.ProjOpenMap D Kind.euclidean p)
    {S : Set (Kind.euclidean.Tuple D p)}
    (hS : Kind.Tuple.IsCompactT D Kind.euclidean S) :
    IsCompact (unfoldMap D p ⁻¹' S) := by
  classical
  apply isCompact_of_finite_subcover
  intro ι U hU hcov
  obtain ⟨𝒰', hsub, hfin, hcov'⟩ := hS (Set.range fun i => unfoldMap D p '' U i)
    (by
      rintro _ ⟨i, rfl⟩
      exact hopen _ (hU i))
    (by
      intro y hy
      obtain ⟨x, rfl⟩ := unfoldMap_surjective D p y
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hy)
      exact ⟨unfoldMap D p '' U i, ⟨i, rfl⟩, ⟨x, hi, rfl⟩⟩)
  have hch : ∀ V : 𝒰', ∃ i, unfoldMap D p '' U i = V.1 := fun V => hsub V.2
  choose f hf using hch
  have := hfin.fintype
  refine ⟨Finset.univ.image f, fun x hx => ?_⟩
  obtain ⟨V, hV, hxV⟩ := hcov' hx
  have hxV' : unfoldMap D p x ∈ unfoldMap D p '' U (f ⟨V, hV⟩) := by
    rw [hf ⟨V, hV⟩]
    exact hxV
  obtain ⟨x', hx', e⟩ := hxV'
  have : x' = x := unfoldMap_injective D p e
  subst this
  exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem f (Finset.mem_univ _))) hx'
theorem smoothInCube_of_mem (D : Params) (p : ℕ+) (P : ℝ)
    (hmetric : TupleFacts.DistIsMetric D Kind.euclidean p)
    (hopen : TupleFacts.ProjOpenMap D Kind.euclidean p)
    {F : Kind.euclidean.Tuple D p → ℂ} (hF : F ∈ cellTestFns D p P) :
    SmoothInCube P (F ∘ unfoldMap D p) := by
  refine ⟨fun ν => hF.1 ν, unfoldMap D p ⁻¹' Kind.Tuple.supportT D Kind.euclidean F,
    isCompact_unfoldMap_preimage D p hopen hF.2.1, ?_, ?_⟩
  · intro u hu j
    obtain ⟨⟨i, μ⟩, rfl⟩ := (blockIndexEquiv p).surjective j
    exact hF.2.2 hu i μ
  · intro u hu
    by_contra hne
    apply hu
    intro r hr
    refine ⟨unfoldMap D p u, hne, ?_⟩
    rw [(hmetric.2.1 _ _).2 rfl]
    exact hr
theorem cubeIntegral_add {p : ℕ+} {P : ℝ} {G G' : Coords p → ℂ}
    (hG : SmoothInCube P G) (hG' : SmoothInCube P G') (k : IntCoords p) :
    cubeIntegral P k (G + G') = cubeIntegral P k G + cubeIntegral P k G' := by
  have h1 : Integrable fun u => G u * conj (fourierChar P k u) := by
    simpa only [conj_fourierChar] using hG.integrable_mul (-k)
  have h2 : Integrable fun u => G' u * conj (fourierChar P k u) := by
    simpa only [conj_fourierChar] using hG'.integrable_mul (-k)
  simp only [cubeIntegral, Pi.add_apply, add_mul]
  exact integral_add h1.integrableOn h2.integrableOn
theorem cubeIntegral_smul {p : ℕ+} (P : ℝ) (c : ℂ) (G : Coords p → ℂ)
    (k : IntCoords p) :
    cubeIntegral P k (c • G) = c * cubeIntegral P k G := by
  simp only [cubeIntegral, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _
theorem fourierCoeff_isComplexLinearForm (D : Params) (p : ℕ+) (P : ℝ)
    (hmetric : TupleFacts.DistIsMetric D Kind.euclidean p)
    (hopen : TupleFacts.ProjOpenMap D Kind.euclidean p)
    (k : IntCoords p) :
    Kind.Tuple.IsComplexLinearForm
      (fun F : cellTestFns D p P => fourierCoeff D P F.1 k) := by
  refine ⟨fun F G H hH => ?_, fun c F H hH => ?_⟩
  · have e : H.1 ∘ unfoldMap D p = F.1 ∘ unfoldMap D p + G.1 ∘ unfoldMap D p := by
      rw [hH]
      rfl
    simp only [fourierCoeff_eq]
    change _ * cubeIntegral P k (H.1 ∘ unfoldMap D p) =
      _ * cubeIntegral P k (F.1 ∘ unfoldMap D p) + _ * cubeIntegral P k (G.1 ∘ unfoldMap D p)
    rw [e, cubeIntegral_add (smoothInCube_of_mem D p P hmetric hopen F.2)
      (smoothInCube_of_mem D p P hmetric hopen G.2), mul_add]
  · have e : H.1 ∘ unfoldMap D p = c • (F.1 ∘ unfoldMap D p) := by
      rw [hH]
      rfl
    simp only [fourierCoeff_eq]
    change _ * cubeIntegral P k (H.1 ∘ unfoldMap D p) =
      c * (_ * cubeIntegral P k (F.1 ∘ unfoldMap D p))
    rw [e, cubeIntegral_smul]
    ring
theorem norm_partialDeriv_le_cNorm (D : Params) {p : ℕ+} (F : Kind.euclidean.Tuple D p → ℂ)
    {ν : ℕ} {α : CoordIndex p} (hα : α.degree ≤ ν) (y) :
    ENNReal.ofReal ‖Kind.Tuple.partialDeriv D Kind.euclidean α F y‖ ≤
      Kind.Tuple.cNorm D Kind.euclidean ν F :=
  le_iSup_of_le α (le_iSup_of_le hα (le_iSup_of_le y le_rfl))
theorem partialDeriv_comp (D : Params) (p : ℕ+)
    (hder : TupleFacts.DerivFacts D Kind.euclidean p)
    {P : ℝ} {F : Kind.euclidean.Tuple D p → ℂ} (hF : F ∈ cellTestFns D p P)
    (α : CoordIndex p) :
    Kind.Tuple.partialDeriv D Kind.euclidean α F ∘ unfoldMap D p =
      Coords.iterPartial α (F ∘ unfoldMap D p) :=
  (hder α.degree F (hF.1 _) α le_rfl).2.1
theorem fourierCoeff_partialDeriv (D : Params) (p : ℕ+) (P : ℝ)
    (hmetric : TupleFacts.DistIsMetric D Kind.euclidean p)
    (hopen : TupleFacts.ProjOpenMap D Kind.euclidean p)
    (hder : TupleFacts.DerivFacts D Kind.euclidean p)
    {F : Kind.euclidean.Tuple D p → ℂ} (hF : F ∈ cellTestFns D p P)
    (α : CoordIndex p) (k : IntCoords p) :
    fourierCoeff D P (Kind.Tuple.partialDeriv D Kind.euclidean α F) k =
      fourierMultiplier P k α * fourierCoeff D P F k := by
  rw [fourierCoeff_eq, fourierCoeff_eq]
  change _ * cubeIntegral P k (Kind.Tuple.partialDeriv D Kind.euclidean α F ∘ unfoldMap D p)
    = _ * (_ * cubeIntegral P k (F ∘ unfoldMap D p))
  rw [partialDeriv_comp D p hder hF,
    cubeIntegral_iterPartial (smoothInCube_of_mem D p P hmetric hopen hF)]
  ring
theorem partialDeriv_zero (D : Params) (p : ℕ+)
    (hder : TupleFacts.DerivFacts D Kind.euclidean p)
    {P : ℝ} {F : Kind.euclidean.Tuple D p → ℂ} (hF : F ∈ cellTestFns D p P) :
    Kind.Tuple.partialDeriv D Kind.euclidean (0 : CoordIndex p) F = F := by
  have h := partialDeriv_comp D p hder hF 0
  rw [iterPartial_zero] at h
  funext y
  obtain ⟨x, rfl⟩ := unfoldMap_surjective D p y
  exact congrFun h x
theorem iterPartial_fourierPartialSum (D : Params) (p : ℕ+) (P : ℝ)
    (hmetric : TupleFacts.DistIsMetric D Kind.euclidean p)
    (hopen : TupleFacts.ProjOpenMap D Kind.euclidean p)
    (hder : TupleFacts.DerivFacts D Kind.euclidean p)
    {F : Kind.euclidean.Tuple D p → ℂ} (hF : F ∈ cellTestFns D p P)
    (α : CoordIndex p) (t : ℕ+) :
    Coords.iterPartial α (fourierPartialSum D P F t) =
      fourierPartialSum D P (Kind.Tuple.partialDeriv D Kind.euclidean α F) t := by
  unfold fourierPartialSum
  rw [iterPartial_sum]
  funext u
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fourierCoeff_partialDeriv D p P hmetric hopen hder hF]
  ring
theorem norm_freq {p : ℕ+} {P : ℝ} (hP : 0 < P) (k : IntCoords p)
    (j : Fin (4 * (p : ℕ))) :
    ‖freq P k j‖ = 2 * Real.pi * ((k j).natAbs : ℝ) / P := by
  have h : ‖((k j : ℤ) : ℂ)‖ = ((k j).natAbs : ℝ) := by
    rw [Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
  rw [freq, norm_div, norm_mul, norm_mul, norm_mul, h, Complex.norm_I]
  simp [abs_of_pos hP, abs_of_pos Real.pi_pos]
theorem fourierMultiplier_single {p : ℕ+} (P : ℝ) (k : IntCoords p)
    (j : Fin (4 * (p : ℕ))) (ν : ℕ) :
    fourierMultiplier P k (Pi.single j ν) = freq P k j ^ ν := by
  rw [fourierMultiplier, Finset.prod_eq_single j]
  · simp [freq]
  · intro b _ hb
    simp [hb]
  · simp
theorem fourierCoeff_decay (D : Params) (p : ℕ+) {P : ℝ} (hP : 0 < P)
    (hmetric : TupleFacts.DistIsMetric D Kind.euclidean p)
    (hopen : TupleFacts.ProjOpenMap D Kind.euclidean p)
    (hder : TupleFacts.DerivFacts D Kind.euclidean p)
    {F : Kind.euclidean.Tuple D p → ℂ} (hF : F ∈ cellTestFns D p P)
    {k : IntCoords p} (hk : k ≠ 0) (ν : ℕ) :
    ENNReal.ofReal ‖fourierCoeff D P F k‖ ≤
      ENNReal.ofReal ((P / (2 * Real.pi * (k.maxAbs : ℝ))) ^ ν) *
        Kind.Tuple.cNorm D Kind.euclidean ν F := by
  have : Nonempty (Fin (4 * (p : ℕ))) := ⟨⟨0, by have := p.pos; omega⟩⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun j => (k j).natAbs)
  have hj' : k.maxAbs = (k j).natAbs := hj
  have hs : (0 : ℝ) < (k.maxAbs : ℝ) := by exact_mod_cast one_le_maxAbs hk
  have hord : CoordIndex.degree (Pi.single j ν : CoordIndex p) = ν := by
    simp [CoordIndex.degree]
  have hb := fourierCoeff_norm_le D hP
    (Kind.Tuple.partialDeriv D Kind.euclidean (Pi.single j ν) F)
    (Kind.Tuple.cNorm D Kind.euclidean ν F)
    (fun y => norm_partialDeriv_le_cNorm D F hord.le y) k
  rw [fourierCoeff_partialDeriv D p P hmetric hopen hder hF, fourierMultiplier_single] at hb
  have hc : ‖fourierCoeff D P F k‖ = (P / (2 * Real.pi * (k.maxAbs : ℝ))) ^ ν *
      ‖freq P k j ^ ν * fourierCoeff D P F k‖ := by
    rw [norm_mul, norm_pow, norm_freq hP, ← hj', ← mul_assoc, ← mul_pow]
    have : P / (2 * Real.pi * (k.maxAbs : ℝ)) * (2 * Real.pi * (k.maxAbs : ℝ) / P) = 1 := by
      field_simp
    rw [this, one_pow, one_mul]
  rw [hc, ENNReal.ofReal_mul (by positivity)]
  gcongr
theorem summable_norm_fourierCoeff (D : Params) (p : ℕ+) {P : ℝ} (hP : 0 < P)
    (hmetric : TupleFacts.DistIsMetric D Kind.euclidean p)
    (hopen : TupleFacts.ProjOpenMap D Kind.euclidean p)
    (hder : TupleFacts.DerivFacts D Kind.euclidean p)
    (hfin : TupleFacts.CNormFiniteOfCompactSupport D Kind.euclidean p)
    {F : Kind.euclidean.Tuple D p → ℂ} (hF : F ∈ cellTestFns D p P) :
    Summable fun k' : IntCoords p => ‖fourierCoeff D P F k'‖ := by
  set ν : ℕ := 4 * (p : ℕ) + 1 with hν
  have hN : Kind.Tuple.cNorm D Kind.euclidean ν F ≠ ∞ :=
    (hfin ν F (hF.1 ν) hF.2.1).ne
  set C : ℝ := (Kind.Tuple.cNorm D Kind.euclidean ν F).toReal with hC
  have hbound : ∀ k' : {k' : IntCoords p // k' ≠ 0}, ‖fourierCoeff D P F k'.1‖ ≤
      ((P / (2 * Real.pi)) ^ ν * C) * ((k'.1.maxAbs : ℝ) ^ ν)⁻¹ := by
    intro k'
    have hs : (0 : ℝ) < (k'.1.maxAbs : ℝ) := by exact_mod_cast one_le_maxAbs k'.2
    have h := fourierCoeff_decay D p hP hmetric hopen hder hF k'.2 ν
    have hne : ENNReal.ofReal ((P / (2 * Real.pi * (k'.1.maxAbs : ℝ))) ^ ν) *
        Kind.Tuple.cNorm D Kind.euclidean ν F ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN
    have h2 := (ENNReal.ofReal_le_iff_le_toReal hne).1 h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
    refine h2.trans (le_of_eq ?_)
    rw [← hC, div_mul_eq_div_div, div_pow, div_pow]
    ring
  have hsub : Summable fun k' : {k' : IntCoords p // k' ≠ 0} => ‖fourierCoeff D P F k'.1‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
      ((summable_tsum_inv_maxAbs_pow_le p).1.mul_left _)
  exact (Set.finite_singleton (0 : IntCoords p)).summable_compl_iff.1 hsub
theorem quotDist_euclidean (D : Params) (x y : Fin 4 → ℝ) :
    Kind.quotDist D Kind.euclidean x y = TorusMetric.euclidNormVec (x - y) := by apply _root_.YangMills.Construction.PeriodicSpace.QuotientGeometry.quotDist_euclidean <;> assumption
theorem isOpen_cell (P : ℝ) : IsOpen (cell P) := by
  have : cell P = Set.pi Set.univ fun _ => Set.Ioo (-P / 2) (P / 2) := by
    ext u
    simp [cell]
  rw [this]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
theorem cell_isOpenQ (D : Params) (P : ℝ) : Kind.IsOpenQ D Kind.euclidean (cell P) := by
  intro (x : Fin 4 → ℝ) hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_cell P) x hx
  refine ⟨ε, hε, fun (y : Fin 4 → ℝ) hy => hball ?_⟩
  have hy' : TorusMetric.euclidNormVec (x - y) < ε :=
    lt_of_eq_of_lt (quotDist_euclidean D x y).symm hy
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro μ
  refine lt_of_le_of_lt ?_ hy'
  rw [Real.dist_eq, abs_sub_comm]
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun ν => (x - y) ν ^ 2) (fun ν _ => sq_nonneg _)
    (Finset.mem_univ μ)
def blockEquiv (p : ℕ+) : Coords p ≃ᵐ (Fin (p : ℕ) → Fin 4 → ℝ) where
  toFun u i μ := u (blockIndexEquiv p (i, μ))
  invFun v j := v ((blockIndexEquiv p).symm j).1 ((blockIndexEquiv p).symm j).2
  left_inv u := by
    funext j
    simp
  right_inv v := by
    funext i μ
    simp
  measurable_toFun :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun μ => measurable_pi_apply _
  measurable_invFun := by
    change Measurable fun (v : Fin (p : ℕ) → Fin 4 → ℝ) (j : Fin (4 * (p : ℕ))) =>
      v ((blockIndexEquiv p).symm j).1 ((blockIndexEquiv p).symm j).2
    exact measurable_pi_lambda _ fun j => (measurable_pi_apply _).comp (measurable_pi_apply _)
theorem blockEquiv_apply (p : ℕ+) (u : Coords p) (i : Fin (p : ℕ)) :
    blockEquiv p u i = u.block i :=
  rfl
theorem measurePreserving_blockEquiv (p : ℕ+) :
    MeasurePreserving (blockEquiv p) volume volume := by
  refine ⟨(blockEquiv p).measurable, ?_⟩
  symm
  refine Measure.pi_eq_generateFrom (μ := fun _ : Fin (p : ℕ) => (volume : Measure (Fin 4 → ℝ)))
    (C := fun _ => Set.pi Set.univ '' Set.pi Set.univ fun _ => {s : Set ℝ | MeasurableSet s})
    (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => Measure.FiniteSpanningSetsIn.pi fun _ => (volume : Measure ℝ).toFiniteSpanningSetsIn)
    ?_
  intro s hs
  choose t ht hst using hs
  have ht' : ∀ i μ, MeasurableSet (t i μ) := fun i μ => ht i μ (Set.mem_univ μ)
  have hmeas : MeasurableSet (Set.pi Set.univ s) := by
    refine MeasurableSet.univ_pi fun i => ?_
    rw [← hst i]
    exact MeasurableSet.univ_pi (ht' i)
  rw [Measure.map_apply (blockEquiv p).measurable hmeas]
  have hpre : (blockEquiv p) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun j : Fin (4 * (p : ℕ)) =>
        t ((blockIndexEquiv p).symm j).1 ((blockIndexEquiv p).symm j).2 := by
    ext u
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h j
      have h1 := h ((blockIndexEquiv p).symm j).1
      rw [← hst] at h1
      have h2 := h1 ((blockIndexEquiv p).symm j).2 (Set.mem_univ _)
      have h3 : blockEquiv p u ((blockIndexEquiv p).symm j).1 ((blockIndexEquiv p).symm j).2 =
          u j := by
        change u (blockIndexEquiv p (((blockIndexEquiv p).symm j).1,
          ((blockIndexEquiv p).symm j).2)) = u j
        simp
      rwa [h3] at h2
    · intro h i
      rw [← hst]
      intro μ _
      have h1 := h (blockIndexEquiv p (i, μ))
      simp only [Equiv.symm_apply_apply] at h1
      exact h1
  rw [hpre, volume_pi, Measure.pi_pi]
  rw [← Equiv.prod_comp (blockIndexEquiv p), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hst i, volume_pi, Measure.pi_pi]
  refine Finset.prod_congr rfl fun μ _ => ?_
  simp
theorem integral_prod_blocks (p : ℕ+) (g : Fin (p : ℕ) → (Fin 4 → ℝ) → ℂ) :
    ∫ u : Coords p, ∏ i, g i (u.block i) = ∏ i, ∫ x, g i x := by
  have h := (measurePreserving_blockEquiv p).integral_comp' (fun v => ∏ i, g i (v i))
  simp only [blockEquiv_apply] at h
  rw [h]
  exact integral_fintype_prod_volume_eq_prod g
theorem pairing_eq_sum_blocks {p : ℕ+} (k : IntCoords p) (u : Coords p) :
    k.pairing u = ∑ i, IntCoords.pairing (p := 1) (k.block i) (u.block i) := by
  rw [IntCoords.pairing, ← Equiv.sum_comp (blockIndexEquiv p), Fintype.sum_prod_type]
  rfl
theorem fourierChar_eq_prod_blocks {p : ℕ+} (P : ℝ) (k : IntCoords p) (u : Coords p) :
    fourierChar P k u = ∏ i, fourierCharR4 P (k.block i) (u.block i) := by
  simp only [fourierCharR4, fourierChar]
  rw [← Complex.exp_sum, pairing_eq_sum_blocks]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_div]
theorem block_of_one (u : Coords 1) (i : Fin ((1 : ℕ+) : ℕ)) : u.block i = u := by
  have hi : (i : ℕ) = 0 := by
    have := i.2
    simp only [PNat.one_coe] at this
    omega
  funext μ
  simp only [Coords.block]
  congr 1
  ext
  simp [hi]
theorem fourierCoeff_ofSingle (D : Params) (P : ℝ) (φ : Kind.euclidean.Pt D → ℂ)
    (κ : Fin 4 → ℤ) :
    fourierCoeff (p := 1) D P (Kind.Tuple.ofSingle D Kind.euclidean φ) κ =
      ((P : ℂ) ^ 4)⁻¹ * ∫ x in cell P, φ x * conj (fourierCharR4 P κ x) := by
  unfold fourierCoeff
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [Kind.Tuple.ofSingle]
  have : Kind.Tuple.proj D Kind.euclidean u ⟨0, (1 : ℕ+).pos⟩ = u :=
    block_of_one u _
  rw [this]
  rfl
theorem fourierCoeff_tensorProd (D : Params) (p : ℕ+) (P : ℝ)
    (h : Fin (p : ℕ) → Kind.euclidean.Pt D → ℂ) (k : IntCoords p) :
    fourierCoeff D P (Kind.Tuple.tensorProd D Kind.euclidean h) k =
      ∏ i, fourierCoeff (p := 1) D P
        (Kind.Tuple.ofSingle D Kind.euclidean (h i)) (k.block i) := by
  classical
  set g : Fin (p : ℕ) → (Fin 4 → ℝ) → ℂ := fun i =>
    (cell P).indicator fun x => h i x * conj (fourierCharR4 P (k.block i) x) with hg
  have hind : ∀ u : Coords p, (coordCube p P).indicator (fun u =>
      Kind.Tuple.tensorProd D Kind.euclidean h
        (Kind.Tuple.proj D Kind.euclidean u) * conj (fourierChar P k u)) u =
      ∏ i, g i (u.block i) := by
    intro u
    by_cases hu : u ∈ coordCube p P
    · have hb : ∀ i, u.block i ∈ cell P := fun i μ => hu _
      rw [Set.indicator_of_mem hu]
      simp only [hg, Set.indicator_of_mem (hb _)]
      rw [Finset.prod_mul_distrib, fourierChar_eq_prod_blocks, map_prod]
      rfl
    · rw [Set.indicator_of_notMem hu]
      have : ∃ j, u j ∉ Set.Ioo (-P / 2) (P / 2) := by
        by_contra hc
        exact hu fun j => by_contra fun hj => hc ⟨j, hj⟩
      obtain ⟨j, hj⟩ := this
      obtain ⟨⟨i, μ⟩, rfl⟩ := (blockIndexEquiv p).surjective j
      have hi : u.block i ∉ cell P := fun hb => hj (hb μ)
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp only [hg]
      exact Set.indicator_of_notMem hi _
  have hint : ∫ u in coordCube p P, Kind.Tuple.tensorProd D Kind.euclidean h
      (Kind.Tuple.proj D Kind.euclidean u) * conj (fourierChar P k u) =
      ∏ i, ∫ x in cell P, h i x * conj (fourierCharR4 P (k.block i) x) := by
    rw [← integral_indicator (measurableSet_coordCube p P)]
    simp only [hind]
    rw [integral_prod_blocks]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hg]
    exact integral_indicator ((isOpen_cell P).measurableSet)
  rw [fourierCoeff, hint]
  simp only [fourierCoeff_ofSingle]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow,
    ← pow_mul]
theorem fourierCoeffBounds_holds (hpoints : TupleFacts.AllFacts) :
    FourierCoeffBounds := by
  intro D p P hP
  obtain ⟨-, -, hmetric, -, -, -, -, hopen, -, -, -, -, -, -, hder, hfin, -, -, -, -, -, -,
    htensor, -⟩ := hpoints D Kind.euclidean p
  refine ⟨fourierCoeff_isComplexLinearForm D p P hmetric hopen, ?_, ?_, ?_, ?_, ?_,
    encard_maxAbs_eq_le, summable_tsum_inv_sq_pnat_le, summable_tsum_inv_maxAbs_pow_le p, ?_, ?_⟩
  · intro F hF k
    refine fourierCoeff_norm_le D hP F _ (fun y => ?_) k
    have h := norm_partialDeriv_le_cNorm D F (ν := 0) (α := 0) (by simp [CoordIndex.degree]) y
    rwa [partialDeriv_zero D p hder hF] at h
  · exact fun α k => iterPartial_fourierChar P α k
  · exact fun F hF α k => fourierCoeff_partialDeriv D p P hmetric hopen hder hF α k
  · exact fun F hF α t => iterPartial_fourierPartialSum D p P hmetric hopen hder hF α t
  · exact fun F hF k hk ν => fourierCoeff_decay D p hP hmetric hopen hder hF hk ν
  · exact fun F hF => summable_norm_fourierCoeff D p hP hmetric hopen hder hfin hF
  · intro h hh
    exact ⟨htensor (fun _ => cell P) h (fun _ => cell_isOpenQ D P) hh,
      fourierCoeff_tensorProd D p P h⟩
end YangMills.Construction.PeriodicSpace.PeriodCell.Fourier
