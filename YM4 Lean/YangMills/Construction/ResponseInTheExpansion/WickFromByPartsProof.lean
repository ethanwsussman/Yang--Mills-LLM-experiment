import YangMills.Construction.ResponseInTheExpansion.WickFromByParts
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.Wick
section PerfectMatchings
variable {q : ℕ}
structure PerfectMatching (s : Finset (Fin q)) (P : Finset (Finset (Fin q))) : Prop where
  card_eq_two : ∀ B ∈ P, B.card = 2
  disjoint_of_ne : ∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → Disjoint B B'
  mem_iff : ∀ x, x ∈ s ↔ ∃ B ∈ P, x ∈ B
def matchingWeight (G : Fin q → Fin q → ℝ) (P : Finset (Finset (Fin q))) : ℝ :=
  ∏ B ∈ P, (if h : B.Nonempty then G (B.min' h) (B.max' h) else 1)
open Classical in
def perfectMatchings (s : Finset (Fin q)) : Finset (Finset (Finset (Fin q))) :=
  (Finset.univ : Finset (Finset (Finset (Fin q)))).filter (PerfectMatching s)
theorem mem_perfectMatchings {s : Finset (Fin q)} {P : Finset (Finset (Fin q))} :
    P ∈ perfectMatchings s ↔ PerfectMatching s P := by
  classical
  simp [perfectMatchings]
def PerfectMatching.toFinpartition {s : Finset (Fin q)} {P : Finset (Finset (Fin q))}
    (h : PerfectMatching s P) : Finpartition s where
  parts := P
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro B hB B' hB' hne
    exact h.disjoint_of_ne B hB B' hB' hne
  sup_parts := by
    ext x
    rw [h.mem_iff x, Finset.mem_sup]
    simp
  bot_notMem := by
    intro hb
    have := h.card_eq_two _ hb
    simp at this
theorem perfectMatching_of_finpartition {s : Finset (Fin q)} (π : Finpartition s)
    (h : ∀ B ∈ π.parts, B.card = 2) : PerfectMatching s π.parts where
  card_eq_two := h
  disjoint_of_ne := fun B hB B' hB' hne => π.disjoint hB hB' hne
  mem_iff := fun x => by
    constructor
    · intro hx
      rw [← π.sup_parts, Finset.mem_sup] at hx
      simpa using hx
    · rintro ⟨B, hB, hx⟩
      exact π.le hB hx
theorem pairingSum_eq_sum_perfectMatchings (G : Fin q → Fin q → ℝ) (s : Finset (Fin q)) :
    pairingSum G s = ∑ P ∈ perfectMatchings s, matchingWeight G P := by
  classical
  unfold pairingSum
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun π _ => π.parts) ?_ ?_ ?_ ?_
  · intro π hπ
    rw [mem_perfectMatchings]
    exact perfectMatching_of_finpartition π (Finset.mem_filter.1 hπ).2
  · intro π _ π' _ h
    exact Finpartition.ext h
  · intro P hP
    have hm := mem_perfectMatchings.1 hP
    exact ⟨hm.toFinpartition, Finset.mem_filter.2 ⟨Finset.mem_univ _, hm.card_eq_two⟩, rfl⟩
  · intro π _
    rfl
theorem perfectMatchings_empty : perfectMatchings (∅ : Finset (Fin q)) = {∅} := by
  ext P
  rw [mem_perfectMatchings, Finset.mem_singleton]
  constructor
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro B hB
    have hc := h.card_eq_two B hB
    obtain ⟨x, hx⟩ : B.Nonempty := by
      rw [← Finset.card_pos]
      omega
    have := (h.mem_iff x).2 ⟨B, hB, hx⟩
    simp at this
  · rintro rfl
    exact ⟨by simp, by simp, by simp⟩
theorem pairingSum_empty (G : Fin q → Fin q → ℝ) : pairingSum G ∅ = 1 := by
  rw [pairingSum_eq_sum_perfectMatchings, perfectMatchings_empty]
  simp [matchingWeight]
variable {s : Finset (Fin q)} {a : Fin q}
theorem perfectMatching_insert_pair {i : Fin q} (ha : a ∉ s) (hi : i ∈ s)
    {P : Finset (Finset (Fin q))} (hP : PerfectMatching (s.erase i) P) :
    PerfectMatching (insert a s) (insert {i, a} P) := by
  have hia : i ≠ a := fun h => ha (h ▸ hi)
  have hdis : ∀ B ∈ P, Disjoint ({i, a} : Finset (Fin q)) B := by
    intro B hB
    rw [Finset.disjoint_left]
    intro x hx hxB
    have hxs := (hP.mem_iff x).2 ⟨B, hB, hxB⟩
    rw [Finset.mem_erase] at hxs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hxs.1 rfl
    · exact ha hxs.2
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    rcases Finset.mem_insert.1 hB with rfl | hB
    · exact Finset.card_pair hia
    · exact hP.card_eq_two B hB
  · intro B hB B' hB' hne
    rcases Finset.mem_insert.1 hB with rfl | hB
    · rcases Finset.mem_insert.1 hB' with rfl | hB'
      · exact absurd rfl hne
      · exact hdis B' hB'
    · rcases Finset.mem_insert.1 hB' with rfl | hB'
      · exact (hdis B hB).symm
      · exact hP.disjoint_of_ne B hB B' hB' hne
  · intro x
    constructor
    · intro hx
      by_cases hxi : x = i
      · exact ⟨{i, a}, Finset.mem_insert_self _ _, by simp [hxi]⟩
      · by_cases hxa : x = a
        · exact ⟨{i, a}, Finset.mem_insert_self _ _, by simp [hxa]⟩
        · have hxs : x ∈ s := by
            rcases Finset.mem_insert.1 hx with h | h
            · exact absurd h hxa
            · exact h
          obtain ⟨B, hB, hxB⟩ := (hP.mem_iff x).1 (Finset.mem_erase.2 ⟨hxi, hxs⟩)
          exact ⟨B, Finset.mem_insert_of_mem hB, hxB⟩
    · rintro ⟨B, hB, hxB⟩
      rcases Finset.mem_insert.1 hB with rfl | hB
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hxB
        rcases hxB with rfl | rfl
        · exact Finset.mem_insert_of_mem hi
        · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_of_mem_erase ((hP.mem_iff x).2 ⟨B, hB, hxB⟩))
theorem exists_perfectMatching_split (ha : a ∉ s) {P : Finset (Finset (Fin q))}
    (hP : PerfectMatching (insert a s) P) :
    ∃ i ∈ s, ∃ P' ∈ perfectMatchings (s.erase i), insert {i, a} P' = P := by
  obtain ⟨B, hB, haB⟩ := (hP.mem_iff a).1 (Finset.mem_insert_self _ _)
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.1 (hP.card_eq_two B hB)
  obtain ⟨i, hia, hset⟩ : ∃ i, i ≠ a ∧ ({u, v} : Finset (Fin q)) = {i, a} := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at haB
    rcases haB with rfl | rfl
    · exact ⟨v, huv.symm, Finset.pair_comm _ _⟩
    · exact ⟨u, huv, rfl⟩
  rw [hset] at hB
  have his : i ∈ s := by
    have : i ∈ insert a s := (hP.mem_iff i).2 ⟨{i, a}, hB, by simp⟩
    rcases Finset.mem_insert.1 this with h | h
    · exact absurd h hia
    · exact h
  have hout : ∀ B' ∈ P, B' ≠ {i, a} → ∀ x ∈ B', x ≠ i ∧ x ≠ a := by
    intro B' hB' hne x hx
    have hd := hP.disjoint_of_ne _ hB' _ hB hne
    rw [Finset.disjoint_left] at hd
    have := hd hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
    exact this
  refine ⟨i, his, P.erase {i, a}, ?_, Finset.insert_erase hB⟩
  rw [mem_perfectMatchings]
  refine ⟨fun B' hB' => hP.card_eq_two B' (Finset.mem_of_mem_erase hB'), ?_, ?_⟩
  · intro B₁ h₁ B₂ h₂ hne
    exact hP.disjoint_of_ne B₁ (Finset.mem_of_mem_erase h₁) B₂ (Finset.mem_of_mem_erase h₂) hne
  · intro x
    constructor
    · intro hx
      rw [Finset.mem_erase] at hx
      obtain ⟨B', hB', hxB⟩ := (hP.mem_iff x).1 (Finset.mem_insert_of_mem hx.2)
      refine ⟨B', Finset.mem_erase.2 ⟨?_, hB'⟩, hxB⟩
      rintro rfl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxB
      rcases hxB with rfl | rfl
      · exact hx.1 rfl
      · exact ha hx.2
    · rintro ⟨B', hB', hxB⟩
      rw [Finset.mem_erase] at hB'
      obtain ⟨h1, h2⟩ := hout B' hB'.2 hB'.1 x hxB
      have := (hP.mem_iff x).2 ⟨B', hB'.2, hxB⟩
      rcases Finset.mem_insert.1 this with h | h
      · exact absurd h h2
      · exact Finset.mem_erase.2 ⟨h1, h⟩
theorem pair_notMem_of_perfectMatching {i : Fin q} (ha : a ∉ s) (hi : i ∈ s)
    {P : Finset (Finset (Fin q))} (hP : PerfectMatching (s.erase i) P) :
    ({i, a} : Finset (Fin q)) ∉ P := by
  intro h
  have := (hP.mem_iff a).2 ⟨_, h, by simp⟩
  exact ha (Finset.mem_of_mem_erase this)
theorem matchingWeight_insert_pair {i : Fin q} (G : Fin q → Fin q → ℝ) (hlt : i < a)
    {P : Finset (Finset (Fin q))} (hn : ({i, a} : Finset (Fin q)) ∉ P) :
    matchingWeight G (insert {i, a} P) = G i a * matchingWeight G P := by
  unfold matchingWeight
  rw [Finset.prod_insert hn]
  congr 1
  have hne : ({i, a} : Finset (Fin q)).Nonempty := ⟨i, by simp⟩
  rw [dif_pos hne]
  have h1 : ({i, a} : Finset (Fin q)).min' hne = i := by
    apply le_antisymm (Finset.min'_le _ _ (by simp))
    apply Finset.le_min'
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact le_rfl
    · exact hlt.le
  have h2 : ({i, a} : Finset (Fin q)).max' hne = a := by
    apply le_antisymm _ (Finset.le_max' _ _ (by simp))
    apply Finset.max'_le
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hlt.le
    · exact le_rfl
  rw [h1, h2]
theorem pairingSum_insert_max (G : Fin q → Fin q → ℝ) (ha : a ∉ s) (hlt : ∀ i ∈ s, i < a) :
    pairingSum G (insert a s) = ∑ i ∈ s, G i a * pairingSum G (s.erase i) := by
  classical
  have hU : perfectMatchings (insert a s) =
      s.biUnion fun i => (perfectMatchings (s.erase i)).image (insert {i, a}) := by
    ext P
    rw [Finset.mem_biUnion]
    constructor
    · intro hP
      obtain ⟨i, hi, P', hP', rfl⟩ := exists_perfectMatching_split ha (mem_perfectMatchings.1 hP)
      exact ⟨i, hi, Finset.mem_image_of_mem _ hP'⟩
    · rintro ⟨i, hi, hP⟩
      obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 hP
      exact mem_perfectMatchings.2 (perfectMatching_insert_pair ha hi (mem_perfectMatchings.1 hP'))
  rw [pairingSum_eq_sum_perfectMatchings, hU, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [pairingSum_eq_sum_perfectMatchings, Finset.mul_sum, Finset.sum_image]
    · refine Finset.sum_congr rfl fun P hP => ?_
      exact matchingWeight_insert_pair G (hlt i hi)
        (pair_notMem_of_perfectMatching ha hi (mem_perfectMatchings.1 hP))
    · intro P hP P' hP' h
      have e := congrArg (fun Q => Finset.erase Q ({i, a} : Finset (Fin q))) h
      simpa [Finset.erase_insert (pair_notMem_of_perfectMatching ha hi (mem_perfectMatchings.1 hP)),
        Finset.erase_insert (pair_notMem_of_perfectMatching ha hi (mem_perfectMatchings.1 hP'))] using e
  · intro i hi j hj hij
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨P₁, h₁, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨P₂, h₂, e⟩ := Finset.mem_image.1 hP'
    have hmem : ({i, a} : Finset (Fin q)) ∈ insert ({j, a} : Finset (Fin q)) P₂ := by
      rw [e]
      exact Finset.mem_insert_self _ _
    have hnot : ({i, a} : Finset (Fin q)) ∉ P₂ := by
      intro h
      have := ((mem_perfectMatchings.1 h₂).mem_iff a).2 ⟨_, h, by simp⟩
      exact ha (Finset.mem_of_mem_erase this)
    rcases Finset.mem_insert.1 hmem with h | h
    · have hia : i ≠ a := (hlt i hi).ne
      have : i ∈ ({j, a} : Finset (Fin q)) := by
        rw [← h]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h'
      · exact hij h'
      · exact hia h'
    · exact hnot h
end PerfectMatchings
section MomentBounds
theorem abs_prod_le_one_add_sum_pow {ι : Type} (s : Finset ι) (z : ι → ℝ) (m : ℕ)
    (hm : s.card ≤ 2 * m) :
    |∏ i ∈ s, z i| ≤ 1 + ∑ i ∈ s, z i ^ (2 * m) := by
  classical
  rw [Finset.abs_prod]
  have hnn : ∀ i, 0 ≤ z i ^ (2 * m) := fun i => Even.pow_nonneg (even_two_mul m) _
  have hsum : 0 ≤ ∑ i ∈ s, z i ^ (2 * m) := Finset.sum_nonneg fun i _ => hnn i
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image s (fun i => |z i|) hne
  have h1 : ∏ i ∈ s, |z i| ≤ |z i₀| ^ s.card := by
    calc ∏ i ∈ s, |z i| ≤ ∏ _i ∈ s, |z i₀| :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) hmax
      _ = _ := by simp
  rcases le_or_gt |z i₀| 1 with hle | hgt
  · have : |z i₀| ^ s.card ≤ 1 := pow_le_one₀ (abs_nonneg _) hle
    linarith
  · have h2 : |z i₀| ^ s.card ≤ |z i₀| ^ (2 * m) := pow_le_pow_right₀ hgt.le hm
    have h3 : |z i₀| ^ (2 * m) = z i₀ ^ (2 * m) := by
      rw [pow_mul, pow_mul, sq_abs]
    have h4 : z i₀ ^ (2 * m) ≤ ∑ i ∈ s, z i ^ (2 * m) :=
      Finset.single_le_sum (f := fun i => z i ^ (2 * m)) (fun i _ => hnn i) hi₀
    linarith
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem abs_integral_prod_le {ι : Type} (s : Finset ι) (Z : ι → Ω → ℝ) (m : ℕ)
    (hm : s.card ≤ 2 * m) (D : ℝ)
    (hint : ∀ i ∈ s, Integrable (fun ω => Z i ω ^ (2 * m)) μ)
    (hD : ∀ i ∈ s, ∫ ω, Z i ω ^ (2 * m) ∂μ ≤ D) :
    |∫ ω, ∏ i ∈ s, Z i ω ∂μ| ≤ 1 + s.card * D := by
  have hg : Integrable (fun ω => 1 + ∑ i ∈ s, Z i ω ^ (2 * m)) μ :=
    (integrable_const 1).add (integrable_finsetSum s hint)
  have hb := norm_integral_le_of_norm_le (f := fun ω => ∏ i ∈ s, Z i ω) hg
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_prod_le_one_add_sum_pow s (fun i => Z i ω) m hm)
  rw [Real.norm_eq_abs] at hb
  refine hb.trans ?_
  rw [integral_add (integrable_const 1) (integrable_finsetSum s hint),
    integral_finsetSum s hint]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  have : ∑ i ∈ s, ∫ ω, Z i ω ^ (2 * m) ∂μ ≤ ∑ _i ∈ s, D := Finset.sum_le_sum hD
  simpa using this
variable {q : ℕ} {ξ R : Fin q → Ω → ℝ} {G : Fin q → Fin q → ℝ} {y : ℝ} {Λ : Fin q → ℝ}
  {A : ℕ → ℝ} {B : ℝ}
theorem abs_integral_prod_mul_remainder_le (hy : 0 < y) (hΛ : ∀ i, 0 < Λ i)
    (h : GaussianByParts μ ξ R G y Λ A B)
    (s : Finset (Fin q)) (a : Fin q) (ha : a ∉ s) :
    |∫ ω, (∏ i ∈ s, ξ i ω) * R a ω ∂μ| ≤
      (1 + ((s.card : ℝ) + 1) * |A (s.card + 1)|) * y ^ s.card * ∏ i ∈ insert a s, Λ i := by
  classical
  set m := s.card + 1 with hm
  set Z : Fin q → Ω → ℝ := fun i ω => if i = a then R a ω / Λ a else ξ i ω / (Λ i * y) with hZ
  have hcard : (insert a s).card = m := Finset.card_insert_of_notMem ha
  have hpow : ∀ i, i ≠ a → (fun ω => Z i ω ^ (2 * m)) =
      fun ω => ((Λ i * y) ^ (2 * m))⁻¹ * ξ i ω ^ (2 * m) := by
    intro i hi
    funext ω
    simp only [hZ, if_neg hi, div_pow]
    rw [div_eq_inv_mul]
  have hpowa : (fun ω => Z a ω ^ (2 * m)) = fun ω => (Λ a ^ (2 * m))⁻¹ * R a ω ^ (2 * m) := by
    funext ω
    simp only [hZ, if_true, div_pow]
    rw [div_eq_inv_mul]
  have hint : ∀ i ∈ insert a s, Integrable (fun ω => Z i ω ^ (2 * m)) μ := by
    intro i _
    by_cases hi : i = a
    · subst hi
      rw [hpowa]
      exact (h.integrable_pow_remainder i m).const_mul _
    · rw [hpow i hi]
      exact (h.integrable_pow_field i m).const_mul _
  have hD : ∀ i ∈ insert a s, ∫ ω, Z i ω ^ (2 * m) ∂μ ≤ |A m| := by
    intro i _
    by_cases hi : i = a
    · subst hi
      rw [hpowa, integral_const_mul]
      have hp : 0 < Λ i ^ (2 * m) := pow_pos (hΛ i) _
      rw [inv_mul_le_iff₀ hp]
      calc ∫ ω, R i ω ^ (2 * m) ∂μ ≤ A m * Λ i ^ (2 * m) := h.moment_remainder_le i m
        _ ≤ |A m| * Λ i ^ (2 * m) := mul_le_mul_of_nonneg_right (le_abs_self _) hp.le
        _ = _ := mul_comm _ _
    · rw [hpow i hi, integral_const_mul]
      have hp : 0 < (Λ i * y) ^ (2 * m) := pow_pos (mul_pos (hΛ i) hy) _
      rw [inv_mul_le_iff₀ hp]
      calc ∫ ω, ξ i ω ^ (2 * m) ∂μ ≤ A m * (Λ i * y) ^ (2 * m) := h.moment_field_le i m
        _ ≤ |A m| * (Λ i * y) ^ (2 * m) := mul_le_mul_of_nonneg_right (le_abs_self _) hp.le
        _ = _ := mul_comm _ _
  have hb := abs_integral_prod_le (μ := μ) (insert a s) Z m (by omega) |A m| hint hD
  rw [hcard] at hb
  set c : ℝ := (∏ i ∈ s, (Λ i * y)) * Λ a with hc
  have hc0 : 0 < c := mul_pos (Finset.prod_pos fun i _ => mul_pos (hΛ i) hy) (hΛ a)
  have hfac : ∀ ω, (∏ i ∈ s, ξ i ω) * R a ω = c * ∏ i ∈ insert a s, Z i ω := by
    intro ω
    rw [Finset.prod_insert ha]
    have e1 : Z a ω = R a ω / Λ a := by simp [hZ]
    have e2 : ∏ i ∈ s, Z i ω = (∏ i ∈ s, ξ i ω) / ∏ i ∈ s, (Λ i * y) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      have : i ≠ a := fun e => ha (e ▸ hi)
      simp [hZ, this]
    rw [e1, e2, hc]
    have h1 : Λ a ≠ 0 := (hΛ a).ne'
    have h2 : ∏ i ∈ s, (Λ i * y) ≠ 0 := (Finset.prod_pos fun i _ => mul_pos (hΛ i) hy).ne'
    generalize (∏ i ∈ s, (Λ i * y)) = Y at h2
    generalize (∏ i ∈ s, ξ i ω) = X
    field_simp
  simp only [hfac]
  rw [integral_const_mul, abs_mul, abs_of_pos hc0]
  have hcv : c = y ^ s.card * ∏ i ∈ insert a s, Λ i := by
    rw [hc, Finset.prod_insert ha, Finset.prod_mul_distrib, Finset.prod_const]
    ring
  have hcast : ((m : ℕ) : ℝ) = (s.card : ℝ) + 1 := by
    rw [hm]
    push_cast
    ring
  rw [hcast] at hb
  calc c * |∫ ω, ∏ i ∈ insert a s, Z i ω ∂μ|
      ≤ c * (1 + ((s.card : ℝ) + 1) * |A m|) := mul_le_mul_of_nonneg_left hb hc0.le
    _ = _ := by rw [hcv]; ring
end MomentBounds
def wickConstant (K : ℕ → ℝ) (b : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => n * b * wickConstant K b (n - 1) + K n
decreasing_by omega
theorem wickConstant_nonneg {K : ℕ → ℝ} {b : ℝ} (hK : ∀ n, 0 ≤ K n) (hb : 0 ≤ b) (n : ℕ) :
    0 ≤ wickConstant K b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [wickConstant]
    | succ n =>
      rw [wickConstant]
      have := ih (n - 1) (by omega)
      have h2 := hK n
      positivity
section Expansion
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {q : ℕ} {ξ R : Fin q → Ω → ℝ} {G : Fin q → Fin q → ℝ} {y : ℝ} {Λ : Fin q → ℝ}
  {A : ℕ → ℝ} {B : ℝ}
theorem abs_integral_prod_sub_pairingSum_le (hy : 0 < y) (hΛ : ∀ i, 0 < Λ i)
    (h : GaussianByParts μ ξ R G y Λ A B) (n : ℕ) :
    ∀ s : Finset (Fin q), s.card = n →
      |(∫ ω, ∏ i ∈ s, ξ i ω ∂μ) - y ^ s.card * pairingSum G s| ≤
        wickConstant (fun n => 1 + ((n : ℝ) + 1) * |A (n + 1)|) |B| s.card * y ^ (s.card + 1) *
          ∏ i ∈ s, Λ i := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp [pairingSum_empty, wickConstant]
    set a := s.max' hne with ha
    set s' := s.erase a with hs'
    have has : a ∈ s := Finset.max'_mem _ _
    have hnot : a ∉ s' := Finset.notMem_erase _ _
    have hins : insert a s' = s := Finset.insert_erase has
    have hlt : ∀ i ∈ s', i < a := fun i hi => Finset.lt_max'_of_mem_erase_max' s hne hi
    set n' := s'.card with hn'
    have hcard : s.card = n' + 1 := by
      rw [← hins, Finset.card_insert_of_notMem hnot]
    set K : ℕ → ℝ := fun n => 1 + ((n : ℝ) + 1) * |A (n + 1)| with hK
    set C := wickConstant K |B| with hC
    set P : ℝ := ∏ i ∈ s, Λ i with hP
    have hparts := h.integration_by_parts s' a hnot hlt
    have he1 : ∫ ω, ∏ i ∈ s, ξ i ω ∂μ = ∫ ω, (∏ i ∈ s', ξ i ω) * ξ a ω ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      change ∏ i ∈ s, ξ i ω = _
      rw [← hins, Finset.prod_insert hnot, mul_comm]
    have hps : pairingSum G s = ∑ i ∈ s', G i a * pairingSum G (s'.erase i) := by
      rw [← hins]
      exact pairingSum_insert_max G hnot hlt
    set J := ∫ ω, (∏ i ∈ s', ξ i ω) * R a ω ∂μ with hJ
    have hJb : |J| ≤ K n' * y ^ n' * P := by
      have := abs_integral_prod_mul_remainder_le hy hΛ h s' a hnot
      rw [hins] at this
      exact this
    have hterm : ∀ i ∈ s', |G i a * ((∫ ω, ∏ j ∈ s'.erase i, ξ j ω ∂μ) -
        y ^ (n' - 1) * pairingSum G (s'.erase i))| ≤ |B| * C (n' - 1) * y ^ n' * P := by
      intro i hi
      have hc1 : (s'.erase i).card = n' - 1 := Finset.card_erase_of_mem hi
      have hn1 : 1 ≤ n' := Finset.card_pos.2 ⟨i, hi⟩
      have hih := ih (n' - 1) (by omega) (s'.erase i) hc1
      rw [hc1] at hih
      have hG := h.abs_covariance_le i a
      have hprod : Λ i * Λ a * ∏ j ∈ s'.erase i, Λ j = P := by
        have e1 : Λ i * ∏ j ∈ s'.erase i, Λ j = ∏ j ∈ s', Λ j := Finset.mul_prod_erase _ _ hi
        have e2 : Λ a * ∏ j ∈ s', Λ j = P := by
          rw [hP, ← hins, Finset.prod_insert hnot]
        calc Λ i * Λ a * ∏ j ∈ s'.erase i, Λ j = Λ a * (Λ i * ∏ j ∈ s'.erase i, Λ j) := by ring
          _ = P := by rw [e1, e2]
      have hy1 : y ^ (n' - 1 + 1) = y ^ n' := by
        congr 1
        omega
      rw [hy1] at hih
      have hΛΛ : 0 < Λ i * Λ a := mul_pos (hΛ i) (hΛ a)
      have hG' : |G i a| ≤ |B| * (Λ i * Λ a) := by
        have : B * Λ i * Λ a ≤ |B| * (Λ i * Λ a) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_abs_self _) hΛΛ.le
        exact hG.trans this
      rw [abs_mul]
      calc |G i a| * |(∫ ω, ∏ j ∈ s'.erase i, ξ j ω ∂μ) - y ^ (n' - 1) * pairingSum G (s'.erase i)|
          ≤ (|B| * (Λ i * Λ a)) * (C (n' - 1) * y ^ n' * ∏ j ∈ s'.erase i, Λ j) :=
            mul_le_mul hG' hih (abs_nonneg _) (by positivity)
        _ = |B| * C (n' - 1) * y ^ n' * (Λ i * Λ a * ∏ j ∈ s'.erase i, Λ j) := by ring
        _ = _ := by rw [hprod]
    have hdiff : (∫ ω, ∏ i ∈ s, ξ i ω ∂μ) - y ^ s.card * pairingSum G s =
        y ^ 2 * ∑ i ∈ s', G i a * ((∫ ω, ∏ j ∈ s'.erase i, ξ j ω ∂μ) -
          y ^ (n' - 1) * pairingSum G (s'.erase i)) - y ^ 2 * J := by
      rw [he1, hparts, hps, hcard, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      have : ∀ i ∈ s', y ^ 2 * (G i a * ((∫ ω, ∏ j ∈ s'.erase i, ξ j ω ∂μ) -
          y ^ (n' - 1) * pairingSum G (s'.erase i))) =
          y ^ 2 * (G i a * ∫ ω, ∏ j ∈ s'.erase i, ξ j ω ∂μ) -
            y ^ (n' + 1) * (G i a * pairingSum G (s'.erase i)) := by
        intro i hi
        have hn1 : 1 ≤ n' := Finset.card_pos.2 ⟨i, hi⟩
        have hy2 : y ^ (n' + 1) = y ^ 2 * y ^ (n' - 1) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hy2]
        ring
      rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]
      ring
    rw [hdiff, hcard]
    have hsum : |∑ i ∈ s', G i a * ((∫ ω, ∏ j ∈ s'.erase i, ξ j ω ∂μ) -
        y ^ (n' - 1) * pairingSum G (s'.erase i))| ≤ n' * (|B| * C (n' - 1) * y ^ n' * P) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum hterm).trans ?_
      simp [hn']
    have hy2 : 0 < y ^ 2 := by positivity
    have hCs : C (n' + 1) = n' * |B| * C (n' - 1) + K n' := by
      rw [hC, wickConstant]
    calc |y ^ 2 * ∑ i ∈ s', G i a * ((∫ ω, ∏ j ∈ s'.erase i, ξ j ω ∂μ) -
          y ^ (n' - 1) * pairingSum G (s'.erase i)) - y ^ 2 * J|
        ≤ |y ^ 2 * ∑ i ∈ s', G i a * ((∫ ω, ∏ j ∈ s'.erase i, ξ j ω ∂μ) -
          y ^ (n' - 1) * pairingSum G (s'.erase i))| + |y ^ 2 * J| := abs_sub _ _
      _ = y ^ 2 * |∑ i ∈ s', G i a * ((∫ ω, ∏ j ∈ s'.erase i, ξ j ω ∂μ) -
          y ^ (n' - 1) * pairingSum G (s'.erase i))| + y ^ 2 * |J| := by
          rw [abs_mul, abs_mul, abs_of_pos hy2]
      _ ≤ y ^ 2 * (n' * (|B| * C (n' - 1) * y ^ n' * P)) + y ^ 2 * (K n' * y ^ n' * P) := by
          gcongr
      _ = C (n' + 1) * y ^ (n' + 1 + 1) * P := by
          rw [hCs, pow_succ y (n' + 1), pow_succ y n']
          ring
end Expansion
theorem wickOfIntegrationByParts_holds : WickOfIntegrationByParts := by
  intro A B
  refine ⟨wickConstant (fun n => 1 + ((n : ℝ) + 1) * |A (n + 1)|) |B|,
    wickConstant_nonneg (fun n => by positivity) (abs_nonneg _), ?_⟩
  intro Ω _ μ _ q ξ R G y Λ hy hΛ h s
  exact abs_integral_prod_sub_pairingSum_le hy hΛ h s.card s rfl
end YangMills.Construction.Wick
end
