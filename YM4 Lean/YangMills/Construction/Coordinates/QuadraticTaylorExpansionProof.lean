import YangMills.Construction.Analysis.QuadraticTaylorUniqueness
import YangMills.Construction.Coordinates.QuadraticTaylorExpansion
import Mathlib
set_option autoImplicit false
open Filter Topology Asymptotics
namespace YangMills.Construction.Coordinates.QuadraticTaylor
open YangMills.Construction.Coordinates.ComplexCoordinates
open YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy
variable {l : ℕ}
noncomputable def coordMonomial (m : Fin l → ℕ) (z : ComplexCoordinates l) : ℂ := ∏ j, z j ^ m j
def exponentsOfDegree (l n : ℕ) : Finset (Fin l → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (n + 1)).filter fun m => ∑ j, m j = n
theorem mem_exponentsOfDegree {n : ℕ} {m : Fin l → ℕ} :
    m ∈ exponentsOfDegree l n ↔ ∑ j, m j = n := by
  simp only [exponentsOfDegree, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    and_iff_right_iff_imp]
  intro hs i
  have := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega
theorem exponent_eq_zero_of_sum_eq_zero {m : Fin l → ℕ} (hs : ∑ j, m j = 0) : m = 0 :=
  funext fun i => (Finset.sum_eq_zero_iff.1 hs) i (Finset.mem_univ i)
theorem coordMonomial_zero (z : ComplexCoordinates l) : coordMonomial (0 : Fin l → ℕ) z = 1 := by
  simp [coordMonomial]
theorem coordMonomial_succ_factor {n : ℕ} (m : Fin l → ℕ) (hm : ∑ j, m j = n + 1) :
    ∃ (j : Fin l) (m' : Fin l → ℕ), ∑ i, m' i = n ∧
      ∀ z : ComplexCoordinates l, coordMonomial m z = z j * coordMonomial m' z := by
  have hex : ∃ j, m j ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    simp [hcon] at hm
  obtain ⟨j, hj⟩ := hex
  obtain ⟨m', hm'⟩ : ∃ m' : Fin l → ℕ, m = m' + Pi.single j 1 := by
    refine ⟨Function.update m j (m j - 1), ?_⟩
    ext i
    by_cases hij : i = j
    · subst hij
      simp
      omega
    · simp [hij]
  subst hm'
  refine ⟨j, m', ?_, ?_⟩
  · simpa [Finset.sum_add_distrib] using hm
  · intro z
    have hs : ∏ i, z i ^ (Pi.single j 1 : Fin l → ℕ) i = z j := by
      rw [Finset.prod_eq_single j]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    simp only [coordMonomial, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    rw [hs, mul_comm]
theorem exists_linearMap_eq_coordMonomial (m : Fin l → ℕ) :
    ∃ L : ComplexCoordinates l →ₗ[ℂ] ℂ, ∑ j, m j = 1 → ∀ z, L z = coordMonomial m z := by
  by_cases hm : ∑ j, m j = 1
  · obtain ⟨j, m', h0, hz⟩ := coordMonomial_succ_factor (n := 0) m hm
    obtain rfl := exponent_eq_zero_of_sum_eq_zero h0
    refine ⟨LinearMap.proj j, fun _ z => ?_⟩
    rw [hz, coordMonomial_zero]
    simp
  · exact ⟨0, fun hs => absurd hs hm⟩
theorem exists_symmetric_bilinear_eq_coordMonomial (m : Fin l → ℕ) :
    ∃ B : ComplexCoordinates l →ₗ[ℂ] ComplexCoordinates l →ₗ[ℂ] ℂ,
      (∀ z z', B z z' = B z' z) ∧ (∑ j, m j = 2 → ∀ z, B z z = 2 * coordMonomial m z) := by
  by_cases hm : ∑ j, m j = 2
  · obtain ⟨j, m₁, h1, hz⟩ := coordMonomial_succ_factor (n := 1) m hm
    obtain ⟨k, m₀, h0, hz'⟩ := coordMonomial_succ_factor (n := 0) m₁ h1
    obtain rfl := exponent_eq_zero_of_sum_eq_zero h0
    let P : ComplexCoordinates l →ₗ[ℂ] ℂ := LinearMap.proj j
    let Q : ComplexCoordinates l →ₗ[ℂ] ℂ := LinearMap.proj k
    have hB : ∀ z z', ((LinearMap.mul ℂ ℂ).compl₁₂ P Q + (LinearMap.mul ℂ ℂ).compl₁₂ Q P) z z'
        = z j * z' k + z k * z' j := fun z z' => by
      simp [P, Q, LinearMap.compl₁₂_apply]
    refine ⟨(LinearMap.mul ℂ ℂ).compl₁₂ P Q + (LinearMap.mul ℂ ℂ).compl₁₂ Q P, ?_, ?_⟩
    · intro z z'
      rw [hB, hB]
      ring
    · intro _ z
      rw [hB, hz, hz', coordMonomial_zero]
      ring
  · exact ⟨0, fun _ _ => rfl, fun hs => absurd hs hm⟩
theorem norm_coordMonomial_le (m : Fin l → ℕ) (z : ComplexCoordinates l) :
    ‖coordMonomial m z‖ ≤ ‖z‖ ^ ∑ j, m j := by
  rw [coordMonomial, norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun _ _ => by positivity) fun j _ => ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm z j) _
theorem secondOrderExpansion_unique (hu : YangMills.Construction.Taylor.QuadraticTaylorUniqueness)
    {f : ComplexCoordinates l → ℂ}
    {p q : (ComplexCoordinates l →ₗ[ℂ] ℂ) ×
      (ComplexCoordinates l →ₗ[ℂ] ComplexCoordinates l →ₗ[ℂ] ℂ)}
    (hp : IsSecondOrderExpansion f p.1 p.2) (hq : IsSecondOrderExpansion f q.1 q.2) :
    p = q := by
  obtain ⟨hps, hpO⟩ := hp
  obtain ⟨hqs, hqO⟩ := hq
  have hd : (fun A : ComplexCoordinates l => (p.1 - q.1) A + ((1 / 2 : ℂ) • (p.2 - q.2)) A A)
      =O[𝓝 0] fun A : ComplexCoordinates l => ‖A‖ ^ 3 :=
    (hqO.sub hpO).congr_left fun z => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
  obtain ⟨hφ, hβ⟩ := hu (ComplexCoordinates l) _ _ hd
  have hdiag : ∀ z, p.2 z z = q.2 z z := fun z => by
    have hz := hβ z
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul] at hz
    have h2 : p.2 z z - q.2 z z = 0 := by simpa using hz
    exact sub_eq_zero.1 h2
  have hφ' : p.1 = q.1 := sub_eq_zero.1 hφ
  have hβ' : p.2 = q.2 := by
    refine LinearMap.ext fun z => LinearMap.ext fun z' => ?_
    have e1 := hdiag (z + z')
    simp only [map_add, LinearMap.add_apply] at e1
    rw [hdiag z, hdiag z', hps z' z, hqs z' z] at e1
    linear_combination e1 / 2
  exact Prod.ext hφ' hβ'
theorem exists_secondOrderExpansion (hps : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {ρ : ℝ} (hρ : 0 < ρ) {f : ComplexCoordinates l → ℂ}
    (hf : ComplexCoordinates.IsHolomorphicIn (N' := 1) (openPolydisk 0 ρ) (fun z _ => f z)) :
    ∃ p : (ComplexCoordinates l →ₗ[ℂ] ℂ) ×
        (ComplexCoordinates l →ₗ[ℂ] ComplexCoordinates l →ₗ[ℂ] ℂ),
      IsSecondOrderExpansion f p.1 p.2 := by
  have hsub : closedPolydisk (0 : ComplexCoordinates l) (ρ / 2) ⊆ openPolydisk 0 ρ :=
    fun z hz j => lt_of_le_of_lt (hz j) (by linarith)
  have h0U : (0 : ComplexCoordinates l) ∈ openPolydisk (0 : ComplexCoordinates l) ρ :=
    fun j => by simpa using hρ
  obtain ⟨c, hsum, hconv⟩ :=
    ((hps.1 l _ hf.1).1 1 _ hf).1 0 h0U (ρ / 2) (by linarith) hsub
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ρ / 4 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; linarith
  let a : (Fin l → ℕ) → ℂ := fun m => c m 0
  let t : ComplexCoordinates l → (Fin l → ℕ) → ℂ := fun z m => coordMonomial m z * a m
  have ht : ∀ z : ComplexCoordinates l, ‖z‖ ≤ r → HasSum (t z) (f z) := by
    intro z hz
    have hzU : z ∈ openPolydisk (0 : ComplexCoordinates l) (ρ / 2) := fun j => by
      have := (norm_le_pi_norm z j).trans hz
      simp only [Pi.zero_apply, sub_zero]
      linarith
    have := Pi.hasSum.1 (hsum z hzU) 0
    simpa [t, a, coordMonomial, monomialTerm] using this
  let p : ComplexCoordinates l := fun _ => (r : ℂ)
  have hpmem : p ∈ closedPolydisk (0 : ComplexCoordinates l) r := fun j => by
    simp [p, abs_of_pos hr0]
  let A : (Fin l → ℕ) → ℝ := fun m => ‖monomialTerm c 0 p m‖
  have hA : Summable A := (hconv r (by linarith)).1 p hpmem
  have hAval : ∀ m, A m = r ^ (∑ j, m j) * ‖c m‖ := by
    intro m
    have e : (∏ j, (p j - (0 : ComplexCoordinates l) j) ^ m j) = (r : ℂ) ^ ∑ j, m j := by
      simp [p, Finset.prod_pow_eq_pow_sum]
    simp only [A, monomialTerm]
    rw [e, norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hA0 : ∀ m, 0 ≤ A m := fun m => norm_nonneg _
  have hbound : ∀ (z : ComplexCoordinates l), ‖z‖ ≤ r → ∀ m : Fin l → ℕ, 3 ≤ ∑ j, m j →
      ‖t z m‖ ≤ A m * (‖z‖ / r) ^ 3 := by
    intro z hz m hm
    have hx0 : 0 ≤ ‖z‖ / r := by positivity
    have hx1 : ‖z‖ / r ≤ 1 := (div_le_one hr0).2 hz
    have hzr : ‖z‖ = r * (‖z‖ / r) := by field_simp
    have hpow : ‖z‖ ^ (∑ j, m j) ≤ r ^ (∑ j, m j) * (‖z‖ / r) ^ 3 := by
      calc ‖z‖ ^ (∑ j, m j) = r ^ (∑ j, m j) * (‖z‖ / r) ^ (∑ j, m j) := by
            rw [← mul_pow, ← hzr]
        _ ≤ r ^ (∑ j, m j) * (‖z‖ / r) ^ 3 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0 hx1 hm) (by positivity)
    calc ‖t z m‖ = ‖coordMonomial m z‖ * ‖a m‖ := norm_mul _ _
      _ ≤ ‖z‖ ^ (∑ j, m j) * ‖c m‖ :=
          mul_le_mul (norm_coordMonomial_le m z) (norm_le_pi_norm (c m) 0) (norm_nonneg _)
            (by positivity)
      _ ≤ (r ^ (∑ j, m j) * (‖z‖ / r) ^ 3) * ‖c m‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = A m * (‖z‖ / r) ^ 3 := by rw [hAval]; ring
  let S : Finset (Fin l → ℕ) :=
    exponentsOfDegree l 0 ∪ (exponentsOfDegree l 1 ∪ exponentsOfDegree l 2)
  have hS : ∀ m, m ∈ S ↔ ∑ j, m j ≤ 2 := by
    intro m
    simp only [S, Finset.mem_union, mem_exponentsOfDegree]
    omega
  have hSsum : ∀ z, ∑ m ∈ S, t z m = ∑ m ∈ exponentsOfDegree l 0, t z m +
      (∑ m ∈ exponentsOfDegree l 1, t z m + ∑ m ∈ exponentsOfDegree l 2, t z m) := by
    intro z
    have d1 : Disjoint (exponentsOfDegree l 1) (exponentsOfDegree l 2) :=
      Finset.disjoint_left.2 fun m h1 h2 => by
        rw [mem_exponentsOfDegree] at h1 h2
        omega
    have d0 : Disjoint (exponentsOfDegree l 0) (exponentsOfDegree l 1 ∪ exponentsOfDegree l 2) :=
      Finset.disjoint_left.2 fun m h1 h2 => by
        rw [Finset.mem_union, mem_exponentsOfDegree, mem_exponentsOfDegree] at h2
        rw [mem_exponentsOfDegree] at h1
        omega
    simp only [S]
    rw [Finset.sum_union d0, Finset.sum_union d1]
  have hD0 : exponentsOfDegree l 0 = {0} := by
    ext m
    rw [mem_exponentsOfDegree, Finset.mem_singleton]
    exact ⟨exponent_eq_zero_of_sum_eq_zero, fun hm => by simp [hm]⟩
  have hf0 : f 0 = a 0 := by
    have h1 : HasSum (t 0) (t 0 0) := by
      refine hasSum_single 0 fun m hm => ?_
      have hex : ∃ j, m j ≠ 0 := by
        by_contra hcon
        simp only [not_exists, ne_eq, not_not] at hcon
        exact hm (funext hcon)
      obtain ⟨j, hj⟩ := hex
      have : coordMonomial m (0 : ComplexCoordinates l) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
      simp [t, this]
    have h2 := (ht 0 (by simpa using hr0.le)).unique h1
    rw [h2]
    simp [t, coordMonomial_zero]
  choose L hL using exists_linearMap_eq_coordMonomial (l := l)
  choose B hBs hB using exists_symmetric_bilinear_eq_coordMonomial (l := l)
  let φ : ComplexCoordinates l →ₗ[ℂ] ℂ := ∑ m ∈ exponentsOfDegree l 1, a m • L m
  let β : ComplexCoordinates l →ₗ[ℂ] ComplexCoordinates l →ₗ[ℂ] ℂ :=
    ∑ m ∈ exponentsOfDegree l 2, a m • B m
  have hφ : ∀ z, φ z = ∑ m ∈ exponentsOfDegree l 1, t z m := by
    intro z
    simp only [φ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hL m (mem_exponentsOfDegree.1 hm) z]
    simp only [t]
    ring
  have hβ : ∀ z, (1 / 2 : ℂ) * β z z = ∑ m ∈ exponentsOfDegree l 2, t z m := by
    intro z
    simp only [β, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hB m (mem_exponentsOfDegree.1 hm) z]
    simp only [t]
    ring
  refine ⟨(φ, β), ?_, ?_⟩
  · intro z z'
    simp only [β, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Finset.sum_congr rfl fun m _ => by rw [hBs]
  · refine IsBigO.of_bound ((∑' m, A m) / r ^ 3) ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ComplexCoordinates l) hr0] with z hz
    have hzr : ‖z‖ ≤ r := by simpa using hz
    have hres : HasSum (fun m => if ∑ j, m j ≤ 2 then 0 else t z m)
        (f z - ∑ m ∈ S, t z m) := by
      have h1 : HasSum (fun m => if m ∈ S then t z m else 0) (∑ m ∈ S, t z m) := by
        have h0 : HasSum (fun m => if m ∈ S then t z m else 0)
            (∑ m ∈ S, if m ∈ S then t z m else 0) :=
          hasSum_sum_of_ne_finset_zero fun m hm => by simp [hm]
        rwa [Finset.sum_congr rfl fun m hm => if_pos hm] at h0
      have hfun : (fun m => if ∑ j, m j ≤ 2 then 0 else t z m)
          = fun m => t z m - if m ∈ S then t z m else 0 := by
        funext m
        by_cases hm : ∑ j, m j ≤ 2
        · simp [hm, (hS m).2 hm]
        · have hmS : m ∉ S := fun h' => hm ((hS m).1 h')
          simp [hm, hmS]
      rw [hfun]
      exact (ht z hzr).sub h1
    have hval : f z - (f 0 + φ z + (1 / 2 : ℂ) * β z z) =
        ∑' m, if ∑ j, m j ≤ 2 then 0 else t z m := by
      rw [hres.tsum_eq, hSsum, hD0, Finset.sum_singleton, hφ, hβ, hf0]
      simp only [t, coordMonomial_zero, one_mul]
      ring
    have hle : ‖∑' m, if ∑ j, m j ≤ 2 then 0 else t z m‖ ≤ (∑' m, A m) * (‖z‖ / r) ^ 3 := by
      refine tsum_of_norm_bounded (hA.hasSum.mul_right _) fun m => ?_
      by_cases hm : ∑ j, m j ≤ 2
      · simp only [hm, if_true, norm_zero]
        exact mul_nonneg (hA0 m) (by positivity)
      · simp only [hm, if_false]
        exact hbound z hzr m (by omega)
    simp only [hval]
    calc _ ≤ (∑' m, A m) * (‖z‖ / r) ^ 3 := hle
      _ = (∑' m, A m) / r ^ 3 * ‖‖z‖ ^ 3‖ := by
          rw [norm_pow, norm_norm, div_pow]
          ring
theorem uniqueExpansion_holds (hu : YangMills.Construction.Taylor.QuadraticTaylorUniqueness)
    (hps : ComplexCoordinates.PowerSeriesHolomorphy.Properties) : UniqueExpansion := by
  intro l ρ hρ f hf
  exact existsUnique_of_exists_of_unique (exists_secondOrderExpansion hps hρ hf)
    fun _ _ hp hq => secondOrderExpansion_unique hu hp hq
end YangMills.Construction.Coordinates.QuadraticTaylor
