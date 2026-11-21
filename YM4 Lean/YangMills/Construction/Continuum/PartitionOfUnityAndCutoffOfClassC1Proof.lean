import YangMills.Construction.PassageToTheLimit.PartitionOfUnityOfClassC1WithSmallPiecesProof
import YangMills.Construction.Continuum.PartitionOfUnityAndCutoffOfClassC1
import Mathlib
set_option autoImplicit false
open YangMills.Construction.EuclideanBalls
noncomputable section
namespace YangMills.Construction.PartitionOfUnity
def translateBump (s : ℝ) : ℝ := Real.smoothTransition (s + 1) - Real.smoothTransition s
theorem translateBump_contDiff : ContDiff ℝ 1 translateBump := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.bump_contDiff <;> assumption
theorem translateBump_nonneg (t : ℝ) : 0 ≤ translateBump t := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.bump_nonneg <;> assumption
theorem translateBump_le_one (t : ℝ) : translateBump t ≤ 1 := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.bump_le_one <;> assumption
theorem translateBump_eq_zero_of_one_le_abs {t : ℝ} (ht : 1 ≤ |t|) : translateBump t = 0 := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.bump_eq_zero <;> assumption
theorem translateBump_add_sub_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    translateBump t + translateBump (t - 1) = 1 := by
  unfold translateBump
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ t + 1),
    Real.smoothTransition.zero_of_nonpos (by linarith : t - 1 ≤ 0), sub_add_cancel]
  ring
variable {n : ℕ}
def productBump (ε : ℝ) (k : Fin n → ℤ) (z : Fin n → ℝ) : ℝ :=
  ∏ μ, translateBump (z μ / ε - k μ)
def latticeCube (ε : ℝ) (k : Fin n → ℤ) : Set (Fin n → ℝ) :=
  Set.Icc (fun μ => ε * ((k μ : ℝ) - 1)) (fun μ => ε * ((k μ : ℝ) + 1))
theorem productBump_contDiff (ε : ℝ) (k : Fin n → ℤ) : ContDiff ℝ 1 (productBump ε k) := by
  show ContDiff ℝ 1 (fun z : Fin n → ℝ => ∏ μ, translateBump (z μ / ε - k μ))
  refine contDiff_prod fun μ _ => translateBump_contDiff.comp ?_
  exact ((contDiff_apply ℝ ℝ μ).div_const ε).sub contDiff_const
theorem support_productBump_subset {ε : ℝ} (hε : 0 < ε) (k : Fin n → ℤ) :
    Function.support (productBump ε k) ⊆ latticeCube ε k := by
  intro z hz
  have hne : ∀ μ, translateBump (z μ / ε - k μ) ≠ 0 := fun μ =>
    Finset.prod_ne_zero_iff.1 hz μ (Finset.mem_univ μ)
  have hlt : ∀ μ, |z μ / ε - k μ| < 1 := fun μ => by
    by_contra hc
    exact hne μ (translateBump_eq_zero_of_one_le_abs (not_lt.1 hc))
  refine ⟨fun μ => ?_, fun μ => ?_⟩
  · have ha := (abs_lt.1 (hlt μ)).1
    have hb : (k μ : ℝ) - 1 ≤ z μ / ε := by linarith
    have := (le_div_iff₀ hε).1 hb
    show ε * ((k μ : ℝ) - 1) ≤ z μ
    linarith
  · have ha := (abs_lt.1 (hlt μ)).2
    have hb : z μ / ε ≤ (k μ : ℝ) + 1 := by linarith
    have := (div_le_iff₀ hε).1 hb
    show z μ ≤ ε * ((k μ : ℝ) + 1)
    linarith
theorem tsupport_productBump_subset {ε : ℝ} (hε : 0 < ε) (k : Fin n → ℤ) :
    tsupport (productBump ε k) ⊆ latticeCube ε k :=
  closure_minimal (support_productBump_subset hε k) isClosed_Icc
theorem productBump_mem_compactC1 {ε : ℝ} (hε : 0 < ε) (k : Fin n → ℤ) :
    productBump ε k ∈ compactC1 n ℝ :=
  ⟨productBump_contDiff ε k,
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
      (tsupport_productBump_subset hε k)⟩
theorem productBump_mem_unitInterval (ε : ℝ) (k : Fin n → ℤ) (z : Fin n → ℝ) :
    productBump ε k z ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg fun _ _ => translateBump_nonneg _,
    Finset.prod_le_one (fun _ _ => translateBump_nonneg _) fun _ _ => translateBump_le_one _⟩
theorem sqrtSumSq_sub_le_of_mem_latticeCube {ε : ℝ} (hε : 0 < ε) (hn : n ≤ 4) (k : Fin n → ℤ)
    {x y : Fin n → ℝ} (hx : x ∈ latticeCube ε k) (hy : y ∈ latticeCube ε k) :
    EuclideanCoords.sqrtSumSq (x - y) ≤ 4 * ε := by
  have hcoord : ∀ μ, (x - y) μ ^ 2 ≤ (2 * ε) ^ 2 := fun μ => by
    have hx1 : ε * ((k μ : ℝ) - 1) ≤ x μ := hx.1 μ
    have hx2 : x μ ≤ ε * ((k μ : ℝ) + 1) := hx.2 μ
    have hy1 : ε * ((k μ : ℝ) - 1) ≤ y μ := hy.1 μ
    have hy2 : y μ ≤ ε * ((k μ : ℝ) + 1) := hy.2 μ
    rw [Pi.sub_apply]
    exact sq_le_sq' (by nlinarith) (by nlinarith)
  have hsum : ∑ μ, (x - y) μ ^ 2 ≤ (n : ℝ) * (2 * ε) ^ 2 := by
    calc ∑ μ, (x - y) μ ^ 2 ≤ ∑ _μ : Fin n, (2 * ε) ^ 2 := Finset.sum_le_sum fun μ _ => hcoord μ
      _ = (n : ℝ) * (2 * ε) ^ 2 := by simp
  have hnr : (n : ℝ) ≤ 4 := by exact_mod_cast hn
  have hbound : ∑ μ, (x - y) μ ^ 2 ≤ (4 * ε) ^ 2 := by
    have : (n : ℝ) * (2 * ε) ^ 2 ≤ 4 * (2 * ε) ^ 2 :=
      mul_le_mul_of_nonneg_right hnr (by positivity)
    nlinarith
  exact Real.sqrt_le_iff.2 ⟨by positivity, hbound⟩
theorem finite_setOf_tsupport_productBump_inter_nonempty {ε : ℝ} (hε : 0 < ε)
    {B : Set (Fin n → ℝ)} (hB : Bornology.IsBounded B) :
    {k : Fin n → ℤ | (tsupport (productBump ε k) ∩ B).Nonempty}.Finite := by
  obtain ⟨R, hR⟩ := hB.exists_norm_le
  set N : ℤ := ⌈R / ε⌉ + 1 with hN
  have hceil : R / ε ≤ (⌈R / ε⌉ : ℝ) := Int.le_ceil _
  refine (Set.finite_Icc (fun _ : Fin n => -N) (fun _ => N)).subset ?_
  rintro k ⟨z, hz, hzB⟩
  have hcube := tsupport_productBump_subset hε k hz
  have hzR : ∀ μ, |z μ| ≤ R := fun μ =>
    (Real.norm_eq_abs _ ▸ norm_le_pi_norm z μ).trans (hR z hzB)
  have hzdiv : ∀ μ, |z μ / ε| ≤ R / ε := fun μ => by
    rw [abs_div, abs_of_pos hε]
    exact div_le_div_of_nonneg_right (hzR μ) hε.le
  have hNreal : (N : ℝ) = (⌈R / ε⌉ : ℝ) + 1 := by rw [hN]; push_cast; ring
  refine ⟨fun μ => ?_, fun μ => ?_⟩
  · have hl : ε * ((k μ : ℝ) - 1) ≤ z μ := hcube.1 μ
    have hu : z μ ≤ ε * ((k μ : ℝ) + 1) := hcube.2 μ
    have hq : z μ / ε ≤ (k μ : ℝ) + 1 := (div_le_iff₀ hε).2 (by linarith)
    have hr := (abs_le.1 (hzdiv μ)).1
    have : (-N : ℝ) ≤ (k μ : ℝ) := by linarith
    exact_mod_cast this
  · have hl : ε * ((k μ : ℝ) - 1) ≤ z μ := hcube.1 μ
    have hq : (k μ : ℝ) - 1 ≤ z μ / ε := (le_div_iff₀ hε).2 (by linarith)
    have hr := (abs_le.1 (hzdiv μ)).2
    have : (k μ : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast this
theorem sum_translateBump_floor_pair (t : ℝ) :
    ∑ j ∈ ({⌊t⌋, ⌊t⌋ + 1} : Finset ℤ), translateBump (t - j) = 1 := by
  rw [Finset.sum_pair (by omega)]
  have hsum := translateBump_add_sub_one (Int.fract_nonneg t) (Int.fract_lt_one t)
  have hf : Int.fract t = t - (⌊t⌋ : ℝ) := rfl
  rw [hf] at hsum
  have hc : t - ((⌊t⌋ + 1 : ℤ) : ℝ) = t - (⌊t⌋ : ℝ) - 1 := by push_cast; ring
  rw [hc]
  exact hsum
theorem translateBump_sub_eq_zero_of_not_mem {t : ℝ} {j : ℤ}
    (hj : j ∉ ({⌊t⌋, ⌊t⌋ + 1} : Finset ℤ)) : translateBump (t - j) = 0 := by
  have hlow : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
  have hup : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one t
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  apply translateBump_eq_zero_of_one_le_abs
  rcases lt_or_gt_of_ne hj.1 with hlt | hgt
  · have : (j : ℝ) + 1 ≤ (⌊t⌋ : ℝ) := by exact_mod_cast hlt
    exact le_abs.2 (Or.inl (by linarith))
  · have htwo : ⌊t⌋ + 2 ≤ j := by omega
    have : (⌊t⌋ : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast htwo
    exact le_abs.2 (Or.inr (by linarith))
theorem hasSum_productBump (ε : ℝ) (z : Fin n → ℝ) : HasSum (fun k => productBump ε k z) 1 := by
  classical
  set S : Finset (Fin n → ℤ) :=
    Fintype.piFinset fun μ => ({⌊z μ / ε⌋, ⌊z μ / ε⌋ + 1} : Finset ℤ) with hS
  have hzero : ∀ k ∉ S, productBump ε k z = 0 := by
    intro k hk
    rw [hS, Fintype.mem_piFinset, not_forall] at hk
    obtain ⟨μ, hμ⟩ := hk
    exact Finset.prod_eq_zero (Finset.mem_univ μ) (translateBump_sub_eq_zero_of_not_mem hμ)
  have hfin : ∑ k ∈ S, productBump ε k z = 1 := by
    have := Finset.prod_univ_sum (fun μ => ({⌊z μ / ε⌋, ⌊z μ / ε⌋ + 1} : Finset ℤ))
      (fun μ (j : ℤ) => translateBump (z μ / ε - j))
    simp only [sum_translateBump_floor_pair, Finset.prod_const_one] at this
    exact this.symm
  exact hfin ▸ hasSum_sum_of_ne_finset_zero hzero
def radialCutoff (ρ : ℝ) (y : Fin 2 → ℝ) : ℝ :=
  1 - Real.smoothTransition ((∑ i, y i ^ 2) / ρ ^ 2 - 1)
theorem radialCutoff_contDiff (ρ : ℝ) : ContDiff ℝ 1 (radialCutoff ρ) := by
  show ContDiff ℝ 1 (fun y : Fin 2 → ℝ => 1 - Real.smoothTransition ((∑ i, y i ^ 2) / ρ ^ 2 - 1))
  refine contDiff_const.sub (Real.smoothTransition.contDiff.comp ?_)
  exact ((ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).pow 2).div_const _).sub contDiff_const
theorem radialCutoff_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {y : Fin 2 → ℝ}
    (hy : 2 * ρ ^ 2 ≤ ∑ i, y i ^ 2) : radialCutoff ρ y = 0 := by
  have hq : 2 ≤ (∑ i, y i ^ 2) / ρ ^ 2 := (le_div_iff₀ (by positivity)).2 hy
  unfold radialCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith), sub_self]
theorem radialCutoff_eq_one {ρ : ℝ} (hρ : 0 < ρ) {y : Fin 2 → ℝ}
    (hy : ∑ i, y i ^ 2 ≤ ρ ^ 2) : radialCutoff ρ y = 1 := by
  have hq : (∑ i, y i ^ 2) / ρ ^ 2 ≤ 1 := (div_le_one (by positivity)).2 hy
  unfold radialCutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]
theorem radialCutoff_hasCompactSupport {ρ : ℝ} (hρ : 0 < ρ) :
    HasCompactSupport (radialCutoff ρ) := by
  refine HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin 2 => -(2 * ρ)) (fun _ => 2 * ρ))) ?_
  intro y hy
  apply radialCutoff_eq_zero hρ
  have hex : ∃ i, (2 * ρ) ^ 2 ≤ y i ^ 2 := by
    by_contra hc
    simp only [not_exists, not_le] at hc
    refine hy ⟨fun i => ?_, fun i => ?_⟩
    · exact (abs_le.1 (abs_le_of_sq_le_sq (hc i).le (by positivity))).1
    · exact (abs_le.1 (abs_le_of_sq_le_sq (hc i).le (by positivity))).2
  obtain ⟨i, hi⟩ := hex
  have hsingle : y i ^ 2 ≤ ∑ j, y j ^ 2 :=
    Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [sq_nonneg ρ]
theorem c1PartitionAndCutoffExist_holds : C1PartitionAndCutoffExist := by
  refine ⟨fun κ hκ ε hε => ⟨productBump ε, fun k => productBump_mem_compactC1 hε k,
      fun k z => productBump_mem_unitInterval ε k z, fun k x hx y hy => ?_,
      fun B hB => finite_setOf_tsupport_productBump_inter_nonempty hε hB,
      fun z => hasSum_productBump ε z⟩,
    fun ρ hρ => ⟨radialCutoff ρ, ⟨radialCutoff_contDiff ρ, radialCutoff_hasCompactSupport hρ⟩,
      fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩⟩
  · exact sqrtSumSq_sub_le_of_mem_latticeCube hε (by omega) k
      (tsupport_productBump_subset hε k hx) (tsupport_productBump_subset hε k hy)
  · have ha := Real.smoothTransition.le_one ((∑ i, y i ^ 2) / ρ ^ 2 - 1)
    have hb := Real.smoothTransition.nonneg ((∑ i, y i ^ 2) / ρ ^ 2 - 1)
    exact ⟨by unfold radialCutoff; linarith, by unfold radialCutoff; linarith⟩
  · exact radialCutoff_eq_one hρ ((Real.sqrt_le_left hρ.le).1 hy)
  · apply radialCutoff_eq_zero hρ
    have hnn : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hsq := pow_le_pow_left₀ (by positivity) hy 2
    have hs : EuclideanCoords.sqrtSumSq y ^ 2 = ∑ i, y i ^ 2 := Real.sq_sqrt hnn
    rw [hs, mul_pow, Real.sq_sqrt (by norm_num)] at hsq
    exact hsq
end YangMills.Construction.PartitionOfUnity
