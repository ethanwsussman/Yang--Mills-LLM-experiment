import YangMills.Construction.TorusOrFourSpace.DistanceAndLiftsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefined
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.TupleMetric
open Kind
open TorusMetric (euclidNormVec)
variable {p : ℕ+}
abbrev coordNorm (v : Coords p) : ℝ := Real.sqrt (∑ j, v j ^ 2)
def ofBlocks (g : Fin (p : ℕ) → Fin 4 → ℝ) : Coords p :=
  fun j => g ⟨(j : ℕ) / 4, by have := j.2; omega⟩ ⟨(j : ℕ) % 4, by omega⟩
theorem block_ofBlocks (g : Fin (p : ℕ) → Fin 4 → ℝ) (i : Fin (p : ℕ)) :
    Coords.block (ofBlocks g) i = g i := by
  funext μ
  have h1 : (4 * (i : ℕ) + (μ : ℕ)) / 4 = i := by have := μ.2; omega
  have h2 : (4 * (i : ℕ) + (μ : ℕ)) % 4 = μ := by have := μ.2; omega
  exact congrArg₂ g (Fin.ext h1) (Fin.ext h2)
theorem block_sub (a b : Coords p) (i : Fin (p : ℕ)) :
    Coords.block (a - b) i = Coords.block a i - Coords.block b i := rfl
theorem block_add (a b : Coords p) (i : Fin (p : ℕ)) :
    Coords.block (a + b) i = Coords.block a i + Coords.block b i := rfl
theorem block_neg (a : Coords p) (i : Fin (p : ℕ)) :
    Coords.block (-a) i = -Coords.block a i := rfl
theorem block_zero (i : Fin (p : ℕ)) : Coords.block (0 : Coords p) i = 0 := rfl
theorem sum_sq_eq_sum_block (v : Coords p) :
    ∑ j, v j ^ 2 = ∑ i, ∑ μ, Coords.block v i μ ^ 2 := by
  let e : Fin (p : ℕ) × Fin 4 ≃ Fin (4 * (p : ℕ)) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm _ _))
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun μ _ => ?_
  have h : e (i, μ) = ⟨4 * (i : ℕ) + (μ : ℕ), by have := i.2; have := μ.2; omega⟩ := by
    apply Fin.ext
    simp [e, finProdFinEquiv]
    omega
  rw [h]
  rfl
theorem coordNorm_eq_sqrt_sum_block (v : Coords p) :
    coordNorm v = Real.sqrt (∑ i, euclidNormVec (Coords.block v i) ^ 2) := by
  rw [coordNorm, sum_sq_eq_sum_block]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [euclidNormVec, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
theorem coordNorm_neg (v : Coords p) : coordNorm (-v) = coordNorm v := by
  simp [coordNorm]
theorem coordNorm_add_le (a b : Coords p) : coordNorm (a + b) ≤ coordNorm a + coordNorm b := by
  have h (v : Coords p) :
      coordNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (4 * (p : ℕ))))‖ := by
    simp [coordNorm, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
  rw [h, h, h, WithLp.toLp_add]
  exact norm_add_le _ _
theorem eq_zero_of_coordNorm_eq_zero (v : Coords p) (h : coordNorm v = 0) : v = 0 := by
  have hs := (Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 hs
  funext j
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (hz j (Finset.mem_univ j))
variable (D : Params) (E : Kind)
theorem zero_mem_periodSet : (0 : Coords p) ∈ Tuple.periodSet D E p :=
  fun i => by rw [block_zero]; exact (E.periodGroup D).zero_mem
theorem add_mem_periodSet {a b : Coords p} (ha : a ∈ Tuple.periodSet D E p)
    (hb : b ∈ Tuple.periodSet D E p) : a + b ∈ Tuple.periodSet D E p :=
  fun i => by rw [block_add]; exact (E.periodGroup D).add_mem (ha i) (hb i)
theorem neg_mem_periodSet {a : Coords p} (ha : a ∈ Tuple.periodSet D E p) :
    -a ∈ Tuple.periodSet D E p :=
  fun i => by rw [block_neg]; exact (E.periodGroup D).neg_mem (ha i)
variable {D E}
theorem proj_eq_proj_iff (hL : WellPosedness.SameLiftIffSubPeriod D E)
    (x x' : Coords p) :
    Tuple.proj D E x = Tuple.proj D E x' ↔
      x - x' ∈ Tuple.periodSet D E p := by
  constructor
  · intro h i
    have hi : E.quotMap D (Coords.block x i) =
        E.quotMap D (Coords.block x' i) := congrFun h i
    rw [block_sub]
    exact (hL _ _).1 ⟨_, rfl, hi.symm⟩
  · intro h
    funext i
    have hi : Coords.block x i - Coords.block x' i ∈ E.periodGroup D := h i
    obtain ⟨y, h1, h2⟩ := (hL _ _).2 hi
    exact h1.trans h2.symm
theorem proj_surjective (hS : Function.Surjective (E.quotMap D)) :
    Function.Surjective (Tuple.proj D E (p := p)) := by
  intro y
  choose g hg using fun i => hS (y i)
  refine ⟨ofBlocks g, ?_⟩
  funext i
  show E.quotMap D (Coords.block (ofBlocks g) i) = y i
  rw [block_ofBlocks, hg]
theorem tupleDist_isLeast (hD : WellPosedness.QuotDistEqMinTranslateNorm D E)
    (x x' : Coords p) :
    IsLeast {r | ∃ k ∈ Tuple.periodSet D E p, r = coordNorm (x - x' - k)}
      (Tuple.tupleDist D E (Tuple.proj D E x)
        (Tuple.proj D E x')) := by
  have hmem : ∀ i, ∃ k ∈ E.periodGroup D,
      quotDist D E (E.quotMap D (Coords.block x i))
          (E.quotMap D (Coords.block x' i)) =
        euclidNormVec (Coords.block x i - Coords.block x' i - k) :=
    fun i => (hD (Coords.block x i) (Coords.block x' i)).1
  constructor
  · choose k hk hk' using hmem
    refine ⟨ofBlocks k, fun i => ?_, ?_⟩
    · rw [block_ofBlocks]
      exact hk i
    · rw [coordNorm_eq_sqrt_sum_block]
      show Real.sqrt (∑ i, quotDist D E (E.quotMap D (Coords.block x i))
        (E.quotMap D (Coords.block x' i)) ^ 2) = _
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hk' i, block_sub, block_sub, block_ofBlocks]
  · rintro r ⟨k, hk, rfl⟩
    rw [coordNorm_eq_sqrt_sum_block]
    show Real.sqrt (∑ i, quotDist D E (E.quotMap D (Coords.block x i))
      (E.quotMap D (Coords.block x' i)) ^ 2) ≤ _
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    have hle : quotDist D E (E.quotMap D (Coords.block x i))
        (E.quotMap D (Coords.block x' i)) ≤
        euclidNormVec (Coords.block x i - Coords.block x' i - Coords.block k i) :=
      (hD (Coords.block x i) (Coords.block x' i)).2 ⟨Coords.block k i, hk i, rfl⟩
    have h0 : 0 ≤ quotDist D E (E.quotMap D (Coords.block x i))
        (E.quotMap D (Coords.block x' i)) := by
      obtain ⟨k₀, -, h⟩ := hmem i
      rw [h]
      exact Real.sqrt_nonneg _
    rw [block_sub, block_sub]
    exact pow_le_pow_left₀ h0 hle 2
theorem quotientDistanceAndLifts_holds (wellPosed : WellPosedness.WellPosed) :
    QuotientDistanceAndLifts := by
  intro D E p
  obtain ⟨hQ, -, hDiff, -, -, -, hLeast, -⟩ := wellPosed D E
  have surj := proj_surjective (p := p) hQ.2.1
  have fib := proj_eq_proj_iff (p := p) hDiff
  have least := tupleDist_isLeast (p := p) hLeast
  have le : ∀ x x' : Coords p,
      Tuple.tupleDist D E (Tuple.proj D E x)
        (Tuple.proj D E x') ≤ coordNorm (x - x') := fun x x' =>
    (least x x').2 ⟨0, zero_mem_periodSet D E, by rw [sub_zero]⟩
  have nonneg : ∀ y y' : E.Tuple D p, 0 ≤ Tuple.tupleDist D E y y' :=
    fun _ _ => Real.sqrt_nonneg _
  have symmLe : ∀ x x' : Coords p,
      Tuple.tupleDist D E (Tuple.proj D E x)
          (Tuple.proj D E x') ≤
        Tuple.tupleDist D E (Tuple.proj D E x')
          (Tuple.proj D E x) := by
    intro x x'
    obtain ⟨k, hk, hk'⟩ := (least x' x).1
    rw [hk', ← coordNorm_neg]
    exact (least x x').2 ⟨-k, neg_mem_periodSet D E hk, by congr 1; abel⟩
  refine ⟨⟨surj, fib⟩, fun x x' => ⟨least x x', le x x'⟩, ⟨nonneg, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro y y'
    obtain ⟨x, rfl⟩ := surj y
    obtain ⟨x', rfl⟩ := surj y'
    constructor
    · intro h
      obtain ⟨k, hk, hk'⟩ := (least x x').1
      have hv := eq_zero_of_coordNorm_eq_zero _ (hk'.symm.trans h)
      refine (fib x x').2 ?_
      rw [sub_eq_zero.1 hv]
      exact hk
    · intro h
      rw [h]
      refine le_antisymm ?_ (nonneg _ _)
      have h0 := le x' x'
      rw [sub_self] at h0
      simpa [coordNorm] using h0
  · intro y y'
    obtain ⟨x, rfl⟩ := surj y
    obtain ⟨x', rfl⟩ := surj y'
    exact le_antisymm (symmLe x x') (symmLe x' x)
  · intro y y' y''
    obtain ⟨x, rfl⟩ := surj y
    obtain ⟨x', rfl⟩ := surj y'
    obtain ⟨x'', rfl⟩ := surj y''
    obtain ⟨k, hk, hk'⟩ := (least x x').1
    obtain ⟨k', hl, hl'⟩ := (least x' x'').1
    rw [hk', hl']
    refine le_trans ((least x x'').2 ⟨k + k', add_mem_periodSet D E hk hl, rfl⟩) ?_
    have hv : x - x'' - (k + k') = (x - x' - k) + (x' - x'' - k') := by abel
    rw [hv]
    exact coordNorm_add_le _ _
  · intro x y'
    obtain ⟨x'', rfl⟩ := surj y'
    obtain ⟨k, hk, hk'⟩ := (least x x'').1
    refine ⟨x'' + k, (fib _ _).2 ?_, ?_⟩
    · rw [add_sub_cancel_left]
      exact hk
    · rw [hk', sub_sub]
  · intro y y'
    obtain ⟨x, hx⟩ := surj y
    obtain ⟨x', hx'⟩ := surj y'
    refine ⟨Tuple.tupleDist D E y y', fun a b ha hb => ?_, fun r hr => ?_⟩
    · have h := least a b
      rw [show Tuple.proj D E a = y from ha,
        show Tuple.proj D E b = y' from hb] at h
      exact h
    · have h := least x x'
      rw [hx, hx'] at h
      exact (hr x x' hx hx').unique h
end YangMills.Construction.PeriodicSpace.TupleMetric
