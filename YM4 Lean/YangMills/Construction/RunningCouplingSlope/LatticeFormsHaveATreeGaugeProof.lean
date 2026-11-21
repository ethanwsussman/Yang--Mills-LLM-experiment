import YangMills.Construction.RunningCouplingSlope.LatticeFormsHaveATreeGauge
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FlatLinearization
open YangMills.Construction.BlockAverages YangMills.Construction.FlatPairing YangMills.Construction.LatticeFractionalIntegration YangMills.Construction.SlopeCoefficient
private def rayPartialSum (ξ : LatticeOneForm) (x : Fin 4 → ℤ) (μ : Fin 4) : ℤ → ℝ
  | Int.ofNat k => ∑ i ∈ Finset.range k, ξ (x + (i : ℤ) • basisVector μ, μ)
  | Int.negSucc k => - ∑ i ∈ Finset.range (k + 1), ξ (x + (-((i : ℤ) + 1)) • basisVector μ, μ)
private theorem rayPartialSum_zero (ξ : LatticeOneForm) (x : Fin 4 → ℤ) (μ : Fin 4) :
    rayPartialSum ξ x μ 0 = 0 := by
  show rayPartialSum ξ x μ (Int.ofNat 0) = 0
  simp [rayPartialSum]
private theorem rayPartialSum_succ_sub (ξ : LatticeOneForm) (x : Fin 4 → ℤ) (μ : Fin 4) (k : ℤ) :
    rayPartialSum ξ x μ (k + 1) - rayPartialSum ξ x μ k = ξ (x + k • basisVector μ, μ) := by
  cases k with
  | ofNat n =>
    have h : (Int.ofNat n + 1 : ℤ) = Int.ofNat (n + 1) := rfl
    rw [h]
    simp only [rayPartialSum, Finset.sum_range_succ]
    simp
  | negSucc n =>
    cases n with
    | zero =>
      have h : (Int.negSucc 0 + 1 : ℤ) = Int.ofNat 0 := rfl
      rw [h]
      simp [rayPartialSum]
    | succ m =>
      have h : (Int.negSucc (m + 1) + 1 : ℤ) = Int.negSucc m := rfl
      have h2 : (Int.negSucc (m + 1) : ℤ) = -(((m + 1 : ℕ) : ℤ) + 1) := rfl
      rw [h]
      simp only [rayPartialSum]
      rw [Finset.sum_range_succ _ (m + 1), h2]
      ring_nf
private theorem abs_rayPartialSum_le (ξ : LatticeOneForm) (x : Fin 4 → ℤ) (μ : Fin 4) (k : ℤ) (W : ℝ)
    (h : ∀ t : ℤ, |t| ≤ |k| → |ξ (x + t • basisVector μ, μ)| ≤ W) :
    |rayPartialSum ξ x μ k| ≤ (k.natAbs : ℝ) * W := by
  cases k with
  | ofNat n =>
    simp only [rayPartialSum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ i ∈ Finset.range n, |ξ (x + (i : ℤ) • basisVector μ, μ)| ≤ W := by
      intro i hi
      refine h i ?_
      have := Finset.mem_range.1 hi
      simp only [Int.ofNat_eq_natCast]
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      omega
    have h2 := Finset.sum_le_card_nsmul _ _ _ this
    simpa using h2
  | negSucc n =>
    simp only [rayPartialSum]
    rw [abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ i ∈ Finset.range (n + 1), |ξ (x + (-((i : ℤ) + 1)) • basisVector μ, μ)| ≤ W := by
      intro i hi
      refine h _ ?_
      have := Finset.mem_range.1 hi
      rw [abs_le]
      have h3 : |Int.negSucc n| = (n : ℤ) + 1 := by
        rw [Int.negSucc_eq, abs_neg, abs_of_nonneg (by positivity)]
      rw [h3]
      omega
    have h2 := Finset.sum_le_card_nsmul _ _ _ this
    simpa [Int.natAbs_negSucc] using h2
private def truncateBelow (o : Fin 4 → ℤ) (i : Fin 4) : Fin 4 → ℤ := fun j => if j < i then o j else 0
private def spanningTreeSum (L : ℕ) (ξ : LatticeOneForm) (z : Fin 4 → ℤ) : ℝ :=
  ∑ i, rayPartialSum ξ (blockCentreOnLattice L (latticeBlockOf L z) + truncateBelow (offsetInBlock L z) i) i
    (offsetInBlock L z i)
private theorem spanningTreeSum_add_basis (L : ℕ) (ξ : LatticeOneForm) (x : Fin 4 → ℤ) (μ : Fin 4)
    (hb : latticeBlockOf L (x + basisVector μ) = latticeBlockOf L x)
    (ho : ∀ l, μ < l → offsetInBlock L x l = 0) :
    spanningTreeSum L ξ (x + basisVector μ) - spanningTreeSum L ξ x = ξ (x, μ) := by
  have ho' : offsetInBlock L (x + basisVector μ) = offsetInBlock L x + basisVector μ := by
    simp only [offsetInBlock, hb]
    abel
  have hi : ∀ i j : Fin 4, i ≠ j → (basisVector i) j = 0 := by
    intro i j hij
    simp [basisVector, hij.symm]
  have hup : ∀ i, i ≤ μ → truncateBelow (offsetInBlock L x + basisVector μ) i = truncateBelow (offsetInBlock L x) i := by
    intro i hiμ
    funext j
    by_cases hj : j < i
    · have : μ ≠ j := (lt_of_lt_of_le hj hiμ).ne'
      simp [truncateBelow, hj, hi μ j this]
    · simp [truncateBelow, hj]
  unfold spanningTreeSum
  rw [hb, ho', ← Finset.sum_sub_distrib, Finset.sum_eq_single μ]
  · rw [hup μ le_rfl]
    have hone : (offsetInBlock L x + basisVector μ) μ = offsetInBlock L x μ + 1 := by
      simp [basisVector]
    rw [hone, rayPartialSum_succ_sub]
    congr 2
    funext j
    have hx : x j = blockCentreOnLattice L (latticeBlockOf L x) j + offsetInBlock L x j := by
      simp [offsetInBlock]
    rcases lt_trichotomy j μ with h | h | h
    · simp [truncateBelow, h, hi μ j h.ne', hx]
    · subst h
      simp [truncateBelow, basisVector, hx]
    · simp [truncateBelow, not_lt.2 h.le, hi μ j h.ne, ho j h, hx]
  · intro i _ hne
    rcases lt_or_gt_of_ne hne with h | h
    · rw [hup i h.le]
      have : (offsetInBlock L x + basisVector μ) i = offsetInBlock L x i := by
        simp [hi μ i h.ne']
      rw [this, sub_self]
    · have h1 : offsetInBlock L x i = 0 := ho i h
      have h2 : (offsetInBlock L x + basisVector μ) i = 0 := by
        simp [hi μ i h.ne, h1]
      rw [h1, h2, rayPartialSum_zero, rayPartialSum_zero, sub_self]
  · intro h
    exact absurd (Finset.mem_univ μ) h
private theorem latticeBlockOf_blockCentreOnLattice {L : ℕ} (hL : 0 < L) (y : Fin 4 → ℤ) :
    latticeBlockOf L (blockCentreOnLattice L y) = y := by
  funext i
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have h0 : 0 ≤ ((L : ℤ) - 1) / 2 := by omega
  have h1 : ((L : ℤ) - 1) / 2 < L := by omega
  simp only [latticeBlockOf, blockCentreOnLattice]
  rw [Int.add_comm, Int.add_mul_ediv_left _ _ hL'.ne', Int.ediv_eq_zero_of_lt h0 h1, zero_add]
private theorem spanningTreeSum_blockCentreOnLattice {L : ℕ} (hL : 0 < L) (ξ : LatticeOneForm) (y : Fin 4 → ℤ) :
    spanningTreeSum L ξ (blockCentreOnLattice L y) = 0 := by
  have ho : ∀ i, offsetInBlock L (blockCentreOnLattice L y) i = 0 := by
    intro i
    simp [offsetInBlock, latticeBlockOf_blockCentreOnLattice hL]
  unfold spanningTreeSum
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [ho i, rayPartialSum_zero]
private theorem abs_offsetInBlock_le {L : ℕ} (hL : 0 < L) (z : Fin 4 → ℤ) (i : Fin 4) :
    |offsetInBlock L z i| ≤ L := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have h0 : 0 ≤ ((L : ℤ) - 1) / 2 := by omega
  have h1 : ((L : ℤ) - 1) / 2 < L := by omega
  have e : offsetInBlock L z i = z i - (L : ℤ) * ((z i + ((L : ℤ) - 1) / 2) / (L : ℤ)) := by
    simp [offsetInBlock, blockCentreOnLattice, latticeBlockOf]
  have h2 := Int.mul_ediv_add_emod (z i + ((L : ℤ) - 1) / 2) L
  have h3 := Int.emod_nonneg (z i + ((L : ℤ) - 1) / 2) hL'.ne'
  have h4 := Int.emod_lt_of_pos (z i + ((L : ℤ) - 1) / 2) hL'
  rw [e, abs_le]
  constructor <;> linarith
private theorem abs_spanningTreeSum_le {L : ℕ} (hL : 0 < L) (ξ : LatticeOneForm) (z : Fin 4 → ℤ) (W : ℝ) (hW : 0 ≤ W)
    (h : ∀ (y : Fin 4 → ℤ) (μ : Fin 4), (∀ j, |y j - z j| ≤ 2 * (L : ℤ)) → |ξ (y, μ)| ≤ W) :
    |spanningTreeSum L ξ z| ≤ 4 * (L : ℝ) * W := by
  unfold spanningTreeSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      |rayPartialSum ξ (blockCentreOnLattice L (latticeBlockOf L z) + truncateBelow (offsetInBlock L z) i) i
        (offsetInBlock L z i)| ≤ (L : ℝ) * W := by
    intro i _
    refine (abs_rayPartialSum_le ξ _ i _ W ?_).trans ?_
    · intro t ht
      refine h _ i ?_
      intro j
      have hoi := abs_offsetInBlock_le hL z i
      have hoj := abs_offsetInBlock_le hL z j
      have hz : z j = blockCentreOnLattice L (latticeBlockOf L z) j + offsetInBlock L z j := by
        simp [offsetInBlock]
      have ht' : |t| ≤ L := ht.trans hoi
      have hu : |truncateBelow (offsetInBlock L z) i j - offsetInBlock L z j| ≤ L := by
        by_cases hj : j < i
        · simp [truncateBelow, hj]
        · simpa [truncateBelow, hj] using hoj
      have hs : |t * (basisVector i) j| ≤ L := by
        by_cases hj : i = j
        · subst hj
          simpa [basisVector] using ht'
        · simp [basisVector, Ne.symm hj]
      have e : (blockCentreOnLattice L (latticeBlockOf L z) + truncateBelow (offsetInBlock L z) i
          + t • basisVector i) j - z j
          = (truncateBelow (offsetInBlock L z) i j - offsetInBlock L z j) + t * (basisVector i) j := by
        rw [hz]
        simp
        ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      linarith
    · have h5 : ((offsetInBlock L z i).natAbs : ℝ) ≤ L := by
        have := abs_offsetInBlock_le hL z i
        have h6 : (offsetInBlock L z i).natAbs ≤ L := by
          rw [abs_le] at this
          omega
        exact_mod_cast h6
      exact mul_le_mul_of_nonneg_right h5 hW
  have := Finset.sum_le_card_nsmul _ _ _ hterm
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  calc _ ≤ ((4 : ℕ) : ℝ) * ((L : ℝ) * W) := this
    _ = 4 * (L : ℝ) * W := by push_cast; ring
private theorem supNorm_le_add (y z : Fin 4 → ℤ) (D : ℕ) (h : ∀ j, |y j - z j| ≤ (D : ℤ)) :
    TorusLumps.offsetNorm y ≤ TorusLumps.offsetNorm z + D := by
  unfold TorusLumps.offsetNorm
  refine Finset.sup_le fun i _ => ?_
  have h1 : (z i).natAbs ≤ Finset.univ.sup fun i => (z i).natAbs :=
    Finset.le_sup (f := fun i => (z i).natAbs) (Finset.mem_univ i)
  have h2 := h i
  rw [abs_le] at h2
  omega
private theorem one_add_offsetNormReal_le (y z : Fin 4 → ℤ) (D : ℕ) (h : ∀ j, |y j - z j| ≤ (D : ℤ)) :
    1 + offsetNormReal y ≤ (1 + (D : ℝ)) * (1 + offsetNormReal z) := by
  have h1 : offsetNormReal y ≤ offsetNormReal z + D := by
    unfold offsetNormReal
    exact_mod_cast supNorm_le_add y z D h
  have h2 : 0 ≤ offsetNormReal z := by
    unfold offsetNormReal
    positivity
  have h3 : (0 : ℝ) ≤ D := by positivity
  nlinarith [mul_nonneg h3 h2]
private theorem latticeLineSum_latticeGradient (f : (Fin 4 → ℤ) → ℝ) (z : Fin 4 → ℤ) (l : List PathStep) :
    latticeLineSum (latticeGradient f) z l =
      f (z + (l.map FlatPairing.stepDisplacement).sum) - f z := by
  induction l generalizing z with
  | nil => simp [latticeLineSum]
  | cons st r ih =>
    obtain ⟨i, s⟩ := st
    cases s <;>
      simp [latticeLineSum, ih, FlatPairing.stepDisplacement, latticeGradient, basisVector,
        add_assoc, sub_eq_add_neg] <;> ring
private theorem sum_reversePath (l : List PathStep) :
    ((reversePath l).map FlatPairing.stepDisplacement).sum =
      - (l.map FlatPairing.stepDisplacement).sum := by
  induction l with
  | nil => simp [reversePath]
  | cons st r ih =>
    obtain ⟨i, s⟩ := st
    have e : reversePath ((i, s) :: r) = reversePath r ++ [(i, !s)] := by
      simp [reversePath]
    rw [e, List.map_append, List.sum_append, ih]
    cases s <;> simp [FlatPairing.stepDisplacement, add_comm]
abbrev _root_.YangMills.SharedProofs.p25873 := @sum_reversePath
private theorem sum_bondContour (L : ℕ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    ((bondContour L h π i).map FlatPairing.stepDisplacement).sum = (L : ℤ) • basisVector i := by
  unfold bondContour
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append, sum_reversePath,
    List.map_replicate, List.sum_replicate]
  simp [FlatPairing.stepDisplacement]
theorem latticeTreeGauge : RunningCouplingSlope.latticeTreeGaugeStatement := by
  intro L hL ξ
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hpoly : HasPolynomialGrowth ξ → ∃ C m : ℝ, 0 ≤ C ∧ 0 ≤ m ∧
      ∀ z, |spanningTreeSum L ξ z| ≤ C * (1 + offsetNormReal z) ^ m := by
    rintro ⟨C, m, h⟩
    have hC : 0 ≤ C := by
      have h0 := h (0, 0)
      have h1 : offsetNormReal (0 : Fin 4 → ℤ) = 0 := by simp [offsetNormReal, TorusLumps.offsetNorm]
      simp only [h1, add_zero, Real.one_rpow, mul_one] at h0
      exact (abs_nonneg _).trans h0
    set m' := max m 0 with hm'
    have hm0 : 0 ≤ m' := le_max_right _ _
    refine ⟨4 * (L : ℝ) * (C * (1 + ((2 * L : ℕ) : ℝ)) ^ m'), m', by positivity, hm0, fun z => ?_⟩
    have hn : ∀ y : Fin 4 → ℤ, 0 ≤ offsetNormReal y := fun y => by
      unfold offsetNormReal
      positivity
    have key := abs_spanningTreeSum_le hL0 ξ z (C * (1 + ((2 * L : ℕ) : ℝ)) ^ m' * (1 + offsetNormReal z) ^ m')
      (by have := hn z; positivity) ?_
    · calc _ ≤ _ := key
        _ = _ := by ring
    · intro y μ hy
      refine (h (y, μ)).trans ?_
      have h1 : 1 + offsetNormReal y ≤ (1 + ((2 * L : ℕ) : ℝ)) * (1 + offsetNormReal z) :=
        one_add_offsetNormReal_le y z (2 * L) (fun j => by simpa using hy j)
      have h2 : (1 : ℝ) ≤ 1 + offsetNormReal y := by linarith [hn y]
      have h3 : (1 + offsetNormReal y) ^ m ≤ (1 + offsetNormReal y) ^ m' :=
        Real.rpow_le_rpow_of_exponent_le h2 (le_max_left _ _)
      have h4 : (1 + offsetNormReal y) ^ m' ≤ ((1 + ((2 * L : ℕ) : ℝ)) * (1 + offsetNormReal z)) ^ m' :=
        Real.rpow_le_rpow (by linarith) h1 hm0
      rw [Real.mul_rpow (by positivity) (by linarith [hn z])] at h4
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (h3.trans h4) hC
  refine ⟨fun z => - spanningTreeSum L ξ z, ?_, ?_, ?_, ?_⟩
  · rintro ⟨x, μ⟩ ⟨hb, ho⟩
    have := spanningTreeSum_add_basis L ξ x μ hb ho
    have e : x + Pi.single μ 1 = x + basisVector μ := rfl
    simp only [latticeGradient, e]
    linarith
  · rintro ⟨C, hC⟩
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (0, 0))
    refine ⟨4 * (L : ℝ) * C, fun z => ?_⟩
    rw [abs_neg]
    exact abs_spanningTreeSum_le hL0 ξ z C hC0 (fun y μ _ => hC (y, μ))
  · intro hξ
    obtain ⟨C, m, hC, hm, h⟩ := hpoly hξ
    refine ⟨⟨C, m, fun z => by rw [abs_neg]; exact h z⟩, C * (2 ^ m + 1), m, ?_⟩
    rintro ⟨x, μ⟩
    have hn : 0 ≤ offsetNormReal x := by
      unfold offsetNormReal
      positivity
    have h1 : 1 + offsetNormReal (x + Pi.single μ 1) ≤ (1 + ((1 : ℕ) : ℝ)) * (1 + offsetNormReal x) := by
      refine one_add_offsetNormReal_le _ _ 1 fun j => ?_
      by_cases hj : j = μ
      · subst hj
        simp
      · simp [hj]
    have h2 : (1 + offsetNormReal (x + Pi.single μ 1)) ^ m ≤ 2 ^ m * (1 + offsetNormReal x) ^ m := by
      have h3 : (0 : ℝ) ≤ 1 + offsetNormReal (x + Pi.single μ 1) := by
        have : 0 ≤ offsetNormReal (x + Pi.single μ 1) := by
          unfold offsetNormReal
          positivity
        linarith
      have h4 := Real.rpow_le_rpow h3 h1 hm
      rw [Real.mul_rpow (by positivity) (by linarith)] at h4
      norm_num at h4
      exact h4
    have h5 := h (x + Pi.single μ 1)
    have h6 := h x
    have h7 : |latticeGradient (fun z => - spanningTreeSum L ξ z) (x, μ)|
        ≤ |spanningTreeSum L ξ (x + Pi.single μ 1)| + |spanningTreeSum L ξ x| := by
      simp only [latticeGradient]
      have e : -spanningTreeSum L ξ (x + Pi.single μ 1) - -spanningTreeSum L ξ x
          = spanningTreeSum L ξ x - spanningTreeSum L ξ (x + Pi.single μ 1) := by ring
      have h9 := abs_add_le (spanningTreeSum L ξ x) (- spanningTreeSum L ξ (x + Pi.single μ 1))
      rw [abs_neg] at h9
      rw [e, sub_eq_add_neg]
      linarith
    have h8 : C * (1 + offsetNormReal (x + Pi.single μ 1)) ^ m ≤ C * (2 ^ m * (1 + offsetNormReal x) ^ m) :=
      mul_le_mul_of_nonneg_left h2 hC
    calc _ ≤ _ := h7
      _ ≤ C * (2 ^ m * (1 + offsetNormReal x) ^ m) + C * (1 + offsetNormReal x) ^ m := by linarith
      _ = _ := by ring
  · intro c
    unfold latticeContourAverage
    have hz : ∀ h ∈ centredCube L, ∀ π : Equiv.Perm (Fin 4),
        latticeLineSum (latticeGradient fun z => - spanningTreeSum L ξ z) (blockCentreOnLattice L c.1)
          (bondContour L h π c.2) = 0 := by
      intro h _ π
      rw [latticeLineSum_latticeGradient, sum_bondContour]
      have e : blockCentreOnLattice L c.1 + (L : ℤ) • basisVector c.2
          = blockCentreOnLattice L (c.1 + basisVector c.2) := by
        funext i
        simp [blockCentreOnLattice, mul_add]
      rw [e, spanningTreeSum_blockCentreOnLattice hL0, spanningTreeSum_blockCentreOnLattice hL0]
      simp
    rw [Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun π _ => hz h hh π, mul_zero]
end YangMills.Construction.FlatLinearization
end
