import YangMills.Construction.Lattice.BareBaseSitesOfTheSchemesProof
import YangMills.Construction.Lattice.CubesOfTwoStandardPartitionsProof
import YangMills.Construction.Lattice.GaugeOnBlocksUnderIsometries
import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open TorusMetric
namespace BlockwiseGauge
variable {L m : ℕ}
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : _root_.YangMills.Construction.TorusMetric.torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem meshSize_eq_pow_mul (hL : 0 < L) (a : ℤ) (d : ℕ) :
    meshSize L a = (L : ℝ) ^ d * meshSize L (a + d) := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.meshSize_eq_pow_mul <;> assumption
theorem exists_norm_apply_eq_mul_meshSize (hL : 0 < L) {j : ℤ} (hj : -(m : ℤ) ≤ j)
    {z : FourTorus L m} (hz : z ∈ sublattice L m j) (μ : Fin 4) :
    ∃ P : ℤ, ‖z μ‖ = |(P : ℝ)| * meshSize L j := by
  obtain ⟨n, hn⟩ := hz
  obtain ⟨v, hv, hv'⟩ := exists_coe_eq_abs_eq_norm (z μ)
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = m + j := ⟨(m + j).toNat, by omega⟩
  have hside : torusSide L m = (2 * (L : ℝ) ^ d) * meshSize L j := by
    have h := meshSize_eq_pow_mul hL (-(m : ℤ)) d
    have h1 : -(m : ℤ) + d = j := by omega
    rw [h1] at h
    have h2 : meshSize L (-(m : ℤ)) = (L : ℝ) ^ m := by simp [meshSize]
    rw [h2] at h
    rw [torusSide, h]
    ring
  have h0 : ((v - (n μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
    rw [AddCircle.coe_sub, hv, hn μ, sub_self]
  rw [AddCircle.coe_eq_zero_iff] at h0
  obtain ⟨w, hw⟩ := h0
  refine ⟨n μ + w * (2 * (L : ℤ) ^ d), ?_⟩
  have hvP : v = ((n μ + w * (2 * (L : ℤ) ^ d) : ℤ) : ℝ) * meshSize L j := by
    have hw' : (w : ℝ) * torusSide L m = v - (n μ : ℝ) * meshSize L j := by
      rw [← hw, zsmul_eq_mul]
    rw [hside] at hw'
    push_cast
    linarith
  rw [← hv', hvP, abs_mul, abs_of_pos (meshSize_pos hL j)]
theorem mem_cubeAround_iff (hL : 0 < L) {j : ℤ} (y : Site L m j) (x : FourTorus L m) :
    x ∈ cubeAround y ↔ ∀ μ, ‖x μ - (y : FourTorus L m) μ‖ ≤ meshSize L j / 2 := by
  show _root_.YangMills.Construction.TorusMetric.torusSupNorm _ ≤ _ ↔ _
  rw [_root_.YangMills.Construction.PeriodicLattice.BlockwiseGauge.torusSupNorm_eq_norm,
    pi_norm_le_iff_of_nonneg (by have := meshSize_pos hL j; positivity)]
  rfl
theorem norm_sub_lt_half_meshSize (hL : Odd L) {a B : ℤ} (ha : -(m : ℤ) ≤ a) (haB : a ≤ B)
    {x : FourTorus L m} (hx : x ∈ sublattice L m B) (y : Site L m a) (h : x ∈ cubeAround y)
    (μ : Fin 4) : ‖x μ - (y : FourTorus L m) μ‖ < meshSize L a / 2 := by
  have hL0 : 0 < L := hL.pos
  have hz : x - (y : FourTorus L m) ∈ sublattice L m B :=
    (sublattice L m B).sub_mem hx (sublattice_mono hL0 m haB y.2)
  obtain ⟨P, hP⟩ := exists_norm_apply_eq_mul_meshSize hL0 (ha.trans haB) hz μ
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = B - a := ⟨(B - a).toNat, by omega⟩
  have hs := meshSize_eq_pow_mul hL0 a d
  have h1 : a + (d : ℤ) = B := by omega
  rw [h1] at hs
  have ht := meshSize_pos hL0 B
  have hle := (mem_cubeAround_iff hL0 y x).1 h μ
  have hP' : ‖x μ - (y : FourTorus L m) μ‖ = |(P : ℝ)| * meshSize L B := hP
  rw [hP', hs] at hle
  rw [hP', hs]
  have hle' : 2 * |(P : ℝ)| ≤ (L : ℝ) ^ d := by
    have : (2 * |(P : ℝ)|) * meshSize L B ≤ (L : ℝ) ^ d * meshSize L B := by linarith
    exact le_of_mul_le_mul_right this ht
  have hint : 2 * |P| ≤ (L : ℤ) ^ d := by
    have : ((2 * |P| : ℤ) : ℝ) ≤ (((L : ℤ) ^ d : ℤ) : ℝ) := by
      push_cast
      exact hle'
    exact_mod_cast this
  have hodd : Odd ((L : ℤ) ^ d) := by
    apply Odd.pow
    exact_mod_cast hL
  have hlt : 2 * |P| < (L : ℤ) ^ d := by
    obtain ⟨c, hc⟩ := hodd
    omega
  have hlt' : 2 * |(P : ℝ)| < (L : ℝ) ^ d := by
    have : ((2 * |P| : ℤ) : ℝ) < (((L : ℤ) ^ d : ℤ) : ℝ) := by exact_mod_cast hlt
    push_cast at this
    exact this
  have := mul_lt_mul_of_pos_right hlt' ht
  linarith
theorem eq_of_mem_cubeAround (hL : Odd L) {a B : ℤ} (ha : -(m : ℤ) ≤ a) (haB : a ≤ B)
    {x : FourTorus L m} (hx : x ∈ sublattice L m B) (y y' : Site L m a) (h : x ∈ cubeAround y)
    (h' : x ∈ cubeAround y') : y = y' := by
  have hL0 : 0 < L := hL.pos
  apply Subtype.ext
  funext μ
  have hz : (y : FourTorus L m) - (y' : FourTorus L m) ∈ sublattice L m a :=
    (sublattice L m a).sub_mem y.2 y'.2
  obtain ⟨P, hP⟩ := exists_norm_apply_eq_mul_meshSize hL0 ha hz μ
  have hP' : ‖(y : FourTorus L m) μ - (y' : FourTorus L m) μ‖ = |(P : ℝ)| * meshSize L a := hP
  have h1 := norm_sub_lt_half_meshSize hL ha haB hx y h μ
  have h2 := norm_sub_lt_half_meshSize hL ha haB hx y' h' μ
  have htri : ‖(y : FourTorus L m) μ - (y' : FourTorus L m) μ‖ ≤
      ‖x μ - (y : FourTorus L m) μ‖ + ‖x μ - (y' : FourTorus L m) μ‖ := by
    have : (y : FourTorus L m) μ - (y' : FourTorus L m) μ =
        (x μ - (y' : FourTorus L m) μ) - (x μ - (y : FourTorus L m) μ) := by abel
    rw [this, add_comm]
    exact norm_sub_le _ _
  have ht := meshSize_pos hL0 a
  have hlt : |(P : ℝ)| * meshSize L a < 1 * meshSize L a := by
    rw [← hP']
    linarith
  have hlt' : |(P : ℝ)| < 1 := lt_of_mul_lt_mul_right hlt ht.le
  have hP0 : P = 0 := by
    have : |P| < 1 := by exact_mod_cast hlt'
    exact Int.abs_lt_one_iff.1 this
  rw [hP0] at hP'
  simp only [Int.cast_zero, abs_zero, zero_mul] at hP'
  exact sub_eq_zero.1 (norm_eq_zero.1 hP')
theorem cubeAround_subset (H : CubesUnderRefinement) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) {t t' : ℤ} (ht : -(m : ℤ) ≤ t) (htt : t ≤ t') (z : Site L m t) (y : Site L m t')
    (hy : (y : FourTorus L m) ∈ cubeAround z) : cubeAround y ⊆ cubeAround z := by
  have hc := ((H L m hL.1 hL.2 hm).1 t t' ht htt).1 z
  intro p hp
  rw [hc]
  simp only [mem_iUnion]
  refine ⟨y, ⟨hy, ?_⟩, hp⟩
  have : t + (((t' - t).toNat : ℕ) : ℤ) = t' := by omega
  show (y : FourTorus L m) ∈ (sublattice L m (t + (((t' - t).toNat : ℕ) : ℤ)) : Set (FourTorus L m))
  rw [this]
  exact y.2
theorem mem_cubeAround_of_mem_cubeAround (H : CubesUnderRefinement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {t t' B : ℤ}
    (ht : -(m : ℤ) ≤ t) (htt : t ≤ t') (htB : t' ≤ B) {x : FourTorus L m}
    (hx : x ∈ sublattice L m B) (z : Site L m t) (y : Site L m t')
    (hz : x ∈ cubeAround z) (hy : x ∈ cubeAround y) : (y : FourTorus L m) ∈ cubeAround z := by
  have hc := ((H L m hL.1 hL.2 hm).1 t t' ht htt).1 z
  rw [hc] at hz
  simp only [mem_iUnion] at hz
  obtain ⟨y', hy', hxy'⟩ := hz
  have : y' = y := eq_of_mem_cubeAround hL.1 (ht.trans htt) htB hx y' y hxy' hy
  rw [← this]
  exact hy'.1
theorem mem_of_mem_annulusSites {K k : ℕ} {Ω : ℕ → Set (FourTorus L m)} {j : ℕ} (hj : j ≤ k)
    {y : SiteAtLevel L m K j} (hy : y ∈ annulusSites K k Ω j) : (y : FourTorus L m) ∈ Ω j := by
  unfold annulusSites at hy
  split_ifs at hy with h
  · exact hy.1
  · obtain rfl : j = k := by omega
    exact hy
theorem false_of_lt_of_mem_cubeAround (H : CubesUnderRefinement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {K k e r : ℕ} {i : ℤ}
    {Ω : ℕ → Set (FourTorus L m)} (hseq : IsChainFromIndex K k i Ω)
    (hsep : IsSeparatedChain K e r 0 k Ω) {j j' : ℕ} (hjj : j < j') (hj' : j' ≤ k)
    (y : SiteAtLevel L m K j) (hy : y ∈ annulusSites K k Ω j)
    (y' : SiteAtLevel L m K j') (hy' : y' ∈ annulusSites K k Ω j')
    {x : FourTorus L m} (hx : x ∈ sublattice L m (levelDepth K 0)) (hxy : x ∈ cubeAround y)
    (hxy' : x ∈ cubeAround y') : False := by
  have hdec : ∀ q, q < k → Ω (q + 1) ⊆ Ω q := hseq.2.2.2.1.1
  have hmono : ∀ q, j + 1 ≤ q → q ≤ k → Ω q ⊆ Ω (j + 1) := by
    intro q hq
    induction q, hq using Nat.le_induction with
    | base => exact fun _ => subset_rfl
    | succ q hq ih =>
      intro hqk
      exact (hdec q (by omega)).trans (ih (by omega))
  obtain ⟨C, hC, hΩ⟩ := hsep.1 j' (Nat.zero_le _) (by omega)
  have hy'Ω : (y' : FourTorus L m) ∈ ⋃₀ C := hΩ ▸ mem_of_mem_annulusSites hj' hy'
  obtain ⟨Q, hQ, hyQ⟩ := hy'Ω
  obtain ⟨hc, z, rfl⟩ := hC hQ
  have hsub : cubeAround z ⊆ Ω j' := by
    rw [hΩ]
    exact subset_sUnion_of_mem hQ
  have hzle : scaledCubeIndex K j' e ≤ levelDepth K j' := by
    simp only [scaledCubeIndex]
    omega
  have hxΩ : x ∈ Ω (j + 1) :=
    hmono j' (by omega) hj' (hsub (cubeAround_subset H hL hm hc hzle z y' hyQ hxy'))
  obtain ⟨C', hC', hΩ'⟩ := hsep.1 (j + 1) (Nat.zero_le _) (by omega)
  have hx' : x ∈ ⋃₀ C' := hΩ' ▸ hxΩ
  obtain ⟨Q', hQ', hxQ'⟩ := hx'
  obtain ⟨hc', z', rfl⟩ := hC' hQ'
  have hsub' : cubeAround z' ⊆ Ω (j + 1) := by
    rw [hΩ']
    exact subset_sUnion_of_mem hQ'
  have hz'le : scaledCubeIndex K (j + 1) e ≤ levelDepth K j := by
    simp only [scaledCubeIndex, levelDepth]
    push_cast
    omega
  have hjB : levelDepth K j ≤ levelDepth K 0 := by
    simp only [levelDepth]
    push_cast
    omega
  have hyΩ : (y : FourTorus L m) ∈ Ω (j + 1) :=
    hsub' (mem_cubeAround_of_mem_cubeAround H hL hm hc' hz'le hjB hx z' y hxQ' hxy)
  have hjk : j < k := by omega
  unfold annulusSites at hy
  rw [if_pos hjk] at hy
  exact hy.2 hyΩ
theorem coe_eq_of_mem_refinedBlock (H : CubesUnderRefinement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {K k e r : ℕ} {i : ℤ}
    (hi : -(m : ℤ) ≤ i) {Ω : ℕ → Set (FourTorus L m)} (hseq : IsChainFromIndex K k i Ω)
    (hsep : IsSeparatedChain K e r 0 k Ω) {x : FourTorus L m}
    (hx : x ∈ sublattice L m (levelDepth K 0)) (j₁ j₂ : ℕ) (h₁ : j₁ ≤ k) (h₂ : j₂ ≤ k)
    (y₁ : SiteAtLevel L m K j₁) (y₂ : SiteAtLevel L m K j₂)
    (hy₁ : y₁ ∈ annulusSites K k Ω j₁) (hy₂ : y₂ ∈ annulusSites K k Ω j₂)
    (hx₁ : x ∈ refinedBlock j₁ y₁) (hx₂ : x ∈ refinedBlock j₂ y₂) :
    (y₁ : FourTorus L m) = y₂ := by
  rcases lt_trichotomy j₁ j₂ with h | rfl | h
  · exact (false_of_lt_of_mem_cubeAround H hL hm hseq hsep h h₂ y₁ hy₁ y₂ hy₂ hx hx₁.1 hx₂.1).elim
  · have hk := hseq.index_le_levelDepth
    have ha : -(m : ℤ) ≤ levelDepth K j₁ := by
      simp only [levelDepth] at hk ⊢
      omega
    have hB : levelDepth K j₁ ≤ levelDepth K 0 := by
      simp only [levelDepth]
      push_cast
      omega
    rw [eq_of_mem_cubeAround hL.1 ha hB hx y₁ y₂ hx₁.1 hx₂.1]
  · exact (false_of_lt_of_mem_cubeAround H hL hm hseq hsep h h₁ y₂ hy₂ y₁ hy₁ hx hx₂.1 hx₁.1).elim
theorem toSublattice_congr {j₁ j₂ : ℤ} {y₁ : Site L m j₁} {y₂ : Site L m j₂}
    (h : (y₁ : FourTorus L m) = y₂) (j' : ℤ) : y₁.toSublattice j' = y₂.toSublattice j' := by
  simp only [Site.toSublattice, h]
theorem coe_toSublattice (hL : 0 < L) {j j' : ℤ} (h : j ≤ j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
theorem blockwiseGauge_eq {K k : ℕ} {Ω : ℕ → Set (FourTorus L m)}
    {v : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2} {x : SiteAtLevel L m K 0}
    (D : ∀ (j₁ j₂ : ℕ), j₁ ≤ k → j₂ ≤ k →
      ∀ (y₁ : SiteAtLevel L m K j₁) (y₂ : SiteAtLevel L m K j₂),
      y₁ ∈ annulusSites K k Ω j₁ → y₂ ∈ annulusSites K k Ω j₂ →
      (x : FourTorus L m) ∈ refinedBlock j₁ y₁ → (x : FourTorus L m) ∈ refinedBlock j₂ y₂ →
      (y₁ : FourTorus L m) = y₂)
    {j : ℕ} (hj : j ≤ k) (y : SiteAtLevel L m K j) (hy : y ∈ annulusSites K k Ω j)
    (hx : (x : FourTorus L m) ∈ refinedBlock j y) :
    blockwiseGauge K k Ω v x = v (y.toSublattice (levelDepth K 0)) := by
  have h : ∃ j, j ≤ k ∧ ∃ y ∈ annulusSites K k Ω j, (x : FourTorus L m) ∈ refinedBlock j y :=
    ⟨j, hj, y, hy, hx⟩
  unfold blockwiseGauge
  rw [dif_pos h]
  exact congrArg v (toSublattice_congr (D _ _ h.choose_spec.1 hj _ _
    h.choose_spec.2.choose_spec.1 hy h.choose_spec.2.choose_spec.2 hx) _)
theorem coe_sitePreimage {σ : FourTorus L m ≃ FourTorus L m} {j : ℤ}
    (h : σ '' (sublattice L m j : Set (FourTorus L m)) = sublattice L m j) (y : Site L m j) :
    ((sitePreimage σ y : Site L m j) : FourTorus L m) = σ.symm y := by
  have hy : (y : FourTorus L m) ∈ σ '' (sublattice L m j : Set (FourTorus L m)) := by
    rw [h]
    exact y.2
  obtain ⟨w, hw, he⟩ := hy
  refine Classical.epsilon_spec (p := fun x : Site L m j => (x : FourTorus L m) = σ.symm y)
    ⟨⟨w, hw⟩, ?_⟩
  show w = σ.symm y
  rw [← he, Equiv.symm_apply_apply]
theorem coe_sitePreimage_symm {σ : FourTorus L m ≃ FourTorus L m} {j : ℤ}
    (h : σ '' (sublattice L m j : Set (FourTorus L m)) = sublattice L m j) (y : Site L m j) :
    ((sitePreimage σ.symm y : Site L m j) : FourTorus L m) = σ y := by
  have hy : σ (y : FourTorus L m) ∈ (sublattice L m j : Set (FourTorus L m)) := by
    rw [← h]
    exact mem_image_of_mem _ y.2
  exact Classical.epsilon_spec (p := fun x : Site L m j => (x : FourTorus L m) = σ.symm.symm y)
    ⟨⟨_, hy⟩, rfl⟩
theorem mem_annulusSites_imageChain {σ : FourTorus L m ≃ FourTorus L m} {K k j : ℕ}
    {Ω : ℕ → Set (FourTorus L m)} {y y' : SiteAtLevel L m K j} (h : (y' : FourTorus L m) = σ y) :
    y' ∈ annulusSites K k (imageChain σ Ω) j ↔ y ∈ annulusSites K k Ω j := by
  unfold annulusSites
  split_ifs with hj
  · show (y' : FourTorus L m) ∈ imageChain σ Ω j \ imageChain σ Ω (j + 1) ↔
      (y : FourTorus L m) ∈ Ω j \ Ω (j + 1)
    rw [h]
    simp only [imageChain, mem_sdiff, σ.injective.mem_set_image]
  · show (y' : FourTorus L m) ∈ imageChain σ Ω k ↔ (y : FourTorus L m) ∈ Ω k
    rw [h]
    simp only [imageChain, σ.injective.mem_set_image]
theorem apply_mem_refinedBlock_iff {σ : FourTorus L m ≃ FourTorus L m} {j : ℤ} {n : ℕ}
    (hj : MapsCellsAndCubes σ j) (hn : MapsCellsAndCubes σ (j + n))
    {y y' : Site L m j} (h : (y' : FourTorus L m) = σ y) (p : FourTorus L m) :
    σ p ∈ refinedBlock n y' ↔ p ∈ refinedBlock n y := by
  have h1 : σ '' cubeAround y = cubeAround y' := hj.2.2.2.2.2.2.2.2.1 y y' h
  have h2 : σ '' (sublattice L m (j + n) : Set (FourTorus L m)) = sublattice L m (j + n) := hn.1
  have hc : σ p ∈ cubeAround y' ↔ p ∈ cubeAround y := by
    rw [← h1]
    exact σ.injective.mem_set_image
  have hl : σ p ∈ (sublattice L m (j + n) : Set (FourTorus L m)) ↔
      p ∈ (sublattice L m (j + n) : Set (FourTorus L m)) := by
    conv_lhs => rw [← h2]
    exact σ.injective.mem_set_image
  simp only [refinedBlock, mem_inter_iff, hc, hl]
end BlockwiseGauge
open BlockwiseGauge in
theorem blockwiseGaugeEquivariance_holds
    (hIso : LatticeIsometryGroupActionStatement)
    (hTwo : CubesUnderRefinement) :
    BlockwiseGaugeEquivariance := by
  intro L m hL hm i hi σ hσ K k e r Ω hseq hsep v
  have hL0 : 0 < L := hL.1.pos
  have hC : ∀ j : ℤ, i ≤ j → MapsCellsAndCubes σ j := fun j hj =>
    ((hIso L m i hL hm hi).2.2.2.2 σ hσ j hj).1
  have hk := hseq.index_le_levelDepth
  have hlev : ∀ j, j ≤ k → i ≤ levelDepth K j := by
    intro j hj
    simp only [levelDepth] at hk ⊢
    omega
  have hlevn : ∀ j, j ≤ k → i ≤ levelDepth K j + (j : ℤ) := by
    intro j hj
    simp only [levelDepth] at hk ⊢
    omega
  have hbare : i ≤ levelDepth K 0 := hlev 0 (Nat.zero_le _)
  have hbareLat := (hC _ hbare).1
  have hDΩ := fun (x : SiteAtLevel L m K 0) =>
    coe_eq_of_mem_refinedBlock hTwo hL hm hi hseq hsep (x := (x : FourTorus L m)) x.2
  have hback : ∀ (x : SiteAtLevel L m K 0) (j : ℕ), j ≤ k → ∀ y : SiteAtLevel L m K j,
      y ∈ annulusSites K k (imageChain σ Ω) j →
      (x : FourTorus L m) ∈ refinedBlock j y →
      ∃ y₀ : SiteAtLevel L m K j, (y : FourTorus L m) = σ y₀ ∧ y₀ ∈ annulusSites K k Ω j ∧
        ((sitePreimage σ x : SiteAtLevel L m K 0) : FourTorus L m) ∈ refinedBlock j y₀ := by
    intro x j hj y hy hxy
    have hyc : (y : FourTorus L m) = σ (sitePreimage σ y : SiteAtLevel L m K j) := by
      rw [coe_sitePreimage (hC _ (hlev j hj)).1, Equiv.apply_symm_apply]
    refine ⟨sitePreimage σ y, hyc, (mem_annulusSites_imageChain hyc).1 hy, ?_⟩
    refine (apply_mem_refinedBlock_iff (hC _ (hlev j hj)) (hC _ (hlevn j hj)) hyc _).1 ?_
    rw [coe_sitePreimage hbareLat, Equiv.apply_symm_apply]
    exact hxy
  have hDσ : ∀ (x : SiteAtLevel L m K 0) (j₁ j₂ : ℕ), j₁ ≤ k → j₂ ≤ k →
      ∀ (y₁ : SiteAtLevel L m K j₁) (y₂ : SiteAtLevel L m K j₂),
      y₁ ∈ annulusSites K k (imageChain σ Ω) j₁ →
      y₂ ∈ annulusSites K k (imageChain σ Ω) j₂ →
      (x : FourTorus L m) ∈ refinedBlock j₁ y₁ → (x : FourTorus L m) ∈ refinedBlock j₂ y₂ →
      (y₁ : FourTorus L m) = y₂ := by
    intro x j₁ j₂ h₁ h₂ y₁ y₂ hy₁ hy₂ hx₁ hx₂
    obtain ⟨z₁, he₁, hz₁, hb₁⟩ := hback x j₁ h₁ y₁ hy₁ hx₁
    obtain ⟨z₂, he₂, hz₂, hb₂⟩ := hback x j₂ h₂ y₂ hy₂ hx₂
    have := hDΩ (sitePreimage σ x) j₁ j₂ h₁ h₂ z₁ z₂ hz₁ hz₂ hb₁ hb₂
    rw [he₁, he₂, this]
  funext x
  show blockwiseGauge K k (imageChain σ Ω) (transportSiteFunction σ v) x =
    blockwiseGauge K k Ω v (sitePreimage σ x)
  by_cases hP : ∃ j, j ≤ k ∧ ∃ y ∈ annulusSites K k Ω j,
      ((sitePreimage σ x : SiteAtLevel L m K 0) : FourTorus L m) ∈ refinedBlock j y
  · obtain ⟨j, hj, y, hy, hxy⟩ := hP
    have hyc : ((sitePreimage σ.symm y : SiteAtLevel L m K j) : FourTorus L m) = σ y :=
      coe_sitePreimage_symm (hC _ (hlev j hj)).1 y
    have hy₂ := (mem_annulusSites_imageChain (Ω := Ω) (k := k) hyc).2 hy
    have hx₂ : (x : FourTorus L m) ∈
        refinedBlock j (sitePreimage σ.symm y : SiteAtLevel L m K j) := by
      have := (apply_mem_refinedBlock_iff (hC _ (hlev j hj)) (hC _ (hlevn j hj)) hyc _).2 hxy
      rwa [coe_sitePreimage hbareLat, Equiv.apply_symm_apply] at this
    rw [blockwiseGauge_eq (hDσ x) hj _ hy₂ hx₂, blockwiseGauge_eq (hDΩ _) hj y hy hxy]
    show v (sitePreimage σ _) = _
    congr 1
    apply Subtype.ext
    have hjB : levelDepth K j ≤ levelDepth K 0 := by
      simp only [levelDepth]
      push_cast
      omega
    rw [coe_sitePreimage hbareLat, coe_toSublattice hL0 hjB, coe_toSublattice hL0 hjB, hyc,
      Equiv.symm_apply_apply]
  · have hQ : ¬∃ j, j ≤ k ∧ ∃ y ∈ annulusSites K k (imageChain σ Ω) j,
        (x : FourTorus L m) ∈ refinedBlock j y := by
      rintro ⟨j, hj, y, hy, hxy⟩
      obtain ⟨y₀, -, hy₀, hb⟩ := hback x j hj y hy hxy
      exact hP ⟨j, hj, y₀, hy₀, hb⟩
    unfold blockwiseGauge
    rw [dif_neg hP, dif_neg hQ]
end YangMills.Construction.PeriodicLattice
