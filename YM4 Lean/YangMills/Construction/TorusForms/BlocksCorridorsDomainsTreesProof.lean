import YangMills.Construction.PeriodicLattice.TorusCurlAverageCoercivityProof
import YangMills.Construction.SeparatedSequences.LowerBoundOnTheContoursAtEveryLevelProof
import YangMills.Construction.TorusForms.AveragesOnUnionsOfBlocksProof
import Mathlib
noncomputable section
namespace YangMills.Construction.BlockSpin
open YangMills.Construction.Lattice
namespace BlockGeometry
section Grid
variable {d : ℕ} {ℓ : Fin d → ℝ} {ε : ℝ}
theorem gridPoint_zero : gridPoint ℓ ε 0 = 0 := by
  apply Subtype.ext
  show torusMk ℓ _ = 0
  have : (fun μ : Fin d => (((0 : Fin d → ℤ) μ : ℤ) : ℝ) * ε) = 0 := by
    funext μ
    simp
  rw [this, map_zero]
theorem gridPoint_add (a b : Fin d → ℤ) :
    gridPoint ℓ ε (a + b) = gridPoint ℓ ε a + gridPoint ℓ ε b := by apply _root_.YangMills.Construction.SeparatedClasses.TreeLowerBound.gridPoint_add <;> assumption
theorem gridPoint_neg (a : Fin d → ℤ) : gridPoint ℓ ε (-a) = -gridPoint ℓ ε a := by
  have h := gridPoint_add (ℓ := ℓ) (ε := ε) (-a) a
  rw [neg_add_cancel, gridPoint_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm
theorem gridPoint_sub (a b : Fin d → ℤ) :
    gridPoint ℓ ε (a - b) = gridPoint ℓ ε a - gridPoint ℓ ε b := by
  rw [sub_eq_add_neg, gridPoint_add, gridPoint_neg, sub_eq_add_neg]
theorem gridPoint_single (μ : Fin d) : gridPoint ℓ ε (Pi.single μ 1) = latticeStep ℓ ε μ := by
  apply Subtype.ext
  show torusMk ℓ _ = torusMk ℓ _
  congr 1
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [basisVector]
  · simp [basisVector, h]
theorem exists_eq_gridPoint (x : LatticeSite ℓ ε) : ∃ a : Fin d → ℤ, x = gridPoint ℓ ε a := by
  obtain ⟨_, u, hu, rfl⟩ := x
  have hm : ∀ μ, ∃ m : ℤ, m • ε = u μ := fun μ =>
    AddSubgroup.mem_zmultiples_iff.mp ((AddSubgroup.mem_pi _).mp hu μ (Set.mem_univ μ))
  choose m hm using hm
  refine ⟨m, Subtype.ext ?_⟩
  show torusMk ℓ _ = torusMk ℓ _
  congr 1
  funext μ
  rw [← hm μ, zsmul_eq_mul]
theorem gridPoint_eq_gridPoint_iff (hε : ε ≠ 0) (R : Fin d → ℤ) (hR : ∀ μ, ℓ μ = R μ * ε)
    (a b : Fin d → ℤ) :
    gridPoint ℓ ε a = gridPoint ℓ ε b ↔ ∀ μ, R μ ∣ a μ - b μ := by
  rw [Subtype.ext_iff]
  show torusMk ℓ _ = torusMk ℓ _ ↔ _
  rw [torusMk_eq_torusMk_iff]
  constructor
  · intro hmem μ
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
      ((AddSubgroup.mem_pi _).mp hmem μ (Set.mem_univ μ))
    refine ⟨k, ?_⟩
    have h1 : (k : ℝ) * ℓ μ = ((a μ : ℝ) - b μ) * ε := by
      have h2 := hk
      rw [zsmul_eq_mul] at h2
      rw [h2]
      simp only [Pi.sub_apply]
      ring
    rw [hR μ] at h1
    have h3 : ((k : ℝ) * R μ) * ε = ((a μ : ℝ) - b μ) * ε := by linarith
    have h4 := mul_right_cancel₀ hε h3
    have h5 : ((a μ - b μ : ℤ) : ℝ) = ((R μ * k : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h5
  · intro hdvd
    refine (AddSubgroup.mem_pi _).mpr fun μ _ => AddSubgroup.mem_zmultiples_iff.mpr ?_
    obtain ⟨k, hk⟩ := hdvd μ
    refine ⟨k, ?_⟩
    have h5 : ((a μ : ℝ) - b μ) = (R μ : ℝ) * k := by exact_mod_cast hk
    rw [zsmul_eq_mul, hR μ]
    simp only [Pi.sub_apply]
    have : (a μ : ℝ) * ε - (b μ : ℝ) * ε = ((a μ : ℝ) - b μ) * ε := by ring
    rw [this, h5]
    ring
end Grid
section Blocks
variable (S : LatticeParameters) {ℓ : Fin S.d → ℝ} {ε ε' : ℝ} {n : ℕ}
theorem blockFactor_pos : (0 : ℤ) < (S.L : ℤ) := by
  have := S.two_le_L
  omega
theorem blockOffset_add_one_le (n : ℕ) : (blockOffset S n : ℤ) + 1 ≤ (S.L : ℤ) ^ n := by
  have hL := S.two_le_L
  have ho := S.offset_lt
  have hpos : 0 < S.L ^ n := Nat.pow_pos (by omega)
  have h := blockOffset_mul S n
  have h1 : blockOffset S n * (S.L - 1) ≤ (S.L ^ n - 1) * (S.L - 1) := by
    rw [h, mul_comm]
    exact Nat.mul_le_mul_left _ (by omega)
  have h2 := Nat.le_of_mul_le_mul_right h1 (by omega)
  have h3 : blockOffset S n + 1 ≤ S.L ^ n := by omega
  exact_mod_cast h3
theorem inBlockIndexRange_zero (n : ℕ) : InBlockIndexRange S n 0 := by
  intro μ
  have := blockOffset_add_one_le S n
  simp only [Pi.zero_apply]
  constructor <;> omega
variable {S}
theorem spacing_ne_zero [hε : IsCommensurateSpacing ℓ ε] : ε ≠ 0 := hε.spacing_pos.ne'
theorem coarseSpacing_ne_zero [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S n ℓ ε ε') :
    ε' ≠ 0 := by
  have := h.isCommensurateSpacing
  exact spacing_ne_zero (ℓ := ℓ)
theorem exists_coarse_ratios [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S n ℓ ε ε') :
    ∃ N : Fin S.d → ℤ, (∀ μ, 2 ≤ N μ) ∧ ∀ μ, ℓ μ = N μ * ε' := by
  have hne := coarseSpacing_ne_zero h
  choose N hN hr using h.ratio_mem
  refine ⟨fun μ => (N μ : ℤ), fun μ => by
    show (2 : ℤ) ≤ (N μ : ℤ)
    exact_mod_cast hN μ, fun μ => ?_⟩
  have := hr μ
  field_simp at this
  push_cast
  linarith
theorem fine_ratio_eq (h : IsBlockSpacing S n ℓ ε ε') {N : Fin S.d → ℤ}
    (hN : ∀ μ, ℓ μ = N μ * ε') (μ : Fin S.d) :
    ℓ μ = (N μ * (S.L : ℤ) ^ n : ℤ) * ε := by
  rw [hN μ, h.spacing_eq]
  push_cast
  ring
theorem toFineSite_add (h : IsBlockSpacing S n ℓ ε ε') (y y' : LatticeSite ℓ ε') :
    h.toFineSite (y + y') = h.toFineSite y + h.toFineSite y' := rfl
theorem toFineSite_gridPoint (h : IsBlockSpacing S n ℓ ε ε') (b : Fin S.d → ℤ) :
    h.toFineSite (gridPoint ℓ ε' b) = gridPoint ℓ ε (fun μ => (S.L : ℤ) ^ n * b μ) := by
  apply Subtype.ext
  show torusMk ℓ _ = torusMk ℓ _
  congr 1
  funext μ
  rw [h.spacing_eq]
  push_cast
  ring
theorem toFineSite_latticeStep (h : IsBlockSpacing S n ℓ ε ε') (μ : Fin S.d) :
    h.toFineSite (latticeStep ℓ ε' μ) = gridPoint ℓ ε (Pi.single μ ((S.L : ℤ) ^ n)) := by
  rw [← gridPoint_single, toFineSite_gridPoint]
  congr 1
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp
  · simp [hν]
theorem mem_blockOf_iff (h : IsBlockSpacing S n ℓ ε ε') (x : LatticeSite ℓ ε)
    (y : LatticeSite ℓ ε') :
    x ∈ blockOf S n ε y ↔
      ∃ σ, InBlockIndexRange S n σ ∧ x = h.toFineSite y + gridPoint ℓ ε σ := by
  constructor
  · rintro ⟨σ, hσ, hx⟩
    exact ⟨σ, hσ, Subtype.ext hx⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, rfl⟩
theorem exists_block_decomposition [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S n ℓ ε ε')
    (x : LatticeSite ℓ ε) :
    ∃ (y : LatticeSite ℓ ε') (σ : Fin S.d → ℤ), InBlockIndexRange S n σ ∧
      x = h.toFineSite y + gridPoint ℓ ε σ := by
  obtain ⟨a, rfl⟩ := exists_eq_gridPoint x
  set M : ℤ := (S.L : ℤ) ^ n with hM
  set o : ℤ := (blockOffset S n : ℤ) with ho
  have hMpos : 0 < M := pow_pos (blockFactor_pos S) n
  refine ⟨gridPoint ℓ ε' fun μ => (a μ + o) / M, fun μ => (a μ + o) % M - o, fun μ => ?_, ?_⟩
  · have h0 := Int.emod_nonneg (a μ + o) hMpos.ne'
    have h1 := Int.emod_lt_of_pos (a μ + o) hMpos
    show -o ≤ (a μ + o) % M - o ∧ (a μ + o) % M - o ≤ M - 1 - o
    constructor <;> omega
  · rw [toFineSite_gridPoint, ← gridPoint_add]
    congr 1
    funext μ
    have := Int.mul_ediv_add_emod (a μ + o) M
    simp only [Pi.add_apply]
    rw [← hM]
    omega
theorem block_decomposition_unique [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S n ℓ ε ε')
    {y₁ y₂ : LatticeSite ℓ ε'} {σ₁ σ₂ : Fin S.d → ℤ} (h₁ : InBlockIndexRange S n σ₁)
    (h₂ : InBlockIndexRange S n σ₂)
    (he : h.toFineSite y₁ + gridPoint ℓ ε σ₁ = h.toFineSite y₂ + gridPoint ℓ ε σ₂) :
    y₁ = y₂ ∧ σ₁ = σ₂ := by
  obtain ⟨N, hN2, hN⟩ := exists_coarse_ratios h
  obtain ⟨b₁, rfl⟩ := exists_eq_gridPoint y₁
  obtain ⟨b₂, rfl⟩ := exists_eq_gridPoint y₂
  rw [toFineSite_gridPoint, toFineSite_gridPoint, ← gridPoint_add, ← gridPoint_add,
    gridPoint_eq_gridPoint_iff (spacing_ne_zero (ℓ := ℓ)) _ (fine_ratio_eq h hN)] at he
  set M : ℤ := (S.L : ℤ) ^ n with hM
  have hMpos : 0 < M := pow_pos (blockFactor_pos S) n
  have hσ : ∀ μ, σ₁ μ = σ₂ μ := by
    intro μ
    have hd : M ∣ (σ₁ μ - σ₂ μ) := by
      obtain ⟨k, hk⟩ := he μ
      simp only [Pi.add_apply] at hk
      refine ⟨N μ * k - b₁ μ + b₂ μ, ?_⟩
      have : σ₁ μ - σ₂ μ = N μ * M * k - M * b₁ μ + M * b₂ μ := by linarith
      rw [this]
      ring
    have habs : |σ₁ μ - σ₂ μ| < M := by
      have a1 := h₁ μ
      have a2 := h₂ μ
      rw [abs_lt]
      constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hd habs
    omega
  have hσ' : σ₁ = σ₂ := funext hσ
  refine ⟨?_, hσ'⟩
  rw [gridPoint_eq_gridPoint_iff (coarseSpacing_ne_zero h) N hN]
  intro μ
  obtain ⟨k, hk⟩ := he μ
  simp only [Pi.add_apply, hσ μ] at hk
  refine ⟨k, ?_⟩
  have h3 : M * (b₁ μ - b₂ μ) = M * (N μ * k) := by linarith
  exact mul_left_cancel₀ hMpos.ne' h3
theorem blockOf_unique [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S n ℓ ε ε')
    {x : LatticeSite ℓ ε} {y₁ y₂ : LatticeSite ℓ ε'} (h₁ : x ∈ blockOf S n ε y₁)
    (h₂ : x ∈ blockOf S n ε y₂) : y₁ = y₂ := by
  obtain ⟨σ₁, r₁, e₁⟩ := (mem_blockOf_iff h _ _).mp h₁
  obtain ⟨σ₂, r₂, e₂⟩ := (mem_blockOf_iff h _ _).mp h₂
  exact (block_decomposition_unique h r₁ r₂ (e₁.symm.trans e₂)).1
theorem toFineSite_mem_blockOf (h : IsBlockSpacing S n ℓ ε ε') (y : LatticeSite ℓ ε') :
    h.toFineSite y ∈ blockOf S n ε y :=
  (mem_blockOf_iff h _ _).mpr
    ⟨0, inBlockIndexRange_zero S n, by rw [gridPoint_zero, add_zero]⟩
theorem add_latticeStep_ne [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S n ℓ ε ε')
    (y : LatticeSite ℓ ε') (μ : Fin S.d) : y + latticeStep ℓ ε' μ ≠ y := by
  obtain ⟨N, hN2, hN⟩ := exists_coarse_ratios h
  intro he
  have h0 : latticeStep ℓ ε' μ = 0 := by simpa using he
  rw [← gridPoint_single, ← gridPoint_zero (ℓ := ℓ) (ε := ε'),
    gridPoint_eq_gridPoint_iff (coarseSpacing_ne_zero h) N hN] at h0
  have h1 := h0 μ
  simp only [Pi.single_eq_same, Pi.zero_apply, sub_zero] at h1
  have := Int.le_of_dvd one_pos h1
  have := hN2 μ
  omega
end Blocks
section Properties
variable {S : LatticeParameters} {ℓ : Fin S.d → ℝ} {ε ε' : ℝ} {n : ℕ}
theorem uniqueBlockDecomposition [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S n ℓ ε ε') :
    UniqueBlockDecomposition S h := by
  intro x
  obtain ⟨y, σ, hσ, hx⟩ := exists_block_decomposition h x
  refine ⟨(y, σ), ⟨hσ, hx⟩, ?_⟩
  rintro ⟨y', σ'⟩ ⟨hσ', hx'⟩
  dsimp only at hσ' hx'
  obtain ⟨e1, e2⟩ := block_decomposition_unique h hσ' hσ (hx'.symm.trans hx)
  rw [e1, e2]
theorem card_blockIndexRange (S : LatticeParameters) (n : ℕ) (o : ℤ) :
    (Fintype.piFinset fun _ : Fin S.d => Finset.Icc (-o) ((S.L : ℤ) ^ n - 1 - o)).card =
      S.L ^ (n * S.d) := by
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have : ((S.L : ℤ) ^ n - 1 - o + 1 - -o).toNat = S.L ^ n := by
    have : (S.L : ℤ) ^ n - 1 - o + 1 - -o = ((S.L ^ n : ℕ) : ℤ) := by
      push_cast
      ring
    rw [this, Int.toNat_natCast]
  rw [this, pow_mul]
theorem blocksPartitionLattice [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S n ℓ ε ε') :
    BlocksPartitionLattice S n ℓ ε ε' := by
  constructor
  · intro x
    obtain ⟨y, σ, hσ, hx⟩ := exists_block_decomposition h x
    have hm : x ∈ blockOf S n ε y := (mem_blockOf_iff h _ _).mpr ⟨σ, hσ, hx⟩
    exact ⟨y, hm, fun y' hy' => blockOf_unique h hy' hm⟩
  · intro y
    set o : ℤ := (blockOffset S n : ℤ) with ho
    set F := Fintype.piFinset fun _ : Fin S.d => Finset.Icc (-o) ((S.L : ℤ) ^ n - 1 - o)
      with hF
    have hmem : ∀ σ, σ ∈ F ↔ InBlockIndexRange S n σ := by
      intro σ
      simp only [hF, Fintype.mem_piFinset, Finset.mem_Icc]
      rfl
    have himg : blockOf S n ε y =
        (fun σ => h.toFineSite y + gridPoint ℓ ε σ) '' (F : Set _) := by
      ext x
      rw [mem_blockOf_iff h]
      constructor
      · rintro ⟨σ, hσ, rfl⟩
        exact ⟨σ, (hmem σ).mpr hσ, rfl⟩
      · rintro ⟨σ, hσ, rfl⟩
        exact ⟨σ, (hmem σ).mp hσ, rfl⟩
    have hinj : Set.InjOn (fun σ => h.toFineSite y + gridPoint ℓ ε σ) (F : Set _) := by
      intro σ hσ τ hτ he
      exact (block_decomposition_unique h ((hmem σ).mp hσ) ((hmem τ).mp hτ) he).2
    rw [himg, hinj.ncard_image, Set.ncard_coe_finset, hF, card_blockIndexRange]
theorem blockTranslate [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S n ℓ ε ε') :
    BlockTranslate S h := by
  intro y μ
  constructor
  · ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨σ, hσ, rfl⟩ := (mem_blockOf_iff h _ _).mp hz
      refine (mem_blockOf_iff h _ _).mpr ⟨σ, hσ, ?_⟩
      dsimp only
      rw [toFineSite_add]
      abel
    · intro hx
      obtain ⟨σ, hσ, rfl⟩ := (mem_blockOf_iff h _ _).mp hx
      refine ⟨h.toFineSite y + gridPoint ℓ ε σ, (mem_blockOf_iff h _ _).mpr ⟨σ, hσ, rfl⟩, ?_⟩
      dsimp only
      rw [toFineSite_add]
      abel
  · intro he
    have h1 := toFineSite_mem_blockOf h y
    rw [← he] at h1
    exact add_latticeStep_ne h y μ (blockOf_unique h h1 (toFineSite_mem_blockOf h y))
theorem add_single_apply_self {d : ℕ} (σ : Fin d → ℤ) (μ : Fin d) (c : ℤ) :
    (σ + Pi.single μ c : Fin d → ℤ) μ = σ μ + c := by simp
theorem add_single_apply_of_ne {d : ℕ} (σ : Fin d → ℤ) {μ κ : Fin d} (c : ℤ) (hκ : κ ≠ μ) :
    (σ + Pi.single μ c : Fin d → ℤ) κ = σ κ := by simp [hκ]
theorem inBlockIndexRange_add_single {σ : Fin S.d → ℤ} (hσ : InBlockIndexRange S n σ)
    {μ : Fin S.d} {c : ℤ} (h1 : -(blockOffset S n : ℤ) ≤ σ μ + c)
    (h2 : σ μ + c ≤ (S.L : ℤ) ^ n - 1 - blockOffset S n) :
    InBlockIndexRange S n (σ + Pi.single μ c) := by apply _root_.YangMills.Construction.BlockSpin.BlockUnions.inBlockIndexRange_add_single <;> assumption
theorem gridPoint_add_latticeStep (h : IsBlockSpacing S n ℓ ε ε') (y : LatticeSite ℓ ε')
    (σ : Fin S.d → ℤ) (μ : Fin S.d) :
    h.toFineSite y + gridPoint ℓ ε σ + latticeStep ℓ ε μ =
      h.toFineSite y + gridPoint ℓ ε (σ + Pi.single μ 1) := by
  rw [gridPoint_add, gridPoint_single, add_assoc]
theorem gridPoint_add_latticeStep_top (h : IsBlockSpacing S n ℓ ε ε') (y : LatticeSite ℓ ε')
    (σ : Fin S.d → ℤ) (μ : Fin S.d) :
    h.toFineSite y + gridPoint ℓ ε σ + latticeStep ℓ ε μ =
      h.toFineSite (y + latticeStep ℓ ε' μ) +
        gridPoint ℓ ε (σ - Pi.single μ ((S.L : ℤ) ^ n - 1)) := by
  have hs : (Pi.single μ ((S.L : ℤ) ^ n) : Fin S.d → ℤ) =
      Pi.single μ ((S.L : ℤ) ^ n - 1) + Pi.single μ 1 := by
    rw [← Pi.single_add]
    congr 1
    ring
  rw [toFineSite_add, toFineSite_latticeStep, hs, gridPoint_sub, gridPoint_add, gridPoint_single]
  abel
theorem inBlockIndexRange_sub_single_top {σ : Fin S.d → ℤ} (hσ : InBlockIndexRange S n σ)
    {μ : Fin S.d} (he : σ μ = (S.L : ℤ) ^ n - 1 - blockOffset S n) :
    InBlockIndexRange S n (σ - Pi.single μ ((S.L : ℤ) ^ n - 1)) := by
  have hlo := blockOffset_add_one_le S n
  rw [sub_eq_add_neg, ← Pi.single_neg]
  exact inBlockIndexRange_add_single hσ (by omega) (by omega)
theorem blockNeighborSite [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S n ℓ ε ε') :
    BlockNeighborSite S h := by
  intro y σ hσ μ
  refine ⟨fun hlt => ?_, fun he => ⟨gridPoint_add_latticeStep_top h y σ μ, ?_⟩⟩
  · have := hσ μ
    exact (mem_blockOf_iff h _ _).mpr ⟨σ + Pi.single μ 1,
      inBlockIndexRange_add_single hσ (by omega) (by omega), gridPoint_add_latticeStep h y σ μ⟩
  · exact (mem_blockOf_iff h _ _).mpr
      ⟨_, inBlockIndexRange_sub_single_top hσ he, gridPoint_add_latticeStep_top h y σ μ⟩
theorem blockOffset_add (S : LatticeParameters) (n n' : ℕ) :
    (blockOffset S (n + n') : ℤ) =
      (S.L : ℤ) ^ n * blockOffset S n' + blockOffset S n := by
  have hL := S.two_le_L
  have cast : ∀ m : ℕ, (blockOffset S m : ℤ) * ((S.L : ℤ) - 1) =
      (S.offset : ℤ) * ((S.L : ℤ) ^ m - 1) := by
    intro m
    have h1 := blockOffset_mul S m
    have hp : 1 ≤ S.L ^ m := Nat.pow_pos (by omega)
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h1
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub hp] at h2
    push_cast at h2
    exact h2
  have hne : (S.L : ℤ) - 1 ≠ 0 := by omega
  apply mul_right_cancel₀ hne
  have e1 := cast (n + n')
  have e2 := cast n'
  have e3 := cast n
  rw [pow_add] at e1
  linear_combination e1 + (S.L : ℤ) ^ n * (-e2) - e3
theorem nestedBlocks [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S n ℓ ε ε') :
    NestedBlocks S n ℓ ε ε' := by
  intro n' ε'' h'' y'
  have h' : IsBlockSpacing S n' ℓ ε' ε'' :=
    ⟨by rw [h''.spacing_eq, h.spacing_eq, pow_add]; ring, h''.ratio_mem⟩
  have hfine : ∀ w : LatticeSite ℓ ε'', h.toFineSite (h'.toFineSite w) = h''.toFineSite w :=
    fun _ => rfl
  set M : ℤ := (S.L : ℤ) ^ n with hM
  set M' : ℤ := (S.L : ℤ) ^ n' with hM'
  set o : ℤ := (blockOffset S n : ℤ) with ho
  set o' : ℤ := (blockOffset S n' : ℤ) with ho'
  have hMpos : 0 < M := pow_pos (blockFactor_pos S) n
  have hMM : (S.L : ℤ) ^ (n + n') = M * M' := pow_add _ _ _
  have hoo : (blockOffset S (n + n') : ℤ) = M * o' + o := blockOffset_add S n n'
  constructor
  · ext x
    simp only [blockUnion, Set.mem_iUnion, exists_prop]
    constructor
    · intro hx
      obtain ⟨σ, hσ, rfl⟩ := (mem_blockOf_iff h'' _ _).mp hx
      refine ⟨h'.toFineSite y' + gridPoint ℓ ε' fun μ => (σ μ + o) / M, ?_, ?_⟩
      · refine (mem_blockOf_iff h' _ _).mpr ⟨_, fun μ => ?_, rfl⟩
        have a := hσ μ
        rw [hMM, hoo] at a
        constructor
        · refine Int.le_ediv_of_mul_le hMpos ?_
          nlinarith [a.1]
        · have : (σ μ + o) / M < M' - o' := by
            refine Int.ediv_lt_of_lt_mul hMpos ?_
            nlinarith [a.2]
          rw [← hM', ← ho']
          omega
      · refine (mem_blockOf_iff h _ _).mpr ⟨fun μ => (σ μ + o) % M - o, fun μ => ?_, ?_⟩
        · have h0 := Int.emod_nonneg (σ μ + o) hMpos.ne'
          have h1 := Int.emod_lt_of_pos (σ μ + o) hMpos
          show -o ≤ (σ μ + o) % M - o ∧ (σ μ + o) % M - o ≤ M - 1 - o
          constructor <;> omega
        · rw [toFineSite_add, hfine, toFineSite_gridPoint, add_assoc, ← gridPoint_add]
          congr 2
          funext μ
          have := Int.mul_ediv_add_emod (σ μ + o) M
          simp only [Pi.add_apply]
          rw [← hM]
          omega
    · rintro ⟨y, hy, hx⟩
      obtain ⟨τ, hτ, rfl⟩ := (mem_blockOf_iff h' _ _).mp hy
      obtain ⟨ρ, hρ, rfl⟩ := (mem_blockOf_iff h _ _).mp hx
      refine (mem_blockOf_iff h'' _ _).mpr ⟨fun μ => M * τ μ + ρ μ, fun μ => ?_, ?_⟩
      · have a := hτ μ
        have b := hρ μ
        rw [hMM, hoo]
        rw [← hM', ← ho'] at a
        rw [← hM, ← ho] at b
        constructor
        · nlinarith [a.1, b.1]
        · nlinarith [a.2, b.2]
      · rw [toFineSite_add, hfine, toFineSite_gridPoint, add_assoc, ← gridPoint_add]
        rfl
  · intro y₁ _ y₂ _ hne
    exact Set.disjoint_left.mpr fun x h₁ h₂ => hne (blockOf_unique h h₁ h₂)
theorem linkInside_iff (b : Link ℓ ε) (X : Set (LatticeSite ℓ ε)) :
    LinkInside S b X ↔ b.1 ∈ X ∧ b.head ∈ X := by
  simp [LinkInside, Link.ends, Set.insert_subset_iff]
theorem linkInBlockOrCorridor [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S n ℓ ε ε') :
    LinkInBlockOrCorridor S n ℓ ε ε' := by
  constructor
  · rintro ⟨x, μ⟩
    obtain ⟨y, σ, hσ, hx⟩ := exists_block_decomposition h x
    have hxy : x ∈ blockOf S n ε y := (mem_blockOf_iff h _ _).mpr ⟨σ, hσ, hx⟩
    by_cases hlt : σ μ < (S.L : ℤ) ^ n - 1 - blockOffset S n
    · have hhead : Link.head (x, μ) ∈ blockOf S n ε y := by
        have := (blockNeighborSite h y σ hσ μ).1 hlt
        rw [← hx] at this
        exact this
      refine Or.inl ⟨⟨y, (linkInside_iff _ _).mpr ⟨hxy, hhead⟩, ?_⟩, ?_⟩
      · intro y' hy'
        exact blockOf_unique h ((linkInside_iff _ _).mp hy').1 hxy
      · rintro c ⟨_, h1, h2⟩
        have e1 : c.1 = y := blockOf_unique h h1 hxy
        have e2 : c.head = y := blockOf_unique h h2 hhead
        exact add_latticeStep_ne h c.1 c.2 (e2.trans e1.symm)
    · have he : σ μ = (S.L : ℤ) ^ n - 1 - blockOffset S n := by
        have := hσ μ
        omega
      have hhead : Link.head (x, μ) ∈ blockOf S n ε (y + latticeStep ℓ ε' μ) := by
        have := ((blockNeighborSite h y σ hσ μ).2 he).2
        rw [← hx] at this
        exact this
      refine Or.inr ⟨⟨(y, μ), ⟨rfl, hxy, hhead⟩, ?_⟩, ?_⟩
      · rintro ⟨y', μ'⟩ ⟨h0, h1, _⟩
        have e1 : y' = y := blockOf_unique h h1 hxy
        dsimp only at h0
        rw [e1, h0]
      · intro y' hy'
        obtain ⟨h1, h2⟩ := (linkInside_iff _ _).mp hy'
        have e1 : y' = y := blockOf_unique h h1 hxy
        have e2 : y' = y + latticeStep ℓ ε' μ := blockOf_unique h h2 hhead
        exact add_latticeStep_ne h y μ (e2.symm.trans e1)
  · rintro c b ⟨_, h1, h2⟩
    exact Or.inl ⟨h1, h2⟩
end Properties
section Plaquettes
variable {S : LatticeParameters} {ℓ : Fin S.d → ℝ} {ε ε' : ℝ} {n : ℕ}
theorem single_one_injective {d : ℕ} {a b : Fin d}
    (h : (Pi.single a 1 : Fin d → ℤ) = Pi.single b 1) : a = b := by
  by_contra hne
  have h1 := congrFun h a
  simp [hne] at h1
theorem single_one_apply_cases {d : ℕ} (a κ : Fin d) :
    (Pi.single a 1 : Fin d → ℤ) κ = 0 ∨ (Pi.single a 1 : Fin d → ℤ) κ = 1 := by apply _root_.YangMills.Construction.PeriodicLattice.TorusCurlAverage.single_apply_zero_or_one <;> assumption
theorem small_combination_eq {i₀ j₀ i₁ j₁ u v f R : ℤ} (hi₀ : i₀ = 0 ∨ i₀ = 1)
    (hj₀ : j₀ = 0 ∨ j₀ = 1) (hi₁ : i₁ = 0 ∨ i₁ = 1) (hj₁ : j₁ = 0 ∨ j₁ = 1)
    (huv : (u = 0 ∧ v = 0) ∨ (u = 1 ∧ v = 0) ∨ (u = 0 ∧ v = 1)) (hf : f = 0 ∨ f = 1)
    (hR : 3 ≤ R) (hd : R ∣ (i₀ * u + j₀ * v + f) - (i₁ * u + j₁ * v)) :
    i₀ * u + j₀ * v + f = i₁ * u + j₁ * v := by
  have hlt : |(i₀ * u + j₀ * v + f) - (i₁ * u + j₁ * v)| < R := by
    rw [abs_lt]
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [mul_zero, mul_one, add_zero, zero_add] <;> constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  omega
theorem plaquette_eq_of_vertices {d : ℕ} {ℓ : Fin d → ℝ} {ε : ℝ} (hε : ε ≠ 0) (R : Fin d → ℤ)
    (hR : ∀ κ, ℓ κ = R κ * ε) (h3 : ∀ κ, 3 ≤ R κ) {p : LatticePlaquette ℓ ε}
    {x : LatticeSite ℓ ε} {μ ν : Fin d} (hμν : ν ≠ μ)
    (hc : p.vertices = {x, x + latticeStep ℓ ε μ, x + latticeStep ℓ ε μ + latticeStep ℓ ε ν,
      x + latticeStep ℓ ε ν}) :
    p.base = x ∧ ((p.first = μ ∧ p.second = ν) ∨ (p.first = ν ∧ p.second = μ)) := by
  obtain ⟨a, rfl⟩ := exists_eq_gridPoint x
  let u : Fin d → ℤ := Pi.single μ 1
  let v : Fin d → ℤ := Pi.single ν 1
  let f : Fin d → ℤ := Pi.single p.first 1
  let s : Fin d → ℤ := Pi.single p.second 1
  let W : ℤ → ℤ → Fin d → ℤ := fun i j κ => a κ + (i * u κ + j * v κ)
  have huv : ∀ κ, (u κ = 0 ∧ v κ = 0) ∨ (u κ = 1 ∧ v κ = 0) ∨ (u κ = 0 ∧ v κ = 1) := by
    intro κ
    by_cases h1 : κ = μ
    · subst h1
      have : v κ = 0 := by simp [v, hμν.symm]
      have h2 : u κ = 1 := by simp [u]
      exact Or.inr (Or.inl ⟨h2, this⟩)
    · have h2 : u κ = 0 := by simp [u, h1]
      rcases single_one_apply_cases ν κ with h | h
      · exact Or.inl ⟨h2, h⟩
      · exact Or.inr (Or.inr ⟨h2, h⟩)
  have four : ∀ z ∈ ({gridPoint ℓ ε a, gridPoint ℓ ε a + latticeStep ℓ ε μ,
      gridPoint ℓ ε a + latticeStep ℓ ε μ + latticeStep ℓ ε ν,
      gridPoint ℓ ε a + latticeStep ℓ ε ν} : Set (LatticeSite ℓ ε)),
      ∃ i j : ℤ, (i = 0 ∨ i = 1) ∧ (j = 0 ∨ j = 1) ∧ z = gridPoint ℓ ε (W i j) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · refine ⟨0, 0, Or.inl rfl, Or.inl rfl, ?_⟩
      congr 1
      funext κ
      simp [W]
    · refine ⟨1, 0, Or.inr rfl, Or.inl rfl, ?_⟩
      rw [← gridPoint_single, ← gridPoint_add]
      congr 1
      funext κ
      simp [W, u]
    · refine ⟨1, 1, Or.inr rfl, Or.inr rfl, ?_⟩
      rw [← gridPoint_single, ← gridPoint_single, ← gridPoint_add, ← gridPoint_add]
      congr 1
      funext κ
      simp [W, u, v, add_assoc]
    · refine ⟨0, 1, Or.inl rfl, Or.inr rfl, ?_⟩
      rw [← gridPoint_single, ← gridPoint_add]
      congr 1
      funext κ
      simp [W, v]
  have mb : p.base ∈ p.vertices := by simp [LatticePlaquette.vertices]
  have mf : p.base + latticeStep ℓ ε p.first ∈ p.vertices := by
    simp [LatticePlaquette.vertices]
  have ms : p.base + latticeStep ℓ ε p.second ∈ p.vertices := by
    simp [LatticePlaquette.vertices]
  rw [hc] at mb mf ms
  obtain ⟨i₀, j₀, hi₀, hj₀, e₀⟩ := four _ mb
  obtain ⟨i₁, j₁, hi₁, hj₁, e₁⟩ := four _ mf
  obtain ⟨i₂, j₂, hi₂, hj₂, e₂⟩ := four _ ms
  rw [e₀, ← gridPoint_single, ← gridPoint_add, gridPoint_eq_gridPoint_iff hε R hR] at e₁ e₂
  have E₁ : ∀ κ, i₀ * u κ + j₀ * v κ + f κ = i₁ * u κ + j₁ * v κ := fun κ =>
    small_combination_eq hi₀ hj₀ hi₁ hj₁ (huv κ) (single_one_apply_cases _ κ) (h3 κ) (by
      have := e₁ κ
      simp only [Pi.add_apply, W] at this
      have e : a κ + (i₀ * u κ + j₀ * v κ) + (Pi.single p.first 1 : Fin d → ℤ) κ -
          (a κ + (i₁ * u κ + j₁ * v κ)) =
          i₀ * u κ + j₀ * v κ + f κ - (i₁ * u κ + j₁ * v κ) := by
        simp only [f]
        ring
      rwa [e] at this)
  have E₂ : ∀ κ, i₀ * u κ + j₀ * v κ + s κ = i₂ * u κ + j₂ * v κ := fun κ =>
    small_combination_eq hi₀ hj₀ hi₂ hj₂ (huv κ) (single_one_apply_cases _ κ) (h3 κ) (by
      have := e₂ κ
      simp only [Pi.add_apply, W] at this
      have e : a κ + (i₀ * u κ + j₀ * v κ) + (Pi.single p.second 1 : Fin d → ℤ) κ -
          (a κ + (i₂ * u κ + j₂ * v κ)) =
          i₀ * u κ + j₀ * v κ + s κ - (i₂ * u κ + j₂ * v κ) := by
        simp only [s]
        ring
      rwa [e] at this)
  have su : ∑ κ, u κ = 1 := by simp [u]
  have sv : ∑ κ, v κ = 1 := by simp [v]
  have sf : ∑ κ, f κ = 1 := by simp [f]
  have ss : ∑ κ, s κ = 1 := by simp [s]
  have S₁ : i₀ + j₀ + 1 = i₁ + j₁ := by
    have := Finset.sum_congr rfl (fun κ (_ : κ ∈ Finset.univ) => E₁ κ)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, su, sv, sf] at this
    linarith
  have S₂ : i₀ + j₀ + 1 = i₂ + j₂ := by
    have := Finset.sum_congr rfl (fun κ (_ : κ ∈ Finset.univ) => E₂ κ)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, su, sv, ss] at this
    linarith
  have hne : ¬(i₁ = i₂ ∧ j₁ = j₂) := by
    rintro ⟨rfl, rfl⟩
    have hfs : f = s := funext fun κ => by
      have := E₁ κ
      have := E₂ κ
      linarith
    exact p.lt.ne (single_one_injective hfs)
  have hcases : i₀ = 0 ∧ j₀ = 0 ∧ ((i₁ = 1 ∧ j₁ = 0 ∧ i₂ = 0 ∧ j₂ = 1) ∨
      (i₁ = 0 ∧ j₁ = 1 ∧ i₂ = 1 ∧ j₂ = 0)) := by omega
  obtain ⟨rfl, rfl, hcase⟩ := hcases
  refine ⟨?_, ?_⟩
  · rw [e₀]
    congr 1
    funext κ
    simp [W]
  · rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · left
      refine ⟨single_one_injective (funext fun κ => ?_),
        single_one_injective (funext fun κ => ?_)⟩
      · have := E₁ κ
        simp only [zero_mul, zero_add, one_mul, add_zero] at this
        exact this
      · have := E₂ κ
        simp only [zero_mul, zero_add, one_mul, add_zero] at this
        exact this
    · right
      refine ⟨single_one_injective (funext fun κ => ?_),
        single_one_injective (funext fun κ => ?_)⟩
      · have := E₁ κ
        simp only [zero_mul, zero_add, one_mul, add_zero] at this
        exact this
      · have := E₂ κ
        simp only [zero_mul, zero_add, one_mul, add_zero] at this
        exact this
theorem plaquette_corridor_links {p : LatticePlaquette ℓ ε} {c : Link ℓ ε'}
    (hc : PlaquetteInLinkCorridor S n p c) :
    (c.2 = p.first ∧ (p.base, p.first) ∈ linkCorridor S n ε c ∧
        (p.base + latticeStep ℓ ε p.second, p.first) ∈ linkCorridor S n ε c) ∨
      (c.2 = p.second ∧ (p.base, p.second) ∈ linkCorridor S n ε c ∧
        (p.base + latticeStep ℓ ε p.first, p.second) ∈ linkCorridor S n ε c) := by
  obtain ⟨b, hb, b', hb', hne, h₁, h₂⟩ := hc
  have hfs : p.first ≠ p.second := p.lt.ne
  simp only [LatticePlaquette.boundaryLinks, Set.mem_insert_iff, Set.mem_singleton_iff] at hb hb'
  rcases hb with rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hne
    | exact Or.inl ⟨h₁.1.symm, h₁, h₂⟩
    | exact Or.inl ⟨h₁.1.symm, h₂, h₁⟩
    | exact Or.inr ⟨h₁.1.symm, h₁, h₂⟩
    | exact Or.inr ⟨h₁.1.symm, h₂, h₁⟩
    | exact absurd (h₁.1.trans h₂.1.symm) hfs
    | exact absurd (h₂.1.trans h₁.1.symm) hfs
theorem exists_fine_ratios [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S n ℓ ε ε') :
    ∃ R : Fin S.d → ℤ, (∀ μ, ℓ μ = R μ * ε) ∧ (∀ μ, 2 ≤ R μ) ∧ (n ≠ 0 → ∀ μ, 3 ≤ R μ) := by
  obtain ⟨N, hN2, hN⟩ := exists_coarse_ratios h
  have hL : (2 : ℤ) ≤ (S.L : ℤ) := by exact_mod_cast S.two_le_L
  have hpow : (1 : ℤ) ≤ (S.L : ℤ) ^ n := one_le_pow₀ (by omega)
  refine ⟨fun μ => N μ * (S.L : ℤ) ^ n, fine_ratio_eq h hN, fun μ => ?_, fun hn μ => ?_⟩
  · have := hN2 μ
    show 2 ≤ N μ * (S.L : ℤ) ^ n
    nlinarith
  · have h2 : (S.L : ℤ) ≤ (S.L : ℤ) ^ n := le_self_pow₀ (by omega) hn
    have := hN2 μ
    show 3 ≤ N μ * (S.L : ℤ) ^ n
    nlinarith
theorem add_fine_latticeStep_ne [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S n ℓ ε ε')
    (x : LatticeSite ℓ ε) (ν : Fin S.d) : x + latticeStep ℓ ε ν ≠ x := by
  obtain ⟨R, hR, hR2, _⟩ := exists_fine_ratios h
  intro he
  have h0 : latticeStep ℓ ε ν = 0 := by simpa using he
  rw [← gridPoint_single, ← gridPoint_zero (ℓ := ℓ) (ε := ε),
    gridPoint_eq_gridPoint_iff (spacing_ne_zero (ℓ := ℓ)) R hR] at h0
  have h1 := h0 ν
  simp only [Pi.single_eq_same, Pi.zero_apply, sub_zero] at h1
  have := Int.le_of_dvd one_pos h1
  have := hR2 ν
  omega
theorem eq_toFineSite_of_mem_blockOf_zero (h : IsBlockSpacing S 0 ℓ ε ε')
    {x : LatticeSite ℓ ε} {y : LatticeSite ℓ ε'} (hx : x ∈ blockOf S 0 ε y) :
    x = h.toFineSite y := by
  obtain ⟨σ, hσ, rfl⟩ := (mem_blockOf_iff h _ _).mp hx
  have h0 : σ = 0 := by
    funext μ
    have := hσ μ
    simp only [blockOffset, pow_zero, Nat.sub_self, Nat.mul_zero, Nat.zero_div, Nat.cast_zero,
      neg_zero, sub_self] at this
    simp only [Pi.zero_apply]
    omega
  rw [h0, gridPoint_zero, add_zero]
theorem plaquettesOfCorridors [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S n ℓ ε ε') :
    PlaquettesOfCorridors S n ℓ ε ε' := by
  refine ⟨fun c p => ⟨fun hc => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rcases plaquette_corridor_links hc with ⟨e, h₁, h₂⟩ | ⟨e, h₁, h₂⟩
    · refine ⟨p.second, p.base, ?_, ?_, ?_, ?_⟩
      · rw [e]
        exact p.lt.ne'
      · rw [e]
        rfl
      · rw [e]
        exact h₁
      · rw [e]
        exact h₂
    · refine ⟨p.first, p.base, ?_, ?_, ?_, ?_⟩
      · rw [e]
        exact p.lt.ne
      · rw [e]
        ext z
        simp only [LatticePlaquette.vertices, Set.mem_insert_iff, Set.mem_singleton_iff]
        rw [add_right_comm p.base (latticeStep ℓ ε p.first) (latticeStep ℓ ε p.second)]
        tauto
      · rw [e]
        exact h₁
      · rw [e]
        exact h₂
  · rintro ⟨ν, x, hν, hcor, h₁, h₂⟩
    have hn : n ≠ 0 := by
      rintro rfl
      have e₁ := eq_toFineSite_of_mem_blockOf_zero h h₁.2.1
      have e₂ := eq_toFineSite_of_mem_blockOf_zero h h₂.2.1
      exact add_fine_latticeStep_ne h x ν (e₂.trans e₁.symm)
    obtain ⟨R, hR, _, hR3⟩ := exists_fine_ratios h
    obtain ⟨hb, hfs⟩ :=
      plaquette_eq_of_vertices (spacing_ne_zero (ℓ := ℓ)) R hR (hR3 hn) hν hcor
    have hbne : ((x, c.2) : Link ℓ ε) ≠ (x + latticeStep ℓ ε ν, c.2) := by
      intro he
      exact add_fine_latticeStep_ne h x ν (congrArg Prod.fst he).symm
    rcases hfs with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · refine ⟨(x, c.2), ?_, (x + latticeStep ℓ ε ν, c.2), ?_, hbne, h₁, h₂⟩
      · simp [LatticePlaquette.boundaryLinks, hb, e₁, e₂]
      · simp [LatticePlaquette.boundaryLinks, hb, e₁, e₂]
    · refine ⟨(x, c.2), ?_, (x + latticeStep ℓ ε ν, c.2), ?_, hbne, h₁, h₂⟩
      · simp [LatticePlaquette.boundaryLinks, hb, e₁, e₂]
      · simp [LatticePlaquette.boundaryLinks, hb, e₁, e₂]
  · intro c ν x _ h₁ h₂
    refine ⟨(linkInside_iff _ _).mpr ⟨h₁.2.1, h₂.2.1⟩, (linkInside_iff _ _).mpr ⟨h₁.2.2, ?_⟩⟩
    have := h₂.2.2
    simp only [Link.head] at this ⊢
    rwa [add_right_comm] at this
  · intro c c' p hc hc'
    rcases plaquette_corridor_links hc with ⟨e, a₁, a₂⟩ | ⟨e, a₁, a₂⟩ <;>
      rcases plaquette_corridor_links hc' with ⟨e', b₁, b₂⟩ | ⟨e', b₁, b₂⟩
    · exact Prod.ext (blockOf_unique h b₁.2.1 a₁.2.1) (e'.trans e.symm)
    · exfalso
      have e₁ : c.1 = c'.1 := blockOf_unique h a₁.2.1 b₁.2.1
      have e₂ : c.1 = c'.head := blockOf_unique h a₂.2.1 b₁.2.2
      exact add_latticeStep_ne h c'.1 c'.2 (e₂.symm.trans e₁)
    · exfalso
      have e₁ : c'.1 = c.1 := blockOf_unique h b₁.2.1 a₁.2.1
      have e₂ : c'.1 = c.head := blockOf_unique h b₂.2.1 a₁.2.2
      exact add_latticeStep_ne h c.1 c.2 (e₂.symm.trans e₁)
    · exact Prod.ext (blockOf_unique h b₁.2.1 a₁.2.1) (e'.trans e.symm)
  · intro c p hc y hin
    have hbase : p.base ∈ blockOf S n ε y := hin (by simp [LatticePlaquette.vertices])
    have hf : p.base + latticeStep ℓ ε p.first ∈ blockOf S n ε y :=
      hin (by simp [LatticePlaquette.vertices])
    have hs : p.base + latticeStep ℓ ε p.second ∈ blockOf S n ε y :=
      hin (by simp [LatticePlaquette.vertices])
    rcases plaquette_corridor_links hc with ⟨_, a₁, _⟩ | ⟨_, a₁, _⟩
    · have e₁ : y = c.1 := blockOf_unique h hbase a₁.2.1
      have e₂ : y = c.head := blockOf_unique h hf a₁.2.2
      exact add_latticeStep_ne h c.1 c.2 (e₂.symm.trans e₁)
    · have e₁ : y = c.1 := blockOf_unique h hbase a₁.2.1
      have e₂ : y = c.head := blockOf_unique h hs a₁.2.2
      exact add_latticeStep_ne h c.1 c.2 (e₂.symm.trans e₁)
  · intro p y y' h₁ h₂
    have hb : p.base ∈ p.vertices := by simp [LatticePlaquette.vertices]
    exact blockOf_unique h (h₂ hb) (h₁ hb)
end Plaquettes
section Domains
variable {S : LatticeParameters} {ℓ : Fin S.d → ℝ} {ε ε' : ℝ} {n : ℕ}
theorem gridPoint_single_natCast {d : ℕ} {ℓ : Fin d → ℝ} {ε : ℝ} (μ : Fin d) (j : ℕ) :
    gridPoint ℓ ε (Pi.single μ (j : ℤ)) = j • latticeStep ℓ ε μ := by
  induction j with
  | zero => simp [gridPoint_zero]
  | succ j ih =>
    have : (Pi.single μ ((j + 1 : ℕ) : ℤ) : Fin d → ℤ) =
        Pi.single μ (j : ℤ) + Pi.single μ 1 := by
      rw [← Pi.single_add]
      congr 1
    rw [this, gridPoint_add, ih, gridPoint_single, succ_nsmul]
theorem nsmul_latticeStep_mem_blockOf (h : IsBlockSpacing S n ℓ ε ε') {y : LatticeSite ℓ ε'}
    {σ : Fin S.d → ℤ} (hσ : InBlockIndexRange S n σ) (μ : Fin S.d) {j : ℕ}
    (hj : j ≤ S.L ^ n) :
    h.toFineSite y + gridPoint ℓ ε σ + j • latticeStep ℓ ε μ ∈
      blockOf S n ε y ∪ blockOf S n ε (y + latticeStep ℓ ε' μ) := by
  have hb := hσ μ
  have hj' : (j : ℤ) ≤ (S.L : ℤ) ^ n := by exact_mod_cast hj
  by_cases hle : σ μ + j ≤ (S.L : ℤ) ^ n - 1 - blockOffset S n
  · left
    refine (mem_blockOf_iff h _ _).mpr ⟨σ + Pi.single μ (j : ℤ),
      inBlockIndexRange_add_single hσ (by omega) hle, ?_⟩
    rw [gridPoint_add, gridPoint_single_natCast, add_assoc]
  · right
    refine (mem_blockOf_iff h _ _).mpr ⟨σ + Pi.single μ ((j : ℤ) - (S.L : ℤ) ^ n),
      inBlockIndexRange_add_single hσ (by omega) (by omega), ?_⟩
    have hs : (Pi.single μ (j : ℤ) : Fin S.d → ℤ) =
        Pi.single μ ((S.L : ℤ) ^ n) + Pi.single μ ((j : ℤ) - (S.L : ℤ) ^ n) := by
      rw [← Pi.single_add]
      congr 1
      ring
    rw [← gridPoint_single_natCast, hs, toFineSite_add, toFineSite_latticeStep, gridPoint_add,
      gridPoint_add]
    abel
theorem linkDomainEndpoints (h : IsBlockSpacing S n ℓ ε ε') :
    LinkDomainEndpoints S n ℓ ε ε' := by
  rintro b a ⟨x, hx, k, hk, rfl⟩ z hz
  obtain ⟨σ, hσ, rfl⟩ := (mem_blockOf_iff h _ _).mp hx
  simp only [Link.ends, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact nsmul_latticeStep_mem_blockOf h hσ b.2 hk.le
  · have := nsmul_latticeStep_mem_blockOf h (y := b.1) hσ b.2 (j := k + 1) hk
    simp only [Link.head]
    rwa [succ_nsmul, ← add_assoc] at this
theorem exists_path_cons {x : LatticeSite ℓ ε} (t : LinkStep ℓ ε) (hs : t.source = x)
    (Γ : LatticePath ℓ ε) (hΓ : Γ.origin = t.target) :
    ∃ Γ' : LatticePath ℓ ε, Γ'.origin = x ∧ Γ'.endpoint = Γ.endpoint ∧
      Γ'.steps = t :: Γ.steps :=
  ⟨⟨x, t :: Γ.steps, hs, hΓ ▸ Γ.walk⟩, rfl, by
    simp only [LatticePath.endpoint, stepsEndpoint, hΓ], rfl⟩
theorem exists_path_in_block (h : IsBlockSpacing S n ℓ ε ε') (y : LatticeSite ℓ ε') :
    ∀ (k : ℕ) (σ τ : Fin S.d → ℤ), InBlockIndexRange S n σ → InBlockIndexRange S n τ →
      ∑ μ, (σ μ - τ μ).natAbs ≤ k →
      ∃ Γ : LatticePath ℓ ε, Γ.origin = h.toFineSite y + gridPoint ℓ ε σ ∧
        Γ.endpoint = h.toFineSite y + gridPoint ℓ ε τ ∧
        ∀ t ∈ Γ.steps, LinkInside S t.link (blockOf S n ε y) := by
  intro k
  induction k with
  | zero =>
    intro σ τ _ _ hk
    have hst : σ = τ := by
      funext μ
      have := (Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hk)) μ (Finset.mem_univ μ)
      omega
    subst hst
    exact ⟨⟨_, [], trivial⟩, rfl, rfl, by simp⟩
  | succ k ih =>
    intro σ τ hσ hτ hk
    by_cases hst : σ = τ
    · subst hst
      exact ⟨⟨_, [], trivial⟩, rfl, rfl, by simp⟩
    obtain ⟨μ, hμ⟩ : ∃ μ, σ μ ≠ τ μ := by
      by_contra hall
      exact hst (funext fun μ => by_contra fun hne => hall ⟨μ, hne⟩)
    have hb := hσ μ
    have hb' := hτ μ
    have hdecr : ∀ c : ℤ, (σ μ + c - τ μ).natAbs < (σ μ - τ μ).natAbs →
        ∑ κ, ((σ + Pi.single μ c : Fin S.d → ℤ) κ - τ κ).natAbs ≤ k := by
      intro c hc
      have hlt : ∑ κ, ((σ + Pi.single μ c : Fin S.d → ℤ) κ - τ κ).natAbs <
          ∑ κ, (σ κ - τ κ).natAbs := by
        refine Finset.sum_lt_sum (fun κ _ => ?_) ⟨μ, Finset.mem_univ μ, ?_⟩
        · by_cases hκ : κ = μ
          · subst hκ
            rw [add_single_apply_self]
            exact hc.le
          · rw [add_single_apply_of_ne _ _ hκ]
        · rw [add_single_apply_self]
          exact hc
      omega
    rcases lt_or_gt_of_ne hμ with hlt | hgt
    · have hr := inBlockIndexRange_add_single hσ (μ := μ) (c := 1) (by omega) (by omega)
      obtain ⟨Γ, e₁, e₂, e₃⟩ := ih _ τ hr hτ (hdecr 1 (by omega))
      obtain ⟨Γ', f₁, f₂, f₃⟩ := exists_path_cons (x := h.toFineSite y + gridPoint ℓ ε σ)
        ⟨(h.toFineSite y + gridPoint ℓ ε σ, μ), true⟩ rfl Γ (by
          rw [e₁, ← gridPoint_add_latticeStep]
          rfl)
      refine ⟨Γ', f₁, f₂.trans e₂, ?_⟩
      rw [f₃]
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · refine (linkInside_iff _ _).mpr ⟨(mem_blockOf_iff h _ _).mpr ⟨σ, hσ, rfl⟩,
          (mem_blockOf_iff h _ _).mpr ⟨_, hr, gridPoint_add_latticeStep h y σ μ⟩⟩
      · exact e₃ t ht
    · have hr := inBlockIndexRange_add_single hσ (μ := μ) (c := -1) (by omega) (by omega)
      obtain ⟨Γ, e₁, e₂, e₃⟩ := ih _ τ hr hτ (hdecr (-1) (by omega))
      have hback : h.toFineSite y + gridPoint ℓ ε (σ + Pi.single μ (-1)) + latticeStep ℓ ε μ =
          h.toFineSite y + gridPoint ℓ ε σ := by
        rw [gridPoint_add_latticeStep, add_assoc, ← Pi.single_add]
        simp
      obtain ⟨Γ', f₁, f₂, f₃⟩ := exists_path_cons (x := h.toFineSite y + gridPoint ℓ ε σ)
        ⟨(h.toFineSite y + gridPoint ℓ ε (σ + Pi.single μ (-1)), μ), false⟩ hback Γ e₁
      refine ⟨Γ', f₁, f₂.trans e₂, ?_⟩
      rw [f₃]
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · refine (linkInside_iff _ _).mpr ⟨(mem_blockOf_iff h _ _).mpr ⟨_, hr, rfl⟩,
          (mem_blockOf_iff h _ _).mpr ⟨σ, hσ, hback⟩⟩
      · exact e₃ t ht
theorem blockPathConnected (h : IsBlockSpacing S n ℓ ε ε') : BlockPathConnected S n ℓ ε ε' := by
  intro y x hx x' hx'
  obtain ⟨σ, hσ, rfl⟩ := (mem_blockOf_iff h _ _).mp hx
  obtain ⟨τ, hτ, rfl⟩ := (mem_blockOf_iff h _ _).mp hx'
  exact exists_path_in_block h y _ σ τ hσ hτ le_rfl
end Domains
section Operators
variable {S : LatticeParameters} {ℓ : Fin S.d → ℝ} {ε ε' : ℝ} {n : ℕ}
open Classical in
theorem blockAverage0_single_of_mem [IsCommensurateSpacing ℓ ε]
    (inst : DecidableEq (LatticeSite ℓ ε)) {x : LatticeSite ℓ ε} {j : LatticeSite ℓ ε'}
    (hx : x ∈ blockOf S n ε j) :
    blockAverage0 S n ε ε' (@Pi.single _ (fun _ => ℝ) _ inst x 1) j =
      ((S.L : ℝ) ^ (n * S.d))⁻¹ := by
  simp only [blockAverage0, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single_of_mem x (by simpa using hx)
    (fun b _ hne => Pi.single_eq_of_ne hne _), Pi.single_eq_same, mul_one]
open Classical in
theorem blockAverage0_single_of_not_mem [IsCommensurateSpacing ℓ ε]
    (inst : DecidableEq (LatticeSite ℓ ε)) {x : LatticeSite ℓ ε} {j : LatticeSite ℓ ε'}
    (hx : x ∉ blockOf S n ε j) :
    blockAverage0 S n ε ε' (@Pi.single _ (fun _ => ℝ) _ inst x 1) j = 0 := by
  simp only [blockAverage0, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_zero, mul_zero]
  intro b hb
  have hb' : b ∈ blockOf S n ε j := by simpa using hb
  refine Pi.single_eq_of_ne ?_ _
  rintro rfl
  exact hx hb'
theorem blockAverage0AdjointConstant [IsCommensurateSpacing ℓ ε] [IsCommensurateSpacing ℓ ε']
    (h : IsBlockSpacing S n ℓ ε ε') : BlockAverage0AdjointConstant S n ℓ ε ε' := by
  intro ω y x hx
  have hε : ε ≠ 0 := spacing_ne_zero (ℓ := ℓ)
  have hL : (S.L : ℝ) ≠ 0 := by
    have := S.two_le_L
    positivity
  simp only [blockAverage0Adjoint, rescaledAdjoint, latticeAdjoint, LinearMap.smul_apply,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single y, blockAverage0_single_of_mem _ hx, h.spacing_eq, mul_div_assoc,
    div_self hε, mul_one, ← pow_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hL), one_mul]
  · intro j _ hj
    rw [blockAverage0_single_of_not_mem _ (fun hm => hj (blockOf_unique h hm hx)), zero_mul]
  · simp
theorem sum_single_one_mul {ι : Type*} [Fintype ι] (inst : DecidableEq ι) (x : ι) (f : ι → ℝ) :
    ∑ z, (@Pi.single ι (fun _ => ℝ) _ inst x 1) z * f z = f x := by
  rw [Finset.sum_eq_single x]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_mul]
  · simp
theorem sum_latticeGradient_mul {d : ℕ} {ℓ : Fin d → ℝ} {ε : ℝ} [IsCommensurateSpacing ℓ ε]
    (δ : Cochain0 ℓ ε) (A : Cochain1 ℓ ε) (μ : Fin d) :
    ∑ z, latticeGradient ℓ ε δ (z, μ) * A (z, μ) =
      ε⁻¹ * (∑ z, δ z * A (z - latticeStep ℓ ε μ, μ) - ∑ z, δ z * A (z, μ)) := by
  have hshift : ∑ z, δ (z + latticeStep ℓ ε μ) * A (z, μ) =
      ∑ z, δ z * A (z - latticeStep ℓ ε μ, μ) :=
    Fintype.sum_equiv (Equiv.addRight (latticeStep ℓ ε μ)) _ _ fun z => by simp
  rw [← hshift, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  show ε⁻¹ * (δ (z + latticeStep ℓ ε μ) - δ z) * A (z, μ) = _
  ring
theorem latticeDivergence_apply {d : ℕ} {ℓ : Fin d → ℝ} {ε : ℝ} [IsCommensurateSpacing ℓ ε]
    (A : Cochain1 ℓ ε) (x : LatticeSite ℓ ε) :
    latticeDivergence ℓ ε A x =
      ε⁻¹ * ∑ μ, (linkComponent A μ (x - latticeStep ℓ ε μ) - linkComponent A μ x) := by
  simp only [latticeDivergence, latticeAdjoint, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [sum_latticeGradient_mul, sum_single_one_mul _ x fun z => A (z - latticeStep ℓ ε μ, μ),
    sum_single_one_mul _ x fun z => A (z, μ)]
  rfl
theorem divergenceLaplacianFormulas (S : LatticeParameters) {ℓ : Fin S.d → ℝ} {ε : ℝ}
    [IsCommensurateSpacing ℓ ε] : DivergenceLaplacianFormulas S ℓ ε := by
  refine ⟨latticeDivergence_apply, fun lam x => ?_⟩
  show latticeDivergence ℓ ε (latticeGradient ℓ ε lam) x = _
  rw [latticeDivergence_apply, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  show ε⁻¹ * (ε⁻¹ * (lam (x - latticeStep ℓ ε μ + latticeStep ℓ ε μ) -
    lam (x - latticeStep ℓ ε μ)) - ε⁻¹ * (lam (x + latticeStep ℓ ε μ) - lam x)) = _
  rw [sub_add_cancel]
  ring
open Classical in
theorem trivialBlocks [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S 0 ℓ ε ε) :
    TrivialBlocks S ℓ ε := by
  have hb : ∀ y : LatticeSite ℓ ε, blockOf S 0 ε y = {y} := by
    intro y
    ext x
    constructor
    · intro hx
      exact eq_toFineSite_of_mem_blockOf_zero h hx
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact toFineSite_mem_blockOf h x
  have hf : ∀ (y : LatticeSite ℓ ε) (g : LatticeSite ℓ ε → ℝ),
      ∑ x ∈ Finset.univ.filter (· ∈ blockOf S 0 ε y), g x = g y := by
    intro y g
    rw [Finset.sum_eq_single_of_mem y (by simp [hb])]
    intro b hb' hne
    exact absurd (by simpa [hb] using hb') hne
  refine ⟨hb, ?_, ?_⟩
  · ext lam y
    simp only [blockAverage0, hf]
    simp
  · ext A b
    simp only [blockAverage1, hf]
    simp
end Operators
section Moves
variable {d : ℕ} {ℓ : Fin d → ℝ} {ε : ℝ}
def movesEndpoint (x : LatticeSite ℓ ε) (ms : List (Fin d × Bool)) : LatticeSite ℓ ε :=
  stepsEndpoint x (stepsOfMoves x ms)
theorem movesEndpoint_cons (x : LatticeSite ℓ ε) (m : Fin d × Bool) (ms : List (Fin d × Bool)) :
    movesEndpoint x (m :: ms) = movesEndpoint (unitStep x m.1 m.2).target ms := rfl
theorem stepsOfMoves_append (x : LatticeSite ℓ ε) (ms₁ ms₂ : List (Fin d × Bool)) :
    stepsOfMoves x (ms₁ ++ ms₂) =
      stepsOfMoves x ms₁ ++ stepsOfMoves (movesEndpoint x ms₁) ms₂ := by
  induction ms₁ generalizing x with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.cons_append, stepsOfMoves, movesEndpoint_cons, ih]
theorem movesEndpoint_append (x : LatticeSite ℓ ε) (ms₁ ms₂ : List (Fin d × Bool)) :
    movesEndpoint x (ms₁ ++ ms₂) = movesEndpoint (movesEndpoint x ms₁) ms₂ := by
  induction ms₁ generalizing x with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.cons_append, movesEndpoint_cons, ih]
def signOfMove (s : Bool) : ℤ := if s then 1 else -1
theorem gridPoint_single_neg_one (μ : Fin d) :
    gridPoint ℓ ε (Pi.single μ (-1)) = -latticeStep ℓ ε μ := by
  rw [Pi.single_neg, gridPoint_neg, gridPoint_single]
theorem unitStep_target (x : LatticeSite ℓ ε) (μ : Fin d) (s : Bool) :
    (unitStep x μ s).target = x + gridPoint ℓ ε (Pi.single μ (signOfMove s)) := by
  cases s
  · simp [unitStep, LinkStep.target, signOfMove, gridPoint_single_neg_one, sub_eq_add_neg]
  · simp [unitStep, LinkStep.target, signOfMove, gridPoint_single, Link.head]
theorem movesEndpoint_replicate (x : LatticeSite ℓ ε) (μ : Fin d) (s : Bool) (k : ℕ) :
    movesEndpoint x (List.replicate k (μ, s)) =
      x + gridPoint ℓ ε (Pi.single μ ((k : ℤ) * signOfMove s)) := by
  induction k generalizing x with
  | zero => simp [(show movesEndpoint x [] = x from rfl), gridPoint_zero]
  | succ k ih =>
    rw [List.replicate_succ, movesEndpoint_cons, ih]
    dsimp only
    have : (Pi.single μ (((k + 1 : ℕ) : ℤ) * signOfMove s) : Fin d → ℤ) =
        Pi.single μ (signOfMove s) + Pi.single μ ((k : ℤ) * signOfMove s) := by
      rw [← Pi.single_add]
      congr 1
      push_cast
      ring
    rw [unitStep_target, this, gridPoint_add, add_assoc]
def axisSegment (σ : Fin d → ℤ) (μ : Fin d) : List (Fin d × Bool) :=
  List.replicate (σ μ).natAbs (μ, decide (0 ≤ σ μ))
theorem natAbs_mul_signOfMove (c : ℤ) : ((c.natAbs : ℤ)) * signOfMove (decide (0 ≤ c)) = c := by
  by_cases h : 0 ≤ c
  · simp only [signOfMove, h, decide_true, if_true]
    omega
  · simp only [signOfMove, h, decide_false, Bool.false_eq_true, if_false]
    omega
theorem movesEndpoint_axisSegment (x : LatticeSite ℓ ε) (σ : Fin d → ℤ) (μ : Fin d) :
    movesEndpoint x (axisSegment σ μ) = x + gridPoint ℓ ε (Pi.single μ (σ μ)) := by
  rw [axisSegment, movesEndpoint_replicate, natAbs_mul_signOfMove]
theorem movesEndpoint_flatMap (σ : Fin d → ℤ) (l : List (Fin d)) (hl : l.Nodup)
    (x : LatticeSite ℓ ε) :
    movesEndpoint x (l.flatMap (axisSegment σ)) =
      x + gridPoint ℓ ε (fun m => if m ∈ l then σ m else 0) := by
  induction l generalizing x with
  | nil =>
    have : (fun m : Fin d => if m ∈ ([] : List (Fin d)) then σ m else 0) = 0 := by
      funext m
      simp
    rw [this, gridPoint_zero, add_zero]
    rfl
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    rw [List.flatMap_cons, movesEndpoint_append, movesEndpoint_axisSegment, ih hl', add_assoc,
      ← gridPoint_add]
    congr 2
    funext m
    by_cases hm : m = a
    · subst hm
      simp [ha]
    · simp [hm]
theorem pairwise_gt_reverse_finRange (d : ℕ) :
    ((List.finRange d).reverse).Pairwise (· > ·) := by
  rw [List.pairwise_reverse]
  exact List.pairwise_lt_finRange d
theorem axisMoves_eq (σ : Fin d → ℤ) :
    axisMoves σ = (List.finRange d).reverse.flatMap (axisSegment σ) := rfl
theorem movesEndpoint_axisMoves (x : LatticeSite ℓ ε) (σ : Fin d → ℤ) :
    movesEndpoint x (axisMoves σ) = x + gridPoint ℓ ε σ := by
  rw [axisMoves_eq,
    movesEndpoint_flatMap σ _ (List.nodup_reverse.mpr (List.nodup_finRange d))]
  congr 2
  funext m
  simp
theorem mem_stepsOfMoves_replicate (x : LatticeSite ℓ ε) (μ : Fin d) (s : Bool) (k : ℕ)
    {t : LinkStep ℓ ε} (ht : t ∈ stepsOfMoves x (List.replicate k (μ, s))) :
    ∃ j : ℕ, j < k ∧ t.link = (x + gridPoint ℓ ε
      (Pi.single μ (if s then (j : ℤ) else -((j : ℤ) + 1))), μ) := by
  induction k generalizing x with
  | zero => simp [stepsOfMoves] at ht
  | succ k ih =>
    rw [List.replicate_succ] at ht
    simp only [stepsOfMoves] at ht
    rcases List.mem_cons.mp ht with rfl | ht
    · refine ⟨0, by omega, ?_⟩
      cases s
      · simp [unitStep, gridPoint_single_neg_one, sub_eq_add_neg]
      · simp [unitStep, gridPoint_zero]
    · obtain ⟨j, hj, hb⟩ := ih _ ht
      refine ⟨j + 1, by omega, ?_⟩
      rw [hb, unitStep_target, add_assoc, ← gridPoint_add, ← Pi.single_add]
      congr 4
      cases s
      · simp [signOfMove]
      · simp [signOfMove]
        ring
def BetweenZeroAnd (σ τ : Fin d → ℤ) : Prop :=
  ∀ m, (0 ≤ τ m ∧ τ m ≤ σ m) ∨ (σ m ≤ τ m ∧ τ m ≤ 0)
theorem links_of_stepsOfMoves (z : LatticeSite ℓ ε) (σ : Fin d → ℤ) (l : List (Fin d))
    (hl : l.Pairwise (· > ·)) (τ : Fin d → ℤ) (hτ : BetweenZeroAnd σ τ)
    (h0 : ∀ a ∈ l, ∀ m, m ≤ a → τ m = 0) {t : LinkStep ℓ ε}
    (ht : t ∈ stepsOfMoves (z + gridPoint ℓ ε τ) (l.flatMap (axisSegment σ))) :
    ∃ (ρ : Fin d → ℤ) (i : Fin d), t.link = (z + gridPoint ℓ ε ρ, i) ∧ BetweenZeroAnd σ ρ ∧
      BetweenZeroAnd σ (ρ + Pi.single i 1) ∧ ∀ m, m < i → ρ m = 0 := by
  induction l generalizing τ with
  | nil => simp [stepsOfMoves] at ht
  | cons a l ih =>
    obtain ⟨hgt, hl'⟩ := List.pairwise_cons.mp hl
    have hτa : τ a = 0 := h0 a List.mem_cons_self a le_rfl
    rw [List.flatMap_cons, stepsOfMoves_append, List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨j, hj, hb⟩ := mem_stepsOfMoves_replicate _ a _ _ ht
      have hlow : ∀ m, m < a → τ m = 0 := fun m hm => h0 a List.mem_cons_self m hm.le
      by_cases hs : 0 ≤ σ a
      · have hj' : (j : ℤ) + 1 ≤ σ a := by omega
        refine ⟨τ + Pi.single a (j : ℤ), a, ?_, fun m => ?_, fun m => ?_, fun m hm => ?_⟩
        · rw [hb, add_assoc, ← gridPoint_add]
          simp [hs]
        · by_cases hm : m = a
          · subst hm
            rw [add_single_apply_self]
            omega
          · rw [add_single_apply_of_ne _ _ hm]
            exact hτ m
        · by_cases hm : m = a
          · subst hm
            rw [add_assoc, ← Pi.single_add, add_single_apply_self]
            omega
          · rw [add_assoc, ← Pi.single_add, add_single_apply_of_ne _ _ hm]
            exact hτ m
        · rw [add_single_apply_of_ne _ _ hm.ne]
          exact hlow m hm
      · have hj' : (j : ℤ) + 1 ≤ -σ a := by omega
        refine ⟨τ + Pi.single a (-((j : ℤ) + 1)), a, ?_, fun m => ?_, fun m => ?_,
          fun m hm => ?_⟩
        · rw [hb, add_assoc, ← gridPoint_add]
          simp [hs]
        · by_cases hm : m = a
          · subst hm
            rw [add_single_apply_self]
            omega
          · rw [add_single_apply_of_ne _ _ hm]
            exact hτ m
        · by_cases hm : m = a
          · subst hm
            rw [add_assoc, ← Pi.single_add, add_single_apply_self]
            omega
          · rw [add_assoc, ← Pi.single_add, add_single_apply_of_ne _ _ hm]
            exact hτ m
        · rw [add_single_apply_of_ne _ _ hm.ne]
          exact hlow m hm
    · rw [movesEndpoint_axisSegment, add_assoc, ← gridPoint_add] at ht
      refine ih hl' _ (fun m => ?_) (fun b hb m hm => ?_) ht
      · by_cases hm : m = a
        · subst hm
          rw [add_single_apply_self, hτa]
          omega
        · rw [add_single_apply_of_ne _ _ hm]
          exact hτ m
      · have hlt : m < a := lt_of_le_of_lt hm (hgt b hb)
        rw [add_single_apply_of_ne _ _ hlt.ne]
        exact h0 a List.mem_cons_self m hlt.le
theorem flatMap_axisSegment_eq_nil (σ : Fin d → ℤ) (l : List (Fin d)) (h : ∀ m ∈ l, σ m = 0) :
    l.flatMap (axisSegment σ) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, ih fun m hm => h m (List.mem_cons_of_mem _ hm)]
    simp [axisSegment, h a List.mem_cons_self]
theorem flatMap_axisSegment_snoc (α β : Fin d → ℤ) (i : Fin d) (s : Bool) (l : List (Fin d))
    (hl : l.Pairwise (· > ·)) (hi : i ∈ l) (hne : ∀ m, m ≠ i → α m = β m)
    (h0 : ∀ m, m < i → α m = 0) (hs : axisSegment β i = axisSegment α i ++ [(i, s)]) :
    l.flatMap (axisSegment β) = l.flatMap (axisSegment α) ++ [(i, s)] := by
  induction l with
  | nil => simp at hi
  | cons a l ih =>
    obtain ⟨hgt, hl'⟩ := List.pairwise_cons.mp hl
    by_cases ha : a = i
    · subst ha
      have hα : l.flatMap (axisSegment α) = [] :=
        flatMap_axisSegment_eq_nil _ _ fun m hm => h0 m (hgt m hm)
      have hβ : l.flatMap (axisSegment β) = [] :=
        flatMap_axisSegment_eq_nil _ _ fun m hm => by
          rw [← hne m (hgt m hm).ne]
          exact h0 m (hgt m hm)
      rw [List.flatMap_cons, List.flatMap_cons, hα, hβ, hs]
      simp
    · have hi' : i ∈ l := by
        rcases List.mem_cons.mp hi with h | h
        · exact absurd h.symm ha
        · exact h
      have hseg : axisSegment β a = axisSegment α a := by
        rw [axisSegment, axisSegment, hne a ha]
      rw [List.flatMap_cons, List.flatMap_cons, ih hl' hi', hseg, List.append_assoc]
theorem axisSegment_snoc_forward (α : Fin d → ℤ) (i : Fin d) (h0 : 0 ≤ α i) {β : Fin d → ℤ}
    (hβ : β i = α i + 1) : axisSegment β i = axisSegment α i ++ [(i, true)] := by
  have e₁ : decide (0 ≤ β i) = true := by
    simp only [decide_eq_true_eq]
    omega
  have e₂ : decide (0 ≤ α i) = true := by simpa using h0
  have e₃ : (β i).natAbs = (α i).natAbs + 1 := by omega
  rw [axisSegment, axisSegment, e₁, e₂, e₃, List.replicate_succ']
theorem axisSegment_snoc_backward (α : Fin d → ℤ) (i : Fin d) (h0 : α i ≤ 0) {β : Fin d → ℤ}
    (hβ : β i = α i - 1) : axisSegment β i = axisSegment α i ++ [(i, false)] := by
  have e₁ : decide (0 ≤ β i) = false := by
    simp only [decide_eq_false_iff_not]
    omega
  have e₃ : (β i).natAbs = (α i).natAbs + 1 := by omega
  rw [axisSegment, axisSegment, e₁, e₃, List.replicate_succ']
  by_cases hz : α i = 0
  · simp [hz]
  · have e₂ : decide (0 ≤ α i) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    rw [e₂]
theorem axisMoves_snoc (α β : Fin d → ℤ) (i : Fin d) (s : Bool)
    (hne : ∀ m, m ≠ i → α m = β m) (h0 : ∀ m, m < i → α m = 0)
    (hs : axisSegment β i = axisSegment α i ++ [(i, s)]) :
    axisMoves β = axisMoves α ++ [(i, s)] := by
  rw [axisMoves_eq, axisMoves_eq]
  exact flatMap_axisSegment_snoc α β i s _ (pairwise_gt_reverse_finRange d) (by simp) hne h0 hs
theorem axisPath_steps_snoc (x : LatticeSite ℓ ε) {α β : Fin d → ℤ} {i : Fin d} {s : Bool}
    (hm : axisMoves β = axisMoves α ++ [(i, s)]) :
    (axisPath x β).steps =
      (axisPath x α).steps ++ [unitStep (x + gridPoint ℓ ε α) i s] := by
  show stepsOfMoves x (axisMoves β) = stepsOfMoves x (axisMoves α) ++ _
  rw [hm, stepsOfMoves_append, movesEndpoint_axisMoves]
  rfl
end Moves
section Trees
variable {S : LatticeParameters} {ℓ : Fin S.d → ℝ} {ε ε' : ℝ}
theorem inBlockIndexRange_of_between {n : ℕ} {σ τ : Fin S.d → ℤ}
    (hσ : InBlockIndexRange S n σ) (hτ : BetweenZeroAnd σ τ) : InBlockIndexRange S n τ := by
  intro m
  have h0 := inBlockIndexRange_zero S n m
  have h1 := hσ m
  simp only [Pi.zero_apply] at h0
  rcases hτ m with h | h <;> constructor <;> omega
theorem index_eq_zero_of_coordinateAgrees [IsCommensurateSpacing ℓ ε] {n : ℕ}
    (h : IsBlockSpacing S n ℓ ε ε') {y : LatticeSite ℓ ε'} {σ : Fin S.d → ℤ}
    (hσ : InBlockIndexRange S n σ) {m : Fin S.d}
    (hs : CoordinateAgrees ((h.toFineSite y + gridPoint ℓ ε σ : LatticeSite ℓ ε) : PeriodicTorus ℓ)
      (y : PeriodicTorus ℓ) m) : σ m = 0 := by
  obtain ⟨u, hu, hum⟩ := hs
  obtain ⟨N, hN2, hN⟩ := exists_coarse_ratios h
  have hε : ε ≠ 0 := spacing_ne_zero (ℓ := ℓ)
  have h1 : torusMk ℓ u = torusMk ℓ fun κ => (σ κ : ℝ) * ε := by
    rw [hu]
    exact add_sub_cancel_left _ _
  rw [torusMk_eq_torusMk_iff] at h1
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
    ((AddSubgroup.mem_pi _).mp h1 m (Set.mem_univ m))
  set M : ℤ := (S.L : ℤ) ^ n with hM
  have h2 : (σ m : ℝ) = ((-(N m * M * k) : ℤ) : ℝ) := by
    have h3 := hk
    rw [zsmul_eq_mul, fine_ratio_eq h hN m] at h3
    simp only [Pi.sub_apply, hum, zero_sub] at h3
    have h4 : ((k : ℝ) * ((N m * M : ℤ) : ℝ)) * ε = -(σ m : ℝ) * ε := by
      rw [mul_assoc, h3]
      ring
    have h5 := mul_right_cancel₀ hε h4
    push_cast at h5 ⊢
    linarith
  have h3 : σ m = -(N m * M * k) := by exact_mod_cast h2
  have hd : M ∣ σ m := ⟨-(N m * k), by rw [h3]; ring⟩
  have hlt : |σ m| < M := by
    have := hσ m
    have hlo := blockOffset_add_one_le S n
    rw [abs_lt]
    constructor <;> omega
  exact Int.eq_zero_of_abs_lt_dvd hd hlt
theorem blockContour_eq_axisPath [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S 1 ℓ ε ε')
    {y : LatticeSite ℓ ε'} {σ : Fin S.d → ℤ} (hσ : InBlockIndexRange S 1 σ)
    {x : LatticeSite ℓ ε} (hx : x ∈ blockOf S 1 ε y)
    (he : x = h.toFineSite y + gridPoint ℓ ε σ) :
    blockContour S h y hx = axisPath (h.toFineSite y) σ := by
  have hspec := Classical.choose_spec hx
  have hc : Classical.choose hx = σ :=
    (block_decomposition_unique h hspec.1 hσ ((Subtype.ext hspec.2 : x = _).symm.trans he)).2
  rw [blockContour, hc]
theorem exists_blockContour_snoc [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S 1 ℓ ε ε')
    {y : LatticeSite ℓ ε'} {b : Link ℓ ε} (hb : b ∈ blockTreeByCoordinates S ε y) :
    ∃ (x x' : LatticeSite ℓ ε) (hx : x ∈ blockOf S 1 ε y) (hx' : x' ∈ blockOf S 1 ε y)
      (t : LinkStep ℓ ε), t.link = b ∧
      (blockContour S h y hx').steps = (blockContour S h y hx).steps ++ [t] := by
  obtain ⟨w, i⟩ := b
  obtain ⟨hin, hco⟩ := hb
  obtain ⟨hw, hhead⟩ := (linkInside_iff _ _).mp hin
  obtain ⟨σ, hσ, rfl⟩ := (mem_blockOf_iff h _ _).mp hw
  have hzero : ∀ m, m < i → σ m = 0 := fun m hm =>
    index_eq_zero_of_coordinateAgrees h hσ (hco m hm)
  have hbound := hσ i
  have htop : σ i < (S.L : ℤ) ^ 1 - 1 - blockOffset S 1 := by
    by_contra hnot
    have he : σ i = (S.L : ℤ) ^ 1 - 1 - blockOffset S 1 := by omega
    have hm := ((blockNeighborSite h y σ hσ i).2 he).2
    exact add_latticeStep_ne h y i (blockOf_unique h hm hhead)
  have hτ : InBlockIndexRange S 1 (σ + Pi.single i 1) :=
    inBlockIndexRange_add_single hσ (by omega) (by omega)
  have hτm : h.toFineSite y + gridPoint ℓ ε (σ + Pi.single i 1) ∈ blockOf S 1 ε y :=
    (mem_blockOf_iff h _ _).mpr ⟨_, hτ, rfl⟩
  have hne : ∀ m, m ≠ i → σ m = (σ + Pi.single i 1 : Fin S.d → ℤ) m := fun m hm =>
    (add_single_apply_of_ne _ _ hm).symm
  by_cases hs : 0 ≤ σ i
  · refine ⟨_, _, hw, hτm, unitStep (h.toFineSite y + gridPoint ℓ ε σ) i true, rfl, ?_⟩
    rw [blockContour_eq_axisPath h hσ hw rfl, blockContour_eq_axisPath h hτ hτm rfl]
    exact axisPath_steps_snoc _ (axisMoves_snoc σ _ i true hne hzero
      (axisSegment_snoc_forward σ i hs (add_single_apply_self σ i 1)))
  · have hback : h.toFineSite y + gridPoint ℓ ε (σ + Pi.single i 1) - latticeStep ℓ ε i =
        h.toFineSite y + gridPoint ℓ ε σ := by
      rw [gridPoint_add, gridPoint_single]
      abel
    refine ⟨_, _, hτm, hw,
      unitStep (h.toFineSite y + gridPoint ℓ ε (σ + Pi.single i 1)) i false, ?_, ?_⟩
    · simp [unitStep, hback]
    · rw [blockContour_eq_axisPath h hσ hw rfl, blockContour_eq_axisPath h hτ hτm rfl]
      refine axisPath_steps_snoc _ (axisMoves_snoc _ σ i false (fun m hm => (hne m hm).symm)
        (fun m hm => ?_) (axisSegment_snoc_backward _ i ?_ ?_))
      · rw [add_single_apply_of_ne _ _ hm.ne]
        exact hzero m hm
      · rw [add_single_apply_self]
        omega
      · rw [add_single_apply_self]
        ring
theorem blockTree_subset [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S 1 ℓ ε ε')
    (y : LatticeSite ℓ ε') : blockTree S h y ⊆ blockTreeByCoordinates S ε y := by
  rintro b ⟨x, hx, t, ht, rfl⟩
  have hspec := Classical.choose_spec hx
  set σ := Classical.choose hx with hσdef
  have hr : InBlockIndexRange S 1 σ := hspec.1
  have h1 : t ∈ stepsOfMoves (h.toFineSite y + gridPoint ℓ ε 0)
      ((List.finRange S.d).reverse.flatMap (axisSegment σ)) := by
    rw [gridPoint_zero, add_zero]
    exact ht
  obtain ⟨ρ, i, hb, hρ, hρ', hz⟩ := links_of_stepsOfMoves (h.toFineSite y) σ _
    (pairwise_gt_reverse_finRange S.d) 0
    (fun m => by
      simp only [Pi.zero_apply]
      by_cases hs : 0 ≤ σ m
      · exact Or.inl ⟨le_rfl, hs⟩
      · exact Or.inr ⟨by omega, le_rfl⟩)
    (fun _ _ _ _ => rfl) h1
  rw [hb]
  refine ⟨(linkInside_iff _ _).mpr
    ⟨(mem_blockOf_iff h _ _).mpr ⟨ρ, inBlockIndexRange_of_between hr hρ, rfl⟩,
      (mem_blockOf_iff h _ _).mpr ⟨_, inBlockIndexRange_of_between hr hρ',
        gridPoint_add_latticeStep h y ρ i⟩⟩, fun m hm => ?_⟩
  refine ⟨fun κ => (ρ κ : ℝ) * ε, ?_, ?_⟩
  · exact (add_sub_cancel_left _ _).symm
  · simp [hz m hm]
theorem pathIntegral_eq_zero {d : ℕ} {ℓ : Fin d → ℝ} {ε : ℝ} (B : Cochain1 ℓ ε)
    (Γ : LatticePath ℓ ε) (hB : ∀ t ∈ Γ.steps, B t.link = 0) : pathIntegral B Γ = 0 := by
  unfold pathIntegral
  apply List.sum_eq_zero
  intro c hc
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
  simp [hB t ht]
theorem blockTreeCoordinateFormula [IsCommensurateSpacing ℓ ε] (h : IsBlockSpacing S 1 ℓ ε ε') :
    BlockTreeCoordinateFormula S h := by
  intro y
  have hsup : blockTreeByCoordinates S ε y ⊆ blockTree S h y := by
    intro b hb
    obtain ⟨x, x', hx, hx', t, rfl, he⟩ := exists_blockContour_snoc h hb
    exact ⟨x', hx', t, by rw [he]; simp, rfl⟩
  have heq : blockTree S h y = blockTreeByCoordinates S ε y :=
    Set.Subset.antisymm (blockTree_subset h y) hsup
  refine ⟨heq, fun b hb => (blockTree_subset h y hb).1,
    fun B => ⟨fun hB x hx => ?_, fun hB b hb => ?_⟩⟩
  · exact pathIntegral_eq_zero B _ fun t ht => hB t.link ⟨x, hx, t, ht, rfl⟩
  · obtain ⟨x, x', hx, hx', t, rfl, he⟩ := exists_blockContour_snoc h (blockTree_subset h y hb)
    have h₁ := hB x hx
    have h₂ := hB x' hx'
    unfold pathIntegral at h₁ h₂
    rw [he, List.map_append, List.sum_append, h₁] at h₂
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      zero_add] at h₂
    split_ifs at h₂
    · exact h₂
    · exact neg_eq_zero.mp h₂
end Trees
end BlockGeometry
theorem blockGeometry_holds : BlockGeometry := by
  open BlockGeometry in
  refine ⟨?_, ?_, ?_⟩
  · intro S ℓ ε ε' n _ _ h
    exact ⟨uniqueBlockDecomposition h, blocksPartitionLattice h, blockTranslate h,
      blockNeighborSite h, nestedBlocks h, linkInBlockOrCorridor h, plaquettesOfCorridors h,
      linkDomainEndpoints h, blockPathConnected h, blockAverage0AdjointConstant h,
      divergenceLaplacianFormulas S⟩
  · intro S ℓ ε _ h
    exact trivialBlocks h
  · intro S ℓ ε ε' _ h
    exact blockTreeCoordinateFormula h
end YangMills.Construction.BlockSpin
