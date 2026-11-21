import YangMills.Construction.Dirichlet.ShellCells
import YangMills.Construction.Torus.ChainScales
import YangMills.Construction.Torus.ChainShells
import YangMills.Construction.Torus.CubePartitionProperties
import YangMills.Construction.Torus.NestedCubePartitions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Dirichlet.ShellCells
open YangMills.Construction.Torus
variable {d : ℕ} {S : ℝ}
structure ScaleLevel (L : ℕ) (ξ : ℝ) (M : ℕ) (d : ℕ) (S : ℝ) (n : ℕ) : Prop where
  fine : CubePartition.Properties d S (scaleSpacing L ξ n)
  coarse : CubePartition.Properties d S ((M : ℝ) * scaleSpacing L ξ n)
  nested : NestedCubes.Properties d S ((M : ℝ) * scaleSpacing L ξ n) (scaleSpacing L ξ n)
structure ChainData (L : ℕ) (ξ : ℝ) (M R₁ t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)) : Prop where
  chain : IsSeparatedChain L ξ M R₁ t Ω
  scales : ChainScales.ScaleFacts L ξ M t Ω
  shells : ChainShells.ShellFacts L ξ M t Ω
  level : ∀ n ≤ lastNonemptyIndex Ω, ScaleLevel L ξ M d S n
theorem scaleLevel_of_le (hCube : CubePartition.PropertiesOfIntegerMultiple)
    (hNest : NestedCubes.PropertiesOfOddRefinement) {L : ℕ} {ξ : ℝ} {M R₁ t : ℕ}
    {Ω : ℕ → Set (PeriodicTorus d S)} (hd : 0 < d) (hL : 3 ≤ L) (hodd : Odd L)
    (hB : IsSeparatedChain L ξ M R₁ t Ω) (sf : ChainScales.ScaleFacts L ξ M t Ω)
    {n : ℕ} (hn : n ≤ lastNonemptyIndex Ω) : ScaleLevel L ξ M d S n := by
  obtain ⟨u, -, hM, hmul⟩ := sf.side_even_multiple
  obtain ⟨k, hk, hS⟩ := hmul ((n : ℤ) + (u : ℤ)) (by omega)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hσ : 0 < scaleSpacing L ξ (n : ℤ) := mul_pos (zpow_pos hLpos _) hB.scale_pos
  have hMpos : 0 < M := by rw [hM]; exact pow_pos (by omega) u
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hstep : scaleSpacing L ξ ((n : ℤ) + (u : ℤ)) = (M : ℝ) * scaleSpacing L ξ (n : ℤ) := by
    simp only [scaleSpacing]
    rw [zpow_add₀ hLpos.ne', hM]
    push_cast
    simp only [zpow_natCast]
    ring
  have hSc : S = ((2 * k : ℕ) : ℝ) * ((M : ℝ) * scaleSpacing L ξ (n : ℤ)) := by
    rw [hS, hstep]; push_cast; ring
  have hSf : S = ((2 * k * M : ℕ) : ℝ) * scaleSpacing L ξ (n : ℤ) := by
    rw [hSc]; push_cast; ring
  have hk2 : 2 ≤ 2 * k := by omega
  have hk3 : 2 ≤ 2 * k * M := hk2.trans (Nat.le_mul_of_pos_right _ hMpos)
  have hoddM : Odd M := by rw [hM]; exact hodd.pow
  exact ⟨hCube d S _ (2 * k * M) hd hσ hk3 hSf,
    hCube d S _ (2 * k) hd (mul_pos hMr hσ) hk2 hSc,
    hNest d S _ _ M (2 * k) hd hσ hoddM rfl hk2 hSc⟩
theorem mem_shellSites_iff {L : ℕ} {ξ : ℝ} {Ω : ℕ → Set (PeriodicTorus d S)} {n : ℕ}
    {y : PeriodicTorus d S} :
    y ∈ shellSites L ξ Ω n ↔
      n ≤ lastNonemptyIndex Ω ∧ y ∈ spacingLattice d S (scaleSpacing L ξ n) ∧ y ∈ shell Ω n :=
  Iff.rfl
namespace ChainData
variable {L : ℕ} {ξ : ℝ} {M R₁ t : ℕ} {Ω : ℕ → Set (PeriodicTorus d S)}
theorem antitone (g : ChainData L ξ M R₁ t Ω) {m n : ℕ} (h : m ≤ n) : Ω n ⊆ Ω m :=
  antitone_nat_of_succ_le (f := Ω) (fun k => g.scales.succ_subset k) h
theorem cube_subset_shell (g : ChainData L ξ M R₁ t Ω) {n : ℕ} (hn : n ≤ lastNonemptyIndex Ω)
    {c : Set (PeriodicTorus d S)} (hc : c ∈ cubePartition d S ((M : ℝ) * scaleSpacing L ξ n))
    (h₁ : c ⊆ Ω n) (h₂ : ¬ c ⊆ Ω (n + 1)) : c ⊆ shell Ω n := by
  rw [g.shells.shell_eq_sUnion n hn]
  exact subset_sUnion_of_mem ⟨hc, h₁, h₂⟩
theorem exists_fine_of_mem_shell (g : ChainData L ξ M R₁ t Ω) {n : ℕ}
    (hn : n ≤ lastNonemptyIndex Ω) {p : PeriodicTorus d S} (hp : p ∈ shell Ω n) :
    ∃ c ∈ cubePartition d S ((M : ℝ) * scaleSpacing L ξ n), c ⊆ Ω n ∧ ¬ c ⊆ Ω (n + 1) ∧
      ∃ Q ∈ cubePartition d S (scaleSpacing L ξ n), Q ⊆ c ∧ p ∈ Q := by
  rw [g.shells.shell_eq_sUnion n hn] at hp
  obtain ⟨c, ⟨hc, h₁, h₂⟩, hpc⟩ := hp
  obtain ⟨Q, ⟨hQ, hQc⟩, hpQ⟩ := ((g.level n hn).nested.cube_eq_sUnion c hc).subset hpc
  exact ⟨c, hc, h₁, h₂, Q, hQ, hQc, hpQ⟩
theorem exists_coarse_of_site (g : ChainData L ξ M R₁ t Ω) {n : ℕ} {y : PeriodicTorus d S}
    (hy : y ∈ shellSites L ξ Ω n) :
    ∃ c ∈ cubePartition d S ((M : ℝ) * scaleSpacing L ξ n), c ⊆ Ω n ∧ ¬ c ⊆ Ω (n + 1) ∧
      cubeAt y (scaleSpacing L ξ n) ⊆ c := by
  obtain ⟨hn, hyl, hyL⟩ := mem_shellSites_iff.mp hy
  obtain ⟨c, hc, h₁, h₂, Q, hQ, hQc, hyQ⟩ := g.exists_fine_of_mem_shell hn hyL
  have hcube : cubeAt y (scaleSpacing L ξ n) ∈ cubePartition d S (scaleSpacing L ξ n) :=
    ⟨y, hyl, rfl⟩
  have hfine := (g.level n hn).fine
  have hQe : Q = cubeAt y (scaleSpacing L ξ n) := by
    by_contra hne
    exact hfine.interior_not_mem_of_ne _ hcube Q hQ hne y (hfine.center_mem_interior y hyl) hyQ
  exact ⟨c, hc, h₁, h₂, hQe ▸ hQc⟩
theorem cubeAt_subset_shell (g : ChainData L ξ M R₁ t Ω) {n : ℕ} {y : PeriodicTorus d S}
    (hy : y ∈ shellSites L ξ Ω n) : cubeAt y (scaleSpacing L ξ n) ⊆ shell Ω n := by
  obtain ⟨c, hc, h₁, h₂, hsub⟩ := g.exists_coarse_of_site hy
  exact hsub.trans (g.cube_subset_shell (mem_shellSites_iff.mp hy).1 hc h₁ h₂)
theorem disjoint_interior_cubeComplement (g : ChainData L ξ M R₁ t Ω) {n : ℕ}
    (hn : n ≤ lastNonemptyIndex Ω)
    {c : Set (PeriodicTorus d S)} (hc : c ∈ cubePartition d S ((M : ℝ) * scaleSpacing L ξ n))
    (h₁ : c ⊆ Ω n) :
    Disjoint (interior c) (cubeComplement ((M : ℝ) * scaleSpacing L ξ n) (Ω n)) := by
  rw [Set.disjoint_left]
  rintro p hp ⟨Q, ⟨hQ, hnot⟩, hpQ⟩
  exact (g.level n hn).coarse.interior_not_mem_of_ne c hc Q hQ
    (fun e => hnot (e ▸ h₁)) p hp hpQ
theorem disjoint_interior_next (g : ChainData L ξ M R₁ t Ω) {n : ℕ}
    (hn : n ≤ lastNonemptyIndex Ω)
    {c : Set (PeriodicTorus d S)} (hc : c ∈ cubePartition d S ((M : ℝ) * scaleSpacing L ξ n))
    (h₁ : c ⊆ Ω n) (h₂ : ¬ c ⊆ Ω (n + 1)) : Disjoint (interior c) (Ω (n + 1)) :=
  (g.level n hn).coarse.disjoint_interior (Ω n) (Ω (n + 1)) (g.chain.isCubeUnion n hn)
    (g.shells.succ_isCubeUnion n hn) (g.scales.succ_subset n) c hc h₁ h₂
theorem disjoint_interior_shell (g : ChainData L ξ M R₁ t Ω) {n : ℕ}
    (hn : n ≤ lastNonemptyIndex Ω)
    {c : Set (PeriodicTorus d S)} (hc : c ∈ cubePartition d S ((M : ℝ) * scaleSpacing L ξ n))
    (h₁ : c ⊆ Ω n) (h₂ : ¬ c ⊆ Ω (n + 1)) {m : ℕ} (hmt : m ≤ t) (hne : m ≠ n) :
    Disjoint (interior c) (shell Ω m) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hmT : m ≤ lastNonemptyIndex Ω := by omega
    have hsub : shell Ω m ⊆ cubeComplement ((M : ℝ) * scaleSpacing L ξ n) (Ω n) := by
      intro p hp
      have hp' := (g.shells.shell_subset m hmT hp).2
      rw [(g.level m hmT).coarse.cubeComplement_eq_closure_compl _
        (g.shells.succ_isCubeUnion m hmT)] at hp'
      rw [(g.level n hn).coarse.cubeComplement_eq_closure_compl _ (g.chain.isCubeUnion n hn)]
      exact closure_mono (compl_subset_compl.mpr (g.antitone (by omega))) hp'
    exact (g.disjoint_interior_cubeComplement hn hc h₁).mono_right hsub
  · by_cases hmT : m ≤ lastNonemptyIndex Ω
    · have hsub : shell Ω m ⊆ Ω (n + 1) := fun p hp =>
        g.antitone (by omega) (g.shells.shell_subset m hmT hp).1
      exact (g.disjoint_interior_next hn hc h₁ h₂).mono_right hsub
    · rw [g.shells.shell_eq_empty m (by omega) hmt]
      exact disjoint_empty _
theorem disjoint_interior_cubeAt_shell (g : ChainData L ξ M R₁ t Ω) {n : ℕ}
    {y : PeriodicTorus d S} (hy : y ∈ shellSites L ξ Ω n) {m : ℕ} (hmt : m ≤ t) (hne : m ≠ n) :
    Disjoint (interior (cubeAt y (scaleSpacing L ξ n))) (shell Ω m) := by
  obtain ⟨c, hc, h₁, h₂, hsub⟩ := g.exists_coarse_of_site hy
  exact (g.disjoint_interior_shell (mem_shellSites_iff.mp hy).1 hc h₁ h₂ hmt hne).mono_left
    (interior_mono hsub)
theorem mem_interior_cubeAt (g : ChainData L ξ M R₁ t Ω) {n : ℕ} {y : PeriodicTorus d S}
    (hy : y ∈ shellSites L ξ Ω n) : y ∈ interior (cubeAt y (scaleSpacing L ξ n)) :=
  (g.level n (mem_shellSites_iff.mp hy).1).fine.center_mem_interior y
    (mem_shellSites_iff.mp hy).2.1
theorem shellIndex_of_mem (g : ChainData L ξ M R₁ t Ω) {n : ℕ} {y : PeriodicTorus d S}
    (hy : y ∈ shellSites L ξ Ω n) : shellIndex L ξ Ω y = n := by
  have hset : {k | y ∈ shellSites L ξ Ω k} = {n} := by
    ext k
    constructor
    · intro hk
      by_contra hne
      obtain ⟨hkT, -, hkL⟩ := mem_shellSites_iff.mp hk
      exact Set.disjoint_left.mp
        (g.disjoint_interior_cubeAt_shell hy (hkT.trans g.scales.lastNonemptyIndex_le) hne)
        (g.mem_interior_cubeAt hy) hkL
    · intro hk
      rw [mem_singleton_iff.mp hk]
      exact hy
  unfold shellIndex
  rw [hset]
  exact csInf_singleton n
theorem siteCube_eq (g : ChainData L ξ M R₁ t Ω) {n : ℕ} {y : PeriodicTorus d S}
    (hy : y ∈ shellSites L ξ Ω n) : siteCube L ξ Ω y = cubeAt y (scaleSpacing L ξ n) := by
  unfold siteCube shellSpacing
  rw [g.shellIndex_of_mem hy]
theorem shellCellFacts (g : ChainData L ξ M R₁ t Ω) {n : ℕ} (hn : n ≤ lastNonemptyIndex Ω) :
    ShellCellFacts L ξ M t Ω n where
  shellIndex_eq _ hy := g.shellIndex_of_mem hy
  cells_eq := by
    have hfine := (g.level n hn).fine
    ext Q
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [g.siteCube_eq hy]
      exact ⟨⟨y, (mem_shellSites_iff.mp hy).2.1, rfl⟩, g.cubeAt_subset_shell hy⟩
    · rintro ⟨⟨c, hc, rfl⟩, hsub⟩
      have hcm : c ∈ shellSites L ξ Ω n :=
        mem_shellSites_iff.mpr ⟨hn, hc, hsub (interior_subset (hfine.center_mem_interior c hc))⟩
      exact ⟨c, hcm, (g.siteCube_eq hcm).symm⟩
  shell_eq_iUnion := by
    have hfine := (g.level n hn).fine
    apply Subset.antisymm
    · intro p hp
      obtain ⟨c, hc, h₁, h₂, Q, hQ, hQc, hpQ⟩ := g.exists_fine_of_mem_shell hn hp
      obtain ⟨z, hz, rfl⟩ := hQ
      have hzL : z ∈ shell Ω n := g.cube_subset_shell hn hc h₁ h₂
        (hQc (interior_subset (hfine.center_mem_interior z hz)))
      have hzm : z ∈ shellSites L ξ Ω n := mem_shellSites_iff.mpr ⟨hn, hz, hzL⟩
      exact mem_iUnion₂.mpr ⟨z, hzm, by rw [g.siteCube_eq hzm]; exact hpQ⟩
    · exact iUnion₂_subset fun y hy => by
        rw [g.siteCube_eq hy]
        exact g.cubeAt_subset_shell hy
  disjoint_cubeComplement y hy := by
    obtain ⟨c, hc, h₁, -, hsub⟩ := g.exists_coarse_of_site hy
    rw [g.siteCube_eq hy]
    exact (g.disjoint_interior_cubeComplement hn hc h₁).mono_left (interior_mono hsub)
  disjoint_nextDomain y hy := by
    obtain ⟨c, hc, h₁, h₂, hsub⟩ := g.exists_coarse_of_site hy
    rw [g.siteCube_eq hy]
    exact (g.disjoint_interior_next hn hc h₁ h₂).mono_left (interior_mono hsub)
  disjoint_otherShell y hy m hmt hne := by
    rw [g.siteCube_eq hy]
    exact g.disjoint_interior_cubeAt_shell hy hmt hne
  disjoint_otherCell y hy y' hy' hne := by
    obtain ⟨m, hmt, hm⟩ := hy'
    rw [g.siteCube_eq hy, g.siteCube_eq hm]
    by_cases hmn : m = n
    · rw [hmn] at hm
      have hfine := (g.level n hn).fine
      have hyl := (mem_shellSites_iff.mp hy).2.1
      have hyl' := (mem_shellSites_iff.mp hm).2.1
      have hinj : cubeAt y' (scaleSpacing L ξ n) ≠ cubeAt y (scaleSpacing L ξ n) :=
        fun e => hne (hfine.cubeAt_injective y' hyl' y hyl e)
      rw [hmn, Set.disjoint_left]
      intro p hp hp'
      exact hfine.interior_not_mem_of_ne _ ⟨y, hyl, rfl⟩ _ ⟨y', hyl', rfl⟩ hinj p hp hp'
    · exact (g.disjoint_interior_cubeAt_shell hy hmt hmn).mono_right (g.cubeAt_subset_shell hm)
  mem_interior_shell y hy := interior_mono (g.cubeAt_subset_shell hy) (g.mem_interior_cubeAt hy)
end ChainData
theorem allShellCellFacts_holds (hShells : ChainShells.ShellsStatement)
    (hScales : ChainScales.ScalesStatement)
    (hCube : CubePartition.PropertiesOfIntegerMultiple)
    (hNest : NestedCubes.PropertiesOfOddRefinement) : AllShellCellFacts := by
  intro d L S ξ M R₁ t Ω hd hL hodd hB n hn
  have sf := hScales d L S ξ M R₁ t Ω (by omega) hB
  have g : ChainData L ξ M R₁ t Ω :=
    ⟨hB, sf, hShells d L S ξ M R₁ t Ω hd hL hodd hB,
      fun _ hk => scaleLevel_of_le hCube hNest hd hL hodd hB sf hk⟩
  exact g.shellCellFacts hn
end YangMills.Construction.Dirichlet.ShellCells
end
