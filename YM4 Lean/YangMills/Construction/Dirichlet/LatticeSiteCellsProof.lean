import YangMills.Construction.Dirichlet.LatticeSiteCells
import YangMills.Construction.Dirichlet.ShellCells
import YangMills.Construction.Torus.ChainScales
import YangMills.Construction.Torus.ChainShells
import YangMills.Construction.Torus.CubePartitionProperties
import YangMills.Construction.Torus.NestedCubePartitions
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.Dirichlet.LatticeSiteCells
theorem scaleSpacing_zero (L : ℕ) (ξ : ℝ) : scaleSpacing L ξ ((0 : ℕ) : ℤ) = ξ := by
  simp [scaleSpacing]
theorem scaleSpacing_natCast (L n : ℕ) (ξ : ℝ) :
    scaleSpacing L ξ (n : ℤ) = ((L ^ n : ℕ) : ℝ) * ξ := by
  simp [scaleSpacing]
theorem allLatticeSiteFacts_holds (hScales : YangMills.Construction.Torus.ChainScales.ScalesStatement)
    (hShells : YangMills.Construction.Torus.ChainShells.ShellsStatement)
    (hCells : YangMills.Construction.Dirichlet.ShellCells.AllShellCellFacts)
    (hPartition : YangMills.Construction.Torus.CubePartition.PropertiesOfIntegerMultiple)
    (hRefine : YangMills.Construction.Torus.NestedCubes.PropertiesOfOddRefinement) :
    AllLatticeSiteFacts := by
  intro d L S ξ M R₁ t Ω hd hL hodd hchain
  have scales := hScales d L S ξ M R₁ t Ω (by omega) hchain
  have shells := hShells d L S ξ M R₁ t Ω hd hL hodd hchain
  have cells := hCells d L S ξ M R₁ t Ω hd hL hodd hchain
  have hξ : 0 < ξ := hchain.scale_pos
  obtain ⟨u, -, hMu, heven⟩ := scales.side_even_multiple
  obtain ⟨k₀, hk₀, hS₀⟩ := heven ((0 : ℕ) : ℤ) (by omega)
  rw [scaleSpacing_zero] at hS₀
  have fine : YangMills.Construction.Torus.CubePartition.Properties d S ξ :=
    hPartition d S ξ (2 * k₀) hd hξ (by omega) (by rw [hS₀]; push_cast; ring)
  have cube_of_point : ∀ x ∈ spacingLattice d S ξ, ∀ Q ∈ cubePartition d S ξ, x ∈ Q →
      Q = cubeAt x ξ := by
    intro x hx Q hQ hxQ
    by_contra hne
    exact fine.interior_not_mem_of_ne (cubeAt x ξ) ⟨x, hx, rfl⟩ Q hQ hne x
      (fine.center_mem_interior x hx) hxQ
  constructor
  · intro x hx hx0
    rw [shells.zero_eq_iUnion_shell] at hx0
    simp only [mem_iUnion, mem_Iic, exists_prop] at hx0
    obtain ⟨m, hm, hxm⟩ := hx0
    have cm := cells m hm
    rw [cm.shell_eq_iUnion] at hxm
    simp only [mem_iUnion, exists_prop] at hxm
    obtain ⟨y, hy, hxy⟩ := hxm
    have hcell : siteCube L ξ Ω y = cubeAt y (scaleSpacing L ξ (m : ℤ)) := by
      simp only [siteCube, shellSpacing, cm.shellIndex_eq y hy]
    obtain ⟨k, hk, hS⟩ := heven (m : ℤ) (by omega)
    have refine : YangMills.Construction.Torus.NestedCubes.Properties d S
        (scaleSpacing L ξ (m : ℤ)) ξ :=
      hRefine d S (scaleSpacing L ξ (m : ℤ)) ξ (L ^ m) (2 * k) hd hξ hodd.pow
        (scaleSpacing_natCast L m ξ) (by omega) (by rw [hS]; push_cast; ring)
    have hyl : y ∈ spacingLattice d S (scaleSpacing L ξ (m : ℤ)) := hy.2.1
    have hxint : x ∈ interior (siteCube L ξ Ω y) := by
      rw [hcell]
      rw [hcell] at hxy
      exact refine.inter_cube_subset_interior y hyl ⟨hx, hxy⟩
    refine ⟨y, ⟨m, (hm.trans scales.lastNonemptyIndex_le), hy⟩, hxint, ?_, ?_, ?_⟩
    · intro y' hy' hne hxy'
      exact disjoint_left.1 (cm.disjoint_otherCell y hy y' hy' hne) hxint hxy'
    · have hcube : cubeAt y (scaleSpacing L ξ (m : ℤ)) ∈
          cubePartition d S (scaleSpacing L ξ (m : ℤ)) := ⟨y, hyl, rfl⟩
      have hxy₂ := hxy
      rw [hcell, refine.cube_eq_sUnion _ hcube] at hxy₂
      obtain ⟨Q, ⟨hQ, hQy⟩, hxQ⟩ := hxy₂
      rw [hcell, ← cube_of_point x hx Q hQ hxQ]
      exact hQy
    · intro m' hy'
      have hm' : m' = m := by
        have hm'T : m' ≤ lastNonemptyIndex Ω := hy'.1
        rw [← (cells m' hm'T).shellIndex_eq y hy', cm.shellIndex_eq y hy]
      subst hm'
      refine ⟨?_, ?_⟩
      · rw [cm.shell_eq_iUnion]
        simp only [mem_iUnion, exists_prop]
        exact ⟨y, hy, hxy⟩
      · intro m'' hm'' hne hxl
        exact disjoint_left.1 (cm.disjoint_otherShell y hy m'' hm'' hne) hxint hxl
  · intro x hx hx0
    obtain ⟨k, hk, hS⟩ := heven (u : ℤ) (by omega)
    have hMξ : (M : ℝ) * scaleSpacing L ξ ((0 : ℕ) : ℤ) = scaleSpacing L ξ (u : ℤ) := by
      rw [scaleSpacing_zero, scaleSpacing_natCast, hMu]
    have refine : YangMills.Construction.Torus.NestedCubes.Properties d S
        (scaleSpacing L ξ (u : ℤ)) ξ :=
      hRefine d S (scaleSpacing L ξ (u : ℤ)) ξ (L ^ u) (2 * k) hd hξ hodd.pow
        (scaleSpacing_natCast L u ξ) (by omega) (by rw [hS]; push_cast; ring)
    have hunion : IsCubeUnion (scaleSpacing L ξ (u : ℤ)) (Ω 0) := by
      have := hchain.isCubeUnion 0 (Nat.zero_le _)
      rwa [hMξ] at this
    obtain ⟨𝒞, h𝒞, hΩ⟩ := refine.isCubeUnion_of_coarse _ hunion
    rw [disjoint_left]
    intro p hp hp0
    rw [hΩ] at hp0
    obtain ⟨Q, hQ, hpQ⟩ := hp0
    by_cases hne : Q = cubeAt x ξ
    · apply hx0
      rw [hΩ]
      exact ⟨Q, hQ, hne ▸ interior_subset (fine.center_mem_interior x hx)⟩
    · exact fine.interior_not_mem_of_ne (cubeAt x ξ) ⟨x, hx, rfl⟩ Q (h𝒞 hQ) hne p hp hpQ
end YangMills.Construction.Dirichlet.LatticeSiteCells
end
