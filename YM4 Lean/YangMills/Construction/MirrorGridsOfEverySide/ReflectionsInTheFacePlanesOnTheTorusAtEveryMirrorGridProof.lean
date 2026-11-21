import YangMills.Construction.ChessboardTori.CellFunctionFamiliesInTheTransferPictureProof
import YangMills.Construction.MirrorGridsOfEverySide.CellsOnTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.GroupOnTheCellsOfTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.ReflectionsInTheFacePlanesOnTheTorusAtEveryMirrorGrid
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
open ChessboardTori (ReflectionGrid orientationSign)
namespace MirrorGridsAllSides
namespace TorusWallReflections
variable {D : GridSetup} (g : ReflectionGrid D)
theorem reflect_eq_update (μ : Fin 4) (s : ℤ) (x : AmbientSpace) :
    g.reflect μ s x = Function.update x μ (2 * wallLevel g μ s - x μ) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [ReflectionGrid.reflect, wallLevel, ChessboardTori.coordVec]
    ring
  · simp [ReflectionGrid.reflect, ChessboardTori.coordVec, Pi.single_eq_of_ne h,
      Function.update_of_ne h]
theorem reflect_eq_reflectVec (μ : Fin 4) (s : ℤ) :
    g.reflect μ s = (D.mirrors μ).reflectVec (wallLevel g μ s) := by
  funext x
  have h := (D.mirrors μ).reflectVec_eq_sub (wallLevel g μ s) x
  rw [h, reflect_eq_update]
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp [PeriodicLattice.coordVec]
    ring
  · simp [PeriodicLattice.coordVec, Pi.single_eq_of_ne hν, Function.update_of_ne hν]
theorem descends (μ : Fin 4) (s : ℤ) : D.Descends (g.reflect μ s) (torusWallReflection g μ s) := by
  rw [reflect_eq_reflectVec]
  exact D.descends_reflect μ _
theorem torusWallReflection_proj (μ : Fin 4) (s : ℤ) (x : AmbientSpace) :
    torusWallReflection g μ s (D.proj x) = D.proj (g.reflect μ s x) :=
  congrFun (descends g μ s) x
theorem proj_update_add (x : AmbientSpace) (μ : Fin 4) (t : ℤ) :
    D.proj (Function.update x μ (x μ + PeriodicLattice.torusSide D.L D.m * t)) =
      D.proj x := by
  have h := TestFunctions.torusProj_add_latticeTranslate (PeriodicLattice.torusSide D.L D.m) x (Pi.single μ t)
  have e : Function.update x μ (x μ + PeriodicLattice.torusSide D.L D.m * t) =
      x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) (Pi.single μ t) := by
    funext ν
    by_cases hν : ν = μ
    · subst hν
      simp [TestFunctions.latticeTranslate]
    · simp [TestFunctions.latticeTranslate, Pi.single_eq_of_ne hν, Function.update_of_ne hν]
  rw [e]
  exact h
theorem exists_int_of_proj_eq {x y : AmbientSpace} (h : D.proj x = D.proj y) (μ : Fin 4) :
    ∃ t : ℤ, x μ = y μ + PeriodicLattice.torusSide D.L D.m * t := by
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq h
  exact ⟨k μ, by rw [hk]; simp [TestFunctions.latticeTranslate]⟩
theorem mem_mirrorSet_iff (μ : Fin 4) (c : ℝ) (y : D.Torus) :
    y ∈ (D.mirrors μ).mirrorSet c ↔ ∃ z : AmbientSpace, D.proj z = y ∧
      (z μ = c ∨ z μ = c + PeriodicLattice.torusSide D.L D.m / 2) := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, rfl, hz⟩
  · rintro ⟨z, rfl, hz⟩
    exact ⟨z, hz, rfl⟩
theorem fixedPoints_eq_mirrorSet (μ : Fin 4) (s : ℤ) :
    {y | torusWallReflection g μ s y = y} = (D.mirrors μ).mirrorSet (wallLevel g μ s) := by
  ext y
  rw [mem_mirrorSet_iff, Set.mem_ofPred_eq]
  constructor
  · intro hy
    have hlift : D.proj (TestFunctions.liftPoint (ℓ := PeriodicLattice.torusSide D.L D.m) y) = y :=
      TestFunctions.torusProj_liftPoint y
    set x := TestFunctions.liftPoint (ℓ := PeriodicLattice.torusSide D.L D.m) y with hx
    rw [← hlift, torusWallReflection_proj] at hy
    obtain ⟨t, ht⟩ := exists_int_of_proj_eq hy μ
    rw [reflect_eq_update] at ht
    simp only [Function.update_self] at ht
    rcases Int.even_or_odd' t with ⟨u, rfl | rfl⟩
    · refine ⟨Function.update x μ (x μ + PeriodicLattice.torusSide D.L D.m * u), ?_, Or.inl ?_⟩
      · rw [proj_update_add, hlift]
      · simp only [Function.update_self]
        push_cast at ht
        linarith
    · refine ⟨Function.update x μ (x μ + PeriodicLattice.torusSide D.L D.m * (u + 1 : ℤ)), ?_, Or.inr ?_⟩
      · rw [proj_update_add, hlift]
      · simp only [Function.update_self]
        push_cast at ht ⊢
        linarith
  · rintro ⟨z, rfl, hz | hz⟩
    · rw [torusWallReflection_proj, reflect_eq_update, hz]
      congr 1
      funext ν
      by_cases hν : ν = μ
      · subst hν
        simp [hz]
        ring
      · simp [Function.update_of_ne hν]
    · rw [torusWallReflection_proj, reflect_eq_update, hz, ← proj_update_add z μ (-1)]
      congr 1
      funext ν
      by_cases hν : ν = μ
      · subst hν
        simp [hz]
        ring
      · simp [Function.update_of_ne hν]
theorem coords_of_mem_interior {k : Fin 4 → ℤ} {x : AmbientSpace} (hx : x ∈ interior (g.cell k))
    (μ : Fin 4) :
    g.origin μ + g.cellSide * k μ < x μ ∧ x μ < g.origin μ + g.cellSide * k μ + g.cellSide := by apply _root_.YangMills.Construction.ChessboardTori.TransferSetupCellFamilies.lt_coord_lt_of_mem_interior_cell <;> assumption
theorem reflect_mem_cell (μ : Fin 4) (s : ℤ) {k : Fin 4 → ℤ} {x : AmbientSpace} (hx : x ∈ g.cell k) :
    g.reflect μ s x ∈ g.cell (Function.update k μ (2 * s - 1 - k μ)) := by
  intro ν
  have h := hx ν
  rw [reflect_eq_update]
  by_cases hν : ν = μ
  · subst hν
    obtain ⟨h₁, h₂⟩ := h
    simp only [Function.update_self, wallLevel, mem_Icc]
    push_cast
    constructor <;> linarith
  · simpa [Function.update_of_ne hν] using h
theorem reflect_image_cell (μ : Fin 4) (s : ℤ) (k : Fin 4 → ℤ) :
    g.reflect μ s '' g.cell k = g.cell (Function.update k μ (2 * s - 1 - k μ)) := by
  refine Subset.antisymm ?_ fun z hz => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact reflect_mem_cell g μ s hx
  · refine ⟨g.reflect μ s z, ?_, g.reflect_involutive μ s z⟩
    have h := reflect_mem_cell g μ s hz
    have e : Function.update (Function.update k μ (2 * s - 1 - k μ)) μ
        (2 * s - 1 - Function.update k μ (2 * s - 1 - k μ) μ) = k := by
      funext ν
      by_cases hν : ν = μ
      · subst hν
        simp
      · simp [Function.update_of_ne hν]
    rwa [e] at h
theorem orientationSign_reflect (μ : Fin 4) (s : ℤ) : orientationSign (g.reflect μ s) = -1 := by
  set R : AmbientSpace →ₗ[ℝ] AmbientSpace :=
    Matrix.toLin' (Matrix.diagonal fun ν : Fin 4 => if ν = μ then (-1 : ℝ) else 1) with hRdef
  have hR : ChessboardTori.HasLinearComponent (g.reflect μ s) R := by
    refine ⟨(2 * wallLevel g μ s) • ChessboardTori.coordVec μ, fun x => ?_⟩
    rw [reflect_eq_update]
    funext ν
    by_cases hν : ν = μ
    · subst hν
      simp [hRdef, Matrix.mulVec_diagonal, ChessboardTori.coordVec]
      ring
    · simp [hRdef, Matrix.mulVec_diagonal, ChessboardTori.coordVec, hν]
  have hx : ChessboardTori.HasLinearComponent (g.reflect μ s)
      (ChessboardTori.linearComponent (g.reflect μ s)) :=
    Classical.epsilon_spec (p := ChessboardTori.HasLinearComponent (g.reflect μ s)) ⟨R, hR⟩
  obtain ⟨w, hw⟩ := hx
  obtain ⟨v, hv⟩ := hR
  have hvw : v = w := by
    have h₁ := hv 0
    have h₂ := hw 0
    simp only [map_zero, zero_add] at h₁ h₂
    exact h₁.symm.trans h₂
  have hlin : ChessboardTori.linearComponent (g.reflect μ s) = R := by
    refine LinearMap.ext fun x => ?_
    have h := (hw x).symm.trans (hv x)
    rw [hvw] at h
    exact add_right_cancel h
  have hdet : LinearMap.det R = -1 := by
    rw [hRdef, LinearMap.det_toLin', Matrix.det_diagonal]
    simp [Finset.prod_ite_eq']
  simp only [orientationSign, hlin, hdet]
  norm_num
end TorusWallReflections
open TorusWallReflections in
theorem allGridsTorusWallReflections_of_cells_of_group
    (h₁ : AllGridsTorusCellStructure)
    (h₂ : AllGridsTorusGroupActsOnCells) :
    AllGridsTorusWallReflections := by
  intro D g hg hℓ μ s
  obtain ⟨⟨n, ⟨h, rfl⟩, hn⟩, -⟩ := h₁ D g hg hℓ
  have hS : 0 < g.cellSide := zpow_pos (by linarith [D.one_lt_factor]) _
  have hℓn : PeriodicLattice.torusSide D.L D.m = ((h : ℝ) + h) * g.cellSide := by
    have e : g.cellsAcross = PeriodicLattice.torusSide D.L D.m / g.cellSide := rfl
    rw [e] at hn
    push_cast at hn
    rw [div_eq_iff hS.ne'] at hn
    exact hn
  have hmem : torusWallReflection g μ s ∈ g.inducedTorusMaps :=
    ⟨g.reflectPerm μ s, Subgroup.subset_closure ⟨(μ, s), rfl⟩, (descends g μ s).symm⟩
  refine ⟨descends g μ s, fixedPoints_eq_mirrorSet g μ s, ?_, ?_, ?_, hmem, ?_⟩
  · refine ⟨g.torusWall μ s, ⟨(μ, s), rfl⟩, g.torusWall μ (s + h), ⟨(μ, s + h), rfl⟩,
      ?_, ?_⟩
    · intro heq
      have hp : D.proj (fun _ => wallLevel g μ s) ∈ g.torusWall μ s :=
        ⟨_, rfl, rfl⟩
      rw [heq] at hp
      obtain ⟨z, hz, hzc⟩ := hp
      obtain ⟨t, ht⟩ := exists_int_of_proj_eq hzc μ
      have hz' : z μ = wallLevel g μ s + ((h : ℝ) * g.cellSide) := by
        have : z μ = g.origin μ + ((s + h : ℤ) : ℝ) * g.cellSide := hz
        rw [this, wallLevel]
        push_cast
        ring
      rw [hz', hℓn] at ht
      have h2 : (h : ℝ) = ((h : ℝ) + h) * t := by
        have := mul_right_cancel₀ hS.ne' (by linarith : (h : ℝ) * g.cellSide = (((h : ℝ) + h) * t) * g.cellSide)
        exact this
      have hh : (h : ℝ) ≠ 0 := by
        intro h0
        rw [h0] at hℓn
        simp at hℓn
        linarith
      have h3 : (1 : ℝ) = 2 * t := by
        apply mul_left_cancel₀ hh
        linarith
      have h4 : (1 : ℤ) = 2 * t := by exact_mod_cast h3
      omega
    · ext y
      rw [mem_mirrorSet_iff]
      constructor
      · rintro ⟨z, rfl, hz | hz⟩
        · exact Or.inl ⟨z, hz, rfl⟩
        · refine Or.inr ⟨z, ?_, rfl⟩
          change z μ = g.origin μ + ((s + h : ℤ) : ℝ) * g.cellSide
          rw [hz, hℓn, wallLevel]
          push_cast
          ring
      · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
        · exact ⟨z, rfl, Or.inl hz⟩
        · refine ⟨z, rfl, Or.inr ?_⟩
          have hz' : z μ = g.origin μ + ((s + h : ℤ) : ℝ) * g.cellSide := hz
          rw [hz', hℓn, wallLevel]
          push_cast
          ring
  · intro k i hi0 hi1 ⟨j, hj⟩
    have hnh : g.cellsAcross = (h : ℝ) + h := by
      rw [hn]
      push_cast
      ring
    rw [hnh] at hi1 hj
    push_cast at hj
    have hk : g.cellSide * k μ = g.cellSide * s + g.cellSide * i + PeriodicLattice.torusSide D.L D.m * j := by
      have hk' : (k μ : ℝ) = s + i + ((h : ℝ) + h) * j := by linarith
      rw [hk', hℓn]
      ring
    have hi : (0 : ℝ) ≤ i := by exact_mod_cast hi0
    have hSi : 0 ≤ g.cellSide * i := mul_nonneg hS.le hi
    constructor
    · intro hle
      rw [hnh] at hle
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hx₁, hx₂⟩ := coords_of_mem_interior g hx μ
      have hup : g.cellSide * ((i : ℝ) + 1) ≤ g.cellSide * h :=
        mul_le_mul_of_nonneg_left (by linarith) hS.le
      refine ⟨Function.update x μ (x μ + PeriodicLattice.torusSide D.L D.m * (-j : ℤ)), ?_,
        proj_update_add x μ (-j)⟩
      have hy : Function.update x μ (x μ + PeriodicLattice.torusSide D.L D.m * (-j : ℤ)) μ =
          x μ + PeriodicLattice.torusSide D.L D.m * (-j : ℤ) := by simp
      change 0 < (1 : ℝ) * (Function.update x μ (x μ + PeriodicLattice.torusSide D.L D.m * (-j : ℤ)) μ -
        wallLevel g μ s) ∧ (1 : ℝ) * (Function.update x μ
          (x μ + PeriodicLattice.torusSide D.L D.m * (-j : ℤ)) μ - wallLevel g μ s) <
          PeriodicLattice.torusSide D.L D.m / 2
      rw [hy, wallLevel]
      push_cast
      have hh2 : PeriodicLattice.torusSide D.L D.m / 2 = g.cellSide * h := by
        rw [hℓn]
        ring
      rw [hh2]
      constructor <;> nlinarith
    · intro hle
      rw [hnh] at hle
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hx₁, hx₂⟩ := coords_of_mem_interior g hx μ
      have hlo : g.cellSide * h ≤ g.cellSide * i := mul_le_mul_of_nonneg_left (by linarith) hS.le
      have hup : g.cellSide * ((i : ℝ) + 1) ≤ g.cellSide * ((h : ℝ) + h) :=
        mul_le_mul_of_nonneg_left (by linarith) hS.le
      refine ⟨Function.update x μ (x μ + PeriodicLattice.torusSide D.L D.m * (-(j + 1) : ℤ)), ?_,
        proj_update_add x μ (-(j + 1))⟩
      have hy : Function.update x μ (x μ + PeriodicLattice.torusSide D.L D.m * (-(j + 1) : ℤ)) μ =
          x μ + PeriodicLattice.torusSide D.L D.m * (-(j + 1) : ℤ) := by simp
      change 0 < (-1 : ℝ) * (Function.update x μ
          (x μ + PeriodicLattice.torusSide D.L D.m * (-(j + 1) : ℤ)) μ - wallLevel g μ s) ∧
        (-1 : ℝ) * (Function.update x μ (x μ + PeriodicLattice.torusSide D.L D.m * (-(j + 1) : ℤ)) μ -
          wallLevel g μ s) < PeriodicLattice.torusSide D.L D.m / 2
      rw [hy, wallLevel]
      push_cast
      have hh2 : PeriodicLattice.torusSide D.L D.m / 2 = g.cellSide * h := by
        rw [hℓn]
        ring
      constructor <;> nlinarith
  · intro k
    rw [← reflect_image_cell, image_image, image_image]
    exact image_congr fun x _ => torusWallReflection_proj g μ s x
  · have hpar := (h₂ D g hg hℓ).2.2.2.1 _ hmem
    have h := hpar ⟨g.reflectPerm μ s, Subgroup.subset_closure ⟨(μ, s), rfl⟩⟩
      (descends g μ s).symm
    exact h.symm.trans (orientationSign_reflect g μ s)
end MirrorGridsAllSides
end YangMills.Construction
end
