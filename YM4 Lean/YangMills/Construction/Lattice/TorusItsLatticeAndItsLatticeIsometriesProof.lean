import YangMills.Construction.ReflectionPositivity.OneTorusAllCutoffsPointsAndTheClassC1
import YangMills.Construction.Lattice.TorusItsLatticeAndItsLatticeIsometries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Conventions.StandingParameters.PeriodicFacts
variable (P : StandingParameters)
theorem L_pos : (0 : ℝ) < (P.L : ℝ) := by
  have h := P.isAdmissible.2
  have h' : 0 < P.L := by omega
  exact_mod_cast h'
theorem cutoffMesh_ne_zero : P.cutoffMesh ≠ 0 := by
  unfold StandingParameters.cutoffMesh PeriodicLattice.meshSize
  exact (zpow_pos (L_pos P) _).ne'
theorem torusSide_eq_cutoffMesh_mul :
    PeriodicLattice.torusSide P.L P.m =
      P.cutoffMesh * (2 * (P.L : ℝ) ^ ((P.m : ℕ) + (P.K : ℕ))) := by
  have hL : (P.L : ℝ) ≠ 0 := (L_pos P).ne'
  unfold StandingParameters.cutoffMesh PeriodicLattice.meshSize PeriodicLattice.torusSide
  rw [zpow_neg, zpow_natCast, pow_add]
  field_simp
theorem sideOverMeshAndSiteLifts_holds : P.SideOverMeshAndSiteLifts := by
  have hmesh := cutoffMesh_ne_zero P
  have hside := torusSide_eq_cutoffMesh_mul P
  have hratio : PeriodicLattice.torusSide P.L P.m / P.cutoffMesh =
      2 * (P.L : ℝ) ^ ((P.m : ℕ) + (P.K : ℕ)) := by
    rw [hside, mul_div_cancel_left₀ _ hmesh]
  have hsub : P.periodLattice ⊆ P.meshLatticeVectors := by
    rintro _ ⟨k, rfl⟩
    refine ⟨fun ν => 2 * (P.L : ℤ) ^ ((P.m : ℕ) + (P.K : ℕ)) * k ν, ?_⟩
    funext ν
    simp only [TestFunctions.latticeTranslate]
    rw [hside]
    push_cast
    ring
  refine ⟨hratio, ⟨2 * (P.L : ℤ) ^ ((P.m : ℕ) + (P.K : ℕ)), ?_⟩, hsub, fun v => ⟨?_, ?_⟩⟩
  · rw [hratio]
    push_cast
    rfl
  · rintro ⟨a, ha⟩
    have hproj : TorusMetric.torusProj (PeriodicLattice.torusSide P.L P.m) v =
        TorusMetric.torusProj (PeriodicLattice.torusSide P.L P.m)
          (TestFunctions.latticeTranslate P.cutoffMesh a) := by
      funext ν
      refine (ha ν).trans ?_
      show (((a ν : ℝ) * P.cutoffMesh : ℝ) : AddCircle (PeriodicLattice.torusSide P.L P.m)) =
        ((P.cutoffMesh * (a ν : ℝ) : ℝ) : AddCircle (PeriodicLattice.torusSide P.L P.m))
      rw [mul_comm]
    obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq hproj
    obtain ⟨a', ha'⟩ := hsub ⟨k, rfl⟩
    exact ⟨a + a', by rw [TestFunctions.latticeTranslate_add, ha', hk]⟩
  · rintro ⟨a, rfl⟩
    refine ⟨a, fun ν => ?_⟩
    show ((P.cutoffMesh * (a ν : ℝ) : ℝ) : AddCircle (PeriodicLattice.torusSide P.L P.m)) =
      (((a ν : ℝ) * P.cutoffMesh : ℝ) : AddCircle (PeriodicLattice.torusSide P.L P.m))
    rw [mul_comm]
theorem torusProj_add (v w : Fin 4 → ℝ) :
    TorusMetric.torusProj (PeriodicLattice.torusSide P.L P.m) (v + w) =
      TorusMetric.torusProj (PeriodicLattice.torusSide P.L P.m) v +
        TorusMetric.torusProj (PeriodicLattice.torusSide P.L P.m) w := by apply _root_.YangMills.Construction.ReflectionPositivity.TorusCutoffs.proj_add <;> assumption
theorem torusProjIsSurjectiveHom_holds : P.TorusProjIsSurjectiveHom := by
  refine ⟨fun p p' => add_comm p p', torusProj_add P, fun p => ?_,
    fun v ζ => (torusProj_add P v ζ).symm⟩
  choose w hw using fun ν => QuotientAddGroup.mk_surjective (p ν)
  exact ⟨w, funext hw⟩
theorem mem_cutoffLatticeIsometries_iff (g : P.Torus ≃ P.Torus) :
    g ∈ P.cutoffLatticeIsometries ↔ PeriodicLattice.IsFlatIsometry g ∧
      g '' (PeriodicLattice.sublattice P.L P.m ((P.K : ℕ) : ℤ) : Set P.Torus) =
        PeriodicLattice.sublattice P.L P.m ((P.K : ℕ) : ℤ) :=
  Iff.rfl
theorem one_mem_cutoffLatticeIsometries : (1 : Equiv.Perm P.Torus) ∈ P.cutoffLatticeIsometries := by
  refine (mem_cutoffLatticeIsometries_iff P _).2 ⟨fun _ _ => rfl, ?_⟩
  simp
theorem mul_mem_cutoffLatticeIsometries {g g' : Equiv.Perm P.Torus}
    (h : g ∈ P.cutoffLatticeIsometries) (h' : g' ∈ P.cutoffLatticeIsometries) :
    g * g' ∈ P.cutoffLatticeIsometries := by
  obtain ⟨hg, hs⟩ := (mem_cutoffLatticeIsometries_iff P g).1 h
  obtain ⟨hg', hs'⟩ := (mem_cutoffLatticeIsometries_iff P g').1 h'
  refine (mem_cutoffLatticeIsometries_iff P _).2 ⟨fun p q => (hg _ _).trans (hg' _ _), ?_⟩
  rw [Equiv.Perm.coe_mul, Set.image_comp, hs', hs]
theorem inv_mem_cutoffLatticeIsometries {g : Equiv.Perm P.Torus}
    (h : g ∈ P.cutoffLatticeIsometries) : g⁻¹ ∈ P.cutoffLatticeIsometries := by
  obtain ⟨hg, hs⟩ := (mem_cutoffLatticeIsometries_iff P g).1 h
  refine (mem_cutoffLatticeIsometries_iff P _).2 ⟨fun p q => ?_, ?_⟩
  · have e := hg (g⁻¹ p) (g⁻¹ q)
    have hgg : ∀ z, g (g⁻¹ z) = z := fun z => g.apply_symm_apply z
    rw [hgg, hgg] at e
    exact e.symm
  · calc (g⁻¹ : Equiv.Perm P.Torus) ''
          (PeriodicLattice.sublattice P.L P.m ((P.K : ℕ) : ℤ) : Set P.Torus)
        = (g⁻¹ : Equiv.Perm P.Torus) ''
            (g '' (PeriodicLattice.sublattice P.L P.m ((P.K : ℕ) : ℤ) : Set P.Torus)) := by
          rw [hs]
      _ = PeriodicLattice.sublattice P.L P.m ((P.K : ℕ) : ℤ) := by
          rw [← Set.image_comp]
          simp
theorem cutoffIsometriesFormGroup_holds : P.CutoffIsometriesFormGroup :=
  ⟨one_mem_cutoffLatticeIsometries P, fun _ _ h h' => mul_mem_cutoffLatticeIsometries P h h',
    fun _ h => inv_mem_cutoffLatticeIsometries P h,
    ⟨{ carrier := P.cutoffLatticeIsometries
       mul_mem' := fun h h' => mul_mem_cutoffLatticeIsometries P h h'
       one_mem' := one_mem_cutoffLatticeIsometries P
       inv_mem' := fun h => inv_mem_cutoffLatticeIsometries P h }, rfl⟩⟩
theorem torusLatticeAndIsometryFacts_holds (h : CenteredLiftUnique) :
    TorusLatticeAndIsometryFacts := fun P =>
  ⟨sideOverMeshAndSiteLifts_holds P, torusProjIsSurjectiveHom_holds P, h P,
    cutoffIsometriesFormGroup_holds P⟩
end YangMills.Construction.Conventions.StandingParameters.PeriodicFacts
end
