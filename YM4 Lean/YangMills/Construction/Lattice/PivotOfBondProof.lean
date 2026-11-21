import YangMills.Construction.Lattice.AxialPathsAndPivots
import YangMills.Construction.Lattice.BareBaseSitesOfTheSchemesProof
import YangMills.Construction.Lattice.PivotOfBond
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace PivotAxis
variable {L m : ℕ}
theorem coe_toSublattice (hL : 0 < L) {j j' : ℤ} (hjj : j ≤ j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
theorem coe_unitStep_eq_smul (hL : 0 < L) {j j' : ℤ} (hjj : j' = j + 1) (ν : Fin 4) :
    ((unitStep L m j ν : Site L m j) : FourTorus L m) =
      (L : ℤ) • ((unitStep L m j' ν : Site L m j') : FourTorus L m) := by
  subst hjj
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hmesh : meshSize L j = ((L : ℤ) • meshSize L (j + 1) : ℝ) := by
    simp only [meshSize, zsmul_eq_mul, Int.cast_natCast]
    rw [neg_add, zpow_add₀ hLne, zpow_neg _ (1 : ℤ), zpow_one]
    field_simp
  funext ρ
  by_cases hρ : ρ = ν
  · subst hρ
    simp only [unitStep, pointOnAxis, Pi.smul_apply, Pi.single_eq_same]
    rw [hmesh]
    rfl
  · simp [unitStep, pointOnAxis, Pi.single_eq_of_ne hρ]
end PivotAxis
theorem pivotOfEveryBond
    (hyp : AxialPathCorridorAndPivotStatement) :
    PivotOfEveryBond := by
  intro s i hi c
  obtain ⟨-, hc⟩ := hyp s i hi
  obtain ⟨huniq, μ, ε, hε, hdisp, hS⟩ := hc c
  obtain ⟨hodd, h13⟩ := s.isAdmissible
  obtain ⟨r, hr⟩ := hodd
  have hLpos : 0 < s.L := by omega
  have hmid : (s.L - 1) / 2 < s.L := by omega
  have hsucc : (s.L + 1) / 2 = (s.L - 1) / 2 + 1 := by omega
  have hmem := (hS.stepBond_mem_bondCorridor_iff ((s.L - 1) / 2)).2 rfl
  have hin : axialPathStepBond c μ ε ((s.L - 1) / 2) ∈
      axialPath (c.source.toSublattice (levelDepth s.K i)) (c.target.toSublattice (levelDepth s.K i)) := by
    rw [hS.axialPath_eq]
    exact List.mem_map.2 ⟨_, List.mem_range.2 hmid, rfl⟩
  have haxis : ∀ (ρ : Fin 4) (σ : ℤ), (σ = 1 ∨ σ = -1) →
      c.target.toSublattice (levelDepth s.K i) - c.source.toSublattice (levelDepth s.K i) =
        (σ * (s.L : ℤ)) • unitStep s.L s.m (levelDepth s.K i) ρ → ρ = μ := by
    intro ρ σ hσ hd
    have habs : |σ * (s.L : ℤ)| = |ε * (s.L : ℤ)| := by
      rcases hσ with rfl | rfl <;> rcases hε with rfl | rfl <;> simp
    have hd' : IsAxialDisplacement (c.source.toSublattice (levelDepth s.K i))
        (c.target.toSublattice (levelDepth s.K i)) ρ (σ * (s.L : ℤ)) :=
      ⟨hd, by rw [habs]; exact hdisp.2⟩
    exact congrArg Prod.fst
      (huniq.unique (y₁ := (ρ, σ * (s.L : ℤ))) (y₂ := (μ, ε * (s.L : ℤ))) hd' hdisp)
  refine ⟨⟨_, ⟨hin, hmem.2⟩, ?_⟩, ?_, hS.pivot_opposite, ?_, hS.pivot_isPositivelyOriented_iff⟩
  · rintro b ⟨hb₁, hb₂⟩
    rw [hS.axialPath_eq] at hb₁
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hb₁
    rw [(hS.stepBond_mem_bondCorridor_iff t).1 ⟨List.mem_range.1 ht, hb₂⟩]
  · rw [IsPivot, hS.pivot_eq]
    exact ⟨hmem.2, hin⟩
  · have hpd : (pivot c : BondAtLevel s.L s.m s.K i).target -
        (pivot c : BondAtLevel s.L s.m s.K i).source =
          ε • unitStep s.L s.m (levelDepth s.K i) μ := by
      rw [hS.pivot_target, hS.pivot_source, add_sub_add_left_eq_sub, ← sub_smul, hsucc]
      congr 1
      push_cast
      ring
    have hdl : c.target.toSublattice (levelDepth s.K i) - c.source.toSublattice (levelDepth s.K i) =
        (s.L : ℤ) • (ε • unitStep s.L s.m (levelDepth s.K i) μ) := by
      rw [smul_smul, mul_comm]
      exact hdisp.1
    have hp : (pivot c : BondAtLevel s.L s.m s.K i).axis = μ := by
      rcases (pivot c : BondAtLevel s.L s.m s.K i).isNeighbour.choose_spec with e | e
      · refine haxis _ 1 (Or.inl rfl) ?_
        rw [hdl, ← hpd, one_mul]
        exact congrArg _ e
      · refine haxis _ (-1) (Or.inr rfl) ?_
        rw [hdl, ← hpd]
        have e' := congrArg (fun x => (s.L : ℤ) • x) e
        simpa [Bond.axis] using e'
    have hcd : c.axis = μ := by
      have hle : levelDepth s.K (i + 1) ≤ levelDepth s.K i := by
        simp only [levelDepth]; push_cast; omega
      have hidx : levelDepth s.K i = levelDepth s.K (i + 1) + 1 := by
        simp only [levelDepth]; push_cast; ring
      have hcoe : ((c.target.toSublattice (levelDepth s.K i) - c.source.toSublattice (levelDepth s.K i) :
          Site s.L s.m (levelDepth s.K i)) : FourTorus s.L s.m) =
            ((c.target - c.source : Site s.L s.m (levelDepth s.K (i + 1))) : FourTorus s.L s.m) := by
        rw [AddSubgroup.coe_sub, AddSubgroup.coe_sub, PivotAxis.coe_toSublattice hLpos hle,
          PivotAxis.coe_toSublattice hLpos hle]
      rcases c.isNeighbour.choose_spec with e | e
      · refine haxis _ 1 (Or.inl rfl) (Subtype.ext ?_)
        rw [hcoe, e, one_mul, AddSubgroup.coe_zsmul]
        exact PivotAxis.coe_unitStep_eq_smul hLpos hidx _
      · refine haxis _ (-1) (Or.inr rfl) (Subtype.ext ?_)
        rw [hcoe, e, AddSubgroup.coe_zsmul, AddSubgroup.coe_neg, PivotAxis.coe_unitStep_eq_smul hLpos hidx]
        simp [Bond.axis]
    rw [hp, hcd]
end YangMills.Construction.PeriodicLattice
