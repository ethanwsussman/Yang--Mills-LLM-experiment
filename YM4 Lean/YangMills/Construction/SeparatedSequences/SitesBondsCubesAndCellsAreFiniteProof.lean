import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegionsProof
import YangMills.Construction.SeparatedSequences.SitesBondsCubesAndCellsAreFinite
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SeparatedSequences.CellSetting.Finiteness
open Set
variable {L m : ℕ}
theorem torusSide_eq_mul_meshSize (hL : 0 < L) {i : ℤ} (hi : -(m : ℤ) ≤ i) :
    PeriodicLattice.torusSide L m =
      ((2 * L ^ (((m : ℤ) + i).toNat) : ℕ) : ℝ) * PeriodicLattice.meshSize L i := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryAction.torusSide_eq_mul_meshSize <;> assumption
theorem site_finite (hL : 0 < L) {i : ℤ} (hi : -(m : ℤ) ≤ i) :
    Finite (PeriodicLattice.Site L m i) := by
  set N : ℕ := 2 * L ^ (((m : ℤ) + i).toNat) with hN
  have hNpos : 0 < N := by positivity
  have hside := torusSide_eq_mul_meshSize (m := m) hL hi
  rw [← hN] at hside
  let f : (Fin 4 → Fin N) → PeriodicLattice.FourTorus L m := fun r μ =>
    ((((r μ : ℕ) : ℝ) * PeriodicLattice.meshSize L i : ℝ) : AddCircle (PeriodicLattice.torusSide L m))
  have hsub : (PeriodicLattice.sublattice L m i : Set (PeriodicLattice.FourTorus L m)) ⊆ range f := by
    rintro x ⟨n, hn⟩
    have hr : ∀ μ, (n μ % (N : ℤ)).toNat < N := fun μ => by
      have h0 : 0 ≤ n μ % (N : ℤ) := Int.emod_nonneg _ (by omega)
      have h1 : n μ % (N : ℤ) < (N : ℤ) := Int.emod_lt_of_pos _ (by omega)
      omega
    refine ⟨fun μ => ⟨(n μ % (N : ℤ)).toNat, hr μ⟩, funext fun μ => ?_⟩
    have h0 : 0 ≤ n μ % (N : ℤ) := Int.emod_nonneg _ (by omega)
    have hcast : (((n μ % (N : ℤ)).toNat : ℕ) : ℝ) = ((n μ % (N : ℤ) : ℤ) : ℝ) := by
      have : (((n μ % (N : ℤ)).toNat : ℕ) : ℤ) = n μ % (N : ℤ) := Int.toNat_of_nonneg h0
      exact_mod_cast this
    show ((((n μ % (N : ℤ)).toNat : ℕ) : ℝ) * PeriodicLattice.meshSize L i :
      AddCircle (PeriodicLattice.torusSide L m)) = x μ
    rw [hn μ, hcast, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    refine ⟨-(n μ / (N : ℤ)), ?_⟩
    have hdiv : ((n μ % (N : ℤ) : ℤ) : ℝ) - (n μ : ℝ) =
        -(((n μ / (N : ℤ) : ℤ) : ℝ) * (N : ℝ)) := by
      have := Int.emod_add_mul_ediv (n μ) (N : ℤ)
      have h2 : ((n μ % (N : ℤ) : ℤ) : ℝ) + (N : ℝ) * ((n μ / (N : ℤ) : ℤ) : ℝ) = (n μ : ℝ) := by
        exact_mod_cast this
      linarith
    rw [← sub_mul, hdiv, zsmul_eq_mul, hside]
    push_cast
    ring
  have hfin : (PeriodicLattice.sublattice L m i : Set (PeriodicLattice.FourTorus L m)).Finite :=
    (finite_range f).subset hsub
  exact hfin.to_subtype
theorem latticeFinite (hL : 0 < L) {i : ℤ} (hi : -(m : ℤ) ≤ i) :
    SeparatedSequences.CellSetting.LatticeFinite L m i := by
  have hs := site_finite (m := m) hL hi
  refine ⟨hs, ?_, ?_⟩
  · exact Finite.of_injective (fun e : PeriodicLattice.Bond L m i => (e.source, e.target))
      fun e e' h => by
        have h' := Prod.ext_iff.mp h
        exact PeriodicLattice.Bond.ext h'.1 h'.2
  · exact Finite.of_injective
      (fun p : PeriodicLattice.Plaquette L m i => (p.origin, p.firstAxis, p.secondAxis))
      fun p p' h => by
        simp only [Prod.mk.injEq] at h
        exact PeriodicLattice.Plaquette.ext h.1 h.2.1 h.2.2
theorem standardCubePartition_finite (hL : 0 < L) {i : ℤ} (hi : -(m : ℤ) ≤ i) :
    (PeriodicLattice.standardCubePartition L m i).Finite := by
  have hs := site_finite (m := m) hL hi
  exact finite_range _
theorem partitionRegions_finite (hL : 0 < L) {i : ℤ} (hi : -(m : ℤ) ≤ i) :
    {X : Set (PeriodicLattice.FourTorus L m) | PeriodicLattice.IsPartitionRegion i X}.Finite := by
  refine ((standardCubePartition_finite (m := m) hL hi).finite_subsets.image sUnion).subset ?_
  rintro X ⟨C, hC, rfl⟩
  exact ⟨C, hC, rfl⟩
theorem blockUnions_finite (hL : 0 < L) (S : SeparatedSequences.ScaleData) (n : ℕ) :
    {X : Set (PeriodicLattice.FourTorus L m) | SeparatedSequences.IsBlockUnion S n X}.Finite := by
  by_cases hi : -(m : ℤ) ≤ S.blockPartitionIndex n
  · refine ((partitionRegions_finite (m := m) hL hi).union (finite_singleton ∅)).subset ?_
    rintro X (rfl | ⟨-, hX⟩)
    · exact Or.inr rfl
    · exact Or.inl hX
  · refine (finite_singleton (∅ : Set (PeriodicLattice.FourTorus L m))).subset ?_
    rintro X (rfl | ⟨h, -⟩)
    · rfl
    · exact absurd h hi
theorem widenedCubes_finite (hL : 0 < L) (S : SeparatedSequences.ScaleData)
    (Ω : ℕ → Set (PeriodicLattice.FourTorus L m)) :
    (SeparatedSequences.widenedCubes S Ω).Finite := by
  refine ((finite_Iic S.top).biUnion fun n _ =>
    (blockUnions_finite (m := m) hL S n).image
      fun q => ((n, q) : SeparatedSequences.LevelCube L m)).subset ?_
  rintro ⟨n, q⟩ ⟨hn, hq⟩
  exact mem_biUnion (show n ∈ Iic S.top from hn) ⟨q, hq.2.2, rfl⟩
theorem statement_holds : Statement := by
  refine ⟨fun L m K _ hL _ _ => ?_, fun L m N S Ω hS => ?_⟩
  · have hL0 : 0 < L := by omega
    refine ⟨fun i hi => latticeFinite hL0 hi, fun n hn => latticeFinite hL0 ?_,
      fun i hi => standardCubePartition_finite hL0 hi⟩
    simp only [PeriodicLattice.levelDepth]
    omega
  · have hL0 : 0 < L := by
      have := hS.covariance.thirteen_le_blockSize
      omega
    have hQ := widenedCubes_finite hL0 S Ω
    exact ⟨hQ, hQ.finite_subsets.subset fun F hF => hF.2.2.1⟩
end YangMills.Construction.SeparatedSequences.CellSetting.Finiteness
