import YangMills.Construction.Lattice.EdgeGraphsAndCubes
import YangMills.Construction.Lattice.EdgeGraphsThatAreNotEmpty
import YangMills.Construction.Lattice.LengthOfAnEdgeGraph
import YangMills.Construction.Lattice.LiftsOfCubesVerticesAndEdgesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace EdgeGraphLength
open CubeLifts LevelUnitPartition
variable {S : LevelUnitPartition}
theorem isPointLift_iff (x : S.Points) (w : Fin 4 → ℝ) :
    S.IsPointLift x w ↔ S.proj w = x := by apply _root_.YangMills.Construction.PeriodicLattice.CubeLifts.isPointLift_iff <;> assumption
theorem not_cubeEdge_subset_singleton (hT : TorusInCubeUnits S) (hC : SiteAndCubeLifts S)
    (hN : ShortVectorsNotPeriods S) {e Q : Set S.Points}
    (he : PeriodicLattice.IsCubeEdge S.index e Q) (v : S.Points) : ¬ e ⊆ {v} := by
  obtain ⟨y, rfl, μ, ε, hε, rfl⟩ := he
  intro hsub
  obtain ⟨c, hc⟩ := hT.2.2.2.2.2.2.1 (y : S.Points)
  have hM : (0 : ℝ) < (S.side : ℝ) := by exact_mod_cast hT.2.2.2.2.2.2.2.2.2.2
  have hW := hT.2.1
  have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      S.proj (c + ((S.side : ℝ) / 2) • Function.update ε μ σ) = v := by
    intro σ hσ
    have hsign : ∀ ν, Function.update ε μ σ ν = 1 ∨ Function.update ε μ σ ν = -1 := by
      intro ν
      by_cases hν : ν = μ
      · subst hν
        simpa using hσ
      · rw [Function.update_of_ne hν]
        exact hε ν
    refine mem_singleton_iff.1 (hsub ⟨?_, fun ν hν => ?_⟩)
    · rw [hC.2.1 y c hc]
      refine ⟨_, fun ν => ?_, rfl⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mem_Icc]
      rcases hsign ν with h | h <;> rw [h] <;> constructor <;> linarith
    · rw [← (isPointLift_iff _ c).1 hc]
      change ((PeriodicLattice.meshSize S.params.L (PeriodicLattice.levelDepth S.params.K S.level) *
          (c + ((S.side : ℝ) / 2) • Function.update ε μ σ) ν : ℝ) :
            AddCircle (PeriodicLattice.torusSide S.params.L S.params.m)) =
        ((PeriodicLattice.meshSize S.params.L (PeriodicLattice.levelDepth S.params.K S.level) * c ν : ℝ) :
            AddCircle (PeriodicLattice.torusSide S.params.L S.params.m)) + _
      rw [← AddCircle.coe_add, ← hW]
      congr 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.update_of_ne hν]
      ring
  have hper : IsPeriodVector S ((c + ((S.side : ℝ) / 2) • Function.update ε μ 1) -
      (c + ((S.side : ℝ) / 2) • Function.update ε μ (-1))) :=
    (hT.2.2.2.2.2.2.2.1 _ _).1 ⟨v, (isPointLift_iff _ _).2 (key 1 (Or.inl rfl)),
      (isPointLift_iff _ _).2 (key (-1) (Or.inr rfl))⟩
  have hμ : ((c + ((S.side : ℝ) / 2) • Function.update ε μ 1) -
      (c + ((S.side : ℝ) / 2) • Function.update ε μ (-1))) μ = (S.side : ℝ) := by
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.update_self]
    ring
  have hν : ∀ ν, ν ≠ μ → ((c + ((S.side : ℝ) / 2) • Function.update ε μ 1) -
      (c + ((S.side : ℝ) / 2) • Function.update ε μ (-1))) ν = 0 := by
    intro ν hν
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.update_of_ne hν]
    ring
  refine hN.1 _ (fun h0 => ?_) (fun ν => ?_) hper
  · rw [h0] at hμ
    simp only [Pi.zero_apply] at hμ
    linarith
  · by_cases h : ν = μ
    · subst h
      exact Or.inr (Or.inl hμ)
    · exact Or.inl (hν ν h)
end EdgeGraphLength
open EdgeGraphLength CubeLifts LevelUnitPartition in
theorem edgeGraphLengthFormula_of_cubes (hG : EdgeGraphsDescribedByCubes)
    (hU : EdgeUnionLength) (hF : CubeLifts.Statement)
    (hA : EdgeGraphCubeRelations) : EdgeGraphLengthFormula := by
  intro S Γ hΓ hne
  obtain ⟨hT, -, hC, hV, -, hN⟩ := hF.2.2 S
  have hpart : S.cubes = standardCubePartition S.params.L S.params.m S.index := hT.2.2.1
  have hX : IsPartitionRegion S.index S.fullRegion := ⟨S.cubes, hpart.subset, rfl⟩
  obtain ⟨-, -, -, -, -, -, hE, -, -⟩ := hA S S.fullRegion Γ hX hΓ hne
  obtain ⟨-, -, -, hUnion, hCorner, -⟩ := hE
  obtain ⟨-, hU2, hU3⟩ := hU S
  have hfin : (S.graphEdges Γ).Finite := hV.2.2.2.2.1.subset fun e h => h.1
  have hcases : (S.edgeCount Γ = 0 ∧ (∃ Δ ∈ S.cubes, ∃ v, S.IsCornerOf v Δ ∧ Γ = {v}) ∧
        PeriodicLattice.edgeCount S.index Γ = 0) ∨
      (1 ≤ S.edgeCount Γ ∧ Γ = ⋃₀ S.graphEdges Γ ∧
        PeriodicLattice.edgeCount S.index Γ = S.edgeCount Γ) := by
    rcases (hG S S.fullRegion hX).1.1 Γ hΓ hne with ⟨Δ, hΔ, v, hv, rfl⟩ | ⟨E, hEf, hEn, hEe, rfl⟩
    · have hΔp : Δ ∈ S.cubes := by
        rw [hpart]
        exact hΔ.1
      have h0 := hCorner v ⟨Δ, hΔp, hv⟩
      refine Or.inl ⟨by simp [LevelUnitPartition.edgeCount, h0], ⟨Δ, hΔp, v, hv, rfl⟩, ?_⟩
      have hempty : {e | (∃ Q ∈ standardCubePartition S.params.L S.params.m S.index,
          PeriodicLattice.IsCubeEdge S.index e Q) ∧ e ⊆ ({v} : Set S.Points)} = ∅ := by
        refine eq_empty_of_forall_notMem ?_
        rintro e ⟨⟨Q, -, hQe⟩, hev⟩
        exact not_cubeEdge_subset_singleton hT hC hN hQe v hev
      unfold PeriodicLattice.edgeCount
      rw [hempty, ncard_empty]
    · have hEp : ∀ e ∈ E, S.IsEdge e := fun e he => by
        obtain ⟨Δ, hΔ, h⟩ := hEe e he
        refine ⟨Δ, ?_, h⟩
        rw [hpart]
        exact hΔ.1
      obtain ⟨h1, h2⟩ := hUnion (⋃₀ E) E hΓ hEf hEn hEp rfl
      have hc : S.edgeCount (⋃₀ E) = E.ncard := congrArg ncard h1
      refine Or.inr ⟨?_, by rw [h1], by rw [h2, hc]⟩
      rw [hc]
      exact (ncard_pos hEf).2 hEn
  refine ⟨hfin, ?_, ?_, fun h1 => hU2 _ hfin (fun e h => h.1) h1, ?_, ?_⟩
  · intro h0
    rcases hcases with ⟨-, h, -⟩ | ⟨h1, -⟩
    · exact h
    · omega
  · intro h1
    rcases hcases with ⟨h0, -⟩ | ⟨-, h, -⟩
    · omega
    · exact h
  · intro h0 x _
    obtain ⟨-, hz, hl⟩ := hU3 x
    refine ⟨hz, fun z hzx => ?_⟩
    rw [(hl z hzx).2.2.1, h0]
    simp
  · have hnum : PeriodicLattice.edgeCount S.index Γ = S.edgeCount Γ := by
      rcases hcases with ⟨h0, -, h⟩ | ⟨-, -, h⟩
      · rw [h, h0]
      · exact h
    change S.side * PeriodicLattice.edgeCount S.index Γ = S.side * S.edgeCount Γ
    rw [hnum]
end YangMills.Construction.PeriodicLattice
