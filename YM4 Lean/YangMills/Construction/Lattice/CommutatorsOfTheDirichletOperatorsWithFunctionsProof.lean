import YangMills.Construction.Lattice.MassiveDirichletOperatorIdentityFacts
import YangMills.Construction.Lattice.DifferenceOperatorsOfTheBareLattice
import YangMills.Construction.Lattice.MatrixValuedFormOperators
import YangMills.Construction.Lattice.GeometryOfASeparatedSequence
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.SeparatedSequences YangMills.Construction.SeparatedSequences.BaseParameters
noncomputable section
namespace YangMills.Construction.SeparatedSequences.DirichletCommutators
section Compressions
variable {V : Type} [AddCommGroup V] [Module ℝ V]
end Compressions
theorem indicatorMul_idem {ι : Type} (X : Set ι) :
    (indicatorMul X : Module.End ℝ (ι → ℝ)) * indicatorMul X = indicatorMul X := by
  apply LinearMap.ext
  intro f
  funext i
  by_cases h : i ∈ X <;> simp [indicatorMul, h]
variable {L m K : ℕ}
section Parameters
variable (D : BaseParameters)
variable (Ω : ℕ → Set D.Torus)
theorem mem_fineBlock_self {n : ℕ} (y : D.LatticeSite n) :
    (y : D.Torus) ∈ fineBlock (D := D) y := by
  have hL : 0 < D.L := by
    have := D.three_le_L
    omega
  refine ⟨?_, ?_⟩
  · have hz : TorusMetric.supNormVec 0 = 0 := by simp [TorusMetric.supNormVec]
    have hb : BddBelow (TorusMetric.supNormVec ''
        (TorusMetric.torusProj (torusSide D.L D.m) ⁻¹' {(0 : FourTorus D.L D.m)})) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨v, _, rfl⟩
      exact (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
    have hm : (0 : ℝ) ∈ TorusMetric.supNormVec ''
        (TorusMetric.torusProj (torusSide D.L D.m) ⁻¹' {(0 : FourTorus D.L D.m)}) :=
      ⟨0, by funext μ; simp [TorusMetric.torusProj], hz⟩
    have hs : 0 ≤ meshSize D.L (levelDepth D.K n) := zpow_nonneg (Nat.cast_nonneg _) _
    have hle := csInf_le hb hm
    show TorusMetric.torusSupNorm ((y : D.Torus) - (y : D.Torus)) ≤ meshSize D.L (levelDepth D.K n) / 2
    rw [sub_self]
    simp only [TorusMetric.torusSupNorm]
    linarith
  · have hle : levelDepth D.K n ≤ levelDepth D.K 0 := by
      simp only [levelDepth]
      omega
    exact sublattice_mono hL _ hle y.2
theorem levelSite_of_mem_layerSites (hB : D.FineSitesPartitionIntoBlocks Ω) {n : ℕ}
    (y : D.LatticeSite n) (hn : n ≤ D.t) (hy : y ∈ D.layerSites Ω n)
    (hm : (y : D.Torus) ∈ D.allLayerPoints Ω) :
    D.levelSite Ω ⟨(y : D.Torus), hm⟩ = ⟨n, y⟩ := by
  obtain ⟨h1, h2, h3⟩ := (D.exists_levelSite Ω ⟨(y : D.Torus), hm⟩).choose_spec
  have hx0 := mem_fineBlock_self D y
  let x : BareSite D.L D.m D.K := ⟨(y : D.Torus), hx0.2⟩
  have hp : D.IsBlockCentreOf Ω (x : D.Torus) ⟨n, y⟩ := ⟨hn, hy, hx0⟩
  have hq : D.IsBlockCentreOf Ω (x : D.Torus) (D.levelSite Ω ⟨(y : D.Torus), hm⟩) := by
    refine ⟨h1, h2, ?_⟩
    have h := mem_fineBlock_self D (D.levelSite Ω ⟨(y : D.Torus), hm⟩).2
    have h3' : (((D.levelSite Ω ⟨(y : D.Torus), hm⟩).2 : D.LatticeSite _) : D.Torus) =
        (y : D.Torus) := h3
    rw [h3'] at h
    exact h
  exact hB.2.1 x _ _ hq hp
end Parameters
end YangMills.Construction.SeparatedSequences.DirichletCommutators
end
