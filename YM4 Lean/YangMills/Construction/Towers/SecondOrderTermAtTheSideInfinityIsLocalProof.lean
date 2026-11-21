import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATower
import YangMills.Construction.Towers.BondsOnWhichTheAveragesDepend
import YangMills.Construction.Towers.SecondOrderTermAtTheSideInfinityIsLocal
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.LocalKernels.QuadraticLocality
open Tower
open Tower.AsDifferentials
theorem initial_near_of_hasEndpointsIn {L k : ℕ} (hZ : FullSpace.AdjacentCubesBounds L k k k)
    (c : FullSpace.Edge L k k) (hc : c.IsPositivelyOriented) (e : FullSpace.Edge L k 0)
    (he : SupportOfMeans.Unbounded.HasEndpointsIn c e) :
    TorusMetric.supNormVec (e.initial.1 - c.initial.1) ≤ 3 := by
  have hs := hZ.sites_near c hc
  rw [Nat.sub_self] at hs
  obtain ⟨ν, hx, hν⟩ := hs _ he.1
  unfold TorusMetric.supNormVec
  refine Finset.sup'_le _ _ fun μ _ => ?_
  have hμ : (e.initial.1 - c.initial.1) μ = (ν μ : ℝ) * meshAt L k 0 := by
    have hx' : e.initial.1 = c.initial.1 + ∑ ρ, Pi.single ρ ((ν ρ : ℝ) * meshAt L k 0) := hx
    rw [hx']
    simp [Finset.sum_apply, Pi.single_apply]
  have hone : meshAt L k k = 1 := by simp [meshAt]
  have h := hν μ
  rw [hone] at h
  rw [hμ]
  linarith
theorem getD_eq_of_definedAlike {p q : Option Matrices.ComplexMatrix2}
    (h : SupportOfMeans.DefinedAlike p q) : p.getD 1 = q.getD 1 := by
  cases p with
  | none =>
    cases q with
    | none => rfl
    | some Y => simpa using h.1
  | some X =>
    cases q with
    | none => simpa using h.1
    | some Y => simpa using h.2 X Y rfl rfl
theorem mixedDirectionalDeriv_congr {α : Type}
    (φ : (α → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2)
    (A A' D D' : α → Matrices.ComplexMatrix2)
    (h : ∀ s t : ℂ, φ (s • A + t • A') = φ (s • D + t • D')) :
    mixedDirectionalDeriv ℂ φ A A' = mixedDirectionalDeriv ℂ φ D D' := by
  unfold mixedDirectionalDeriv
  simp only [Algebra.algebraMap_self, RingHom.id_apply, h]
theorem quadraticTermIsLocal_of (hD : CovariantMeansAreDerivatives)
    (hR : SupportOfMeans.SupportOfMeansHolds)
    (hZ : BlockPathContourPivotStatement) :
    QuadraticTermIsLocal := by
  intro L hL k hk W hW B hB B' hB' C hC C' hC' c hloc
  have hterm := (hD L hL k hk).2.2 W hW
  have hR' := (hR L hL k hk).2
  have hZ' : FullSpace.AdjacentCubesBounds L k k k :=
    (hZ L hL k k k hk le_rfl le_rfl).2.2.2.2.2.1
  have hF := (hR'.finite_nonempty k le_rfl c.1).1.coe_toFinset
  have hread := hR'.dependsOnlyOn k le_rfl c.1 _ hF
  have hWc : W ∈ SupportOfMeans.Unbounded.baseFields L k := hW.1
  have hpos : ∀ (X Y : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) (s t : ℂ),
      X ∈ boundedSubmodule (FullSpace.complexEdgeForms (meshAt L k 0)) →
      Y ∈ boundedSubmodule (FullSpace.complexEdgeForms (meshAt L k 0)) →
      ∀ e : FullSpace.Edge L k 0, e.IsPositivelyOriented →
        (s • X + t • Y) e ∈ PeriodicLattice.complexLieAlgebra := by
    intro X Y s t hX hY e he
    exact ((FullSpace.complexEdgeForms (meshAt L k 0)).add_mem
      ((FullSpace.complexEdgeForms (meshAt L k 0)).smul_mem s hX.1)
      ((FullSpace.complexEdgeForms (meshAt L k 0)).smul_mem t hY.1)).1 e he
  have hv : ∀ s t : ℂ,
      FullSpace.AsDifferentials.topLogRatio L k W c (s • B + t • B') =
        FullSpace.AsDifferentials.topLogRatio L k W c (s • C + t • C') := by
    intro s t
    have hagree : ∀ e ∈ (hR'.finite_nonempty k le_rfl c.1).1.toFinset,
        W e = W e ∧ (s • B + t • B') e = (s • C + t • C') e := by
      intro e heF
      have heF' : e ∈ SupportOfMeans.Unbounded.supportEdges c.1 := by
        simpa using heF
      obtain ⟨h₁, h₂⟩ := hloc ⟨e, heF'.1⟩ (initial_near_of_hasEndpointsIn hZ' c.1 c.2 e heF'.2)
      refine ⟨rfl, ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [h₁, h₂]
    have halike := hread.definedAlike_twist W hWc W hWc _ _ (hpos B B' s t hB hB')
      (hpos C C' s t hC hC') hagree
    have hval : FullSpace.AsDifferentials.iterMean
          (FullSpace.expTwist (s • B + t • B') W) k c.1 =
        FullSpace.AsDifferentials.iterMean
          (FullSpace.expTwist (s • C + t • C') W) k c.1 :=
      getD_eq_of_definedAlike halike
    simp only [FullSpace.AsDifferentials.topLogRatio,
      FullSpace.AsDifferentials.iterLogRatio,
      FullSpace.AsDifferentials.iterRatio, hval]
  have key : ∀ X X' : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2,
      X ∈ boundedSubmodule (FullSpace.complexEdgeForms (meshAt L k 0)) →
      X' ∈ boundedSubmodule (FullSpace.complexEdgeForms (meshAt L k 0)) →
      FullSpace.AsDifferentials.complexQuadraticTerm L k W X X' c =
        mixedDirectionalDeriv ℂ
          (FullSpace.AsDifferentials.topLogRatio L k W c) X X' := by
    intro X X' hX hX'
    unfold FullSpace.AsDifferentials.complexQuadraticTerm quadraticTermAt
    rw [dif_pos ⟨hX, hX'⟩]
    exact (hterm.2.2 ⟨X, hX⟩ ⟨X', hX'⟩ c).1.symm
  rw [key B B' hB hB', key C C' hC hC']
  exact mixedDirectionalDeriv_congr _ _ _ _ _ hv
end YangMills.Construction.LocalKernels.QuadraticLocality
end
