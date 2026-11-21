import YangMills.Construction.InfiniteLattice.SubgroupsOfFiniteIndexContainCubicLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
theorem finiteIndexSubgroupsContainCubicSublattices_holds :
    FiniteIndexSubgroupsContainCubicSublattices := by
  intro Q _ s hs hdvd
  have hs3 : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hle : latticeSubgroup (s : ℝ) ≤ latticeSubgroup 1 := by
    rintro x ⟨n, hn⟩
    exact ⟨fun μ => n μ * (s : ℤ), fun μ => by simp [hn μ]⟩
  have hrank : ∃ v : Fin 4 → LatticePoint 1, (∀ i, v i ∈ cubicSublattice 1 s) ∧
      LinearIndependent ℝ fun i => (v i : AmbientSpace) := by
    refine ⟨fun i => ⟨Pi.single i (s : ℝ), hle ⟨Pi.single i 1, fun ν => ?_⟩⟩, fun i => ?_, ?_⟩
    · by_cases h : ν = i
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    · refine AddSubgroup.mem_addSubgroupOf.mpr ⟨Pi.single i 1, fun ν => ?_⟩
      by_cases h : ν = i
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    · rw [Fintype.linearIndependent_iff]
      intro g hg i
      have hi := congrFun hg i
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.zero_apply] at hi
      have hs0 : (s : ℝ) ≠ 0 := by linarith
      exact (mul_eq_zero.mp hi).resolve_right hs0
  have hshort : ∀ γ ∈ cubicSublattice 1 s, γ ≠ 0 → minimalPeriodRatio * 1 ≤ ‖(γ : AmbientSpace)‖ := by
    intro γ hγ hne
    obtain ⟨n, hn⟩ := AddSubgroup.mem_addSubgroupOf.mp hγ
    have hex : ∃ μ, n μ ≠ 0 := by
      by_contra hall
      have hzero : ∀ μ, n μ = 0 := fun μ => by_contra fun h => hall ⟨μ, h⟩
      exact hne (Subtype.ext (funext fun μ => by simp [hn μ, hzero μ]))
    obtain ⟨μ, hμ⟩ := hex
    have hone : (1 : ℝ) ≤ |(n μ : ℝ)| := by
      exact_mod_cast Int.one_le_abs hμ
    have hcoord : (3 : ℝ) ≤ ‖(γ : AmbientSpace) μ‖ := by
      rw [hn μ, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s)]
      nlinarith
    have hnorm := norm_le_pi_norm (γ : AmbientSpace) μ
    simp only [minimalPeriodRatio, mul_one]
    linarith
  refine ⟨hle, ⟨cubicSublattice 1 s, hrank, hshort⟩, rfl, ?_⟩
  intro γ hγ
  obtain ⟨n, hn⟩ := AddSubgroup.mem_addSubgroupOf.mp hγ
  let y : LatticePoint 1 := ⟨fun μ => (n μ : ℝ), n, fun μ => by simp⟩
  have hy : γ = s • y := by
    apply Subtype.ext
    funext μ
    simp [y, hn μ, mul_comm]
  obtain ⟨t, ht⟩ := hdvd
  rw [hy, ht, mul_comm Q.index t, mul_smul]
  exact Q.nsmul_mem (Q.nsmul_index_mem y) t
end YangMills.Construction.InfiniteLattice
