import YangMills.Construction.Lattice.TorusAsAQuotientInLevelUnits
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicLattice.TorusQuotient
theorem torusQuotientInLevelUnits_holds : TorusQuotientInLevelUnits := by
  intro s k _ N
  have hL0 : s.L ≠ 0 := by
    have := s.isAdmissible.2
    omega
  have hL : (s.L : ℝ) ≠ 0 := by exact_mod_cast hL0
  have hside : (s.L : ℝ) ^ levelDepth s.K k * s.side = N := by
    simp only [N, Conventions.StandingParameters.side, torusSide, sideInLevelUnits, levelDepth]
    rw [mul_left_comm, ← zpow_natCast (s.L : ℝ) (s.m : ℕ), ← zpow_add₀ hL]
    congr 2
    ring
  have hinv : (s.L : ℝ) ^ ((k : ℤ) - ((s.K : ℕ) : ℤ)) * (s.L : ℝ) ^ levelDepth s.K k = 1 := by
    rw [← zpow_add₀ hL, levelDepth, sub_add_sub_cancel, sub_self, zpow_zero]
  have hinv' : (s.L : ℝ) ^ levelDepth s.K k * (s.L : ℝ) ^ ((k : ℤ) - ((s.K : ℕ) : ℤ)) = 1 := by
    rw [mul_comm, hinv]
  have hform : ∀ (x : Fin 4 → ℝ) (μ : Fin 4), levelProj s.L s.m s.K k x μ =
      (((s.L : ℝ) ^ ((k : ℤ) - ((s.K : ℕ) : ℤ)) * x μ : ℝ) : AddCircle (torusSide s.L s.m)) := by
    intro x μ
    simp only [levelProj, TorusMetric.torusProj, Pi.smul_apply, smul_eq_mul, meshSize,
      levelDepth, neg_sub]
  refine ⟨hside, hside, ?_, hform, ?_⟩
  · intro y
    choose v hv using fun μ => QuotientAddGroup.mk_surjective (y μ)
    refine ⟨fun μ => (s.L : ℝ) ^ levelDepth s.K k * v μ, ?_⟩
    funext μ
    rw [hform, ← mul_assoc, hinv, one_mul]
    exact hv μ
  · intro x x'
    constructor
    · intro hxx
      have hμ : ∀ μ, ∃ n : ℤ, x μ - x' μ = N * (n : ℝ) := by
        intro μ
        have h1 := congrFun hxx μ
        rw [hform, hform, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at h1
        obtain ⟨n, hn⟩ := h1
        refine ⟨n, ?_⟩
        have hs : s.side = torusSide s.L s.m := rfl
        rw [zsmul_eq_mul, ← mul_sub] at hn
        rw [← hside, hs]
        calc x μ - x' μ
            = (s.L : ℝ) ^ levelDepth s.K k * ((s.L : ℝ) ^ ((k : ℤ) - ((s.K : ℕ) : ℤ)) *
                (x μ - x' μ)) := by rw [← mul_assoc, hinv', one_mul]
          _ = (s.L : ℝ) ^ levelDepth s.K k * torusSide s.L s.m * (n : ℝ) := by rw [← hn]; ring
      choose n hn using hμ
      exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩
      funext μ
      rw [hform, hform, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
      refine ⟨n μ, ?_⟩
      have hs : s.side = torusSide s.L s.m := rfl
      rw [zsmul_eq_mul, ← mul_sub, hn μ, ← hside, hs]
      calc (n μ : ℝ) * torusSide s.L s.m
          = ((s.L : ℝ) ^ ((k : ℤ) - ((s.K : ℕ) : ℤ)) * (s.L : ℝ) ^ levelDepth s.K k) *
              (torusSide s.L s.m * (n μ : ℝ)) := by rw [hinv]; ring
        _ = _ := by ring
end YangMills.Construction.PeriodicLattice.TorusQuotient
