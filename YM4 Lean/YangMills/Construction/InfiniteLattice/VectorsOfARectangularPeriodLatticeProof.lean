import YangMills.Construction.InfiniteLattice.VectorsOfARectangularPeriodLattice
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction.InfiniteLattice.RectangularPeriods
open YangMills.Construction.NormalFamilies
open YangMills.Construction.PeriodicLattice (coordVec)
theorem coordVec_apply (μ ν : Fin 4) :
    coordVec μ ν = (((Pi.single μ 1 : Fin 4 → ℤ) ν : ℤ) : ℝ) := by
  by_cases h : ν = μ
  · subst h
    simp [coordVec]
  · simp [coordVec, Pi.single_eq_of_ne h]
theorem coordVec_dotProduct (μ lam : Fin 4) :
    coordVec μ ⬝ᵥ coordVec lam = if μ = lam then 1 else 0 := by
  by_cases h : μ = lam
  · subst h
    simp [coordVec]
  · simp [coordVec, h]
theorem isNormalVector_integral_cases {n : AmbientSpace} (h : IsNormalVector n) :
    ∃ z : Fin 4 → ℤ, (∀ ν, n ν = (z ν : ℝ)) ∧
      (normSq n = 1 ∨ (normSq n = 2 ∧ ∃ μ, n μ = 1)) := by
  rcases h with ⟨μ, rfl⟩ | ⟨μ, lam, hlt, rfl | rfl⟩
  · refine ⟨Pi.single μ 1, coordVec_apply μ, Or.inl ?_⟩
    rw [normSq_eq_dotProduct, coordVec_dotProduct, if_pos rfl]
  · have hne : μ ≠ lam := ne_of_lt hlt
    refine ⟨Pi.single μ 1 + Pi.single lam 1, fun ν => ?_, Or.inr ⟨?_, μ, ?_⟩⟩
    · simp only [Pi.add_apply, coordVec_apply, Int.cast_add]
    · rw [normSq_eq_dotProduct]
      simp only [dotProduct_add, add_dotProduct, coordVec_dotProduct, hne, hne.symm, if_true,
        if_false]
      norm_num
    · simp [coordVec, Pi.single_eq_of_ne hne]
  · have hne : μ ≠ lam := ne_of_lt hlt
    refine ⟨Pi.single μ 1 - Pi.single lam 1, fun ν => ?_, Or.inr ⟨?_, μ, ?_⟩⟩
    · simp only [Pi.sub_apply, coordVec_apply, Int.cast_sub]
    · rw [normSq_eq_dotProduct]
      simp only [dotProduct_sub, sub_dotProduct, coordVec_dotProduct, hne, hne.symm, if_true,
        if_false]
      norm_num
    · simp [coordVec, Pi.single_eq_of_ne hne]
theorem frame_lengthSq_ne_zero (F : OrthogonalNormalFrame) (i : Fin 4) : F.lengthSq i ≠ 0 := by
  obtain ⟨_, _, h | ⟨h, _⟩⟩ := isNormalVector_integral_cases (F.isNormal i) <;>
    · rw [OrthogonalNormalFrame.lengthSq, h]
      norm_num
theorem frame_sideVec_apply (F : OrthogonalNormalFrame) (s : Fin 4 → ℕ+) (i ν : Fin 4) :
    F.sideVec s i ν = ((s i : ℕ) : ℝ) * ((F.lengthSq i)⁻¹ * F.vec i ν) := by
  simp [OrthogonalNormalFrame.sideVec, OrthogonalNormalFrame.dual, OrthogonalNormalFrame.lengthSq,
    NormalFamilies.dualVector]
theorem frame_vec_dotProduct_sideVec (F : OrthogonalNormalFrame) (s : Fin 4 → ℕ+) (i j : Fin 4) :
    F.vec i ⬝ᵥ F.sideVec s j = if i = j then ((s i : ℕ) : ℝ) else 0 := by
  have hside : F.vec i ⬝ᵥ F.sideVec s j =
      ((s j : ℕ) : ℝ) * ((F.lengthSq j)⁻¹ * (F.vec i ⬝ᵥ F.vec j)) := by
    simp [OrthogonalNormalFrame.sideVec, OrthogonalNormalFrame.dual,
      OrthogonalNormalFrame.lengthSq, NormalFamilies.dualVector, dotProduct_smul]
  rw [hside]
  by_cases h : i = j
  · subst h
    have hq : F.vec i ⬝ᵥ F.vec i = F.lengthSq i :=
      (normSq_eq_dotProduct _).symm
    rw [if_pos rfl, hq, inv_mul_cancel₀ (frame_lengthSq_ne_zero F i), mul_one]
  · rw [if_neg h, F.pairwise_orthogonal h, mul_zero, mul_zero]
theorem mem_latticeSubgroup_one_iff (x : AmbientSpace) :
    x ∈ latticeSubgroup 1 ↔ ∃ k : Fin 4 → ℤ, ∀ μ, x μ = (k μ : ℝ) := by
  change (∃ k : Fin 4 → ℤ, ∀ μ, x μ = (k μ : ℝ) * 1) ↔ _
  simp only [mul_one]
theorem frame_sideVec_mem_iff (F : OrthogonalNormalFrame) (s : Fin 4 → ℕ+) (i : Fin 4) :
    F.sideVec s i ∈ latticeSubgroup 1 ↔ F.lengthSq i = 1 ∨ Even (s i : ℕ) := by
  obtain ⟨z, hz, hq | ⟨hq, μ, hμ⟩⟩ := isNormalVector_integral_cases (F.isNormal i)
  · have hq' : F.lengthSq i = 1 := hq
    refine ⟨fun _ => Or.inl hq', fun _ => ?_⟩
    rw [mem_latticeSubgroup_one_iff]
    refine ⟨fun ν => ((s i : ℕ) : ℤ) * z ν, fun ν => ?_⟩
    rw [frame_sideVec_apply, hq', hz]
    push_cast
    ring
  · have hq' : F.lengthSq i = 2 := hq
    rw [mem_latticeSubgroup_one_iff, hq']
    constructor
    · rintro ⟨k, hk⟩
      refine Or.inr ⟨(k μ).toNat, ?_⟩
      have hkμ := hk μ
      rw [frame_sideVec_apply, hq', hμ] at hkμ
      have hint : ((s i : ℕ) : ℤ) = k μ + k μ := by
        have : (((s i : ℕ) : ℤ) : ℝ) = ((k μ + k μ : ℤ) : ℝ) := by
          push_cast
          rw [← hkμ]
          ring
        exact_mod_cast this
      omega
    · rintro (h | ⟨r, hr⟩)
      · norm_num at h
      · refine ⟨fun ν => (r : ℤ) * z ν, fun ν => ?_⟩
        rw [frame_sideVec_apply, hq', hz, hr]
        push_cast
        ring
theorem rectangularPeriodVectors : RectangularPeriodVectors :=
  fun F s => ⟨frame_vec_dotProduct_sideVec F s, frame_sideVec_mem_iff F s⟩
end YangMills.Construction.InfiniteLattice.RectangularPeriods
end
