import YangMills.Construction.InfiniteLattice.MirrorGridsAndFunctionsOfACell
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
open scoped ComplexConjugate
namespace YangMills.Construction.InfiniteLattice
open YangMills.Construction.CutoffLattice (spacingAt FieldsAt)
namespace ReflectionGrid
variable {L K : ℕ} (G : ReflectionGrid L K)
theorem exists_edge_eq_natCast_mul_spacingAt (hL : Conventions.IsAdmissibleBlockingFactor L) :
    ∃ n : ℕ, G.edge = (n : ℝ) * spacingAt L K := by
  obtain ⟨⟨q, hq⟩, hl⟩ := G.edge_admissible
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by have := hL.2; omega : 1 < L)
  have hL0 : (L : ℝ) ≠ 0 := (zero_lt_one.trans hL1).ne'
  have ha : spacingAt L K = (L : ℝ) ^ (-(K : ℤ)) := rfl
  have hexp : -(K : ℤ) ≤ q - 2 := by
    have h : (L : ℝ) ^ (-(K : ℤ)) ≤ (L : ℝ) ^ (q - 2) := by
      have h2 : (L : ℝ) ^ (q - 2) = (L : ℝ) ^ q / (L : ℝ) ^ 2 := by
        rw [zpow_sub₀ hL0]
        norm_cast
      rw [h2, ← ha, ← hq]
      exact hl
    exact (zpow_le_zpow_iff_right₀ hL1).mp h
  refine ⟨L ^ (q + K).toNat, ?_⟩
  have hn : ((L ^ (q + K).toNat : ℕ) : ℝ) = (L : ℝ) ^ (q + K) := by
    rw [Nat.cast_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  rw [hn, ha, hq, ← zpow_add₀ hL0]
  congr 1
  ring
theorem wallReflect_mem_latticeAt (hL : Conventions.IsAdmissibleBlockingFactor L) (μ : Fin 4) (k : ℤ)
    {x : AmbientSpace} (hx : x ∈ CutoffLattice.latticeAt L K) :
    G.wallReflect μ k x ∈ CutoffLattice.latticeAt L K := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨N, hN⟩ := G.exists_edge_eq_natCast_mul_spacingAt hL
  obtain ⟨i, hi⟩ := G.shift_mem μ
  refine ⟨Function.update n μ (2 * i + 1 + 2 * k * N - n μ), fun ν => ?_⟩
  by_cases h : ν = μ
  · subst h
    simp only [wallReflect, Pi.sub_apply, Pi.smul_apply, basisVec, Pi.single_eq_same,
      smul_eq_mul, mul_one, Function.update_self]
    rw [hn, hi, hN]
    push_cast
    ring
  · simp [wallReflect, basisVec, Pi.single_eq_of_ne h, Function.update_of_ne h, hn]
theorem wallReflect_wallReflect (μ : Fin 4) (k : ℤ) (x : AmbientSpace) :
    G.wallReflect μ k (G.wallReflect μ k x) = x := by
  rw [G.wallReflect_eq_hyperplaneReflect]
  exact InfiniteLattice.hyperplaneReflect_hyperplaneReflect
    (by simp [basisVec, dotProduct, Pi.single_apply]) _ x
theorem image_latticeAt_of_mem_reflectionGroup (hL : Conventions.IsAdmissibleBlockingFactor L)
    {g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace} (hg : g ∈ G.reflectionGroup) :
    g '' (CutoffLattice.latticeAt L K : Set AmbientSpace) = CutoffLattice.latticeAt L K := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨⟨μ, k⟩, rfl⟩ := hg
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact G.wallReflect_mem_latticeAt hL μ k hx
    · intro hy
      exact ⟨G.wallReflect μ k y, G.wallReflect_mem_latticeAt hL μ k hy,
        G.wallReflect_wallReflect μ k y⟩
  | one => simp
  | mul g h _ _ hg hh =>
    rw [AffineEquiv.coe_mul, Set.image_comp, hh, hg]
  | inv g _ hg =>
    conv_lhs => rw [← hg]
    rw [← Set.image_comp]
    have : ⇑(g⁻¹) ∘ ⇑g = id := by
      funext z
      exact g.symm_apply_apply z
    rw [this, Set.image_id]
def toLatticeSymmetry (hL : Conventions.IsAdmissibleBlockingFactor L) (g : G.reflectionGroup) :
    LatticeSymmetry (spacingAt L K) where
  toFun := (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace)
  preservesDist := G.euclidNormVec_sub_of_mem_reflectionGroup g.2
  image_eq := G.image_latticeAt_of_mem_reflectionGroup hL g.2
def torusTileIndices (m : ℕ) : Set (Fin 4 → ℤ) :=
  {k | ∀ μ, 0 ≤ k μ ∧ (k μ : ℝ) ≤ PeriodicLattice.torusSide L m / G.edge - 1}
theorem torusTileIndices_finite (m : ℕ) : (G.torusTileIndices m).Finite := by
  refine (Set.finite_Icc (0 : Fin 4 → ℤ) fun _ => ⌊PeriodicLattice.torusSide L m / G.edge⌋).subset ?_
  intro k hk
  refine ⟨fun μ => (hk μ).1, fun μ => Int.le_floor.mpr ?_⟩
  linarith [(hk μ).2]
end ReflectionGrid
end YangMills.Construction.InfiniteLattice
end
