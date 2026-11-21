import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def coarsen (b : ℕ) (k : Fin 4 → ℤ) : ReflectionGrid D where
  q := g.q + b
  one_sub_K_le_q := by
    have := g.one_sub_K_le_q
    omega
  origin := fun μ => g.origin μ + g.cellSide * k μ
  origin_mem := fun μ => by
    obtain ⟨i, hi⟩ := g.origin_mem μ
    refine ⟨i + g.cellRatio * k μ, ?_⟩
    rw [hi, g.cellSide_eq]
    push_cast
    ring
theorem cellSide_coarsen (b : ℕ) (k : Fin 4 → ℤ) :
    (g.coarsen b k).cellSide = (D.L : ℝ) ^ b * g.cellSide := by
  have hL : (D.L : ℝ) ≠ 0 := by linarith [D.one_lt_factor]
  simp only [cellSide, coarsen]
  rw [zpow_add₀ hL, zpow_natCast, mul_comm]
theorem IsCoarse.coarsen {g : ReflectionGrid D} (h : g.IsCoarse) (b : ℕ) (k : Fin 4 → ℤ) :
    (g.coarsen b k).IsCoarse := by
  have h' : 0 ≤ g.q := h
  show 0 ≤ g.q + (b : ℤ)
  omega
def IsFiniteCellFamily (O : Set (Set AmbientSpace)) : Prop := O.Finite ∧ O ⊆ g.cellSet
def cellIndexSet (O : Set (Set AmbientSpace)) : Set (Fin 4 → ℤ) := {k | g.cell k ∈ O}
end ReflectionGrid
open Classical in
def minCorner (I : Set (Fin 4 → ℤ)) : Fin 4 → ℤ :=
  if I = ∅ then 0 else fun μ => sInf ((fun k : Fin 4 → ℤ => k μ) '' I)
open Classical in
def minScaleExponent (L : ℕ) (I : Set (Fin 4 → ℤ)) : ℕ :=
  if I = ∅ then 0
  else sInf {b : ℕ | ∀ k ∈ I, ∀ μ, k μ - minCorner I μ < (L : ℤ) ^ b}
theorem minCorner_isLeast {I : Set (Fin 4 → ℤ)} (hI : I.Finite) (hne : I.Nonempty) (μ : Fin 4) :
    IsLeast ((fun k : Fin 4 → ℤ => k μ) '' I) (minCorner I μ) := by
  have hne' : I ≠ ∅ := hne.ne_empty
  have hfin : ((fun k : Fin 4 → ℤ => k μ) '' I).Finite := hI.image _
  have hval : minCorner I μ = sInf ((fun k : Fin 4 → ℤ => k μ) '' I) := by
    simp [minCorner, hne']
  rw [hval]
  exact ⟨Int.csInf_mem (hne.image _) hfin.bddBelow, fun _ hx => csInf_le hfin.bddBelow hx⟩
theorem minScaleExponent_isLeast {L : ℕ} (hL : 1 < L) {I : Set (Fin 4 → ℤ)} (hI : I.Finite) :
    IsLeast {b : ℕ | ∀ k ∈ I, ∀ μ, k μ - minCorner I μ < (L : ℤ) ^ b} (minScaleExponent L I) := by
  by_cases hempty : I = ∅
  · subst hempty
    simp [minScaleExponent, IsLeast, lowerBounds]
  have hset : {b : ℕ | ∀ k ∈ I, ∀ μ, k μ - minCorner I μ < (L : ℤ) ^ b}.Nonempty := by
    have hfin : ((fun p : (Fin 4 → ℤ) × Fin 4 => p.1 p.2 - minCorner I p.2) ''
        (I ×ˢ (univ : Set (Fin 4)))).Finite := (hI.prod finite_univ).image _
    obtain ⟨M, hM⟩ := hfin.bddAbove
    refine ⟨M.toNat, fun k hk μ => ?_⟩
    have h1 : k μ - minCorner I μ ≤ M := hM ⟨(k, μ), ⟨hk, mem_univ μ⟩, rfl⟩
    have h2 : M ≤ (M.toNat : ℤ) := Int.self_le_toNat M
    have h3 : ((M.toNat : ℕ) : ℤ) < (L : ℤ) ^ M.toNat := by
      exact_mod_cast Nat.lt_pow_self hL
    omega
  have hval : minScaleExponent L I =
      sInf {b : ℕ | ∀ k ∈ I, ∀ μ, k μ - minCorner I μ < (L : ℤ) ^ b} := by
    simp [minScaleExponent, hempty]
  rw [hval]
  exact ⟨Nat.sInf_mem hset, fun _ hb => Nat.sInf_le hb⟩
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
theorem cellSide_pos : 0 < g.cellSide := zpow_pos (by linarith [D.one_lt_factor]) _
theorem cell_injective : Function.Injective g.cell := by
  have hs := g.cellSide_pos
  have key : ∀ k k' : Fin 4 → ℤ, g.cell k = g.cell k' → ∀ μ, k' μ ≤ k μ := by
    intro k k' h μ
    have hx : (fun ν => g.origin ν + g.cellSide * k ν) ∈ g.cell k := fun ν => by
      simp [hs.le]
    rw [h] at hx
    have h0 := (hx μ).1
    have h1 : g.cellSide * (k' μ : ℝ) ≤ g.cellSide * (k μ : ℝ) := by linarith
    exact_mod_cast le_of_mul_le_mul_left h1 hs
  intro k k' h
  funext μ
  exact le_antisymm (key k' k h.symm μ) (key k k' h μ)
variable {g}
theorem IsFiniteCellFamily.finite_cellIndexSet {O : Set (Set AmbientSpace)}
    (hO : g.IsFiniteCellFamily O) : (g.cellIndexSet O).Finite :=
  hO.1.preimage g.cell_injective.injOn
variable (g)
def enclosingCoarsening (O : Set (Set AmbientSpace)) : ReflectionGrid D :=
  g.coarsen (minScaleExponent D.L (g.cellIndexSet O)) (minCorner (g.cellIndexSet O))
theorem cellSide_enclosingCoarsening (O : Set (Set AmbientSpace)) :
    (g.enclosingCoarsening O).cellSide =
      (D.L : ℝ) ^ minScaleExponent D.L (g.cellIndexSet O) * g.cellSide :=
  g.cellSide_coarsen _ _
end ReflectionGrid
end YangMills.Construction.ChessboardTori
end
