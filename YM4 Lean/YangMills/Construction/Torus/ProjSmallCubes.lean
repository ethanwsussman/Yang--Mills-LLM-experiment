import YangMills.Construction.Torus.SeparatedChains
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Torus
namespace ProjCubes
structure ProjFacts (d : ℕ) (S : ℝ) : Prop where
  injOn_cube : ∀ (c : Fin d → ℝ) (s : ℝ), s ≤ S →
    InjOn (torusProj d S) {v | ∀ μ, |v μ - c μ| < s / 2}
  supNorm_eq : ∀ v w : Fin d → ℝ, ‖v - w‖ ≤ S / 2 →
    supNorm (torusProj d S v - torusProj d S w) = ‖v - w‖
  lOneNorm_eq : ∀ v w : Fin d → ℝ, ‖v - w‖ ≤ S / 2 →
    lOneNorm (torusProj d S v - torusProj d S w) = ∑ μ, |v μ - w μ|
  lOneNorm_proj_le : ∀ v : Fin d → ℝ, lOneNorm (torusProj d S v) ≤ ∑ μ, |v μ|
  lOneNorm_add_le : ∀ p q : PeriodicTorus d S, lOneNorm (p + q) ≤ lOneNorm p + lOneNorm q
  mem_cubeAt_iff : ∀ (c : Fin d → ℝ) (σ : ℝ) (p : PeriodicTorus d S), 0 ≤ σ →
    (p ∈ cubeAt (torusProj d S c) σ ↔
      ∃ v : Fin d → ℝ, torusProj d S v = p ∧ ∀ μ, |v μ - c μ| ≤ σ / 2)
def ProjFactsHold : Prop := ∀ (d : ℕ) (S : ℝ), 0 < S → ProjFacts d S
end ProjCubes
end YangMills.Construction
end
