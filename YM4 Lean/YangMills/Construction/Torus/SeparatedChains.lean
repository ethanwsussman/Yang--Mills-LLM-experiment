import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Torus
def scaleSpacing (L : ℕ) (ξ : ℝ) (n : ℤ) : ℝ := (L : ℝ) ^ n * ξ
def IsPowerGe (L M : ℕ) : Prop := L ≤ M ∧ ∃ μ : ℕ, M = L ^ μ
abbrev PeriodicTorus (d : ℕ) (S : ℝ) : Type := Fin d → AddCircle S
variable {d : ℕ} {S : ℝ}
def torusProj (d : ℕ) (S : ℝ) (v : Fin d → ℝ) : PeriodicTorus d S := fun μ => (v μ : AddCircle S)
def supNorm (p : PeriodicTorus d S) : ℝ := sInf {r | ∃ v : Fin d → ℝ, torusProj d S v = p ∧ r = ‖v‖}
def lOneNorm (p : PeriodicTorus d S) : ℝ :=
  sInf {r | ∃ v : Fin d → ℝ, torusProj d S v = p ∧ r = ∑ μ, |v μ|}
def supSetDist (A B : Set (PeriodicTorus d S)) : ℝ≥0∞ :=
  ⨅ p ∈ A, ⨅ q ∈ B, ENNReal.ofReal (supNorm (p - q))
structure TorusSegment (d : ℕ) where
  start : Fin d → ℝ
  direction : Fin d → ℝ
def TorusSegment.pointAt (S : ℝ) (s : TorusSegment d) (τ : ℝ) : PeriodicTorus d S :=
  torusProj d S (s.start + τ • s.direction)
def TorusSegment.lOneLength (s : TorusSegment d) : ℝ := ∑ μ, |s.direction μ|
def segmentUnion (S : ℝ) (Γ : List (TorusSegment d)) : Set (PeriodicTorus d S) :=
  {p | ∃ s ∈ Γ, ∃ τ ∈ Icc (0 : ℝ) 1, p = s.pointAt S τ}
def lengthWithin (Γ : List (TorusSegment d)) (X : Set (PeriodicTorus d S)) : ℝ :=
  (Γ.map fun s => s.lOneLength * (volume {τ ∈ Icc (0 : ℝ) 1 | s.pointAt S τ ∈ X}).toReal).sum
def spacingLattice (d : ℕ) (S σ : ℝ) : AddSubgroup (PeriodicTorus d S) where
  carrier := {x | ∃ k : Fin d → ℤ, x = torusProj d S fun μ => (k μ : ℝ) * σ}
  add_mem' := by
    rintro x y ⟨k, rfl⟩ ⟨k', rfl⟩
    refine ⟨k + k', ?_⟩
    funext μ
    simp [torusProj, add_mul]
  zero_mem' := ⟨0, by funext μ; simp [torusProj]⟩
  neg_mem' := by
    rintro x ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    funext μ
    simp [torusProj]
def cubeAt (c : PeriodicTorus d S) (σ : ℝ) : Set (PeriodicTorus d S) := {p | supNorm (p - c) ≤ σ / 2}
def cubePartition (d : ℕ) (S σ : ℝ) : Set (Set (PeriodicTorus d S)) :=
  {Q | ∃ c ∈ spacingLattice d S σ, Q = cubeAt c σ}
def IsCubeUnion (σ : ℝ) (X : Set (PeriodicTorus d S)) : Prop :=
  ∃ 𝒞 ⊆ cubePartition d S σ, X = ⋃₀ 𝒞
def cubeComplement (σ : ℝ) (X : Set (PeriodicTorus d S)) : Set (PeriodicTorus d S) :=
  ⋃₀ {Q ∈ cubePartition d S σ | ¬ Q ⊆ X}
def lastNonemptyIndex (Ω : ℕ → Set (PeriodicTorus d S)) : ℕ := sSup {n | (Ω n).Nonempty}
structure IsSeparatedChain (L : ℕ) (ξ : ℝ) (M R₁ t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)) : Prop where
  scale_pos : 0 < ξ
  period_pos : 0 < S
  blockSize_isPowerGe : IsPowerGe L M
  gapSize_isPowerGe : IsPowerGe L R₁
  zero_nonempty : (Ω 0).Nonempty
  succ_subset : ∀ n, n < t → Ω (n + 1) ⊆ Ω n
  eq_empty_of_lt : ∀ n, t < n → Ω n = ∅
  period_eq_even_mul :
    ∃ k : ℕ, 0 < k ∧ S = 2 * (k : ℝ) * ((M : ℝ) * scaleSpacing L ξ (lastNonemptyIndex Ω))
  isCubeUnion : ∀ n ≤ lastNonemptyIndex Ω, IsCubeUnion ((M : ℝ) * scaleSpacing L ξ n) (Ω n)
  separated : ∀ n, n < t →
    ENNReal.ofReal ((R₁ : ℝ) * (M : ℝ) * scaleSpacing L ξ n) <
      supSetDist (cubeComplement ((M : ℝ) * scaleSpacing L ξ n) (Ω n)) (Ω (n + 1))
def shell (Ω : ℕ → Set (PeriodicTorus d S)) (n : ℕ) : Set (PeriodicTorus d S) := closure (Ω n \ Ω (n + 1))
def shellSites (L : ℕ) (ξ : ℝ) (Ω : ℕ → Set (PeriodicTorus d S)) (n : ℕ) : Set (PeriodicTorus d S) :=
  {y | n ≤ lastNonemptyIndex Ω ∧ y ∈ spacingLattice d S (scaleSpacing L ξ n) ∧ y ∈ shell Ω n}
def unionShellSites (L : ℕ) (ξ : ℝ) (t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)) : Set (PeriodicTorus d S) :=
  {y | ∃ n ≤ t, y ∈ shellSites L ξ Ω n}
def shellIndex (L : ℕ) (ξ : ℝ) (Ω : ℕ → Set (PeriodicTorus d S)) (y : PeriodicTorus d S) : ℕ :=
  sInf {n | y ∈ shellSites L ξ Ω n}
def shellSpacing (L : ℕ) (ξ : ℝ) (Ω : ℕ → Set (PeriodicTorus d S)) (y : PeriodicTorus d S) : ℝ :=
  scaleSpacing L ξ (shellIndex L ξ Ω y)
def siteCube (L : ℕ) (ξ : ℝ) (Ω : ℕ → Set (PeriodicTorus d S)) (y : PeriodicTorus d S) : Set (PeriodicTorus d S) :=
  cubeAt y (shellSpacing L ξ Ω y)
def doubledSiteCube (L : ℕ) (ξ : ℝ) (Ω : ℕ → Set (PeriodicTorus d S)) (y : PeriodicTorus d S) :
    Set (PeriodicTorus d S) :=
  cubeAt y (2 * shellSpacing L ξ Ω y)
def chainWeightedLength (L : ℕ) (ξ : ℝ) (t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S))
    (Γ : List (TorusSegment d)) : ℝ :=
  ∑ n ∈ Finset.Icc 1 t, (scaleSpacing L ξ n)⁻¹ * lengthWithin Γ (shell Ω n) +
    (scaleSpacing L ξ 0)⁻¹ * lengthWithin Γ (Ω 1)ᶜ
def chainWeightedDist (L : ℕ) (ξ : ℝ) (t : ℕ) (Ω : ℕ → Set (PeriodicTorus d S)) (p q : PeriodicTorus d S) : ℝ :=
  sInf {r | ∃ Γ : List (TorusSegment d), IsConnected (segmentUnion S Γ) ∧ p ∈ segmentUnion S Γ ∧
    q ∈ segmentUnion S Γ ∧ r = chainWeightedLength L ξ t Ω Γ}
def unitSpacing (L u : ℕ) : ℝ := (L : ℝ) ^ (-(u : ℤ))
def unitSide (L m K u : ℕ) : ℝ := 2 * (L : ℝ) ^ ((m : ℤ) + (K : ℤ) - (u : ℤ))
end YangMills.Construction.Torus
