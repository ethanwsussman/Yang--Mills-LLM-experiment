import YangMills.Construction.RotationInvariance.HarmonicsAtLabelledSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane ForwardTube
namespace RealPlane
variable {n n' : ℕ}
def LabelledPoints.IsInjectiveIn (A : Set RealPlane)
    (c : LabelledPoints n) : Prop :=
  c.points ∈ injectiveTuplesIn A n
def mapAppend (a : RealPlane → RealPlane)
    (x : Fin n → RealPlane) (y : Fin n' → RealPlane) : Fin (n + n') → RealPlane :=
  Fin.append (mapPoints a x) y
theorem mapAppend_reflectFirst_injective {x : Fin n → RealPlane}
    {y : Fin n' → RealPlane} (hx : x ∈ injectiveTuplesIn openRightHalf n)
    (hy : y ∈ injectiveTuplesIn openRightHalf n') :
    mapAppend reflectFirst x y ∈ injectivePointTuples (n + n') ∧
      (∀ i, mapAppend reflectFirst x y (Fin.castAdd n' i) ∈ openLeftHalf) ∧
      ∀ j, mapAppend reflectFirst x y (Fin.natAdd n j) ∈ openRightHalf := by
  have hfirst : ∀ i, mapAppend reflectFirst x y (Fin.castAdd n' i) = reflectFirst (x i) := by
    intro i
    simp [mapAppend, mapPoints]
  have hlast : ∀ j, mapAppend reflectFirst x y (Fin.natAdd n j) = y j := by
    intro j
    simp [mapAppend]
  have htime : ∀ i, reflectFirst (x i) 0 = -(x i 0) := by
    intro i
    simp [reflectFirst]
  have hneg : ∀ i, mapAppend reflectFirst x y (Fin.castAdd n' i) ∈ openLeftHalf := by
    intro i
    have h0 : 0 < x i 0 := hx.2 i
    rw [hfirst]
    show reflectFirst (x i) 0 < 0
    rw [htime]
    linarith
  have hpos : ∀ j, mapAppend reflectFirst x y (Fin.natAdd n j) ∈ openRightHalf := by
    intro j
    rw [hlast]
    exact hy.2 j
  refine ⟨?_, hneg, hpos⟩
  show Function.Injective _
  have hcross : ∀ i j, mapAppend reflectFirst x y (Fin.castAdd n' i) ≠
      mapAppend reflectFirst x y (Fin.natAdd n j) := by
    intro i j h
    have h1 : (mapAppend reflectFirst x y (Fin.castAdd n' i)) 0 < 0 := hneg i
    have h2 : 0 < (mapAppend reflectFirst x y (Fin.natAdd n j)) 0 := hpos j
    rw [h] at h1
    linarith
  intro a b hab
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left k =>
      rw [hfirst, hfirst] at hab
      have h0 : x i 0 = x k 0 := by
        have := congrArg (fun v : RealPlane => v 0) hab
        simpa [htime] using this
      have h1 : x i 1 = x k 1 := by
        have := congrArg (fun v : RealPlane => v 1) hab
        simpa [reflectFirst] using this
      have hxx : x i = x k := by
        ext m
        fin_cases m
        · exact h0
        · exact h1
      rw [hx.1 hxx]
    | right k => exact absurd hab (hcross i k)
  | right j =>
    induction b using Fin.addCases with
    | left k => exact absurd hab.symm (hcross k j)
    | right k =>
      rw [hlast, hlast] at hab
      rw [hy.1 hab]
def IsLine (l : Set RealPlane) : Prop :=
  ∃ L : AffineSubspace ℝ RealPlane,
    (L : Set RealPlane) = l ∧ Module.finrank ℝ L.direction = 1
def IsUnitNormal (l : Set RealPlane) (ν : RealPlane) : Prop :=
  ‖ν‖ = 1 ∧ ∀ a ∈ l, ∀ b ∈ l, inner ℝ ν (b - a) = 0
def posSide (ν u : RealPlane) : Set RealPlane :=
  {y | 0 < inner ℝ ν (y - u)}
def negSide (ν u : RealPlane) : Set RealPlane :=
  {y | inner ℝ ν (y - u) < 0}
def reflectAcross (ν u y : RealPlane) : RealPlane :=
  y - (2 * inner ℝ ν (y - u)) • ν
def IsOpenSide (l P : Set RealPlane) : Prop :=
  ∃ u ∈ l, ∃ ν, IsUnitNormal l ν ∧ P = posSide ν u
def NormalPointsInto (l : Set RealPlane) (ν : RealPlane)
    (P : Set RealPlane) : Prop :=
  IsUnitNormal l ν ∧ ∃ u ∈ l, P = posSide ν u
def AreOpenSides (l P Q : Set RealPlane) : Prop :=
  ∃ u ∈ l, ∃ ν, IsUnitNormal l ν ∧
    P = posSide ν u ∧ Q = negSide ν u
def lineReflection (l : Set RealPlane) : RealPlane → RealPlane :=
  Classical.epsilon fun f => ∃ u ∈ l, ∃ ν, IsUnitNormal l ν ∧ f = reflectAcross ν u
theorem negSide_eq_posSide_neg (ν u : RealPlane) :
    negSide ν u = posSide (-ν) u := by
  ext y
  simp [negSide, posSide, inner_neg_left]
namespace IsLine
variable {l : Set RealPlane} {ν ν' u u' : RealPlane}
theorem nonempty (hl : IsLine l) : l.Nonempty := by
  obtain ⟨L, rfl, hL⟩ := hl
  rcases L.eq_bot_or_nonempty with rfl | h
  · rw [AffineSubspace.direction_bot, finrank_bot] at hL
    exact absurd hL (by norm_num)
  · exact h
private theorem finrank_direction_orthogonal {L : AffineSubspace ℝ RealPlane}
    (hL : Module.finrank ℝ L.direction = 1) : Module.finrank ℝ L.directionᗮ = 1 := by
  have h := L.direction.finrank_add_finrank_orthogonal
  rw [hL] at h
  simp at h
  omega
private theorem mem_direction_orthogonal {L : AffineSubspace ℝ RealPlane}
    (hν : IsUnitNormal (L : Set RealPlane) ν) (hu : u ∈ (L : Set RealPlane)) :
    ν ∈ L.directionᗮ := by
  rw [Submodule.mem_orthogonal']
  intro w hw
  have hmem : w +ᵥ u ∈ L := AffineSubspace.vadd_mem_of_mem_direction hw hu
  have := hν.2 u hu (w +ᵥ u) hmem
  simpa [real_inner_comm] using this
theorem eq_or_eq_neg (hl : IsLine l) (hν : IsUnitNormal l ν)
    (hν' : IsUnitNormal l ν') : ν' = ν ∨ ν' = -ν := by
  obtain ⟨u, hu⟩ := hl.nonempty
  obtain ⟨L, rfl, hL⟩ := hl
  have h0 : (⟨ν, mem_direction_orthogonal hν hu⟩ : L.directionᗮ) ≠ 0 := by
    intro h
    have : ν = 0 := congrArg Subtype.val h
    simpa [this] using hν.1
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ h0).mp (finrank_direction_orthogonal hL)
    ⟨ν', mem_direction_orthogonal hν' hu⟩
  have hcν : c • ν = ν' := congrArg Subtype.val hc
  have habs : |c| = 1 := by
    have := congrArg norm hcν
    rwa [norm_smul, hν.1, hν'.1, mul_one, Real.norm_eq_abs] at this
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
  · left
    rw [← hcν, h, one_smul]
  · right
    rw [← hcν, h, neg_one_smul]
end IsLine
theorem posSide_eq_of_mem {l : Set RealPlane} {ν u u' : RealPlane}
    (hν : IsUnitNormal l ν) (hu : u ∈ l) (hu' : u' ∈ l) :
    posSide ν u = posSide ν u' := by
  have h := hν.2 u hu u' hu'
  ext y
  have hy : inner ℝ ν (y - u) = inner ℝ ν (y - u') := by
    have : y - u = (y - u') + (u' - u) := by abel
    rw [this, inner_add_right, h, add_zero]
  simp [posSide, hy]
theorem reflectAcross_eq_of_mem {l : Set RealPlane} {ν ν' u u' : RealPlane}
    (hl : IsLine l) (hν : IsUnitNormal l ν) (hν' : IsUnitNormal l ν')
    (hu : u ∈ l) (hu' : u' ∈ l) : reflectAcross ν u = reflectAcross ν' u' := by
  have h := hν.2 u hu u' hu'
  have hy : ∀ y, inner ℝ ν (y - u) = inner ℝ ν (y - u') := by
    intro y
    have : y - u = (y - u') + (u' - u) := by abel
    rw [this, inner_add_right, h, add_zero]
  funext y
  rcases hl.eq_or_eq_neg hν hν' with rfl | rfl
  · simp [reflectAcross, hy]
  · simp [reflectAcross, hy, inner_neg_left]
theorem lineReflection_eq {l : Set RealPlane} {ν u : RealPlane}
    (hl : IsLine l) (hu : u ∈ l) (hν : IsUnitNormal l ν) :
    lineReflection l = reflectAcross ν u := by
  have hex : ∃ f : RealPlane → RealPlane,
      ∃ u ∈ l, ∃ ν, IsUnitNormal l ν ∧ f = reflectAcross ν u :=
    ⟨_, u, hu, ν, hν, rfl⟩
  obtain ⟨u₂, hu₂, ν₂, hν₂, h⟩ := Classical.epsilon_spec hex
  rw [lineReflection, h]
  exact reflectAcross_eq_of_mem hl hν₂ hν hu₂ hu
def tupleTwoMul {α : Type*} {k : ℕ} (t : Fin (k + k) → α) : Fin (2 * k) → α :=
  fun i => t (Fin.cast (two_mul k) i)
end RealPlane
namespace EuclideanFunctionals
def harmonicGramKernel (S : ConnFamily) (φ₀ : openingAngles) (s : ℝ) {n n' : ℕ}
    (x : LabelledPoints n) (y : LabelledPoints n') : ℂ :=
  ∑ h ∈ Finset.Icc (-(maxFrequency S φ₀ (n + n') : ℤ)) (maxFrequency S φ₀ (n + n') : ℤ),
    pointHarmonic S φ₀ h (n + n') (Fin.append x.labelVec y.labelVec)
        (mapAppend RealPlane.reflectFirst x.points y.points) *
      Complex.exp (-(4 * (h : ℂ) * (s : ℂ)))
def topIndex (S : ConnFamily) (φ₀ : openingAngles) (k : ℕ) : ℕ := maxFrequency S φ₀ (2 * k)
def topCoeff (S : ConnFamily) (φ₀ : openingAngles) (k : ℕ) :
    (Fin (2 * k) → realLabels) → (Fin (2 * k) → RealPlane) → ℂ :=
  pointHarmonic S φ₀ (-(topIndex S φ₀ k : ℤ)) (2 * k)
end EuclideanFunctionals
end YangMills.Construction
end
