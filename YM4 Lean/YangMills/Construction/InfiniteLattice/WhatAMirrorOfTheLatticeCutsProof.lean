import YangMills.Construction.InfiniteLattice.EightLoopsRoundAPlaquette
import YangMills.Construction.InfiniteLattice.WhatAMirrorOfTheLatticeCuts
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies.MirrorCuts
open YangMills.Construction.InfiniteLattice
open YangMills.Construction.PeriodicLattice (coordVec)
theorem coe_add_coord (x y : LatticePoint 1) (ρ : Fin 4) :
    ((x + y : LatticePoint 1) : AmbientSpace) ρ = (x : AmbientSpace) ρ + (y : AmbientSpace) ρ := rfl
theorem axisStep_coord (μ ρ : Fin 4) :
    ((axisStep 1 μ : LatticePoint 1) : AmbientSpace) ρ = if ρ = μ then 1 else 0 := by
  simp [axisStep, Pi.single_apply]
theorem corner_le_of_mem (p : ElementaryPlaquette 1) {z : LatticePoint 1}
    (hz : z ∈ plaquetteCorners p) (ρ : Fin 4) :
    (p.corner : AmbientSpace) ρ ≤ (z : AmbientSpace) ρ := by
  simp only [plaquetteCorners, mem_insert_iff, mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact le_rfl
  all_goals
    simp only [coe_add_coord, axisStep_coord]
    split_ifs <;> linarith
theorem eq_corner_of_hasCornerSquare {p : ElementaryPlaquette 1} {x : LatticePoint 1}
    {μ ν : Fin 4} (hsq : HasCornerSquare p x μ ν) : x = p.corner := by
  have hx : x ∈ plaquetteCorners p := by
    rw [hsq]
    simp
  have hc : p.corner ∈ plaquetteCorners p := by
    simp [plaquetteCorners]
  rw [hsq] at hc
  simp only [mem_insert_iff, mem_singleton_iff] at hc
  refine Subtype.ext (funext fun ρ => le_antisymm ?_ (corner_le_of_mem p hx ρ))
  rcases hc with hc | hc | hc | hc
  · rw [hc]
  all_goals
    have hρ := congrArg (fun z : LatticePoint 1 => (z : AmbientSpace) ρ) hc
    simp only [coe_add_coord, axisStep_coord] at hρ
    rw [hρ]
    split_ifs <;> linarith
theorem axis_of_step_mem {p : ElementaryPlaquette 1} {μ : Fin 4}
    (hmem : p.corner + axisStep 1 μ ∈ plaquetteCorners p) : μ = p.lowAxis ∨ μ = p.highAxis := by
  by_contra hne
  obtain ⟨hlo, hhi⟩ := not_or.mp hne
  simp only [plaquetteCorners, mem_insert_iff, mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem | hmem | hmem <;>
    · have hμ := congrArg (fun z : LatticePoint 1 => (z : AmbientSpace) μ) hmem
      simp [coe_add_coord, axisStep_coord, hlo, hhi] at hμ
theorem liesInPlane_of_hasCornerSquare {p : ElementaryPlaquette 1} {μ ν : Fin 4} (hne : ν ≠ μ)
    (hsq : HasCornerSquare p p.corner μ ν) : p.LiesInPlane μ ν := by
  have hμ : μ = p.lowAxis ∨ μ = p.highAxis := axis_of_step_mem (by rw [hsq]; simp)
  have hν : ν = p.lowAxis ∨ ν = p.highAxis := axis_of_step_mem (by rw [hsq]; simp)
  rcases hμ with a | a <;> rcases hν with b | b
  · exact (hne (b.trans a.symm)).elim
  · exact Or.inl ⟨a.symm, b.symm⟩
  · exact Or.inr ⟨b.symm, a.symm⟩
  · exact (hne (b.trans a.symm)).elim
theorem hasDiagonalCornersAtLevel_iff (v : AmbientSpace) (c : ℝ) (p : ElementaryPlaquette 1) :
    HasDiagonalCornersAtLevel v c p ↔
      ∃ y y' : LatticePoint 1, IsDiagonalCornerPair p y y' ∧
        linearHeight v (y : LatticePoint 1) = c ∧ linearHeight v (y' : LatticePoint 1) = c := by
  constructor
  · rintro (⟨a, b⟩ | ⟨a, b⟩)
    · exact ⟨_, _, Or.inl ⟨rfl, rfl⟩, a, b⟩
    · exact ⟨_, _, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), a, b⟩
  · rintro ⟨y, y', (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), a, b⟩
    · exact Or.inl ⟨a, b⟩
    · exact Or.inl ⟨b, a⟩
    · exact Or.inr ⟨a, b⟩
    · exact Or.inr ⟨b, a⟩
theorem levelCorners_of_diagonalPair (P : NormalLevelPair 1) {p : ElementaryPlaquette 1}
    {y y' : LatticePoint 1}
    (hnorm : P.normal = coordVec p.lowAxis - coordVec p.highAxis ∨
      P.normal = coordVec p.lowAxis + coordVec p.highAxis)
    (hcut : DiagonalCutProperties P p.lowAxis p.highAxis p) (hpair : IsDiagonalCornerPair p y y')
    (hy : linearHeight P.normal (y : LatticePoint 1) = P.level)
    (hy' : linearHeight P.normal (y' : LatticePoint 1) = P.level) :
    (y = levelCornerOne P.normal p ∧ y' = levelCornerTwo P.normal p) ∨
      (y = levelCornerTwo P.normal p ∧ y' = levelCornerOne P.normal p) := by
  obtain ⟨hdiff, hsum, -, -, -, hz, hz', -⟩ := hcut
  rcases hnorm with hn | hn
  · obtain ⟨e₁, e₂, e₃, e₄⟩ := hdiff hn
    rw [e₃] at hz
    rw [e₄] at hz'
    rw [e₁, e₂]
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · linarith
    · linarith
  · obtain ⟨e₁, e₂, e₃, e₄⟩ := hsum hn
    rw [e₃] at hz
    rw [e₄] at hz'
    rw [e₁, e₂]
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · linarith
    · linarith
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
theorem twoLinkHolonomy_opposite (l l' : Link 1) (V : GaugeField 1) :
    twoLinkHolonomy l'.opposite l.opposite V = (twoLinkHolonomy l l' V)⁻¹ := by
  simp only [twoLinkHolonomy, mul_inv_rev]
  rw [V.2, V.2]
theorem re_trace_inv_mul_inv
    (hcomm : ∀ g₁ g₂ : Matrices.ComplexMatrix2.specialUnitary,
      (Matrices.ComplexMatrix2.fullTrace
          ((g₁ * g₂ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re =
        (Matrices.ComplexMatrix2.fullTrace
          ((g₂ * g₁ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re)
    (hinv : ∀ g₁ : Matrices.ComplexMatrix2.specialUnitary,
      (Matrices.ComplexMatrix2.fullTrace
          ((g₁⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re =
        (Matrices.ComplexMatrix2.fullTrace (g₁ : Matrices.ComplexMatrix2)).re)
    (A B : Matrices.ComplexMatrix2.specialUnitary) :
    (Matrices.ComplexMatrix2.fullTrace
        ((A⁻¹ * (B⁻¹)⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re =
      (Matrices.ComplexMatrix2.fullTrace
        ((A * B⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re := by
  rw [inv_inv, ← hinv (A⁻¹ * B), mul_inv_rev, inv_inv, hcomm]
theorem splits_levelCorners (P : NormalLevelPair 1) {μ ν : Fin 4} {p : ElementaryPlaquette 1}
    (hcut : DiagonalCutProperties P μ ν p) :
    SplitsThroughCorners P p (levelCornerOne P.normal p) (levelCornerTwo P.normal p) := by
  obtain ⟨-, -, hcorn, -, -, hz, hz', hθ, -, hform⟩ := hcut
  exact ⟨raisedCorner P.normal p, loweredCorner P.normal p, linkToRaised P.normal p,
    linkFromRaised P.normal p, linkToLowered P.normal p, linkFromLowered P.normal p,
    hcorn, hz, hz', hθ, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun U => hform U⟩
theorem splits_levelCorners_swap
    (hcomm : ∀ g₁ g₂ : Matrices.ComplexMatrix2.specialUnitary,
      (Matrices.ComplexMatrix2.fullTrace
          ((g₁ * g₂ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re =
        (Matrices.ComplexMatrix2.fullTrace
          ((g₂ * g₁ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re)
    (hinv : ∀ g₁ : Matrices.ComplexMatrix2.specialUnitary,
      (Matrices.ComplexMatrix2.fullTrace
          ((g₁⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re =
        (Matrices.ComplexMatrix2.fullTrace (g₁ : Matrices.ComplexMatrix2)).re)
    (P : NormalLevelPair 1) {μ ν : Fin 4} {p : ElementaryPlaquette 1}
    (hcut : DiagonalCutProperties P μ ν p) :
    SplitsThroughCorners P p (levelCornerTwo P.normal p) (levelCornerOne P.normal p) := by
  obtain ⟨-, -, hcorn, -, -, hz, hz', hθ, -, hform⟩ := hcut
  refine ⟨raisedCorner P.normal p, loweredCorner P.normal p, (linkFromRaised P.normal p).opposite,
    (linkToRaised P.normal p).opposite, (linkFromLowered P.normal p).opposite,
    (linkToLowered P.normal p).opposite, by rw [hcorn, insert_comm], hz, hz', hθ, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, fun U => ⟨?_, ?_⟩⟩
  · rw [twoLinkHolonomy_opposite, twoLinkHolonomy_opposite]
    exact (hform U).1.trans (re_trace_inv_mul_inv hcomm hinv _ _).symm
  · rw [twoLinkHolonomy_opposite, twoLinkHolonomy_opposite]
    exact congrArg (·⁻¹) (hform U).2
theorem cutsAtDiagonalMirror_of
    (hcomm : ∀ g₁ g₂ : Matrices.ComplexMatrix2.specialUnitary,
      (Matrices.ComplexMatrix2.fullTrace
          ((g₁ * g₂ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re =
        (Matrices.ComplexMatrix2.fullTrace
          ((g₂ * g₁ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re)
    (hinv : ∀ g₁ : Matrices.ComplexMatrix2.specialUnitary,
      (Matrices.ComplexMatrix2.fullTrace
          ((g₁⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re =
        (Matrices.ComplexMatrix2.fullTrace (g₁ : Matrices.ComplexMatrix2)).re)
    (P : NormalLevelPair 1) (hD : DiagonalCutCharacterization P) :
    CutsAtDiagonalMirror P := by
  intro μ ν hlt hnorm _ p
  obtain ⟨hiff, -, -, hdata⟩ := hD μ ν hlt hnorm p
  have hiff' : IsCutBy p P.normal P.level ↔ p.LiesInPlane μ ν ∧
      ∃ y y' : LatticePoint 1, IsDiagonalCornerPair p y y' ∧
        linearHeight P.normal (y : LatticePoint 1) = P.level ∧
        linearHeight P.normal (y' : LatticePoint 1) = P.level :=
    hiff.trans (and_congr_right fun _ => hasDiagonalCornersAtLevel_iff _ _ _)
  refine ⟨hiff', fun y y' hpl hpair hy hy' => ?_⟩
  have hcut := hdata (hiff'.mpr ⟨hpl, y, y', hpair, hy, hy'⟩)
  have hax : p.lowAxis = μ ∧ p.highAxis = ν := by
    rcases hpl with h | ⟨h₁, h₂⟩
    · exact h
    · have hlt' := p.lowAxis_lt_highAxis
      rw [h₁, h₂] at hlt'
      exact absurd hlt' (not_lt.mpr hlt.le)
  obtain ⟨rfl, rfl⟩ := hax
  rcases levelCorners_of_diagonalPair P hnorm hcut hpair hy hy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact splits_levelCorners P hcut
  · exact splits_levelCorners_swap hcomm hinv P hcut
theorem cutsAtLinkMirror_of (P : NormalLevelPair 1) (hH : HeightIncrementAlongLinks P.normal)
    (hL : AxisCutCharacterization P) : CutsAtLinkMirror P := by
  intro μ hμ hlev p
  obtain ⟨hiff, hdata⟩ := hL μ hμ hlev p
  have hbase : ∀ ν : Fin 4, ν ≠ μ →
      linearHeight P.normal (p.corner : LatticePoint 1) = P.level - 1 / 2 →
      HasBaseEdgeAtLevel P.normal P.level ν p := fun ν hν h => by
    obtain ⟨h₁, h₂, -⟩ := hH p.corner ν
    have h₀ : P.normal ν = 0 := by
      rw [hμ]
      simp [coordVec, Pi.single_eq_of_ne hν]
    exact ⟨h, by rw [h₂, h₀] at h₁; linarith⟩
  refine ⟨hiff.trans ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨ν, hν, hpl, hb⟩
    exact ⟨p.corner, ν, hν, (hdata ν hν hpl hb).1, hb.1⟩
  · rintro ⟨x, ν, hν, hsq, hx⟩
    obtain rfl := eq_corner_of_hasCornerSquare hsq
    exact ⟨ν, hν, liesInPlane_of_hasCornerSquare hν hsq, hbase ν hν hx⟩
  · intro x ν hν hsq hx
    obtain rfl := eq_corner_of_hasCornerSquare hsq
    have hcut := hdata ν hν (liesInPlane_of_hasCornerSquare hν hsq) (hbase ν hν hx)
    exact ⟨hcut.2.2.2.1, hcut.2.2.2.2⟩
theorem cutPlaquettesOfMirror_holds (hCut : LinksAndCutPlaquettesAtLevel)
    (hLoop : InfiniteLattice.PlaquetteLoopTraces) : CutPlaquettesOfMirror := by
  obtain ⟨-, hcomm, hinv, -⟩ := hLoop
  intro P
  obtain ⟨hH, -, -, -, hSite, hDiag, hLink⟩ := hCut P
  refine ⟨fun hq hk p => ?_, cutsAtDiagonalMirror_of hcomm hinv P hDiag,
    cutsAtLinkMirror_of P hH hLink⟩
  obtain ⟨k, hk⟩ := hk
  exact hSite ⟨hq, k, by rw [hk, mul_one]⟩ p
end YangMills.Construction.NormalFamilies.MirrorCuts
