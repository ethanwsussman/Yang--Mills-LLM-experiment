import YangMills.Construction.RunningCouplingSlope.PositiveBondsOfALevelAreThoseOfAFrame
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower BlockAverages
namespace FrameEdges
variable {L n : ℕ}
private def coordSite (d : ℤ) (z : Fin 4 → ℤ) : PeriodicLattice.Site L n d :=
  PeriodicLattice.offsetSite 0 z
private theorem coe_coordSite (d : ℤ) (z : Fin 4 → ℤ) (ν : Fin 4) :
    ((coordSite (L := L) (n := n) d z : PeriodicLattice.Site L n d) : PeriodicLattice.FourTorus L n) ν =
      (((z ν : ℝ) * PeriodicLattice.meshSize L d : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
  have h1 : ((coordSite (L := L) (n := n) d z : PeriodicLattice.Site L n d) : PeriodicLattice.FourTorus L n) =
      ∑ μ, z μ • PeriodicLattice.pointOnAxis L n μ (PeriodicLattice.meshSize L d) := by
    show (PeriodicLattice.sublattice L n d).subtype (coordSite d z) = _
    simp only [coordSite, PeriodicLattice.offsetSite, zero_add]
    rw [map_sum]
    exact Finset.sum_congr rfl fun μ _ => map_zsmul _ _ _
  rw [h1, Finset.sum_apply, Finset.sum_eq_single ν]
  · simp only [Pi.smul_apply, PeriodicLattice.pointOnAxis, Pi.single_eq_same]
    rw [← zsmul_eq_mul]
    exact (QuotientAddGroup.mk_zsmul _ _ _).symm
  · intro b _ hb
    simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hb.symm]
  · simp
private theorem coordSite_eq_iff {d : ℤ} {P : ℕ} (hs : PeriodicLattice.meshSize L d ≠ 0)
    (hP : (P : ℝ) * PeriodicLattice.meshSize L d = PeriodicLattice.torusSide L n) (z z' : Fin 4 → ℤ) :
    coordSite (L := L) (n := n) d z = coordSite d z' ↔ ∀ ν, ∃ m : ℤ, z ν - z' ν = m * P := by
  have one : ∀ a b : ℤ, ((((a : ℝ) * PeriodicLattice.meshSize L d : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) =
      (((b : ℝ) * PeriodicLattice.meshSize L d : ℝ) : AddCircle (PeriodicLattice.torusSide L n))) ↔
      ∃ m : ℤ, a - b = m * P := by
    intro a b
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      rw [← hP, zsmul_eq_mul, ← mul_assoc, ← sub_mul] at hm
      have := mul_right_cancel₀ hs hm
      exact_mod_cast this.symm
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      rw [← hP, zsmul_eq_mul, ← mul_assoc, ← sub_mul]
      congr 1
      exact_mod_cast hm.symm
  constructor
  · intro h ν
    have := congrFun (congrArg (fun x : PeriodicLattice.Site L n d => (x : PeriodicLattice.FourTorus L n)) h) ν
    simp only [coe_coordSite] at this
    exact (one _ _).mp this
  · intro h
    refine Subtype.ext (funext fun ν => ?_)
    rw [coe_coordSite, coe_coordSite]
    exact (one _ _).mpr (h ν)
private theorem exists_coordSite_eq (d : ℤ) (x : PeriodicLattice.Site L n d) :
    ∃ z : Fin 4 → ℤ, x = coordSite d z := by
  obtain ⟨z, hz⟩ := x.2
  refine ⟨z, Subtype.ext (funext fun ν => ?_)⟩
  rw [coe_coordSite, hz ν]
private theorem unitStep_eq_coordSite (d : ℤ) (μ : Fin 4) :
    PeriodicLattice.unitStep L n d μ = coordSite d (Pi.single μ 1) := by
  refine Subtype.ext (funext fun ν => ?_)
  rw [coe_coordSite]
  by_cases h : ν = μ
  · subst h
    simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis]
  · simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
end FrameEdges
open FrameEdges in
theorem framePositiveEdgesBijective : FramePositiveEdgesBijective := by
  intro L hL n k j hn hj F l hper
  have hL0 : 0 < L := by have := hL.2; omega
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL0.ne'
  set P : ℕ := 2 * L ^ (n + (k - j)) with hPdef
  have hs : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j) ≠ 0 := by
    unfold PeriodicLattice.meshSize
    exact zpow_ne_zero _ hLr
  have hP : (P : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j) =
      PeriodicLattice.torusSide L n := by
    have e : PeriodicLattice.levelDepth k j = ((k - j : ℕ) : ℤ) := by
      simp [PeriodicLattice.levelDepth, Nat.cast_sub hj]
    simp only [PeriodicLattice.meshSize, PeriodicLattice.torusSide, hPdef, e]
    push_cast
    rw [zpow_neg, zpow_natCast, pow_add]
    field_simp
  have hP2 : 2 ≤ P := by
    have : 0 < L ^ (n + (k - j)) := pow_pos hL0 _
    omega
  have hinj : ∀ x x' : F.Site l,
      coordSite (L := L) (n := n) (PeriodicLattice.levelDepth k j) (siteCoords x) =
        coordSite _ (siteCoords x') → x = x' := by
    intro x x' h
    funext ν
    obtain ⟨m, hm⟩ := (coordSite_eq_iff hs hP _ _).mp h ν
    rw [← ZMod.intCast_zmod_cast (x ν), ← ZMod.intCast_zmod_cast (x' ν)]
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨-m, ?_⟩
    have hc : ((F.period l ν : ℕ) : ℤ) = (P : ℤ) := by exact_mod_cast hper ν
    rw [hc]
    have : siteCoords x' ν - siteCoords x ν = -(m * P) := by linarith
    show siteCoords x' ν - siteCoords x ν = _
    rw [this]
    ring
  refine ⟨fun b => ⟨b.2, ?_⟩, ?_, ?_⟩
  · simp [edgeOfCoords, PeriodicLattice.Bond.forwardFrom]
  · rintro ⟨x, μ⟩ ⟨x', μ'⟩ h
    have ht : coordSite (L := L) (n := n) (PeriodicLattice.levelDepth k j) (siteCoords x) =
        coordSite _ (siteCoords x') :=
      congrArg PeriodicLattice.Bond.source h
    have hx := hinj x x' ht
    subst hx
    have hh := congrArg PeriodicLattice.Bond.target h
    simp only [edgeOfCoords, PeriodicLattice.Bond.forwardFrom] at hh
    have hst := add_left_cancel hh
    rw [unitStep_eq_coordSite, unitStep_eq_coordSite] at hst
    by_contra hne
    have hμ : μ ≠ μ' := fun e => hne (by rw [e])
    obtain ⟨m, hm⟩ := (coordSite_eq_iff hs hP _ _).mp hst μ
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hμ, sub_zero] at hm
    have h1 : (P : ℤ) ∣ 1 := ⟨m, by rw [hm]; ring⟩
    have := Int.le_of_dvd one_pos h1
    omega
  · intro c hc
    obtain ⟨μ, hμ⟩ := hc
    obtain ⟨z, hz⟩ := exists_coordSite_eq _ c.source
    let x : F.Site l := siteOfCoords l z
    have e : coordSite (L := L) (n := n) (PeriodicLattice.levelDepth k j) (siteCoords x) = c.source := by
      rw [hz, coordSite_eq_iff hs hP]
      intro ν
      have h₁ : (((siteCoords x ν : ℤ)) : ZMod (F.period l ν)) = (z ν : ZMod (F.period l ν)) :=
        ZMod.intCast_zmod_cast _
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h₁
      obtain ⟨m, hm⟩ := h₁
      refine ⟨-m, ?_⟩
      have hc : ((F.period l ν : ℕ) : ℤ) = (P : ℤ) := by exact_mod_cast hper ν
      rw [hc] at hm
      have : siteCoords x ν - z ν = -(z ν - siteCoords x ν) := by ring
      rw [this, hm]
      ring
    refine ⟨(x, μ), ?_⟩
    have ehead : c.target = c.source + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ := by
      rw [← hμ]
      abel
    cases c with
    | mk src tgt adj =>
      simp only at e ehead
      subst ehead
      subst e
      rfl
end YangMills.Construction.RunningCouplingSlope
end
