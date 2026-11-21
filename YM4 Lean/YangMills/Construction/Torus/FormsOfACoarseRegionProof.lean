import YangMills.Construction.Torus.SeparatedSequenceOfACoarseRegion
import YangMills.Construction.SeparatedSequences.ExpansionsOfACoarseRegionProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace GeneralTorus.CoarseRegionForms
open PeriodicLattice.ScaledFun
variable (R : CoarseCubeRegion)
theorem levelSpacing_zero_eq_h : R.scaleData.levelSpacing 0 = R.scales.fineMesh.h := by apply _root_.YangMills.Construction.GeneralTorus.CoarseCubeRegion.levelSpacing_zero <;> assumption
theorem baseSite_injective : Function.Injective R.baseSite := by apply _root_.YangMills.Construction.GeneralTorus.CoarseRegionExpansions.Restriction.baseSite_injective <;> assumption
theorem baseSite_surjective : Function.Surjective R.baseSite := by
  rintro ⟨y, k, hk⟩
  refine ⟨⟨y, fun μ _ => AddSubgroup.mem_zmultiples_iff.mpr ⟨k μ, ?_⟩⟩, Subtype.ext rfl⟩
  rw [hk, levelSpacing_zero_eq_h]
  simp only [torusProj]
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul, mul_comm]
  rfl
def fineSiteEquiv : PeriodicLattice.GridPoint 4 R.scales.fineMesh ≃ R.scaleData.BaseSite :=
  Equiv.ofBijective R.baseSite ⟨baseSite_injective R, baseSite_surjective R⟩
theorem levelSpacing_coe_ne_zero :
    ((R.scaleData.levelSpacing 0 : ℝ) : AddCircle (R.period : ℝ)) ≠ 0 := by
  have hL : 1 ≤ R.L := R.L_pos
  have hper : 8 ≤ R.period := by
    rw [R.period_eq]
    have := Nat.mul_pos R.blockCount_pos R.L_pos
    omega
  have hper' : (8 : ℝ) ≤ (R.period : ℝ) := by exact_mod_cast hper
  have hξ0 : 0 < R.scaleData.levelSpacing 0 := by
    rw [levelSpacing_zero_eq_h]
    exact R.scales.fineMesh.h_pos
  have hξ1 : R.scaleData.levelSpacing 0 ≤ 1 := by
    rw [R.levelSpacing_zero, PeriodicLattice.fineScale]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hL))
  intro h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).mp h
  rw [zsmul_eq_mul] at hn
  rcases lt_trichotomy n 0 with h0 | h0 | h0
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
    nlinarith
  · subst h0
    simp at hn
    linarith
  · have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    nlinarith
theorem unitStep_injective :
    Function.Injective (unitStep R.scaleData.torusSide (R.scaleData.levelSpacing 0)) := by
  intro μ ν h
  by_contra hne
  have h1 := congrArg
    (fun y : LatticeSite R.scaleData.torusSide (R.scaleData.levelSpacing 0) =>
      (y : R.scaleData.Space) μ) h
  change (((Pi.single μ (R.scaleData.levelSpacing 0) : Fin 4 → ℝ) μ : ℝ) :
      AddCircle (R.period : ℝ)) =
    (((Pi.single ν (R.scaleData.levelSpacing 0) : Fin 4 → ℝ) μ : ℝ) :
      AddCircle (R.period : ℝ)) at h1
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h1
  exact levelSpacing_coe_ne_zero R h1
theorem posBondDir_bondFrom (x : R.scaleData.BaseSite) (μ : Fin 4) :
    ScaleData.posBondDir (ScaleData.bondFrom x μ) = μ := by
  apply unitStep_injective R
  have h := (ScaleData.bondFrom x μ).2.choose_spec
  have h' : (ScaleData.bondFrom x μ).1.tgt - (ScaleData.bondFrom x μ).1.src =
      unitStep R.scaleData.torusSide (R.scaleData.levelSpacing 0) μ := by
    simp [ScaleData.bondFrom, LatticeBond.plus]
  exact h.symm.trans h'
def linkToBond (b : PeriodicLattice.Link 4 R.scales.fineMesh) : R.scaleData.BaseBond :=
  ScaleData.bondFrom (R.baseSite b.2) b.1
theorem linkToBond_bijective : Function.Bijective (linkToBond R) := by
  constructor
  · rintro ⟨μ, x⟩ ⟨ν, y⟩ h
    have hb := congrArg Subtype.val h
    have ht : R.baseSite x = R.baseSite y := congrArg LatticeBond.src hb
    have hxy := baseSite_injective R ht
    subst hxy
    have hd := congrArg ScaleData.posBondDir h
    simp only [linkToBond, posBondDir_bondFrom] at hd
    rw [hd]
  · rintro ⟨c, μ, hμ⟩
    obtain ⟨x, hx⟩ := baseSite_surjective R c.src
    refine ⟨(μ, x), Subtype.ext (LatticeBond.ext hx ?_)⟩
    change R.baseSite x + unitStep R.scaleData.torusSide (R.scaleData.levelSpacing 0) μ = c.tgt
    rw [hx, ← hμ]
    abel
def linkEquiv : PeriodicLattice.Link 4 R.scales.fineMesh ≃ R.scaleData.BaseBond :=
  Equiv.ofBijective (linkToBond R) (linkToBond_bijective R)
def toBasePlaquette
    (q : PeriodicLattice.OrderedAxisPair 4 × PeriodicLattice.GridPoint 4 R.scales.fineMesh) :
    R.scaleData.BasePlaquette :=
  ⟨R.baseSite q.2, q.1.1.1, q.1.1.2, q.1.2⟩
theorem toBasePlaquette_bijective : Function.Bijective (toBasePlaquette R) := by
  constructor
  · rintro ⟨⟨⟨μ, ν⟩, hq⟩, x⟩ ⟨⟨⟨μ', ν'⟩, hq'⟩, y⟩ h
    have hb : R.baseSite x = R.baseSite y := congrArg LatticePlaquette.basePoint h
    have h1 : μ = μ' := congrArg LatticePlaquette.dir₁ h
    have h2 : ν = ν' := congrArg LatticePlaquette.dir₂ h
    have hxy := baseSite_injective R hb
    subst hxy h1 h2
    rfl
  · rintro ⟨y, μ, ν, hq⟩
    obtain ⟨x, rfl⟩ := baseSite_surjective R y
    exact ⟨(⟨(μ, ν), hq⟩, x), rfl⟩
def plaquetteEquiv :
    PeriodicLattice.OrderedAxisPair 4 × PeriodicLattice.GridPoint 4 R.scales.fineMesh ≃
      R.scaleData.BasePlaquette :=
  Equiv.ofBijective (toBasePlaquette R) (toBasePlaquette_bijective R)
end GeneralTorus.CoarseRegionForms
end YangMills.Construction
end
