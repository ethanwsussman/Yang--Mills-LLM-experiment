import YangMills.Construction.Torus.GreenIdentitiesAndBlockForm
import YangMills.Construction.Torus.InverseOfAMatrixWithExponentialDecayProof
import YangMills.Construction.Lattice.BlocksCorridorsPivotBondsAndTheWeightsOfTheOneStepAverage
import YangMills.Construction.Lattice.BondEnergyCurlAverageBound
import YangMills.Construction.Torus.ScalarProductsTransposesAndProjectionsOfASettingProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.GeneralTorus.CoarseLapLowerBounds
open GaugeSetting
theorem blockFactor_pos (Λ : UnitSpacingLattice) : 0 < Λ.blockFactor := by
  cases Λ with
  | intLattice L hb _ =>
    have := hb.thirteen_le
    show 0 < L
    omega
  | torusLevel D _ _ =>
    have := D.blocking.thirteen_le
    show 0 < D.L
    omega
section Pivots
variable {Λ : UnitSpacingLattice}
variable [Finite Λ.Edge]
theorem blockAverage_add (hQ : UnitSpacingLattice.CubesCorridorsAndBlockAverageWeights)
    (c : Λ.CenterEdge) (g h : Λ.Edge → ℝ) :
    UnitSpacingLattice.blockAverage (g + h) c =
      UnitSpacingLattice.blockAverage g c + UnitSpacingLattice.blockAverage h c := by
  obtain ⟨-, -, -, hc⟩ := hQ Λ
  obtain ⟨-, -, hf, -⟩ := hc c
  rw [hf, hf, hf, ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finsum_congr fun b => by simp [mul_add]
end Pivots
theorem finite_coarseBond (W : GaugeSetting) : Finite W.CoarseBond := by apply _root_.YangMills.Construction.GeneralTorus.InnerProductsAdjointsProjections.finite_coarseBond <;> assumption
section UnitLevel
variable {W : GaugeSetting} {unit : W.data.levelSpacing W.data.lastLevel = 1}
  {multiple : IsEvenMultipleOf W.data.torusSide (W.data.L : ℝ)}
include unit multiple in
theorem unitStep_injective {μ ν : Fin 4}
    (h : unitStep W.data.torusSide (W.data.levelSpacing W.data.lastLevel) μ =
      unitStep W.data.torusSide (W.data.levelSpacing W.data.lastLevel) ν) : μ = ν := by
  by_contra hne
  have h1 := congrArg (fun x : W.data.SiteAt W.data.lastLevel => (x : W.data.Space) μ) h
  simp only [unitStep, coordPoint, TorusMetric.torusProj, Pi.single_eq_same,
    Pi.single_eq_of_ne hne, unit] at h1
  have h2 : ((1 : ℝ) : AddCircle W.data.torusSide) = 0 := by simpa using h1
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h2
  obtain ⟨k, -, hS⟩ := multiple
  rw [hS, zsmul_eq_mul] at hn
  have h3 : (n * (2 * k * W.data.L) : ℤ) = 1 := by exact_mod_cast hn
  have h4 : (2 : ℤ) ∣ 1 := ⟨n * k * W.data.L, by rw [← h3]; ring⟩
  norm_num at h4
end UnitLevel
end YangMills.Construction.GeneralTorus.CoarseLapLowerBounds
