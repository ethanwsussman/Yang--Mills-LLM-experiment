import YangMills.Construction.DirichletOperator.FactsOfTheSettingInLevelUnitsProof
import YangMills.Construction.GeneralTorus.ShellsCubesAndScaledDistance
import YangMills.Construction.SeparatedSequences.NumbersOfThePropagatorServeOnTheTori
import YangMills.Construction.Torus.ObjectsOfASequenceOfRegionsOnAGeneralTorus
import YangMills.Construction.Torus.PhysicalTorusInLevelUnitsAsATorusOfGeneralSide
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal ContDiff
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace GeneralTorus.GreenBounds.FromPropagator
open RegionObjects
variable {L : ℕ}
variable {W : GaugeSetting} {h : SetsAreCubeUnions W}
theorem finite_fineSite (hs : Agrees W h) : Finite (toNestedRegions W h).FineSite :=
  Finite.of_injective _ hs.base_sites.1
theorem finite_fineBond (hs : Agrees W h) : Finite (toNestedRegions W h).FineBond := by
  have := finite_fineSite hs
  refine Finite.of_surjective (fun p : (toNestedRegions W h).FineSite × Fin 4 =>
    (⟨p.1, p.2⟩ : (toNestedRegions W h).FineBond)) ?_
  rintro ⟨x, μ⟩
  exact ⟨(x, μ), rfl⟩
theorem bondFrom_src_posBondDir {D : ScaleData} (c : D.BaseBond) :
    ScaleData.bondFrom c.1.src (ScaleData.posBondDir c) = c := by
  apply Subtype.ext
  apply LatticeBond.ext
  · rfl
  · have hc := c.2.choose_spec
    change c.1.tgt - c.1.src = unitStep D.torusSide (D.levelSpacing 0) (ScaleData.posBondDir c) at hc
    change c.1.src + unitStep D.torusSide (D.levelSpacing 0) (ScaleData.posBondDir c) = c.1.tgt
    rw [← hc]
    abel
theorem supNormVec_eq_norm (v : Fin 4 → ℝ) : supNormVec v = ‖v‖ := by apply _root_.YangMills.Construction.LevelUnitFacts.supNormVec_eq_norm <;> assumption
theorem supNorm_eq_torusSupNorm {S : ℝ} (x : Torus4 S) : Torus.supNorm x = torusSupNorm x := by
  unfold Torus.supNorm torusSupNorm
  congr 1
  ext r
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, supNormVec_eq_norm v⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, supNormVec_eq_norm v⟩
theorem cubeAt_eq_supCube {S : ℝ} (c : Torus4 S) (σ : ℝ) :
    Torus.cubeAt c σ = supCube σ c := by
  ext p
  simp only [Torus.cubeAt, supCube, mem_ofPred_eq]
  rw [supNorm_eq_torusSupNorm]
section Physical
variable (s : LevelUnitChain L)
include s in
theorem blockingFactor_pos : (0 : ℝ) < L := by
  have := s.blocking.thirteen_le
  exact_mod_cast (by omega : 0 < L)
end Physical
section Holder
open RegionSequence.NestedRegions
variable (s : LevelUnitChain L) {h : SetsAreCubeUnions s.setting}
end Holder
end GeneralTorus.GreenBounds.FromPropagator
namespace SeparatedClasses
open SingleSequence
end SeparatedClasses
end YangMills.Construction
