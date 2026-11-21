import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.InequalitiesOnCubesOfTheFirstKindProof
import YangMills.Construction.DirichletOperator.BoundsOfTheLocalOperatorsOnEnlargedCubesProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
open YangMills.Construction.CubeTorus (torusSetting levelSpacing tensorModulusAt TensorAnchorSupported)
open YangMills.Construction.CubeOperators
  (RegularityConstants cubeDivOne IsCubeScale cutoffSize sourceSize chosenConstants)
open YangMills.Construction.LeibnizHolder (supBondOn supTensorOn)
open YangMills.Construction.EnlargedCubeBounds (EnlargedKernelBounds)
open YangMills.Construction.ApproxInverseScales (blockLowerBound outerCube)
noncomputable section
namespace YangMills.Construction.CubeDivTermBound
section Lattice
variable {𝒯 : NestedRegions}
theorem finite_fineBond (hl : TorusLengthsStatement) (𝒯 : NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem bondInner_add_left [Finite 𝒯.FineBond] (A B g : 𝒯.FineBond → ℝ) :
    bondInner (A + B) g = bondInner A g + bondInner B g := by apply _root_.YangMills.Construction.RegionSequence.Positivity.bondInner_add_left <;> assumption
theorem eq_of_bondInner_eq [Finite 𝒯.FineBond] (F : Submodule ℝ (𝒯.FineBond → ℝ))
    {X Y : 𝒯.FineBond → ℝ} (hX : X ∈ F) (hY : Y ∈ F)
    (h : ∀ v ∈ F, bondInner X v = bondInner Y v) : X = Y := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.eq_of_bondInner_eq <;> assumption
theorem fwdDiff_add (ν : Fin 4) (A B : 𝒯.FineBond → ℝ) :
    fwdDiff ν (A + B) = fwdDiff ν A + fwdDiff ν B := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.fwdDiff_add <;> assumption
theorem nablaOne_add (A B : 𝒯.FineBond → ℝ) : nablaOne (A + B) = nablaOne A + nablaOne B := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.nablaOne_add <;> assumption
theorem supBond_nonneg (f : 𝒯.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
theorem supTensor_nonneg {r : ℕ} (J : 𝒯.Tensor r) : 0 ≤ supTensor J :=
  Real.iSup_nonneg fun _ => supBond_nonneg _
theorem supBond_smul_le [Finite 𝒯.FineBond] {s t : ℝ} (hs : 0 ≤ s) (f : 𝒯.FineBond → ℝ)
    (h : supBond f ≤ t) : supBond (s • f) ≤ s * t := by
  refine Real.iSup_le (fun b => ?_) (mul_nonneg hs ((supBond_nonneg f).trans h))
  have hb : ‖f b‖ ≤ supBond f := le_ciSup (Set.finite_range fun b => ‖f b‖).bddAbove b
  calc ‖(s • f) b‖ = s * ‖f b‖ := by
        rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hs]
    _ ≤ s * t := mul_le_mul_of_nonneg_left (hb.trans h) hs
theorem le_holderBond [Finite 𝒯.FineBond] (α lam : ℝ) (f : 𝒯.FineBond → ℝ) {b b' : 𝒯.FineBond}
    (hd : b.dir = b'.dir) (h₀ : 0 < siteLOneDist b.source b'.source)
    (h₁ : siteLOneDist b.source b'.source ≤ lam) :
    (lam / siteLOneDist b.source b'.source) ^ α * ‖f b' - f b‖ ≤ holderBond α lam f := by apply _root_.YangMills.Construction.CubeTermBounds.le_holderBond <;> assumption
theorem holderBond_nonneg (α lam : ℝ) (f : 𝒯.FineBond → ℝ) : 0 ≤ holderBond α lam f := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.holderBond_nonneg <;> assumption
theorem holderTensor_nonneg {r : ℕ} (α lam : ℝ) (J : 𝒯.Tensor r) :
    0 ≤ holderTensor α lam J :=
  Real.iSup_nonneg fun _ => holderBond_nonneg _ _ _
theorem supTensor_le_sourceSize {r : ℕ} (ε lam : ℝ) (J : 𝒯.Tensor r) :
    supTensor J ≤ sourceSize ε lam J :=
  le_add_of_nonneg_left (holderTensor_nonneg _ _ _)
theorem sourceSize_nonneg {r : ℕ} (ε lam : ℝ) (J : 𝒯.Tensor r) :
    0 ≤ sourceSize ε lam J := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.sourceNormSum_nonneg <;> assumption
theorem holderBond_le_holderTensor (α lam : ℝ) (ζ : 𝒯.FineSite → ℝ) (ν : Fin 4)
    (u : 𝒯.FineBond → ℝ) :
    holderBond α lam (smulSiteBond ζ (fwdDiff ν u)) ≤
      holderTensor α lam (smulSiteTensor ζ (nablaOne u)) :=
  le_ciSup (f := fun μ : Fin 1 → Fin 4 =>
    holderBond α lam (smulSiteTensor ζ (nablaOne u) μ))
    (Set.finite_range _).bddAbove (fun _ => ν)
theorem abs_le_tensorModulusAt {r : ℕ} (J : 𝒯.Tensor r) (ν : Fin r → Fin 4) (x : 𝒯.FineBond) :
    |J ν x| ≤ tensorModulusAt J x :=
  le_ciSup (f := fun μ => |J μ x|) (Set.finite_range _).bddAbove ν
end Lattice
section Operators
variable {𝒮 : NestedRegions} {M : ℕ}
theorem levelSpacing_pos (Q : LevelCube 𝒮 M) : 0 < levelSpacing Q := by apply _root_.YangMills.Construction.EnlargedCubeBounds.Assembly.levelSpacing_pos <;> assumption
theorem inv_mem_forms {c : RegularityConstants} {Q : LevelCube 𝒮 M} (h : c.CubeHolds Q)
    {u : Q.system.setting.FineBond → ℝ} (hu : u ∈ Q.system.forms) :
    Q.system.inv u ∈ Q.system.forms := by
  obtain ⟨g, hg, rfl⟩ := h.invertible.surjOn hu
  exact (Classical.epsilon_spec
    (p := fun g' => g' ∈ (Q.system.forms : Set (Q.system.setting.FineBond → ℝ)) ∧
      Q.system.op g' = Q.system.op g) ⟨g, hg, rfl⟩).1
end Operators
end YangMills.Construction.CubeDivTermBound
