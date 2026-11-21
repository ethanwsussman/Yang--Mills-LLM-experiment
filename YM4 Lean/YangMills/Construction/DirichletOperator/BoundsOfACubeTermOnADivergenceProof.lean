import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.AdjointTermsAsOperatorsOnFormsProof
import YangMills.Construction.DirichletOperator.BoundsOfTheLocalOperatorsOnEnlargedCubes
import YangMills.Construction.DirichletOperator.DivergenceSourceOnTheTorusOfACube
import YangMills.Construction.DirichletOperator.HolderSeminormsOfAFormOfACubeNearASite
import YangMills.Construction.DirichletOperator.RegularityOfTheLocalOperatorsProof
import YangMills.Construction.DirichletOperator.SupremaOfACubeTermNearASite
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
open YangMills.Construction.PartitionCubes
open YangMills.Construction.CubeOperators (chosenConstants cubeDivOne cutoffSize)
open YangMills.Construction.CubeTorus (levelSpacing TensorAnchorSupported)
open YangMills.Construction.ApproxInverseScales
noncomputable section
namespace YangMills.Construction.CubeTermBounds
theorem finite_fineBond (hl : TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
section Pairing
variable {𝒯 : NestedRegions}
theorem bondInner_comm (A B : 𝒯.FineBond → ℝ) : bondInner A B = bondInner B A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
theorem bondInner_add_left [Finite 𝒯.FineBond] (A B g : 𝒯.FineBond → ℝ) :
    bondInner (A + B) g = bondInner A g + bondInner B g := by apply _root_.YangMills.Construction.RegionSequence.Positivity.bondInner_add_left <;> assumption
theorem eq_of_bondInner_eq [Finite 𝒯.FineBond] (F : Submodule ℝ (𝒯.FineBond → ℝ))
    {X Y : 𝒯.FineBond → ℝ} (hX : X ∈ F) (hY : Y ∈ F)
    (h : ∀ v ∈ F, bondInner X v = bondInner Y v) : X = Y := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.eq_of_bondInner_eq <;> assumption
theorem fwdDiff_smul_fun (ν : Fin 4) (c : ℝ) (A : 𝒯.FineBond → ℝ) :
    NestedRegions.fwdDiff ν (c • A) = c • NestedRegions.fwdDiff ν A := by
  funext b
  simp only [NestedRegions.fwdDiff, Pi.smul_apply, smul_eq_mul]
  ring
end Pairing
section Sizes
variable {𝒯 : NestedRegions}
theorem supBond_nonneg (f : 𝒯.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
theorem supTensor_nonneg {r : ℕ} (J : 𝒯.Tensor r) : 0 ≤ supTensor J :=
  Real.iSup_nonneg fun _ => supBond_nonneg _
theorem holderBond_nonneg (α lam : ℝ) (f : 𝒯.FineBond → ℝ) : 0 ≤ holderBond α lam f := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.holderBond_nonneg <;> assumption
theorem le_holderBond [Finite 𝒯.FineBond] (α lam : ℝ) (f : 𝒯.FineBond → ℝ) {b b' : 𝒯.FineBond}
    (hd : b.dir = b'.dir) (h₀ : 0 < siteLOneDist b.source b'.source)
    (h₁ : siteLOneDist b.source b'.source ≤ lam) :
    (lam / siteLOneDist b.source b'.source) ^ α * ‖f b' - f b‖ ≤ holderBond α lam f := by
  refine le_csSup ?_ ⟨b, b', hd, h₀, h₁, rfl⟩
  refine (Set.finite_range fun p : 𝒯.FineBond × 𝒯.FineBond =>
    (lam / siteLOneDist p.1.source p.2.source) ^ α * ‖f p.2 - f p.1‖).bddAbove.mono ?_
  rintro _ ⟨c, c', -, -, -, rfl⟩
  exact ⟨(c, c'), rfl⟩
theorem cubeHalfSide_mono (o : 𝒯.Point) {a b : ℝ} (h : a ≤ b) :
    cubeHalfSide o a ⊆ cubeHalfSide o b := by
  intro p hp
  have hp' : supNorm (p - o) ≤ 2 * a / 2 := hp
  show supNorm (p - o) ≤ 2 * b / 2
  linarith
theorem anchoredIn_mono {X Y : Set 𝒯.Point} (h : X ⊆ Y) {b : 𝒯.FineBond} (hb : AnchoredIn X b) :
    AnchoredIn Y b := h hb
theorem tensorAnchorSupported_mono {X Y : Set 𝒯.Point} (h : X ⊆ Y) {J : 𝒯.Tensor 1}
    (hJ : TensorAnchorSupported X J) : TensorAnchorSupported Y J :=
  fun ν b hb => hJ ν b fun h' => hb (anchoredIn_mono h h')
end Sizes
theorem nestedScale_pos (𝒯 : NestedRegions) (n : ℕ) : 0 < 𝒯.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem supNorm_target_sub_source {𝒯 : NestedRegions} (b : 𝒯.FineBond) :
    supNorm ((b.target : 𝒯.Point) - (b.source : 𝒯.Point)) ≤ 𝒯.ξ := by apply _root_.YangMills.Construction.RegionSequence.AnchorCutIdentities.supNorm_target_sub_source <;> assumption
theorem two_term_value_bound {C B ξ e W K S a b : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hξ : 0 < ξ)
    (he : 0 ≤ e) (hW : W ≤ S) (hK : K ≤ 4 * S) (ha : a ≤ C * (B * ξ * e * W))
    (hb : b ≤ C * (B * ξ ^ 2 * e * K)) : a + ξ⁻¹ * b ≤ 5 * C * B * ξ * S * e := by
  have hP : 0 ≤ C * B * ξ * e := by positivity
  have h₁ : a ≤ C * B * ξ * e * S :=
    ha.trans (by
      have := mul_le_mul_of_nonneg_left hW hP
      linarith)
  have h₂ : ξ⁻¹ * b ≤ C * B * ξ * e * (4 * S) := by
    have h₃ : ξ⁻¹ * b ≤ ξ⁻¹ * (C * (B * ξ ^ 2 * e * K)) :=
      mul_le_mul_of_nonneg_left hb (inv_pos.2 hξ).le
    have h₄ : ξ⁻¹ * (C * (B * ξ ^ 2 * e * K)) = C * B * ξ * e * K := by
      field_simp
    rw [h₄] at h₃
    exact h₃.trans (mul_le_mul_of_nonneg_left hK hP)
  linarith
variable {𝒮 : NestedRegions} {M : ℕ}
theorem inv_mem_forms (𝔏 : CubeSystem 𝒮)
    (hb : BijOn 𝔏.op (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) 𝔏.forms)
    {u : 𝔏.setting.FineBond → ℝ} (hu : u ∈ 𝔏.forms) : 𝔏.inv u ∈ 𝔏.forms := by
  obtain ⟨g, hg, rfl⟩ := hb.surjOn hu
  exact (Classical.epsilon_spec
    (p := fun g' => g' ∈ (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) ∧
      𝔏.op g' = 𝔏.op g) ⟨g, hg, rfl⟩).1
end YangMills.Construction.CubeTermBounds
