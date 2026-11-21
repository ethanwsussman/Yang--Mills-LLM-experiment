import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.InequalitiesOnCubesOfTheFirstKindProof
import YangMills.Construction.DirichletOperator.BoundsOfACubeTermOnADivergenceProof
import YangMills.Construction.DirichletOperator.BoundsOnTheOperatorsOfASeparatedSequenceProof
import YangMills.Construction.DirichletOperator.DecayOfAFormFromBoundsOnSmallCubes
import YangMills.Construction.DirichletOperator.GreenOperatorOfACubeOnADivergenceOfACell
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes YangMills.Construction.RemainderEstimates
open YangMills.Construction.DirichletOperator.SmallCubeDecay (PointwiseBounds L2Bounds weightFrom)
open YangMills.Construction.ApproxInverseTerms (SourceSplitsAt)
open YangMills.Construction.EnlargedCubeBounds (EnlargedKernelBounds)
open YangMills.Construction.CubeOperators (chosenConstants cubeDivOne sourceSize IsCubeScale)
open YangMills.Construction.CubeTorus (levelSpacing tensorModulusAt TensorAnchorSupported)
noncomputable section
namespace YangMills.Construction.CubeGreenDivergence
theorem finite_fineBond (hl : Torus.TorusLengthsStatement) (𝒯 : NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
section InnerProduct
variable {𝒯 : NestedRegions}
theorem fwdDiff_add (ν : Fin 4) (A B : 𝒯.FineBond → ℝ) :
    fwdDiff ν (A + B) = fwdDiff ν A + fwdDiff ν B := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.fwdDiff_add <;> assumption
theorem fwdDiff_smul (ν : Fin 4) (c : ℝ) (A : 𝒯.FineBond → ℝ) :
    fwdDiff ν (c • A) = c • fwdDiff ν A := by apply _root_.YangMills.Construction.CubeTermBounds.fwdDiff_smul_fun <;> assumption
end InnerProduct
section Norms
variable {𝒯 : NestedRegions}
theorem supBond_nonneg (f : 𝒯.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
theorem supTensor_nonneg {r : ℕ} (J : 𝒯.Tensor r) : 0 ≤ supTensor J :=
  Real.iSup_nonneg fun _ => supBond_nonneg _
theorem supSite_nonneg (f : 𝒯.FineSite → ℝ) : 0 ≤ supSite f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem holderBond_nonneg (α lam : ℝ) (f : 𝒯.FineBond → ℝ) : 0 ≤ holderBond α lam f := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.holderBond_nonneg <;> assumption
theorem holderTensor_nonneg {r : ℕ} (α lam : ℝ) (J : 𝒯.Tensor r) :
    0 ≤ holderTensor α lam J :=
  Real.iSup_nonneg fun _ => holderBond_nonneg _ _ _
theorem supTensor_le_sourceSize {r : ℕ} (ε lam : ℝ) (J : 𝒯.Tensor r) :
    supTensor J ≤ sourceSize ε lam J :=
  le_add_of_nonneg_left (holderTensor_nonneg _ _ _)
theorem sourceSize_nonneg {r : ℕ} (ε lam : ℝ) (J : 𝒯.Tensor r) :
    0 ≤ sourceSize ε lam J := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.sourceNormSum_nonneg <;> assumption
theorem ltwoTensor_nonneg {r : ℕ} (J : 𝒯.Tensor r) : 0 ≤ ltwoTensor J := by apply _root_.YangMills.Construction.CornerGreen.ltwoTensor_nonneg' <;> assumption
theorem tensorModulusAt_add_smul_le (J J' : 𝒯.Tensor 1) {c : ℝ} (hc : 0 ≤ c)
    (x : 𝒯.FineBond) :
    tensorModulusAt (J + c • J') x ≤ tensorModulusAt J x + c * tensorModulusAt J' x := by
  have hb : ∀ K : 𝒯.Tensor 1, BddAbove (range fun ν => |K ν x|) := fun K =>
    (finite_range _).bddAbove
  have h₀ : ∀ K : 𝒯.Tensor 1, 0 ≤ tensorModulusAt K x := fun K =>
    Real.iSup_nonneg fun _ => abs_nonneg _
  refine Real.iSup_le (fun ν => ?_) (add_nonneg (h₀ J) (mul_nonneg hc (h₀ J')))
  have h₁ : |J ν x| ≤ tensorModulusAt J x := le_ciSup (hb J) ν
  have h₂ : |J' ν x| ≤ tensorModulusAt J' x := le_ciSup (hb J') ν
  calc |(J + c • J') ν x| = |J ν x + c * J' ν x| := by simp
    _ ≤ |J ν x| + |c * J' ν x| := abs_add_le _ _
    _ = |J ν x| + c * |J' ν x| := by rw [abs_mul, abs_of_nonneg hc]
    _ ≤ _ := add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ hc)
theorem nablaOne_add_smul (A B : 𝒯.FineBond → ℝ) (c : ℝ) :
    nablaOne (A + c • B) = nablaOne A + c • nablaOne B := by
  funext ν
  simp only [nablaOne, fwdDiff_add, fwdDiff_smul, Pi.add_apply, Pi.smul_apply]
theorem cubeHalfSide_mono (o : 𝒯.Point) {a b : ℝ} (h : a ≤ b) :
    cubeHalfSide o a ⊆ cubeHalfSide o b := by apply _root_.YangMills.Construction.CubeTermBounds.cubeHalfSide_mono <;> assumption
theorem anchoredIn_mono {X Y : Set 𝒯.Point} (h : X ⊆ Y) {b : 𝒯.FineBond}
    (hb : AnchoredIn X b) : AnchoredIn Y b := h hb
theorem tensorAnchorSupported_mono {X Y : Set 𝒯.Point} (h : X ⊆ Y) {J : 𝒯.Tensor 1}
    (hJ : TensorAnchorSupported X J) : TensorAnchorSupported Y J :=
  fun ν b hb => hJ ν b fun h' => hb (anchoredIn_mono h h')
end Norms
theorem nestedScale_pos (𝒯 : NestedRegions) (n : ℕ) : 0 < 𝒯.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem nestedLevelScale_pos (𝒯 : NestedRegions) (y : 𝒯.Point) : 0 < 𝒯.levelScale y := by apply _root_.YangMills.Construction.RegionSequence.OperatorEstimates.levelScale_pos <;> assumption
theorem two_term_value_bound {C B ξ e W K S a b : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hξ : 0 < ξ)
    (he : 0 ≤ e) (hW : W ≤ S) (hK : K ≤ 4 * S) (ha : a ≤ C * (B * ξ * e * W))
    (hb : b ≤ C * (B * ξ ^ 2 * e * K)) : a + ξ⁻¹ * b ≤ 5 * C * B * ξ * S * e := by apply _root_.YangMills.Construction.CubeTermBounds.two_term_value_bound <;> assumption
theorem two_term_difference_bound {C B ξ e K S b : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hξ : 0 < ξ)
    (he : 0 ≤ e) (hK : K ≤ 4 * S) (hb : b ≤ C * (B * ξ * e * K)) :
    ξ⁻¹ * b ≤ 4 * C * B * S * e := by
  have hP : 0 ≤ C * B * e := by positivity
  have h₃ : ξ⁻¹ * b ≤ ξ⁻¹ * (C * (B * ξ * e * K)) :=
    mul_le_mul_of_nonneg_left hb (inv_pos.2 hξ).le
  have h₄ : ξ⁻¹ * (C * (B * ξ * e * K)) = C * B * e * K := by
    field_simp
  rw [h₄] at h₃
  have := mul_le_mul_of_nonneg_left hK hP
  linarith
variable {𝒮 : NestedRegions} {M : ℕ}
theorem inv_mem_forms (𝔏 : CubeSystem 𝒮)
    (hb : BijOn 𝔏.op (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) 𝔏.forms)
    {u : 𝔏.setting.FineBond → ℝ} (hu : u ∈ 𝔏.forms) : 𝔏.inv u ∈ 𝔏.forms := by apply _root_.YangMills.Construction.CubeTermBounds.inv_mem_forms <;> assumption
structure NearCubeData (L : ℕ) (C₀ : ℝ) (Q : LevelCube 𝒮 M) (y' : 𝒮.Point) (J : 𝒮.Tensor 1)
    (k : Q.system.setting.FineBond → ℝ) : Prop where
  finite_bonds : Finite Q.system.setting.FineBond
  one_le_C : 1 ≤ C₀
  one_le_B : 1 ≤ (chosenConstants L).B
  splits : SourceSplitsAt Q y' J k
  mem_forms : divForm Q J ∈ Q.system.forms
  form_eq : divForm Q J =
    Q.system.inv (cubeDivOne Q (Q.system.pullTensor Q.partitionFn J)) +
      (levelSpacing Q)⁻¹ • Q.system.inv k
  bounds_at : ∀ o, EnlargedKernelBounds (chosenConstants L) C₀ Q o (Q.system.embed y')
    (𝒮.scale (Q.level + 1)) (𝒮.levelScale y')
theorem NearCubeData.pointwise_bounds {L : ℕ} {C₀ : ℝ} {Q : LevelCube 𝒮 M} {y' : 𝒮.Point}
    {J : 𝒮.Tensor 1} {k : Q.system.setting.FineBond → ℝ} (h : NearCubeData L C₀ Q y' J k)
    (hk : k ∈ Q.system.forms) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    PointwiseBounds Q L y'
      (5 * C₀ * (chosenConstants L).B * levelSpacing Q * sourceSize ε (𝒮.levelScale y') J)
      ((2 * C₀ * |(chosenConstants L).Bε ε| + 4 * C₀ * (chosenConstants L).B) *
        sourceSize ε (𝒮.levelScale y') J)
      (divForm Q J) := by
  intro o x hx
  have := h.finite_bonds
  have hB := h.bounds_at o
  have hC : 0 ≤ C₀ := by linarith [h.one_le_C]
  have hBn : 0 ≤ (chosenConstants L).B := by linarith [h.one_le_B]
  have hξ : 0 < levelSpacing Q := nestedScale_pos 𝒮 Q.level
  have hξ₁ : 0 < 𝒮.scale (Q.level + 1) := nestedScale_pos 𝒮 _
  have hy : 0 < 𝒮.levelScale y' := nestedLevelScale_pos 𝒮 y'
  have he : 0 ≤ (chosenConstants L).expDecay Q o (Q.system.embed y') := (Real.exp_pos _).le
  have hde : weightFrom Q L o y' = (chosenConstants L).expDecay Q o (Q.system.embed y') := rfl
  have hx4 : AnchoredIn (cubeHalfSide o (4 * 𝒮.scale (Q.level + 1))) x :=
    anchoredIn_mono (cubeHalfSide_mono o (by linarith)) hx
  have hw := h.splits.pulled_support
  have hw4 := tensorAnchorSupported_mono (cubeHalfSide_mono (Q.system.embed y')
    (show 𝒮.levelScale y' ≤ 4 * 𝒮.levelScale y' by linarith)) hw
  have hT := supTensor_le_sourceSize ε (𝒮.levelScale y') J
  have hK : supBond k ≤ 4 * sourceSize ε (𝒮.levelScale y') J := by
    have := h.splits.rest_sup
    linarith
  have hinv : 0 ≤ (levelSpacing Q)⁻¹ := (inv_pos.2 hξ).le
  rw [hde]
  refine ⟨?_, ?_⟩
  · have h₁ := hB.source _ hw4 x hx4
    have h₂ := hB.value k hk h.splits.rest_support x hx4
    have h₃ := two_term_value_bound hC hBn hξ he (h.splits.pulled_sup.trans hT) hK h₁ h₂
    rw [h.form_eq]
    refine le_trans ?_ h₃
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hinv]
  · have h₁ := hB.source_difference ε hε₀ hε₁ _ hw x hx4
    have h₂ := hB.difference k hk h.splits.rest_support x hx4
    have h₃ := two_term_difference_bound hC hBn hξ he hK h₂
    have h₄ := h.splits.pulled_size ε hε₀.le hε₁
    have h₅ : C₀ * ((chosenConstants L).Bε ε *
        (chosenConstants L).expDecay Q o (Q.system.embed y') *
        sourceSize ε (𝒮.levelScale y') (Q.system.pullTensor Q.partitionFn J)) ≤
        2 * C₀ * |(chosenConstants L).Bε ε| * sourceSize ε (𝒮.levelScale y') J *
          (chosenConstants L).expDecay Q o (Q.system.embed y') := by
      have hF0 := sourceSize_nonneg ε (𝒮.levelScale y') (Q.system.pullTensor Q.partitionFn J)
      have hP : 0 ≤ C₀ * |(chosenConstants L).Bε ε| *
          (chosenConstants L).expDecay Q o (Q.system.embed y') := by positivity
      have h₆ := mul_le_mul_of_nonneg_left h₄ hP
      have h₇ : (chosenConstants L).Bε ε *
          (chosenConstants L).expDecay Q o (Q.system.embed y') *
          sourceSize ε (𝒮.levelScale y') (Q.system.pullTensor Q.partitionFn J) ≤
          |(chosenConstants L).Bε ε| * (chosenConstants L).expDecay Q o (Q.system.embed y') *
          sourceSize ε (𝒮.levelScale y') (Q.system.pullTensor Q.partitionFn J) := by
        gcongr
        exact le_abs_self _
      have h₈ := mul_le_mul_of_nonneg_left h₇ hC
      nlinarith
    rw [h.form_eq, nablaOne_add_smul]
    refine (tensorModulusAt_add_smul_le _ _ hinv x).trans ?_
    have := h₁.trans h₅
    nlinarith
end YangMills.Construction.CubeGreenDivergence
