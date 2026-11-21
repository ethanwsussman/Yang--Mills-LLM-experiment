import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.FactsOfTheCellsOfACube
import YangMills.Construction.DirichletOperator.ApproximateInverseAndLocalDefects
import YangMills.Construction.DirichletOperator.SourcesOfTheAdjointDefectOfACube
import YangMills.Construction.DirichletOperator.TermsOfTheRemainder
import YangMills.Construction.DirichletOperator.PropagatorBoundsForDivergenceSourcesProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
open YangMills.Construction.PartitionCubes YangMills.Construction.RemainderEstimates
noncomputable section
namespace YangMills.Construction.CubeAdjointDefect.LocalPartsAtCells
section SupremaOverBonds
theorem finite_fineBond (hT : Torus.TorusLengthsStatement) (𝒯 : NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
variable {𝒯 : NestedRegions}
theorem supBond_nonneg (f : 𝒯.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
theorem supTensor_nonneg {r : ℕ} (J : 𝒯.Tensor r) : 0 ≤ supTensor J :=
  Real.iSup_nonneg fun _ => supBond_nonneg _
theorem norm_le_supBond [Finite 𝒯.FineBond] (f : 𝒯.FineBond → ℝ) (b : 𝒯.FineBond) :
    ‖f b‖ ≤ supBond f :=
  le_ciSup (f := fun b => ‖f b‖) (Set.finite_range _).bddAbove b
theorem norm_le_supTensor [Finite 𝒯.FineBond] {r : ℕ} (J : 𝒯.Tensor r) (ν) (b : 𝒯.FineBond) :
    ‖J ν b‖ ≤ supTensor J :=
  (norm_le_supBond (J ν) b).trans
    (le_ciSup (f := fun ν => supBond (J ν)) (Set.finite_range _).bddAbove ν)
theorem supBond_mono [Finite 𝒯.FineBond] {f g : 𝒯.FineBond → ℝ} (h : ∀ b, ‖f b‖ ≤ ‖g b‖) :
    supBond f ≤ supBond g :=
  Real.iSup_le (fun b => (h b).trans (norm_le_supBond g b)) (supBond_nonneg g)
theorem supTensor_mono [Finite 𝒯.FineBond] {r : ℕ} {J J' : 𝒯.Tensor r}
    (h : ∀ ν b, ‖J ν b‖ ≤ ‖J' ν b‖) : supTensor J ≤ supTensor J' :=
  Real.iSup_le (fun ν => Real.iSup_le
    (fun b => (h ν b).trans (norm_le_supTensor J' ν b)) (supTensor_nonneg J')) (supTensor_nonneg J')
theorem restrictBonds_of_mem {X : Set 𝒯.Point} {b : 𝒯.FineBond} (h : AnchoredIn X b)
    (f : 𝒯.FineBond → ℝ) : restrictBonds X f b = f b :=
  Set.indicator_of_mem (s := {b | AnchoredIn X b}) h f
theorem norm_restrictBonds_le (X : Set 𝒯.Point) (f : 𝒯.FineBond → ℝ) (b : 𝒯.FineBond) :
    ‖restrictBonds X f b‖ ≤ ‖f b‖ := by
  by_cases h : AnchoredIn X b
  · rw [restrictBonds_of_mem h]
  · have h' : restrictBonds X f b = 0 := Set.indicator_of_notMem (s := {b | AnchoredIn X b}) h f
    rw [h', norm_zero]
    exact norm_nonneg _
end SupremaOverBonds
theorem weightedDist_nonneg (𝒮 : NestedRegions) (y y' : 𝒮.Point) : 0 ≤ 𝒮.weightedDist y y' := by apply _root_.YangMills.Construction.DivSourceEstimate.weightedDist_nonneg <;> assumption
section OneCube
variable {𝒮 : NestedRegions} {M : ℕ}
theorem cell_term_le (hT : Torus.TorusLengthsStatement) (Q : LevelCube 𝒮 M) {C₀ : ℝ}
    {w : 𝒮.oneForms →ₗ[ℝ] Q.system.setting.Tensor 1}
    {u : 𝒮.oneForms →ₗ[ℝ] Q.system.forms} (hloc : Q.AdjointDivergenceForm C₀ w u) (A : 𝒮.oneForms)
    (hξ : 0 < 𝒮.scale Q.level) (v : Q.system.setting.Point) :
    𝒮.scale Q.level * supTensor (Q.restrictTensorToCell v (w A)) +
        𝒮.scale Q.level ^ 2 *
          supBond (Q.restrictBondsToCell v (u A : Q.system.setting.FineBond → ℝ)) ≤
      max C₀ 0 * (M : ℝ)⁻¹ * supBond (A : 𝒮.FineBond → ℝ) := by
  have := finite_fineBond hT Q.system.setting
  have := finite_fineBond hT 𝒮
  have hb' : 𝒮.scale Q.level * supTensor (restrictTensor (Q.toCubeTorusSet univ) (w A)) +
      𝒮.scale Q.level ^ 2 * supBond (restrictBonds (Q.toCubeTorusSet univ) (u A : _ → ℝ)) ≤
      C₀ * (M : ℝ)⁻¹ * supBond (restrictBonds (Q.supNbhd univ) (A : 𝒮.FineBond → ℝ)) :=
    hloc.bound .sup univ A
  have hmono : Q.toCubeTorusSet (Q.supNbhd Q.supp) ⊆ Q.toCubeTorusSet univ := by
    rintro _ ⟨p, ⟨-, hp⟩, rfl⟩
    exact ⟨p, ⟨mem_univ _, hp⟩, rfl⟩
  have h₁ : supTensor (Q.restrictTensorToCell v (w A)) ≤
      supTensor (restrictTensor (Q.toCubeTorusSet univ) (w A)) := by
    refine supTensor_mono fun ν b => ?_
    by_cases hb : w A ν b = 0
    · simp [LevelCube.restrictTensorToCell, restrictTensor, restrictBonds, indicator, hb]
    · have hin : AnchoredIn (Q.toCubeTorusSet univ) b := by
        refine hmono ?_
        by_contra hn
        exact hb (hloc.tensor_supported A ν b hn)
      have h₀ : restrictTensor (Q.toCubeTorusSet univ) (w A) ν b = w A ν b :=
        restrictBonds_of_mem hin _
      rw [h₀]
      exact norm_restrictBonds_le _ _ _
  have h₂ : supBond (Q.restrictBondsToCell v (u A : Q.system.setting.FineBond → ℝ)) ≤
      supBond (restrictBonds (Q.toCubeTorusSet univ) (u A : Q.system.setting.FineBond → ℝ)) := by
    refine supBond_mono fun b => ?_
    by_cases hb : (u A : Q.system.setting.FineBond → ℝ) b = 0
    · simp [LevelCube.restrictBondsToCell, restrictBonds, indicator, hb]
    · have hin : AnchoredIn (Q.toCubeTorusSet univ) b := by
        refine hmono ?_
        by_contra hn
        exact hb (hloc.form_supported A b hn)
      rw [restrictBonds_of_mem hin]
      exact norm_restrictBonds_le _ _ _
  have h₃ : supBond (restrictBonds (Q.supNbhd univ) (A : 𝒮.FineBond → ℝ)) ≤
      supBond (A : 𝒮.FineBond → ℝ) := supBond_mono fun b => norm_restrictBonds_le _ _ _
  have hMinv : (0 : ℝ) ≤ (M : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg M)
  have h₄ : C₀ * (M : ℝ)⁻¹ * supBond (restrictBonds (Q.supNbhd univ) (A : 𝒮.FineBond → ℝ)) ≤
      max C₀ 0 * (M : ℝ)⁻¹ * supBond (A : 𝒮.FineBond → ℝ) := by
    have h₅ : C₀ * (M : ℝ)⁻¹ ≤ max C₀ 0 * (M : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hMinv
    have h₆ : 0 ≤ max C₀ 0 * (M : ℝ)⁻¹ := mul_nonneg (le_max_right _ _) hMinv
    calc C₀ * (M : ℝ)⁻¹ * supBond (restrictBonds (Q.supNbhd univ) (A : 𝒮.FineBond → ℝ))
        ≤ max C₀ 0 * (M : ℝ)⁻¹ *
            supBond (restrictBonds (Q.supNbhd univ) (A : 𝒮.FineBond → ℝ)) :=
          mul_le_mul_of_nonneg_right h₅ (supBond_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left h₃ h₆
  have h₅ := mul_le_mul_of_nonneg_left h₁ hξ.le
  have h₆ := mul_le_mul_of_nonneg_left h₂ (pow_pos hξ 2).le
  linarith
end OneCube
section NearCells
variable {𝒮 : NestedRegions} {M : ℕ}
end NearCells
end YangMills.Construction.CubeAdjointDefect.LocalPartsAtCells
