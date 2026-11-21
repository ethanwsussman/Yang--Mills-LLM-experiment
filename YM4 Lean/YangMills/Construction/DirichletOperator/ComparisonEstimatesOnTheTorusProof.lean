import YangMills.Construction.DirichletOperator.BoundsOnTheDefectsOfTheCutOff
import YangMills.Construction.DirichletOperator.ChangedLongitudinalSourceAtTheCellsOfACubeProof
import YangMills.Construction.RegionSequence.PartitionConsequences
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace YangMills.Construction
open Set
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes CubeTorusComparison
open DirichletGreen (fieldModulusAt)
open CubeTorus (torusSetting levelSpacing)
noncomputable section
namespace TorusComparisonProof
section Lengths
variable {S : ℝ}
theorem supNorm_torusProj_le (v : Fin 4 → ℝ) : supNorm (torusProj 4 S v) ≤ ‖v‖ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_proj_le <;> assumption
theorem supNorm_add_le (hc : Function.Surjective (torusProj 4 S)) (p q : PeriodicTorus 4 S) :
    supNorm (p + q) ≤ supNorm p + supNorm q := by
  have hne : ∀ r : PeriodicTorus 4 S, {t | ∃ v : Fin 4 → ℝ, torusProj 4 S v = r ∧ t = ‖v‖}.Nonempty := by
    intro r
    obtain ⟨v, hv⟩ := hc r
    exact ⟨_, v, hv, rfl⟩
  have h₁ : supNorm (p + q) - supNorm q ≤ supNorm p := by
    refine le_csInf (hne p) ?_
    rintro r ⟨v, hv, rfl⟩
    have h₂ : supNorm (p + q) - ‖v‖ ≤ supNorm q := by
      refine le_csInf (hne q) ?_
      rintro r' ⟨w, hw, rfl⟩
      have h₃ : torusProj 4 S (v + w) = p + q := by
        rw [← hv, ← hw]
        funext μ
        simp [torusProj]
      have h₄ := supNorm_torusProj_le (S := S) (v + w)
      rw [h₃] at h₄
      linarith [norm_add_le v w]
    linarith
  linarith
theorem supNorm_unitStep_le {ξ : ℝ} (hξ : 0 < ξ) (μ : Fin 4) :
    supNorm ((unitStep 4 S ξ μ : LatticeSite 4 S ξ) : PeriodicTorus 4 S) ≤ ξ := by
  have h := supNorm_torusProj_le (S := S) (Pi.single μ ξ)
  have hn : ‖(Pi.single μ ξ : Fin 4 → ℝ)‖ ≤ ξ := by
    refine (pi_norm_le_iff_of_nonneg hξ.le).2 fun ν => ?_
    by_cases hν : ν = μ
    · subst hν
      simp [abs_of_pos hξ]
    · simp [Pi.single_eq_of_ne hν, hξ.le]
  exact h.trans hn
end Lengths
theorem finite_fineSite (hl : TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineSite := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineSite <;> assumption
section Linear
variable {𝒯 : NestedRegions}
theorem latticeLaplacian_add (f g : 𝒯.FineSite → ℝ) :
    latticeLaplacian (f + g) = latticeLaplacian f + latticeLaplacian g := by apply _root_.YangMills.Construction.RegionSequence.Positivity.latticeLaplacian_add <;> assumption
theorem latticeLaplacian_smul (c : ℝ) (f : 𝒯.FineSite → ℝ) :
    latticeLaplacian (c • f) = c • latticeLaplacian f := by apply _root_.YangMills.Construction.RegionSequence.Positivity.latticeLaplacian_smul <;> assumption
theorem projSites_add (f g : 𝒯.FineSite → ℝ) :
    projSites (f + g) = projSites f + projSites g := by apply _root_.YangMills.Construction.RegionSequence.Positivity.projSites_add <;> assumption
theorem projSites_smul (c : ℝ) (f : 𝒯.FineSite → ℝ) :
    projSites (c • f) = c • projSites f := by apply _root_.YangMills.Construction.RegionSequence.Positivity.projSites_smul <;> assumption
def dirichletLapLinear : (𝒯.FineSite → ℝ) →ₗ[ℝ] 𝒯.FineSite → ℝ where
  toFun := dirichletLap
  map_add' f g := by
    simp only [dirichletLap, projSites_add, latticeLaplacian_add]
  map_smul' c f := by
    simp only [dirichletLap, projSites_smul, latticeLaplacian_smul, RingHom.id_apply]
variable [Finite 𝒯.FineSite]
end Linear
section Defect
variable {𝒮 : NestedRegions} {M : ℕ} (Q : LevelCube 𝒮 M)
variable [Finite 𝒮.FineSite] [Finite (torusSetting Q).FineSite] [Finite ↥𝒮.allCentres]
end Defect
structure SequenceInputs (𝒮 : NestedRegions) (B δ c : ℝ) : Prop where
  B_nonneg : 0 ≤ B
  c_nonneg : 0 ≤ c
  green_le : ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres, ∀ f ∈ 𝒮.siteFns, VanishesOff (𝒮.cellOf y') f →
    ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ 𝒮.cellOf y →
      |gaugeGreenOp f x| ≤
          B * 𝒮.levelScale y ^ 2 * Real.exp (-δ * 𝒮.weightedDist y y') * supNormAll f ∧
      fieldModulusAt (Dirichlet.grad (gaugeGreenOp f)) x ≤
          B * 𝒮.levelScale y * Real.exp (-δ * 𝒮.weightedDist y y') * supNormAll f
  inverse_le : ∀ y y' : ↥𝒮.allCentres,
    |avgGreenSqInv (indicator {y'} fun _ => (1 : ℝ)) y| ≤
      B * (𝒮.levelScale y ^ 4)⁻¹ * Real.exp (-δ * 𝒮.weightedDist y y')
  sum_le : ∀ y : ↥𝒮.allCentres, ∑ᶠ y' : ↥𝒮.allCentres, Real.exp (-(δ / 2) * 𝒮.weightedDist y y') ≤ c
  scale_rpow_le : ∀ q : ℝ, |q| ≤ 8 → ∀ y y' : ↥𝒮.allCentres, 𝒮.levelScale y' ^ q ≤
    (𝒮.L : ℝ) ^ |q| * 𝒮.levelScale y ^ q * Real.exp (δ / 2 * 𝒮.weightedDist y y')
section Cells
variable {𝒮 : NestedRegions}
theorem cast_L_pos (𝒮 : NestedRegions) : (0 : ℝ) < (𝒮.L : ℝ) := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.blockFactor_pos <;> assumption
theorem levelScale_pos (y : 𝒮.Point) : 0 < 𝒮.levelScale y := by apply _root_.YangMills.Construction.RegionSequence.OperatorEstimates.levelScale_pos <;> assumption
theorem cellOf_subset (hc : RegionSequence.CellStructure.CellStructureClaim) {y : 𝒮.Point}
    (hy : y ∈ 𝒮.allCentres) : 𝒮.cellOf y ⊆ 𝒮.Ω 0 := by
  rw [← (hc 𝒮).2.1.union_eq]
  exact subset_biUnion_of_mem (u := fun y => 𝒮.cellOf y) hy
theorem centreOfSite_spec (hc : RegionSequence.CellStructure.CellStructureClaim) {x : 𝒮.FineSite}
    (hx : (x : 𝒮.Point) ∈ 𝒮.Ω 0) :
    𝒮.centreOfSite x ∈ 𝒮.allCentres ∧ (x : 𝒮.Point) ∈ 𝒮.cellOf (𝒮.centreOfSite x) := by
  obtain ⟨y, hy, hxy, -⟩ := (hc 𝒮).2.1.fine_site x hx
  exact Classical.epsilon_spec (p := fun y => y ∈ 𝒮.allCentres ∧ (x : 𝒮.Point) ∈ 𝒮.cellOf y)
    ⟨y, hy, interior_subset hxy⟩
theorem centreOfSite_eq (hc : RegionSequence.CellStructure.CellStructureClaim) {x : 𝒮.FineSite}
    {y : 𝒮.Point} (hy : y ∈ 𝒮.allCentres) (hxy : (x : 𝒮.Point) ∈ 𝒮.cellOf y) :
    𝒮.centreOfSite x = y := by
  have hx := cellOf_subset hc hy hxy
  obtain ⟨y₀, -, -, hu⟩ := (hc 𝒮).2.1.fine_site x hx
  obtain ⟨h₁, h₂⟩ := centreOfSite_spec hc hx
  rw [hu _ h₁ h₂, hu y hy hxy]
variable [Fintype ↥𝒮.allCentres]
variable [Finite 𝒮.FineSite]
end Cells
section Steps
variable {𝒮 : NestedRegions} {B δ c : ℝ}
variable [Fintype ↥𝒮.allCentres]
theorem weighted_sum_le (hi : SequenceInputs 𝒮 B δ c) {D q : ℝ} (hD : 0 ≤ D) (hq : |q| ≤ 8)
    (y : ↥𝒮.allCentres) (b : ↥𝒮.allCentres → ℝ) (hb : ∀ y', b y' ≤ D * 𝒮.levelScale y' ^ q) :
    ∑ y' : ↥𝒮.allCentres, Real.exp (-δ * 𝒮.weightedDist y y') * b y' ≤
      D * (𝒮.L : ℝ) ^ |q| * c * 𝒮.levelScale y ^ q := by
  have hL := cast_L_pos 𝒮
  have hξ := levelScale_pos (𝒮 := 𝒮) y
  have hA : 0 ≤ D * (𝒮.L : ℝ) ^ |q| * 𝒮.levelScale y ^ q := by positivity
  have h₁ : ∀ y' : ↥𝒮.allCentres, Real.exp (-δ * 𝒮.weightedDist y y') * b y' ≤
      D * (𝒮.L : ℝ) ^ |q| * 𝒮.levelScale y ^ q *
        Real.exp (-(δ / 2) * 𝒮.weightedDist y y') := by
    intro y'
    have h₂ := hi.scale_rpow_le q hq y y'
    have h₃ : b y' ≤ D * ((𝒮.L : ℝ) ^ |q| * 𝒮.levelScale y ^ q *
        Real.exp (δ / 2 * 𝒮.weightedDist y y')) :=
      (hb y').trans (mul_le_mul_of_nonneg_left h₂ hD)
    have h₄ := mul_le_mul_of_nonneg_left h₃ (Real.exp_pos (-δ * 𝒮.weightedDist y y')).le
    have e : Real.exp (-(δ / 2) * 𝒮.weightedDist y y') =
        Real.exp (-δ * 𝒮.weightedDist y y') *
          Real.exp (δ / 2 * 𝒮.weightedDist y y') := by
      rw [← Real.exp_add]
      ring_nf
    rw [e]
    calc _ ≤ _ := h₄
      _ = _ := by ring
  have h₅ := hi.sum_le y
  rw [finsum_eq_sum_of_fintype] at h₅
  calc ∑ y' : ↥𝒮.allCentres, Real.exp (-δ * 𝒮.weightedDist y y') * b y'
      ≤ ∑ y' : ↥𝒮.allCentres, D * (𝒮.L : ℝ) ^ |q| * 𝒮.levelScale y ^ q *
        Real.exp (-(δ / 2) * 𝒮.weightedDist y y') := Finset.sum_le_sum fun y' _ => h₁ y'
    _ = D * (𝒮.L : ℝ) ^ |q| * 𝒮.levelScale y ^ q *
        ∑ y' : ↥𝒮.allCentres, Real.exp (-(δ / 2) * 𝒮.weightedDist y y') := by
      rw [Finset.mul_sum]
    _ ≤ D * (𝒮.L : ℝ) ^ |q| * 𝒮.levelScale y ^ q * c := mul_le_mul_of_nonneg_left h₅ hA
    _ = _ := by ring
variable [Finite 𝒮.FineSite]
end Steps
section Transfer
variable {𝒮 : NestedRegions} {s' : ℕ} (e : 𝒮.EndsAt s') (so : TruncationAgrees e)
end Transfer
section Cube
variable {𝒮 : NestedRegions} {M : ℕ} {Q : LevelCube 𝒮 M}
theorem nestedScale_pos (𝒮 : NestedRegions) (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem one_le_cast_L (𝒮 : NestedRegions) : (1 : ℝ) ≤ (𝒮.L : ℝ) := by apply _root_.YangMills.Construction.RegionSequence.PartitionConsequences.one_le_L <;> assumption
theorem levelScale_eq (y : 𝒮.Point) : 𝒮.levelScale y = (𝒮.L : ℝ) ^ 𝒮.level y * 𝒮.ξ :=
  𝒮.scale_eq_pow_mul (𝒮.level y)
theorem levelSpacing_eq (Q : LevelCube 𝒮 M) : levelSpacing Q = (𝒮.L : ℝ) ^ Q.level * 𝒮.ξ :=
  𝒮.scale_eq_pow_mul Q.level
theorem levelSpacing_pos (Q : LevelCube 𝒮 M) : 0 < levelSpacing Q := nestedScale_pos 𝒮 Q.level
theorem ξ_le_levelScale (y : 𝒮.Point) : 𝒮.ξ ≤ 𝒮.levelScale y := by apply _root_.YangMills.Construction.DivSourceEstimate.ξ_le_levelScale <;> assumption
theorem thicken_mono {a b : ℝ} (h : a ≤ b) : Q.thicken a ⊆ Q.thicken b := by apply _root_.YangMills.Construction.CubeAdjointDefect.LongChangeAtCells.thicken_mono' <;> assumption
end Cube
section Defect
variable {𝒮 : NestedRegions} {M : ℕ} {Q : LevelCube 𝒮 M} {B δ c : ℝ}
variable [Fintype ↥𝒮.allCentres] [Finite 𝒮.FineSite]
end Defect
section Adjoint
variable {𝒮 : NestedRegions} {M : ℕ} {Q : LevelCube 𝒮 M}
variable [Fintype ↥𝒮.allCentres] [Finite 𝒮.FineSite] [Finite (torusSetting Q).FineSite]
end Adjoint
section Requirements
variable {𝒮 : NestedRegions} {B δ c : ℝ}
variable [Fintype ↥𝒮.allCentres] [Finite 𝒮.FineSite]
end Requirements
end TorusComparisonProof
end
end YangMills.Construction
