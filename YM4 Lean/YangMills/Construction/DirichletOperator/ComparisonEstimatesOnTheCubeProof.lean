import YangMills.Construction.DirichletOperator.AdjointDefectOfACubeAsItsSourcesProof
import YangMills.Construction.DirichletOperator.BoundsOnTheDefectsOfTheCutOff
import YangMills.Construction.DirichletOperator.InequalitiesOnCubesOfTheFirstKindProof
import YangMills.Construction.DirichletOperator.LowerBoundOfTheBasicOperatorProof
import YangMills.Construction.RegionSequence.AverageWeightBounds
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes CubeTorusComparison
open DirichletGreen (fieldModulusAt)
open YangMills.Construction.CubeTorus (torusSetting levelSpacing chosenConstants)
namespace CubeTorusComparison.Estimates
section Lengths
variable {S : ℝ}
theorem exists_torusProj_eq_abs_eq (p : PeriodicTorus 4 S) :
    ∃ b : Fin 4 → ℝ, torusProj 4 S b = p ∧ ∀ μ, |b μ| = ‖p μ‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.exists_lift_abs_eq_norm <;> assumption
theorem norm_apply_le_supNorm (p : PeriodicTorus 4 S) (μ : Fin 4) : ‖p μ‖ ≤ supNorm p := by apply _root_.YangMills.Construction.RegionSequence.AverageWeightBounds.norm_apply_le_supNorm <;> assumption
theorem supNorm_le_of_forall_norm_le {p : PeriodicTorus 4 S} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ μ, ‖p μ‖ ≤ a) : supNorm p ≤ a := by
  obtain ⟨b, hb, hb'⟩ := exists_torusProj_eq_abs_eq p
  have hbdd : BddBelow {r | ∃ v : Fin 4 → ℝ, torusProj 4 S v = p ∧ r = ‖v‖} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨v, -, rfl⟩
    exact norm_nonneg _
  refine (csInf_le hbdd ⟨b, hb, rfl⟩).trans ?_
  exact (pi_norm_le_iff_of_nonneg ha).2 fun μ => by
    rw [Real.norm_eq_abs, hb' μ]
    exact h μ
theorem supNorm_nonneg (p : PeriodicTorus 4 S) : 0 ≤ supNorm p :=
  (norm_nonneg _).trans (norm_apply_le_supNorm p 0)
theorem supNorm_zero : supNorm (0 : PeriodicTorus 4 S) = 0 :=
  le_antisymm (supNorm_le_of_forall_norm_le le_rfl fun μ => by simp) (supNorm_nonneg _)
theorem supNorm_sub_comm (p q : PeriodicTorus 4 S) : supNorm (p - q) = supNorm (q - p) := by apply _root_.YangMills.Construction.PartitionCubes.TorusComponents.supNorm_sub_comm <;> assumption
theorem supNorm_sub_le_add (p q s : PeriodicTorus 4 S) :
    supNorm (p - s) ≤ supNorm (p - q) + supNorm (q - s) := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.supNorm_sub_le <;> assumption
theorem lOneNorm_eq_sum_norm (p : PeriodicTorus 4 S) : lOneNorm p = ∑ μ, ‖p μ‖ := by apply _root_.YangMills.Construction.PartitionCubes.TorusTransfer.lOneNorm_eq_sum_norm <;> assumption
theorem supNorm_le_lOneNorm (p : PeriodicTorus 4 S) : supNorm p ≤ lOneNorm p := by
  rw [lOneNorm_eq_sum_norm]
  exact supNorm_le_of_forall_norm_le (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun μ =>
    Finset.single_le_sum (f := fun μ => ‖p μ‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ μ)
end Lengths
section Whole
variable {𝒯 : NestedRegions}
theorem finite_fineSite (𝒯 : NestedRegions) : Finite 𝒯.FineSite := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineSite <;> assumption
structure WholeTorus (𝒯 : NestedRegions) : Prop where
  region_zero : 𝒯.Ω 0 = univ
  bonds_univ : 𝒯.bonds = univ
  cellFacts : CellStructure.CellFacts 𝒯
  adjointFacts : CellStructure.AdjointFacts 𝒯
  positivityFacts : CellStructure.PositivityFacts 𝒯
  transferRange : GaugeProjections.TransferRange 𝒯
variable [Fintype 𝒯.FineSite] [Fintype 𝒯.allCentres]
theorem innerSum_eq_sum (f g : 𝒯.FineSite → ℝ) : innerSum f g = 𝒯.ξ ^ 4 * ∑ x, f x * g x := by
  rw [innerSum, finsum_eq_sum_of_fintype]
theorem innerSum_comm (f g : 𝒯.FineSite → ℝ) : innerSum f g = innerSum g f := by
  simp only [innerSum_eq_sum, mul_comm (f _)]
variable (h : WholeTorus 𝒯)
include h
omit h in
theorem blockAvg_add (f g : 𝒯.FineSite → ℝ) :
    blockAvg (f + g) = blockAvg f + blockAvg g := by
  funext y
  simp only [blockAvg, Pi.add_apply]
  rw [finsum_mem_add_distrib (Set.toFinite _), mul_add]
omit h in
theorem blockAvg_smul (c : ℝ) (f : 𝒯.FineSite → ℝ) :
    blockAvg (c • f) = c • blockAvg f := by
  funext y
  simp only [blockAvg, Pi.smul_apply, smul_eq_mul]
  rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
    finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), ← Finset.mul_sum]
  ring
end Whole
section Chain
variable {𝒯 : NestedRegions}
structure KernelBounds (𝒯 : NestedRegions) (r B : ℝ) (dec : 𝒯.allCentres → 𝒯.allCentres → ℝ) :
    Prop where
  green_le : ∀ (w w' : 𝒯.allCentres) (f : 𝒯.FineSite → ℝ), VanishesOff (𝒯.cellOf w') f →
    ∀ x : 𝒯.FineSite, (x : 𝒯.Point) ∈ 𝒯.cellOf w →
      |gaugeGreenOp f x| ≤ B * r ^ 2 * dec w w' * supSite f
  grad_green_le : ∀ (w w' : 𝒯.allCentres) (f : 𝒯.FineSite → ℝ), VanishesOff (𝒯.cellOf w') f →
    ∀ x : 𝒯.FineSite, (x : 𝒯.Point) ∈ 𝒯.cellOf w →
      fieldModulusAt (grad (gaugeGreenOp f)) x ≤ B * r * dec w w' * supSite f
  green_div_le : ∀ (w w' : 𝒯.allCentres) (F : BondField 4 𝒯.side 𝒯.ξ),
    (∀ ν, VanishesOff (𝒯.cellOf w') (F ν)) → ∀ x : 𝒯.FineSite, (x : 𝒯.Point) ∈ 𝒯.cellOf w →
      |gaugeGreenOp (latticeDiv F) x| ≤ B * r * dec w w' * fieldSupNorm F
  inv_le : ∀ w w' : 𝒯.allCentres,
    |avgGreenSqInv (indicator {w'} fun _ => (1 : ℝ)) w| ≤ B * (r ^ 4)⁻¹ * dec w w'
variable [Fintype 𝒯.FineSite] [Fintype 𝒯.allCentres]
theorem abs_le_fieldModulusAt (F : BondField 4 𝒯.side 𝒯.ξ) (x : 𝒯.FineSite) (μ : Fin 4) :
    |F μ x| ≤ fieldModulusAt F x :=
  le_ciSup (f := fun μ => |F μ x|) (Set.finite_range _).bddAbove μ
variable (h : WholeTorus 𝒯) {r B : ℝ} {dec : 𝒯.allCentres → 𝒯.allCentres → ℝ}
  (hb : KernelBounds 𝒯 r B dec) (hr : 0 < r) (hB : 0 ≤ B) (hdec : ∀ w w', 0 ≤ dec w w')
include h hb hr hB hdec
end Chain
section Weight
variable {𝒯 : NestedRegions} [Fintype 𝒯.FineSite] [Fintype 𝒯.allCentres]
structure SourceBounds (r B m j : ℝ) (E : 𝒯.allCentres → ℝ) (src : 𝒯.FineSite → ℝ) : Prop where
  coeff_le : ∀ w : 𝒯.allCentres, |transferGramInv (transferAdj src) w| ≤
    m ^ 2 * B ^ 2 * (r ^ 3)⁻¹ * j * E w
  transfer_le : ∀ (w : 𝒯.allCentres) (x : 𝒯.FineSite), (x : 𝒯.Point) ∈ 𝒯.cellOf w →
    |transferOp (transferGramInv (transferAdj src)) x| ≤ m ^ 3 * B ^ 3 * r⁻¹ * j * E w
  grad_transfer_le : ∀ (w : 𝒯.allCentres) (x : 𝒯.FineSite), (x : 𝒯.Point) ∈ 𝒯.cellOf w →
    fieldModulusAt (grad (transferOp (transferGramInv (transferAdj src)))) x ≤
      m ^ 3 * B ^ 3 * (r ^ 2)⁻¹ * j * E w
  green_proj_le : ∀ (w : 𝒯.allCentres) (x : 𝒯.FineSite), (x : 𝒯.Point) ∈ 𝒯.cellOf w →
    |gaugeGreenOp (rangeProj src) x| ≤ 2 * m ^ 4 * B ^ 4 * r * j * E w
end Weight
section Source
variable {𝒯 : NestedRegions} [Fintype 𝒯.FineSite] [Fintype 𝒯.allCentres]
def fineBondEquiv (𝒯 : NestedRegions) : 𝒯.FineBond ≃ Fin 4 × 𝒯.FineSite where
  toFun b := (b.dir, b.source)
  invFun p := ⟨p.2, p.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
end Source
section LevelSequence
variable {𝒯 : NestedRegions}
theorem scale_succ (𝒯 : NestedRegions) (n : ℕ) :
    𝒯.scale (n + 1) = (𝒯.L : ℝ) * 𝒯.scale n := by apply _root_.YangMills.Construction.PartitionCoefficients.nestedScale_succ <;> assumption
end LevelSequence
section OnTheCube
variable {𝒮 : NestedRegions} {M : ℕ} (Q : LevelCube 𝒮 M)
structure TorusShape : Prop where
  L_eq : (torusSetting Q).L = 𝒮.L
  ξ_eq : (torusSetting Q).ξ = 𝒮.ξ
  side_eq : (torusSetting Q).side = 8 * cubeSide 𝒮 M Q.level
  s_eq : (torusSetting Q).s = Q.level + 1
  region_eq_univ : ∀ j ≤ Q.level, (torusSetting Q).Ω j = univ
  bonds_eq_univ : (torusSetting Q).bonds = univ
variable {Q}
theorem scale_pos (𝒮 : NestedRegions) (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem ξ_le_scale (𝒮 : NestedRegions) (n : ℕ) : 𝒮.ξ ≤ 𝒮.scale n := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.ξ_le_scale <;> assumption
end OnTheCube
section EvaluationMaps
variable {𝒮 : NestedRegions} {M : ℕ} {Q : LevelCube 𝒮 M}
theorem mapSite_coe (hF : Q.FirstTypeProperties) (hsh : TorusShape Q) (x : 𝒮.FineSite)
    (hx : (x : 𝒮.Point) ∈ Q.strictPts) :
    ((Q.system.mapSite x : (torusSetting Q).FineSite) : (torusSetting Q).Point) =
      Q.system.embed x := by
  have hsites := hF.embed_sites 0 (Or.inl (Nat.zero_le _))
  have e0 : 𝒮.scale 0 = 𝒮.ξ := by
    simp [NestedRegions.scale, scaleSpacing]
  rw [e0] at hsites
  have hm : Q.system.embed x ∈ spacingLattice 4 (torusSetting Q).side 𝒮.ξ := by
    have h₁ : Q.system.embed x ∈ Q.system.embed ''
        ((spacingLattice 4 𝒮.side 𝒮.ξ : Set 𝒮.Point) ∩ Q.strictPts) := ⟨x, ⟨x.2, hx⟩, rfl⟩
    rw [hsites] at h₁
    exact h₁.1
  have gen : ∀ (p : (torusSetting Q).Point) (σ σ' : ℝ), σ = σ' →
      p ∈ spacingLattice 4 (torusSetting Q).side σ' →
        p ∈ spacingLattice 4 (torusSetting Q).side σ := by
    rintro p σ _ rfl hp
    exact hp
  exact Classical.epsilon_spec (p := fun y : (torusSetting Q).FineSite =>
    (y : (torusSetting Q).Point) = Q.system.embed x) ⟨⟨_, gen _ _ _ hsh.ξ_eq hm⟩, rfl⟩
theorem mem_strictPts_of_mem_thicken (hS : Q.SupportBounds) (hb : 0 ≤ cubeSide 𝒮 M Q.level)
    {x : 𝒮.Point} (hx : x ∈ Q.thicken (5 / 6)) : x ∈ Q.strictPts := by
  have h' : supNorm (x - Q.centre) < 5 / 6 * cubeSide 𝒮 M Q.level :=
    hS.thickened_subset (5 / 6) (by norm_num) (by norm_num) hx
  change supNorm (x - Q.centre) < cubeSide 𝒮 M Q.level
  linarith
theorem supNorm_torusProj_le {S : ℝ} {v : Fin 4 → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hv : ∀ ν, |v ν| ≤ a) : supNorm (torusProj 4 S v) ≤ a :=
  supNorm_le_of_forall_norm_le ha fun ν =>
    (TorusMetric.addCircle_norm_coe_le_abs (v ν)).trans (hv ν)
theorem supNorm_unitStep_le (𝒮 : NestedRegions) (μ : Fin 4) :
    supNorm ((unitStep 4 𝒮.side 𝒮.ξ μ : 𝒮.FineSite) : 𝒮.Point) ≤ 𝒮.ξ := by
  have e : ((unitStep 4 𝒮.side 𝒮.ξ μ : 𝒮.FineSite) : 𝒮.Point) =
      torusProj 4 𝒮.side (Pi.single μ 𝒮.ξ) := rfl
  rw [e]
  refine supNorm_torusProj_le 𝒮.ξ_pos.le fun ν => ?_
  by_cases h : ν = μ
  · subst h
    simp [abs_of_pos 𝒮.ξ_pos]
  · simp [Pi.single_eq_of_ne h, 𝒮.ξ_pos.le]
end EvaluationMaps
section OnOneCube
end OnOneCube
end CubeTorusComparison.Estimates
end YangMills.Construction
