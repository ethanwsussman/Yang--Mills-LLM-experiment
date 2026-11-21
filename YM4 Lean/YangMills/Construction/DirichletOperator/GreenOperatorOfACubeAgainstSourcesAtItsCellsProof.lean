import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.CubeNearASiteProof
import YangMills.Construction.DirichletOperator.CubeTermBoundsOfTheDifferenceOfADivergenceProof
import YangMills.Construction.DirichletOperator.DivergenceSourceOnTheTorusOfACubeProof
import YangMills.Construction.DirichletOperator.FactsOfTheCellsOfACube
import YangMills.Construction.DirichletOperator.GreenOperatorOfACubeAgainstSourcesAtItsCells
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes RemainderEstimates
open CubeAdjointDefect (cellWeightedSum)
open CubeOperators (cutoffSize cubeDivOne IsCubeScale)
open CubeTorus (TensorAnchorSupported)
namespace CubeGreenSources
theorem finite_fineSite (hl : TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineSite := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineSite <;> assumption
theorem finite_fineBond (hl : TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
section InnerProducts
variable {𝒯 : NestedRegions}
theorem bondInner_comm (A B : 𝒯.FineBond → ℝ) : bondInner A B = bondInner B A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
theorem bondInner_add_left [Finite 𝒯.FineBond] (A B g : 𝒯.FineBond → ℝ) :
    bondInner (A + B) g = bondInner A g + bondInner B g := by apply _root_.YangMills.Construction.RegionSequence.Positivity.bondInner_add_left <;> assumption
theorem eq_of_bondInner_eq [Finite 𝒯.FineBond] (F : Submodule ℝ (𝒯.FineBond → ℝ))
    {X Y : 𝒯.FineBond → ℝ} (hX : X ∈ F) (hY : Y ∈ F)
    (h : ∀ v ∈ F, bondInner X v = bondInner Y v) : X = Y := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.eq_of_bondInner_eq <;> assumption
theorem fwdDiff_add (ν : Fin 4) (A B : 𝒯.FineBond → ℝ) :
    fwdDiff ν (A + B) = fwdDiff ν A + fwdDiff ν B := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.fwdDiff_add <;> assumption
theorem fwdDiff_smul (ν : Fin 4) (c : ℝ) (A : 𝒯.FineBond → ℝ) :
    fwdDiff ν (c • A) = c • fwdDiff ν A := by apply _root_.YangMills.Construction.CubeTermBounds.fwdDiff_smul_fun <;> assumption
end InnerProducts
section HolderSeminorms
variable {𝒯 : NestedRegions}
theorem supBond_nonneg (f : 𝒯.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
theorem supTensor_nonneg {r : ℕ} (J : 𝒯.Tensor r) : 0 ≤ supTensor J :=
  Real.iSup_nonneg fun _ => supBond_nonneg _
theorem supSite_nonneg (f : 𝒯.FineSite → ℝ) : 0 ≤ supSite f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem abs_le_supSite [Finite 𝒯.FineSite] (f : 𝒯.FineSite → ℝ) (x : 𝒯.FineSite) :
    |f x| ≤ supSite f :=
  le_ciSup (f := fun x => ‖f x‖) (Set.finite_range _).bddAbove x
theorem holderSite_nonneg (α lam : ℝ) (f : 𝒯.FineSite → ℝ) : 0 ≤ holderSite α lam f := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.holderSite_nonneg <;> assumption
theorem le_holderSite [Finite 𝒯.FineSite] (α lam : ℝ) (f : 𝒯.FineSite → ℝ) {x x' : 𝒯.FineSite}
    (h₀ : 0 < siteLOneDist x x') (h₁ : siteLOneDist x x' ≤ lam) :
    (lam / siteLOneDist x x') ^ α * ‖f x' - f x‖ ≤ holderSite α lam f := by
  refine le_csSup ?_ ⟨x, x', h₀, h₁, rfl⟩
  refine (Set.finite_range fun p : 𝒯.FineSite × 𝒯.FineSite =>
    (lam / siteLOneDist p.1 p.2) ^ α * ‖f p.2 - f p.1‖).bddAbove.mono ?_
  rintro _ ⟨c, c', -, -, rfl⟩
  exact ⟨(c, c'), rfl⟩
theorem holderSite_mul_le [Finite 𝒯.FineSite] {α lam κ : ℝ} (hα₁ : α < 1)
    (hlam : 0 ≤ lam) (hκ : 0 ≤ κ) (ζ φ : 𝒯.FineSite → ℝ) (h₀ : ∀ x, 0 ≤ φ x) (h₁ : ∀ x, φ x ≤ 1)
    (hφ : ∀ x x', |φ x' - φ x| ≤ κ * siteLOneDist x x') :
    holderSite α lam (fun x => ζ x * φ x) ≤
      holderSite α lam ζ + κ * lam * supSite ζ := by
  refine Real.sSup_le ?_ (add_nonneg (holderSite_nonneg _ _ _)
    (mul_nonneg (mul_nonneg hκ hlam) (supSite_nonneg _)))
  rintro _ ⟨x, x', hd, hd₁, rfl⟩
  set d := siteLOneDist x x' with hdd
  have hratio : 1 ≤ lam / d := (one_le_div hd).2 hd₁
  have hp : (lam / d) ^ α ≤ lam / d := by
    calc (lam / d) ^ α ≤ (lam / d) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hratio hα₁.le
      _ = lam / d := Real.rpow_one _
  have hp₀ : 0 ≤ (lam / d) ^ α := Real.rpow_nonneg (by linarith) _
  have hz := le_holderSite α lam ζ hd hd₁
  have hs := abs_le_supSite ζ x
  have hL := hφ x x'
  have hn : ‖ζ x' * φ x' - ζ x * φ x‖ ≤ ‖ζ x' - ζ x‖ + |ζ x| * (κ * d) := by
    have e : ζ x' * φ x' - ζ x * φ x = (ζ x' - ζ x) * φ x' + ζ x * (φ x' - φ x) := by ring
    rw [e, Real.norm_eq_abs, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg (h₀ x')]
      exact mul_le_of_le_one_right (abs_nonneg _) (h₁ x')
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hL (abs_nonneg _)
  have hκd : 0 ≤ |ζ x| * (κ * d) := mul_nonneg (abs_nonneg _) (mul_nonneg hκ hd.le)
  calc (lam / d) ^ α * ‖ζ x' * φ x' - ζ x * φ x‖
      ≤ (lam / d) ^ α * (‖ζ x' - ζ x‖ + |ζ x| * (κ * d)) :=
        mul_le_mul_of_nonneg_left hn hp₀
    _ = (lam / d) ^ α * ‖ζ x' - ζ x‖ + (lam / d) ^ α * (|ζ x| * (κ * d)) := by ring
    _ ≤ holderSite α lam ζ + (lam / d) * (|ζ x| * (κ * d)) :=
        add_le_add hz (mul_le_mul_of_nonneg_right hp hκd)
    _ = holderSite α lam ζ + κ * lam * |ζ x| := by
        field_simp
    _ ≤ holderSite α lam ζ + κ * lam * supSite ζ := by
        have := mul_le_mul_of_nonneg_left hs (mul_nonneg hκ hlam)
        linarith
end HolderSeminorms
section CubeOperatorsOnForms
variable {𝒮 : NestedRegions} {M : ℕ}
theorem divOne_add {𝒯 : NestedRegions} (J J' : 𝒯.Tensor 1) :
    divOne (J + J') = divOne J + divOne J' := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.divOne_add <;> assumption
theorem inv_mem_forms (𝔏 : CubeSystem 𝒮)
    (hb : BijOn 𝔏.op (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) 𝔏.forms)
    {u : 𝔏.setting.FineBond → ℝ} (hu : u ∈ 𝔏.forms) : 𝔏.inv u ∈ 𝔏.forms := by apply _root_.YangMills.Construction.CubeTermBounds.inv_mem_forms <;> assumption
def cellContribution (c : CubeOperators.RegularityConstants) (Q : LevelCube 𝒮 M)
    (o : Q.system.setting.Point) (J : Q.system.setting.Tensor 1)
    (s : Q.system.setting.FineBond → ℝ) (w : Q.system.setting.Point) : ℝ :=
  Real.exp (-c.δ * Q.torusDist o w) *
    (𝒮.scale Q.level * supTensor (Q.restrictTensorToCell w J) +
      𝒮.scale Q.level ^ 2 * supBond (Q.restrictBondsToCell w s))
def cellSeries (c : CubeOperators.RegularityConstants) (Q : LevelCube 𝒮 M)
    (o : Q.system.setting.Point) (J : Q.system.setting.Tensor 1)
    (s : Q.system.setting.FineBond → ℝ) : ℝ :=
  ∑ᶠ w ∈ Q.cellPoints, cellContribution c Q o J s w
theorem scale_pos (𝒯 : NestedRegions) (n : ℕ) : 0 < 𝒯.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
structure SumReady (c : CubeOperators.RegularityConstants) (Q : LevelCube 𝒮 M) : Prop where
  bonds_finite : Finite Q.system.setting.FineBond
  holds : c.CubeHolds Q
  cells : Q.CellProperties
  cells_finite : Q.cellPoints.Finite
  div_mem : ∀ J, cubeDivOne Q J ∈ Q.system.forms
  div_add : ∀ J J', cubeDivOne Q (J + J') = cubeDivOne Q J + cubeDivOne Q J'
namespace SumReady
variable {c : CubeOperators.RegularityConstants} {Q : LevelCube 𝒮 M}
theorem inv_add (R : SumReady c Q) {a b : Q.system.setting.FineBond → ℝ}
    (ha : a ∈ Q.system.forms) (hb : b ∈ Q.system.forms) :
    Q.system.inv (a + b) = Q.system.inv a + Q.system.inv b := by
  have := R.bonds_finite
  have hG : ∀ {u : Q.system.setting.FineBond → ℝ}, u ∈ Q.system.forms →
      Q.system.inv u ∈ Q.system.forms := fun hu => inv_mem_forms _ R.holds.invertible hu
  have hab := Q.system.forms.add_mem ha hb
  refine eq_of_bondInner_eq Q.system.forms (hG hab) (Q.system.forms.add_mem (hG ha) (hG hb))
    fun v hv => ?_
  rw [R.holds.symmetric _ hab v hv, bondInner_add_left, bondInner_add_left,
    R.holds.symmetric _ ha v hv, R.holds.symmetric _ hb v hv]
theorem inv_zero (R : SumReady c Q) : Q.system.inv 0 = 0 := by
  have h := R.inv_add Q.system.forms.zero_mem Q.system.forms.zero_mem
  rw [add_zero] at h
  exact left_eq_add.mp h
theorem inv_sum (R : SumReady c Q) {ι : Type} (t : Finset ι)
    (f : ι → Q.system.setting.FineBond → ℝ) (hf : ∀ w ∈ t, f w ∈ Q.system.forms) :
    Q.system.inv (∑ w ∈ t, f w) = ∑ w ∈ t, Q.system.inv (f w) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using R.inv_zero
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      R.inv_add (hf a (Finset.mem_insert_self a t))
        (Q.system.forms.sum_mem fun w hw => hf w (Finset.mem_insert_of_mem hw)),
      ih fun w hw => hf w (Finset.mem_insert_of_mem hw)]
theorem cubeDivOne_zero (R : SumReady c Q) : cubeDivOne Q 0 = 0 := by
  have h := R.div_add 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h
theorem cubeDivOne_sum (R : SumReady c Q) {ι : Type} (t : Finset ι)
    (f : ι → Q.system.setting.Tensor 1) :
    cubeDivOne Q (∑ w ∈ t, f w) = ∑ w ∈ t, cubeDivOne Q (f w) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using R.cubeDivOne_zero
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, R.div_add, ih]
theorem inv_eq_sum_cells (R : SumReady c Q) (J : Q.system.setting.Tensor 1)
    {s : Q.system.setting.FineBond → ℝ} (hs : s ∈ Q.system.forms) :
    Q.system.inv (cubeDivOne Q J + s) =
      ∑ w ∈ R.cells_finite.toFinset, (Q.system.inv (cubeDivOne Q (Q.restrictTensorToCell w J)) +
        Q.system.inv (Q.restrictBondsToCell w s)) := by
  have hJ : J = ∑ w ∈ R.cells_finite.toFinset, Q.restrictTensorToCell w J := by
    funext ν b
    refine (congrFun (congrFun (R.cells.tensors_sum J) ν) b).trans ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ R.cells_finite, Finset.sum_apply, Finset.sum_apply]
  have hS : s = ∑ w ∈ R.cells_finite.toFinset, Q.restrictBondsToCell w s := by
    funext b
    refine (congrFun (R.cells.forms_sum s hs) b).trans ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ R.cells_finite, Finset.sum_apply]
  have e₁ : cubeDivOne Q J =
      ∑ w ∈ R.cells_finite.toFinset, cubeDivOne Q (Q.restrictTensorToCell w J) :=
    (congrArg (cubeDivOne Q) hJ).trans (R.cubeDivOne_sum _ _)
  have e₃ : cubeDivOne Q J + s = ∑ w ∈ R.cells_finite.toFinset,
      (cubeDivOne Q (Q.restrictTensorToCell w J) + Q.restrictBondsToCell w s) := by
    rw [Finset.sum_add_distrib, ← e₁, ← hS]
  have hcut : ∀ w ∈ R.cells_finite.toFinset, Q.restrictBondsToCell w s ∈ Q.system.forms :=
    fun w hw => R.cells.forms_restrict s hs w (R.cells_finite.mem_toFinset.1 hw)
  rw [e₃, R.inv_sum _ _ fun w hw => Q.system.forms.add_mem (R.div_mem _) (hcut w hw)]
  exact Finset.sum_congr rfl fun w hw => R.inv_add (R.div_mem _) (hcut w hw)
theorem isCubeScale_cellSide (R : SumReady c Q) {w : Q.system.setting.Point}
    (hw : w ∈ Q.cellPoints) : IsCubeScale Q (Q.cellSide w) :=
  R.cells.side w hw
theorem cellAt_subset (R : SumReady c Q) {w : Q.system.setting.Point} (hw : w ∈ Q.cellPoints) :
    Q.cellAt w ⊆ cubeHalfSide w (Q.cellSide w) := by
  have hpos : 0 ≤ Q.cellSide w := by
    rcases R.cells.side w hw with h | h <;> rw [h]
    · exact (scale_pos 𝒮 _).le
    · exact (scale_pos 𝒮 _).le
  intro p hp
  have hp' : p ∈ cubeAt w (Q.cellSide w) := by
    unfold LevelCube.cellAt at hp
    unfold LevelCube.cellSide
    split_ifs at hp ⊢ with h
    · exact hp
    · exact hp
  have hp'' : supNorm (p - w) ≤ Q.cellSide w / 2 := hp'
  show supNorm (p - w) ≤ 2 * Q.cellSide w / 2
  linarith
theorem restrictBonds_supported (R : SumReady c Q) {w : Q.system.setting.Point}
    (hw : w ∈ Q.cellPoints) (s : Q.system.setting.FineBond → ℝ) :
    AnchorSupported (cubeHalfSide w (Q.cellSide w)) (Q.restrictBondsToCell w s) := by
  intro b hb
  show indicator {b | AnchoredIn (Q.cellAt w) b} s b = 0
  have hnb : b ∉ {b | AnchoredIn (Q.cellAt w) b} := fun h => hb (R.cellAt_subset hw h)
  exact indicator_of_notMem hnb _
theorem restrictTensor_supported (R : SumReady c Q) {w : Q.system.setting.Point}
    (hw : w ∈ Q.cellPoints) (J : Q.system.setting.Tensor 1) :
    TensorAnchorSupported (cubeHalfSide w (Q.cellSide w)) (Q.restrictTensorToCell w J) :=
  fun ν => R.restrictBonds_supported hw (J ν)
theorem abs_inv_le (R : SumReady c Q) {o : Q.system.setting.Point} {lam₁ : ℝ}
    (h₁ : IsCubeScale Q lam₁) (J : Q.system.setting.Tensor 1)
    {s : Q.system.setting.FineBond → ℝ} (hs : s ∈ Q.system.forms)
    (x : Q.system.setting.FineBond) (hx : AnchoredIn (cubeHalfSide o lam₁) x) :
    |Q.system.inv (cubeDivOne Q J + s) x| ≤ c.B * cellSeries c Q o J s := by
  rw [R.inv_eq_sum_cells J hs, cellSeries, finsum_mem_eq_finite_toFinset_sum _ R.cells_finite,
    Finset.mul_sum, Finset.sum_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w hw => ?_)
  have hw' := R.cells_finite.mem_toFinset.1 hw
  have hb := R.holds.bounds lam₁ _ h₁ (R.isCubeScale_cellSide hw') o w
  have hJ := hb.source _ (R.restrictTensor_supported hw' J) x hx
  have hS := hb.value _ (R.cells.forms_restrict s hs w hw') (R.restrictBonds_supported hw' s) x hx
  simp only [Pi.add_apply]
  refine (abs_add_le _ _).trans ((add_le_add hJ hS).trans (le_of_eq ?_))
  simp only [cellContribution, CubeOperators.RegularityConstants.expDecay, CubeTorus.levelSpacing]
  ring
end SumReady
end CubeOperatorsOnForms
section TransferToTorus
variable {𝒮 : NestedRegions} {M : ℕ}
theorem fineBond_ext {b b' : 𝒮.FineBond} (h₁ : b.1 = b'.1) (h₂ : b.2 = b'.2) : b = b' := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.fineBond_ext <;> assumption
theorem mapBond_secondType (Q : LevelCube 𝒮 M) (b : 𝒮.FineBond) :
    Q.secondTypeSystem.mapBond b = b := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.mapBond_secondType <;> assumption
theorem tsupport_subset_thicken (hl : TorusLengthsStatement) (Q : LevelCube 𝒮 M) (ς : ℝ) :
    tsupport Q.partitionFn ⊆ Q.thicken ς := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.tsupport_subset_thicken <;> assumption
end TransferToTorus
section NearCubes
variable {𝒮 : NestedRegions} {M : ℕ}
theorem mem_centresAt_level {y : 𝒮.Point} (hy : y ∈ 𝒮.allCentres) :
    y ∈ 𝒮.centresAt (𝒮.level y) := by apply _root_.YangMills.Construction.CubeNearSite.mem_centresAt_level <;> assumption
theorem levelScale_pos (y : 𝒮.Point) : 0 < 𝒮.levelScale y := by apply _root_.YangMills.Construction.RegionSequence.OperatorEstimates.levelScale_pos <;> assumption
end NearCubes
end CubeGreenSources
end YangMills.Construction
