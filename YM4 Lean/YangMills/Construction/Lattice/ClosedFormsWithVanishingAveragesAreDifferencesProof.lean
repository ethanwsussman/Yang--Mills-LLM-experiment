import YangMills.Construction.Lattice.AveragesAndWeightsProof
import YangMills.Construction.Lattice.IntertwiningOfTheAveragesWithTheDifferenceProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Set PeriodicLattice PeriodicLattice.DirichletOperators TorusMetric SeparatedSequences
  SeparatedSequences.BaseParameters
namespace VanishingAverageGradients
abbrev unitVec (μ : Fin 4) : Fin 4 → ℤ := Pi.single μ 1
def cubeBox (a : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(a : ℤ)) a
theorem mem_cubeBox {a : ℕ} {j : Fin 4 → ℤ} : j ∈ cubeBox a ↔ ∀ ν, -(a : ℤ) ≤ j ν ∧ j ν ≤ a := by
  simp [cubeBox, Fintype.mem_piFinset, Finset.mem_Icc]
theorem card_cubeBox (a : ℕ) : (cubeBox a).card = (2 * a + 1) ^ 4 := by
  have e : ((a : ℤ) + 1 + a).toNat = 2 * a + 1 := by omega
  simp [cubeBox, Fintype.card_piFinset, Finset.prod_const, e]
def pairing (c : Fin 4 → ℝ) (j : Fin 4 → ℤ) : ℝ := ∑ ν, c ν * (j ν : ℝ)
theorem pairing_add (c : Fin 4 → ℝ) (j j' : Fin 4 → ℤ) :
    pairing c (j + j') = pairing c j + pairing c j' := by
  simp [pairing, mul_add, Finset.sum_add_distrib]
theorem pairing_single (c : Fin 4 → ℝ) (ν : Fin 4) (k : ℤ) :
    pairing c (Pi.single ν k) = c ν * (k : ℝ) := by
  rw [pairing, Finset.sum_eq_single ν]
  · simp
  · intro μ _ hμ
    simp [Pi.single_eq_of_ne hμ]
  · simp
def periodSubgroup (F : (Fin 4 → ℤ) → ℝ) : AddSubgroup (Fin 4 → ℤ) where
  carrier := {v | ∀ k, F (k + v) = F k}
  add_mem' := by
    intro a b ha hb k
    rw [← add_assoc, hb, ha]
  zero_mem' := fun k => by simp
  neg_mem' := by
    intro a ha k
    have h := ha (k + -a)
    rw [neg_add_cancel_right] at h
    exact h.symm
theorem eq_at_zero_of_step_invariant {F : (Fin 4 → ℤ) → ℝ}
    (h : ∀ μ k, F (k + unitVec μ) = F k) (k : Fin 4 → ℤ) : F k = F 0 := by
  have e : k = ∑ μ, (k μ) • unitVec μ := by
    funext ν
    simp [Finset.sum_apply, Pi.single_apply]
  have hk : k ∈ periodSubgroup F := by
    rw [e]
    exact sum_mem fun μ _ => zsmul_mem (show unitVec μ ∈ periodSubgroup F from h μ) _
  simpa using hk 0
section ModelParameters
variable (E : BaseParameters)
theorem lengthRatio_pos : 0 < E.L := by
  have := E.three_le_L
  omega
theorem lengthRatio_real_pos : (0 : ℝ) < E.L := by exact_mod_cast lengthRatio_pos E
def fineStep (ν : Fin 4) : E.Torus :=
  ((unitStep E.L E.m (levelDepth E.K 0) ν : BareSite E.L E.m E.K) : E.Torus)
def fineVec (a : Fin 4 → ℤ) : E.Torus := ∑ ν, a ν • fineStep E ν
theorem fineVec_single (ν : Fin 4) (k : ℤ) : fineVec E (Pi.single ν k) = k • fineStep E ν := by
  rw [fineVec, Finset.sum_eq_single ν]
  · simp
  · intro μ _ hμ
    simp [Pi.single_eq_of_ne hμ]
  · simp
theorem fineVec_apply (a : Fin 4 → ℤ) (μ : Fin 4) :
    fineVec E a μ = (((a μ : ℝ) * meshSize E.L (levelDepth E.K 0) : ℝ) :
      AddCircle (torusSide E.L E.m)) := by
  have hz : ∀ (k : ℤ) (c : ℝ), k • (c : AddCircle (torusSide E.L E.m)) =
      (((k : ℝ) * c : ℝ) : AddCircle (torusSide E.L E.m)) := by
    intro k c
    rw [← zsmul_eq_mul]
    rfl
  rw [fineVec, Finset.sum_apply, Finset.sum_eq_single μ]
  · show a μ • pointOnAxis E.L E.m μ (meshSize E.L (levelDepth E.K 0)) μ = _
    rw [← hz]
    simp [pointOnAxis]
  · intro ν _ hν
    show a ν • pointOnAxis E.L E.m ν (meshSize E.L (levelDepth E.K 0)) μ = 0
    simp [pointOnAxis, Pi.single_eq_of_ne hν.symm]
  · simp
theorem meshSize_levelDepth (n : ℕ) :
    meshSize E.L (levelDepth E.K n) = ((E.L : ℝ) ^ n) * meshSize E.L (levelDepth E.K 0) := by
  have hL : (E.L : ℝ) ≠ 0 := (lengthRatio_real_pos E).ne'
  simp only [meshSize, levelDepth]
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ hL]
  congr 1
  ring
theorem unitStep_level_eq (n : ℕ) (μ : Fin 4) :
    ((unitStep E.L E.m (levelDepth E.K n) μ : E.LatticeSite n) : E.Torus) =
      fineVec E (Pi.single μ ((E.L : ℤ) ^ n)) := by
  funext ν
  rw [fineVec_apply]
  by_cases h : ν = μ
  · subst h
    show pointOnAxis E.L E.m ν _ ν = _
    simp only [pointOnAxis, Pi.single_eq_same]
    rw [meshSize_levelDepth]
    push_cast
    rfl
  · show pointOnAxis E.L E.m μ _ ν = _
    simp [pointOnAxis, Pi.single_eq_of_ne h]
end ModelParameters
section Blocks
variable (E : BaseParameters)
theorem isLevelLift_unique {x x' : E.Torus} {w : Fin 4 → ℝ}
    (h : IsLevelLift E.L E.m E.K E.t x w) (h' : IsLevelLift E.L E.m E.K E.t x' w) : x = x' := by
  obtain ⟨v, hv, hw⟩ := h
  obtain ⟨v', hv', hw'⟩ := h'
  funext μ
  rw [← hv, ← hv']
  have h1 : toLevelUnits E.L E.K E.t (v μ) = toLevelUnits E.L E.K E.t (v' μ) :=
    (hw μ).symm.trans (hw' μ)
  simp only [toLevelUnits] at h1
  have hL' : (E.L : ℝ) ≠ 0 := (lengthRatio_real_pos E).ne'
  rw [mul_left_cancel₀ (zpow_ne_zero _ hL') h1]
theorem shiftedPoint_eq (i : ℕ) (p : E.Torus) (a : Fin 4 → ℤ) :
    E.shiftedPoint i p a = p + fineVec E (fun ν => (E.L : ℤ) ^ i * a ν) := by
  change torusClassOf E.L E.m E.K E.t (Classical.epsilon (IsLevelLift E.L E.m E.K E.t p) +
    E.orderMesh i • ∑ μ, (a μ : ℝ) • coordVec μ) = _
  have h0 : IsLevelLift E.L E.m E.K E.t p (Classical.epsilon (IsLevelLift E.L E.m E.K E.t p)) := by
    refine Classical.epsilon_spec (p := IsLevelLift E.L E.m E.K E.t p) ?_
    choose v hv using fun μ => QuotientAddGroup.mk_surjective (p μ)
    exact ⟨_, v, hv, fun _ => rfl⟩
  set w0 := Classical.epsilon (IsLevelLift E.L E.m E.K E.t p) with hw0
  set r : Fin 4 → ℝ := E.orderMesh i • ∑ μ, (a μ : ℝ) • coordVec μ with hr
  have hθ : toLevelUnits E.L E.K E.t (meshSize E.L (levelDepth E.K 0)) = E.levelMeshRatio 0 :=
    E.lengthInUnits_meshSize 0
  have hrμ : ∀ μ, r μ = E.orderMesh i * (a μ : ℝ) := by
    intro μ
    simp [hr, coordVec, Finset.sum_apply, Pi.single_apply]
  have hl : IsLevelLift E.L E.m E.K E.t (p + fineVec E fun ν => (E.L : ℤ) ^ i * a ν) (w0 + r) := by
    obtain ⟨v, hv, hw⟩ := h0
    refine ⟨fun μ => v μ + (((E.L : ℤ) ^ i * a μ : ℤ) : ℝ) * meshSize E.L (levelDepth E.K 0),
      fun μ => ?_, fun μ => ?_⟩
    · rw [Pi.add_apply, fineVec_apply, ← hv μ]
      rfl
    · rw [Pi.add_apply, hw μ, hrμ μ]
      have e1 : toLevelUnits E.L E.K E.t
          (v μ + (((E.L : ℤ) ^ i * a μ : ℤ) : ℝ) * meshSize E.L (levelDepth E.K 0)) =
          toLevelUnits E.L E.K E.t (v μ) + (((E.L : ℤ) ^ i * a μ : ℤ) : ℝ) *
            toLevelUnits E.L E.K E.t (meshSize E.L (levelDepth E.K 0)) := by
        simp only [toLevelUnits]
        ring
      rw [e1, hθ]
      simp only [orderMesh]
      push_cast
      ring
  exact isLevelLift_unique E (Classical.epsilon_spec
    (⟨_, hl⟩ : ∃ x, IsLevelLift E.L E.m E.K E.t x (w0 + r))) hl
def halfWidth (n : ℕ) : ℕ := E.L ^ n / 2
theorem two_mul_halfWidth_add_one (n : ℕ) : 2 * halfWidth E n + 1 = E.L ^ n :=
  Nat.two_mul_div_two_add_one_of_odd E.odd_L.pow
theorem mem_boundedOffsets_iff (n : ℕ) (a : Fin 4 → ℤ) :
    a ∈ boundedOffsets (E.L ^ n) ↔ a ∈ cubeBox (halfWidth E n) := by
  have hh : (((E.L ^ n : ℕ) : ℝ) - 1) / 2 = (halfWidth E n : ℝ) := by
    have h1 : (((E.L ^ n : ℕ)) : ℝ) = 2 * (halfWidth E n : ℝ) + 1 := by
      exact_mod_cast (two_mul_halfWidth_add_one E n).symm
    rw [h1]
    ring
  rw [mem_cubeBox]
  show (∀ μ, |(a μ : ℝ)| ≤ (((E.L ^ n : ℕ) : ℝ) - 1) / 2) ↔ _
  rw [hh]
  refine forall_congr' fun ν => ?_
  rw [abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
def asFineSite {n : ℕ} (y : E.LatticeSite n) : BareSite E.L E.m E.K :=
  ⟨y, sublattice_mono (lengthRatio_pos E) E.m (by simp only [levelDepth]; push_cast; omega) y.2⟩
def fineSiteAt {n : ℕ} (y : E.LatticeSite n) (a : Fin 4 → ℤ) : BareSite E.L E.m E.K :=
  asFineSite E y + ∑ ν, a ν • unitStep E.L E.m (levelDepth E.K 0) ν
theorem coe_fineSiteAt {n : ℕ} (y : E.LatticeSite n) (a : Fin 4 → ℤ) :
    ((fineSiteAt E y a : BareSite E.L E.m E.K) : E.Torus) = (y : E.Torus) + fineVec E a := by
  simp [fineSiteAt, asFineSite, fineVec, fineStep]
def coarseSiteAt {n : ℕ} (y : E.LatticeSite (n + 1)) (i : Fin 4 → ℤ) : E.LatticeSite n :=
  ⟨y, sublattice_mono (lengthRatio_pos E) E.m (by simp only [levelDepth]; push_cast; omega) y.2⟩ +
    ∑ ν, i ν • unitStep E.L E.m (levelDepth E.K n) ν
theorem coe_coarseSiteAt {n : ℕ} (y : E.LatticeSite (n + 1)) (i : Fin 4 → ℤ) :
    ((coarseSiteAt E y i : E.LatticeSite n) : E.Torus) =
      (y : E.Torus) + fineVec E (fun ν => (E.L : ℤ) ^ n * i ν) := by
  have h1 : ((∑ ν, i ν • unitStep E.L E.m (levelDepth E.K n) ν : E.LatticeSite n) : E.Torus) =
      fineVec E (fun ν => (E.L : ℤ) ^ n * i ν) := by
    rw [AddSubgroup.val_finsetSum, fineVec]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [AddSubgroup.coe_zsmul, unitStep_level_eq, fineVec_single, smul_smul, mul_comm]
  simp only [coarseSiteAt, AddSubgroup.coe_add, h1]
end Blocks
section Sequence
variable (D : SequenceDatum) (H : LatticeCubeStatement)
include H in
theorem cube_sublattice_points {i i' : ℕ} (hii : i' ≤ i) (hi : i ≤ D.t) (y : D.LatticeSite i) :
    (∀ z : D.Torus, (z ∈ cube (D := D.toBaseParameters) y ∧
        z ∈ (sublattice D.L D.m (levelDepth D.K i') : Set D.Torus)) ↔
      ∃ a ∈ cubeBox (halfWidth D.toBaseParameters (i - i')),
        z = (y : D.Torus) + fineVec D.toBaseParameters (fun ν => (D.L : ℤ) ^ i' * a ν)) ∧
    ∀ a ∈ cubeBox (halfWidth D.toBaseParameters (i - i')),
      ∀ a' ∈ cubeBox (halfWidth D.toBaseParameters (i - i')),
        fineVec D.toBaseParameters (fun ν => (D.L : ℤ) ^ i' * a ν) =
          fineVec D.toBaseParameters (fun ν => (D.L : ℤ) ^ i' * a' ν) → a = a' := by
  have hiK : i ≤ D.m + D.K := (hi.trans D.t_le_K).trans (Nat.le_add_left _ _)
  obtain ⟨-, -, hLow, -, -, -, -, hBl2, -⟩ := H D i i' hii hiK
  have hmem : (y : D.Torus) ∈ D.orderCentreSet i := by
    rw [(hLow i hi).2.1]
    exact y.2
  obtain ⟨h1, h2, -⟩ := hBl2.1 ⟨y, hmem⟩
  have hcube := (hLow i hi).2.2 ⟨y, hmem⟩ y rfl
  rw [hcube, (hLow i' (hii.trans hi)).2.1] at h1
  simp only [orderScaleRatio] at h1 h2
  constructor
  · intro z
    have h3 : z ∈ (sublattice D.L D.m (levelDepth D.K i') : Set D.Torus) ∩
        cube (D := D.toBaseParameters) y ↔ _ := Set.ext_iff.1 h1 z
    constructor
    · rintro ⟨ha, hb⟩
      obtain ⟨a, ha', hz⟩ := h3.1 ⟨hb, ha⟩
      exact ⟨a, (mem_boundedOffsets_iff _ _ a).1 ha', by rw [← hz]; exact shiftedPoint_eq _ _ _ _⟩
    · rintro ⟨a, ha, rfl⟩
      have := h3.2 ⟨a, (mem_boundedOffsets_iff _ _ a).2 ha, shiftedPoint_eq _ _ _ _⟩
      exact ⟨this.2, this.1⟩
  · intro a ha a' ha' he
    refine h2 ((mem_boundedOffsets_iff _ _ a).2 ha) ((mem_boundedOffsets_iff _ _ a').2 ha') ?_
    rw [shiftedPoint_eq, shiftedPoint_eq, he]
include H in
theorem mem_fineBlock_iff {n : ℕ} (hn : n ≤ D.t) (y : D.LatticeSite n)
    (x : BareSite D.L D.m D.K) :
    (x : D.Torus) ∈ fineBlock (D := D.toBaseParameters) y ↔
      ∃ a ∈ cubeBox (halfWidth D.toBaseParameters n),
        x = fineSiteAt D.toBaseParameters y a := by
  have h := (cube_sublattice_points D H (Nat.zero_le n) hn y).1 (x : D.Torus)
  simp only [pow_zero, one_mul, Nat.sub_zero] at h
  constructor
  · intro hx
    obtain ⟨a, ha, hz⟩ := h.1 hx
    exact ⟨a, ha, Subtype.ext (by rw [coe_fineSiteAt, hz])⟩
  · rintro ⟨a, ha, rfl⟩
    exact h.2 ⟨a, ha, by rw [coe_fineSiteAt]⟩
include H in
theorem mem_coarseBlock_iff {n : ℕ} (hn : n + 1 ≤ D.t) (y : D.LatticeSite (n + 1))
    (z : D.LatticeSite n) :
    (z : D.Torus) ∈ coarseBlock (D := D.toBaseParameters) y ↔
      ∃ i ∈ cubeBox (halfWidth D.toBaseParameters 1),
        z = coarseSiteAt D.toBaseParameters y i := by
  have h := (cube_sublattice_points D H (show n ≤ n + 1 by omega) hn y).1 (z : D.Torus)
  simp only [Nat.add_sub_cancel_left] at h
  constructor
  · intro hz
    obtain ⟨a, ha, he⟩ := h.1 hz
    exact ⟨a, ha, Subtype.ext (by rw [coe_coarseSiteAt, he])⟩
  · rintro ⟨i, hi, rfl⟩
    exact h.2 ⟨i, hi, by rw [coe_coarseSiteAt]⟩
end Sequence
section Relation
theorem unitStep_injective {L m : ℕ} (hL : 0 < L) {j : ℤ} (hj : 0 ≤ j) :
    Function.Injective (unitStep L m j) := by apply _root_.YangMills.Construction.SeparatedSequences.BlockAverages.unitStep_injective <;> assumption
variable (D : SequenceDatum) (H : LatticeCubeStatement)
  (HG : SequenceGeometry) (φ : BondFrame)
  (G : ∀ n : ℕ, D.LatticeSite n → ℝ) (cc : Fin 4 → ℝ)
def BlockMeanRelation : Prop :=
  ∀ n, n + 1 ≤ D.t → ∀ y : D.LatticeSite (n + 1),
    G (n + 1) y = ((D.L : ℝ) ^ dimension)⁻¹ *
      ∑ᶠ z : {z : D.LatticeSite n //
        (z : D.Torus) ∈ coarseBlock (D := D.toBaseParameters) y}, G n z.1
variable {D φ G cc}
include H in
theorem mem_layerSites_iff {n : ℕ} (hn : n ≤ D.t) (y : D.LatticeSite n) :
    y ∈ D.layerSites D.region n ↔
      (y : D.Torus) ∈ D.memberAt D.region n ∧ (y : D.Torus) ∉ D.memberAt D.region (n + 1) := by apply _root_.YangMills.Construction.AveragesDifference.mem_layerSites_iff <;> assumption
variable (D G cc) in
def offsetInBlock (p : Σ n : ℕ, D.LatticeSite n) (x : BareSite D.L D.m D.K) : Fin 4 → ℤ :=
  Classical.epsilon fun a => a ∈ cubeBox (halfWidth D.toBaseParameters p.1) ∧
    x = fineSiteAt D.toBaseParameters p.2 a
variable (D G cc) in
open Classical in
def primitive (f : ZeroForms D.L D.m D.K) : ZeroForms D.L D.m D.K := fun x =>
  if x ∈ sitesOfRegion D.K (D.region 0) then
    f x - G (D.blockCentre D.region (x : D.Torus)).1 (D.blockCentre D.region (x : D.Torus)).2 +
      pairing cc (offsetInBlock D (D.blockCentre D.region (x : D.Torus)) x)
  else 0
end Relation
section Constant
variable (D : SequenceDatum) (H : LatticeCubeStatement)
end Constant
end VanishingAverageGradients
end YangMills.Construction.PeriodicLattice
end
