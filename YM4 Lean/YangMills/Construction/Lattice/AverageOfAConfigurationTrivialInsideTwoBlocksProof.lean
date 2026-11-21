import YangMills.Construction.Averaging.MeanOfTheConstantFamily
import YangMills.Construction.Lattice.AverageOfAConfigurationTrivialInsideTwoBlocks
import YangMills.Construction.Lattice.BoxesOfSitesFromACornerProof
import YangMills.Construction.Lattice.ContourFamiliesAndCombsInABlock
import YangMills.Construction.Lattice.GaugeCovarianceOfHolonomyProof
import YangMills.Construction.Lattice.GaugeSizeAnglesAndBlockMean
import YangMills.Construction.Lattice.StraightPathCorridorAndPivotBondOfEitherOrientationProof
import YangMills.Construction.Towers.DilationCarriesObjectsAtAStepOfASideProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice.TwoBlockFieldMean
variable {L m : ℕ} {j : ℤ}
private theorem mul_inv_of_det_one {X : ComplexMatrix2} (hX : X ∈ complexGaugeGroup) :
    X * X⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p13806 <;> assumption
private theorem inv_mul_of_det_one {X : ComplexMatrix2} (hX : X ∈ complexGaugeGroup) :
    X⁻¹ * X = 1 := by apply _root_.YangMills.DeltaSharedProofs.p40097 <;> assumption
private theorem inv_inv_of_det_one {X : ComplexMatrix2} (hX : X ∈ complexGaugeGroup) :
    X⁻¹⁻¹ = X :=
  Matrix.inv_eq_left_inv (mul_inv_of_det_one hX)
abbrev _root_.YangMills.DeltaSharedProofs.p3551 := @inv_inv_of_det_one
abbrev _root_.YangMills.SharedProofs.p6288 := @inv_inv_of_det_one
private theorem inv_mem_of_det_one {X : ComplexMatrix2} (hX : X ∈ complexGaugeGroup) :
    X⁻¹ ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
private theorem one_mem_det_one : (1 : ComplexMatrix2) ∈ complexGaugeGroup := Matrix.det_one
private theorem logSeries_one : ComplexMatrix2.logSeries 1 = 0 := by
  simp [ComplexMatrix2.logSeries]
private theorem isBondPathFromTo_cons {b : Bond L m j} {Γ : List (Bond L m j)}
    {z z' : Site L m j} :
    IsBondPathFromTo (b :: Γ) z z' ↔ b.source = z ∧ IsBondPathFromTo Γ b.target z' := by apply _root_.YangMills.Construction.PeriodicLattice.AxialPathCorridorProof.bondPath_cons_iff <;> assumption
private theorem pathHolonomy_eq_of_pureGauge {W : Bond L m j → ComplexMatrix2}
    {g : Site L m j → ComplexMatrix2}
    (hg : ∀ z, (g z)⁻¹ * g z = 1) (hg' : ∀ z, g z * (g z)⁻¹ = 1) :
    ∀ (Γ : List (Bond L m j)) (z z' : Site L m j), IsBondPathFromTo Γ z z' →
      (∀ b ∈ Γ, W b = (g b.source)⁻¹ * g b.target) → pathHolonomy W Γ = (g z)⁻¹ * g z'
  | [], z, z', h, _ => by
    obtain rfl := h.2.1 rfl
    simp [pathHolonomy, hg]
  | b :: Γ, z, z', h, hb => by
    obtain ⟨rfl, h'⟩ := isBondPathFromTo_cons.1 h
    have ih := pathHolonomy_eq_of_pureGauge hg hg' Γ b.target z' h'
      (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb'))
    have e : pathHolonomy W (b :: Γ) = W b * pathHolonomy W Γ := by simp [pathHolonomy]
    rw [e, ih, hb b (by simp), mul_assoc, ← mul_assoc (g b.target), hg', one_mul]
private theorem isBondPathFromTo_nil (z : Site L m j) :
    IsBondPathFromTo ([] : List (Bond L m j)) z z := by
  simp [IsBondPathFromTo, IsBondPath]
private theorem isBondPathFromTo_forwardFlow (μ : Fin 4) :
    ∀ (n : ℕ) (x : Site L m j),
      IsBondPathFromTo (forwardAxisPath x μ n) x (x + (n : ℤ) • unitStep L m j μ)
  | 0, x => by simpa [forwardAxisPath] using isBondPathFromTo_nil x
  | n + 1, x => by
    have h := isBondPathFromTo_forwardFlow μ n (x + unitStep L m j μ)
    have e : x + unitStep L m j μ + (n : ℤ) • unitStep L m j μ =
        x + ((n + 1 : ℕ) : ℤ) • unitStep L m j μ := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [e] at h
    exact isBondPathFromTo_cons.2 ⟨rfl, h⟩
private theorem isBondPathFromTo_backwardFlow (μ : Fin 4) :
    ∀ (n : ℕ) (x : Site L m j),
      IsBondPathFromTo (backwardAxisPath x μ n) x (x + (-(n : ℤ)) • unitStep L m j μ)
  | 0, x => by simpa [backwardAxisPath] using isBondPathFromTo_nil x
  | n + 1, x => by
    have h := isBondPathFromTo_backwardFlow μ n (x - unitStep L m j μ)
    have e : x - unitStep L m j μ + (-(n : ℤ)) • unitStep L m j μ =
        x + (-((n + 1 : ℕ) : ℤ)) • unitStep L m j μ := by
      simp only [Nat.cast_add, Nat.cast_one, neg_add, add_smul, neg_smul, one_smul]
      abel
    rw [e] at h
    exact isBondPathFromTo_cons.2 ⟨rfl, h⟩
private theorem isBondPathFromTo_flowAlong (x : Site L m j) (μ : Fin 4) (n : ℤ) :
    IsBondPathFromTo (flowAlong x μ n) x (x + n • unitStep L m j μ) := by
  unfold flowAlong
  split_ifs with h
  · have := isBondPathFromTo_forwardFlow μ n.toNat x
    rwa [Int.toNat_of_nonneg h] at this
  · have := isBondPathFromTo_backwardFlow μ (-n).toNat x
    rwa [Int.toNat_of_nonneg (by omega), neg_neg] at this
private theorem isBondPathFromTo_axialPath {x x' : Site L m j} {μ : Fin 4} {n : ℤ}
    (h : IsAxialDisplacement x x' μ n) : IsBondPathFromTo (axialPath x x') x x' := by
  have hex : ∃ q : Fin 4 × ℤ, IsAxialDisplacement x x' q.1 q.2 := ⟨(μ, n), h⟩
  unfold axialPath
  rw [dif_pos hex]
  have e : x + hex.choose.2 • unitStep L m j hex.choose.1 = x' := by
    rw [← hex.choose_spec.1]
    abel
  have := isBondPathFromTo_flowAlong x hex.choose.1 hex.choose.2
  rwa [e] at this
private theorem isBondPathFromTo_boundaryBonds (p : Plaquette L m j) :
    IsBondPathFromTo p.boundaryBonds p.origin p.origin := by apply _root_.YangMills.SharedProofs.p81322 <;> assumption
private theorem coe_toSublattice (hL : 0 < L) {j' : ℤ} (h : j ≤ j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y := by apply _root_.YangMills.Construction.PeriodicLattice.CornerBoxes.coe_toSublattice <;> assumption
section ConstantFamily
variable {ι : Type*} [Fintype ι] [Nonempty ι]
private theorem isLogMean_const_one_iff (H : Set ComplexMatrix2) (W : ComplexMatrix2) :
    ComplexMatrix2.IsLogMean H (fun _ : ι => (1 : ComplexMatrix2)) W ↔
      ComplexMatrix2.IsLogMean H (Averaging.identityFamily (Fintype.card ι)) W := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have : Nonempty (Fin (Fintype.card ι)) := ⟨⟨0, hn⟩⟩
  simp [ComplexMatrix2.IsLogMean, Averaging.identityFamily, Finset.sum_const, Finset.card_univ]
private theorem one_le_card_index : 1 ≤ Fintype.card ι := Fintype.card_pos
omit [Fintype ι] in
private theorem familyDiameter_const_one [Fintype ι] :
    ComplexMatrix2.familyDiameter (fun _ : ι => (1 : ComplexMatrix2)) = 0 := by
  simp [ComplexMatrix2.familyDiameter]
private theorem complexLogMean_const_one (hconst : Averaging.IdentityFamilyMeanIsOne) :
    complexLogMean (fun _ : ι => (1 : ComplexMatrix2)) = 1 := by
  refine Eq.trans ?_ (hconst (Fintype.card ι) one_le_card_index).2.2
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  unfold complexLogMean
  congr 1
  funext W
  apply propext
  rw [isLogMean_const_one_iff]
  exact and_congr Iff.rfl ⟨fun ⟨_, h⟩ => ⟨⟨0, hn⟩, h⟩, fun ⟨_, h⟩ => ⟨Classical.arbitrary ι, h⟩⟩
private theorem hasUniqueLogMean_const_one (hconst : Averaging.IdentityFamilyMeanIsOne) :
    ComplexMatrix2.HasUniqueLogMean compactGaugeGroup (fun _ : ι => (1 : ComplexMatrix2)) := by
  obtain ⟨W, hW, hu⟩ :=
    ((hconst (Fintype.card ι) one_le_card_index).2.1 compactGaugeGroup (Or.inl rfl)).2.1
  exact ⟨W, (isLogMean_const_one_iff _ _).2 hW,
    fun W' h' => hu W' ((isLogMean_const_one_iff _ _).1 h')⟩
private theorem logMean_const_one (hconst : Averaging.IdentityFamilyMeanIsOne) :
    ComplexMatrix2.logMean compactGaugeGroup (fun _ : ι => (1 : ComplexMatrix2)) = 1 := by
  refine Eq.trans ?_
    ((hconst (Fintype.card ι) one_le_card_index).2.1 compactGaugeGroup (Or.inl rfl)).2.2
  unfold ComplexMatrix2.logMean
  congr 1
  funext W
  exact propext (isLogMean_const_one_iff compactGaugeGroup W)
end ConstantFamily
private instance instNonemptyAxisOrdering {j' : ℤ} (y : Site L m j) (x : Site L m j') :
    Nonempty (AxisOrdering y x) :=
  ⟨(offsetAxes y x).equivFin.symm⟩
section Gauge
variable {K q : ℕ}
private def sourceBlockGauge (c : BondAtLevel L m K (q + 1)) (X : ComplexMatrix2)
    (z : SiteAtLevel L m K q) : ComplexMatrix2 :=
  open Classical in if (z : FourTorus L m) ∈ unitBlock c.source then 1 else X
private theorem sourceBlockGauge_of_mem_source {c : BondAtLevel L m K (q + 1)} {X : ComplexMatrix2}
    {z : SiteAtLevel L m K q} (h : (z : FourTorus L m) ∈ unitBlock c.source) :
    sourceBlockGauge c X z = 1 :=
  if_pos h
private theorem not_mem_sourceBlock_of_mem_targetBlock {c : BondAtLevel L m K (q + 1)}
    (hdis : unitBlock c.source ∩ unitBlock c.target = ∅) {z : FourTorus L m}
    (h : z ∈ (unitBlock c.target : Set (FourTorus L m))) :
    z ∉ (unitBlock c.source : Set (FourTorus L m)) := by
  intro h'
  have : z ∈ unitBlock c.source ∩ unitBlock c.target := ⟨h', h⟩
  rw [hdis] at this
  exact this
private theorem sourceBlockGauge_of_mem_target {c : BondAtLevel L m K (q + 1)} {X : ComplexMatrix2}
    (hdis : unitBlock c.source ∩ unitBlock c.target = ∅) {z : SiteAtLevel L m K q}
    (h : (z : FourTorus L m) ∈ unitBlock c.target) : sourceBlockGauge c X z = X :=
  if_neg (not_mem_sourceBlock_of_mem_targetBlock hdis h)
private theorem sourceBlockGauge_inv_mul {c : BondAtLevel L m K (q + 1)} {X : ComplexMatrix2}
    (hX : X ∈ complexGaugeGroup) (z : SiteAtLevel L m K q) :
    (sourceBlockGauge c X z)⁻¹ * sourceBlockGauge c X z = 1 := by
  unfold sourceBlockGauge
  split_ifs
  · simp
  · exact inv_mul_of_det_one hX
private theorem sourceBlockGauge_mul_inv {c : BondAtLevel L m K (q + 1)} {X : ComplexMatrix2}
    (hX : X ∈ complexGaugeGroup) (z : SiteAtLevel L m K q) :
    sourceBlockGauge c X z * (sourceBlockGauge c X z)⁻¹ = 1 := by
  unfold sourceBlockGauge
  split_ifs
  · simp
  · exact mul_inv_of_det_one hX
private theorem mem_bondsInDoubleBlock_iff {c : BondAtLevel L m K (q + 1)}
    {b : BondAtLevel L m K q} :
    b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K q)) ↔
      (b.source : FourTorus L m) ∈ bondDoubleBlock c ∧
        (b.target : FourTorus L m) ∈ bondDoubleBlock c :=
  Iff.rfl
private theorem twoBlockFieldValues_eq_pureGauge {c : BondAtLevel L m K (q + 1)}
    {X : ComplexMatrix2} (hk : DoubleBlockBondClassification c) (hX : X ∈ complexGaugeGroup)
    {b : BondAtLevel L m K q} (hb : b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K q))) :
    twoBlockFieldValues (levelDepth K q) c X b =
      (sourceBlockGauge c X b.source)⁻¹ * sourceBlockGauge c X b.target := by
  obtain ⟨hdis, hkinds, -, -, -⟩ := hk
  rcases hkinds b hb with ⟨hA, hB, hC, hD⟩ | ⟨hA, hB, hC, hD⟩ | ⟨hA, hB, hC, hD⟩ |
    ⟨hA, hB, hC, hD⟩
  · have h : b ∈ (bondsInside (unitBlock c.source) : Set (BondAtLevel L m K q)) ∨
        b ∈ (bondsInside (unitBlock c.target) : Set (BondAtLevel L m K q)) := Or.inl hA
    rw [twoBlockFieldValues, if_pos h, sourceBlockGauge_of_mem_source hA.1,
      sourceBlockGauge_of_mem_source hA.2]
    simp
  · have h : b ∈ (bondsInside (unitBlock c.source) : Set (BondAtLevel L m K q)) ∨
        b ∈ (bondsInside (unitBlock c.target) : Set (BondAtLevel L m K q)) := Or.inr hB
    rw [twoBlockFieldValues, if_pos h, sourceBlockGauge_of_mem_target hdis hB.1,
      sourceBlockGauge_of_mem_target hdis hB.2, inv_mul_of_det_one hX]
  · have h : ¬(b ∈ (bondsInside (unitBlock c.source) : Set (BondAtLevel L m K q)) ∨
        b ∈ (bondsInside (unitBlock c.target) : Set (BondAtLevel L m K q))) := not_or.2 ⟨hA, hB⟩
    rw [twoBlockFieldValues, if_neg h, if_pos hC, sourceBlockGauge_of_mem_source hC.1,
      sourceBlockGauge_of_mem_target hdis hC.2]
    simp
  · have h : ¬(b ∈ (bondsInside (unitBlock c.source) : Set (BondAtLevel L m K q)) ∨
        b ∈ (bondsInside (unitBlock c.target) : Set (BondAtLevel L m K q))) := not_or.2 ⟨hA, hB⟩
    rw [twoBlockFieldValues, if_neg h, if_neg hC, if_pos hD,
      sourceBlockGauge_of_mem_target (z := b.source) hdis hD.2,
      sourceBlockGauge_of_mem_source (z := b.target) hD.1]
    simp
private theorem onSetElseOne_twoBlockFieldValues (c : BondAtLevel L m K (q + 1))
    (X : ComplexMatrix2) :
    onSetElseOne (bondsInDoubleBlock c) (twoBlockFieldValues (levelDepth K q) c X) =
      twoBlockFieldValues (levelDepth K q) c X := by
  funext b
  unfold onSetElseOne
  by_cases hb : b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K q))
  · rw [if_pos hb]
  · rw [if_neg hb]
    have h₁ : ¬(b ∈ (bondsInside (unitBlock c.source) : Set (BondAtLevel L m K q)) ∨
        b ∈ (bondsInside (unitBlock c.target) : Set (BondAtLevel L m K q))) := by
      rintro (⟨h, h'⟩ | ⟨h, h'⟩)
      · exact hb (mem_bondsInDoubleBlock_iff.2 ⟨Or.inl h, Or.inl h'⟩)
      · exact hb (mem_bondsInDoubleBlock_iff.2 ⟨Or.inr h, Or.inr h'⟩)
    have h₂ : b ∉ (bondCorridor c : Set (BondAtLevel L m K q)) :=
      fun h => hb (mem_bondsInDoubleBlock_iff.2 ⟨Or.inl h.1, Or.inr h.2⟩)
    have h₃ : b.opposite ∉ (bondCorridor c : Set (BondAtLevel L m K q)) :=
      fun h => hb (mem_bondsInDoubleBlock_iff.2 ⟨Or.inr h.2, Or.inl h.1⟩)
    rw [twoBlockFieldValues, if_neg h₁, if_neg h₂, if_neg h₃]
private theorem twoBlockFieldValues_opposite {c : BondAtLevel L m K (q + 1)} {X : ComplexMatrix2}
    (hdis : unitBlock c.source ∩ unitBlock c.target = ∅) (hX : X ∈ complexGaugeGroup) :
    twoBlockFieldValues (levelDepth K q) c.opposite X⁻¹ =
      twoBlockFieldValues (levelDepth K q) c X := by
  funext b
  have et : c.opposite.source = c.target := rfl
  have eh : c.opposite.target = c.source := rfl
  have hcor : b ∈ (bondCorridor c.opposite : Set (BondAtLevel L m K q)) ↔
      b.opposite ∈ (bondCorridor c : Set (BondAtLevel L m K q)) :=
    ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hcor' : b.opposite ∈ (bondCorridor c.opposite : Set (BondAtLevel L m K q)) ↔
      b ∈ (bondCorridor c : Set (BondAtLevel L m K q)) :=
    ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [twoBlockFieldValues, twoBlockFieldValues, et, eh]
  by_cases h₁ : b ∈ (bondsInside (unitBlock c.source) : Set (BondAtLevel L m K q)) ∨
      b ∈ (bondsInside (unitBlock c.target) : Set (BondAtLevel L m K q))
  · rw [if_pos h₁, if_pos h₁.symm]
  · have h₁' : ¬(b ∈ (bondsInside (unitBlock c.target) : Set (BondAtLevel L m K q)) ∨
        b ∈ (bondsInside (unitBlock c.source) : Set (BondAtLevel L m K q))) :=
      fun h => h₁ h.symm
    rw [if_neg h₁, if_neg h₁']
    by_cases h₂ : b ∈ (bondCorridor c : Set (BondAtLevel L m K q))
    · have h₃ : b ∉ (bondCorridor c.opposite : Set (BondAtLevel L m K q)) :=
        fun h => not_mem_sourceBlock_of_mem_targetBlock hdis h.1 h₂.1
      rw [if_neg h₃, if_pos (hcor'.2 h₂), if_pos h₂, inv_inv_of_det_one hX]
    · by_cases h₄ : b.opposite ∈ (bondCorridor c : Set (BondAtLevel L m K q))
      · rw [if_pos (hcor.2 h₄), if_neg h₂, if_pos h₄]
      · rw [if_neg (mt hcor.1 h₄), if_neg (mt hcor'.1 h₂), if_neg h₂, if_neg h₄]
private theorem isGaugeField_twoBlockFieldValues {c : BondAtLevel L m K (q + 1)}
    {X : ComplexMatrix2} {𝒢 : Set ComplexMatrix2}
    (hk : DoubleBlockBondClassification c) (hXc : X ∈ complexGaugeGroup)
    (h1 : (1 : ComplexMatrix2) ∈ 𝒢) (hX : X ∈ 𝒢) (hXi : X⁻¹ ∈ 𝒢) :
    IsGaugeField 𝒢 (bondsInDoubleBlock c) (twoBlockFieldValues (levelDepth K q) c X) := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · rw [twoBlockFieldValues_eq_pureGauge hk hXc hb]
    unfold sourceBlockGauge
    split_ifs <;> simp [*, inv_mul_of_det_one hXc]
  · rw [twoBlockFieldValues_eq_pureGauge hk hXc hb,
      twoBlockFieldValues_eq_pureGauge hk hXc (hk.2.2.1 b hb)]
    change (sourceBlockGauge c X b.target)⁻¹ * sourceBlockGauge c X b.source = _
    unfold sourceBlockGauge
    split_ifs <;> simp [inv_mul_of_det_one hXc, inv_inv_of_det_one hXc]
private theorem pathHolonomy_twoBlockFieldValues {c : BondAtLevel L m K (q + 1)}
    {X : ComplexMatrix2} (hk : DoubleBlockBondClassification c) (hX : X ∈ complexGaugeGroup)
    {Γ : List (BondAtLevel L m K q)} {z z' : SiteAtLevel L m K q}
    (hΓ : IsBondPathFromTo Γ z z')
    (hb : ∀ b ∈ Γ, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K q))) :
    pathHolonomy (twoBlockFieldValues (levelDepth K q) c X) Γ =
      (sourceBlockGauge c X z)⁻¹ * sourceBlockGauge c X z' :=
  pathHolonomy_eq_of_pureGauge (sourceBlockGauge_inv_mul hX) (sourceBlockGauge_mul_inv hX)
    Γ z z' hΓ fun b h => twoBlockFieldValues_eq_pureGauge hk hX (hb b h)
private theorem twoBlockFieldTransports_holds {c : BondAtLevel L m K (q + 1)} {X : ComplexMatrix2}
    (hk : DoubleBlockBondClassification c) (hX : X ∈ complexGaugeGroup) :
    TwoBlockFieldTransports (levelDepth K q) c X := by
  refine ⟨isGaugeField_twoBlockFieldValues hk hX one_mem_det_one hX (inv_mem_of_det_one hX),
    fun hXr => isGaugeField_twoBlockFieldValues hk hX (one_mem _) hXr
      (inv_mem_specialUnitary hXr), ?_, ?_⟩
  · have hb : (bondsInDoubleBlock c.opposite : Set (BondAtLevel L m K q)) =
        bondsInDoubleBlock c :=
      hk.2.2.2.1
    simp only [twoBlockField, twoBlockFieldValues_opposite hk.1 hX, hb]
  · intro Γ z z' hΓ hb
    refine ⟨?_, fun h h' => ?_⟩
    · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
      · rw [pathHolonomy_twoBlockFieldValues hk hX hΓ hb,
          sourceBlockGauge_of_mem_source (z := z) h, sourceBlockGauge_of_mem_source (z := z') h']
        simp
      · rw [pathHolonomy_twoBlockFieldValues hk hX hΓ hb,
          sourceBlockGauge_of_mem_target (z := z) hk.1 h,
          sourceBlockGauge_of_mem_target (z := z') hk.1 h', inv_mul_of_det_one hX]
    · rw [pathHolonomy_twoBlockFieldValues hk hX hΓ hb, sourceBlockGauge_of_mem_source (z := z) h,
        sourceBlockGauge_of_mem_target (z := z') hk.1 h']
      simp
private theorem plaquetteHolonomy_trivial {c : BondAtLevel L m K (q + 1)} {X : ComplexMatrix2}
    (hk : DoubleBlockBondClassification c) (hpl : DoubleBlockPlaquetteBondsInside c)
    (hX : X ∈ complexGaugeGroup) : TwoBlockPlaquetteHolonomyTrivial (levelDepth K q) c X := by
  intro p hp
  rw [plaquetteHolonomy,
    pathHolonomy_twoBlockFieldValues hk hX (isBondPathFromTo_boundaryBonds p) (hpl p hp),
    sourceBlockGauge_inv_mul hX]
private theorem levelDepth_succ_le (K q : ℕ) : levelDepth K (q + 1) ≤ levelDepth K q := by apply _root_.YangMills.Construction.Tower.ScalingPreservesStepsAtSide.levelDepth_succ_le <;> assumption
private theorem centre_mem_sitesInBlock (hcf : BlockContoursAndCombs)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hq : q < K)
    {y : SiteAtLevel L m K (q + 1)} {x : SiteAtLevel L m K q}
    (hx : (x : FourTorus L m) ∈ unitBlock y) :
    y.toSublattice (levelDepth K q) ∈ sitesInBlock (levelDepth K q) y := by
  obtain ⟨σ⟩ := instNonemptyAxisOrdering y x
  have hyy := ((hcf L m K hL hm q hq y x hx).2.1 _ ⟨σ, rfl⟩).2.1
  have hpos : 0 < L := by have := hL.2; omega
  show ((y.toSublattice (levelDepth K q) : SiteAtLevel L m K q) : FourTorus L m) ∈ unitBlock y
  rw [coe_toSublattice hpos (levelDepth_succ_le K q)]
  exact hyy
private theorem contourHolonomy_trivial (hconst : Averaging.IdentityFamilyMeanIsOne)
    (hcf : BlockContoursAndCombs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hq : q < K) {c : BondAtLevel L m K (q + 1)} {X : ComplexMatrix2}
    (hk : DoubleBlockBondClassification c) (hcon : ContoursStayInBlocks c)
    (hX : X ∈ complexGaugeGroup) : TwoBlockContourHolonomyTrivial (levelDepth K q) c X := by
  intro y hy x hx
  have hy' : y = c.source ∨ y = c.target := hy
  have hall : ∀ Γ ∈ contourSet y x,
      pathHolonomy (twoBlockFieldValues (levelDepth K q) c X) Γ = 1 := by
    intro Γ hΓ
    have hpath := ((hcf L m K hL hm q hq y x hx).2.1 Γ hΓ).1
    have hc := centre_mem_sitesInBlock hcf hL hm hq (y := y) (x := x) hx
    rw [pathHolonomy_twoBlockFieldValues hk hX hpath (hcon y hy' x hx Γ hΓ).2]
    rcases hy' with rfl | rfl
    · rw [sourceBlockGauge_of_mem_source (z := x) hx,
        sourceBlockGauge_of_mem_source (z := c.source.toSublattice _) hc]
      simp
    · rw [sourceBlockGauge_of_mem_target (z := x) hk.1 hx,
        sourceBlockGauge_of_mem_target (z := c.target.toSublattice _) hk.1 hc,
        inv_mul_of_det_one hX]
  have hfam : contourHolonomies (twoBlockFieldValues (levelDepth K q) c X) y x = fun _ => 1 :=
    funext fun σ => hall _ ⟨σ, rfl⟩
  have hconf :=
    isGaugeField_twoBlockFieldValues hk hX one_mem_det_one hX (inv_mem_of_det_one hX)
  have hsub : ∀ b ∈ (bondsInside (unitBlock y) : Set (BondAtLevel L m K q)),
      b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K q)) := by
    rintro b ⟨h, h'⟩
    rcases hy' with rfl | rfl
    · exact mem_bondsInDoubleBlock_iff.2 ⟨Or.inl h, Or.inl h'⟩
    · exact mem_bondsInDoubleBlock_iff.2 ⟨Or.inr h, Or.inr h'⟩
  refine ⟨hall, ⟨⟨fun b hb => hconf.1 b (hsub b hb), fun b hb => hconf.2 b (hsub b hb)⟩, ?_⟩,
    ?_, fun _ => ⟨?_, ?_⟩⟩
  · rw [hfam, familyDiameter_const_one]
    norm_num [Averaging.centreOfMassDiameter]
  · unfold complexMeanContourHolonomy
    rw [hfam]
    exact complexLogMean_const_one hconst
  · unfold HasContourMean
    rw [hfam]
    exact hasUniqueLogMean_const_one hconst
  · unfold meanContourHolonomy
    rw [hfam]
    exact logMean_const_one hconst
private theorem pathHolonomy_crossingPath {c : BondAtLevel L m K (q + 1)} {X : ComplexMatrix2}
    (hk : DoubleBlockBondClassification c) (hs : AxialPathsSpanDoubleBlock c)
    (hX : X ∈ complexGaugeGroup) {x : SiteAtLevel L m K q}
    (hx : x ∈ sitesInBlock (levelDepth K q) c.source) :
    pathHolonomy (twoBlockFieldValues (levelDepth K q) c X) (crossingPath c x) = X := by
  obtain ⟨hx', ⟨μ, k, hd⟩, -, -, hb⟩ := hs.1 x hx
  have hp : IsBondPathFromTo (crossingPath c x) x (shiftAcross c x) :=
    isBondPathFromTo_axialPath hd
  rw [pathHolonomy_twoBlockFieldValues hk hX hp hb, sourceBlockGauge_of_mem_source (z := x) hx,
    sourceBlockGauge_of_mem_target hk.1 hx']
  simp
private theorem parallelTransport_twoBlockFieldValues (hcf : BlockContoursAndCombs)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hq : q < K)
    {c : BondAtLevel L m K (q + 1)} {X : ComplexMatrix2} (hk : DoubleBlockBondClassification c)
    (hs : AxialPathsSpanDoubleBlock c) (hX : X ∈ complexGaugeGroup) :
    parallelTransport (twoBlockFieldValues (levelDepth K q) c X) c = X := by
  obtain ⟨b, hb⟩ := hs.2
  have hc := centre_mem_sitesInBlock hcf hL hm hq (y := c.source) (x := b.source) hb.1
  have hpos : 0 < L := by have := hL.2; omega
  have et : shiftAcross c (c.source.toSublattice (levelDepth K q)) =
      c.target.toSublattice (levelDepth K q) := by
    apply Subtype.ext
    show ((c.source.toSublattice (levelDepth K q) +
      (c.target - c.source).toSublattice (levelDepth K q) :
      SiteAtLevel L m K q) : FourTorus L m) = _
    rw [AddSubgroup.coe_add, coe_toSublattice hpos (levelDepth_succ_le K q),
      coe_toSublattice hpos (levelDepth_succ_le K q),
      coe_toSublattice hpos (levelDepth_succ_le K q), AddSubgroup.coe_sub]
    abel
  have h := pathHolonomy_crossingPath hk hs hX hc
  rw [crossingPath, et] at h
  exact h
private theorem crossingHolonomy_holds (hconst : Averaging.IdentityFamilyMeanIsOne)
    (hcf : BlockContoursAndCombs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hq : q < K) {c : BondAtLevel L m K (q + 1)} {X : ComplexMatrix2}
    (hk : DoubleBlockBondClassification c) (hcon : ContoursStayInBlocks c)
    (hs : AxialPathsSpanDoubleBlock c) (hX : X ∈ complexGaugeGroup) :
    TwoBlockCrossingHolonomy (levelDepth K q) c X := by
  intro x hx
  have hC := contourHolonomy_trivial hconst hcf hL hm hq hk hcon hX
  have hcr := pathHolonomy_crossingPath hk hs hX hx
  have htr := parallelTransport_twoBlockFieldValues hcf hL hm hq hk hs hX
  refine ⟨hcr, htr, ?_⟩
  rw [complexCrossingDefect, (hC c.source (Or.inl rfl) x hx).2.2.1,
    (hC c.target (Or.inr rfl) (shiftAcross c x) (hs.1 x hx).1).2.2.1, hcr, htr]
  simp [mul_inv_of_det_one hX]
private theorem crossingDefect_twoBlockFieldValues (hconst : Averaging.IdentityFamilyMeanIsOne)
    (hcf : BlockContoursAndCombs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hq : q < K) {c : BondAtLevel L m K (q + 1)} {X : ComplexMatrix2}
    (hk : DoubleBlockBondClassification c) (hcon : ContoursStayInBlocks c)
    (hs : AxialPathsSpanDoubleBlock c) (hX : X ∈ complexGaugeGroup)
    (hXr : X ∈ compactGaugeGroup)
    {x : SiteAtLevel L m K q} (hx : x ∈ sitesInBlock (levelDepth K q) c.source) :
    crossingDefect (twoBlockFieldValues (levelDepth K q) c X) c x = 1 := by
  have hC := contourHolonomy_trivial hconst hcf hL hm hq hk hcon hX
  rw [crossingDefect, ((hC c.source (Or.inl rfl) x hx).2.2.2 hXr).2,
    ((hC c.target (Or.inr rfl) (shiftAcross c x) (hs.1 x hx).1).2.2.2 hXr).2,
    pathHolonomy_crossingPath hk hs hX hx,
    parallelTransport_twoBlockFieldValues hcf hL hm hq hk hs hX]
  simp [mul_inv_of_det_one hX]
private theorem matExp_smul_finsum_logSeries_eq_one {α : Type*} (S : Set α)
    (f : α → ComplexMatrix2) (w : ℂ) (h : ∀ x ∈ S, f x = 1) :
    ComplexMatrix2.matExp (w • ∑ᶠ x ∈ S, ComplexMatrix2.logSeries (f x)) = 1 := by
  have e : ∑ᶠ x ∈ S, ComplexMatrix2.logSeries (f x) = 0 :=
    finsum_mem_of_eqOn_zero fun x hx => by rw [h x hx, logSeries_one]; rfl
  rw [e, smul_zero]
  exact NormedSpace.exp_zero
private theorem complexAverage_twoBlockFieldValues (hconst : Averaging.IdentityFamilyMeanIsOne)
    (hcf : BlockContoursAndCombs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hq : q < K) {c : BondAtLevel L m K (q + 1)} {X : ComplexMatrix2}
    (hk : DoubleBlockBondClassification c) (hcon : ContoursStayInBlocks c)
    (hs : AxialPathsSpanDoubleBlock c) (hX : X ∈ complexGaugeGroup) :
    twoBlockFieldValues (levelDepth K q) c X ∈
        (complexAveragingDomainNearOne c : Set (BondAtLevel L m K q → ComplexMatrix2)) ∧
      complexBlockAverageOnPositive (twoBlockFieldValues (levelDepth K q) c X) c = X := by
  have hC := contourHolonomy_trivial hconst hcf hL hm hq hk hcon hX
  have hD := crossingHolonomy_holds hconst hcf hL hm hq hk hcon hs hX
  refine ⟨⟨⟨isGaugeField_twoBlockFieldValues hk hX one_mem_det_one hX (inv_mem_of_det_one hX),
    fun x hx => (hC c.source (Or.inl rfl) x hx).2.1.2,
    fun x hx => (hC c.target (Or.inr rfl) x hx).2.1.2⟩, fun x hx => ?_⟩, ?_⟩
  · rw [(hD x hx).2.2]
    simp
  · rw [complexBlockAverageOnPositive,
      matExp_smul_finsum_logSeries_eq_one _ _ _ fun x hx => (hD x hx).2.2, one_mul,
      parallelTransport_twoBlockFieldValues hcf hL hm hq hk hs hX]
private theorem regularAverage_twoBlockFieldValues (hconst : Averaging.IdentityFamilyMeanIsOne)
    (hcf : BlockContoursAndCombs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hq : q < K) {c : BondAtLevel L m K (q + 1)} {X : ComplexMatrix2} {ω : ℝ}
    (hω : 0 < ω) (hk : DoubleBlockBondClassification c) (hcon : ContoursStayInBlocks c)
    (hs : AxialPathsSpanDoubleBlock c) (hpl : DoubleBlockPlaquetteBondsInside c)
    (hX : X ∈ complexGaugeGroup) (hXr : X ∈ compactGaugeGroup) :
    IsRegularAveragingCase ω (twoBlockFieldValues (levelDepth K q) c X) c ∧
      blockAverageOnPositive ω (twoBlockFieldValues (levelDepth K q) c X) c = X := by
  have hC := contourHolonomy_trivial hconst hcf hL hm hq hk hcon hX
  have hel := fun {x : SiteAtLevel L m K q} (hx : x ∈ sitesInBlock (levelDepth K q) c.source) =>
    crossingDefect_twoBlockFieldValues hconst hcf hL hm hq hk hcon hs hX hXr hx
  have hA : IsRegularAveragingCase ω (twoBlockFieldValues (levelDepth K q) c X) c := by
    refine ⟨fun p hp => ?_, fun x hx => ((hC c.source (Or.inl rfl) x hx).2.2.2 hXr).1,
      fun x hx => ((hC c.target (Or.inr rfl) x hx).2.2.2 hXr).1, fun x hx => ?_⟩
    · rw [plaquetteHolonomy_trivial hk hpl hX p hp]
      simpa using hω
    · rw [hel hx]
      simp
  refine ⟨hA, ?_⟩
  rw [blockAverageOnPositive, if_pos hA, regularAverageValue,
    matExp_smul_finsum_logSeries_eq_one _ _ _ fun x hx => hel hx, one_mul,
    parallelTransport_twoBlockFieldValues hcf hL hm hq hk hs hX]
end Gauge
private theorem positivelyOriented_of_isPositivelyOriented {c : Bond L m j}
    (h : c.IsPositivelyOriented) : c.positivelyOriented = c := if_pos h
private theorem positivelyOriented_of_not_isPositivelyOriented {c : Bond L m j}
    (h : ¬c.IsPositivelyOriented) : c.positivelyOriented = c.opposite := if_neg h
theorem twoBlockFieldMeanProperties_holds (hd : DoubleBlockStructure.Statement)
    (hcf : BlockContoursAndCombs) (hconst : Averaging.IdentityFamilyMeanIsOne) :
    TwoBlockFieldMeanProperties := by
  intro L hL m K q hm hq c X hX
  obtain ⟨hk, hcon, hs, hpl, -⟩ := hd L m K q hL hm hq c
  obtain ⟨hk', hcon', hs', hpl', -⟩ := hd L m K q hL hm hq c.opposite
  have hXi := inv_mem_of_det_one hX
  have hval := twoBlockFieldValues_opposite (q := q) hk.1 hX
  have hid := onSetElseOne_twoBlockFieldValues (q := q) c X
  have hcc := complexAverage_twoBlockFieldValues hconst hcf hL hm hq hk hcon hs hX
  have hcc' := complexAverage_twoBlockFieldValues hconst hcf hL hm hq hk' hcon' hs' hXi
  rw [hval] at hcc'
  have hB := plaquetteHolonomy_trivial hk hpl hX
  refine ⟨twoBlockFieldTransports_holds hk hX, hB,
    contourHolonomy_trivial hconst hcf hL hm hq hk hcon hX,
    crossingHolonomy_holds hconst hcf hL hm hq hk hcon hs hX, ?_, fun hXr => ?_⟩
  · have hdom : twoBlockFieldValues (levelDepth K q) c X ∈
        (complexAveragingDomainNearOne c.positivelyOriented :
          Set (BondAtLevel L m K q → ComplexMatrix2)) := by
      by_cases hp : c.IsPositivelyOriented
      · rw [positivelyOriented_of_isPositivelyOriented hp]
        exact hcc.1
      · rw [positivelyOriented_of_not_isPositivelyOriented hp]
        exact hcc'.1
    refine ⟨by rw [hid]; exact hdom, ⟨subset_rfl, ?_⟩, ?_⟩
    · show onSetElseOne (bondsInDoubleBlock c) (twoBlockFieldValues (levelDepth K q) c X) ∈ _
      rw [hid]
      exact hdom
    · show complexBlockAverage
        (onSetElseOne (bondsInDoubleBlock c) (twoBlockFieldValues (levelDepth K q) c X)) c = X
      rw [hid]
      by_cases hp : c.IsPositivelyOriented
      · exact (if_pos hp).trans hcc.2
      · refine (if_neg hp).trans ?_
        rw [hcc'.2, inv_inv_of_det_one hX]
  · have hω : 0 < Averaging.smoothingRadius L :=
      (Averaging.isSmoothingRadius_smoothingRadius hL.1 hL.2).1
    have hXri := inv_mem_specialUnitary hXr
    have hrc := regularAverage_twoBlockFieldValues hconst hcf hL hm hq hω hk hcon hs hpl hX hXr
    have hrc' :=
      regularAverage_twoBlockFieldValues hconst hcf hL hm hq hω hk' hcon' hs' hpl' hXi hXri
    rw [hval] at hrc'
    have hcase : IsRegularAveragingCase (Averaging.smoothingRadius L)
        (twoBlockFieldValues (levelDepth K q) c X) c.positivelyOriented := by
      by_cases hp : c.IsPositivelyOriented
      · rw [positivelyOriented_of_isPositivelyOriented hp]
        exact hrc.1
      · rw [positivelyOriented_of_not_isPositivelyOriented hp]
        exact hrc'.1
    refine ⟨fun U hU hag => ⟨hU, fun p hp => ?_⟩, ?_,
      show (bondsInDoubleBlock c : Set (BondAtLevel L m K q)) ⊆ bondsInDoubleBlock c from
        subset_rfl, ?_⟩
    · have e : plaquetteHolonomy U p =
          plaquetteHolonomy (twoBlockFieldValues (levelDepth K q) c X) p := by
        unfold plaquetteHolonomy pathHolonomy
        congr 1
        exact List.map_congr_left fun b hb => hag b (hpl p hp b hb)
      rw [e, hB p hp]
      simpa using hω
    · rw [partialBlockAverageCase, hid]
      exact if_pos hcase
    · show blockAverage (Averaging.smoothingRadius L)
        (onSetElseOne (bondsInDoubleBlock c) (twoBlockFieldValues (levelDepth K q) c X)) c = X
      rw [hid]
      by_cases hp : c.IsPositivelyOriented
      · exact (if_pos hp).trans hrc.2
      · refine (if_neg hp).trans ?_
        rw [hrc'.2, inv_inv_of_det_one hX]
end PeriodicLattice.TwoBlockFieldMean
end YangMills.Construction
