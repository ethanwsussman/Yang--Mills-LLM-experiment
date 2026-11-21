import YangMills.Construction.RunningCouplingSlope.LegsOfTheOrdersAreContours
import YangMills.Construction.RunningCouplingSlope.PlainExpansionsDetermineTheBlocks
import YangMills.Construction.Towers.AveragedContourOfAPairDoesNotDependOnTheBondProof
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.ReverseOfAStraightPathOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MeanExpansionsLocal
open YangMills.Construction.Tower
variable {L n k : ℕ}
private abbrev linksUnder {j : ℕ} (c : Edge L n k j) : Set (Edge L n k 0) :=
  PeriodicLattice.bondsInside
    (PeriodicLattice.refinedBlock j c.source ∪ PeriodicLattice.refinedBlock j c.target)
private abbrev doubleBlock {j : ℕ} (c : Edge L n k (j + 1)) : Set (PeriodicLattice.FourTorus L n) :=
  PeriodicLattice.unitBlock c.source ∪ PeriodicLattice.unitBlock c.target
private structure Hypotheses (L n k : ℕ) : Prop where
  hZ : BlockPathContourPivotStatement
  hC : AxisOrderLegsAreContours
  hR : AxisPathReversal.MainStatement
  hL : Conventions.IsAdmissibleBlockingFactor L
  hn : 0 < n
  hk : 1 ≤ k
private theorem isPositivelyOriented_or_opposite {j : ℕ} (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem linksUnder_opposite {j : ℕ} (c : Edge L n k j) :
    linksUnder c.opposite = linksUnder c := by
  change PeriodicLattice.bondsInside
    (PeriodicLattice.refinedBlock j c.target ∪ PeriodicLattice.refinedBlock j c.source) = _
  rw [union_comm]
abbrev _root_.YangMills.DeltaSharedProofs.p502040 := @linksUnder_opposite
private theorem mem_refinedBlock_zero (H : Hypotheses L n k) {j : ℕ} (hj : j ≤ k) (y : Vertex L n k j) :
    (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock 0 y := by
  have E := ((H.hZ L H.hL k 0 j H.hk (Nat.zero_le _) hj).1 n H.hn).1.eq_image y
  rw [E]
  have e : ∀ μ : Fin 4, PeriodicLattice.pointOnAxis L n μ 0 = 0 := fun μ => by
    rw [PeriodicLattice.pointOnAxis,
      show ((0 : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) = 0 from rfl, Pi.single_zero]
  exact ⟨0, by simp [offsetBox], by simp [offsetPoint, e]⟩
private theorem mem_linksUnder_self (H : Hypotheses L n k) (b : Edge L n k 0) : b ∈ linksUnder b :=
  ⟨Or.inl (mem_refinedBlock_zero H (Nat.zero_le _) b.source),
    Or.inr (mem_refinedBlock_zero H (Nat.zero_le _) b.target)⟩
private theorem opposite_mem_linksUnder (H : Hypotheses L n k) (b : Edge L n k 0) :
    b.opposite ∈ linksUnder b :=
  ⟨Or.inr (mem_refinedBlock_zero H (Nat.zero_le _) b.target),
    Or.inl (mem_refinedBlock_zero H (Nat.zero_le _) b.source)⟩
private theorem refinedBlock_subset_succ (H : Hypotheses L n k) {j : ℕ} (hj : j < k)
    {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
    (hx : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y) :
    PeriodicLattice.refinedBlock j x ⊆ PeriodicLattice.refinedBlock (j + 1) y := by
  intro z hz
  have E := ((H.hZ L H.hL k (j + 1) (j + 1) H.hk le_rfl (by omega)).1 n H.hn).1.eq_biUnion_lower
    (by omega) y
  rw [E]
  exact mem_iUnion₂.2 ⟨x, hx, hz⟩
private theorem linksUnder_subset (H : Hypotheses L n k) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1))
    {b : Edge L n k j} (e₁ : (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c)
    (e₂ : (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c) :
    linksUnder b ⊆ linksUnder c := by
  have sub : ∀ x : Vertex L n k j, (x : PeriodicLattice.FourTorus L n) ∈ doubleBlock c →
      PeriodicLattice.refinedBlock j x ⊆
        PeriodicLattice.refinedBlock (j + 1) c.source ∪ PeriodicLattice.refinedBlock (j + 1) c.target :=
    fun x hx => hx.elim (fun h => (refinedBlock_subset_succ H hj h).trans subset_union_left)
      fun h => (refinedBlock_subset_succ H hj h).trans subset_union_right
  have sub' : PeriodicLattice.refinedBlock j b.source ∪ PeriodicLattice.refinedBlock j b.target ⊆
      PeriodicLattice.refinedBlock (j + 1) c.source ∪ PeriodicLattice.refinedBlock (j + 1) c.target :=
    union_subset (sub _ e₁) (sub _ e₂)
  exact fun w hw => ⟨sub' hw.1, sub' hw.2⟩
private theorem orderedContour_ends_mem (H : Hypotheses L n k) {j : ℕ} (hj : j < k)
    {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    (σ : PeriodicLattice.AxisOrdering y x) {b : Edge L n k j}
    (hb : b ∈ PeriodicLattice.orderedContour y x σ) :
    (b.source : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∧
      (b.target : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y := by
  obtain ⟨Hb, -, -, -, -, Hc⟩ := (H.hZ L H.hL k 1 (j + 1) H.hk (by omega) (by omega)).1 n H.hn
  have hx' : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock 1 y := hx
  rw [Hb.eq_image y] at hx'
  obtain ⟨ν, hν, hxν⟩ := hx'
  obtain ⟨-, -, -, -, hz⟩ := ((Hc (by omega)).1.contours y ν hν x hxν.symm).2 _ ⟨σ, rfl⟩
  exact ⟨hz b.source (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩)),
    hz b.target (Or.inr (Or.inr ⟨b, hb, Or.inr rfl⟩))⟩
private theorem contourLeg_ends_mem (H : Hypotheses L n k) {j : ℕ} (hj : j < k)
    {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) (π : Equiv.Perm (Fin 4))
    {b : Edge L n k j} (hb : b ∈ contourLeg y x π) :
    (b.source : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∧
      (b.target : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y := by
  obtain ⟨σ, e⟩ := H.hC L n (PeriodicLattice.levelDepth k (j + 1)) (PeriodicLattice.levelDepth k j) y x π
  rw [contourLeg, e] at hb
  exact orderedContour_ends_mem H hj hx σ hb
private theorem shiftAcross_mem (H : Hypotheses L n k) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1))
    {x : Vertex L n k j} (hx : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock c.source) :
    ((PeriodicLattice.shiftAcross c x : Vertex L n k j) : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.unitBlock c.target := by
  have Ht := ((H.hZ L H.hL k 1 (j + 1) H.hk (by omega) (by omega)).1 n H.hn).2.2.1
  have e := Ht.coe_shiftAcross c x hx
  have h := (Ht.bijOn c).mapsTo hx
  rw [e]
  exact h
private theorem crossingPath_ends_mem_of_pos (H : Hypotheses L n k) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) {x : Vertex L n k j}
    (hx : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock c.source) {b : Edge L n k j}
    (hb : b ∈ PeriodicLattice.crossingPath c x) :
    (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c ∧
      (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c := by
  have Ht := ((H.hZ L H.hL k 1 (j + 1) H.hk (by omega) (by omega)).1 n H.hn).2.2.1
  exact ⟨Ht.crossingPath_vertex_mem c hc x hx b.source (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩)),
    Ht.crossingPath_vertex_mem c hc x hx b.target (Or.inr (Or.inr ⟨b, hb, Or.inr rfl⟩))⟩
private theorem block_width_lt_half_side (H : Hypotheses L n k) {j : ℕ} (hj : j < k) :
    (((|(L : ℤ) ^ 1| : ℤ)) : ℝ) * meshAt L k j < PeriodicLattice.torusSide L n / 2 := by
  have hL13 : (13 : ℝ) ≤ L := by exact_mod_cast H.hL.2
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0 : (L : ℝ) ≠ 0 := by linarith
  have e : (((|(L : ℤ) ^ 1| : ℤ)) : ℝ) = L := by simp
  rw [e, meshAt, PeriodicLattice.torusSide]
  have h1 : (L : ℝ) * (L : ℝ) ^ ((j : ℤ) - (k : ℤ)) ≤ 1 := by
    have h : (L : ℝ) * (L : ℝ) ^ ((j : ℤ) - (k : ℤ)) = (L : ℝ) ^ ((j : ℤ) - (k : ℤ) + 1) := by
      rw [zpow_add_one₀ hL0]; ring
    rw [h]
    exact zpow_le_one_of_nonpos₀ hL1 (by omega)
  have h2 : (L : ℝ) ≤ (L : ℝ) ^ n := by
    calc (L : ℝ) = (L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (L : ℝ) ^ n := pow_le_pow_right₀ hL1 H.hn
  linarith
private theorem crossingPath_ends_mem (H : Hypotheses L n k) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1))
    {x : Vertex L n k j} (hx : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock c.source)
    {b : Edge L n k j} (hb : b ∈ PeriodicLattice.crossingPath c x) :
    (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c ∧
      (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c := by
  by_cases hc : c.IsPositivelyOriented
  · exact crossingPath_ends_mem_of_pos H hj hc hx hb
  have hr : c.opposite.IsPositivelyOriented := (isPositivelyOriented_or_opposite c).resolve_left hc
  have Ht := ((H.hZ L H.hL k 1 (j + 1) H.hk (by omega) (by omega)).1 n H.hn).2.2.1
  obtain ⟨x', hx'd⟩ : ∃ x' : Vertex L n k j, x' = PeriodicLattice.shiftAcross c x := ⟨_, rfl⟩
  have hx' : (x' : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock c.opposite.source := by
    rw [hx'd]; exact shiftAcross_mem H hj c hx
  have ht : (PeriodicLattice.shiftAcross c.opposite x' : Vertex L n k j) = x := by
    apply Subtype.ext
    have e₁ := Ht.coe_shiftAcross c.opposite x' hx'
    have e₂ := Ht.coe_shiftAcross c x hx
    rw [← hx'd] at e₂
    refine e₁.trans ?_
    change (x' : PeriodicLattice.FourTorus L n) +
      ((c.source : PeriodicLattice.FourTorus L n) - (c.target : PeriodicLattice.FourTorus L n)) = x
    rw [e₂]
    abel
  obtain ⟨μ, hμ⟩ := id hr
  have hd := (Ht.isAxialDisplacement c.opposite μ hμ x' hx').1
  rw [ht] at hd
  obtain ⟨-, -, e, -⟩ := (((H.hR L H.hL k).1 n H.hn).1 j hj.le).2 x' x μ ((L : ℤ) ^ 1) hd
    (block_width_lt_half_side H hj)
  have hb' : b ∈ PeriodicLattice.reversePath (PeriodicLattice.axialPath x' x) := by
    rw [← e, hx'd]; exact hb
  simp only [PeriodicLattice.reversePath, List.mem_reverse, List.mem_map] at hb'
  obtain ⟨r, hr', rfl⟩ := hb'
  have hcr : r ∈ PeriodicLattice.crossingPath c.opposite x' := by
    rw [PeriodicLattice.crossingPath, ht]; exact hr'
  have h := crossingPath_ends_mem_of_pos H hj hr hx' hcr
  exact ⟨Or.symm h.2, Or.symm h.1⟩
private theorem pathHolonomy_congr {j : ℕ} {V V' : Edge L n k j → Matrices.ComplexMatrix2}
    {Γ : List (Edge L n k j)} (h : ∀ b ∈ Γ, V b = V' b) :
    PeriodicLattice.pathHolonomy V Γ = PeriodicLattice.pathHolonomy V' Γ := by apply _root_.YangMills.Construction.Tower.PairContourIndependence.pathHolonomy_congr <;> assumption
private theorem contourMean_congr (H : Hypotheses L n k) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1))
    {V V' : Edge L n k j → Matrices.ComplexMatrix2}
    (h : ∀ b : Edge L n k j, (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c →
      (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c → V b = V' b) :
    contourMean V c = contourMean V' c := by
  simp only [contourMean]
  refine congrArg _ (finsum_mem_congr rfl fun x hx => Finset.sum_congr rfl fun π _ => ?_)
  have hx' := shiftAcross_mem H hj c hx
  simp only [contourHolonomy]
  rw [pathHolonomy_congr (V := V) (V' := V') (Γ := contourLeg c.source x π) fun b hb =>
      h b (Or.inl (contourLeg_ends_mem H hj hx π hb).1) (Or.inl (contourLeg_ends_mem H hj hx π hb).2),
    pathHolonomy_congr (V := V) (V' := V') (Γ := PeriodicLattice.crossingPath c x) fun b hb =>
      h b (crossingPath_ends_mem H hj c hx hb).1 (crossingPath_ends_mem H hj c hx hb).2,
    pathHolonomy_congr (V := V) (V' := V')
      (Γ := contourLeg c.target (PeriodicLattice.shiftAcross c x) π)
      fun b hb => h b (Or.inr (contourLeg_ends_mem H hj hx' π hb).1)
        (Or.inr (contourLeg_ends_mem H hj hx' π hb).2)]
private theorem meanRadius_congr (H : Hypotheses L n k) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1))
    {V V' : Edge L n k j → Matrices.ComplexMatrix2}
    (h : ∀ b : Edge L n k j, (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c →
      (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c → V b = V' b) :
    meanRadius V c = meanRadius V' c := by
  simp only [meanRadius, contourMean_congr H hj c h]
private theorem normalizedMean_congr (H : Hypotheses L n k) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1))
    {V V' : Edge L n k j → Matrices.ComplexMatrix2}
    (h : ∀ b : Edge L n k j, (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c →
      (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c → V b = V' b) :
    normalizedMean V c = normalizedMean V' c := by
  simp only [normalizedMean, meanRadius_congr H hj c h, contourMean_congr H hj c h]
private theorem complexMeanContourHolonomy_congr (H : Hypotheses L n k) {j : ℕ} (hj : j < k)
    {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    {V V' : Edge L n k j → Matrices.ComplexMatrix2}
    (h : ∀ b : Edge L n k j, (b.source : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y →
      (b.target : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y → V b = V' b) :
    PeriodicLattice.complexMeanContourHolonomy V y x =
      PeriodicLattice.complexMeanContourHolonomy V' y x := by
  have e : PeriodicLattice.contourHolonomies V y x = PeriodicLattice.contourHolonomies V' y x := by
    funext σ
    exact pathHolonomy_congr fun b hb =>
      h b (orderedContour_ends_mem H hj hx σ hb).1 (orderedContour_ends_mem H hj hx σ hb).2
  simp only [PeriodicLattice.complexMeanContourHolonomy, e]
private theorem logDirectionalDeriv_congr {α : Type}
    {φ φ' : (α → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2} {W W' : Matrices.ComplexMatrix2}
    {B B' : α → Matrices.ComplexMatrix2} (hW : W = W') (h : ∀ t : ℂ, φ (t • B) = φ' (t • B')) :
    logDirectionalDeriv ℂ φ W B = logDirectionalDeriv ℂ φ' W' B' := by
  have e : ∀ t : ℂ, φ (algebraMap ℂ ℂ t • B) = φ' (algebraMap ℂ ℂ t • B') := fun t => h _
  simp only [logDirectionalDeriv, e, hW]
private theorem expTwist_eq_of_eqOn {j : ℕ} {S : Edge L n k j → Prop}
    (hS : ∀ b, S b → S b.opposite) {V V' B B' : Edge L n k j → Matrices.ComplexMatrix2}
    (h : ∀ b, S b → V b = V' b ∧ B b = B' b) (t : ℂ) (b : Edge L n k j) (hb : S b) :
    PeriodicLattice.expTwist (t • B) V b = PeriodicLattice.expTwist (t • B') V' b := by
  have h₁ := h b hb
  have h₂ := h b.opposite (hS b hb)
  simp only [PeriodicLattice.expTwist, Pi.smul_apply, h₁.1, h₁.2, h₂.1, h₂.2]
private theorem contourLogDrift_congr (H : Hypotheses L n k) {j : ℕ} (hj : j < k) (y : Vertex L n k (j + 1))
    {V V' B B' : Edge L n k j → Matrices.ComplexMatrix2}
    (h : ∀ b : Edge L n k j, (b.source : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∧
      (b.target : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y →
        V b = V' b ∧ B b = B' b) :
    contourLogDrift V B y = contourLogDrift V' B' y := by
  simp only [contourLogDrift]
  refine congrArg _ (finsum_mem_congr rfl fun x hx => ?_)
  refine logDirectionalDeriv_congr
    (complexMeanContourHolonomy_congr H hj hx fun b e₁ e₂ => (h b ⟨e₁, e₂⟩).1) fun t => ?_
  exact complexMeanContourHolonomy_congr H hj hx fun b e₁ e₂ =>
    expTwist_eq_of_eqOn (S := fun b : Edge L n k j =>
      (b.source : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∧
        (b.target : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y)
      (fun _ hb => ⟨hb.2, hb.1⟩) h t b ⟨e₁, e₂⟩
private theorem meanCovariantStep_congr (H : Hypotheses L n k) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented)
    {V V' B B' : Edge L n k j → Matrices.ComplexMatrix2}
    (h : ∀ b : Edge L n k j, (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c ∧
      (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c → V b = V' b ∧ B b = B' b) :
    meanCovariantStep V B c = meanCovariantStep V' B' c := by
  have d₁ : contourLogDrift V B c.source = contourLogDrift V' B' c.source :=
    contourLogDrift_congr H hj c.source fun b e => h b ⟨Or.inl e.1, Or.inl e.2⟩
  have d₂ : contourLogDrift V B c.target = contourLogDrift V' B' c.target :=
    contourLogDrift_congr H hj c.target fun b e => h b ⟨Or.inr e.1, Or.inr e.2⟩
  have hA : normalizedMean V c = normalizedMean V' c :=
    normalizedMean_congr H hj c fun b e₁ e₂ => (h b ⟨e₁, e₂⟩).1
  have hD : logDirectionalDeriv ℂ (fun X => normalizedMean (PeriodicLattice.expTwist X V) c)
        (normalizedMean V c) B =
      logDirectionalDeriv ℂ (fun X => normalizedMean (PeriodicLattice.expTwist X V') c)
        (normalizedMean V' c) B' :=
    logDirectionalDeriv_congr hA fun t => normalizedMean_congr H hj c fun b e₁ e₂ =>
      expTwist_eq_of_eqOn (S := fun b : Edge L n k j =>
        (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c ∧
          (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c)
        (fun _ hb => ⟨hb.2, hb.1⟩) h t b ⟨e₁, e₂⟩
  simp only [meanCovariantStep, holLeftDifferential, covDiff, Pi.add_apply,
    extendOddly, if_pos hc]
  rw [hD, hA, d₁, d₂]
private theorem meanCovariantStep_of_not_pos {j : ℕ} (V B : Edge L n k j → Matrices.ComplexMatrix2)
    {c : Edge L n k (j + 1)} (hc : ¬c.IsPositivelyOriented) (hr : c.opposite.IsPositivelyOriented) :
    meanCovariantStep V B c = -meanCovariantStep V B c.opposite := by
  simp only [meanCovariantStep, holLeftDifferential, covDiff, Pi.add_apply,
    extendOddly, if_neg hc, if_pos hr, neg_add]
private theorem remainderGaugeField_congr {a a' : Edge L n k 0 → Matrices.ComplexMatrix2} {b : Edge L n k 0}
    (h : a b = a' b) (h' : a b.opposite = a' b.opposite) :
    remainderGaugeField a b = remainderGaugeField a' b := by
  simp only [remainderGaugeField, IdentityExpChart.expForm,
    PeriodicLattice.expTwist, scaledRemainderForm, Pi.smul_apply, h, h']
private theorem meanIterate_succ {j : ℕ} (hj : j < k) (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    meanIterate U (j + 1) =
      fieldOfPositiveValues fun c => normalizedMean (meanIterate U j) c.1 := by
  change levelField (quietPoint U) (j + 1) = _
  rw [levelField, dif_pos hj]
  congr 1
  funext c
  exact one_mul _
private theorem meanIterate_succ_congr {j : ℕ} (hj : j < k) {U U' : Edge L n k 0 → Matrices.ComplexMatrix2}
    (c : Edge L n k (j + 1))
    (h : ∀ c' : Edge L n k (j + 1), (c' = c ∨ c' = c.opposite) → c'.IsPositivelyOriented →
      normalizedMean (meanIterate U j) c' = normalizedMean (meanIterate U' j) c') :
    meanIterate U (j + 1) c = meanIterate U' (j + 1) c := by
  rw [meanIterate_succ hj U, meanIterate_succ hj U']
  simp only [fieldOfPositiveValues]
  by_cases hc : c.IsPositivelyOriented
  · simp only [dif_pos hc]
    exact h c (Or.inl rfl) hc
  · by_cases hr : c.opposite.IsPositivelyOriented
    · simp only [dif_neg hc, dif_pos hr]
      rw [h c.opposite (Or.inr rfl) hr]
    · simp only [dif_neg hc, dif_neg hr]
abbrev _root_.YangMills.SharedProofs.p35999 := @meanIterate_succ_congr
private theorem meanIterate_local (H : Hypotheses L n k) : ∀ j ≤ k, ∀ (b : Edge L n k j)
    (v v' : Edge L n k 0 → Matrices.ComplexMatrix2), EqOn v v' (linksUnder b) →
    meanIterate (remainderGaugeField v) j b = meanIterate (remainderGaugeField v') j b := by
  intro j
  induction j with
  | zero =>
    intro _ b v v' h
    exact remainderGaugeField_congr (h (mem_linksUnder_self H b)) (h (opposite_mem_linksUnder H b))
  | succ j ih =>
    intro hj c v v' h
    have hjk : j < k := by omega
    refine meanIterate_succ_congr hjk c fun c' hc' _ => ?_
    have h' : EqOn v v' (linksUnder c') := by
      rcases hc' with rfl | rfl
      · exact h
      · rw [linksUnder_opposite]; exact h
    exact normalizedMean_congr H hjk c' fun b e₁ e₂ =>
      ih hjk.le b v v' (h'.mono (linksUnder_subset H hjk c' e₁ e₂))
private theorem meanCovariant_local (H : Hypotheses L n k) : ∀ j ≤ k, ∀ (c : Edge L n k j)
    (v v' B B' : Edge L n k 0 → Matrices.ComplexMatrix2), EqOn v v' (linksUnder c) →
    EqOn B B' (linksUnder c) →
    meanCovariant (remainderGaugeField v) j B c =
      meanCovariant (remainderGaugeField v') j B' c := by
  intro j
  induction j with
  | zero =>
    intro _ c v v' B B' _ h
    exact h (mem_linksUnder_self H c)
  | succ j ih =>
    intro hj c v v' B B' h₁ h₂
    have hjk : j < k := by omega
    have pos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented → EqOn v v' (linksUnder c) →
        EqOn B B' (linksUnder c) →
        meanCovariantStep (meanIterate (remainderGaugeField v) j)
            (meanCovariant (remainderGaugeField v) j B) c =
          meanCovariantStep (meanIterate (remainderGaugeField v') j)
            (meanCovariant (remainderGaugeField v') j B') c := by
      intro c hc h₁ h₂
      refine meanCovariantStep_congr H hjk hc fun b e => ?_
      have sub := linksUnder_subset H hjk c e.1 e.2
      exact ⟨meanIterate_local H j hjk.le b v v' (h₁.mono sub),
        ih hjk.le b v v' B B' (h₁.mono sub) (h₂.mono sub)⟩
    change meanCovariantStep _ _ c = meanCovariantStep _ _ c
    by_cases hc : c.IsPositivelyOriented
    · exact pos c hc h₁ h₂
    · have hr := (isPositivelyOriented_or_opposite c).resolve_left hc
      rw [meanCovariantStep_of_not_pos _ _ hc hr, meanCovariantStep_of_not_pos _ _ hc hr,
        pos c.opposite hr (by rw [linksUnder_opposite]; exact h₁)
          (by rw [linksUnder_opposite]; exact h₂)]
private theorem composedCubeAverage_local (H : Hypotheses L n k) : ∀ j ≤ k, ∀ (y : Vertex L n k j)
    (v v' : Edge L n k 0 → Matrices.ComplexMatrix2) (l l' : Vertex L n k 0 → Matrices.ComplexMatrix2),
    (∀ x : Vertex L n k 0, (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock j y →
      l x = l' x) →
    EqOn v v' (PeriodicLattice.bondsInside (PeriodicLattice.refinedBlock j y)) →
    composedCubeAverage (quietPoint (remainderGaugeField v)) j l y =
      composedCubeAverage (quietPoint (remainderGaugeField v')) j l' y := by
  intro j
  induction j with
  | zero =>
    intro _ y v v' l l' h _
    exact h y (mem_refinedBlock_zero H (Nat.zero_le _) y)
  | succ j ih =>
    intro hj y v v' l l' h₁ h₂
    have hjk : j < k := by omega
    simp only [composedCubeAverage, adjointCubeAverage]
    refine congrArg _ (finsum_mem_congr rfl fun x hx => ?_)
    have sub := refinedBlock_subset_succ H hjk (y := y) (x := x) hx
    rw [ih hjk.le x v v' l l' (fun z hz => h₁ z (sub hz)) fun b hb => h₂ ⟨sub hb.1, sub hb.2⟩]
    rw [complexMeanContourHolonomy_congr H hjk hx fun b e₁ e₂ =>
      meanIterate_local H j hjk.le b v v' fun w hw => by
        have sub' : PeriodicLattice.refinedBlock j b.source ∪ PeriodicLattice.refinedBlock j b.target ⊆
            PeriodicLattice.refinedBlock (j + 1) y :=
          union_subset (refinedBlock_subset_succ H hjk e₁) (refinedBlock_subset_succ H hjk e₂)
        exact h₂ ⟨sub' hw.1, sub' hw.2⟩]
theorem claim_of_geometry (hZ : BlockPathContourPivotStatement)
    (hC : AxisOrderLegsAreContours)
    (hR : AxisPathReversal.MainStatement) : Claim := by
  intro L hL
  refine ⟨1, one_pos, fun n k hn hk => ?_⟩
  have H : Hypotheses L n k := ⟨hZ, hC, hR, hL, hn, hk⟩
  exact ⟨fun c v _ v' _ B _ B' _ h₁ h₂ => meanCovariant_local H k le_rfl c v v' B B' h₁ h₂,
    fun y v _ v' _ l l' _ _ h₁ h₂ => composedCubeAverage_local H k le_rfl y v v' l l' h₁ h₂,
    fun j hj c v _ v' _ h => meanRadius_congr H hj c fun b e₁ e₂ =>
      meanIterate_local H j hj.le b v v' (h.mono (linksUnder_subset H hj c e₁ e₂))⟩
end YangMills.Construction.RunningCouplingSlope.MeanExpansionsLocal
end
