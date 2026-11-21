import YangMills.Construction.RunningCouplingSlope.NoiseAndStepKernelsAtARadius
import YangMills.Construction.RunningCouplingSlope.PlainExpansionsDetermineTheBlocksProof
import YangMills.Construction.RunningCouplingSlope.PlainIteratesAreNearOne
import YangMills.Construction.RunningCouplingSlope.PlainStepKernelsReadTheDoubleBlock
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.KernelLocality
open Tower
variable {L n k : ℕ}
private abbrev finerEdges {j : ℕ} (c : Edge L n k j) : Set (Edge L n k 0) :=
  PeriodicLattice.bondsInside
    (PeriodicLattice.refinedBlock j c.source ∪ PeriodicLattice.refinedBlock j c.target)
private abbrev doubleBlock {j : ℕ} (c : Edge L n k (j + 1)) : Set (PeriodicLattice.FourTorus L n) :=
  PeriodicLattice.unitBlock c.source ∪ PeriodicLattice.unitBlock c.target
private structure Hyps (L n k : ℕ) : Prop where
  hZ : BlockPathContourPivotStatement
  hC : AxisOrderLegsAreContours
  hR : AxisPathReversal.MainStatement
  hL : Conventions.IsAdmissibleBlockingFactor L
  hn : 0 < n
  hk : 1 ≤ k
private theorem positive_or_opposite {j : ℕ} (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem finerEdges_opposite {j : ℕ} (c : Edge L n k j) :
    finerEdges c.opposite = finerEdges c := by apply _root_.YangMills.DeltaSharedProofs.p502040 <;> assumption
private theorem mem_refinedBlock_zero (G : Hyps L n k) {j : ℕ} (hj : j ≤ k) (y : Vertex L n k j) :
    (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock 0 y := by
  have H := ((G.hZ L G.hL k 0 j G.hk (Nat.zero_le _) hj).1 n G.hn).1.eq_image y
  rw [H]
  have e : ∀ μ : Fin 4, PeriodicLattice.pointOnAxis L n μ 0 = 0 := fun μ => by
    rw [PeriodicLattice.pointOnAxis,
      show ((0 : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) = 0 from rfl, Pi.single_zero]
  exact ⟨0, by simp [offsetBox], by simp [offsetPoint, e]⟩
private theorem self_mem_finerEdges (G : Hyps L n k) (b : Edge L n k 0) : b ∈ finerEdges b :=
  ⟨Or.inl (mem_refinedBlock_zero G (Nat.zero_le _) b.source),
    Or.inr (mem_refinedBlock_zero G (Nat.zero_le _) b.target)⟩
private theorem opposite_mem_finerEdges (G : Hyps L n k) (b : Edge L n k 0) :
    b.opposite ∈ finerEdges b :=
  ⟨Or.inr (mem_refinedBlock_zero G (Nat.zero_le _) b.target),
    Or.inl (mem_refinedBlock_zero G (Nat.zero_le _) b.source)⟩
private theorem refinedBlock_subset (G : Hyps L n k) {j : ℕ} (hj : j < k)
    {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
    (hx : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y) :
    PeriodicLattice.refinedBlock j x ⊆ PeriodicLattice.refinedBlock (j + 1) y := by
  intro z hz
  have H := ((G.hZ L G.hL k (j + 1) (j + 1) G.hk le_rfl (by omega)).1 n G.hn).1.eq_biUnion_lower
    (by omega) y
  rw [H]
  exact mem_iUnion₂.2 ⟨x, hx, hz⟩
private theorem finerEdges_subset (G : Hyps L n k) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1))
    {b : Edge L n k j} (e₁ : (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c)
    (e₂ : (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c) :
    finerEdges b ⊆ finerEdges c := by
  have sub : ∀ x : Vertex L n k j, (x : PeriodicLattice.FourTorus L n) ∈ doubleBlock c →
      PeriodicLattice.refinedBlock j x ⊆
        PeriodicLattice.refinedBlock (j + 1) c.source ∪ PeriodicLattice.refinedBlock (j + 1) c.target :=
    fun x hx => hx.elim (fun h => (refinedBlock_subset G hj h).trans subset_union_left)
      fun h => (refinedBlock_subset G hj h).trans subset_union_right
  have sub' : PeriodicLattice.refinedBlock j b.source ∪ PeriodicLattice.refinedBlock j b.target ⊆
      PeriodicLattice.refinedBlock (j + 1) c.source ∪ PeriodicLattice.refinedBlock (j + 1) c.target :=
    union_subset (sub _ e₁) (sub _ e₂)
  exact fun w hw => ⟨sub' hw.1, sub' hw.2⟩
private theorem orderedContour_ends (G : Hyps L n k) {j : ℕ} (hj : j < k)
    {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    (σ : PeriodicLattice.AxisOrdering y x) {b : Edge L n k j}
    (hb : b ∈ PeriodicLattice.orderedContour y x σ) :
    (b.source : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∧
      (b.target : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y := by
  obtain ⟨Hb, -, -, -, -, Hc⟩ := (G.hZ L G.hL k 1 (j + 1) G.hk (by omega) (by omega)).1 n G.hn
  have hx' : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock 1 y := hx
  rw [Hb.eq_image y] at hx'
  obtain ⟨ν, hν, hxν⟩ := hx'
  obtain ⟨-, -, -, -, hz⟩ := ((Hc (by omega)).1.contours y ν hν x hxν.symm).2 _ ⟨σ, rfl⟩
  exact ⟨hz b.source (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩)),
    hz b.target (Or.inr (Or.inr ⟨b, hb, Or.inr rfl⟩))⟩
private theorem contourLeg_ends (G : Hyps L n k) {j : ℕ} (hj : j < k)
    {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    (π : Equiv.Perm (Fin 4)) {b : Edge L n k j} (hb : b ∈ contourLeg y x π) :
    (b.source : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∧
      (b.target : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y := by
  obtain ⟨σ, e⟩ := G.hC L n (PeriodicLattice.levelDepth k (j + 1))
    (PeriodicLattice.levelDepth k j) y x π
  rw [contourLeg, e] at hb
  exact orderedContour_ends G hj hx σ hb
private theorem shiftAcross_mem (G : Hyps L n k) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1))
    {x : Vertex L n k j}
    (hx : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock c.source) :
    ((PeriodicLattice.shiftAcross c x : Vertex L n k j) : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.unitBlock c.target := by
  have Ht := ((G.hZ L G.hL k 1 (j + 1) G.hk (by omega) (by omega)).1 n G.hn).2.2.1
  have e := Ht.coe_shiftAcross c x hx
  have h := (Ht.bijOn c).mapsTo hx
  rw [e]
  exact h
private theorem crossingPath_ends_of_positive (G : Hyps L n k) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) {x : Vertex L n k j}
    (hx : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock c.source)
    {b : Edge L n k j} (hb : b ∈ PeriodicLattice.crossingPath c x) :
    (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c ∧
      (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c := by
  have Ht := ((G.hZ L G.hL k 1 (j + 1) G.hk (by omega) (by omega)).1 n G.hn).2.2.1
  exact ⟨Ht.crossingPath_vertex_mem c hc x hx b.source (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩)),
    Ht.crossingPath_vertex_mem c hc x hx b.target (Or.inr (Or.inr ⟨b, hb, Or.inr rfl⟩))⟩
private theorem crossingPath_fits (G : Hyps L n k) {j : ℕ} (hj : j < k) :
    (((|(L : ℤ) ^ 1| : ℤ)) : ℝ) * meshAt L k j < PeriodicLattice.torusSide L n / 2 := by
  have hL13 : (13 : ℝ) ≤ L := by exact_mod_cast G.hL.2
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
      _ ≤ (L : ℝ) ^ n := pow_le_pow_right₀ hL1 G.hn
  linarith
private theorem crossingPath_ends (G : Hyps L n k) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1))
    {x : Vertex L n k j}
    (hx : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock c.source)
    {b : Edge L n k j} (hb : b ∈ PeriodicLattice.crossingPath c x) :
    (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c ∧
      (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c := by
  by_cases hc : c.IsPositivelyOriented
  · exact crossingPath_ends_of_positive G hj hc hx hb
  have hr : c.opposite.IsPositivelyOriented := (positive_or_opposite c).resolve_left hc
  have Ht := ((G.hZ L G.hL k 1 (j + 1) G.hk (by omega) (by omega)).1 n G.hn).2.2.1
  obtain ⟨x', hx'd⟩ : ∃ x' : Vertex L n k j, x' = PeriodicLattice.shiftAcross c x := ⟨_, rfl⟩
  have hx' : (x' : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock c.opposite.source := by
    rw [hx'd]; exact shiftAcross_mem G hj c hx
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
  obtain ⟨-, -, e, -⟩ := (((G.hR L G.hL k).1 n G.hn).1 j hj.le).2 x' x μ ((L : ℤ) ^ 1) hd
    (crossingPath_fits G hj)
  have hb' : b ∈ PeriodicLattice.reversePath (PeriodicLattice.axialPath x' x) := by
    rw [← e, hx'd]; exact hb
  simp only [PeriodicLattice.reversePath, List.mem_reverse, List.mem_map] at hb'
  obtain ⟨r, hr', rfl⟩ := hb'
  have hcr : r ∈ PeriodicLattice.crossingPath c.opposite x' := by
    rw [PeriodicLattice.crossingPath, ht]; exact hr'
  have h := crossingPath_ends_of_positive G hj hr hx' hcr
  exact ⟨Or.symm h.2, Or.symm h.1⟩
private theorem pathHolonomy_congr {j : ℕ} {V V' : Edge L n k j → Matrices.ComplexMatrix2}
    {Γ : List (Edge L n k j)} (h : ∀ b ∈ Γ, V b = V' b) :
    PeriodicLattice.pathHolonomy V Γ = PeriodicLattice.pathHolonomy V' Γ := by apply _root_.YangMills.Construction.Tower.PairContourIndependence.pathHolonomy_congr <;> assumption
private theorem contourMean_congr (G : Hyps L n k) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1))
    {V V' : Edge L n k j → Matrices.ComplexMatrix2}
    (h : ∀ b : Edge L n k j, (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c →
      (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c → V b = V' b) :
    contourMean V c = contourMean V' c := by
  simp only [contourMean]
  refine congrArg _ (finsum_mem_congr rfl fun x hx => Finset.sum_congr rfl fun π _ => ?_)
  have hx' := shiftAcross_mem G hj c hx
  simp only [contourHolonomy]
  rw [pathHolonomy_congr (V := V) (V' := V') (Γ := contourLeg c.source x π) fun b hb =>
      h b (Or.inl (contourLeg_ends G hj hx π hb).1) (Or.inl (contourLeg_ends G hj hx π hb).2),
    pathHolonomy_congr (V := V) (V' := V') (Γ := PeriodicLattice.crossingPath c x) fun b hb =>
      h b (crossingPath_ends G hj c hx hb).1 (crossingPath_ends G hj c hx hb).2,
    pathHolonomy_congr (V := V) (V' := V')
      (Γ := contourLeg c.target (PeriodicLattice.shiftAcross c x) π)
      fun b hb => h b (Or.inr (contourLeg_ends G hj hx' π hb).1)
        (Or.inr (contourLeg_ends G hj hx' π hb).2)]
private theorem meanRadius_congr (G : Hyps L n k) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1))
    {V V' : Edge L n k j → Matrices.ComplexMatrix2}
    (h : ∀ b : Edge L n k j, (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c →
      (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c → V b = V' b) :
    meanRadius V c = meanRadius V' c := by
  simp only [meanRadius, contourMean_congr G hj c h]
private theorem normalizedMean_congr (G : Hyps L n k) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1))
    {V V' : Edge L n k j → Matrices.ComplexMatrix2}
    (h : ∀ b : Edge L n k j, (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c →
      (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c → V b = V' b) :
    normalizedMean V c = normalizedMean V' c := by
  simp only [normalizedMean, meanRadius_congr G hj c h, contourMean_congr G hj c h]
private theorem complexContourMean_congr (G : Hyps L n k) {j : ℕ} (hj : j < k)
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
      h b (orderedContour_ends G hj hx σ hb).1 (orderedContour_ends G hj hx σ hb).2
  simp only [PeriodicLattice.complexMeanContourHolonomy, e]
private theorem logDirectionalDeriv_congr {α : Type}
    {φ φ' : (α → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    {W W' : Matrices.ComplexMatrix2} {B B' : α → Matrices.ComplexMatrix2} (hW : W = W')
    (h : ∀ t : ℂ, φ (t • B) = φ' (t • B')) :
    logDirectionalDeriv ℂ φ W B = logDirectionalDeriv ℂ φ' W' B' := by
  have e : ∀ t : ℂ, φ (algebraMap ℂ ℂ t • B) = φ' (algebraMap ℂ ℂ t • B') := fun t => h _
  simp only [logDirectionalDeriv, e, hW]
private theorem expTwist_agree {j : ℕ} {S : Edge L n k j → Prop}
    (hS : ∀ b, S b → S b.opposite) {V V' B B' : Edge L n k j → Matrices.ComplexMatrix2}
    (h : ∀ b, S b → V b = V' b ∧ B b = B' b) (t : ℂ) (b : Edge L n k j) (hb : S b) :
    PeriodicLattice.expTwist (t • B) V b = PeriodicLattice.expTwist (t • B') V' b := by
  have h₁ := h b hb
  have h₂ := h b.opposite (hS b hb)
  simp only [PeriodicLattice.expTwist, Pi.smul_apply, h₁.1, h₁.2, h₂.1, h₂.2]
private theorem contourLogDrift_congr (G : Hyps L n k) {j : ℕ} (hj : j < k) (y : Vertex L n k (j + 1))
    {V V' B B' : Edge L n k j → Matrices.ComplexMatrix2}
    (h : ∀ b : Edge L n k j,
      (b.source : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∧
      (b.target : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y →
        V b = V' b ∧ B b = B' b) :
    contourLogDrift V B y = contourLogDrift V' B' y := by
  simp only [contourLogDrift]
  refine congrArg _ (finsum_mem_congr rfl fun x hx => ?_)
  refine logDirectionalDeriv_congr
    (complexContourMean_congr G hj hx fun b e₁ e₂ => (h b ⟨e₁, e₂⟩).1) fun t => ?_
  exact complexContourMean_congr G hj hx fun b e₁ e₂ =>
    expTwist_agree (S := fun b : Edge L n k j =>
      (b.source : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∧
        (b.target : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y)
      (fun _ hb => ⟨hb.2, hb.1⟩) h t b ⟨e₁, e₂⟩
private theorem meanCovariantStep_congr (G : Hyps L n k) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented)
    {V V' B B' : Edge L n k j → Matrices.ComplexMatrix2}
    (h : ∀ b : Edge L n k j, (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c ∧
      (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c → V b = V' b ∧ B b = B' b) :
    meanCovariantStep V B c = meanCovariantStep V' B' c := by
  have d₁ : contourLogDrift V B c.source = contourLogDrift V' B' c.source :=
    contourLogDrift_congr G hj c.source fun b e => h b ⟨Or.inl e.1, Or.inl e.2⟩
  have d₂ : contourLogDrift V B c.target = contourLogDrift V' B' c.target :=
    contourLogDrift_congr G hj c.target fun b e => h b ⟨Or.inr e.1, Or.inr e.2⟩
  have hA : normalizedMean V c = normalizedMean V' c :=
    normalizedMean_congr G hj c fun b e₁ e₂ => (h b ⟨e₁, e₂⟩).1
  have hD : logDirectionalDeriv ℂ (fun X => normalizedMean (PeriodicLattice.expTwist X V) c)
        (normalizedMean V c) B =
      logDirectionalDeriv ℂ (fun X => normalizedMean (PeriodicLattice.expTwist X V') c)
        (normalizedMean V' c) B' :=
    logDirectionalDeriv_congr hA fun t => normalizedMean_congr G hj c fun b e₁ e₂ =>
      expTwist_agree (S := fun b : Edge L n k j =>
        (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c ∧
          (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c)
        (fun _ hb => ⟨hb.2, hb.1⟩) h t b ⟨e₁, e₂⟩
  simp only [meanCovariantStep, holLeftDifferential, covDiff, Pi.add_apply,
    extendOddly, if_pos hc]
  rw [hD, hA, d₁, d₂]
private theorem remainderGaugeField_congr {a a' : Edge L n k 0 → Matrices.ComplexMatrix2}
    {b : Edge L n k 0} (h : a b = a' b) (h' : a b.opposite = a' b.opposite) :
    remainderGaugeField a b = remainderGaugeField a' b := by
  simp only [remainderGaugeField, IdentityExpChart.expForm,
    PeriodicLattice.expTwist, scaledRemainderForm, Pi.smul_apply, h, h']
private theorem meanIterate_step {j : ℕ} (hj : j < k) {U U' : Edge L n k 0 → Matrices.ComplexMatrix2}
    (c : Edge L n k (j + 1))
    (h : ∀ c' : Edge L n k (j + 1), (c' = c ∨ c' = c.opposite) → c'.IsPositivelyOriented →
      normalizedMean (meanIterate U j) c' = normalizedMean (meanIterate U' j) c') :
    meanIterate U (j + 1) c = meanIterate U' (j + 1) c := by apply _root_.YangMills.SharedProofs.p35999 <;> assumption
private theorem meanIterate_local (G : Hyps L n k) : ∀ j ≤ k, ∀ (b : Edge L n k j)
    (v v' : Edge L n k 0 → Matrices.ComplexMatrix2), EqOn v v' (finerEdges b) →
    meanIterate (remainderGaugeField v) j b = meanIterate (remainderGaugeField v') j b := by
  intro j
  induction j with
  | zero =>
    intro _ b v v' h
    exact remainderGaugeField_congr (h (self_mem_finerEdges G b)) (h (opposite_mem_finerEdges G b))
  | succ j ih =>
    intro hj c v v' h
    have hjk : j < k := by omega
    refine meanIterate_step hjk c fun c' hc' _ => ?_
    have h' : EqOn v v' (finerEdges c') := by
      rcases hc' with rfl | rfl
      · exact h
      · rw [finerEdges_opposite]; exact h
    exact normalizedMean_congr G hjk c' fun b e₁ e₂ =>
      ih hjk.le b v v' (h'.mono (finerEdges_subset G hjk c' e₁ e₂))
private theorem self_mem_refinedBlock (G : Hyps L n k) {j : ℕ} (hj : j ≤ k) (y : Vertex L n k j) :
    (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock j y := by
  have H := ((G.hZ L G.hL k j j G.hk le_rfl hj).1 n G.hn).1.eq_image y
  rw [H]
  have e : ∀ μ : Fin 4, PeriodicLattice.pointOnAxis L n μ 0 = 0 := fun μ => by
    rw [PeriodicLattice.pointOnAxis,
      show ((0 : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) = 0 from rfl, Pi.single_zero]
  have hL1 : (1 : ℝ) ≤ L := by
    have : (13 : ℝ) ≤ L := by exact_mod_cast G.hL.2
    linarith
  refine ⟨0, fun μ => ?_, by simp [offsetPoint, e]⟩
  have := one_le_pow₀ (n := j) hL1
  simp only [Pi.zero_apply, Int.cast_zero, abs_zero]
  linarith
private theorem cubesOfEdge_subset (G : Hyps L n k) {j : ℕ} (hj : j < k) (c : Edge L n k (j + 1))
    {b : Edge L n k j} (e₁ : (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock c)
    (e₂ : (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock c) :
    cubesOfEdge b ⊆ cubesOfEdge c := by
  have sub : ∀ x : Vertex L n k j, (x : PeriodicLattice.FourTorus L n) ∈ doubleBlock c →
      PeriodicLattice.refinedBlock j x ⊆ cubesOfEdge c :=
    fun x hx => hx.elim (fun h => (refinedBlock_subset G hj h).trans subset_union_left)
      fun h => (refinedBlock_subset G hj h).trans subset_union_right
  exact union_subset (sub _ e₁) (sub _ e₂)
private theorem ofPauliCoeffs_off {j : ℕ} (c : Fin 3 × PositiveEdge L n k j → ℂ) {b : Edge L n k j}
    (h₁ : ∀ (hb : b.IsPositivelyOriented) (a : Fin 3), c (a, ⟨b, hb⟩) = 0)
    (h₂ : ∀ (hb : b.opposite.IsPositivelyOriented) (a : Fin 3), c (a, ⟨b.opposite, hb⟩) = 0) :
    (edgePauliCoordinates L n k j).ofCoeffs c b = 0 := by
  classical
  have zero : ∀ {b : Edge L n k j} (hb : b.IsPositivelyOriented),
      (∀ a : Fin 3, c (a, ⟨b, hb⟩) = 0) → ofPauliCoeffs c ⟨b, hb⟩ = 0 := fun hb h =>
    Finset.sum_eq_zero fun a _ => by rw [h a, zero_smul]
  have e : (edgePauliCoordinates L n k j).ofCoeffs c b =
      extendOddly (fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0) b :=
    rfl
  rw [e]
  unfold extendOddly
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos hb]
    beta_reduce
    rw [dif_pos hb]
    exact zero hb (h₁ hb)
  · rw [if_neg hb]
    beta_reduce
    by_cases hr : b.opposite.IsPositivelyOriented
    · rw [dif_pos hr, zero hr (h₂ hr), neg_zero]
    · rw [dif_neg hr, neg_zero]
private theorem unitCoeffForm_off {j : ℕ} (ι : Fin 3 × PositiveEdge L n k j) {b : Edge L n k j}
    (h₁ : b ≠ ι.2.1) (h₂ : b.opposite ≠ ι.2.1) : unitCoeffForm L n k j ι b = 0 := by
  classical
  refine ofPauliCoeffs_off _ (fun hb a => Pi.single_eq_of_ne (fun e => h₁ ?_) _)
    (fun hb a => Pi.single_eq_of_ne (fun e => h₂ ?_) _)
  · exact congrArg (fun p : Fin 3 × PositiveEdge L n k j => p.2.1) e
  · exact congrArg (fun p : Fin 3 × PositiveEdge L n k j => p.2.1) e
private theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem stepKernelLocality (hZ : BlockPathContourPivotStatement)
    (hC : AxisOrderLegsAreContours)
    (hR : AxisPathReversal.MainStatement)
    (hK : StepAndNoiseKernelsNearIdentity)
    (hN : MeanIteratesNearIdentity.Claim) : StepKernelLocality := by
  intro L hL
  obtain ⟨r, hr, HK⟩ := hK L hL
  obtain ⟨ρ, hρ, HN⟩ := hN L hL r hr
  refine ⟨ρ, hρ, fun n k hn hk => ?_⟩
  have G : Hyps L n k := ⟨hZ, hC, hR, hL, hn, hk⟩
  refine ⟨fun j hj y => self_mem_refinedBlock G hj y, fun j hj ι' ι v hv => ?_⟩
  obtain ⟨h0, he⟩ := (HK n k hn hk).1 _ (HN n k hn hk v hv) j hj
  have hc : ι'.2.1.IsPositivelyOriented := ι'.2.2
  refine ⟨fun hne => ?_, fun v' hv' h => ?_⟩
  · by_contra hsub
    refine hne ?_
    have hfar : ∀ b : Edge L n k j,
        (b.source : PeriodicLattice.FourTorus L n) ∈ doubleBlock ι'.2.1 ∧
        (b.target : PeriodicLattice.FourTorus L n) ∈ doubleBlock ι'.2.1 →
          b ≠ ι.2.1 ∧ b.opposite ≠ ι.2.1 := by
      intro b e
      refine ⟨fun eb => hsub ?_, fun eb => hsub ?_⟩
      · rw [← eb]
        exact cubesOfEdge_subset G hj ι'.2.1 e.1 e.2
      · rw [← eb]
        exact cubesOfEdge_subset G hj ι'.2.1 e.2 e.1
    have hs := meanCovariantStep_congr G hj hc (V := meanIterate (remainderGaugeField v) j)
      (V' := meanIterate (remainderGaugeField v) j)
      (B := unitCoeffForm L n k j ι) (B' := 0)
      fun b e => ⟨rfl, unitCoeffForm_off ι (hfar b e).1 (hfar b e).2⟩
    rw [he, Pi.smul_apply, hs, h0, Pi.zero_apply, smul_zero, pauliCoeff_zero]
  · obtain ⟨h0', he'⟩ := (HK n k hn hk).1 _ (HN n k hn hk v' hv') j hj
    have hs := meanCovariantStep_congr G hj hc (V := meanIterate (remainderGaugeField v) j)
      (V' := meanIterate (remainderGaugeField v') j)
      (B := unitCoeffForm L n k j ι) (B' := unitCoeffForm L n k j ι)
      fun b e => ⟨meanIterate_local G j hj.le b v v'
        (EqOn.mono (finerEdges_subset G hj ι'.2.1 e.1 e.2) h), rfl⟩
    rw [he, he', Pi.smul_apply, Pi.smul_apply, hs]
end YangMills.Construction.RunningCouplingSlope.KernelLocality
end
