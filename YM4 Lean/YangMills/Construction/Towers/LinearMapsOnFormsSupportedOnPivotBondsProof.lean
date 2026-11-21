import YangMills.Construction.Lattice.BareBaseSitesOfTheSchemesProof
import YangMills.Construction.Lattice.DoubleBlockStraightPathCorridorAndPivotBond
import YangMills.Construction.Lattice.PropertiesOfTheTwoSchemes
import YangMills.Construction.Lattice.QuotientLatticesAndNeighbours
import YangMills.Construction.Towers.AtMostOneStraightPath
import YangMills.Construction.Towers.BlocksOfATower
import YangMills.Construction.Towers.LinearMapsOnFormsSupportedOnPivotBonds
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.PivotFormsProof
open YangMills.Construction.PeriodicLattice (FourTorus unitBlock sitesInBlock bondCorridor crossingPath
  levelDepth pivot unitStep shiftAcross)
theorem coe_toSublattice {L n : ℕ} (hL : 0 < L) {a b : ℤ} (h : a ≤ b) (y : PeriodicLattice.Site L n a) :
    ((y.toSublattice b : PeriodicLattice.Site L n b) : FourTorus L n) = y := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
theorem add_add_nsmul_eq_succ_nsmul {X : Type*} [AddCommGroup X] (x s : X) (i : ℕ) :
    x + s + i • s = x + (i + 1) • s := by
  rw [succ_nsmul]
  abel
theorem bondFormSumAlong_forwardFlow {L n : ℕ} {a : ℤ}
    (B : PeriodicLattice.Bond L n a → Matrices.ComplexMatrix2) (μ : Fin 4)
    (m : ℕ) (x : PeriodicLattice.Site L n a) :
    PeriodicLattice.bondFormSumAlong B (PeriodicLattice.forwardAxisPath x μ m) =
      ∑ i ∈ Finset.range m, B (PeriodicLattice.Bond.forwardFrom (x + i • unitStep L n a μ) μ) := by
  induction m generalizing x with
  | zero => simp [PeriodicLattice.bondFormSumAlong, PeriodicLattice.forwardAxisPath]
  | succ m ih =>
    have h := ih (x + unitStep L n a μ)
    simp only [add_add_nsmul_eq_succ_nsmul] at h
    rw [Finset.sum_range_succ', ← h]
    simp [PeriodicLattice.bondFormSumAlong, PeriodicLattice.forwardAxisPath, add_comm]
theorem forwardFrom_mem_forwardFlow {L n : ℕ} {a : ℤ} (μ : Fin 4) (m i : ℕ) (hi : i < m)
    (x : PeriodicLattice.Site L n a) :
    PeriodicLattice.Bond.forwardFrom (x + i • unitStep L n a μ) μ ∈ PeriodicLattice.forwardAxisPath x μ m := by
  induction m generalizing x i with
  | zero => omega
  | succ m ih =>
    cases i with
    | zero => simp [PeriodicLattice.forwardAxisPath]
    | succ i =>
      have h := ih i (by omega) (x + unitStep L n a μ)
      rw [add_add_nsmul_eq_succ_nsmul] at h
      simp only [PeriodicLattice.forwardAxisPath]
      exact List.mem_cons_of_mem _ h
theorem not_both_orientations (hLat : QuotientLattices.TorusAndSpaceLatticeProperties) {L n k j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hjk : j ≤ k) (c : Edge L n k j) (μ : Fin 4)
    (hμ : c.target - c.source = unitStep L n (levelDepth k j) μ) (ν : Fin 4)
    (hν : c.source - c.target = unitStep L n (levelDepth k j) ν) : False := by
  have h9 := (hLat L hL n j k hn hjk).2.2.2.2.2.1
  have hμ' : (c.target : FourTorus L n) - (c.source : FourTorus L n) =
      ((1 : ℤˣ) : ℤ) • QuotientLattices.torusAxisSteps L n k j μ := by
    simpa [QuotientLattices.torusAxisSteps] using congrArg Subtype.val hμ
  have hν' : (c.source : FourTorus L n) - (c.target : FourTorus L n) =
      ((1 : ℤˣ) : ℤ) • QuotientLattices.torusAxisSteps L n k j ν := by
    simpa [QuotientLattices.torusAxisSteps] using congrArg Subtype.val hν
  rcases ((h9.2.2 c.source c.source.2 c.target c.target.2).2 1 μ hμ').2 with ⟨-, h⟩ | ⟨-, h⟩
  · exact h ⟨ν, hν'⟩
  · exact h ⟨μ, hμ'⟩
theorem pivotFormsStatement_holds (hSch : PeriodicLattice.AveragingSchemeProperties)
    (hPiv : PeriodicLattice.DoubleBlockGeometryClaim)
    (hZ : BlockStructure) (hStr : AxisPathUniqueness.AxisPathsUnique)
    (hLat : QuotientLattices.TorusAndSpaceLatticeProperties) : LinearizationFacts.pivotFormsStatement := by
  intro L hL n k j hn hjk B hB hs
  have hL0 : 0 < L := by have := hL.2; omega
  have hdata : Averaging.LayerwiseParameters 4 2 L k n Matrices.ComplexMatrix2.specialUnitary
      (PeriodicLattice.torusSide L n) :=
    ⟨rfl, rfl, rfl, hL.1, hL.2, by omega, hn, rfl⟩
  have hcor := ((hPiv L k n hdata).2 j hjk).1
  obtain ⟨hDisp, hSort, hTrans, -⟩ := (hZ L k (j + 1) hL (by omega) (by omega) (by omega)).1 n hn
  have huniq : ∀ x : Vertex L n k j, ∃! y : Vertex L n k (j + 1), (x : FourTorus L n) ∈ unitBlock y :=
    hSort.2.1
  obtain ⟨t, ht⟩ := hL.1
  have hhalf : PeriodicLattice.centreToFaceSteps L = (t : ℤ) := by
    unfold PeriodicLattice.centreToFaceSteps
    omega
  have htoNat : (PeriodicLattice.centreToFaceSteps L).toNat = t := by
    rw [hhalf]
    simp
  have hle : levelDepth k (j + 1) ≤ levelDepth k j := by
    simp only [levelDepth]
    push_cast
    omega
  have hpos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      (pivot c : Edge L n k j) ∈ (bondCorridor c : Set (Edge L n k j)) ∧
        Disjoint (unitBlock c.source) (unitBlock c.target) := by
    rintro c ⟨μ, hμ⟩
    have hc := hcor c μ hμ
    refine ⟨?_, hc.blocks_disjoint⟩
    rw [hc.pivot_eq, htoNat]
    exact (hc.mem_bondCorridor_iff t (by omega)).2 hhalf.symm
  have hB' : PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra B := hB
  have hinsidePos : ∀ (y : Vertex L n k (j + 1)) (b : Edge L n k j), b.IsPositivelyOriented →
      (b.source : FourTorus L n) ∈ unitBlock y → (b.target : FourTorus L n) ∈ unitBlock y → B b = 0 := by
    intro y b hb h1 h2
    refine hs b hb fun c hc heq => ?_
    obtain ⟨⟨h3, h4⟩, hd⟩ := hpos c hc
    rw [← heq] at h3 h4
    have e1 : c.source = y := (huniq b.source).unique h3 h1
    have e2 : c.target = y := (huniq b.target).unique h4 h2
    rw [e1, e2] at hd
    exact Set.disjoint_left.1 hd h1 h1
  have hinside : ∀ (y : Vertex L n k (j + 1)) (b : Edge L n k j),
      (b.source : FourTorus L n) ∈ unitBlock y → (b.target : FourTorus L n) ∈ unitBlock y → B b = 0 := by
    intro y b h1 h2
    obtain ⟨μ, h | h⟩ := b.isNeighbour
    · exact hinsidePos y b ⟨μ, h⟩ h1 h2
    · have h0 := hinsidePos y b.opposite
        ⟨μ, by show b.source - b.target = _; rw [← neg_sub, h, neg_neg]⟩ h2 h1
      have h3 := hB'.2 b
      rw [h0] at h3
      exact neg_eq_zero.1 h3.symm
  have hcontour : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      x ∈ sitesInBlock (levelDepth k j) y → PeriodicLattice.contourFormAverage B y x = 0 := by
    intro y x hx
    have hp := ((hSch L hL n k j hn hjk .centred).1 y x hx).1
    have hz : ∀ σ, PeriodicLattice.bondFormSumAlong B (PeriodicLattice.orderedContour y x σ) = 0 := by
      intro σ
      refine List.sum_eq_zero fun v hv => ?_
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hv
      obtain ⟨h1, h2⟩ := (hp.contour_within σ).2 b hb
      exact hinside y b h1 h2
    simp only [PeriodicLattice.contourFormAverage, hz, Finset.sum_const_zero, smul_zero]
  refine ⟨?_, ?_, ?_⟩
  · funext y
    have h0 : ∑ᶠ x ∈ sitesInBlock (levelDepth k j) y, PeriodicLattice.contourFormAverage B y x = 0 :=
      (finsum_mem_congr rfl fun x hx => hcontour y x hx).trans (by simp)
    show PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x ∈ sitesInBlock (levelDepth k j) y, PeriodicLattice.contourFormAverage B y x = 0
    rw [h0, smul_zero]
  · funext x
    have hex : ∃ y : Vertex L n k (j + 1), x.1 ∈ sitesInBlock (levelDepth k j) y ∧
        (x.1 : FourTorus L n) ≠ y := by
      obtain ⟨y, hy, -⟩ := huniq x.1
      refine ⟨y, hy, fun h => x.2 ?_⟩
      rw [h]
      exact y.2
    exact hcontour _ _ (Classical.epsilon_spec hex).1
  · intro c hc
    obtain ⟨μ, hμ⟩ := id hc
    have hc' := hcor c μ hμ
    have hT := hTrans c μ (Or.inl hμ)
    have hcoeT : ∀ x : Vertex L n k j, ((shiftAcross c x : Vertex L n k j) : FourTorus L n) =
        (x : FourTorus L n) + ((c.target : FourTorus L n) - (c.source : FourTorus L n)) := by
      intro x
      show ((x + (c.target - c.source).toSublattice (levelDepth k j) : Vertex L n k j) : FourTorus L n) = _
      rw [AddSubgroup.coe_add, coe_toSublattice hL0 hle, AddSubgroup.coe_sub]
    have hmem : ∀ x ∈ sitesInBlock (levelDepth k j) c.source,
        shiftAcross c x ∈ sitesInBlock (levelDepth k j) c.target := by
      intro x hx
      show ((shiftAcross c x : Vertex L n k j) : FourTorus L n) ∈ unitBlock c.target
      rw [hcoeT]
      exact hT.1.mapsTo hx
    have hQ : linearSmoothing L n k j B c = crossingSmoothing L n k j B c := by
      show PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum B c =
        PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.source,
          edgeFormPathSum B (crossingPath c x)
      refine congrArg (PeriodicLattice.inverseFourthPowerWeight L • ·)
        (finsum_mem_congr rfl fun x hx => ?_)
      rw [hcontour c.source x hx, hcontour c.target _ (hmem x hx), zero_add, sub_zero]
      rfl
    refine ⟨hQ, ?_⟩
    have hhead : (c.target : FourTorus L n) = (c.source : FourTorus L n) +
        (((L : ℤ) • unitStep L n (levelDepth k j) μ : Vertex L n k j) : FourTorus L n) := by
      calc (c.target : FourTorus L n) =
            ((c.target.toSublattice (levelDepth k j) : Vertex L n k j) : FourTorus L n) :=
            (coe_toSublattice hL0 hle c.target).symm
        _ = _ := by rw [hc'.target_eq, AddSubgroup.coe_add, coe_toSublattice hL0 hle c.source]
    have hstep : ∀ x : Vertex L n k j,
        shiftAcross c x - x = (L : ℤ) • unitStep L n (levelDepth k j) μ := by
      intro x
      apply Subtype.ext
      rw [AddSubgroup.coe_sub, hcoeT, hhead]
      abel
    have hcross : ∀ x ∈ sitesInBlock (levelDepth k j) c.source,
        crossingPath c x = PeriodicLattice.forwardAxisPath x μ L := by
      intro x hx
      obtain ⟨-, ⟨t', ht', hdisp⟩, -, -⟩ := hT.2 x (shiftAcross c x) hx (hcoeT x)
      have hb1 : ((|(L : ℤ)| : ℤ) : ℝ) < (L : ℝ) ^ ((n : ℤ) + levelDepth k j) := by
        have h2 := hdisp.2
        rw [ht'] at h2
        simpa using h2
      have hbd : ((|(L : ℤ)| : ℤ) : ℝ) * meshAt L k j < PeriodicLattice.torusSide L n / 2 := by
        rw [← meshSize_levelDepth]
        exact ((hLat L hL n j k hn (by omega)).2.2.1 (L : ℤ)).1 hb1
      have h3 := ((hStr L hL k j (by omega)).1 n hn).2 x (shiftAcross c x) μ μ L L
        (hstep x) hbd (hstep x) hbd
      show PeriodicLattice.axialPath x (shiftAcross c x) = _
      rw [h3.2]
      simp [PeriodicLattice.flowAlong]
    have hzero : ∀ x ∈ sitesInBlock (levelDepth k j) c.source, ∀ b ∈ crossingPath c x,
        b.IsPositivelyOriented → b ≠ pivot c → B b = 0 := by
      intro x hx b hb hbp hne
      obtain ⟨h1, h2⟩ := (((hSch L hL n k j hn hjk .centred).2.1 c hc).1.crossing_within x hx).2 b hb
      refine hs b hbp fun c' hc' heq => hne ?_
      obtain ⟨⟨h3, h4⟩, hd⟩ := hpos c' hc'
      rw [← heq] at h3 h4
      have hcc : c' = c := by
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exfalso
          have e1 := (huniq b.source).unique h3 h1
          have e2 := (huniq b.target).unique h4 h2
          rw [e1, e2] at hd
          exact Set.disjoint_left.1 hd h1 h1
        · exact PeriodicLattice.Bond.ext ((huniq b.source).unique h3 h1)
            ((huniq b.target).unique h4 h2)
        · exfalso
          have e1 := (huniq b.source).unique h3 h1
          have e2 := (huniq b.target).unique h4 h2
          obtain ⟨ν, hν⟩ := hc'
          rw [e1, e2] at hν
          exact not_both_orientations hLat hL hn (by omega) c μ hμ ν hν
        · exfalso
          have e1 := (huniq b.source).unique h3 h1
          have e2 := (huniq b.target).unique h4 h2
          rw [e1, e2] at hd
          exact Set.disjoint_left.1 hd h1 h1
      rw [heq, hcc]
    have hfin : (sitesInBlock (levelDepth k j) c.source).Finite := by
      have h0 : (unitBlock c.source).Finite :=
        Set.finite_of_ncard_ne_zero (by rw [(hDisp c.source).2.2.1]; exact pow_ne_zero _ hL0.ne')
      exact h0.preimage Subtype.val_injective.injOn
    have hsum : ∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.source, edgeFormPathSum B (crossingPath c x) =
        L • B (pivot c) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
      have h1 : ∀ x ∈ hfin.toFinset, edgeFormPathSum B (crossingPath c x) = ∑ i ∈ Finset.range L,
          B (PeriodicLattice.Bond.forwardFrom (x + i • unitStep L n (levelDepth k j) μ) μ) :=
        fun x hx => by
          show PeriodicLattice.bondFormSumAlong B (crossingPath c x) = _
          rw [hcross x (hfin.mem_toFinset.1 hx), bondFormSumAlong_forwardFlow]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      have h2 : ∀ i ∈ Finset.range L, ∑ x ∈ hfin.toFinset,
          B (PeriodicLattice.Bond.forwardFrom (x + i • unitStep L n (levelDepth k j) μ) μ) =
            B (pivot c) := by
        intro i hi
        have hi' := Finset.mem_range.1 hi
        have hx₀ : c.source.toSublattice (levelDepth k j) + ((t : ℤ) - i) • unitStep L n (levelDepth k j) μ ∈
            sitesInBlock (levelDepth k j) c.source := by
          show ((c.source.toSublattice (levelDepth k j) + ((t : ℤ) - i) • unitStep L n (levelDepth k j) μ :
            Vertex L n k j) : FourTorus L n) ∈ unitBlock c.source
          rw [show unitBlock c.source = _ from hc'.source_block]
          refine ⟨Pi.single μ ((t : ℤ) - i), fun ν => ?_, ?_⟩
          · rw [hhalf]
            by_cases hνμ : ν = μ
            · subst hνμ
              rw [Pi.single_eq_same, abs_le]
              omega
            · rw [Pi.single_eq_of_ne hνμ]
              simp
          · congr 1
            simp [PeriodicLattice.offsetSite, Pi.single_apply, ite_smul]
        have hb₀ : PeriodicLattice.Bond.forwardFrom (c.source.toSublattice (levelDepth k j) +
            ((t : ℤ) - i) • unitStep L n (levelDepth k j) μ + i • unitStep L n (levelDepth k j) μ) μ =
              pivot c := by
          rw [hc'.pivot_eq, htoNat]
          show _ = PeriodicLattice.Bond.forwardFrom (c.source.toSublattice (levelDepth k j) +
            (t : ℤ) • unitStep L n (levelDepth k j) μ) μ
          congr 1
          rw [sub_smul, natCast_zsmul, natCast_zsmul]
          abel
        rw [Finset.sum_eq_single_of_mem _ (hfin.mem_toFinset.2 hx₀) ?_, hb₀]
        intro x hx hne
        have hxS := hfin.mem_toFinset.1 hx
        refine hzero x hxS _ ?_ ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩ fun he => hne ?_
        · rw [hcross x hxS]
          exact forwardFrom_mem_forwardFlow μ L i hi' x
        · have h3 := congrArg PeriodicLattice.Bond.source (he.trans hb₀.symm)
          exact add_right_cancel (show x + i • unitStep L n (levelDepth k j) μ = _ from h3)
      rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range]
    show PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth k j) c.source,
      edgeFormPathSum B (crossingPath c x) = TrivialLinearization.pivotScale L • B (pivot c)
    have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
    rw [hsum, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    simp only [PeriodicLattice.inverseFourthPowerWeight, TrivialLinearization.pivotScale,
      Complex.ofReal_zpow, Complex.ofReal_natCast]
    rw [show (-3 : ℤ) = -4 + 1 by norm_num, zpow_add₀ hLc, zpow_one]
end YangMills.Construction.Tower.PivotFormsProof
end
