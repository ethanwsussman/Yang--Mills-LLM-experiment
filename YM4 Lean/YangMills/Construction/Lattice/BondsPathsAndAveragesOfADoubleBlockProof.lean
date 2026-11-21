import YangMills.Construction.Lattice.AveragingMapReadsAnyFunctionOnTheDoubleBlockProof
import YangMills.Construction.Lattice.AxialPathsAndPivots
import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlock
import YangMills.Construction.Lattice.ContoursWithinBlocks
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.DoubleBlockStructure
section BondFacts
variable {L m : ℕ} {j j' : ℤ}
private theorem pathHolonomy_congr {U U' : Bond L m j → Matrices.ComplexMatrix2}
    {γ : List (Bond L m j)} (h : ∀ b ∈ γ, U b = U' b) :
    pathHolonomy U γ = pathHolonomy U' γ := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexAverageLocality.pathHolonomy_congr <;> assumption
private theorem boundaryBonds_mem_bondsInside {S : Set (FourTorus L m)} {p : Plaquette L m j'}
    (hp : p ∈ (plaquettesInside S : Set (Plaquette L m j'))) :
    ∀ b ∈ p.boundaryBonds, b ∈ (bondsInside S : Set (Bond L m j')) := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.boundaryBonds_mem_bondsInside <;> assumption
private theorem bondsInDoubleBlock_opposite (c : Bond L m j) :
    (bondsInDoubleBlock c.opposite : Set (Bond L m j')) = bondsInDoubleBlock c := by apply _root_.YangMills.Construction.PeriodicLattice.bondsInDoubleBlock_opposite <;> assumption
private theorem bondCorridor_opposite (c : Bond L m j) :
    (bondCorridor c.opposite : Set (Bond L m j')) = Bond.opposite '' bondCorridor c := by
  ext b
  constructor
  · intro hb
    exact ⟨b.opposite, ⟨hb.2, hb.1⟩, Bond.ext rfl rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha.2, ha.1⟩
private theorem oneOfFourHolds_of_or_of_or {a b a' b' : Prop} (hs : a ∨ b) (ht : a' ∨ b')
    (d1 : a → b → False) (d2 : a' → b' → False) :
    OneOfFourHolds (a ∧ a') (b ∧ b') (a ∧ b') (a' ∧ b) := by
  unfold OneOfFourHolds
  tauto
private theorem oneOfFourHolds_of_disjoint (c : Bond L m j)
    (hd : unitBlock c.source ∩ unitBlock c.target = ∅) (b : Bond L m j')
    (hb : b ∈ (bondsInDoubleBlock c : Set (Bond L m j'))) :
    OneOfFourHolds
      ((b.source : FourTorus L m) ∈ unitBlock c.source ∧
        (b.target : FourTorus L m) ∈ unitBlock c.source)
      ((b.source : FourTorus L m) ∈ unitBlock c.target ∧
        (b.target : FourTorus L m) ∈ unitBlock c.target)
      (b ∈ (bondCorridor c : Set (Bond L m j')))
      (b.opposite ∈ (bondCorridor c : Set (Bond L m j'))) := by
  have hdis : ∀ z : FourTorus L m, z ∈ unitBlock c.source → z ∈ unitBlock c.target → False :=
    fun z h1 h2 => by
      have hz : z ∈ unitBlock c.source ∩ unitBlock c.target := ⟨h1, h2⟩
      rw [hd] at hz
      exact hz
  have hs : (b.source : FourTorus L m) ∈ unitBlock c.source ∨
      (b.source : FourTorus L m) ∈ unitBlock c.target := hb.1
  have ht : (b.target : FourTorus L m) ∈ unitBlock c.source ∨
      (b.target : FourTorus L m) ∈ unitBlock c.target := hb.2
  exact oneOfFourHolds_of_or_of_or hs ht (hdis b.source) (hdis b.target)
private theorem forwardFlow_length (x : Site L m j) (μ : Fin 4) (k : ℕ) :
    (forwardAxisPath x μ k).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [forwardAxisPath, ih]
abbrev _root_.YangMills.SharedProofs.p1058 := @forwardFlow_length
private theorem backwardFlow_length (x : Site L m j) (μ : Fin 4) (k : ℕ) :
    (backwardAxisPath x μ k).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [backwardAxisPath, ih]
abbrev _root_.YangMills.SharedProofs.p8383 := @backwardFlow_length
private theorem coe_toSublattice (hL : 0 < L) (h : j ≤ j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y := by apply _root_.YangMills.Construction.SeparatedSequences.BlockAverages.coe_toSublattice <;> assumption
private theorem forwardFrom_mem_forwardFlow (y : Site L m j) (μ : Fin 4) (k i : ℕ) (hi : i < k) :
    Bond.forwardFrom (y + (i : ℤ) • unitStep L m j μ) μ ∈ forwardAxisPath y μ k := by
  induction k generalizing y i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => simp [forwardAxisPath]
    | succ i =>
      have e : y + ((i + 1 : ℕ) : ℤ) • unitStep L m j μ =
          y + unitStep L m j μ + (i : ℤ) • unitStep L m j μ := by
        push_cast
        rw [add_smul, one_smul]
        abel
      rw [e]
      exact List.mem_cons_of_mem _ (ih (y + unitStep L m j μ) i (by omega))
private theorem exists_eq_of_mem_backwardFlow (z : Site L m j) (μ : Fin 4) (k : ℕ)
    (b : Bond L m j) (hb : b ∈ backwardAxisPath z μ k) :
    ∃ i : ℕ, i < k ∧ b = Bond.backwardFrom (z - (i : ℤ) • unitStep L m j μ) μ := by
  induction k generalizing z with
  | zero => simp [backwardAxisPath] at hb
  | succ k ih =>
    rw [backwardAxisPath, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨0, by omega, by simp⟩
    · obtain ⟨i, hi, rfl⟩ := ih _ hb
      refine ⟨i + 1, by omega, ?_⟩
      congr 1
      push_cast
      rw [add_smul, one_smul]
      abel
private theorem opposite_mem_forwardFlow (y : Site L m j) (μ : Fin 4) (k : ℕ) (b : Bond L m j)
    (hb : b ∈ backwardAxisPath (y + (k : ℤ) • unitStep L m j μ) μ k) :
    b.opposite ∈ forwardAxisPath y μ k := by
  obtain ⟨i, hi, rfl⟩ := exists_eq_of_mem_backwardFlow _ _ _ _ hb
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 + i := ⟨k - (i + 1), by omega⟩
  have e : (Bond.backwardFrom (y + ((r + 1 + i : ℕ) : ℤ) • unitStep L m j μ -
      (i : ℤ) • unitStep L m j μ) μ).opposite =
      Bond.forwardFrom (y + (r : ℤ) • unitStep L m j μ) μ := by
    have h : y + ((r + 1 + i : ℕ) : ℤ) • unitStep L m j μ - (i : ℤ) • unitStep L m j μ =
        y + (r : ℤ) • unitStep L m j μ + unitStep L m j μ := by
      push_cast
      rw [add_smul, add_smul, one_smul]
      abel
    rw [h]
    apply Bond.ext
    · simp [Bond.opposite, Bond.backwardFrom, Bond.forwardFrom]
    · simp [Bond.opposite, Bond.backwardFrom, Bond.forwardFrom]
  rw [e]
  exact forwardFrom_mem_forwardFlow _ _ _ _ (by omega)
end BondFacts
variable {L m K n : ℕ}
private theorem bondClassification (hS : AxialPathCorridorAndPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (c : BondAtLevel L m K (n + 1)) : DoubleBlockBondClassification c := by
  have hK : 0 < K := by omega
  obtain ⟨-, μ, ε, -, -, hst⟩ := (hS ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩ n hn).2 c
  have hd : unitBlock c.source ∩ unitBlock c.target = ∅ := hst.unitBlock_inter_eq_empty
  exact ⟨hd, fun b hb => oneOfFourHolds_of_disjoint c hd b hb, fun b hb => ⟨hb.2, hb.1⟩,
    bondsInDoubleBlock_opposite c, bondCorridor_opposite c⟩
private theorem contoursStayInBlocks (hC : ContoursWithinBlockStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (c : BondAtLevel L m K (n + 1)) : ContoursStayInBlocks c := by
  intro y hy x hx γ hγ
  obtain ⟨hs, hb⟩ := hC L m K n hL hm hn y x hx γ hγ
  refine ⟨fun z hz => hs z hz, fun b hbγ => ?_⟩
  have hin : (b.source : FourTorus L m) ∈ unitBlock y ∧
      (b.target : FourTorus L m) ∈ unitBlock y := hb b hbγ
  rcases hy with rfl | rfl
  · exact ⟨Or.inl hin.1, Or.inl hin.2⟩
  · exact ⟨Or.inr hin.1, Or.inr hin.2⟩
private theorem crossingPath_properties (hS : AxialPathCorridorAndPivotStatement)
    (hP : BlockPaths.Statement) (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hn : n < K) (c : BondAtLevel L m K (n + 1)) (x : SiteAtLevel L m K n)
    (hx : x ∈ sitesInBlock (levelDepth K n) c.source) :
    (shiftAcross c x : FourTorus L m) ∈ unitBlock c.target ∧
    (∃ (μ : Fin 4) (k : ℤ), IsAxialDisplacement x (shiftAcross c x) μ k) ∧
    (crossingPath c x).length = L ∧
    ∀ b ∈ crossingPath c x, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := by
  have hLpos : 0 < L := by
    have := hL.2
    omega
  have hK : 0 < K := by omega
  obtain ⟨ν, hc | hc⟩ := c.isNeighbour
  · obtain ⟨hco, -, -, hst, hin⟩ := (hP L m K hL.1 hL.2 hm n hn).2 c ν hc
    obtain ⟨-, -, -, himage, htrans, -⟩ := hco
    obtain ⟨hdisp, hcross, -, -⟩ := hst.1 x hx
    refine ⟨?_, ⟨ν, L, ?_⟩, ?_, hin.2 x hx⟩
    · rw [htrans x hx]
      exact show x + blockTranslation L m (levelDepth K n) ν ∈
          sitesInBlock (levelDepth K n) c.target from by
        rw [← himage]
        exact ⟨x, hx, rfl⟩
    · rw [htrans x hx]
      exact hdisp
    · rw [hcross, forwardFlow_length]
  · have hd : c.opposite.target - c.opposite.source = unitStep L m (levelDepth K (n + 1)) ν := by
      change c.source - c.target = _
      rw [← neg_sub, hc, neg_neg]
    obtain ⟨hco, -, -, hst, hin⟩ := (hP L m K hL.1 hL.2 hm n hn).2 c.opposite ν hd
    obtain ⟨htarget, -, -, himage, htrans, -⟩ := hco
    have hx' : x ∈ sitesInBlock (levelDepth K n) c.opposite.target := hx
    rw [← himage] at hx'
    obtain ⟨x₀, hx₀, rfl⟩ := hx'
    obtain ⟨hdisp, hcross, -, -⟩ := hst.1 x₀ hx₀
    have hle : levelDepth K (n + 1) ≤ levelDepth K n := by
      simp only [levelDepth]
      push_cast
      omega
    have ht : shiftAcross c (x₀ + blockTranslation L m (levelDepth K n) ν) = x₀ := by
      have h1 : (c.opposite.target - c.opposite.source).toSublattice (levelDepth K n) =
          blockTranslation L m (levelDepth K n) ν := by
        have h := htrans x₀ hx₀
        simp only [shiftAcross] at h
        exact add_left_cancel h
      have h2 : (c.target - c.source).toSublattice (levelDepth K n) =
          -(c.opposite.target - c.opposite.source).toSublattice (levelDepth K n) := by
        apply Subtype.ext
        rw [AddSubgroup.coe_neg, coe_toSublattice hLpos hle, coe_toSublattice hLpos hle,
          ← AddSubgroup.coe_neg]
        congr 1
        change c.target - c.source = -(c.source - c.target)
        abel
      simp only [shiftAcross]
      rw [h2, h1]
      abel
    have hneg : IsAxialDisplacement (x₀ + blockTranslation L m (levelDepth K n) ν) x₀ ν
        (-(L : ℤ)) := by
      refine ⟨?_, ?_⟩
      · rw [neg_smul]
        simp [blockTranslation]
      · rw [abs_neg]
        exact hdisp.2
    have hu : ∃! q : Fin 4 × ℤ, IsAxialDisplacement (c.source.toSublattice (levelDepth K n))
        (c.target.toSublattice (levelDepth K n)) q.1 q.2 :=
      ((hS ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩ n hn).2 c).1
    have hmove : ∀ (μ : Fin 4) (k : ℤ),
        IsAxialDisplacement (x₀ + blockTranslation L m (levelDepth K n) ν) x₀ μ k →
          IsAxialDisplacement (c.source.toSublattice (levelDepth K n))
            (c.target.toSublattice (levelDepth K n)) μ k := by
      intro μ k h
      refine ⟨?_, h.2⟩
      rw [← h.1]
      have h3 : c.source.toSublattice (levelDepth K n) =
          c.target.toSublattice (levelDepth K n) + blockTranslation L m (levelDepth K n) ν :=
        htarget
      rw [h3]
      abel
    have hex : ∃ q : Fin 4 × ℤ,
        IsAxialDisplacement (x₀ + blockTranslation L m (levelDepth K n) ν) x₀ q.1 q.2 :=
      ⟨(ν, -(L : ℤ)), hneg⟩
    have hq : hex.choose = (ν, -(L : ℤ)) :=
      hu.unique (hmove _ _ hex.choose_spec) (hmove _ _ hneg)
    have hpath : crossingPath c (x₀ + blockTranslation L m (levelDepth K n) ν) =
        backwardAxisPath (x₀ + blockTranslation L m (levelDepth K n) ν) ν L := by
      rw [crossingPath, ht, axialPath, dif_pos hex, hq]
      have h0 : ¬ (0 : ℤ) ≤ -(L : ℤ) := by omega
      simp only [flowAlong, if_neg h0, neg_neg, Int.toNat_natCast]
    refine ⟨?_, ⟨ν, -(L : ℤ), ?_⟩, ?_, fun b hb => ?_⟩
    · rw [ht]
      exact hx₀
    · rw [ht]
      exact hneg
    · rw [hpath, backwardFlow_length]
    · rw [hpath] at hb
      have hr := opposite_mem_forwardFlow x₀ ν L b hb
      rw [← hcross] at hr
      have hbond := hin.2 x₀ hx₀ b.opposite hr
      exact ⟨Or.symm hbond.2, Or.symm hbond.1⟩
private theorem axialPathsSpanDoubleBlock (hS : AxialPathCorridorAndPivotStatement)
    (hP : BlockPaths.Statement) (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hn : n < K) (c : BondAtLevel L m K (n + 1)) : AxialPathsSpanDoubleBlock c := by
  have hK : 0 < K := by omega
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := crossingPath_properties hS hP hL hm hn c x hx
    refine ⟨h1, h2, h3, ?_, h4⟩
    rintro z (rfl | rfl | ⟨b, hb, rfl | rfl⟩)
    · exact Or.inl hx
    · exact Or.inr h1
    · exact (h4 b hb).1
    · exact (h4 b hb).2
  · obtain ⟨-, μ, ε, -, -, hst⟩ := (hS ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩ n hn).2 c
    exact ⟨pivot c, hst.pivot_source_mem, hst.pivot_target_mem⟩
private theorem toSublattice_mem_sitesInBlock (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (y : SiteAtLevel L m K (n + 1)) :
    y.toSublattice (levelDepth K n) ∈ sitesInBlock (levelDepth K n) y := by apply _root_.YangMills.SharedProofs.p38533 <;> assumption
private theorem averageDependsOnDoubleBlock_of_isPositivelyOriented (hP : BlockPaths.Statement)
    (hM : BlockAverageDependsOnDoubleBlock)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    {c : BondAtLevel L m K (n + 1)} (hc : c.IsPositivelyOriented) :
    AverageDependsOnDoubleBlock c := by
  intro U hU U' hU' h
  obtain ⟨μ, hμ⟩ := hc
  obtain ⟨⟨-, -, -, hd4, hd5, -⟩, -, -, hSt, hPth⟩ := (hP L m K hL.1 hL.2 hm n hn).2 c μ hμ
  have hTargetMem : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      shiftAcross c x ∈ sitesInBlock (levelDepth K n) c.target := by
    intro x hx
    rw [hd5 x hx, ← hd4]
    exact ⟨x, hx, rfl⟩
  have hSource : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      contourHolonomies U c.source x = contourHolonomies U' c.source x := fun x hx =>
    funext fun σ => pathHolonomy_congr fun b hb =>
      h b ((hPth.1 c.source (Or.inl rfl) x hx).1 _ ⟨σ, rfl⟩ b hb)
  have hTarget : ∀ x ∈ sitesInBlock (levelDepth K n) c.target,
      contourHolonomies U c.target x = contourHolonomies U' c.target x := fun x hx =>
    funext fun σ => pathHolonomy_congr fun b hb =>
      h b ((hPth.1 c.target (Or.inr rfl) x hx).1 _ ⟨σ, rfl⟩ b hb)
  have hCross : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      pathHolonomy U (crossingPath c x) = pathHolonomy U' (crossingPath c x) := fun x hx =>
    pathHolonomy_congr fun b hb => h b (hPth.2 x hx b hb)
  have hTransport : parallelTransport U c = parallelTransport U' c := by
    unfold parallelTransport
    rw [hSt.2.1]
    exact hCross _ (toSublattice_mem_sitesInBlock hP hL hm hn c.source)
  have hDefect : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      crossingDefect U c x = crossingDefect U' c x := by
    intro x hx
    unfold crossingDefect meanContourHolonomy
    rw [hSource x hx, hTarget _ (hTargetMem x hx), hCross x hx, hTransport]
  have hContourDefect : ∀ x ∈ sitesInBlock (levelDepth K n) c.source, ∀ σ σ',
      contourCrossingDefect U c x σ σ' = contourCrossingDefect U' c x σ σ' := by
    intro x hx σ σ'
    have e1 : pathHolonomy U (orderedContour c.source x σ) =
        pathHolonomy U' (orderedContour c.source x σ) :=
      congrFun (hSource x hx) σ
    have e2 : pathHolonomy U (orderedContour c.target (shiftAcross c x) σ') =
        pathHolonomy U' (orderedContour c.target (shiftAcross c x) σ') :=
      congrFun (hTarget _ (hTargetMem x hx)) σ'
    unfold contourCrossingDefect
    rw [e1, e2, hCross x hx, hTransport]
  have hNear : DoubleBlockPlaquettesNear (Averaging.smoothingRadius L) c U ↔
      DoubleBlockPlaquettesNear (Averaging.smoothingRadius L) c U' := by
    unfold DoubleBlockPlaquettesNear
    refine forall₂_congr fun p hp => ?_
    unfold plaquetteHolonomy
    rw [pathHolonomy_congr fun b hb => h b (boundaryBonds_mem_bondsInside hp b hb)]
  have hRegular : IsRegularAveragingCase (Averaging.smoothingRadius L) U c ↔
      IsRegularAveragingCase (Averaging.smoothingRadius L) U' c := by
    unfold IsRegularAveragingCase HasContourMean
    refine and_congr hNear (and_congr ?_ (and_congr ?_ ?_))
    · exact forall₂_congr fun x hx => by rw [hSource x hx]
    · exact forall₂_congr fun x hx => by rw [hTarget x hx]
    · exact forall₂_congr fun x hx => by rw [hDefect x hx]
  have hNotMinus : (∀ x ∈ sitesInBlock (levelDepth K n) c.source, ∀ σ σ',
      contourCrossingDefect U c x σ σ' ≠ -1) ↔
      ∀ x ∈ sitesInBlock (levelDepth K n) c.source, ∀ σ σ',
        contourCrossingDefect U' c x σ σ' ≠ -1 :=
    forall₂_congr fun x hx => forall_congr' fun σ => forall_congr' fun σ' => by
      rw [hContourDefect x hx σ σ']
  refine ⟨⟨fun h1 => ⟨hU', hNear.1 h1.2⟩, fun h1 => ⟨hU, hNear.2 h1.2⟩⟩, ?_,
    hM L m K n hL hm hn _ c U U' h⟩
  by_cases h1 : IsRegularAveragingCase (Averaging.smoothingRadius L) U c
  · exact Or.inl ⟨h1, hRegular.1 h1⟩
  · have h1' : ¬IsRegularAveragingCase (Averaging.smoothingRadius L) U' c := fun h' =>
      h1 (hRegular.2 h')
    by_cases h2 : ∀ x ∈ sitesInBlock (levelDepth K n) c.source, ∀ σ σ',
        contourCrossingDefect U c x σ σ' ≠ -1
    · exact Or.inr (Or.inl ⟨⟨h1, h2⟩, ⟨h1', hNotMinus.1 h2⟩⟩)
    · exact Or.inr (Or.inr ⟨⟨h1, fun hb => h2 hb.2⟩, ⟨h1', fun hb => h2 (hNotMinus.2 hb.2)⟩⟩)
theorem statement_holds (hS : AxialPathCorridorAndPivotStatement)
    (hP : BlockPaths.Statement) (hC : ContoursWithinBlockStatement)
    (hM : BlockAverageDependsOnDoubleBlock) : Statement := by
  intro L m K n hL hm hn c
  exact ⟨bondClassification hS hL hm hn c, contoursStayInBlocks hC hL hm hn c,
    axialPathsSpanDoubleBlock hS hP hL hm hn c,
    fun p hp b hb => boundaryBonds_mem_bondsInside hp b hb,
    fun hc => averageDependsOnDoubleBlock_of_isPositivelyOriented hP hM hL hm hn hc⟩
end YangMills.Construction.PeriodicLattice.DoubleBlockStructure
