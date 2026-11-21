import YangMills.Construction.SeparatedSequences.ClassGeometryInWeightedData
import YangMills.Construction.SeparatedSequences.ObjectsUpToTheLastNonEmptyMember
import YangMills.Construction.Torus.PhysicalTorusInLevelUnitsAsATorusOfGeneralSide
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace SeparatedClasses.WeightedGeometryOfClass
open SingleSequence SingleSequence.SequenceData
private abbrev levelDataOf (s : SequenceData) (e : ℕ) : GeneralTorus.LevelUnitParams where
  L := s.data.L
  blocking := s.blockingFactor
  m := s.data.m
  m_pos := s.data.m.pos
  K := s.data.cutoff
  K_pos := s.data.K.pos
  t := s.data.t
  t_le := s.data.t_le_cutoff
  blockExp := e
  gapExp := s.data.gapExp
private theorem unitTorusSide_eq (s : SequenceData) (e : ℕ) :
    s.unitTorusSide = (levelDataOf s e).toScaleData.torusSide := by
  change 2 * (s.data.L : ℝ) ^ (((s.data.m : ℕ) : ℤ) + ((s.data.cutoff : ℕ) : ℤ) - (s.data.t : ℤ)) =
    2 * (s.data.L : ℝ) ^ ((s.data.m : ℕ) + (s.data.cutoff : ℕ) - s.data.t)
  have h : s.data.t ≤ (s.data.m : ℕ) + (s.data.cutoff : ℕ) := by
    have h' : s.data.t ≤ (s.data.cutoff : ℕ) := s.data.t_le_cutoff
    omega
  rw [← zpow_natCast (s.data.L : ℝ), Nat.cast_sub h, Nat.cast_add]
private theorem toTorus_eq_readPoint (s : SequenceData) (e : ℕ) :
    s.toTorus (levelDataOf s e).toScaleData.torusSide = (levelDataOf s e).readPoint := by
  have h : (levelDataOf s e).toScaleData.torusSide ≠ 0 := (levelDataOf s e).torusSide_ne_zero
  funext x
  unfold SequenceData.toTorus
  rw [dif_pos h]
  rfl
private theorem pathLengthIn_empty (S : ℝ) (Γ : List LiftedSegment) : pathLengthIn S Γ ∅ = 0 := by
  simp [pathLengthIn]
private theorem cubePartition_eq_image {S σ : ℝ} {F : Prop} (hF : F) :
    {Q : Set (Torus4 S) | F ∧ ∃ y ∈ GeneralTorus.spacingLattice S σ, Q = GeneralTorus.supCube σ y} =
      GeneralTorus.supCube σ '' (GeneralTorus.spacingLattice S σ : Set (Torus4 S)) := by
  ext Q
  constructor
  · rintro ⟨-, y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hF, y, hy, rfl⟩
theorem holds (h : GeneralTorus.LevelUnitParams.EvaluationAgrees)
    (hlast : AgreesUpToLastNonempty) : Statement := by
  intro s D B hD
  obtain ⟨L, st, bn, bnp, lbn, gn, gnp, lgn, ξ, ξp, top, S, sm⟩ := D
  obtain ⟨hL, hb, hg, hξ, htop, hS, hmem⟩ := hD
  dsimp only at hL hb hg hξ htop hS
  subst hL hb hg hξ htop
  have hS' : S = (levelDataOf s s.data.blockExp).toScaleData.torusSide :=
    hS.trans (unitTorusSide_eq s _)
  subst hS'
  set P := levelDataOf s s.data.blockExp with hP
  have hread : s.toTorus P.toScaleData.torusSide = P.readPoint := toTorus_eq_readPoint s _
  have hread0 : s.toTorus P.toScaleData.torusSide = (levelDataOf s 0).readPoint :=
    toTorus_eq_readPoint s 0
  obtain ⟨hlat, hcubes, hsame, hobj⟩ := h P
  obtain ⟨-, hcubes0, -, -⟩ := h (levelDataOf s 0)
  have hsep : SeparatedSequences.IsSeparatedSequence P.seqScales P.gapFactor s.Ω := by
    have hg : P.gapFactor = (s.data.gapSize : ℝ) := by
      simp [P, GeneralTorus.LevelUnitParams.gapFactor, ClassData.gapSize]
    rw [hg]
    exact s.Ω_mem.2.1
  obtain ⟨B', hB'⟩ := hsame.1 s.Ω hsep
  obtain ⟨hlay, hsites, hsite, hlen, hdist⟩ := hobj s.Ω B' hsep hB'
  have hc := hlast s.data s.Ω s.Ω_mem
  have hTt : s.lastIdx ≤ s.data.t := s.data.lastNonempty_le s.Ω
  have hmember : ∀ n, SeparatedSequences.truncatedMember P.seqScales s.Ω n = s.Ω n := by
    intro n
    unfold SeparatedSequences.truncatedMember
    split_ifs with hn
    · rfl
    · exact (s.Ω_mem.2.2 n (not_le.mp hn)).symm
  have hBm : ∀ n, B.stage n = B'.set n := by
    intro n
    rw [hmem n, hB' n, hmember n, ← hread]
    rfl
  have hBlayer : ∀ n, B.layer n = B'.shell n := by
    intro n
    rcases lt_trichotomy n s.lastIdx with hn | hn | hn
    · have h1 : n < s.data.t := hn.trans_le hTt
      have e1 : B.layer n = closure (B.stage n \ B.stage (n + 1)) := if_pos hn
      have e2 : B'.shell n = closure (B'.set n \ B'.set (n + 1)) := if_pos h1
      rw [e1, e2, hBm, hBm]
    · subst hn
      have e1 : B.layer s.lastIdx = B.stage s.lastIdx := by
        unfold Weighted.SeparatedChain.layer
        rw [if_neg (lt_irrefl _), if_pos rfl]
      have e2 : SeparatedSequences.layerSet P.seqScales s.Ω s.lastIdx = s.Ω s.lastIdx := by
        have e3 := hc.layer_eq.1 s.lastIdx le_rfl
        refine e3.trans ?_
        change SeparatedSequences.layerSet (ClassData.truncScales hTt) s.Ω s.lastIdx = s.Ω s.lastIdx
        unfold SeparatedSequences.layerSet
        rw [if_neg (lt_irrefl _), if_pos rfl]
      rw [e1, hlay, e2, hmem, ← hread]
      rfl
    · have e1 : B.layer n = ∅ := by
        unfold Weighted.SeparatedChain.layer
        rw [if_neg (not_lt.mpr hn.le), if_neg hn.ne']
      have e2 : SeparatedSequences.layerSet P.seqScales s.Ω n = ∅ := by
        by_cases hnt : n ≤ s.data.t
        · exact hc.layer_eq.2 n hn hnt
        · have h1 : ¬n < P.seqScales.top := fun h' => hnt (le_of_lt h')
          have h2 : ¬n = P.seqScales.top := fun h' => hnt (le_of_eq h')
          unfold SeparatedSequences.layerSet
          rw [if_neg h1, if_neg h2]
      rw [e1, hlay, e2, image_empty]
  have hBsites : ∀ n, B.layerSites n = B'.shellSites n := by
    intro n
    change _ ∩ B.layer n = _ ∩ B'.shell n
    rw [hBlayer n]
    rfl
  have hBlayerEmpty : ∀ n, s.lastIdx < n → B.layer n = ∅ := by
    intro n hn
    unfold Weighted.SeparatedChain.layer
    rw [if_neg (not_lt.mpr hn.le), if_neg hn.ne']
  have hBempty : ∀ n, s.lastIdx < n → B.layerSites n = ∅ := by
    intro n hn
    change _ ∩ B.layer n = ∅
    rw [hBlayerEmpty n hn, inter_empty]
  have hBspacing : ∀ x, B.siteScale x = B'.localSpacing x := by
    intro x
    change _ = P.toScaleData.levelSpacing _
    unfold Weighted.SeparatedChain.siteScale
    simp only [hBsites]
    rfl
  have hBcube : ∀ x, B.siteCube x = B'.localCube x := by
    intro x
    unfold Weighted.SeparatedChain.siteCube GeneralTorus.SeparatedChain.localCube
    rw [hBspacing]
    rfl
  have hBlength : ∀ Γ, B.weightedLength Γ = B'.scaledLength Γ := by
    intro Γ
    have hsum : ∑ n ∈ Finset.Icc 1 s.lastIdx,
          (P.toScaleData.levelSpacing n)⁻¹ * pathLengthIn P.toScaleData.torusSide Γ (B'.shell n) =
        ∑ n ∈ Finset.Icc 1 s.data.t,
          (P.toScaleData.levelSpacing n)⁻¹ * pathLengthIn P.toScaleData.torusSide Γ (B'.shell n) := by
      refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hTt) ?_
      intro n hn hn'
      have hgt : s.lastIdx < n := by
        simp only [Finset.mem_Icc, not_and, not_le] at hn hn'
        exact hn' hn.1
      rw [← hBlayer n, hBlayerEmpty n hgt, pathLengthIn_empty, mul_zero]
    unfold Weighted.SeparatedChain.weightedLength
      GeneralTorus.SeparatedChain.scaledLength
    rw [hBm 1]
    simp only [hBlayer]
    exact congrArg₂ (· + ·) hsum rfl
  have hBdist : ∀ x x', B.weightedDistance x x' = B'.scaledDist x x' := by
    intro x x'
    unfold Weighted.SeparatedChain.weightedDistance
      GeneralTorus.SeparatedChain.scaledDist
    simp only [hBlength]
    rfl
  have hr : ∀ X : Set s.data.Point, s.toTorus P.toScaleData.torusSide '' X = P.readPoint '' X :=
    fun X => by
      rw [hread]
  have hq : (fun Q : Set s.data.Point => s.toTorus P.toScaleData.torusSide '' Q) =
      fun Q => P.readPoint '' Q := by
    rw [hread]
  have hq0 : (fun Q : Set s.data.Point => s.toTorus P.toScaleData.torusSide '' Q) =
      fun Q => (levelDataOf s 0).readPoint '' Q := by
    rw [hread0]
    rfl
  have hLpos : (0 : ℝ) < s.data.L := by
    have := s.blockingFactor.thirteen_le
    exact_mod_cast (by omega : 0 < s.data.L)
  have hspos : ∀ (e n : ℕ), 0 < (levelDataOf s e).toScaleData.levelSpacing n := fun e n =>
    mul_pos (pow_pos hLpos n) (levelDataOf s e).toScaleData.baseSpacing_pos
  have hTmem : s.lastIdx ∈ {n | n ≤ s.data.t ∧ (s.Ω n).Nonempty} :=
    Nat.sSup_mem ⟨0, Nat.zero_le _, s.Ω_mem.1⟩ ⟨s.data.t, fun _ hx => hx.1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact (hr _).trans (hlat.2.2.2.2.2 n (hn.trans hTt)).2
  · intro n hn
    obtain ⟨-, h2, h3⟩ := hcubes0 n (hn.trans hTt)
    have e := h3 (Nat.zero_le _)
    have eidx : PeriodicLattice.coarseCubeIndex s.data.cutoff 0 n =
        PeriodicLattice.levelDepth s.data.cutoff n := by
      simp [PeriodicLattice.coarseCubeIndex, PeriodicLattice.scaledCubeIndex]
    have eside : (levelDataOf s 0).toScaleData.blockLength n =
        (levelDataOf s 0).toScaleData.levelSpacing n := by
      change ((s.data.L ^ 0 : ℕ) : ℝ) * _ = _
      simp
    have hform := h2.1 (Nat.zero_le _)
    rw [eside] at hform
    have e2 : (levelDataOf s 0).toScaleData.blockPartition n =
        (levelDataOf s 0).toScaleData.cubePartition
          ((levelDataOf s 0).toScaleData.levelSpacing n) := by
      unfold GeneralTorus.ScaleData.blockPartition
      rw [eside]
    rw [eidx] at e
    exact (congrArg (· '' _) hq0).trans
      (e.trans (e2.trans (cubePartition_eq_image ⟨hspos 0 n, hform⟩)))
  · intro n hn
    obtain ⟨h1, h2, h3⟩ := hcubes n (hn.trans hTt)
    have hfloor : -((s.data.m : ℕ) : ℤ) ≤
        PeriodicLattice.coarseCubeIndex s.data.cutoff s.data.blockExp n := by
      rcases s.Ω_mem.2.1.1 s.lastIdx hTt with h0 | ⟨h0, -⟩
      · exact absurd h0 hTmem.2.ne_empty
      · have h0' : -((s.data.m : ℕ) : ℤ) ≤
            ((s.data.cutoff : ℕ) : ℤ) - (s.lastIdx : ℤ) - (s.data.blockExp : ℤ) := h0
        have hn' : (n : ℤ) ≤ (s.lastIdx : ℤ) := by exact_mod_cast hn
        change -((s.data.m : ℕ) : ℤ) ≤
          ((s.data.cutoff : ℕ) : ℤ) - (n : ℤ) - (s.data.blockExp : ℤ)
        linarith
    have hle := h1.1 hfloor
    have hform : P.toScaleData.AdmitsPartition (P.toScaleData.blockLength n) :=
      ⟨mul_pos (by exact_mod_cast pow_pos (by exact_mod_cast hLpos) _) (hspos _ n), h2.1 hle⟩
    exact (congrArg (· '' _) hq).trans ((h3 hle).trans (cubePartition_eq_image hform))
  · intro n
    exact (hr _).trans ((hlay n).symm.trans (hBlayer n).symm)
  · intro n hn
    exact (congrArg (fun f : s.data.Point → _ =>
      (fun y : s.data.LatticeSite n => f (y : s.data.Point)) '' s.data.layerSitesAt s.Ω n) hread).trans
        ((hsites n hn).symm.trans (hBsites n).symm)
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨n, hn, z, hz, rfl⟩ := mem_iUnion₂.mp hy
      have hx : s.toTorus P.toScaleData.torusSide (z : s.data.Point) ∈ B.layerSites n := by
        rw [hBsites n, hsites n hn, hread]
        exact ⟨z, hz, rfl⟩
      have hnT : n ≤ s.lastIdx := by
        by_contra hgt
        rw [hBempty n (not_le.mp hgt)] at hx
        exact hx
      exact mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hnT), hx⟩
    · intro hx
      obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
      have hnT : n ≤ s.data.t := (Nat.le_of_lt_succ (Finset.mem_range.mp hn)).trans hTt
      rw [hBsites n, hsites n hnT] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      exact ⟨z, mem_iUnion₂.mpr ⟨n, hnT, z, hz, rfl⟩, congrFun hread _⟩
  · intro y
    have e := (hsite y.level y.2.1 y.site y.2.2).1
    have e' : s.toTorus P.toScaleData.torusSide y.point = P.readPoint y.point := congrFun hread _
    exact (congrArg B.siteScale e').trans ((hBspacing _).trans e)
  · intro y
    have e := (hsite y.level y.2.1 y.site y.2.2).2.1
    have e' : s.toTorus P.toScaleData.torusSide y.point = P.readPoint y.point := congrFun hread _
    exact (congrArg B.siteCube e').trans ((hBcube _).trans (e.trans (hr _).symm))
  · intro Γ
    exact (hBlength _).trans (hlen Γ)
  · intro y y'
    have e1 : s.toTorus P.toScaleData.torusSide y = P.readPoint y := congrFun hread _
    have e2 : s.toTorus P.toScaleData.torusSide y' = P.readPoint y' := congrFun hread _
    exact (congrArg ENNReal.ofReal
      ((congrArg₂ B.weightedDistance e1 e2).trans (hBdist _ _))).trans (hdist y y')
end SeparatedClasses.WeightedGeometryOfClass
end YangMills.Construction
