import YangMills.Construction.HullsInEveryVolume.ClassesOfAHullAreShort
import YangMills.Construction.LawByMomentsOfTheFlow.SeveralLongClassesOnATorusProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
open TorusFields TorusLumps RenormalizationStepParameters StepReturn WeightedResponses ResponseInTheExpansion
private theorem card_walks_le {V : Type} [Fintype V] [DecidableEq V] (R : V → V → Prop) [DecidableRel R] (A : ℕ)
    (hA : ∀ a, (Finset.univ.filter fun b => R b a).card ≤ A) (z : V) (k : ℕ) :
    (Finset.univ.filter fun f : Fin (k + 1) → V =>
        f 0 = z ∧ ∀ i : Fin k, R (f i.succ) (f i.castSucc)).card ≤ A ^ k := by apply _root_.YangMills.SharedProofs.p86552 <;> assumption
private theorem hullClass_chainConnected {n r : ℕ} [NeZero n] {Y : Finset (TorusSite n)} {z : TorusSite n} :
    ∀ a ∈ hullClass r Y z, ∀ b ∈ hullClass r Y z, ChainConnected r (hullClass r Y z) a b := by apply _root_.YangMills.SharedProofs.p95188 <;> assumption
private theorem measureReal_unitsAtDepth_le (Tb : ParameterAssignment) (y g β : ℝ) (K m : ℕ)
    (T : StageTower (Tb.stepParameters y)) (hy : Tb.floorMin ≤ y) (hDr : Tb.Admissible)
    (hP : ∀ (u n : ℕ) [NeZero n], HullChainAtLevel Tb y g β K m T u n →
      ∀ S : Finset (TorusSite n), Separated (30 * stageRange T u) S →
        (markedSampleLaw T β u n).real {w | ∀ z ∈ S, IsUnit T u n w z} ≤
          Real.exp (-(separatedUnitRate Tb * stageCoupling T u * (S.card : ℝ))))
    (hLaw : sampleBelowLawStatement) (hDraw : forgetLastStepStatement)
    (j u n : ℕ) [NeZero n] (hj : j ≤ u) (hAt : HullChainAtLevel Tb y g β K m T u n)
    (S : Finset (TorusSite (fineSide (Tb.stepParameters y).side j n)))
    (hS : Separated (30 * stageRange T (u - j)) S) :
    (markedSampleLaw T β u n).real {w | UnitsAtDepth T j u n w S} ≤
      Real.exp (-(separatedUnitRate Tb * stageCoupling T (u - j) * (S.card : ℝ))) := by apply _root_.YangMills.SharedProofs.p38694 <;> assumption
private theorem minLeafCountScaled_bounds (L j m : ℕ) (hL : 1600 ≤ L) (hm : 1 ≤ m) :
    1 ≤ minLeafCountScaled L j m ∧ (m : ℝ) ≤ 12 * (minLeafCountScaled L j m : ℝ) := by apply _root_.YangMills.SharedProofs.p73794 <;> assumption
private theorem walk_term_le (c4 C lL lj lx x' N : ℝ) (r : ℕ) (k : ℕ) (hr : 1 ≤ r) (hN : 0 ≤ N)
    (hkN : ((k : ℝ) + 1) ≤ 12 * N)
    (hF : C * (1 + lj) * (lL + lx) + 48 * Real.log (83 * (r : ℝ)) + 12 ≤ c4 * x' / 2) :
    (((83 * r) ^ 4) ^ k : ℕ) * ((2 : ℝ) ^ (k + 1) * Real.exp (C * N * (1 + lj) * (lL + lx)) *
      Real.exp (-(c4 * x' * N))) ≤ Real.exp (-(c4 * x' * N / 2)) := by apply _root_.YangMills.SharedProofs.p9637 <;> assumption
private theorem sum_over_depths_le (c4 lam c y xu E : ℝ) (u : ℕ) (x' N : ℕ → ℝ) (hc4 : 0 < c4) (hlam : 0 < lam)
    (hN : ∀ j, j ≤ u → 1 ≤ N j) (hE : ∀ j, j ≤ u → E ≤ c4 * xu * N j / 10) (hxu : y ≤ xu)
    (hs : ∀ j, j ≤ u → xu + lam * j - c ≤ x' j) (hy : 0 ≤ 2 / 5 * y - c / 2)
    (hq : Real.exp (-(c4 * (2 / 5 * y - c / 2))) ≤ 1 - Real.exp (-(c4 * lam / 2))) :
    ∑ j ∈ Finset.range (u + 1), Real.exp (-(c4 * x' j * N j / 2)) ≤ Real.exp (-E) := by apply _root_.YangMills.SharedProofs.p32958 <;> assumption
private theorem exists_floor_log_sq_le (C lL c lam c4 : ℝ) (hlam : 0 < lam) (hc : 0 ≤ c) (hc4 : 0 < c4)
    (hlL : 0 ≤ lL) :
    ∃ y₀ : ℝ, ∀ x : ℝ, y₀ ≤ x → ∀ j : ℕ, (j : ℝ) ≤ (x + c) / lam →
      C * (1 + Real.log ((j : ℝ) + 1)) * (lL + Real.log x) +
        48 * Real.log (83 * ((x + c) ^ ((1 : ℝ) / 100) + 1)) + 12 ≤ c4 * x / 2 := by apply _root_.YangMills.SharedProofs.p12277 <;> assumption
private theorem couplingFlow_ge_of_flowCrossing (Tb : ParameterAssignment) (y g β : ℝ) (K : ℕ)
    (h : FlowCrossing Tb y g β K) (hB : 0 ≤ Tb.B)
    (hRet : ExpansionReturnsAt (Tb.stepParameters y))
    (hRow : HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β)) :
    ∀ u ≤ K, y ≤ (couplingFlow (Tb.stepParameters y) β u).1 := by apply _root_.YangMills.SharedProofs.p87009 <;> assumption
private theorem measureReal_long_hullClass_le (Tb : ParameterAssignment) (y g β : ℝ) (K m : ℕ)
    (T : StageTower (Tb.stepParameters y)) (u n : ℕ) [NeZero n]
    (hAt : HullChainAtLevel Tb y g β K m T u n) (z : TorusSite n) (D : ℝ) (hD : 0 ≤ D)
    (hy : Tb.floorMin ≤ y) (hy1 : 1 ≤ y) (hDr : Tb.Admissible)
    (hSites : sitesAlongHullClassStatement) (C₁ : ℝ)
    (hUnits : ∀ mm : ℕ, 1 ≤ mm → ∃ F : (Fin mm → TorusSite n) → (j : ℕ) →
        Finset (Finset (TorusSite (fineSide (Tb.stepParameters y).side j n))),
      ∀ ys : Fin mm → TorusSite n, (∀ i i', i ≠ i' → 40 * stageRange T u ≤ supDist (ys i) (ys i')) →
        (∀ j ≤ u, ((F ys j).card : ℝ) ≤ 2 ^ mm * Real.exp (C₁ *
            (minLeafCountScaled (Tb.stepParameters y).side j mm : ℝ) *
            (1 + Real.log ((j : ℝ) + 1)) *
            (Real.log ((Tb.stepParameters y).side : ℝ) + Real.log (stageCoupling T (u - j)))) ∧
          ∀ S ∈ F ys j, S.card = minLeafCountScaled (Tb.stepParameters y).side j mm) ∧
        ∀ w : MarkedSample (Tb.stepParameters y) u n, (∀ i, ys i ∈ hullSet T u n w) →
          ∃ j ≤ u, ∃ S ∈ F ys j, UnitsAtDepth T j u n w S ∧ Separated (30 * stageRange T (u - j)) S)
    (hP : ∀ (u n : ℕ) [NeZero n], HullChainAtLevel Tb y g β K m T u n →
      ∀ S : Finset (TorusSite n), Separated (30 * stageRange T u) S →
        (markedSampleLaw T β u n).real {w | ∀ z ∈ S, IsUnit T u n w z} ≤
          Real.exp (-(separatedUnitRate Tb * stageCoupling T u * (S.card : ℝ))))
    (hLaw : sampleBelowLawStatement) (hDraw : forgetLastStepStatement)
    (lam c : ℝ) (hlam : 0 < lam)
    (hslope : ∀ j ≤ u, lam * (j : ℝ) - c ≤ stageCoupling T (u - j) - stageCoupling T u)
    (hfloor : ∀ i ≤ K, y ≤ stageCoupling T i)
    (hlogsq : ∀ x : ℝ, y ≤ x → ∀ j : ℕ, (j : ℝ) ≤ (x + c) / lam →
      C₁ * (1 + Real.log ((j : ℝ) + 1)) * (Real.log ((Tb.stepParameters y).side : ℝ) + Real.log x) +
        48 * Real.log (83 * ((x + c) ^ ((1 : ℝ) / 100) + 1)) + 12 ≤ separatedUnitRate Tb * x / 2)
    (hc4 : 0 < separatedUnitRate Tb)
    (hyc : 0 ≤ 2 / 5 * y - c / 2)
    (hq : Real.exp (-(separatedUnitRate Tb * (2 / 5 * y - c / 2))) ≤
      1 - Real.exp (-(separatedUnitRate Tb * lam / 2))) :
    (markedSampleLaw T β u n).real {w | z ∈ hullSet T u n w ∧
        D ≤ (supDiam (hullClass (stageRange T u) (hullSet T u n w) z) : ℝ)} ≤
      Real.exp (-(hullDecayRate Tb * stageCoupling T u * (1 + D / (stageRange T u : ℝ)))) := by
  classical
  have hfit : (Tb.stepParameters y).Admissible := hDr.fits y hy
  have hgt : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side := hDr.L_gt
  have : IsProbabilityMeasure (markedSampleLaw T β u n) :=
    (hDraw _ hfit hgt T hAt.chain.cutoff_bottom hAt.chain.marks β u n).1
  have hLbig : 1600 ≤ (Tb.stepParameters y).side := by
    have : 2 ^ 40 ≤ Tb.side := hDr.L_ge
    have h2 : (Tb.stepParameters y).side = Tb.side := rfl
    rw [h2]
    omega
  have hxu : y ≤ stageCoupling T u := hfloor u hAt.le
  have hxu0 : 0 < stageCoupling T u := by linarith
  set r := stageRange T u with hrdef
  have hr1 : 1 ≤ r := Nat.ceil_pos.2 (Real.rpow_pos_of_pos hxu0 _)
  have hmm : ⌈D / (82 * (r : ℝ))⌉₊ ≤ max 1 ⌈D / (82 * (r : ℝ))⌉₊ := le_max_right _ _
  obtain ⟨k, hk⟩ : ∃ k, max 1 ⌈D / (82 * (r : ℝ))⌉₊ = k + 1 :=
    ⟨max 1 ⌈D / (82 * (r : ℝ))⌉₊ - 1, by have := le_max_left 1 ⌈D / (82 * (r : ℝ))⌉₊; omega⟩
  obtain ⟨F, hF⟩ := hUnits (k + 1) (by omega)
  set N : ℕ → ℕ := fun j => minLeafCountScaled (Tb.stepParameters y).side j (k + 1) with hNdef
  have hNb : ∀ j, 1 ≤ N j ∧ ((k + 1 : ℕ) : ℝ) ≤ 12 * (N j : ℝ) := fun j =>
    minLeafCountScaled_bounds _ j (k + 1) hLbig (by omega)
  let Tup : Finset (Fin (k + 1) → TorusSite n) := Finset.univ.filter fun f =>
    (f 0 = z ∧ ∀ i : Fin k, supDist (f i.succ) (f i.castSucc) < 41 * r) ∧
      ∀ i i', i ≠ i' → 40 * r ≤ supDist (f i) (f i')
  have hnbr : ∀ a : TorusSite n,
      (Finset.univ.filter fun b : TorusSite n => supDist b a < 41 * r).card ≤ (83 * r) ^ 4 := by
    intro a
    have hone := (hSites n r {a} a 0 hr1 le_rfl (Finset.mem_singleton_self a)
      (fun p hp q hq => by
        rw [Finset.mem_singleton.1 hp, Finset.mem_singleton.1 hq]
        exact Relation.ReflTransGen.refl) (by simp)).2
    convert hone
  have hTup : Tup.card ≤ ((83 * r) ^ 4) ^ k := by
    refine le_trans (Finset.card_le_card ?_)
      (card_walks_le (fun a b : TorusSite n => supDist a b < 41 * r) _ hnbr z k)
    intro f hf
    simp only [Tup, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    exact hf.1
  let G : (Fin (k + 1) → TorusSite n) → (j : ℕ) →
      Finset (Finset (TorusSite (fineSide (Tb.stepParameters y).side j n))) :=
    fun f j => (F f j).filter fun S => Separated (30 * stageRange T (u - j)) S
  let Ev : (j : ℕ) → Finset (TorusSite (fineSide (Tb.stepParameters y).side j n)) →
      Set (MarkedSample (Tb.stepParameters y) u n) :=
    fun j S => {w | UnitsAtDepth T j u n w S}
  have hcover : {w | z ∈ hullSet T u n w ∧ D ≤ (supDiam (hullClass r (hullSet T u n w) z) : ℝ)} ⊆
      ⋃ f ∈ Tup, ⋃ j ∈ Finset.range (u + 1), ⋃ S ∈ G f j, Ev j S := by
    rintro w ⟨hz, hdiam⟩
    obtain ⟨⟨ys, h0, hin, hap, hnear⟩, -⟩ := hSites n r (hullClass r (hullSet T u n w) z) z D hr1 hD
      (Finset.mem_filter.2 ⟨hz, Relation.ReflTransGen.refl⟩) hullClass_chainConnected hdiam
    rw [hk] at hin hap hnear
    have hfT : (fun i : Fin (k + 1) => ys i) ∈ Tup := by
      simp only [Tup, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨by simpa using h0, fun i => ?_⟩, fun i i' hii => ?_⟩
      · have := hnear i (by omega)
        simpa [Fin.val_succ] using this
      · exact hap i i.2 i' i'.2 (fun h => hii (Fin.ext h))
    have hpair : ∀ i i' : Fin (k + 1), i ≠ i' → 40 * r ≤ supDist (ys i) (ys i') :=
      fun i i' hii => hap i i.2 i' i'.2 (fun h => hii (Fin.ext h))
    obtain ⟨j, hj, S, hS, hUB, hAp⟩ := (hF _ hpair).2 w
      (fun i => (Finset.mem_filter.1 (hin i i.2)).1)
    simp only [Set.mem_iUnion]
    exact ⟨_, hfT, j, Finset.mem_range.2 (by omega), S, Finset.mem_filter.2 ⟨hS, hAp⟩, hUB⟩
  let b : ℕ → ℝ := fun j => (2 : ℝ) ^ (k + 1) * Real.exp (C₁ * (N j : ℝ) * (1 + Real.log ((j : ℝ) + 1)) *
      (Real.log ((Tb.stepParameters y).side : ℝ) + Real.log (stageCoupling T (u - j)))) *
      Real.exp (-(separatedUnitRate Tb * stageCoupling T (u - j) * (N j : ℝ)))
  have hb0 : ∀ j, 0 ≤ b j := fun j => by positivity
  have hlevel : ∀ f ∈ Tup, ∀ j ∈ Finset.range (u + 1),
      (markedSampleLaw T β u n).real (⋃ S ∈ G f j, Ev j S) ≤ b j := by
    intro f hf j hj
    have hj' : j ≤ u := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hfp : ∀ i i' : Fin (k + 1), i ≠ i' → 40 * stageRange T u ≤ supDist (f i) (f i') := by
      have := (Finset.mem_filter.1 hf).2.2
      exact this
    obtain ⟨hcard, hsz⟩ := (hF f hfp).1 j hj'
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    have hone : ∀ S ∈ G f j, (markedSampleLaw T β u n).real (Ev j S) ≤
        Real.exp (-(separatedUnitRate Tb * stageCoupling T (u - j) * (N j : ℝ))) := by
      intro S hS
      obtain ⟨hSF, hSA⟩ := Finset.mem_filter.1 hS
      have := measureReal_unitsAtDepth_le Tb y g β K m T hy hDr hP hLaw hDraw j u n hj' hAt S hSA
      rwa [hsz S hSF] at this
    refine (Finset.sum_le_sum hone).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have hG : ((G f j).card : ℝ) ≤ ((F f j).card : ℝ) := by
      exact_mod_cast Finset.card_filter_le _ _
    exact hG.trans hcard
  have hsumall : (markedSampleLaw T β u n).real
      {w | z ∈ hullSet T u n w ∧ D ≤ (supDiam (hullClass r (hullSet T u n w) z) : ℝ)} ≤
      (Tup.card : ℝ) * ∑ j ∈ Finset.range (u + 1), b j := by
    refine (measureReal_mono hcover (measure_ne_top _ _)).trans ?_
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    have : ∀ f ∈ Tup, (markedSampleLaw T β u n).real
        (⋃ j ∈ Finset.range (u + 1), ⋃ S ∈ G f j, Ev j S) ≤ ∑ j ∈ Finset.range (u + 1), b j := by
      intro f hf
      exact (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum (hlevel f hf))
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  refine hsumall.trans ?_
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range (u + 1), b j := Finset.sum_nonneg fun j _ => hb0 j
  have hTupR : (Tup.card : ℝ) ≤ (((83 * r) ^ 4) ^ k : ℕ) := by exact_mod_cast hTup
  refine (mul_le_mul_of_nonneg_right hTupR hsum0).trans ?_
  rw [Finset.mul_sum]
  have hslope' : ∀ j ≤ u, stageCoupling T u + lam * (j : ℝ) - c ≤ stageCoupling T (u - j) := fun j hj => by
    have := hslope j hj
    linarith
  have hterm : ∀ j ∈ Finset.range (u + 1), (((83 * r) ^ 4) ^ k : ℕ) * b j ≤
      Real.exp (-(separatedUnitRate Tb * stageCoupling T (u - j) * (N j : ℝ) / 2)) := by
    intro j hj
    have hj' : j ≤ u := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hx' : y ≤ stageCoupling T (u - j) := hfloor _ (by have := hAt.le; omega)
    have hs := hslope j hj'
    have hjR : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjx : (j : ℝ) ≤ (stageCoupling T (u - j) + c) / lam := by
      rw [le_div_iff₀ hlam]
      nlinarith
    have hf := hlogsq _ hx' j hjx
    have hrR' : (r : ℝ) ≤ (stageCoupling T (u - j) + c) ^ ((1 : ℝ) / 100) + 1 := by
      have h1 : (r : ℝ) ≤ stageCoupling T u ^ ((1 : ℝ) / 100) + 1 :=
        (Nat.ceil_lt_add_one (Real.rpow_nonneg hxu0.le _)).le
      have h2 : stageCoupling T u ≤ stageCoupling T (u - j) + c := by
        have := mul_nonneg hlam.le hjR
        linarith
      have h3 := Real.rpow_le_rpow hxu0.le h2 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 100)
      linarith
    have hlog : Real.log (83 * (r : ℝ)) ≤
        Real.log (83 * ((stageCoupling T (u - j) + c) ^ ((1 : ℝ) / 100) + 1)) :=
      Real.log_le_log (by positivity) (by linarith)
    refine walk_term_le (separatedUnitRate Tb) C₁ _ _ _ _ _ r k hr1 (Nat.cast_nonneg _) ?_ ?_
    · have := (hNb j).2
      push_cast at this
      exact this
    · linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  refine sum_over_depths_le (separatedUnitRate Tb) lam c y (stageCoupling T u) _ u
    (fun j => stageCoupling T (u - j))
    (fun j => (N j : ℝ)) hc4 hlam (fun j _ => by exact_mod_cast (hNb j).1) ?_ hxu hslope' hyc hq
  intro j _
  have hN12 := (hNb j).2
  push_cast at hN12
  have hD82 : D / (r : ℝ) ≤ 82 * ((k : ℝ) + 1) := by
    have h1 : D / (82 * (r : ℝ)) ≤ (⌈D / (82 * (r : ℝ))⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈D / (82 * (r : ℝ))⌉₊ : ℝ) ≤ (k : ℝ) + 1 := by
      rw [hk] at hmm
      exact_mod_cast hmm
    have h3 : D / (r : ℝ) = 82 * (D / (82 * (r : ℝ))) := by
      field_simp
    rw [h3]
    linarith
  have hone : 1 + D / (r : ℝ) ≤ 996 * (N j : ℝ) := by nlinarith
  have hrate : hullDecayRate Tb ≤ separatedUnitRate Tb / 10 ^ 4 := min_le_left _ _
  calc hullDecayRate Tb * stageCoupling T u * (1 + D / (r : ℝ))
      ≤ separatedUnitRate Tb / 10 ^ 4 * stageCoupling T u * (996 * (N j : ℝ)) := by gcongr
    _ ≤ separatedUnitRate Tb * stageCoupling T u * (N j : ℝ) / 10 := by
        have : 0 ≤ separatedUnitRate Tb * stageCoupling T u * (N j : ℝ) := by positivity
        nlinarith
theorem hullClassDiameterTail (hSites : sitesAlongHullClassStatement)
    (hU : UnitsOfSeparatedHullSites) (hP : separatedUnitsBoundStatement)
    (hSl : FlowDescendsLinearly) (hLaw : sampleBelowLawStatement)
    (hDraw : forgetLastStepStatement) : hullClassDiameterTailStatement := by
  obtain ⟨C₁, hU⟩ := hU
  intro a ha
  obtain ⟨L₁, r₁, Cd₁, hr₁, H₁⟩ := hU a ha
  obtain ⟨L₂, r₂, Cd₂, hr₂, H₂⟩ := hP a ha
  obtain ⟨L₃, r₃, hr₃, H₃⟩ := hSl a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (r₁ c) (min (r₂ c) (r₃ c)), max Cd₁ Cd₂,
    fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (hr₃ c)), ?_⟩
  intro L hodd hL Tb hTa hTL hDr hCold hOn hrt hCd
  have hL1 : L₁ ≤ L := (le_max_left _ _).trans hL
  have hL2 : L₂ ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hL3 : L₃ ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  have hrt1 : Tb.rt ≤ r₁ Tb.toChainParameters := hrt.trans (min_le_left _ _)
  have hrt2 : Tb.rt ≤ r₂ Tb.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrt3 : Tb.rt ≤ r₃ Tb.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨lam, c₅, hlam, H₃⟩ := H₃ L hodd hL3
  obtain ⟨y₃, H₃⟩ := H₃ Tb hTa hTL hDr hrt3
  obtain ⟨M₁, H₁⟩ := H₁ L hodd hL1 Tb hTa hTL hDr hCold hOn hrt1 ((le_max_left _ _).trans hCd)
  obtain ⟨M₂, H₂⟩ := H₂ L hodd hL2 Tb hTa hTL hDr hCold hOn hrt2 ((le_max_right _ _).trans hCd)
  refine ⟨max M₁ M₂, fun Kr hM hη hN hfit hResp => ?_⟩
  obtain ⟨y₁, H₁⟩ := H₁ Kr ((le_max_left _ _).trans hM) hη hN hfit hResp
  obtain ⟨y₂, H₂⟩ := H₂ Kr ((le_max_right _ _).trans hM) hη hN hfit hResp
  have hLpos : (1 : ℝ) ≤ ((Tb.stepParameters 0).side : ℝ) := by
    have : 2 ^ 40 ≤ Tb.side := hDr.L_ge
    have h1 : 1 ≤ Tb.side := le_trans (by norm_num) this
    exact_mod_cast h1
  have hc4 : 0 < separatedUnitRate Tb := by
    have hκ := hDr.κ_pos
    have hσ := hDr.σ_pos
    have hcE := hDr.cE_pos
    have hLp : (0 : ℝ) < (Tb.side : ℝ) := by
      have : (1 : ℝ) ≤ (Tb.side : ℝ) := hLpos
      linarith
    unfold separatedUnitRate unitDecayRate
    have : 0 < min (Tb.κ * Tb.threshold ^ 2) Tb.cE := lt_min (by positivity) hcE
    positivity
  set c := max c₅ 0 with hcdef
  have hc : 0 ≤ c := le_max_right _ _
  set q := Real.exp (-(separatedUnitRate Tb * lam / 2)) with hqd
  have hq1 : q < 1 := by
    rw [hqd, Real.exp_lt_one_iff]
    have : 0 < separatedUnitRate Tb * lam / 2 := by positivity
    linarith
  have hq0 : 0 < q := Real.exp_pos _
  have hlq : 0 ≤ -Real.log (1 - q) := by
    have := Real.log_nonpos (by linarith : (0 : ℝ) ≤ 1 - q) (by linarith : 1 - q ≤ 1)
    linarith
  obtain ⟨y₄, H₄⟩ := exists_floor_log_sq_le (C₁ (Tb.stepParameters 0).side)
    (Real.log ((Tb.stepParameters 0).side : ℝ)) c lam
    (separatedUnitRate Tb) hlam hc hc4 (Real.log_nonneg hLpos)
  refine ⟨max (max y₁ y₂) (max y₃ (max Tb.floorMin (max y₄
      (5 / 2 * (c / 2 + -Real.log (1 - q) / separatedUnitRate Tb))))),
    fun y hy hRet hRow => ?_⟩
  have hy1' : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy2' : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy3' : y₃ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy0' : Tb.floorMin ≤ y :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have hy4' : y₄ ≤ y :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hy
  have hy5' : 5 / 2 * (c / 2 + -Real.log (1 - q) / separatedUnitRate Tb) ≤ y :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hy
  have hfit' : (Tb.stepParameters y).Admissible := hDr.fits y hy0'
  have hyone : 1 ≤ y := hfit'.y₁_ge
  have hlq2 : 0 ≤ -Real.log (1 - q) / separatedUnitRate Tb := div_nonneg hlq hc4.le
  have hyc : 0 ≤ 2 / 5 * y - c / 2 := by linarith
  have hq' : Real.exp (-(separatedUnitRate Tb * (2 / 5 * y - c / 2))) ≤ 1 - q := by
    have h1 : -Real.log (1 - q) ≤ separatedUnitRate Tb * (2 / 5 * y - c / 2) := by
      have h2 : -Real.log (1 - q) / separatedUnitRate Tb ≤ 2 / 5 * y - c / 2 := by linarith
      rwa [div_le_iff₀ hc4, mul_comm] at h2
    calc Real.exp (-(separatedUnitRate Tb * (2 / 5 * y - c / 2))) ≤ Real.exp (Real.log (1 - q)) :=
          Real.exp_le_exp.2 (by linarith)
      _ = 1 - q := Real.exp_log (by linarith)
  have hslopeAll := H₃ y hy3' hRet hRow
  intro g β K m T u n _ hAt z D hD
  have hchain := hAt.chain
  have hβ : y ≤ β := by
    have h1 := hchain.toCrossingVolume.toFlowCrossing.le_inv_sq
    have h2 := hchain.toCrossingVolume.toFlowCrossing.upper_le
    have h3 : windowUpper (Tb.stepParameters y) g = (g ^ 2)⁻¹ + 2 * Tb.B := rfl
    have hB := hDr.B_ge
    linarith
  have hstay := couplingFlow_ge_of_flowCrossing Tb y g β K hchain.toCrossingVolume.toFlowCrossing
    (by linarith [hDr.B_ge]) hRet (hRow β hβ)
  have hcoup : ∀ i ≤ K, stageCoupling T i = (couplingFlow (Tb.stepParameters y) β i).1 := fun i hi =>
    hchain.follows i (by omega)
  have hfloor : ∀ i ≤ K, y ≤ stageCoupling T i := fun i hi => by
    rw [hcoup i hi]
    exact hstay i hi
  have hslope : ∀ j ≤ u, lam * (j : ℝ) - c ≤ stageCoupling T (u - j) - stageCoupling T u := by
    intro j hj
    have hu := hAt.le
    have := hslopeAll β hβ u (fun k hk => hstay k (by omega)) (u - j) (by omega)
    rw [hcoup _ (by omega), hcoup _ hu]
    have e : ((u : ℝ) - ((u - j : ℕ) : ℝ)) = j := by
      rw [Nat.cast_sub hj]
      ring
    rw [e] at this
    have : c₅ ≤ c := le_max_left _ _
    linarith
  exact measureReal_long_hullClass_le Tb y g β K m T u n hAt z D hD hy0' hyone hDr hSites
    (C₁ (Tb.stepParameters y).side)
    (H₁ y hy1' hRet hRow g β K m T u n hAt) (H₂ y hy2' hRet hRow g β K m T) hLaw hDraw lam c hlam hslope hfloor
    (fun x hx j hj => H₄ x (hy4'.trans hx) j hj) hc4 hyc hq'
end YangMills.Construction.HullTrees
end
