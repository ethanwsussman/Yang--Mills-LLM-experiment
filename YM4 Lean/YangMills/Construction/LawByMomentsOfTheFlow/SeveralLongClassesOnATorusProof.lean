import YangMills.Construction.CellOfTheFlow.AFalseSiteHoldsALongClassProof
import YangMills.Construction.HullsInEveryVolume.SitesAlongAClass
import YangMills.Construction.HullsInEveryVolume.UnitsInSeparatePlaces
import YangMills.Construction.HullsInEveryVolume.UnitsOfSeveralSitesOfAHull
import YangMills.Construction.LawByMomentsOfTheFlow.SeveralLongClassesOnATorus
import YangMills.Construction.ResponseInTheExpansion.LawOfTheDrawsBelow
import YangMills.Construction.ResponseInTheExpansion.RunningCouplingSlope
import YangMills.Construction.ResponseInTheExpansion.TheDrawBelowHasItsLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open HullTrees TorusFields TorusLumps WeightedResponses RenormalizationStepParameters
private theorem card_paths_le {V : Type} [Fintype V] [DecidableEq V] (R : V → V → Prop) [DecidableRel R] (A : ℕ)
    (hA : ∀ a, (Finset.univ.filter fun b => R b a).card ≤ A) (z : V) (k : ℕ) :
    (Finset.univ.filter fun f : Fin (k + 1) → V =>
        f 0 = z ∧ ∀ i : Fin k, R (f i.succ) (f i.castSucc)).card ≤ A ^ k := by
  induction k with
  | zero =>
    have hsub : (Finset.univ.filter fun f : Fin 1 → V =>
        f 0 = z ∧ ∀ i : Fin 0, R (f i.succ) (f i.castSucc)) ⊆ {fun _ => z} := by
      intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      simp only [Finset.mem_singleton]
      funext i
      rw [Subsingleton.elim i 0]
      exact hf.1
    simpa using Finset.card_le_card hsub
  | succ k ih =>
    set P := Finset.univ.filter fun f : Fin (k + 1) → V =>
      f 0 = z ∧ ∀ i : Fin k, R (f i.succ) (f i.castSucc) with hP
    have hsub : (Finset.univ.filter fun f : Fin (k + 1 + 1) → V =>
        f 0 = z ∧ ∀ i : Fin (k + 1), R (f i.succ) (f i.castSucc)) ⊆
        P.biUnion fun g => (Finset.univ.filter fun b => R b (g (Fin.last k))).image
          fun a => (Fin.snoc (α := fun _ => V) g a : Fin (k + 1 + 1) → V) := by
      intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      obtain ⟨h0, hR⟩ := hf
      refine Finset.mem_biUnion.2 ⟨Fin.init f, ?_, Finset.mem_image.2
        ⟨f (Fin.last (k + 1)), ?_, Fin.snoc_init_self f⟩⟩
      · simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, fun i => ?_⟩
        · exact h0
        · have := hR i.castSucc
          have e : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
          rw [e] at this
          exact this
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hR (Fin.last k)
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ P.card * A := Finset.card_biUnion_le_card_mul _ _ _ fun g _ =>
          Finset.card_image_le.trans (hA _)
      _ ≤ A ^ k * A := Nat.mul_le_mul_right _ ih
      _ = A ^ (k + 1) := (pow_succ A k).symm
abbrev _root_.YangMills.SharedProofs.p86552 := @card_paths_le
private theorem chainConnected_swap {n r : ℕ} [NeZero n] {Y : Finset (TorusSite n)} {a b : TorusSite n}
    (h : ChainConnected r Y a b) : ChainConnected r Y b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, by rw [supDist_comm]; exact hbc.2.2⟩ ih
private theorem chainConnected_in_hullClass {n r : ℕ} {Y : Finset (TorusSite n)} {z a : TorusSite n}
    (h : ChainConnected r Y z a) : ChainConnected r (hullClass r Y z) z a := by
  classical
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    refine ih.tail ⟨?_, ?_, hbc.2.2⟩
    · exact Finset.mem_filter.2 ⟨hbc.1, hab⟩
    · exact Finset.mem_filter.2 ⟨hbc.2.1, hab.tail hbc⟩
private theorem hullClass_chainConnected {n r : ℕ} [NeZero n] {Y : Finset (TorusSite n)} {z : TorusSite n} :
    ∀ a ∈ hullClass r Y z, ∀ b ∈ hullClass r Y z, ChainConnected r (hullClass r Y z) a b := by
  classical
  intro a ha b hb
  exact (chainConnected_swap (chainConnected_in_hullClass (Finset.mem_filter.1 ha).2)).trans
    (chainConnected_in_hullClass (Finset.mem_filter.1 hb).2)
abbrev _root_.YangMills.SharedProofs.p95188 := @hullClass_chainConnected
private theorem unitsAtDepth_iff {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) (s : ℕ) :
    ∀ (j n : ℕ) [NeZero n] (w : MarkedSample ℓ (s + j) n) (S : Finset (TorusSite (fineSide ℓ.side j n))),
      UnitsAtDepth T j (s + j) n w S ↔
        ∀ z ∈ S, HullTrees.IsUnit T s (fineSide ℓ.side j n) (ResponseInTheExpansion.sampleBelow ℓ s j n w) z
  | 0, _, _, _, _ => Iff.rfl
  | j + 1, n, _, w, S => unitsAtDepth_iff T s j (n * ℓ.side) w.1 S
private theorem fineSide_eq_torusSideAtLevel {L K m s j n : ℕ} (hn : n = torusSideAtLevel L K m (s + j))
    (h : s + j ≤ K) : fineSide L j n = torusSideAtLevel L K m s := by
  subst hn
  simp only [torusSideAtLevel, fineSide_eq]
  have : K - s = (K - (s + j)) + j := by omega
  rw [this, pow_add, mul_assoc]
private theorem measure_unitsAtDepth_le (Tb : ParameterAssignment) (y g β : ℝ) (K m : ℕ)
    (T : StageTower (Tb.stepParameters y)) (hy : Tb.floorMin ≤ y) (hDr : Tb.Admissible)
    (hP : ∀ (u n : ℕ) [NeZero n], HullChainAtLevel Tb y g β K m T u n →
      ∀ S : Finset (TorusSite n), HullTrees.Separated (30 * stageRange T u) S →
        (markedSampleLaw T β u n).real {w | ∀ z ∈ S, HullTrees.IsUnit T u n w z} ≤
          Real.exp (-(separatedUnitRate Tb * stageCoupling T u * (S.card : ℝ))))
    (hLaw : ResponseInTheExpansion.sampleBelowLawStatement) (hDraw : forgetLastStepStatement)
    (j u n : ℕ) [NeZero n] (hj : j ≤ u) (hAt : HullChainAtLevel Tb y g β K m T u n)
    (S : Finset (TorusSite (fineSide (Tb.stepParameters y).side j n)))
    (hS : HullTrees.Separated (30 * stageRange T (u - j)) S) :
    (markedSampleLaw T β u n).real {w | UnitsAtDepth T j u n w S} ≤
      Real.exp (-(separatedUnitRate Tb * stageCoupling T (u - j) * (S.card : ℝ))) := by
  obtain ⟨s, rfl⟩ : ∃ s, u = s + j := ⟨u - j, by omega⟩
  simp only [Nat.add_sub_cancel] at hS ⊢
  have hfit : (Tb.stepParameters y).Admissible := hDr.fits y hy
  have hgt : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side := hDr.L_gt
  have hcut := hAt.chain.cutoff_bottom
  have hcoins := hAt.chain.marks
  obtain ⟨hm, hmap⟩ := (hLaw _ hfit hgt T hcut hcoins β (fun _ => 0)).1 s j n
  have := (hDraw _ hfit hgt T hcut hcoins β s (fineSide (Tb.stepParameters y).side j n)).1
  have hAt' : HullChainAtLevel Tb y g β K m T s (fineSide (Tb.stepParameters y).side j n) :=
    ⟨hAt.chain, by have := hAt.le; omega, fineSide_eq_torusSideAtLevel hAt.side_eq hAt.le⟩
  have hset : {w | UnitsAtDepth T j (s + j) n w S} = ResponseInTheExpansion.sampleBelow (Tb.stepParameters y) s j n ⁻¹'
      {w' | ∀ z ∈ S, HullTrees.IsUnit T s (fineSide (Tb.stepParameters y).side j n) w' z} := by
    ext w
    exact unitsAtDepth_iff T s j n w S
  rw [hset]
  refine le_trans ?_ (hP s _ hAt' S hS)
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  rw [← hmap]
  exact Measure.le_map_apply hm.aemeasurable _
abbrev _root_.YangMills.SharedProofs.p38694 := @measure_unitsAtDepth_le
private theorem minLeafCountScaled_bounds (L j m : ℕ) (hL : 1600 ≤ L) (hm : 1 ≤ m) :
    1 ≤ minLeafCountScaled L j m ∧ (m : ℝ) ≤ 12 * (minLeafCountScaled L j m : ℝ) := by
  have hθ : 0 < levelWeight j := by unfold levelWeight; positivity
  have hk : 16 ≤ treeBranching L := by unfold treeBranching; omega
  have ha1 : max 1 (levelWeight j * (treeBranching L : ℝ) ^ j) ≤ (minLeafCount L j : ℝ) := Nat.le_ceil _
  have hb : levelWeight j * (m : ℝ) ≤ (⌈levelWeight j * (m : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hbpos : 0 < ⌈levelWeight j * (m : ℝ)⌉₊ := Nat.ceil_pos.2 (by positivity)
  have hapos : 0 < minLeafCount L j := by
    have : (1 : ℝ) ≤ (minLeafCount L j : ℝ) := (le_max_left _ _).trans ha1
    exact_mod_cast (by linarith : (0 : ℝ) < (minLeafCount L j : ℝ))
  refine ⟨Nat.mul_pos hapos hbpos, ?_⟩
  have hkj : ((j : ℝ) + 1) ^ 4 ≤ (treeBranching L : ℝ) ^ j := by
    have h2 : (j : ℝ) + 1 ≤ 2 ^ j := by
      have : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
      exact_mod_cast this
    have h16 : (16 : ℝ) ≤ treeBranching L := by exact_mod_cast hk
    calc ((j : ℝ) + 1) ^ 4 ≤ ((2 : ℝ) ^ j) ^ 4 := by gcongr
      _ = (16 : ℝ) ^ j := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ (treeBranching L : ℝ) ^ j := by gcongr
  have hpi : Real.pi ^ 4 ≤ 108 := by
    have h1 : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
    calc Real.pi ^ 4 ≤ (3.15 : ℝ) ^ 4 := by gcongr
      _ ≤ 108 := by norm_num
  have hθ2 : 1 ≤ 12 * (levelWeight j * (levelWeight j * (treeBranching L : ℝ) ^ j)) := by
    have hj1 : (0 : ℝ) < ((j : ℝ) + 1) ^ 4 := by positivity
    have hπ : 0 < Real.pi ^ 4 := by positivity
    have e : levelWeight j * levelWeight j = 9 / Real.pi ^ 4 / ((j : ℝ) + 1) ^ 4 := by
      unfold levelWeight
      field_simp
      ring
    have : 1 ≤ 108 / Real.pi ^ 4 := by rw [le_div_iff₀ hπ]; linarith
    calc (1 : ℝ) ≤ 108 / Real.pi ^ 4 * (((treeBranching L : ℝ) ^ j) / ((j : ℝ) + 1) ^ 4) := by
          have : 1 ≤ ((treeBranching L : ℝ) ^ j) / ((j : ℝ) + 1) ^ 4 := by rw [le_div_iff₀ hj1]; linarith
          nlinarith
      _ = 12 * (levelWeight j * levelWeight j * (treeBranching L : ℝ) ^ j) := by rw [e]; ring
      _ = _ := by ring
  have hN : (minLeafCountScaled L j m : ℝ) = (minLeafCount L j : ℝ) * (⌈levelWeight j * (m : ℝ)⌉₊ : ℝ) := by
    unfold minLeafCountScaled; push_cast; ring
  have ha2 : levelWeight j * (treeBranching L : ℝ) ^ j ≤ (minLeafCount L j : ℝ) := (le_max_right _ _).trans ha1
  rw [hN]
  calc (m : ℝ) ≤ 12 * (levelWeight j * (levelWeight j * (treeBranching L : ℝ) ^ j)) * m := by nlinarith
    _ = 12 * ((levelWeight j * (treeBranching L : ℝ) ^ j) * (levelWeight j * m)) := by ring
    _ ≤ 12 * ((minLeafCount L j : ℝ) * (⌈levelWeight j * (m : ℝ)⌉₊ : ℝ)) := by
        have : 0 ≤ levelWeight j * (m : ℝ) := by positivity
        gcongr
abbrev _root_.YangMills.SharedProofs.p73794 := @minLeafCountScaled_bounds
private theorem levelTerm_le (c4 C lL lj lx x' N : ℝ) (r : ℕ) (k : ℕ) (hr : 1 ≤ r) (hN : 0 ≤ N)
    (hkN : ((k : ℝ) + 1) ≤ 12 * N)
    (hF : C * (1 + lj) * (lL + lx) + 48 * Real.log (83 * (r : ℝ)) + 12 ≤ c4 * x' / 2) :
    (((83 * r) ^ 4) ^ k : ℕ) * ((2 : ℝ) ^ (k + 1) * Real.exp (C * N * (1 + lj) * (lL + lx)) *
      Real.exp (-(c4 * x' * N))) ≤ Real.exp (-(c4 * x' * N / 2)) := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h83 : (0 : ℝ) < 83 * (r : ℝ) := by positivity
  set lr := Real.log (83 * (r : ℝ)) with hlr
  have hlr0 : 0 ≤ lr := Real.log_nonneg (by linarith)
  have e1 : ((((83 * r) ^ 4) ^ k : ℕ) : ℝ) = Real.exp (4 * (k : ℝ) * lr) := by
    have : (83 * (r : ℝ)) = Real.exp lr := (Real.exp_log h83).symm
    push_cast
    rw [this, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have e2 : (2 : ℝ) ^ (k + 1) ≤ Real.exp ((k : ℝ) + 1) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    calc (2 : ℝ) ^ (k + 1) ≤ (Real.exp 1) ^ (k + 1) := by gcongr
      _ = Real.exp ((k : ℝ) + 1) := by
        rw [← Real.exp_nat_mul]
        push_cast
        ring_nf
  rw [e1]
  calc Real.exp (4 * (k : ℝ) * lr) * ((2 : ℝ) ^ (k + 1) * Real.exp (C * N * (1 + lj) * (lL + lx)) *
        Real.exp (-(c4 * x' * N)))
      ≤ Real.exp (4 * (k : ℝ) * lr) * (Real.exp ((k : ℝ) + 1) * Real.exp (C * N * (1 + lj) * (lL + lx)) *
        Real.exp (-(c4 * x' * N))) := by gcongr
    _ = Real.exp (4 * (k : ℝ) * lr + ((k : ℝ) + 1) + C * N * (1 + lj) * (lL + lx) - c4 * x' * N) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-(c4 * x' * N / 2)) := by
        apply Real.exp_le_exp.2
        have h1 : 4 * (k : ℝ) * lr ≤ 48 * N * lr := by
          have : 4 * (k : ℝ) ≤ 48 * N := by nlinarith
          exact mul_le_mul_of_nonneg_right this hlr0
        have h2 := mul_le_mul_of_nonneg_left hF hN
        nlinarith
abbrev _root_.YangMills.SharedProofs.p9637 := @levelTerm_le
private theorem sum_over_depths_le (c4 lam c y xu E : ℝ) (u : ℕ) (x' N : ℕ → ℝ) (hc4 : 0 < c4) (hlam : 0 < lam)
    (hN : ∀ j, j ≤ u → 1 ≤ N j) (hE : ∀ j, j ≤ u → E ≤ c4 * xu * N j / 10) (hxu : y ≤ xu)
    (hs : ∀ j, j ≤ u → xu + lam * j - c ≤ x' j) (hy : 0 ≤ 2 / 5 * y - c / 2)
    (hq : Real.exp (-(c4 * (2 / 5 * y - c / 2))) ≤ 1 - Real.exp (-(c4 * lam / 2))) :
    ∑ j ∈ Finset.range (u + 1), Real.exp (-(c4 * x' j * N j / 2)) ≤ Real.exp (-E) := by
  set q := Real.exp (-(c4 * lam / 2)) with hqd
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hterm : ∀ j ∈ Finset.range (u + 1), Real.exp (-(c4 * x' j * N j / 2)) ≤
      Real.exp (-E) * Real.exp (-(c4 * (2 / 5 * y - c / 2))) * q ^ j := by
    intro j hj
    have hj' : j ≤ u := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hqj : q ^ j = Real.exp (-(c4 * lam / 2) * j) := by
      rw [hqd, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [hqj, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hN1 := hN j hj'
    have hE1 := hE j hj'
    have hs1 := hs j hj'
    have hjR : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hb : 0 ≤ 2 / 5 * xu + lam * j / 2 - c / 2 := by
      have := mul_nonneg hlam.le hjR
      linarith
    have h1 : c4 * N j / 2 * (xu + lam * j - c) ≤ c4 * N j / 2 * x' j :=
      mul_le_mul_of_nonneg_left hs1 (by positivity)
    have h2 : c4 * (2 / 5 * xu + lam * j / 2 - c / 2) ≤ c4 * N j * (2 / 5 * xu + lam * j / 2 - c / 2) := by
      have : c4 * 1 ≤ c4 * N j := mul_le_mul_of_nonneg_left hN1 hc4.le
      have := mul_le_mul_of_nonneg_right this hb
      linarith
    have h3 : c4 * (2 / 5 * y) ≤ c4 * (2 / 5 * xu) := by
      have : 2 / 5 * y ≤ 2 / 5 * xu := by linarith
      exact mul_le_mul_of_nonneg_left this hc4.le
    nlinarith
  have hgeom : (∑ j ∈ Finset.range (u + 1), q ^ j) * (1 - q) ≤ 1 := by
    rw [geom_sum_mul_neg]
    have := pow_nonneg hq0 (u + 1)
    linarith
  calc ∑ j ∈ Finset.range (u + 1), Real.exp (-(c4 * x' j * N j / 2))
      ≤ ∑ j ∈ Finset.range (u + 1), Real.exp (-E) * Real.exp (-(c4 * (2 / 5 * y - c / 2))) * q ^ j :=
        Finset.sum_le_sum hterm
    _ = Real.exp (-E) * (Real.exp (-(c4 * (2 / 5 * y - c / 2))) * ∑ j ∈ Finset.range (u + 1), q ^ j) := by
        rw [← Finset.mul_sum, mul_assoc]
    _ ≤ Real.exp (-E) * ((1 - q) * ∑ j ∈ Finset.range (u + 1), q ^ j) := by gcongr
    _ ≤ Real.exp (-E) * 1 := by
        have : (1 - q) * ∑ j ∈ Finset.range (u + 1), q ^ j ≤ 1 := by rw [mul_comm]; exact hgeom
        gcongr
    _ = Real.exp (-E) := mul_one _
abbrev _root_.YangMills.SharedProofs.p32958 := @sum_over_depths_le
private theorem log_count_le_half_rate (C lL c lam c4 : ℝ) (hlam : 0 < lam) (hc : 0 ≤ c) (hc4 : 0 < c4)
    (hlL : 0 ≤ lL) :
    ∃ y₀ : ℝ, ∀ x : ℝ, y₀ ≤ x → ∀ j : ℕ, (j : ℝ) ≤ (x + c) / lam →
      C * (1 + Real.log ((j : ℝ) + 1)) * (lL + Real.log x) +
        48 * Real.log (83 * ((x + c) ^ ((1 : ℝ) / 100) + 1)) + 12 ≤ c4 * x / 2 := by
  set a := 2 / lam + 1 with ha
  have hapos : 0 < a := by positivity
  set la := Real.log a
  set l249 := Real.log 249
  have hl249 : 0 ≤ l249 := Real.log_nonneg (by norm_num)
  set Q := |C| * (2 + |la|) * (1 + lL) + 48 * l249 + 60 with hQ
  have hQpos : 0 < Q := by positivity
  have hlittle := (Real.isLittleO_pow_log_id_atTop (n := 2)).def (c := c4 / (2 * Q)) (by positivity)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hlittle
  refine ⟨max X (max (Real.exp 1) (max 1 c)), fun x hx j hj => ?_⟩
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp 1 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx1 : 1 ≤ x := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hx
  have hxc : c ≤ x := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hx
  have hx0 : 0 < x := by linarith
  set lx := Real.log x with hlx
  have hlx1 : 1 ≤ lx := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hsq : lx ^ 2 ≤ c4 / (2 * Q) * x := by
    have := hX x hxX
    simp only [id, Real.norm_eq_abs] at this
    rw [abs_of_nonneg (by positivity), abs_of_pos hx0] at this
    exact this
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hjle : (j : ℝ) + 1 ≤ a * x := by
    have h1 : (x + c) / lam ≤ 2 / lam * x := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hlam]
      linarith
    have : a * x = 2 / lam * x + x := by rw [ha]; ring
    linarith
  have hlj : Real.log ((j : ℝ) + 1) ≤ la + lx := by
    have := Real.log_le_log hj1 hjle
    rwa [Real.log_mul hapos.ne' hx0.ne'] at this
  have hlj0 : 0 ≤ Real.log ((j : ℝ) + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith)
  have hP1 : 1 + Real.log ((j : ℝ) + 1) ≤ (2 + |la|) * lx := by
    have := le_abs_self la
    nlinarith [abs_nonneg la]
  have hP2 : lL + lx ≤ (1 + lL) * lx := by nlinarith
  have hprod : C * (1 + Real.log ((j : ℝ) + 1)) * (lL + lx) ≤ |C| * (2 + |la|) * (1 + lL) * lx ^ 2 := by
    calc C * (1 + Real.log ((j : ℝ) + 1)) * (lL + lx)
        ≤ |C| * (1 + Real.log ((j : ℝ) + 1)) * (lL + lx) := by
          have := le_abs_self C
          gcongr
      _ ≤ |C| * ((2 + |la|) * lx) * ((1 + lL) * lx) := by gcongr
      _ = _ := by ring
  have hR : 83 * ((x + c) ^ ((1 : ℝ) / 100) + 1) ≤ 249 * x := by
    have h2x : 1 ≤ 2 * x := by linarith
    have h1 : (x + c) ^ ((1 : ℝ) / 100) ≤ (2 * x) ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    have h2 : (2 * x) ^ ((1 : ℝ) / 100) ≤ (2 * x) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h2x (by norm_num)
    rw [Real.rpow_one] at h2
    linarith
  have hlR : Real.log (83 * ((x + c) ^ ((1 : ℝ) / 100) + 1)) ≤ l249 + lx := by
    have hpos : 0 < 83 * ((x + c) ^ ((1 : ℝ) / 100) + 1) := by
      have : 0 ≤ (x + c) ^ ((1 : ℝ) / 100) := Real.rpow_nonneg (by linarith) _
      positivity
    have := Real.log_le_log hpos hR
    rwa [Real.log_mul (by norm_num) hx0.ne'] at this
  have hlx2 : lx ≤ lx ^ 2 := by nlinarith
  have hfin : Q * lx ^ 2 ≤ c4 * x / 2 := by
    have := mul_le_mul_of_nonneg_left hsq hQpos.le
    have e : Q * (c4 / (2 * Q) * x) = c4 * x / 2 := by field_simp
    linarith
  have hl2 : 48 * (l249 + lx) + 12 ≤ (48 * l249 + 60) * lx ^ 2 := by nlinarith
  have : Q * lx ^ 2 = |C| * (2 + |la|) * (1 + lL) * lx ^ 2 + (48 * l249 + 60) * lx ^ 2 := by
    rw [hQ]; ring
  linarith
abbrev _root_.YangMills.SharedProofs.p12277 := @log_count_le_half_rate
private theorem flow_stays_above (Tb : ParameterAssignment) (y g β : ℝ) (K : ℕ) (h : FlowCrossing Tb y g β K)
    (hB : 0 ≤ Tb.B) (hRet : StepReturn.ExpansionReturnsAt (Tb.stepParameters y))
    (hRow : HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β)) :
    ∀ u ≤ K, y ≤ (couplingFlow (Tb.stepParameters y) β u).1 := by
  have htop : y ≤ windowUpper (Tb.stepParameters y) g - 2 * Tb.B := by
    have : windowUpper (Tb.stepParameters y) g = (g ^ 2)⁻¹ + 2 * Tb.B := rfl
    rw [this]
    linarith [h.le_inv_sq]
  have hbelow : ∀ k < K, y ≤ (couplingFlow (Tb.stepParameters y) β k).1 := fun k hk => by
    have := h.isFirst.2 k hk
    linarith
  have hstep : ∀ t : ℕ, y ≤ (couplingFlow (Tb.stepParameters y) β t).1 →
      HasExpansion (Tb.stepParameters y) t (couplingFlow (Tb.stepParameters y) β t).1
        (couplingFlow (Tb.stepParameters y) β t).2 →
      HasExpansion (Tb.stepParameters y) (t + 1) (couplingFlow (Tb.stepParameters y) β (t + 1)).1
          (couplingFlow (Tb.stepParameters y) β (t + 1)).2 ∧
        |(couplingFlow (Tb.stepParameters y) β (t + 1)).1 - (couplingFlow (Tb.stepParameters y) β t).1| ≤
          2 * Tb.B := by
    intro t hx hr
    obtain ⟨x', ⟨h1, h2⟩, h3⟩ := hRet t _ _ hx hr
    have hnext : (couplingFlow (Tb.stepParameters y) β (t + 1)).1 = x' := by
      have hex : ∃ x' : ℝ, HasExpansion (Tb.stepParameters y) (t + 1) x'
          (kernelImage (Tb.stepParameters y) (couplingFlow (Tb.stepParameters y) β t).1
            (couplingFlow (Tb.stepParameters y) β t).2) := ⟨x', h1⟩
      show expansionCoupling (Tb.stepParameters y) t _ _ = x'
      unfold expansionCoupling
      rw [dif_pos hex]
      obtain ⟨_, f, hf, _⟩ := hex.choose_spec
      exact h3 _ f hf
    rw [hnext]
    exact ⟨h1, h2⟩
  have hrows : ∀ t ≤ K, HasExpansion (Tb.stepParameters y) t (couplingFlow (Tb.stepParameters y) β t).1
      (couplingFlow (Tb.stepParameters y) β t).2 := by
    intro t
    induction t with
    | zero => intro _; exact hRow
    | succ t ih =>
      intro ht
      exact (hstep t (hbelow t (by omega)) (ih (by omega))).1
  intro u hu
  rcases Nat.lt_or_ge u K with hlt | hge
  · exact hbelow u hlt
  · obtain rfl : u = K := le_antisymm hu hge
    cases u with
    | zero =>
      have : (couplingFlow (Tb.stepParameters y) β 0).1 = β := rfl
      rw [this]
      linarith [h.upper_le]
    | succ t =>
      have h1 := (hstep t (hbelow t (by omega)) (hrows t (by omega))).2
      have h2 := h.isFirst.2 t (by omega)
      have h3 := (abs_le.1 h1).1
      linarith
abbrev _root_.YangMills.SharedProofs.p87009 := @flow_stays_above
private theorem supDist_first_le {n : ℕ} [NeZero n] {k r : ℕ} {f : Fin (k + 1) → TorusSite n}
    (h : ∀ i : Fin k, supDist (f i.succ) (f i.castSucc) < 41 * r) (i : Fin (k + 1)) :
    supDist (f i) (f 0) ≤ 41 * r * (i : ℕ) := by
  induction i using Fin.induction with
  | zero => simp [supDist]
  | succ i ih =>
    have h1 := supDist_triangle (f i.succ) (f i.castSucc) (f 0)
    have h2 := h i
    have h3 : ((i.succ : Fin (k + 1)) : ℕ) = (i : ℕ) + 1 := Fin.val_succ i
    have h4 : ((i.castSucc : Fin (k + 1)) : ℕ) = (i : ℕ) := Fin.val_castSucc i
    rw [h4] at ih
    rw [h3, Nat.mul_add, Nat.mul_one]
    omega
private theorem long_classes_measure_le (Tb : ParameterAssignment) (y g β : ℝ) (K m : ℕ)
    (T : StageTower (Tb.stepParameters y)) (u n : ℕ) [NeZero n]
    (hAt : HullChainAtLevel Tb y g β K m T u n) (q : ℕ) (zs : Fin q → TorusSite n) (D : ℝ) (hq1 : 1 ≤ q)
    (hD : 0 ≤ D)
    (hfar : ∀ c e, c ≠ e → 83 * stageRange T u * TorusLimits.keptSitesAlong D (stageRange T u) ≤
      supDist (zs c) (zs e))
    (hy : Tb.floorMin ≤ y) (hyone : 1 ≤ y) (hDr : Tb.Admissible)
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
          ∃ j ≤ u, ∃ S ∈ F ys j, UnitsAtDepth T j u n w S ∧
            HullTrees.Separated (30 * stageRange T (u - j)) S)
    (hP : ∀ (u n : ℕ) [NeZero n], HullChainAtLevel Tb y g β K m T u n →
      ∀ S : Finset (TorusSite n), HullTrees.Separated (30 * stageRange T u) S →
        (markedSampleLaw T β u n).real {w | ∀ z ∈ S, HullTrees.IsUnit T u n w z} ≤
          Real.exp (-(separatedUnitRate Tb * stageCoupling T u * (S.card : ℝ))))
    (hLaw : ResponseInTheExpansion.sampleBelowLawStatement) (hDraw : forgetLastStepStatement)
    (lam c : ℝ) (hlam : 0 < lam)
    (hslope : ∀ j ≤ u, lam * (j : ℝ) - c ≤ stageCoupling T (u - j) - stageCoupling T u)
    (hfloor : ∀ i ≤ K, y ≤ stageCoupling T i)
    (hf1 : ∀ x : ℝ, y ≤ x → ∀ j : ℕ, (j : ℝ) ≤ (x + c) / lam →
      C₁ * (1 + Real.log ((j : ℝ) + 1)) * (Real.log ((Tb.stepParameters y).side : ℝ) + Real.log x) +
        48 * Real.log (83 * ((x + c) ^ ((1 : ℝ) / 100) + 1)) + 12 ≤ separatedUnitRate Tb * x / 2)
    (hc4 : 0 < separatedUnitRate Tb)
    (hyc : 0 ≤ 2 / 5 * y - c / 2)
    (hq : Real.exp (-(separatedUnitRate Tb * (2 / 5 * y - c / 2))) ≤
      1 - Real.exp (-(separatedUnitRate Tb * lam / 2))) :
    (markedSampleLaw T β u n).real {w | ∀ e, zs e ∈ hullSet T u n w ∧
        D ≤ (supDiam (hullClass (stageRange T u) (hullSet T u n w) (zs e)) : ℝ)} ≤
      Real.exp (-(hullDecayRate Tb * stageCoupling T u * (1 + D / (stageRange T u : ℝ)))) ^ q := by
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
  have hfar' : ∀ c e, c ≠ e → 83 * r * (k + 1) ≤ supDist (zs c) (zs e) := by
    intro c e hce
    have := hfar c e hce
    rw [show TorusLimits.keptSitesAlong D r = k + 1 from hk] at this
    exact this
  obtain ⟨kk, hkk⟩ : ∃ kk, q * (k + 1) = kk + 1 := ⟨q * (k + 1) - 1, by
    have : 1 ≤ q * (k + 1) := Nat.mul_pos hq1 (by omega)
    omega⟩
  obtain ⟨F, hF⟩ := hUnits (kk + 1) (by omega)
  set N : ℕ → ℕ := fun j => minLeafCountScaled (Tb.stepParameters y).side j (kk + 1) with hNdef
  have hNb : ∀ j, 1 ≤ N j ∧ ((kk + 1 : ℕ) : ℝ) ≤ 12 * (N j : ℝ) := fun j =>
    minLeafCountScaled_bounds _ j (kk + 1) hLbig (by omega)
  let Tup : TorusSite n → Finset (Fin (k + 1) → TorusSite n) := fun z => Finset.univ.filter fun f =>
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
  have hTup : ∀ z, (Tup z).card ≤ ((83 * r) ^ 4) ^ k := by
    intro z
    refine le_trans (Finset.card_le_card ?_)
      (card_paths_le (fun a b : TorusSite n => supDist a b < 41 * r) _ hnbr z k)
    intro f hf
    simp only [Tup, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    exact hf.1
  let Tups : Finset (Fin q → Fin (k + 1) → TorusSite n) := Fintype.piFinset fun e => Tup (zs e)
  have hTups : Tups.card ≤ (((83 * r) ^ 4) ^ k) ^ q := by
    rw [Fintype.card_piFinset]
    calc ∏ e : Fin q, (Tup (zs e)).card ≤ ∏ _e : Fin q, ((83 * r) ^ 4) ^ k :=
          Finset.prod_le_prod' fun e _ => hTup _
      _ = _ := by simp
  let flat : (Fin q → Fin (k + 1) → TorusSite n) → Fin (kk + 1) → TorusSite n := fun f i =>
    f (finProdFinEquiv.symm (Fin.cast hkk.symm i)).1 (finProdFinEquiv.symm (Fin.cast hkk.symm i)).2
  have hflat : ∀ f ∈ Tups, ∀ i i', i ≠ i' → 40 * r ≤ supDist (flat f i) (flat f i') := by
    intro f hf i i' hii
    have hfc : ∀ e, (f e 0 = zs e ∧ ∀ i : Fin k, supDist (f e i.succ) (f e i.castSucc) < 41 * r) ∧
        ∀ i i', i ≠ i' → 40 * r ≤ supDist (f e i) (f e i') := by
      intro e
      have := Fintype.mem_piFinset.1 hf e
      simpa only [Tup, Finset.mem_filter, Finset.mem_univ, true_and] using this
    obtain ⟨c, a⟩ : ∃ p, p = finProdFinEquiv.symm (Fin.cast hkk.symm i) := ⟨_, rfl⟩
    obtain ⟨e, b⟩ : ∃ p, p = finProdFinEquiv.symm (Fin.cast hkk.symm i') := ⟨_, rfl⟩
    have hne : finProdFinEquiv.symm (Fin.cast hkk.symm i) ≠ finProdFinEquiv.symm (Fin.cast hkk.symm i') := by
      intro h
      exact hii (by simpa using finProdFinEquiv.symm.injective h)
    show 40 * r ≤ supDist (f (finProdFinEquiv.symm (Fin.cast hkk.symm i)).1
        (finProdFinEquiv.symm (Fin.cast hkk.symm i)).2)
      (f (finProdFinEquiv.symm (Fin.cast hkk.symm i')).1 (finProdFinEquiv.symm (Fin.cast hkk.symm i')).2)
    generalize finProdFinEquiv.symm (Fin.cast hkk.symm i) = s at hne
    generalize finProdFinEquiv.symm (Fin.cast hkk.symm i') = t at hne
    obtain ⟨c, a⟩ := s
    obtain ⟨e, b⟩ := t
    by_cases hce : c = e
    · subst hce
      refine (hfc c).2 a b fun hab => hne (by rw [hab])
    · have h1 := hfar' c e hce
      have ha := supDist_first_le (hfc c).1.2 a
      have hb := supDist_first_le (hfc e).1.2 b
      rw [(hfc c).1.1] at ha
      rw [(hfc e).1.1] at hb
      have t1 := supDist_triangle (zs c) (f c a) (zs e)
      have t2 := supDist_triangle (f c a) (f e b) (zs e)
      have s1 : supDist (zs c) (f c a) = supDist (f c a) (zs c) := supDist_comm _ _
      have ha' : 41 * r * (a : ℕ) ≤ 41 * (r * k) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by have := a.2; omega))
      have hb' : 41 * r * (b : ℕ) ≤ 41 * (r * k) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by have := b.2; omega))
      have e1 : 83 * r * (k + 1) = 83 * (r * k) + 83 * r := by ring
      show 40 * r ≤ supDist (f c a) (f e b)
      omega
  let G : (Fin q → Fin (k + 1) → TorusSite n) → (j : ℕ) →
      Finset (Finset (TorusSite (fineSide (Tb.stepParameters y).side j n))) :=
    fun f j => (F (flat f) j).filter fun S => HullTrees.Separated (30 * stageRange T (u - j)) S
  let Ev : (j : ℕ) → Finset (TorusSite (fineSide (Tb.stepParameters y).side j n)) →
      Set (MarkedSample (Tb.stepParameters y) u n) :=
    fun j S => {w | UnitsAtDepth T j u n w S}
  have hcover : {w | ∀ e, zs e ∈ hullSet T u n w ∧ D ≤ (supDiam (hullClass r (hullSet T u n w) (zs e)) : ℝ)} ⊆
      ⋃ f ∈ Tups, ⋃ j ∈ Finset.range (u + 1), ⋃ S ∈ G f j, Ev j S := by
    intro w hw
    have hone : ∀ e, ∃ f : Fin (k + 1) → TorusSite n, f ∈ Tup (zs e) ∧ ∀ i, f i ∈ hullSet T u n w := by
      intro e
      obtain ⟨hz, hdiam⟩ := hw e
      obtain ⟨⟨ys, h0, hin, hap, hnear⟩, -⟩ := hSites n r (hullClass r (hullSet T u n w) (zs e)) (zs e) D hr1 hD
        (Finset.mem_filter.2 ⟨hz, Relation.ReflTransGen.refl⟩) hullClass_chainConnected hdiam
      rw [hk] at hin hap hnear
      refine ⟨fun i : Fin (k + 1) => ys i, ?_, fun i => (Finset.mem_filter.1 (hin i i.2)).1⟩
      simp only [Tup, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨by simpa using h0, fun i => ?_⟩, fun i i' hii => ?_⟩
      · have := hnear i (by omega)
        simpa [Fin.val_succ] using this
      · exact hap i i.2 i' i'.2 (fun h => hii (Fin.ext h))
    choose f hfT hfin using hone
    have hfm : f ∈ Tups := Fintype.mem_piFinset.2 hfT
    obtain ⟨j, hj, S, hS, hUB, hAp⟩ := (hF _ (hflat f hfm)).2 w (fun i => hfin _ _)
    simp only [Set.mem_iUnion]
    exact ⟨_, hfm, j, Finset.mem_range.2 (by omega), S, Finset.mem_filter.2 ⟨hS, hAp⟩, hUB⟩
  let b : ℕ → ℝ := fun j => (2 : ℝ) ^ (kk + 1) * Real.exp (C₁ * (N j : ℝ) * (1 + Real.log ((j : ℝ) + 1)) *
      (Real.log ((Tb.stepParameters y).side : ℝ) + Real.log (stageCoupling T (u - j)))) *
      Real.exp (-(separatedUnitRate Tb * stageCoupling T (u - j) * (N j : ℝ)))
  have hb0 : ∀ j, 0 ≤ b j := fun j => by positivity
  have hlevel : ∀ f ∈ Tups, ∀ j ∈ Finset.range (u + 1),
      (markedSampleLaw T β u n).real (⋃ S ∈ G f j, Ev j S) ≤ b j := by
    intro f hf j hj
    have hj' : j ≤ u := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    obtain ⟨hcard, hsz⟩ := (hF _ (hflat f hf)).1 j hj'
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    have hone : ∀ S ∈ G f j, (markedSampleLaw T β u n).real (Ev j S) ≤
        Real.exp (-(separatedUnitRate Tb * stageCoupling T (u - j) * (N j : ℝ))) := by
      intro S hS
      obtain ⟨hSF, hSA⟩ := Finset.mem_filter.1 hS
      have := measure_unitsAtDepth_le Tb y g β K m T hy hDr hP hLaw hDraw j u n hj' hAt S hSA
      rwa [hsz S hSF] at this
    refine (Finset.sum_le_sum hone).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have hG : ((G f j).card : ℝ) ≤ ((F (flat f) j).card : ℝ) := by
      exact_mod_cast Finset.card_filter_le _ _
    exact hG.trans hcard
  have hsumall : (markedSampleLaw T β u n).real
      {w | ∀ e, zs e ∈ hullSet T u n w ∧ D ≤ (supDiam (hullClass r (hullSet T u n w) (zs e)) : ℝ)} ≤
      (Tups.card : ℝ) * ∑ j ∈ Finset.range (u + 1), b j := by
    refine (measureReal_mono hcover (measure_ne_top _ _)).trans ?_
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    have : ∀ f ∈ Tups, (markedSampleLaw T β u n).real
        (⋃ j ∈ Finset.range (u + 1), ⋃ S ∈ G f j, Ev j S) ≤ ∑ j ∈ Finset.range (u + 1), b j := by
      intro f hf
      exact (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum (hlevel f hf))
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  refine hsumall.trans ?_
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range (u + 1), b j := Finset.sum_nonneg fun j _ => hb0 j
  have hTupR : (Tups.card : ℝ) ≤ (((83 * r) ^ 4) ^ kk : ℕ) := by
    have h1 : (((83 * r) ^ 4) ^ k) ^ q ≤ ((83 * r) ^ 4) ^ kk := by
      rw [← pow_mul]
      refine Nat.pow_le_pow_right (Nat.pos_of_ne_zero (by positivity)) ?_
      have : k * q + q = kk + 1 := by rw [← hkk]; ring
      omega
    exact_mod_cast hTups.trans h1
  refine (mul_le_mul_of_nonneg_right hTupR hsum0).trans ?_
  rw [Finset.mul_sum]
  have hslope' : ∀ j ≤ u, stageCoupling T u + lam * (j : ℝ) - c ≤ stageCoupling T (u - j) := fun j hj => by
    have := hslope j hj
    linarith
  have hterm : ∀ j ∈ Finset.range (u + 1), (((83 * r) ^ 4) ^ kk : ℕ) * b j ≤
      Real.exp (-(separatedUnitRate Tb * stageCoupling T (u - j) * (N j : ℝ) / 2)) := by
    intro j hj
    have hj' : j ≤ u := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hx' : y ≤ stageCoupling T (u - j) := hfloor _ (by have := hAt.le; omega)
    have hs := hslope j hj'
    have hjR : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjx : (j : ℝ) ≤ (stageCoupling T (u - j) + c) / lam := by
      rw [le_div_iff₀ hlam]
      nlinarith
    have hf := hf1 _ hx' j hjx
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
    refine levelTerm_le (separatedUnitRate Tb) C₁ _ _ _ _ _ r kk hr1 (Nat.cast_nonneg _) ?_ ?_
    · have := (hNb j).2
      push_cast at this
      exact this
    · linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  have hpow : Real.exp (-(hullDecayRate Tb * stageCoupling T u * (1 + D / (r : ℝ)))) ^ q =
      Real.exp (-(hullDecayRate Tb * stageCoupling T u * (1 + D / (r : ℝ)) * (q : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpow]
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
  have hqR : (q : ℝ) * ((k : ℝ) + 1) = (kk : ℝ) + 1 := by exact_mod_cast hkk
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hone : (1 + D / (r : ℝ)) * (q : ℝ) ≤ 996 * (N j : ℝ) := by
    have h1 : 1 + D / (r : ℝ) ≤ 83 * ((k : ℝ) + 1) := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hq0
    nlinarith
  have hrate : hullDecayRate Tb ≤ separatedUnitRate Tb / 10 ^ 4 := min_le_left _ _
  calc hullDecayRate Tb * stageCoupling T u * (1 + D / (r : ℝ)) * (q : ℝ)
      = hullDecayRate Tb * stageCoupling T u * ((1 + D / (r : ℝ)) * (q : ℝ)) := by ring
    _ ≤ separatedUnitRate Tb / 10 ^ 4 * stageCoupling T u * (996 * (N j : ℝ)) := by gcongr
    _ ≤ separatedUnitRate Tb * stageCoupling T u * (N j : ℝ) / 10 := by
        have : 0 ≤ separatedUnitRate Tb * stageCoupling T u * (N j : ℝ) := by positivity
        nlinarith
theorem severalLongHullClasses_holds (hSites : sitesAlongHullClassStatement)
    (hU : UnitsOfSeparatedHullSites) (hP : separatedUnitsBoundStatement)
    (hSl : FlowDescendsLinearly) (hLaw : ResponseInTheExpansion.sampleBelowLawStatement)
    (hDraw : forgetLastStepStatement) : severalLongHullClassesStatement := by
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
  obtain ⟨y₄, H₄⟩ := log_count_le_half_rate (C₁ (Tb.stepParameters 0).side)
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
  intro g β K m T u n _ hAt qq zs D hq1 hD hfar
  have hrun := hAt.chain
  have hβ : y ≤ β := by
    have h1 := hrun.toCrossingVolume.toFlowCrossing.le_inv_sq
    have h2 := hrun.toCrossingVolume.toFlowCrossing.upper_le
    have h3 : windowUpper (Tb.stepParameters y) g = (g ^ 2)⁻¹ + 2 * Tb.B := rfl
    have hB := hDr.B_ge
    linarith
  have hstay := flow_stays_above Tb y g β K hrun.toCrossingVolume.toFlowCrossing
    (by linarith [hDr.B_ge]) hRet (hRow β hβ)
  have hcoup : ∀ i ≤ K, stageCoupling T i = (couplingFlow (Tb.stepParameters y) β i).1 := fun i hi =>
    hrun.follows i (by omega)
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
  exact long_classes_measure_le Tb y g β K m T u n hAt qq zs D hq1 hD hfar hy0' hyone hDr hSites
    (C₁ (Tb.stepParameters y).side)
    (H₁ y hy1' hRet hRow g β K m T u n hAt) (H₂ y hy2' hRet hRow g β K m T) hLaw hDraw lam c hlam hslope hfloor
    (fun x hx j hj => H₄ x (hy4'.trans hx) j hj) hc4 hyc hq'
end YangMills.Construction.MomentLaw
end
