import YangMills.Construction.ClusterExpansionOfAStep.OffsetsAboveABox
import YangMills.Construction.LawOnABoxOfTheFlow.WeightsOfABlock
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsTheDescendedFormProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxEvents
open TorusFields TorusLumps TorusContours CongruentBoxes StepSettings BlockPlaces WeightedResponses ResponseInTheExpansion
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
private theorem supDist_le_of_parentBlock {L n : ℕ} [NeZero L] [NeZero n] (u v : TorusSite (n * L)) :
    _root_.YangMills.Construction.TorusFields.supDist u v ≤ L * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L u) (parentBlock L v) + L := by
  obtain ⟨a, ha, hb⟩ := exists_offset_of_supDist (parentBlock L u) (parentBlock L v)
  have hu : u = blockCentre L (parentBlock L u) + siteOfInt (refinedOffset L 0 (siteOffset u)) :=
    eq_blockCentre_add_of_parentBlock (y := parentBlock L u) (a := 0) (x := u) (by
      funext i
      simp [siteOfInt])
  have hv : v = blockCentre L (parentBlock L u) + siteOfInt (refinedOffset L a (siteOffset v)) :=
    eq_blockCentre_add_of_parentBlock (y := parentBlock L u) (a := a) (x := v) ha
  have hdiff : v = u + siteOfInt (refinedOffset L a (siteOffset v) - refinedOffset L 0 (siteOffset u)) := by
    have e : (siteOfInt (refinedOffset L a (siteOffset v) - refinedOffset L 0 (siteOffset u)) : TorusSite (n * L)) =
        siteOfInt (refinedOffset L a (siteOffset v)) - siteOfInt (refinedOffset L 0 (siteOffset u)) := by
      funext i
      simp [siteOfInt]
    rw [e]
    nth_rewrite 1 [hv]
    nth_rewrite 2 [hu]
    abel
  have := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le u (refinedOffset L a (siteOffset v) - refinedOffset L 0 (siteOffset u))
    (L * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L u) (parentBlock L v) + L) (fun i => by
      have h1 := hb i
      have h2 := (siteOffset v i).2
      have h3 := (siteOffset u i).2
      simp only [Pi.sub_apply, refinedOffset, Pi.zero_apply, mul_zero, zero_add]
      have h4 : ((L : ℤ) * a i).natAbs = L * (a i).natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      have h5 : L * (a i).natAbs ≤ L * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L u) (parentBlock L v) := Nat.mul_le_mul_left _ h1
      omega)
  rwa [← hdiff] at this
private theorem supDist_le_siteAbove {L : ℕ} [NeZero L] (hL : 2 ≤ L) :
    ∀ (s m : ℕ) [NeZero m] (y o : TorusSite (fineSide L s m)),
      _root_.YangMills.Construction.TorusFields.supDist y o ≤ L ^ s * _root_.YangMills.Construction.TorusFields.supDist (siteAbove L s m y) (siteAbove L s m o) + 2 * L ^ s := by
  intro s
  induction s with
  | zero =>
    intro m _ y o
    simp [siteAbove, fineSide]
  | succ s ih =>
    intro m _ y o
    have hne : NeZero (m * L) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne L)⟩
    have h1 := ih (m * L) y o
    have h2 := supDist_le_of_parentBlock (siteAbove L s (m * L) y) (siteAbove L s (m * L) o)
    have h3 : siteAbove L (s + 1) m y = parentBlock L (siteAbove L s (m * L) y) := rfl
    have h4 : siteAbove L (s + 1) m o = parentBlock L (siteAbove L s (m * L) o) := rfl
    rw [h3, h4]
    set D := _root_.YangMills.Construction.TorusFields.supDist (parentBlock L (siteAbove L s (m * L) y)) (parentBlock L (siteAbove L s (m * L) o))
    have h5 : L ^ s * _root_.YangMills.Construction.TorusFields.supDist (siteAbove L s (m * L) y) (siteAbove L s (m * L) o) ≤ L ^ s * (L * D + L) :=
      Nat.mul_le_mul_left _ h2
    have h6 : 2 * L ^ s ≤ L ^ (s + 1) := by
      rw [pow_succ, mul_comm]
      exact Nat.mul_le_mul_left _ hL
    have h7 : L ^ s * (L * D + L) = L ^ (s + 1) * D + L ^ (s + 1) := by
      rw [pow_succ]
      ring
    refine le_trans h1 ?_
    omega
private theorem card_parentBlock_fibre_le {L n : ℕ} [NeZero L] [NeZero n] (Y : TorusSite n)
    [DecidablePred fun x : TorusSite (n * L) => parentBlock L x = Y] :
    (Finset.univ.filter fun x : TorusSite (n * L) => parentBlock L x = Y).card ≤ L ^ 4 := by
  classical
  have hinj : Set.InjOn (siteOffset : TorusSite (n * L) → BlockOffset L)
      (Finset.univ.filter fun x : TorusSite (n * L) => parentBlock L x = Y) := by
    intro x hx z hz hxz
    have h1 : parentBlock L x = Y := (Finset.mem_filter.1 hx).2
    have h2 : parentBlock L z = Y := (Finset.mem_filter.1 hz).2
    rw [← blockSite_parentBlock_siteOffset x, ← blockSite_parentBlock_siteOffset z, h1, h2, hxz]
  have := Finset.card_le_card_of_injOn (t := (Finset.univ : Finset (BlockOffset L))) siteOffset
    (fun _ _ => Finset.mem_univ _) hinj
  simpa [Finset.card_univ, Fintype.card_pi] using this
private theorem card_siteAbove_fibre_le {L : ℕ} [NeZero L] :
    ∀ (s m : ℕ) [NeZero m] (Y : TorusSite m) [DecidablePred fun y : TorusSite (fineSide L s m) => siteAbove L s m y = Y],
      (Finset.univ.filter fun y : TorusSite (fineSide L s m) => siteAbove L s m y = Y).card ≤ L ^ (4 * s) := by
  intro s
  induction s with
  | zero =>
    intro m _ Y _
    have h : (Finset.univ.filter fun y : TorusSite (fineSide L 0 m) => siteAbove L 0 m y = Y).card ≤ 1 :=
      Finset.card_le_one.2 fun a ha b hb => ((Finset.mem_filter.1 ha).2).trans ((Finset.mem_filter.1 hb).2).symm
    simpa using h
  | succ s ih =>
    intro m _ Y _
    classical
    have hne : NeZero (m * L) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne L)⟩
    let A : Finset (TorusSite (fineSide L s (m * L))) :=
      Finset.univ.filter fun y => parentBlock L (siteAbove L s (m * L) y) = Y
    have hsub : A ⊆ (Finset.univ.filter fun x : TorusSite (m * L) => parentBlock L x = Y).biUnion fun x : TorusSite (m * L) =>
          Finset.univ.filter fun y : TorusSite (fineSide L s (m * L)) => siteAbove L s (m * L) y = x := by
      intro y hy
      have h1 : parentBlock L (siteAbove L s (m * L) y) = Y := (Finset.mem_filter.1 hy).2
      exact Finset.mem_biUnion.2 ⟨siteAbove L s (m * L) y, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
    have hA : A.card ≤ L ^ 4 * L ^ (4 * s) := by
      refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le_card_mul _ _ (L ^ (4 * s)) fun x _ => ?_).trans ?_)
      · exact ih (m * L) x
      · exact Nat.mul_le_mul_right _ (card_parentBlock_fibre_le Y)
    have hB : (Finset.univ.filter fun y : TorusSite (fineSide L (s + 1) m) => siteAbove L (s + 1) m y = Y).card ≤ A.card := by
      refine Finset.card_le_card_of_injOn (fun y => y) (fun y hy => ?_) (fun a _ b _ h => h)
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hy).2⟩
    refine hB.trans (hA.trans (le_of_eq ?_))
    ring
private theorem supDist_add_nsmul_unitStep_le {M : ℕ} [NeZero M] (x : TorusSite M) (d : Fin 4) (k : ℕ) :
    _root_.YangMills.Construction.TorusFields.supDist (x + k • unitStep M d) x ≤ k := by
  induction k with
  | zero => simp [_root_.YangMills.Construction.TorusFields.supDist_self]
  | succ k ih =>
    have h1 : _root_.YangMills.Construction.TorusFields.supDist (x + (k + 1) • unitStep M d) (x + k • unitStep M d) ≤ 1 := by
      have := _root_.YangMills.Construction.TorusContours.supDist_sub_unitStep_le (x + (k + 1) • unitStep M d) d
      have e : x + (k + 1) • unitStep M d - unitStep M d = x + k • unitStep M d := by
        rw [succ_nsmul]
        abel
      rwa [e] at this
    exact (_root_.YangMills.Construction.TorusFields.supDist_triangle _ (x + k • unitStep M d) _).trans (by omega)
private theorem supDist_add_unitStep_le {M : ℕ} [NeZero M] (x : TorusSite M) (d : Fin 4) :
    _root_.YangMills.Construction.TorusFields.supDist (x + unitStep M d) x ≤ 1 := by apply _root_.YangMills.SharedProofs.p63420 <;> assumption
private theorem supDist_vertex_le {M : ℕ} [NeZero M] {x y : TorusSite M} {k : ℕ} (h : _root_.YangMills.Construction.TorusFields.supDist x y ≤ k)
    {μ ν : Fin 4} {z : TorusSite M} (hz : z ∈ plaquetteVertices x μ ν) : _root_.YangMills.Construction.TorusFields.supDist z y ≤ k + 2 := by
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · omega
  · have h1 := supDist_add_unitStep_le x μ
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (x + unitStep M μ) x y
    omega
  · have h1 := supDist_add_unitStep_le x ν
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (x + unitStep M ν) x y
    omega
  · have h0 : _root_.YangMills.Construction.TorusFields.supDist (x + unitStep M μ + unitStep M ν) y ≤ k + 2 := by
      have h1 := supDist_add_unitStep_le (x + unitStep M μ) ν
      have h3 := supDist_add_unitStep_le x μ
      have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (x + unitStep M μ) x y
      have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle (x + unitStep M μ + unitStep M ν) (x + unitStep M μ) y
      omega
    exact h0
theorem blockWeightBounds : blockWeightBoundsStatement := by
  intro L _ hL s m _ P o
  classical
  set N := L ^ s with hN
  let Fib : Finset (TorusSite (fineSide L s m)) := Finset.univ.filter fun y => siteAbove L s m y = P.1
  let g : ℕ → ℕ → TorusSite (fineSide L s m) → TorusPlaquette (fineSide L s m) :=
    fun i j y => (y + i • unitStep _ P.2.1 + j • unitStep _ P.2.2, P.2.1, P.2.2)
  let c : TorusPlaquette (fineSide L s m) → ℝ :=
    fun p => ∑ y ∈ Fib, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, if p = g i j y then 1 else 0
  have hw : ∀ p, blockWeight L s P p = (1 / (L : ℝ) ^ (4 * s)) * c p := fun p => rfl
  have hc0 : ∀ p, 0 ≤ c p := fun p =>
    Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs <;> norm_num
  have hNr : ((N : ℕ) : ℝ) = (L : ℝ) ^ s := by rw [hN]; push_cast; rfl
  have h1 : ∀ p, c p ≤ (N : ℝ) ^ 2 := by
    intro p
    have e : c p = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ y ∈ Fib, if p = g i j y then (1 : ℝ) else 0 := by
      simp only [c]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
    have hone : ∀ i j, ∑ y ∈ Fib, (if p = g i j y then (1 : ℝ) else 0) ≤ 1 := by
      intro i j
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have : (Fib.filter fun y => p = g i j y).card ≤ 1 := by
        refine Finset.card_le_one.2 fun a ha b hb => ?_
        have ea := (Finset.mem_filter.1 ha).2
        have eb := (Finset.mem_filter.1 hb).2
        have := (Prod.mk.inj (ea.symm.trans eb)).1
        exact add_right_cancel (add_right_cancel this)
      exact_mod_cast this
    rw [e]
    calc _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hone i j
      _ = (N : ℝ) ^ 2 := by simp [sq]
  have h2 : ∑ p : TorusPlaquette (fineSide L s m), c p ≤ (L : ℝ) ^ (4 * s) * (N : ℝ) ^ 2 := by
    have e : ∑ p : TorusPlaquette (fineSide L s m), c p =
        ∑ y ∈ Fib, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, (1 : ℝ) := by
      simp only [c]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp
    rw [e]
    have hF : (Fib.card : ℝ) ≤ (L : ℝ) ^ (4 * s) := by
      have := card_siteAbove_fibre_le (L := L) s m P.1
      exact_mod_cast this
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
    calc (Fib.card : ℝ) * ((N : ℝ) * (N : ℝ)) = (Fib.card : ℝ) * (N : ℝ) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hF this
  refine ⟨?_, ?_⟩
  · have hD : (0 : ℝ) < (L : ℝ) ^ (4 * s) := by positivity
    have hDN : (L : ℝ) ^ (4 * s) = (N : ℝ) ^ 4 := by
      rw [hNr, ← pow_mul, mul_comm]
    have hsum : ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L s m))), blockWeight L s P p ^ 2 ≤
        (1 / (L : ℝ) ^ (4 * s)) ^ 2 * ((N : ℝ) ^ 2 * ∑ p : TorusPlaquette (fineSide L s m), c p) := by
      have h3 : ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L s m))), blockWeight L s P p ^ 2 ≤
          ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L s m))),
            (1 / (L : ℝ) ^ (4 * s)) ^ 2 * ((N : ℝ) ^ 2 * c p) := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [hw, mul_pow, sq (c p)]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (h1 p) (hc0 p)
      refine h3.trans ((Finset.sum_le_univ_sum_of_nonneg fun p => ?_).trans (le_of_eq ?_))
      · have := hc0 p
        positivity
      · rw [← Finset.mul_sum, ← Finset.mul_sum]
    refine hsum.trans ?_
    have hN0 : (0 : ℝ) < (N : ℝ) ^ 4 := by rw [← hDN]; exact hD
    calc (1 / (L : ℝ) ^ (4 * s)) ^ 2 * ((N : ℝ) ^ 2 * ∑ p : TorusPlaquette (fineSide L s m), c p)
        ≤ (1 / (L : ℝ) ^ (4 * s)) ^ 2 * ((N : ℝ) ^ 2 * ((L : ℝ) ^ (4 * s) * (N : ℝ) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 1 := by
          have hNne : (N : ℝ) ≠ 0 := by
            intro h0
            rw [h0] at hN0
            norm_num at hN0
          rw [hDN]
          field_simp
  · intro p hp z hz
    have hex : ∃ y ∈ Fib, ∃ i ∈ Finset.range N, ∃ j ∈ Finset.range N, p = g i j y := by
      by_contra hcon
      push_neg at hcon
      apply hp
      rw [hw]
      have : c p = 0 := by
        simp only [c]
        refine Finset.sum_eq_zero fun y hy => Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
        rw [if_neg (hcon y hy i hi j hj)]
      rw [this, mul_zero]
    obtain ⟨y, hy, i, hi, j, hj, rfl⟩ := hex
    have hyP : siteAbove L s m y = P.1 := (Finset.mem_filter.1 hy).2
    have hyo := supDist_le_siteAbove hL s m y o
    rw [hyP, ← hN] at hyo
    have hi' : i + 1 ≤ N := Finset.mem_range.1 hi
    have hj' : j + 1 ≤ N := Finset.mem_range.1 hj
    have hp1 : _root_.YangMills.Construction.TorusFields.supDist (y + i • unitStep (fineSide L s m) P.2.1 + j • unitStep (fineSide L s m) P.2.2) y ≤ i + j := by
      have a1 := supDist_add_nsmul_unitStep_le (y + i • unitStep (fineSide L s m) P.2.1) P.2.2 j
      have a2 := supDist_add_nsmul_unitStep_le y P.2.1 i
      have a3 := _root_.YangMills.Construction.TorusFields.supDist_triangle (y + i • unitStep (fineSide L s m) P.2.1 + j • unitStep (fineSide L s m) P.2.2)
        (y + i • unitStep (fineSide L s m) P.2.1) y
      omega
    have hz2 : _root_.YangMills.Construction.TorusFields.supDist z y ≤ i + j + 2 := supDist_vertex_le hp1 hz
    have hz3 := _root_.YangMills.Construction.TorusFields.supDist_triangle z y o
    omega
end YangMills.Construction.BoxEvents
end
