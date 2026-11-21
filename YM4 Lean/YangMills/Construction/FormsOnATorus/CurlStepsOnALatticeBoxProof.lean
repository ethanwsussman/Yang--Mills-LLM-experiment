import YangMills.Construction.ColdChainAtEveryLevel.KernelsOnCellsProof
import YangMills.Construction.ColdChainAtEveryLevel.NearlyFlatPairingProof
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAboveTheFrameIsLocalProof
import YangMills.Construction.ColdStepAtMirrorFrames.ResponsesNearAFlatTopProof
import YangMills.Construction.FormsOnATorus.CurlStepsOnALatticeBox
import YangMills.Construction.HoleBesideASecondHole.CellsPutBackProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitForms
private def shiftBy (d : Fin 4) (s : ℕ) (y : Fin 4 → ℤ) : Fin 4 → ℤ := y + (s : ℤ) • Pi.single d (1 : ℤ)
private theorem shiftBy_succ (d : Fin 4) (s : ℕ) (y : Fin 4 → ℤ) :
    shiftBy d (s + 1) y = shiftBy d s y + Pi.single d 1 := by
  unfold shiftBy
  push_cast
  rw [add_smul, one_smul, add_assoc]
private theorem abs_le_telescope (g : (Fin 4 → ℤ) → ℝ) (d : Fin 4) (y : Fin 4 → ℤ) (s : ℕ) :
    |g y| ≤ |g (shiftBy d s y)| + ∑ u ∈ Finset.range s, |siteForwardDiff d g (shiftBy d u y)| := by
  induction s with
  | zero => simp [shiftBy]
  | succ s ih =>
    rw [Finset.sum_range_succ]
    have h : g (shiftBy d s y) = g (shiftBy d (s + 1) y) - siteForwardDiff d g (shiftBy d s y) := by
      simp [siteForwardDiff, shiftBy_succ]
    have h2 : |g (shiftBy d s y)| ≤ |g (shiftBy d (s + 1) y)| + |siteForwardDiff d g (shiftBy d s y)| := by
      rw [h]; exact abs_sub _ _
    linarith
private theorem mul_abs_le_line (t : ℕ) (g : (Fin 4 → ℤ) → ℝ) (d : Fin 4) (y : Fin 4 → ℤ) :
    (t : ℝ) * |g y| ≤ ∑ s ∈ Finset.range t, |g (shiftBy d s y)| +
      t * ∑ s ∈ Finset.range t, |siteForwardDiff d g (shiftBy d s y)| := by
  have h : ∀ s ∈ Finset.range t, |g y| ≤ |g (shiftBy d s y)| +
      ∑ u ∈ Finset.range t, |siteForwardDiff d g (shiftBy d u y)| := by
    intro s hs
    refine (abs_le_telescope g d y s).trans ?_
    have : ∑ u ∈ Finset.range s, |siteForwardDiff d g (shiftBy d u y)| ≤
        ∑ u ∈ Finset.range t, |siteForwardDiff d g (shiftBy d u y)| :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (Finset.mem_range.1 hs).le) fun _ _ _ => abs_nonneg _
    linarith
  have := Finset.sum_le_sum h
  simpa [Finset.sum_add_distrib, Finset.card_range] using this
private def boxSum (t : ℕ) : List (Fin 4) → ((Fin 4 → ℤ) → ℝ) → (Fin 4 → ℤ) → ℝ
  | [], f, y => f y
  | d :: ds, f, y => ∑ s ∈ Finset.range t, boxSum t ds f (shiftBy d s y)
private def dirSubsets : List (Fin 4) → List (List (Fin 4))
  | [] => [[]]
  | d :: ds => dirSubsets ds ++ (dirSubsets ds).map (· ++ [d])
private theorem finset_sum_list_map_comm {α : Type} (T : Finset ℕ) (l : List α) (f : ℕ → α → ℝ) :
    ∑ s ∈ T, (l.map (f s)).sum = (l.map fun a => ∑ s ∈ T, f s a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]
private theorem mul_list_map_sum {α : Type} (c : ℝ) (l : List α) (f : α → ℝ) :
    c * (l.map f).sum = (l.map fun a => c * f a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [mul_add, ih]
private theorem abs_le_boxSum (t : ℕ) (ds : List (Fin 4)) :
    ∀ (g : (Fin 4 → ℤ) → ℝ) (y : Fin 4 → ℤ), (t : ℝ) ^ ds.length * |g y| ≤
      ((dirSubsets ds).map fun S => (t : ℝ) ^ S.length *
        boxSum t ds (fun x => |siteForwardDiffs S g x|) y).sum := by
  induction ds with
  | nil =>
    intro g y
    simp [dirSubsets, boxSum, siteForwardDiffs]
  | cons d ds ih =>
    intro g y
    have h1 := mul_abs_le_line t g d y
    have ht : (0 : ℝ) ≤ (t : ℝ) ^ ds.length := by positivity
    have ht1 : (0 : ℝ) ≤ (t : ℝ) := by positivity
    have e1 : ∑ s ∈ Finset.range t, (t : ℝ) ^ ds.length * |g (shiftBy d s y)| ≤
        ∑ s ∈ Finset.range t, ((dirSubsets ds).map fun S => (t : ℝ) ^ S.length *
          boxSum t ds (fun x => |siteForwardDiffs S g x|) (shiftBy d s y)).sum :=
      Finset.sum_le_sum fun s _ => ih g _
    have e2 : ∑ s ∈ Finset.range t, (t : ℝ) ^ ds.length * |siteForwardDiff d g (shiftBy d s y)| ≤
        ∑ s ∈ Finset.range t, ((dirSubsets ds).map fun S => (t : ℝ) ^ S.length *
          boxSum t ds (fun x => |siteForwardDiffs S (siteForwardDiff d g) x|) (shiftBy d s y)).sum :=
      Finset.sum_le_sum fun s _ => ih (siteForwardDiff d g) _
    rw [finset_sum_list_map_comm] at e1 e2
    have e3 : (t : ℝ) ^ (d :: ds).length * |g y| ≤
        ∑ s ∈ Finset.range t, (t : ℝ) ^ ds.length * |g (shiftBy d s y)| +
        t * ∑ s ∈ Finset.range t, (t : ℝ) ^ ds.length * |siteForwardDiff d g (shiftBy d s y)| := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      calc (t : ℝ) ^ (d :: ds).length * |g y| = (t : ℝ) ^ ds.length * (t * |g y|) := by
            simp [pow_succ]; ring
        _ ≤ (t : ℝ) ^ ds.length * (∑ s ∈ Finset.range t, |g (shiftBy d s y)| +
              t * ∑ s ∈ Finset.range t, |siteForwardDiff d g (shiftBy d s y)|) :=
            mul_le_mul_of_nonneg_left h1 ht
        _ = _ := by ring
    refine e3.trans ?_
    have e4 := add_le_add e1 (mul_le_mul_of_nonneg_left e2 ht1)
    refine e4.trans (le_of_eq ?_)
    rw [mul_list_map_sum]
    simp only [dirSubsets, List.map_append, List.sum_append, List.map_map, boxSum]
    congr 1
    · congr 1
      apply List.map_congr_left
      intro S _
      simp [Finset.mul_sum]
    · congr 1
      apply List.map_congr_left
      intro S _
      have : siteForwardDiffs (S ++ [d]) g = siteForwardDiffs S (siteForwardDiff d g) := by
        simp [siteForwardDiffs, List.foldr_append]
      simp only [Function.comp, List.length_append, List.length_singleton, this, pow_succ]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
private theorem dirSubsets_length (ds : List (Fin 4)) : (dirSubsets ds).length = 2 ^ ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [dirSubsets, ih, pow_succ, mul_two]
private theorem length_le_of_mem_dirSubsets (ds : List (Fin 4)) :
    ∀ S ∈ dirSubsets ds, S.length ≤ ds.length := by
  induction ds with
  | nil => simp [dirSubsets]
  | cons d ds ih =>
    intro S hS
    simp only [dirSubsets, List.mem_append, List.mem_map] at hS
    rcases hS with h | ⟨S', h, rfl⟩
    · exact (ih S h).trans (by simp)
    · simpa using ih S' h
private theorem shiftBy_apply (d : Fin 4) (s : ℕ) (y : Fin 4 → ℤ) (i : Fin 4) :
    shiftBy d s y i = y i + (if i = d then (s : ℤ) else 0) := by
  simp [shiftBy, Pi.single_apply]
private theorem mem_siteCube_iff {r : ℕ} {x : Fin 4 → ℤ} : x ∈ siteCube r ↔ ∀ i, |x i| ≤ (r : ℤ) := by
  simp [siteCube, Fintype.mem_piFinset, abs_le]
private def cornerPoint (y : Fin 4 → ℤ) (q : ℕ × ℕ × ℕ × ℕ) : Fin 4 → ℤ :=
  shiftBy 3 q.2.2.2 (shiftBy 2 q.2.2.1 (shiftBy 1 q.2.1 (shiftBy 0 q.1 y)))
private theorem cornerPoint_apply (y : Fin 4 → ℤ) (q : ℕ × ℕ × ℕ × ℕ) :
    cornerPoint y q 0 = y 0 + q.1 ∧ cornerPoint y q 1 = y 1 + q.2.1 ∧
      cornerPoint y q 2 = y 2 + q.2.2.1 ∧ cornerPoint y q 3 = y 3 + q.2.2.2 := by
  simp [cornerPoint, shiftBy_apply]
private theorem cornerPoint_injective (y : Fin 4 → ℤ) : Function.Injective (cornerPoint y) := by
  intro q q' h
  obtain ⟨a0, a1, a2, a3⟩ := cornerPoint_apply y q
  obtain ⟨b0, b1, b2, b3⟩ := cornerPoint_apply y q'
  rw [h] at a0 a1 a2 a3
  obtain ⟨q0, q1, q2, q3⟩ := q
  obtain ⟨r0, r1, r2, r3⟩ := q'
  simp only at a0 a1 a2 a3 b0 b1 b2 b3
  have e0 : q0 = r0 := by omega
  have e1 : q1 = r1 := by omega
  have e2 : q2 = r2 := by omega
  have e3 : q3 = r3 := by omega
  simp [e0, e1, e2, e3]
private def cornerIndices (t : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  Finset.range t ×ˢ Finset.range t ×ˢ Finset.range t ×ˢ Finset.range t
private theorem boxSum_four (t : ℕ) (f : (Fin 4 → ℤ) → ℝ) (y : Fin 4 → ℤ) :
    boxSum t [0, 1, 2, 3] f y = ∑ q ∈ cornerIndices t, f (cornerPoint y q) := by
  simp only [boxSum, cornerIndices, Finset.sum_product, cornerPoint]
private theorem cornerPoint_mem {t q : ℕ} {y : Fin 4 → ℤ} (hy : y ∈ siteCube q) {w : ℕ × ℕ × ℕ × ℕ}
    (hw : w ∈ cornerIndices t) : cornerPoint y w ∈ siteCube (q + t) := by
  rw [mem_siteCube_iff] at hy ⊢
  simp only [cornerIndices, Finset.mem_product, Finset.mem_range] at hw
  obtain ⟨a0, a1, a2, a3⟩ := cornerPoint_apply y w
  obtain ⟨h0, h1, h2, h3⟩ := hw
  intro i
  have hi := hy i
  rw [abs_le] at hi ⊢
  push_cast
  fin_cases i
  · simp only [Fin.zero_eta, a0] at hi ⊢; omega
  · simp only [Fin.mk_one, a1] at hi ⊢; omega
  · have : (⟨2, by omega⟩ : Fin 4) = 2 := rfl
    simp only [this, a2] at hi ⊢; omega
  · have : (⟨3, by omega⟩ : Fin 4) = 3 := rfl
    simp only [this, a3] at hi ⊢; omega
private theorem abs_le_of_forwardDiff_norms {t q : ℕ} (ht : 1 ≤ t) (g : (Fin 4 → ℤ) → ℝ) {y : Fin 4 → ℤ}
    (hy : y ∈ siteCube q) {X : ℝ}
    (h : ∀ S : List (Fin 4), S.length ≤ 4 →
      (t : ℝ) ^ S.length * Real.sqrt (∑ x ∈ siteCube (q + t), siteForwardDiffs S g x ^ 2) ≤ (t : ℝ) ^ 2 * X) :
    |g y| ≤ 16 * X := by
  have hw := abs_le_boxSum t [0, 1, 2, 3] g y
  have hterm : ∀ a ∈ (dirSubsets [0, 1, 2, 3]).map (fun S => (t : ℝ) ^ S.length *
      boxSum t [0, 1, 2, 3] (fun x => |siteForwardDiffs S g x|) y), a ≤ (t : ℝ) ^ 4 * X := by
    intro a ha
    obtain ⟨S, hS, rfl⟩ := List.mem_map.1 ha
    have hlen : S.length ≤ 4 := by simpa using length_le_of_mem_dirSubsets _ S hS
    rw [boxSum_four]
    set f : (Fin 4 → ℤ) → ℝ := siteForwardDiffs S g
    have hcs : (∑ w ∈ cornerIndices t, |f (cornerPoint y w)|) ^ 2 ≤
        ((t : ℝ) ^ 2) ^ 2 * ∑ x ∈ siteCube (q + t), f x ^ 2 := by
      have h1 := sq_sum_le_card_mul_sum_sq (s := cornerIndices t) (f := fun w => |f (cornerPoint y w)|)
      have hc : ((cornerIndices t).card : ℝ) = ((t : ℝ) ^ 2) ^ 2 := by
        simp [cornerIndices, Finset.card_product]; ring
      rw [hc] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      simp only [sq_abs]
      have h2 : ∑ w ∈ cornerIndices t, f (cornerPoint y w) ^ 2 =
          ∑ x ∈ (cornerIndices t).image (cornerPoint y), f x ^ 2 :=
        (Finset.sum_image (f := fun x => f x ^ 2) fun a _ b _ e => cornerPoint_injective y e).symm
      rw [h2]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
      exact cornerPoint_mem hy hw
    have hsq : ∑ w ∈ cornerIndices t, |f (cornerPoint y w)| ≤
        (t : ℝ) ^ 2 * Real.sqrt (∑ x ∈ siteCube (q + t), f x ^ 2) := by
      have hs0 : 0 ≤ ∑ x ∈ siteCube (q + t), f x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
      rw [mul_pow, Real.sq_sqrt hs0]
      exact hcs
    calc (t : ℝ) ^ S.length * ∑ w ∈ cornerIndices t, |f (cornerPoint y w)|
        ≤ (t : ℝ) ^ S.length * ((t : ℝ) ^ 2 * Real.sqrt (∑ x ∈ siteCube (q + t), f x ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (t : ℝ) ^ 2 * ((t : ℝ) ^ S.length * Real.sqrt (∑ x ∈ siteCube (q + t), f x ^ 2)) := by ring
      _ ≤ (t : ℝ) ^ 2 * ((t : ℝ) ^ 2 * X) := mul_le_mul_of_nonneg_left (h S hlen) (by positivity)
      _ = (t : ℝ) ^ 4 * X := by ring
  have hsum := List.sum_le_card_nsmul _ _ hterm
  have hlen : ((dirSubsets [0, 1, 2, 3]).map (fun S => (t : ℝ) ^ S.length *
      boxSum t [0, 1, 2, 3] (fun x => |siteForwardDiffs S g x|) y)).length = 16 := by
    rw [List.length_map, dirSubsets_length]; rfl
  rw [hlen] at hsum
  have h4 := hw.trans hsum
  have h5 : (t : ℝ) ^ 4 * |g y| ≤ (t : ℝ) ^ 4 * (16 * X) := by
    simp only [List.length_cons, List.length_nil, nsmul_eq_mul] at h4
    push_cast at h4
    have : (t : ℝ) ^ 4 * (16 * X) = 16 * ((t : ℝ) ^ 4 * X) := by ring
    rw [this]
    simpa using h4
  exact le_of_mul_le_mul_left h5 (by positivity)
private def supNorm (x : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun i => (x i).natAbs
private theorem mem_siteCube_iff_supNorm {r : ℕ} {x : Fin 4 → ℤ} : x ∈ siteCube r ↔ supNorm x ≤ r := by apply _root_.YangMills.Construction.CellKernels.mem_centredBox_iff_supNorm <;> assumption
private theorem supNorm_le_add (x y : Fin 4 → ℤ) : supNorm x ≤ supNorm y + supNorm (x - y) := by
  rw [supNorm, Finset.sup_le_iff]
  intro i _
  have h1 : (y i).natAbs ≤ supNorm y := Finset.le_sup (f := fun i => (y i).natAbs) (Finset.mem_univ i)
  have h2 : ((x - y) i).natAbs ≤ supNorm (x - y) :=
    Finset.le_sup (f := fun i => ((x - y) i).natAbs) (Finset.mem_univ i)
  simp only [Pi.sub_apply] at h2
  omega
private theorem supNorm_sub_comm (x y : Fin 4 → ℤ) : supNorm (x - y) = supNorm (y - x) := by apply _root_.YangMills.Construction.FlatPairing.supNorm_sub_comm <;> assumption
private theorem bondSupDist_eq (b b' : IntBond) : bondSupDist b b' = supNorm (b.1 - b'.1) := rfl
private theorem bondSupDist_comm (b b' : IntBond) : bondSupDist b b' = bondSupDist b' b := by
  rw [bondSupDist_eq, bondSupDist_eq, supNorm_sub_comm]
private theorem card_bondCube (r : ℕ) : ((bondCube r).card : ℝ) = 4 * (2 * r + 1) ^ 4 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtFrameLocalityAux.card_bondLabels <;> assumption
private theorem card_sphere_le (H : Finset IntBond) (b : IntBond) (t : ℕ) :
    ((H.filter fun b' => bondSupDist b b' = t).card : ℝ) ≤ 4 * (2 * t + 1) ^ 4 := by
  rw [← card_bondCube]
  have : (H.filter fun b' => bondSupDist b b' = t).card ≤ (bondCube t).card := by
    refine Finset.card_le_card_of_injOn (fun b' => (b'.1 - b.1, b'.2)) ?_ ?_
    · intro b' hb'
      have hb := (Finset.mem_filter.1 hb').2
      simp only [bondCube, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.coe_univ,
        Set.mem_univ, and_true, mem_siteCube_iff_supNorm]
      rw [supNorm_sub_comm, ← bondSupDist_eq (b := b) (b' := b')]
      exact hb.le
    · intro a _ a' _ h
      simp only [Prod.mk.injEq, sub_left_inj] at h
      exact Prod.ext h.1 h.2
  exact_mod_cast this
private theorem schur_bound (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (H : Finset IntBond) (b : IntBond),
      ∑ b' ∈ H, (bondSupDist b b' : ℝ) ^ 2 * (C * Real.exp (-(c * bondSupDist b b'))) ≤ K := by
  set f : ℕ → ℝ := fun t => (t : ℝ) ^ 2 * (C * Real.exp (-(c * t))) with hf
  set g : ℕ → ℝ := fun t => 4 * (2 * (t : ℝ) + 1) ^ 4 * f t with hg
  have hf0 : ∀ t, 0 ≤ f t := fun t => by simp only [hf]; positivity
  have hg0 : ∀ t, 0 ≤ g t := fun t => by
    simp only [hg]
    have := hf0 t
    positivity
  have hr : ‖Real.exp (-c)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_lt_exp.2 (by linarith : -c < 0)).trans_eq Real.exp_zero
  have hsum : Summable g := by
    have h6 := (summable_pow_mul_geometric_of_norm_lt_one 6 hr).mul_left (4 * 81 * C)
    refine Summable.of_nonneg_of_le hg0 (fun t => ?_) h6
    have hexp : Real.exp (-(c * t)) = Real.exp (-c) ^ t := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    simp only [hg, hf, hexp]
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
      have h3 : (2 * (t : ℝ) + 1) ^ 4 ≤ 81 * (t : ℝ) ^ 4 := by
        have : 2 * (t : ℝ) + 1 ≤ 3 * t := by linarith
        calc (2 * (t : ℝ) + 1) ^ 4 ≤ (3 * (t : ℝ)) ^ 4 := by gcongr
          _ = 81 * (t : ℝ) ^ 4 := by ring
      calc 4 * (2 * (t : ℝ) + 1) ^ 4 * ((t : ℝ) ^ 2 * (C * Real.exp (-c) ^ t))
          ≤ 4 * (81 * (t : ℝ) ^ 4) * ((t : ℝ) ^ 2 * (C * Real.exp (-c) ^ t)) := by gcongr
        _ = 4 * 81 * C * ((t : ℝ) ^ 6 * Real.exp (-c) ^ t) := by ring
  refine ⟨∑' t, g t, tsum_nonneg hg0, fun H b => ?_⟩
  have h1 : ∑ b' ∈ H, f (bondSupDist b b') =
      ∑ t ∈ H.image (bondSupDist b), (H.filter fun b' => bondSupDist b b' = t).card • f t :=
    Finset.sum_comp f (bondSupDist b)
  have h2 : ∑ t ∈ H.image (bondSupDist b), (H.filter fun b' => bondSupDist b b' = t).card • f t ≤
      ∑ t ∈ H.image (bondSupDist b), g t := by
    refine Finset.sum_le_sum fun t _ => ?_
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (card_sphere_le H b t) (hf0 t)
  have h3 := hsum.sum_le_tsum (H.image (bondSupDist b)) fun t _ => hg0 t
  calc _ = ∑ b' ∈ H, f (bondSupDist b b') := rfl
    _ ≤ _ := (h1.le.trans h2).trans h3
private def cutoff (r t : ℕ) (x : Fin 4 → ℤ) : ℝ :=
  max 0 (min 1 (((r : ℝ) + 1 + t - supNorm x) / t))
private theorem cutoff_mem_Icc (r t : ℕ) (x) : 0 ≤ cutoff r t x ∧ cutoff r t x ≤ 1 := by
  unfold cutoff
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
private theorem cutoff_eq_one {r t : ℕ} (ht : 1 ≤ t) {x} (h : supNorm x ≤ r + 1) : cutoff r t x = 1 := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have h1 : (supNorm x : ℝ) ≤ r + 1 := by exact_mod_cast h
  have : 1 ≤ ((r : ℝ) + 1 + t - supNorm x) / t := by
    rw [le_div_iff₀ ht0]; linarith
  unfold cutoff
  rw [min_eq_left this, max_eq_right zero_le_one]
private theorem cutoff_eq_zero {r t : ℕ} (ht : 1 ≤ t) {x} (h : r + 1 + t ≤ supNorm x) : cutoff r t x = 0 := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have h1 : (r : ℝ) + 1 + t ≤ supNorm x := by exact_mod_cast h
  have : ((r : ℝ) + 1 + t - supNorm x) / t ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ht0.le
  unfold cutoff
  rw [min_eq_right (this.trans zero_le_one), max_eq_left this]
private theorem clamp_lipschitz (a b : ℝ) : |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |a - b| := by apply _root_.YangMills.Construction.Reinsertion.abs_clamp_sub_clamp_le <;> assumption
private theorem cutoff_lipschitz {r t : ℕ} (ht : 1 ≤ t) (x y) :
    |cutoff r t x - cutoff r t y| ≤ (supNorm (x - y) : ℝ) / t := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  refine (clamp_lipschitz _ _).trans ?_
  have e : ((r : ℝ) + 1 + t - supNorm x) / t - ((r : ℝ) + 1 + t - supNorm y) / t =
      ((supNorm y : ℝ) - supNorm x) / t := by ring
  rw [e, abs_div, abs_of_pos ht0]
  refine div_le_div_of_nonneg_right ?_ ht0.le
  rw [abs_le]
  have h1 : (supNorm x : ℝ) ≤ supNorm y + supNorm (x - y) := by exact_mod_cast supNorm_le_add x y
  have h2 : (supNorm y : ℝ) ≤ supNorm x + supNorm (y - x) := by exact_mod_cast supNorm_le_add y x
  rw [supNorm_sub_comm y x] at h2
  constructor <;> linarith
private theorem localized_quadratic_identity (U : Finset IntBond) (Q : IntBond → IntBond → ℝ)
    (hs : ∀ b b', Q b b' = Q b' b) (χ w : IntBond → ℝ) :
    ∑ b ∈ U, ∑ b' ∈ U, (χ b * w b) * Q b b' * (χ b' * w b') =
      ∑ b' ∈ U, χ b' ^ 2 * w b' * ∑ b ∈ U, w b * Q b b' -
      (1 / 2) * ∑ b ∈ U, ∑ b' ∈ U, (χ b - χ b') ^ 2 * (w b * Q b b' * w b') := by
  have h1 : ∑ b ∈ U, ∑ b' ∈ U, χ b ^ 2 * (w b * Q b b' * w b') =
      ∑ b ∈ U, ∑ b' ∈ U, χ b' ^ 2 * (w b * Q b b' * w b') := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [hs b' b]; ring
  have h2 : ∑ b' ∈ U, χ b' ^ 2 * w b' * ∑ b ∈ U, w b * Q b b' =
      ∑ b ∈ U, ∑ b' ∈ U, χ b' ^ 2 * (w b * Q b b' * w b') := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have h3 : ∑ b ∈ U, ∑ b' ∈ U, (χ b - χ b') ^ 2 * (w b * Q b b' * w b') =
      ∑ b ∈ U, ∑ b' ∈ U, χ b ^ 2 * (w b * Q b b' * w b') -
      2 * ∑ b ∈ U, ∑ b' ∈ U, (χ b * w b) * Q b b' * (χ b' * w b') +
      ∑ b ∈ U, ∑ b' ∈ U, χ b' ^ 2 * (w b * Q b b' * w b') := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  rw [h2, h3, h1]
  ring
private theorem supNorm_add_single_le (x : Fin 4 → ℤ) (i : Fin 4) :
    supNorm (x + Pi.single i 1) ≤ supNorm x + 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearUniformTop.offsetSupNorm_add_single_le <;> assumption
private theorem close_pair_bound {δ d t E q a b : ℝ} (ht : 0 < t) (hδ : δ ^ 2 ≤ (d / t) ^ 2) (hq : |q| ≤ E) :
    δ ^ 2 * (|a| * |q| * |b|) ≤ d ^ 2 * E / t ^ 2 * ((a ^ 2 + b ^ 2) / 2) := by
  have hab : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have hE : 0 ≤ E := (abs_nonneg _).trans hq
  calc δ ^ 2 * (|a| * |q| * |b|) = δ ^ 2 * |q| * (|a| * |b|) := by ring
    _ ≤ (d / t) ^ 2 * E * ((a ^ 2 + b ^ 2) / 2) := by gcongr
    _ = d ^ 2 * E / t ^ 2 * ((a ^ 2 + b ^ 2) / 2) := by
        rw [div_pow]; ring
private theorem distant_pair_bound {δ W E q a b : ℝ} (hδ : δ ^ 2 ≤ 1) (ha : |a| ≤ W) (hb : |b| ≤ W)
    (hq : |q| ≤ E) :
    δ ^ 2 * (|a| * |q| * |b|) ≤ W ^ 2 * E := by
  have hW : 0 ≤ W := (abs_nonneg _).trans ha
  have hE : 0 ≤ E := (abs_nonneg _).trans hq
  calc δ ^ 2 * (|a| * |q| * |b|) ≤ 1 * (W * E * W) := by gcongr
    _ = W ^ 2 * E := by ring
set_option maxHeartbeats 1600000 in
private theorem caccioppoli {cK c C K : ℝ} {Q : IntBond → IntBond → ℝ} (hQ : IsGradientBlindKernel cK c C Q)
    (hc : 0 < c) (hK0 : 0 ≤ K)
    (hK : ∀ (H : Finset IntBond) (b : IntBond),
      ∑ b' ∈ H, (bondSupDist b b' : ℝ) ^ 2 * (C * Real.exp (-(c * bondSupDist b b'))) ≤ K)
    {w : IntBond → ℝ} {ρ r t : ℕ} {W ε : ℝ} (ht : 1 ≤ t) (hW0 : 0 ≤ W)
    (hs : ∀ b, b ∉ bondCube ρ → w b = 0) (hW : ∀ b, |w b| ≤ W)
    (hres : ∀ b ∈ bondCube (r + 1 + t), |kernelResidual Q w b| ≤ ε) :
    2 * cK * ∑ p ∈ plaquetteCube r, intCurl w p ^ 2 ≤
      K / (t : ℝ) ^ 2 * ∑ b ∈ bondCube (r + 1 + 2 * t), w b ^ 2 +
      ((bondCube (r + 1 + t)).card : ℝ) * (W * ε) +
      ((bondCube (r + 1 + t)).card : ℝ) *
        (((bondCube ρ).card : ℝ) * (W ^ 2 * (C * Real.exp (-(c * t))))) := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hC : 0 ≤ C := by
    have h1 := hQ.decay ((0 : Fin 4 → ℤ), (0 : Fin 4)) ((0 : Fin 4 → ℤ), (0 : Fin 4))
    have hp := Real.exp_pos
      (-(c * bondSupDist ((0 : Fin 4 → ℤ), (0 : Fin 4)) ((0 : Fin 4 → ℤ), (0 : Fin 4))))
    by_contra hn
    push Not at hn
    have := mul_neg_of_neg_of_pos hn hp
    linarith [abs_nonneg (Q ((0 : Fin 4 → ℤ), (0 : Fin 4)) ((0 : Fin 4 → ℤ), (0 : Fin 4)))]
  set U := bondCube ρ with hU
  set G₀ := bondCube (r + 1 + t) with hG₀
  set G₁ := bondCube (r + 1 + 2 * t) with hG₁
  set χ : IntBond → ℝ := fun b => cutoff r t b.1 with hχ
  set y : IntBond → ℝ := fun b => χ b * w b with hy
  have hyU : ∀ b, b ∉ U → y b = 0 := fun b hb => by simp [hy, hs b hb]
  set yF : IntBond →₀ ℝ := Finsupp.onFinset U y (fun b hb => by_contra fun h => hb (hyU b h)) with hyF
  have hyv : ∀ b, yF b = y b := fun b => rfl
  have hfl := hQ.coercive yF (plaquetteCube r) (fun p hp => by
    simpa [plaquetteCube] using (Finset.mem_product.1 hp).2)
  have hsup : yF.support ⊆ U := Finsupp.support_onFinset_subset
  have hdouble : ∑ b ∈ yF.support, ∑ b' ∈ yF.support, yF b * Q b b' * yF b' =
      ∑ b ∈ U, ∑ b' ∈ U, (χ b * w b) * Q b b' * (χ b' * w b') := by
    have e1 : ∀ b, ∑ b' ∈ yF.support, yF b * Q b b' * yF b' = ∑ b' ∈ U, yF b * Q b b' * yF b' := by
      intro b
      refine Finset.sum_subset hsup fun b' _ hb' => ?_
      rw [Finsupp.notMem_support_iff.1 hb', mul_zero]
    simp only [e1]
    rw [Finset.sum_subset hsup fun b _ hb => by
      refine Finset.sum_eq_zero fun b' _ => ?_
      rw [Finsupp.notMem_support_iff.1 hb, zero_mul, zero_mul]]
    rfl
  have hcurl : ∑ p ∈ plaquetteCube r, intCurl yF p ^ 2 = ∑ p ∈ plaquetteCube r, intCurl w p ^ 2 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp1 : supNorm p.1 ≤ r := mem_siteCube_iff_supNorm.1 (Finset.mem_product.1 hp).1
    have hb : ∀ x : Fin 4 → ℤ, supNorm x ≤ r + 1 → ∀ i, yF (x, i) = w (x, i) := by
      intro x hx i
      rw [hyv]
      simp [hy, hχ, cutoff_eq_one ht hx]
    simp only [intCurl]
    rw [hb _ (by omega), hb _ ((supNorm_add_single_le _ _).trans (by omega)),
      hb _ ((supNorm_add_single_le _ _).trans (by omega)), hb _ (by omega)]
  rw [hcurl, hdouble, localized_quadratic_identity U Q hQ.symm χ w] at hfl
  have hres' : ∀ b', ∑ b ∈ U, w b * Q b b' = kernelResidual Q w b' := by
    intro b'
    symm
    refine finsum_eq_sum_of_support_subset _ ?_
    intro b hb
    by_contra hn
    exact hb (by simp [hs b (by simpa using hn)])
  have hχ0 : ∀ b, b ∉ G₀ → χ b = 0 := by
    intro b hb
    refine cutoff_eq_zero ht ?_
    by_contra hn
    exact hb (Finset.mem_product.2 ⟨mem_siteCube_iff_supNorm.2 (by omega), Finset.mem_univ _⟩)
  have hχr : ∀ b, 0 ≤ χ b ∧ χ b ≤ 1 := fun b => cutoff_mem_Icc r t b.1
  have piece1 : ∑ b' ∈ U, χ b' ^ 2 * w b' * ∑ b ∈ U, w b * Q b b' ≤ (G₀.card : ℝ) * (W * ε) := by
    have hε : ∀ b ∈ G₀, 0 ≤ ε := fun b hb => (abs_nonneg _).trans (hres b hb)
    have h1 : ∀ b' ∈ U, χ b' ^ 2 * w b' * ∑ b ∈ U, w b * Q b b' ≤ if b' ∈ G₀ then W * ε else 0 := by
      intro b' _
      by_cases hb : b' ∈ G₀
      · rw [if_pos hb, hres']
        have e1 : χ b' ^ 2 ≤ 1 := by nlinarith [hχr b']
        have e2 := hW b'
        have e3 := hres b' hb
        calc χ b' ^ 2 * w b' * kernelResidual Q w b' ≤ |χ b' ^ 2 * w b' * kernelResidual Q w b'| :=
              le_abs_self _
          _ = χ b' ^ 2 * |w b'| * |kernelResidual Q w b'| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
          _ ≤ 1 * W * ε := by
              have := hε b' hb
              gcongr
          _ = W * ε := by ring
      · rw [if_neg hb, hχ0 b' hb]; simp
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases hG : (U.filter fun b => b ∈ G₀).card = 0
    · rw [hG]
      have : (0 : ℝ) ≤ (G₀.card : ℝ) * (W * ε) := by
        by_cases hE : G₀.Nonempty
        · obtain ⟨b, hb⟩ := hE
          have := hε b hb
          positivity
        · rw [Finset.not_nonempty_iff_eq_empty.1 hE]; simp
      simpa using this
    · obtain ⟨b, hb⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hG)
      have hWε : 0 ≤ W * ε := mul_nonneg hW0 (hε b (Finset.mem_filter.1 hb).2)
      refine mul_le_mul_of_nonneg_right ?_ hWε
      exact_mod_cast Finset.card_le_card fun b hb => (Finset.mem_filter.1 hb).2
  set f : IntBond → IntBond → ℝ := fun b b' => (χ b - χ b') ^ 2 * (|w b| * |Q b b'| * |w b'|) with hf
  have hf0 : ∀ b b', 0 ≤ f b b' := fun b b' => by simp only [hf]; positivity
  have hfs : ∀ b b', f b b' = f b' b := fun b b' => by
    simp only [hf]
    rw [hQ.symm b b']
    ring
  set Ut := U.filter fun b => b ∈ G₀ with hUt
  have step1 : -((1 / 2) * ∑ b ∈ U, ∑ b' ∈ U, (χ b - χ b') ^ 2 * (w b * Q b b' * w b')) ≤
      ∑ b ∈ Ut, ∑ b' ∈ U, f b b' := by
    set g : IntBond → IntBond → ℝ := fun b b' => if b ∈ G₀ then f b b' else 0 with hg
    have e1 : ∑ b ∈ Ut, ∑ b' ∈ U, f b b' = ∑ b ∈ U, ∑ b' ∈ U, g b b' := by
      rw [hUt, Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : b ∈ G₀
      · simp [hg, hb]
      · simp [hg, hb]
    have e2 : ∑ b ∈ U, ∑ b' ∈ U, g b b' = ∑ b ∈ U, ∑ b' ∈ U, g b' b := Finset.sum_comm
    have e3 : ∀ b b', -((χ b - χ b') ^ 2 * (w b * Q b b' * w b')) ≤ g b b' + g b' b := by
      intro b b'
      have e4 : -((χ b - χ b') ^ 2 * (w b * Q b b' * w b')) ≤ f b b' := by
        have := neg_abs_le (w b * Q b b' * w b')
        simp only [hf]
        rw [abs_mul, abs_mul] at this
        nlinarith [sq_nonneg (χ b - χ b')]
      by_cases h1 : b ∈ G₀
      · have : g b b' = f b b' := by simp [hg, h1]
        have h2 : 0 ≤ g b' b := by
          simp only [hg]
          split_ifs
          · exact hf0 _ _
          · exact le_rfl
        linarith
      · by_cases h2 : b' ∈ G₀
        · have : g b' b = f b b' := by simp [hg, h2, hfs b b']
          have h3 : 0 ≤ g b b' := by simp [hg, h1]
          linarith
        · have : f b b' = 0 := by simp [hf, hχ0 b h1, hχ0 b' h2]
          have h3 : g b b' = 0 := by simp [hg, h1]
          have h4 : g b' b = 0 := by simp [hg, h2]
          linarith
    have e5 : -∑ b ∈ U, ∑ b' ∈ U, (χ b - χ b') ^ 2 * (w b * Q b b' * w b') ≤
        ∑ b ∈ U, ∑ b' ∈ U, g b b' + ∑ b ∈ U, ∑ b' ∈ U, g b' b := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun b _ => ?_
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun b' _ => e3 b b'
    rw [e1]
    linarith
  set u : IntBond → ℝ := fun b => if b ∈ G₁ then w b ^ 2 else 0 with hu
  have hu0 : ∀ b, 0 ≤ u b := fun b => by
    simp only [hu]
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  set m : IntBond → IntBond → ℝ := fun b b' =>
    (bondSupDist b b' : ℝ) ^ 2 * (C * Real.exp (-(c * bondSupDist b b'))) with hm
  have hm0 : ∀ b b', 0 ≤ m b b' := fun b b' => by simp only [hm]; positivity
  set B : ℝ := W ^ 2 * (C * Real.exp (-(c * t))) with hB
  have hB0 : 0 ≤ B := by simp only [hB]; positivity
  have hlip : ∀ b b', (χ b - χ b') ^ 2 ≤ ((bondSupDist b b' : ℝ) / t) ^ 2 := by
    intro b b'
    have := cutoff_lipschitz (r := r) ht b.1 b'.1
    rw [← bondSupDist_eq] at this
    calc (χ b - χ b') ^ 2 = |χ b - χ b'| ^ 2 := (sq_abs _).symm
      _ ≤ _ := by gcongr
  have step2 : ∀ b ∈ Ut, ∀ b' ∈ U, f b b' ≤ m b b' / (t : ℝ) ^ 2 * ((u b + u b') / 2) + B := by
    intro b hb b' _
    have hbG : b ∈ G₀ := (Finset.mem_filter.1 hb).2
    have hb0 : supNorm b.1 ≤ r + 1 + t := mem_siteCube_iff_supNorm.1 (Finset.mem_product.1 hbG).1
    by_cases hd : bondSupDist b b' ≤ t
    · have h1 : b ∈ G₁ := Finset.mem_product.2 ⟨mem_siteCube_iff_supNorm.2 (by omega), Finset.mem_univ _⟩
      have h2 : b' ∈ G₁ := by
        refine Finset.mem_product.2 ⟨mem_siteCube_iff_supNorm.2 ?_, Finset.mem_univ _⟩
        have := supNorm_le_add b'.1 b.1
        rw [supNorm_sub_comm, ← bondSupDist_eq] at this
        omega
      have e1 : u b = w b ^ 2 := by simp [hu, h1]
      have e2 : u b' = w b' ^ 2 := by simp [hu, h2]
      rw [e1, e2]
      have := close_pair_bound (a := w b) (b := w b') ht0 (hlip b b') (hQ.decay b b')
      exact le_add_of_le_of_nonneg this hB0
    · have h1 : (χ b - χ b') ^ 2 ≤ 1 := by
        have := hχr b
        have := hχr b'
        nlinarith
      have h2 : |Q b b'| ≤ C * Real.exp (-(c * t)) := by
        refine (hQ.decay b b').trans ?_
        have : (t : ℝ) ≤ bondSupDist b b' := by exact_mod_cast (not_le.1 hd).le
        gcongr
      have h4 : 0 ≤ m b b' / (t : ℝ) ^ 2 * ((u b + u b') / 2) := by
        have := hm0 b b'
        have := hu0 b
        have := hu0 b'
        positivity
      have h5 : f b b' ≤ B := distant_pair_bound h1 (hW b) (hW b') h2
      linarith
  have hcardUt : (Ut.card : ℝ) ≤ G₀.card := by
    exact_mod_cast Finset.card_le_card fun b hb => (Finset.mem_filter.1 hb).2
  have hsumU : ∑ b ∈ U, u b ≤ ∑ b ∈ G₁, w b ^ 2 := by
    simp only [hu]
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => (Finset.mem_filter.1 hb).2)
      fun _ _ _ => sq_nonneg _
  have hsumUt : ∑ b ∈ Ut, u b ≤ ∑ b ∈ G₁, w b ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => hu0 _).trans hsumU
  have step3 : ∑ b ∈ Ut, ∑ b' ∈ U, m b b' / (t : ℝ) ^ 2 * ((u b + u b') / 2) ≤
      K / (t : ℝ) ^ 2 * ∑ b ∈ G₁, w b ^ 2 := by
    have e1 : ∑ b ∈ Ut, ∑ b' ∈ U, m b b' / (t : ℝ) ^ 2 * ((u b + u b') / 2) =
        1 / (2 * (t : ℝ) ^ 2) * (∑ b ∈ Ut, u b * ∑ b' ∈ U, m b b') +
        1 / (2 * (t : ℝ) ^ 2) * (∑ b' ∈ U, u b' * ∑ b ∈ Ut, m b b') := by
      rw [Finset.mul_sum, Finset.mul_sum]
      have : ∑ b' ∈ U, 1 / (2 * (t : ℝ) ^ 2) * (u b' * ∑ b ∈ Ut, m b b') =
          ∑ b ∈ Ut, ∑ b' ∈ U, 1 / (2 * (t : ℝ) ^ 2) * (u b' * m b b') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b' _ => ?_
        rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [this, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b' _ => ?_
      field_simp
    have e2 : ∑ b ∈ Ut, u b * ∑ b' ∈ U, m b b' ≤ K * ∑ b ∈ G₁, w b ^ 2 := by
      calc ∑ b ∈ Ut, u b * ∑ b' ∈ U, m b b' ≤ ∑ b ∈ Ut, u b * K :=
            Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hK U b) (hu0 b)
        _ = K * ∑ b ∈ Ut, u b := by rw [← Finset.sum_mul, mul_comm]
        _ ≤ _ := mul_le_mul_of_nonneg_left hsumUt hK0
    have e3 : ∑ b' ∈ U, u b' * ∑ b ∈ Ut, m b b' ≤ K * ∑ b ∈ G₁, w b ^ 2 := by
      have hsym : ∀ b', ∑ b ∈ Ut, m b b' ≤ K := by
        intro b'
        have := hK Ut b'
        simpa only [hm, bondSupDist_comm b'] using this
      calc ∑ b' ∈ U, u b' * ∑ b ∈ Ut, m b b' ≤ ∑ b' ∈ U, u b' * K :=
            Finset.sum_le_sum fun b' _ => mul_le_mul_of_nonneg_left (hsym b') (hu0 b')
        _ = K * ∑ b ∈ U, u b := by rw [← Finset.sum_mul, mul_comm]
        _ ≤ _ := mul_le_mul_of_nonneg_left hsumU hK0
    rw [e1]
    have hp : 0 ≤ 1 / (2 * (t : ℝ) ^ 2) := by positivity
    have := mul_le_mul_of_nonneg_left e2 hp
    have := mul_le_mul_of_nonneg_left e3 hp
    have e4 : K / (t : ℝ) ^ 2 * ∑ b ∈ G₁, w b ^ 2 =
        1 / (2 * (t : ℝ) ^ 2) * (K * ∑ b ∈ G₁, w b ^ 2) +
          1 / (2 * (t : ℝ) ^ 2) * (K * ∑ b ∈ G₁, w b ^ 2) := by
      field_simp
      ring
    linarith
  have step4 : ∑ b ∈ Ut, ∑ b' ∈ U, f b b' ≤
      K / (t : ℝ) ^ 2 * ∑ b ∈ G₁, w b ^ 2 + (G₀.card : ℝ) * ((U.card : ℝ) * B) := by
    have e1 : ∑ b ∈ Ut, ∑ b' ∈ U, f b b' ≤
        ∑ b ∈ Ut, ∑ b' ∈ U, (m b b' / (t : ℝ) ^ 2 * ((u b + u b') / 2) + B) :=
      Finset.sum_le_sum fun b hb => Finset.sum_le_sum fun b' hb' => step2 b hb b' hb'
    have e2 : ∑ b ∈ Ut, ∑ b' ∈ U, (m b b' / (t : ℝ) ^ 2 * ((u b + u b') / 2) + B) =
        ∑ b ∈ Ut, ∑ b' ∈ U, m b b' / (t : ℝ) ^ 2 * ((u b + u b') / 2) +
          (Ut.card : ℝ) * ((U.card : ℝ) * B) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have e3 : (Ut.card : ℝ) * ((U.card : ℝ) * B) ≤ (G₀.card : ℝ) * ((U.card : ℝ) * B) :=
      mul_le_mul_of_nonneg_right hcardUt (by positivity)
    linarith
  linarith
private def contract (d : Fin 4) (F : (Fin 4 → ℤ) × Fin 4 × Fin 4 → ℝ) : IntBond → ℝ :=
  fun b => F (b.1, d, b.2)
private def iteratedContract (v : IntBond → ℝ) : List (Fin 4) → IntBond → ℝ
  | [] => v
  | d :: l => contract d (intCurl (iteratedContract v l))
private theorem intCurl_contract (d : Fin 4) (w : IntBond → ℝ) :
    intCurl (contract d (intCurl w)) = plaquetteForwardDiff d (intCurl w) := by
  funext p
  obtain ⟨x, i, j⟩ := p
  simp only [intCurl, contract, plaquetteForwardDiff]
  have h1 : x + Pi.single i 1 + Pi.single d 1 = x + Pi.single d 1 + Pi.single i 1 := add_right_comm _ _ _
  have h2 : x + Pi.single j 1 + Pi.single d 1 = x + Pi.single d 1 + Pi.single j 1 := add_right_comm _ _ _
  have h3 : x + Pi.single i 1 + Pi.single j 1 = x + Pi.single j 1 + Pi.single i 1 := add_right_comm _ _ _
  rw [h1, h2, h3]
  ring
private theorem intCurl_iteratedContract (v : IntBond → ℝ) (l : List (Fin 4)) :
    intCurl (iteratedContract v l) = plaquetteForwardDiffs l (intCurl v) := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    show intCurl (contract d (intCurl (iteratedContract v l))) = _
    rw [intCurl_contract, ih]
    rfl
private theorem supNorm_le_add_single (x : Fin 4 → ℤ) (i : Fin 4) :
    supNorm x ≤ supNorm (x + Pi.single i 1) + 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearUniformTop.offsetSupNorm_le_add_single <;> assumption
private theorem notMem_bondCube_iff {ρ : ℕ} {b : IntBond} : b ∉ bondCube ρ ↔ ρ < supNorm b.1 := by
  simp [bondCube, Finset.mem_product, mem_siteCube_iff_supNorm]
private theorem contract_support {w : IntBond → ℝ} {ρ : ℕ} (d : Fin 4)
    (hs : ∀ b, b ∉ bondCube ρ → w b = 0) :
    ∀ b, b ∉ bondCube (ρ + 1) → contract d (intCurl w) b = 0 := by
  intro b hb
  rw [notMem_bondCube_iff] at hb
  have h1 := supNorm_le_add_single b.1 d
  have h2 := supNorm_le_add_single b.1 b.2
  simp only [contract, intCurl]
  rw [hs (b.1, d) (notMem_bondCube_iff.2 (by simpa using (by omega : ρ < supNorm b.1))),
    hs (b.1 + Pi.single d 1, b.2)
      (notMem_bondCube_iff.2 (by simpa using (by omega : ρ < supNorm (b.1 + Pi.single d 1)))),
    hs (b.1 + Pi.single b.2 1, d)
      (notMem_bondCube_iff.2 (by simpa using (by omega : ρ < supNorm (b.1 + Pi.single b.2 1)))),
    hs (b.1, b.2) (notMem_bondCube_iff.2 (by simpa using (by omega : ρ < supNorm b.1)))]
  simp
private theorem abs_contract_le {w : IntBond → ℝ} {W : ℝ} (d : Fin 4) (hW : ∀ b, |w b| ≤ W) (b : IntBond) :
    |contract d (intCurl w) b| ≤ 4 * W := by
  simp only [contract, intCurl]
  have h1 := hW (b.1, d)
  have h2 := hW (b.1 + Pi.single d 1, b.2)
  have h3 := hW (b.1 + Pi.single b.2 1, d)
  have h4 := hW (b.1, b.2)
  rw [abs_le] at *
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
private theorem finite_support_mul {w : IntBond → ℝ} {ρ : ℕ} (hs : ∀ b, b ∉ bondCube ρ → w b = 0)
    (g : IntBond → ℝ) : (Function.support fun b => w b * g b).Finite := by
  refine (bondCube ρ).finite_toSet.subset ?_
  intro b hb
  by_contra hn
  exact hb (by simp [hs b (by simpa using hn)])
private def bondTranslate (d : Fin 4) : IntBond ≃ IntBond where
  toFun b := (b.1 + Pi.single d 1, b.2)
  invFun b := (b.1 - Pi.single d 1, b.2)
  left_inv b := by simp
  right_inv b := by simp
private theorem kernelResidual_contract {cK c C : ℝ} {Q : IntBond → IntBond → ℝ}
    (hQ : IsGradientBlindKernel cK c C Q) {w : IntBond → ℝ} {ρ : ℕ} (hs : ∀ b, b ∉ bondCube ρ → w b = 0)
    (d : Fin 4) (b' : IntBond) :
    kernelResidual Q (contract d (intCurl w)) b' =
      kernelResidual Q w (b'.1 + Pi.single d 1, b'.2) - kernelResidual Q w b' := by
  set A : IntBond → ℝ := fun b => w (b.1 + Pi.single d 1, b.2) with hA
  set φ : (Fin 4 → ℤ) → ℝ := fun x => w (x, d) with hφ
  set G : IntBond → ℝ := fun b => φ b.1 - φ (b.1 + Pi.single b.2 1) with hG
  have hsA : ∀ b, b ∉ bondCube (ρ + 1) → A b = 0 := by
    intro b hb
    rw [notMem_bondCube_iff] at hb
    have := supNorm_le_add_single b.1 d
    exact hs _ (notMem_bondCube_iff.2 (by simpa using (by omega : ρ < supNorm (b.1 + Pi.single d 1))))
  have hsG : ∀ b, b ∉ bondCube (ρ + 1) → G b = 0 := by
    intro b hb
    rw [notMem_bondCube_iff] at hb
    have := supNorm_le_add_single b.1 b.2
    simp only [hG, hφ]
    rw [hs (b.1, d) (notMem_bondCube_iff.2 (by simpa using (by omega : ρ < supNorm b.1))),
      hs (b.1 + Pi.single b.2 1, d)
        (notMem_bondCube_iff.2 (by simpa using (by omega : ρ < supNorm (b.1 + Pi.single b.2 1))))]
    simp
  have hsplit : ∀ b, contract d (intCurl w) b * Q b b' =
      A b * Q b b' - w b * Q b b' + G b * Q b b' := by
    intro b
    simp only [contract, intCurl, hA, hG, hφ]
    ring
  have hAres : ∑ᶠ b, A b * Q b b' = kernelResidual Q w (b'.1 + Pi.single d 1, b'.2) := by
    have e : ∀ b, A b * Q b b' =
        (fun c => w c * Q c (b'.1 + Pi.single d 1, b'.2)) (bondTranslate d b) := by
      intro b
      simp only [hA, bondTranslate, Equiv.coe_fn_mk]
      rw [hQ.shift_invariant d b b']
    simp only [e]
    exact finsum_comp_equiv (f := fun c => w c * Q c (b'.1 + Pi.single d 1, b'.2)) (bondTranslate d)
  have hGres : ∑ᶠ b, G b * Q b b' = 0 := by
    rw [finsum_eq_sum_of_support_subset (f := fun b => G b * Q b b') (s := bondCube (ρ + 1)) (by
      intro b hb
      by_contra hn
      exact hb (by simp [hsG b (by simpa using hn)]))]
    set φF : (Fin 4 → ℤ) →₀ ℝ := Finsupp.onFinset (siteCube ρ) φ (fun x hx => by
      by_contra hn
      exact hx (hs (x, d) (by simpa [bondCube, Finset.mem_product] using hn))) with hφF
    have hb := hQ.kills_gradients b' φF
    have hb2 : HasSum (fun b : IntBond => Q b' b * (φF b.1 - φF (b.1 + Pi.single b.2 1)))
        (∑ b ∈ bondCube (ρ + 1), Q b' b * (φF b.1 - φF (b.1 + Pi.single b.2 1))) :=
      hasSum_sum_of_ne_finset_zero fun b hb => by
        have : G b = 0 := hsG b hb
        change Q b' b * G b = 0
        rw [this, mul_zero]
    have := hb.unique hb2
    rw [this]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hQ.symm b b', mul_comm]
    rfl
  have hfA := finite_support_mul hsA (fun b => Q b b')
  have hfw := finite_support_mul hs (fun b => Q b b')
  have hfG := finite_support_mul hsG (fun b => Q b b')
  simp only [kernelResidual, hsplit]
  rw [finsum_add_distrib, finsum_sub_distrib hfA hfw, hAres, hGres, add_zero]
  · rfl
  · exact (hfA.union hfw).subset (Function.support_sub _ _)
  · exact hfG
private theorem sum_sq_contract_le (G : (Fin 4 → ℤ) × Fin 4 × Fin 4 → ℝ) (x : Fin 4 → ℤ) (d : Fin 4)
    (hd : ∀ i, G (x, i, i) = 0) (ha : ∀ i j, G (x, j, i) = -G (x, i, j)) :
    ∑ i : Fin 4, G (x, d, i) ^ 2 ≤
      ∑ q ∈ Finset.univ.filter (fun q : Fin 4 × Fin 4 => q.1 < q.2), G (x, q.1, q.2) ^ 2 := by
  have hfil : Finset.univ.filter (fun q : Fin 4 × Fin 4 => q.1 < q.2) =
      {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by decide
  rw [hfil]
  have e : ∀ i j, G (x, j, i) ^ 2 = G (x, i, j) ^ 2 := fun i j => by rw [ha]; ring
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Finset.sum_singleton,
    Fin.sum_univ_four]
  have h01 := sq_nonneg (G (x, 0, 1))
  have h02 := sq_nonneg (G (x, 0, 2))
  have h03 := sq_nonneg (G (x, 0, 3))
  have h12 := sq_nonneg (G (x, 1, 2))
  have h13 := sq_nonneg (G (x, 1, 3))
  have h23 := sq_nonneg (G (x, 2, 3))
  fin_cases d <;> simp [hd, e 0 1, e 0 2, e 0 3, e 1 2, e 1 3, e 2 3] <;> linarith
private theorem intCurl_diag (w : IntBond → ℝ) (x : Fin 4 → ℤ) (i : Fin 4) : intCurl w (x, i, i) = 0 := by
  simp [intCurl]
private theorem intCurl_antisymm (w : IntBond → ℝ) (x : Fin 4 → ℤ) (i j : Fin 4) :
    intCurl w (x, j, i) = -intCurl w (x, i, j) := by
  simp only [intCurl]
  ring
private theorem sum_sq_contract_le_curl (w : IntBond → ℝ) (d : Fin 4) (r : ℕ) :
    ∑ b ∈ bondCube r, contract d (intCurl w) b ^ 2 ≤ ∑ p ∈ plaquetteCube r, intCurl w p ^ 2 := by
  simp only [bondCube, plaquetteCube, Finset.sum_product, contract]
  refine Finset.sum_le_sum fun x _ => ?_
  exact sum_sq_contract_le (intCurl w) x d (intCurl_diag w x) (intCurl_antisymm w x)
private theorem iteratedContract_support {v : IntBond → ℝ} {ρ : ℕ} (hs : ∀ b, b ∉ bondCube ρ → v b = 0)
    (l : List (Fin 4)) : ∀ b, b ∉ bondCube (ρ + l.length) → iteratedContract v l b = 0 := by
  induction l with
  | nil => exact fun b hb => hs b (by simpa using hb)
  | cons d l ih => exact contract_support d ih
private theorem abs_iteratedContract_le {v : IntBond → ℝ} {W : ℝ} (hW : ∀ b, |v b| ≤ W) (l : List (Fin 4)) :
    ∀ b, |iteratedContract v l b| ≤ 4 ^ l.length * W := by
  induction l with
  | nil => exact fun b => by simpa [iteratedContract] using hW b
  | cons d l ih =>
    intro b
    have := abs_contract_le d ih b
    simp only [iteratedContract, List.length_cons, pow_succ]
    linarith
private theorem abs_kernelResidual_iteratedContract_le {cK c C : ℝ} {Q : IntBond → IntBond → ℝ}
    (hQ : IsGradientBlindKernel cK c C Q) {v : IntBond → ℝ} {ρ r : ℕ} {ε : ℝ}
    (hs : ∀ b, b ∉ bondCube ρ → v b = 0) (hε : ∀ b ∈ bondCube r, |kernelResidual Q v b| ≤ ε)
    (l : List (Fin 4)) :
    ∀ (q : ℕ), q + l.length ≤ r → ∀ b ∈ bondCube q,
      |kernelResidual Q (iteratedContract v l) b| ≤ 2 ^ l.length * ε := by
  induction l with
  | nil =>
    intro q hq b hb
    have : b ∈ bondCube r := by
      refine Finset.mem_product.2 ⟨mem_siteCube_iff_supNorm.2 ?_, Finset.mem_univ _⟩
      have := mem_siteCube_iff_supNorm.1 (Finset.mem_product.1 hb).1
      simp only [List.length_nil] at hq
      omega
    simpa [iteratedContract] using hε b this
  | cons d l ih =>
    intro q hq b hb
    simp only [List.length_cons] at hq
    have hq1 : q + 1 + l.length ≤ r := by omega
    have hbq := mem_siteCube_iff_supNorm.1 (Finset.mem_product.1 hb).1
    have h1 := ih (q + 1) hq1 b
      (Finset.mem_product.2 ⟨mem_siteCube_iff_supNorm.2 (by omega), Finset.mem_univ _⟩)
    have h2 := ih (q + 1) hq1 (b.1 + Pi.single d 1, b.2) (Finset.mem_product.2
      ⟨mem_siteCube_iff_supNorm.2 ((supNorm_add_single_le _ _).trans (by omega)), Finset.mem_univ _⟩)
    show |kernelResidual Q (contract d (intCurl (iteratedContract v l))) b| ≤ _
    rw [kernelResidual_contract hQ (iteratedContract_support hs l)]
    simp only [List.length_cons, pow_succ]
    have := abs_sub (kernelResidual Q (iteratedContract v l) (b.1 + Pi.single d 1, b.2))
      (kernelResidual Q (iteratedContract v l) b)
    linarith
private theorem bondCube_mono {a b : ℕ} (h : a ≤ b) : bondCube a ⊆ bondCube b := by
  intro x hx
  have := mem_siteCube_iff_supNorm.1 (Finset.mem_product.1 hx).1
  exact Finset.mem_product.2 ⟨mem_siteCube_iff_supNorm.2 (by omega), Finset.mem_univ _⟩
private theorem sum_sq_plaquetteCube_nonneg (F : (Fin 4 → ℤ) × Fin 4 × Fin 4 → ℝ) (r : ℕ) :
    0 ≤ ∑ p ∈ plaquetteCube r, F p ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
private def stepError (c C : ℝ) (ρ r M t : ℕ) (W ε : ℝ) : ℝ :=
  ((bondCube r).card : ℝ) * ((4 ^ M * W) * (2 ^ M * ε)) +
    ((bondCube r).card : ℝ) *
      (((bondCube (ρ + M)).card : ℝ) * ((4 ^ M * W) ^ 2 * (C * Real.exp (-(c * t)))))
private theorem chain_inequality {a κ Φ Φ' Φ₀ E A B : ℝ} (h3 : Φ ≤ a * Φ' + E) (IH : Φ' ≤ A * Φ₀ + B * E)
    (ha0 : 0 ≤ a) (ha : a ≤ κ) (hB : 1 ≤ B) (hE : 0 ≤ E) : Φ ≤ A * a * Φ₀ + B * (1 + κ) * E := by
  have h4 := mul_le_mul_of_nonneg_left IH ha0
  have h5 : a * (B * E) ≤ κ * (B * E) := mul_le_mul_of_nonneg_right ha (by positivity)
  have h7 : E ≤ B * E := le_mul_of_one_le_left hE hB
  nlinarith
set_option maxHeartbeats 800000 in
private theorem caccioppoli_iterate {cK c C K : ℝ} {Q : IntBond → IntBond → ℝ}
    (hQ : IsGradientBlindKernel cK c C Q)
    (hcK : 0 < cK) (hc : 0 < c) (hC : 0 ≤ C) (hK0 : 0 ≤ K)
    (hK : ∀ (H : Finset IntBond) (b : IntBond),
      ∑ b' ∈ H, (bondSupDist b b' : ℝ) ^ 2 * (C * Real.exp (-(c * bondSupDist b b'))) ≤ K)
    {v : IntBond → ℝ} {ρ r t M : ℕ} {W ε : ℝ} (ht : 1 ≤ t) (hW0 : 0 ≤ W) (hε0 : 0 ≤ ε)
    (hs : ∀ b, b ∉ bondCube ρ → v b = 0) (hW : ∀ b, |v b| ≤ W)
    (hε : ∀ b ∈ bondCube r, |kernelResidual Q v b| ≤ ε) (l : List (Fin 4)) (hM : l.length ≤ M) :
    ∀ q : ℕ, q + l.length * (2 * t + 2) ≤ r →
      ∑ p ∈ plaquetteCube q, intCurl (iteratedContract v l) p ^ 2 ≤
        (K / (2 * cK) / (t : ℝ) ^ 2) ^ l.length * ∑ p ∈ plaquetteCube r, intCurl v p ^ 2 +
        (1 + K / (2 * cK)) ^ l.length * (stepError c C ρ r M t W ε / (2 * cK)) := by
  have ht1 : (1 : ℝ) ≤ (t : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast ht)
  set κ := K / (2 * cK) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hE0 : 0 ≤ stepError c C ρ r M t W ε / (2 * cK) := by
    unfold stepError
    positivity
  induction l with
  | nil =>
    intro q hq
    simp only [List.length_nil, zero_mul, add_zero] at hq
    simp only [iteratedContract, List.length_nil, pow_zero, one_mul]
    have : ∑ p ∈ plaquetteCube q, intCurl v p ^ 2 ≤ ∑ p ∈ plaquetteCube r, intCurl v p ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
      intro p hp
      have := mem_siteCube_iff_supNorm.1 (Finset.mem_product.1 hp).1
      exact Finset.mem_product.2 ⟨mem_siteCube_iff_supNorm.2 (by omega), (Finset.mem_product.1 hp).2⟩
    linarith
  | cons d l ih =>
    intro q hq
    simp only [List.length_cons] at hq hM
    have hM' : l.length ≤ M := by omega
    have hq' : q + 1 + 2 * t + l.length * (2 * t + 2) ≤ r := by
      have : (l.length + 1) * (2 * t + 2) = l.length * (2 * t + 2) + (2 * t + 2) := by ring
      omega
    have IH := ih hM' (q + 1 + 2 * t) hq'
    set w := iteratedContract v (d :: l) with hw
    have hwS : ∀ b, b ∉ bondCube (ρ + M) → w b = 0 := fun b hb =>
      iteratedContract_support hs (d :: l) b fun h =>
        hb (bondCube_mono (by simp only [List.length_cons]; omega) h)
    have hWm : ∀ b, |w b| ≤ 4 ^ M * W := fun b => (abs_iteratedContract_le hW (d :: l) b).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (by simp only [List.length_cons]; omega)) hW0)
    have hmul : l.length + 1 ≤ (l.length + 1) * (2 * t + 2) := Nat.le_mul_of_pos_right _ (by omega)
    have hmul2 : (l.length + 1) * (2 * t + 2) = l.length * (2 * t + 2) + (2 * t + 2) := by ring
    have hmul3 : l.length ≤ l.length * (2 * t + 2) := Nat.le_mul_of_pos_right _ (by omega)
    have hrs : ∀ b ∈ bondCube (q + 1 + t), |kernelResidual Q w b| ≤ 2 ^ M * ε := fun b hb =>
      (abs_kernelResidual_iteratedContract_le hQ hs hε (d :: l) (q + 1 + t)
        (by simp only [List.length_cons]; omega) b hb).trans
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) (by simp only [List.length_cons]; omega)) hε0)
    have hstep := caccioppoli hQ hc hK0 hK ht (by positivity) hwS hWm hrs
    have hsq : ∑ b ∈ bondCube (q + 1 + 2 * t), w b ^ 2 ≤
        ∑ p ∈ plaquetteCube (q + 1 + 2 * t), intCurl (iteratedContract v l) p ^ 2 :=
      sum_sq_contract_le_curl (iteratedContract v l) d _
    have hN : ((bondCube (q + 1 + t)).card : ℝ) ≤ (bondCube r).card := by
      exact_mod_cast Finset.card_le_card (bondCube_mono (by omega))
    have herr : ((bondCube (q + 1 + t)).card : ℝ) * ((4 ^ M * W) * (2 ^ M * ε)) +
        ((bondCube (q + 1 + t)).card : ℝ) *
          (((bondCube (ρ + M)).card : ℝ) * ((4 ^ M * W) ^ 2 * (C * Real.exp (-(c * t))))) ≤
        stepError c C ρ r M t W ε := by
      unfold stepError
      gcongr
    set Φ := ∑ p ∈ plaquetteCube q, intCurl w p ^ 2 with hΦ
    set Φ' := ∑ p ∈ plaquetteCube (q + 1 + 2 * t), intCurl (iteratedContract v l) p ^ 2 with hΦ'
    set Φ₀ := ∑ p ∈ plaquetteCube r, intCurl v p ^ 2 with hΦ₀
    set E := stepError c C ρ r M t W ε / (2 * cK) with hE
    have h2 : 2 * cK * Φ ≤ K / (t : ℝ) ^ 2 * Φ' + stepError c C ρ r M t W ε := by
      have : K / (t : ℝ) ^ 2 * ∑ b ∈ bondCube (q + 1 + 2 * t), w b ^ 2 ≤ K / (t : ℝ) ^ 2 * Φ' :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      linarith
    have h3 : Φ ≤ κ / (t : ℝ) ^ 2 * Φ' + E := by
      have hc2 : (0 : ℝ) < 2 * cK := by positivity
      have e : κ / (t : ℝ) ^ 2 * Φ' + E =
          (K / (t : ℝ) ^ 2 * Φ' + stepError c C ρ r M t W ε) / (2 * cK) := by
        simp only [hκ, hE]
        field_simp
      rw [e, le_div_iff₀ hc2]
      linarith
    have hκt : 0 ≤ κ / (t : ℝ) ^ 2 := by positivity
    have hκt1 : κ / (t : ℝ) ^ 2 ≤ κ := div_le_self hκ0 ht1
    have h6 : (1 : ℝ) ≤ (1 + κ) ^ l.length := one_le_pow₀ (by linarith)
    have hfin := chain_inequality h3 IH hκt hκt1 h6 hE0
    have e1 : (κ / (t : ℝ) ^ 2) ^ (l.length + 1) =
        (κ / (t : ℝ) ^ 2) ^ l.length * (κ / (t : ℝ) ^ 2) := pow_succ _ _
    have e2 : (1 + κ) ^ (l.length + 1) = (1 + κ) ^ l.length * (1 + κ) := pow_succ _ _
    rw [List.length_cons, e1, e2]
    exact hfin
private theorem siteForwardDiffs_eq (F : (Fin 4 → ℤ) × Fin 4 × Fin 4 → ℝ) (i k : Fin 4) (S : List (Fin 4)) :
    ∀ x, siteForwardDiffs S (fun x => F (x, i, k)) x = plaquetteForwardDiffs S F (x, i, k) := by
  induction S with
  | nil => intro x; rfl
  | cons d S ih =>
    intro x
    show siteForwardDiff d (siteForwardDiffs S fun x => F (x, i, k)) x =
      plaquetteForwardDiff d (plaquetteForwardDiffs S F) (x, i, k)
    simp only [siteForwardDiff, plaquetteForwardDiff, ih]
private theorem plaquetteForwardDiffs_append (S l : List (Fin 4)) (F : (Fin 4 → ℤ) × Fin 4 × Fin 4 → ℝ) :
    plaquetteForwardDiffs S (plaquetteForwardDiffs l F) = plaquetteForwardDiffs (S ++ l) F := by
  simp [plaquetteForwardDiffs, List.foldr_append]
private theorem sum_sq_plane_le (F : (Fin 4 → ℤ) × Fin 4 × Fin 4 → ℝ) {i k : Fin 4} (hik : i < k) (r : ℕ) :
    ∑ x ∈ siteCube r, F (x, i, k) ^ 2 ≤ ∑ p ∈ plaquetteCube r, F p ^ 2 := by
  simp only [plaquetteCube, Finset.sum_product]
  refine Finset.sum_le_sum fun x _ => ?_
  exact Finset.single_le_sum (f := fun q : Fin 4 × Fin 4 => F (x, q.1, q.2) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_filter.2 ⟨Finset.mem_univ (i, k), hik⟩)
private theorem sqrt_le_of_le {Φ Φ₀ E κ a : ℝ} (hκ : 1 ≤ κ) (ha : 0 ≤ a) (hΦ₀ : 0 ≤ Φ₀) (hE : 0 ≤ E)
    (h : Φ ≤ κ * (a ^ 2 * Φ₀) + κ * E) :
    Real.sqrt Φ ≤ κ * (a * Real.sqrt Φ₀ + Real.sqrt E) := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have e0 := Real.sq_sqrt hΦ₀
  have e1 := Real.sq_sqrt hE
  have e2 : (κ * (a * Real.sqrt Φ₀ + Real.sqrt E)) ^ 2 =
      κ ^ 2 * (a ^ 2 * Φ₀ + E + 2 * a * Real.sqrt Φ₀ * Real.sqrt E) := by
    rw [mul_pow, add_sq, mul_pow, e0, e1]
    ring
  rw [e2]
  have h3 : κ ≤ κ ^ 2 := by nlinarith
  have h4 : 0 ≤ a ^ 2 * Φ₀ + E := by positivity
  have h5 : 0 ≤ 2 * a * Real.sqrt Φ₀ * Real.sqrt E := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h3 h4, mul_nonneg (sq_nonneg κ) h5]
private theorem stepError_eq (c C : ℝ) (ρ r M t : ℕ) (W ε : ℝ) :
    stepError c C ρ r M t W ε = energyStepError c C ρ r M t W ε := by
  simp only [stepError, energyStepError, card_bondCube, bondCubeCard]
theorem curlDiffBound : curlDiffBoundStatement := by
  intro cK c C hcK hc hC j
  obtain ⟨K, hK0, hK⟩ := schur_bound c C hc hC
  set κ₁ : ℝ := 1 + K / (2 * cK) with hκ₁
  have hκ₁1 : 1 ≤ κ₁ := by
    have : 0 ≤ K / (2 * cK) := by positivity
    linarith
  have hκM : 1 ≤ κ₁ ^ (j + 4) := one_le_pow₀ hκ₁1
  refine ⟨16 * κ₁ ^ (j + 4), by positivity, ?_⟩
  intro Q hQ v ρ r t q W ε ht hq hW0 hε0 hs hW hε l hl y hy i k hik
  rw [← stepError_eq]
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  set Φ₀ := ∑ p ∈ plaquetteCube r, intCurl v p ^ 2 with hΦ₀
  have hΦ₀0 : 0 ≤ Φ₀ := sum_sq_plaquetteCube_nonneg _ _
  set E := stepError c C ρ r (j + 4) t W ε / (2 * cK) with hE
  have hE0 : 0 ≤ E := by
    simp only [hE]
    unfold stepError
    positivity
  set g : (Fin 4 → ℤ) → ℝ := fun x => plaquetteForwardDiffs l (intCurl v) (x, i, k) with hg
  set X := κ₁ ^ (j + 4) * (((t : ℝ) ^ (j + 2))⁻¹ * Real.sqrt Φ₀ + (t : ℝ) ^ 2 * Real.sqrt E) with hX
  have key : |g y| ≤ 16 * X := by
    refine abs_le_of_forwardDiff_norms ht g hy fun S hS => ?_
    set m := S.length + j with hm
    have hsl : (S ++ l).length = m := by simp [hm, hl]
    have hmM : m ≤ j + 4 := by omega
    have hch := caccioppoli_iterate (M := j + 4) hQ hcK hc hC hK0 hK ht hW0 hε0 hs hW hε (S ++ l)
      (by rw [hsl]; exact hmM) (q + t)
      (by
        rw [hsl]
        have : m * (2 * t + 2) ≤ (j + 4) * (2 * t + 2) := Nat.mul_le_mul_right _ hmM
        omega)
    rw [hsl, intCurl_iteratedContract, ← plaquetteForwardDiffs_append] at hch
    have hsum : ∑ x ∈ siteCube (q + t), siteForwardDiffs S g x ^ 2 ≤
        ∑ p ∈ plaquetteCube (q + t), plaquetteForwardDiffs S (plaquetteForwardDiffs l (intCurl v)) p ^ 2 := by
      simp only [hg, siteForwardDiffs_eq]
      exact sum_sq_plane_le _ hik _
    set a : ℝ := ((t : ℝ) ^ m)⁻¹ with ha
    have ha0 : 0 ≤ a := by positivity
    have hpow : (K / (2 * cK) / (t : ℝ) ^ 2) ^ m ≤ κ₁ ^ (j + 4) * a ^ 2 := by
      have e : (K / (2 * cK) / (t : ℝ) ^ 2) ^ m = (K / (2 * cK)) ^ m * a ^ 2 := by
        simp only [ha, div_pow, inv_pow]
        rw [div_eq_mul_inv, ← pow_mul, ← pow_mul, mul_comm 2 m]
      rw [e]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc (K / (2 * cK)) ^ m ≤ κ₁ ^ m := pow_le_pow_left₀ (by positivity) (by simp only [hκ₁]; linarith) _
        _ ≤ κ₁ ^ (j + 4) := pow_le_pow_right₀ hκ₁1 hmM
    have hpow2 : (1 + K / (2 * cK)) ^ m ≤ κ₁ ^ (j + 4) := pow_le_pow_right₀ hκ₁1 hmM
    have hΦ : ∑ x ∈ siteCube (q + t), siteForwardDiffs S g x ^ 2 ≤
        κ₁ ^ (j + 4) * (a ^ 2 * Φ₀) + κ₁ ^ (j + 4) * E := by
      refine hsum.trans (hch.trans ?_)
      have e1 := mul_le_mul_of_nonneg_right hpow hΦ₀0
      have e2 := mul_le_mul_of_nonneg_right hpow2 hE0
      nlinarith
    have hroot := sqrt_le_of_le hκM ha0 hΦ₀0 hE0 hΦ
    have hts : (t : ℝ) ^ S.length * a = ((t : ℝ) ^ j)⁻¹ := by
      simp only [ha, hm, pow_add]
      field_simp
    have hts2 : (t : ℝ) ^ S.length ≤ (t : ℝ) ^ 4 := pow_le_pow_right₀ ht1 hS
    calc (t : ℝ) ^ S.length * Real.sqrt (∑ x ∈ siteCube (q + t), siteForwardDiffs S g x ^ 2)
        ≤ (t : ℝ) ^ S.length * (κ₁ ^ (j + 4) * (a * Real.sqrt Φ₀ + Real.sqrt E)) :=
          mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = κ₁ ^ (j + 4) * (((t : ℝ) ^ S.length * a) * Real.sqrt Φ₀ +
            (t : ℝ) ^ S.length * Real.sqrt E) := by ring
      _ ≤ κ₁ ^ (j + 4) * (((t : ℝ) ^ j)⁻¹ * Real.sqrt Φ₀ + (t : ℝ) ^ 4 * Real.sqrt E) := by
          rw [hts]
          gcongr
      _ = (t : ℝ) ^ 2 * X := by
          simp only [hX, pow_add]
          field_simp
  calc |plaquetteForwardDiffs l (intCurl v) (y, i, k)| = |g y| := rfl
    _ ≤ 16 * X := key
    _ = _ := by simp only [hX]; ring
end YangMills.Construction.LimitForms
end
