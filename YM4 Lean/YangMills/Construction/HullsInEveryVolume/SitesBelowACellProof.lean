import YangMills.Construction.HullsInEveryVolume.NoisesOfTheChain
import Mathlib
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.ChainNoise
open TorusFields WeightedResponses ChessboardGrids
def sitesUnderCellStatement : Prop :=
  ∀ (L u n : ℕ) [NeZero L] [NeZero n] (gr : MirrorGrid) (c : Fin 4 → ℕ), Odd L →
    (∀ Q : Finset (TorusSite n), Q ⊆ gr.cellSites n c →
      sitesUnder L u n Q ⊆ (gr.atDepth L u).cellSites (fineSide L u n) c) ∧
    ∀ z : Fin 4 → ℤ, (siteOfInt (fun i => (L : ℤ) ^ u * z i) : TorusSite (fineSide L u n)) ∈ sitesUnder L u n {siteOfInt z}
end YangMills.Construction.ChainNoise
end

noncomputable section
namespace YangMills.Construction.ChainNoise
open TorusFields TorusLumps ChessboardGrids WeightedResponses
private theorem zmod_val_intCast_toNat (m : ℕ) [NeZero m] (a : ℤ) : ((a : ZMod m)).val = (a % (m : ℤ)).toNat := by
  have h := ZMod.val_intCast (n := m) a
  rw [← h]
  exact (Int.toNat_natCast _).symm
private theorem cellIndex_below {L n : ℕ} (l : ℕ) (hL : Odd L) (hn : 0 < n) (X o : ℤ) :
    ((X - ((L : ℤ) * o + ((L : ℤ) - 1) / 2 + 1)) % ((n * L : ℕ) : ℤ)).toNat / (l * L) =
      ((((X + ((L : ℤ) - 1) / 2) / (L : ℤ)) - (o + 1)) % (n : ℤ)).toNat / l := by
  obtain ⟨t, ht⟩ := hL
  have hLpos : 0 < L := by omega
  have hLz : (0 : ℤ) < L := by exact_mod_cast hLpos
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  have ht2 : ((L : ℤ) - 1) / 2 = t := by rw [ht]; push_cast; omega
  rw [ht2]
  set Y := (X + t) / (L : ℤ) with hY
  set e := (X + t) % (L : ℤ) with he
  have he0 : 0 ≤ e := Int.emod_nonneg _ hLz.ne'
  have he1 : e < L := Int.emod_lt_of_pos _ hLz
  have hXY : X + t = (L : ℤ) * Y + e := (Int.mul_ediv_add_emod _ _).symm
  set B := Y - (o + 1) with hB
  set b := B % (n : ℤ) with hb
  have hb0 : 0 ≤ b := Int.emod_nonneg _ hnz.ne'
  have hb1 : b < n := Int.emod_lt_of_pos _ hnz
  have hBb : B = b + (n : ℤ) * (B / (n : ℤ)) := (Int.emod_add_mul_ediv _ _).symm
  have hA : X - ((L : ℤ) * o + t + 1) = ((L : ℤ) * b + e) + ((n * L : ℕ) : ℤ) * (B / (n : ℤ)) := by
    have h1 : (L : ℤ) = 2 * t + 1 := by rw [ht]; push_cast; ring
    push_cast
    have h2 : X = (L : ℤ) * (B + (o + 1)) + e - t := by rw [hB]; linarith
    calc X - ((L : ℤ) * o + t + 1) = (L : ℤ) * B + e + ((L : ℤ) - 2 * t - 1) := by rw [h2]; ring
      _ = (L : ℤ) * B + e := by rw [h1]; ring
      _ = (L : ℤ) * (b + (n : ℤ) * (B / (n : ℤ))) + e := by rw [← hBb]
      _ = _ := by ring
  have hm : (X - ((L : ℤ) * o + t + 1)) % ((n * L : ℕ) : ℤ) = (L : ℤ) * b + e := by
    rw [hA, Int.add_mul_emod_self_left]
    refine Int.emod_eq_of_lt (by positivity) ?_
    push_cast
    nlinarith
  rw [hm]
  obtain ⟨bn, hbn⟩ := Int.eq_ofNat_of_zero_le hb0
  obtain ⟨en, hen⟩ := Int.eq_ofNat_of_zero_le he0
  have hen1 : en < L := by
    have : (en : ℤ) < L := by rw [← hen]; exact he1
    exact_mod_cast this
  rw [hbn, hen]
  have h3 : ((L : ℤ) * (bn : ℤ) + (en : ℤ)).toNat = L * bn + en := by
    exact_mod_cast Int.toNat_natCast (L * bn + en)
  rw [h3, Int.toNat_natCast, mul_comm l L, ← Nat.div_div_eq_div_mul]
  congr 1
  rw [Nat.mul_add_div hLpos, Nat.div_eq_of_lt hen1, add_zero]
private theorem atDepth_one_atDepth {L : ℕ} (hL : Odd L) (gr : MirrorGrid) (u : ℕ) :
    (gr.atDepth L 1).atDepth L u = gr.atDepth L (u + 1) := by
  obtain ⟨t, ht⟩ := hL
  obtain ⟨s, hs⟩ : Odd ((L : ℤ) ^ u) := Odd.pow (by rw [ht]; exact ⟨t, by push_cast; ring⟩)
  have h1 : ((L : ℤ) - 1) / 2 = t := by rw [ht]; push_cast; omega
  have h2 : ((L : ℤ) ^ u - 1) / 2 = s := by rw [hs]; omega
  have h3 : (L : ℤ) = 2 * t + 1 := by rw [ht]; push_cast; ring
  have h4 : ((L : ℤ) ^ (u + 1) - 1) / 2 = (L : ℤ) ^ u * t + s := by
    rw [pow_succ, hs, h3]
    have : (2 * s + 1) * (2 * (t : ℤ) + 1) - 1 = 2 * ((2 * s + 1) * t + s) := by ring
    rw [this]
    simp
  simp only [MirrorGrid.atDepth, pow_one, h1]
  congr 1
  · ring
  · funext i
    rw [h2, h4, pow_succ]
    ring
abbrev _root_.YangMills.SharedProofs.p49727 := @atDepth_one_atDepth
private theorem sitesInBlocks_cellSites {L n : ℕ} [NeZero L] [NeZero n] (hL : Odd L) (gr : MirrorGrid) (c : Fin 4 → ℕ) :
    sitesInBlocks L (gr.cellSites n c) ⊆ (gr.atDepth L 1).cellSites (n * L) c := by
  classical
  intro x hx
  have hx1 : parentBlock L x ∈ gr.cellSites n c := (Finset.mem_filter.mp hx).2
  have hx2 : gr.cellIndex (parentBlock L x) = c := (Finset.mem_filter.mp hx1).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  funext i
  have h1 : ((parentBlock L x i - ((gr.offset i + 1 : ℤ) : ZMod n)).val / gr.side) = c i := congrFun hx2 i
  rw [← h1]
  show (x i - (((gr.atDepth L 1).offset i + 1 : ℤ) : ZMod (n * L))).val / (gr.side * L ^ 1) = _
  set X : ℤ := (x i).cast with hX
  have hxi : x i = ((X : ℤ) : ZMod (n * L)) := by rw [hX, ZMod.intCast_zmod_cast]
  have e1 : x i - (((gr.atDepth L 1).offset i + 1 : ℤ) : ZMod (n * L)) =
      ((X - ((L : ℤ) * gr.offset i + ((L : ℤ) - 1) / 2 + 1) : ℤ) : ZMod (n * L)) := by
    rw [hxi]
    simp only [MirrorGrid.atDepth, pow_one]
    push_cast
    ring
  have e2 : parentBlock L x i - ((gr.offset i + 1 : ℤ) : ZMod n) =
      ((((X + ((L : ℤ) - 1) / 2) / (L : ℤ)) - (gr.offset i + 1) : ℤ) : ZMod n) := by
    simp only [parentBlock]
    push_cast
    rfl
  rw [e1, e2, zmod_val_intCast_toNat, zmod_val_intCast_toNat, pow_one]
  exact cellIndex_below gr.side hL (Nat.pos_of_ne_zero (NeZero.ne n)) X (gr.offset i)
private theorem sitesUnder_mono {L : ℕ} [NeZero L] (u : ℕ) : ∀ (n : ℕ) [NeZero n] {Q Q' : Finset (TorusSite n)}, Q ⊆ Q' →
    sitesUnder L u n Q ⊆ sitesUnder L u n Q' := by
  induction u with
  | zero => intro n _ Q Q' h; exact h
  | succ u ih =>
    intro n _ Q Q' h
    refine ih (n * L) ?_
    intro x hx
    classical
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h (Finset.mem_filter.mp hx).2⟩
abbrev _root_.YangMills.SharedProofs.p53753 := @sitesUnder_mono
private theorem parentBlock_siteOfInt_mul {L n : ℕ} [NeZero L] [NeZero n] (hL : Odd L) (z : Fin 4 → ℤ) :
    parentBlock L (siteOfInt (fun i => (L : ℤ) * z i) : TorusSite (n * L)) = siteOfInt z := by
  obtain ⟨t, ht⟩ := hL
  have hLz : (0 : ℤ) < L := by
    have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact_mod_cast this
  have ht2 : ((L : ℤ) - 1) / 2 = t := by rw [ht]; push_cast; omega
  have h3 : (L : ℤ) = 2 * t + 1 := by rw [ht]; push_cast; ring
  funext i
  simp only [parentBlock, siteOfInt]
  set q := ((L : ℤ) * z i) / ((n * L : ℕ) : ℤ) with hq
  have h1 : ((((L : ℤ) * z i : ℤ) : ZMod (n * L)).cast : ℤ) = (L : ℤ) * (z i - (n : ℤ) * q) := by
    have h2 := ZMod.val_intCast (n := n * L) ((L : ℤ) * z i)
    have h4 := Int.emod_add_mul_ediv ((L : ℤ) * z i) ((n * L : ℕ) : ℤ)
    rw [← hq] at h4
    have h7 : ((n * L : ℕ) : ℤ) = (n : ℤ) * L := by push_cast; ring
    have h5 : ((((L : ℤ) * z i : ℤ) : ZMod (n * L)).cast : ℤ) = ((((L : ℤ) * z i : ℤ) : ZMod (n * L)).val : ℤ) :=
      (ZMod.natCast_val _).symm
    rw [h5, h2]
    linear_combination h4 - q * h7
  rw [h1, ht2]
  have h6 : ((L : ℤ) * (z i - (n : ℤ) * q) + t) / (L : ℤ) = z i - (n : ℤ) * q := by
    rw [add_comm, Int.add_mul_ediv_left _ _ hLz.ne', Int.ediv_eq_zero_of_lt (by omega) (by omega), zero_add]
  rw [h6]
  push_cast
  simp
theorem sitesUnderCell_holds : sitesUnderCellStatement := by
  intro L u
  induction u with
  | zero =>
    intro n _ _ gr c _
    refine ⟨fun Q hQ => ?_, fun z => ?_⟩
    · have h : gr.atDepth L 0 = gr := by
        cases gr
        simp [MirrorGrid.atDepth]
      rw [h]
      exact hQ
    · simp only [sitesUnder, pow_zero, one_mul]
      exact Finset.mem_singleton_self _
  | succ u ih =>
    intro n _ _ gr c hL
    refine ⟨fun Q hQ => ?_, fun z => ?_⟩
    · have h1 := (ih (n * L) (gr.atDepth L 1) c hL).1 _ subset_rfl
      rw [atDepth_one_atDepth hL] at h1
      have h2 : sitesInBlocks L Q ⊆ sitesInBlocks L (gr.cellSites n c) := by
        intro x hx
        classical
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ (Finset.mem_filter.mp hx).2⟩
      exact (sitesUnder_mono u (n * L) (h2.trans (sitesInBlocks_cellSites hL gr c))).trans h1
    · have h1 := (ih (n * L) gr c hL).2 (fun i => (L : ℤ) * z i)
      have h2 : (fun i => (L : ℤ) ^ u * ((L : ℤ) * z i)) = fun i => (L : ℤ) ^ (u + 1) * z i := by
        funext i
        rw [pow_succ]
        ring
      rw [h2] at h1
      refine sitesUnder_mono u (n * L) ?_ h1
      intro x hx
      classical
      rw [Finset.mem_singleton] at hx
      subst hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [parentBlock_siteOfInt_mul hL]; exact Finset.mem_singleton_self _⟩
end YangMills.Construction.ChainNoise
end
