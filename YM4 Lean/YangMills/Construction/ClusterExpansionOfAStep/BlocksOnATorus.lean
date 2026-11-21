import YangMills.Construction.ClusterExpansionOfAStep.OffsetsAboveABox
import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusBlocks
open TorusFields TorusLumps
variable {n : ℕ} [NeZero n]
def blockCentreSite (L : ℕ) (Y : TorusSite n) : TorusSite (n * L) :=
  siteOfInt fun k => (L : ℤ) * ((Y k).cast : ℤ)
section Arithmetic
variable {L : ℕ} [NeZero L]
theorem cast_intCast_eq_sub_mul_ediv (z : ℤ) :
    ((((z : ZMod (n * L))).cast : ℤ)) = z - ((n * L : ℕ) : ℤ) * (z / ((n * L : ℕ) : ℤ)) := by
  have h := ZMod.coe_intCast (n := n * L) z
  haveI : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have h2 : ((((z : ZMod (n * L))).cast : ℤ)) = z % ((n * L : ℕ) : ℤ) := h
  rw [h2, Int.emod_def]
theorem parentBlock_siteOfInt (z : Fin 4 → ℤ) (k : Fin 4) :
    parentBlock L (siteOfInt z : TorusSite (n * L)) k = (((z k + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ) : ZMod n) := by
  have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  show (((((((z k : ℤ) : ZMod (n * L))).cast : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ) : ZMod n) = _
  rw [cast_intCast_eq_sub_mul_ediv]
  set q := z k / ((n * L : ℕ) : ℤ)
  have h : z k - ((n * L : ℕ) : ℤ) * q + ((L : ℤ) - 1) / 2 = (z k + ((L : ℤ) - 1) / 2) + (L : ℤ) * (-(n : ℤ) * q) := by
    push_cast
    ring
  rw [h, Int.add_mul_ediv_left _ _ (ne_of_gt hLpos)]
  push_cast
  simp
theorem blockCentreSite_apply_add (Y : TorusSite n) (k : Fin 4) (e : ℤ) :
    (((L : ℤ) * ((Y k).cast : ℤ) + e : ℤ) : ZMod (n * L)) = (blockCentreSite L Y k) + (e : ZMod (n * L)) := by
  simp [blockCentreSite, siteOfInt]
theorem parentBlock_blockCentreSite_add (Y : TorusSite n) (e : Fin 4 → ℤ) :
    parentBlock L (blockCentreSite L Y + siteOfInt e) = Y + siteOfInt fun i => (e i + ((L : ℤ) - 1) / 2) / (L : ℤ) := by apply _root_.YangMills.Construction.CongruentBoxes.parentBlock_blockCentre_add <;> assumption
theorem parentBlock_blockCentreSite (hL : Odd L) (Y : TorusSite n) : parentBlock L (blockCentreSite L Y) = Y := by
  have h := parentBlock_blockCentreSite_add (L := L) Y 0
  have h0 : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite (n * L)) = 0 := by
    funext k
    simp [siteOfInt]
  have h1 : (siteOfInt fun i => ((0 : Fin 4 → ℤ) i + ((L : ℤ) - 1) / 2) / (L : ℤ) : TorusSite n) = 0 := by
    funext k
    have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have : (((L : ℤ) - 1) / 2) / (L : ℤ) = 0 := by
      apply Int.ediv_eq_zero_of_lt <;> omega
    simp [siteOfInt, this]
  rwa [h0, add_zero, h1, add_zero] at h
theorem exists_eq_blockCentreSite_add (hL : Odd L) (x : TorusSite (n * L)) :
    ∃ o : Fin 4 → ℤ, (∀ i, 0 ≤ o i + ((L : ℤ) - 1) / 2 ∧ o i + ((L : ℤ) - 1) / 2 < L) ∧
      x = blockCentreSite L (parentBlock L x) + siteOfInt o := by
  have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  haveI : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  set c : ℤ := ((L : ℤ) - 1) / 2 with hc
  refine ⟨fun i => ((x i).cast : ℤ) + c - (L : ℤ) * ((((x i).cast : ℤ) + c) / (L : ℤ)) - c, fun i => ?_, ?_⟩
  · have h1 := Int.emod_nonneg (((x i).cast : ℤ) + c) (ne_of_gt hLpos)
    have h2 := Int.emod_lt_of_pos (((x i).cast : ℤ) + c) hLpos
    have h3 := Int.emod_def (((x i).cast : ℤ) + c) (L : ℤ)
    constructor <;> simp only <;> omega
  · funext k
    show x k = blockCentreSite L (parentBlock L x) k +
      ((((x k).cast : ℤ) + c - (L : ℤ) * ((((x k).cast : ℤ) + c) / (L : ℤ)) - c : ℤ) : ZMod (n * L))
    have hb : parentBlock L x k = (((((x k).cast : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ) : ZMod n) := rfl
    rw [← hc] at hb
    generalize (((x k).cast : ℤ) + c) / (L : ℤ) = A at hb ⊢
    have h1 : (((parentBlock L x k).cast : ℤ)) = A - (n : ℤ) * (A / (n : ℤ)) := by
      rw [hb]
      have h3 : ((((A : ZMod n)).cast : ℤ)) = A % (n : ℤ) := ZMod.coe_intCast (n := n) A
      rw [h3, Int.emod_def]
    have hcentre : blockCentreSite L (parentBlock L x) k = (((L : ℤ) * (A - (n : ℤ) * (A / (n : ℤ))) : ℤ) : ZMod (n * L)) := by
      simp only [blockCentreSite, siteOfInt]
      rw [h1]
    rw [hcentre, ← Int.cast_add]
    have hint : (L : ℤ) * (A - (n : ℤ) * (A / (n : ℤ))) + (((x k).cast : ℤ) + c - (L : ℤ) * A - c) =
        ((x k).cast : ℤ) - ((n * L : ℕ) : ℤ) * (A / (n : ℤ)) := by
      push_cast
      ring
    rw [hint]
    have hz' : (n : ZMod (n * L)) * (L : ZMod (n * L)) = 0 := by
      have : ((n * L : ℕ) : ZMod (n * L)) = 0 := ZMod.natCast_self _
      exact_mod_cast this
    push_cast
    rw [hz', zero_mul, sub_zero]
theorem supDist_parentBlock_le (hL : Odd L) (x x' : TorusSite (n * L)) :
    supDist (parentBlock L x) (parentBlock L x') ≤ supDist x x' + 1 := by
  have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  haveI : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  obtain ⟨o, ho, hx⟩ := exists_eq_blockCentreSite_add hL x
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist x x'
  set B := parentBlock L x with hB
  have hx' : x' = blockCentreSite L B + siteOfInt (o + e) := by
    rw [he, siteOfInt_add, ← add_assoc, ← hx]
  have hbB : parentBlock L x' = B + siteOfInt fun i => ((o + e) i + ((L : ℤ) - 1) / 2) / (L : ℤ) := by
    rw [hx', parentBlock_blockCentreSite_add]
  rw [hbB]
  refine supDist_add_siteOfInt_le B _ _ fun i => ?_
  have h1 := hb i
  have h2 := ho i
  set c : ℤ := ((L : ℤ) - 1) / 2
  set u := o i + c with hu
  have hval : ((o + e) i + c) = u + e i := by
    simp only [Pi.add_apply, hu]
    ring
  rw [hval]
  have hNL : ((e i).natAbs : ℤ) ≤ ((e i).natAbs : ℤ) * (L : ℤ) := by nlinarith
  have hlow : -((e i).natAbs : ℤ) - 1 ≤ (u + e i) / (L : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hLpos]
    have h4 : -((e i).natAbs : ℤ) ≤ e i := by omega
    nlinarith [h2.1, h2.2]
  have hupp : (u + e i) / (L : ℤ) ≤ ((e i).natAbs : ℤ) + 1 := by
    have : (u + e i) / (L : ℤ) < ((e i).natAbs : ℤ) + 2 := by
      rw [Int.ediv_lt_iff_lt_mul hLpos]
      have h4 : e i ≤ ((e i).natAbs : ℤ) := by omega
      nlinarith [h2.1, h2.2]
    omega
  omega
theorem mul_supDist_parentBlock_le (hL : Odd L) (x x' : TorusSite (n * L)) :
    L * supDist (parentBlock L x) (parentBlock L x') ≤ supDist x x' + L := by
  have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLn : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  haveI : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  obtain ⟨o, ho, hx⟩ := exists_eq_blockCentreSite_add hL x
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist x x'
  set B := parentBlock L x with hB
  have hx' : x' = blockCentreSite L B + siteOfInt (o + e) := by
    rw [he, siteOfInt_add, ← add_assoc, ← hx]
  have hbB : parentBlock L x' = B + siteOfInt fun i => ((o + e) i + ((L : ℤ) - 1) / 2) / (L : ℤ) := by
    rw [hx', parentBlock_blockCentreSite_add]
  have hm : supDist B (parentBlock L x') ≤ (supDist x x' + L) / L := by
    rw [hbB]
    refine supDist_add_siteOfInt_le B _ _ fun i => ?_
    have h1 := hb i
    have h2 := ho i
    set c : ℤ := ((L : ℤ) - 1) / 2
    set u := o i + c with hu
    have hval : ((o + e) i + c) = u + e i := by
      simp only [Pi.add_apply, hu]
      ring
    rw [hval]
    rw [Nat.le_div_iff_mul_le hLn]
    have hq := Int.emod_add_mul_ediv (u + e i) (L : ℤ)
    have hr0 := Int.emod_nonneg (u + e i) (ne_of_gt hLpos)
    have hr1 := Int.emod_lt_of_pos (u + e i) hLpos
    set q := (u + e i) / (L : ℤ)
    set r0 := (u + e i) % (L : ℤ)
    have h3 : ((q.natAbs * L : ℕ) : ℤ) ≤ ((supDist x x' + L : ℕ) : ℤ) := by
      push_cast
      have h4 : (L : ℤ) * q = u + e i - r0 := by linarith
      have h5 : |q| * (L : ℤ) = |(L : ℤ) * q| := by
        rw [abs_mul, abs_of_pos hLpos]
        ring
      rw [h5, h4, abs_le]
      have h6 : ((e i).natAbs : ℤ) ≤ supDist x x' := by exact_mod_cast h1
      have h7 : -((e i).natAbs : ℤ) ≤ e i := by omega
      have h8 : e i ≤ ((e i).natAbs : ℤ) := by omega
      constructor <;> linarith [h2.1, h2.2]
    exact_mod_cast h3
  calc L * supDist B (parentBlock L x') ≤ L * ((supDist x x' + L) / L) := Nat.mul_le_mul_left _ hm
    _ ≤ supDist x x' + L := Nat.mul_div_le _ _
theorem supDist_le_mul_supDist_parentBlock_add_one (hL : Odd L) (x x' : TorusSite (n * L)) :
    supDist x x' ≤ L * (supDist (parentBlock L x) (parentBlock L x') + 1) := by
  have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  haveI : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  obtain ⟨o, ho, hx⟩ := exists_eq_blockCentreSite_add hL x
  obtain ⟨o', ho', hx'⟩ := exists_eq_blockCentreSite_add hL x'
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist (parentBlock L x) (parentBlock L x')
  have hcentre : blockCentreSite L (parentBlock L x') =
      blockCentreSite L (parentBlock L x) + siteOfInt fun i => (L : ℤ) * e i := by
    funext k
    simp only [blockCentreSite, siteOfInt, Pi.add_apply]
    have h1 : parentBlock L x' k = parentBlock L x k + ((e k : ℤ) : ZMod n) := by
      rw [he]
      rfl
    have h2 : (((parentBlock L x' k).cast : ℤ) : ZMod n) = (((parentBlock L x k).cast + e k : ℤ) : ZMod n) := by
      simp [h1, ZMod.intCast_zmod_cast]
    obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).mp h2
    have hz : ((n : ZMod (n * L)) * (L : ZMod (n * L))) = 0 := by
      have : ((n * L : ℕ) : ZMod (n * L)) = 0 := ZMod.natCast_self _
      exact_mod_cast this
    have h3 : (((parentBlock L x' k).cast : ℤ)) = ((parentBlock L x k).cast + e k : ℤ) - (n : ℤ) * q := by
      linarith
    rw [h3]
    push_cast
    linear_combination (-(q : ZMod (n * L))) * hz
  have hdiff : x' = x + siteOfInt fun i => o' i - o i + (L : ℤ) * e i := by
    conv_lhs => rw [hx', hcentre]
    conv_rhs => rw [hx]
    funext k
    simp only [siteOfInt, Pi.add_apply]
    push_cast
    ring
  rw [hdiff]
  refine supDist_add_siteOfInt_le x _ _ fun i => ?_
  have h1 := hb i
  have h2 := ho i
  have h3 := ho' i
  have hbd : ((L * (supDist (parentBlock L x) (parentBlock L (x + siteOfInt fun i => o' i - o i + (L : ℤ) * e i)) + 1) : ℕ) : ℤ) =
      (L : ℤ) * ((supDist (parentBlock L x) (parentBlock L x') : ℤ) + 1) := by
    rw [← hdiff]
    push_cast
    ring
  have hk : |e i| ≤ (supDist (parentBlock L x) (parentBlock L x') : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1
  have hmain : |o' i - o i + (L : ℤ) * e i| ≤ (L : ℤ) * ((supDist (parentBlock L x) (parentBlock L x') : ℤ) + 1) := by
    have a1 : |o' i - o i| ≤ (L : ℤ) := by
      rw [abs_le]
      constructor <;> omega
    have a2 : |(L : ℤ) * e i| ≤ (L : ℤ) * (supDist (parentBlock L x) (parentBlock L x') : ℤ) := by
      rw [abs_mul, abs_of_pos hLpos]
      exact mul_le_mul_of_nonneg_left hk hLpos.le
    calc _ ≤ |o' i - o i| + |(L : ℤ) * e i| := abs_add_le _ _
      _ ≤ (L : ℤ) + (L : ℤ) * (supDist (parentBlock L x) (parentBlock L x') : ℤ) := add_le_add a1 a2
      _ = _ := by ring
  have hnat : ((o' i - o i + (L : ℤ) * e i).natAbs : ℤ) ≤
      ((L * (supDist (parentBlock L x) (parentBlock L (x + siteOfInt fun i => o' i - o i + (L : ℤ) * e i)) + 1) : ℕ) : ℤ) := by
    rw [hbd, ← Int.abs_eq_natAbs]
    exact hmain
  exact_mod_cast hnat
end Arithmetic
end YangMills.Construction.TorusBlocks
end
