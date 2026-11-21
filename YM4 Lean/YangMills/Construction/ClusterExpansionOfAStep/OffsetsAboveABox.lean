import YangMills.Construction.ClusterExpansionOfAStep.PlacesOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.SetsEqualInBoxes
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.CongruentBoxes
open TorusFields TorusLumps StepSettings BlockPlaces
variable {n n' : ℕ} [NeZero n] [NeZero n'] {L : ℕ} [NeZero L]
def blockCentre (L : ℕ) (y : TorusSite n) : TorusSite (n * L) := siteOfInt fun i => (L : ℤ) * ((y i).cast : ℤ)
def coarseOffset (L : ℕ) (h : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => (h i + ((L : ℤ) - 1) / 2) / (L : ℤ)
def offsetInBlock (L : ℕ) [NeZero L] (h : Fin 4 → ℤ) : BlockOffset L :=
  fun i => Fin.ofNat L (((h i + ((L : ℤ) - 1) / 2) % (L : ℤ)).toNat)
def refinedOffset (L : ℕ) (a : Fin 4 → ℤ) (o : BlockOffset L) : Fin 4 → ℤ :=
  fun i => (L : ℤ) * a i + (((o i : ℕ) : ℤ) - ((L : ℤ) - 1) / 2)
def refinedRadius (L m : ℕ) : ℕ := L * m + (L - 1) / 2
theorem side_pos_int : (0 : ℤ) < (L : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
theorem parentBlock_siteOfInt (c : Fin 4 → ℤ) :
    parentBlock L (siteOfInt c : TorusSite (n * L)) = siteOfInt (fun i => (c i + ((L : ℤ) - 1) / 2) / (L : ℤ)) := by
  funext i
  simp only [parentBlock, siteOfInt]
  have hL : (0 : ℤ) < L := side_pos_int
  have hc : (((c i : ZMod (n * L))).cast : ℤ) = c i % ((n * L : ℕ) : ℤ) := ZMod.coe_intCast _
  rw [hc, Int.emod_def]
  have e : c i - ((n * L : ℕ) : ℤ) * (c i / ((n * L : ℕ) : ℤ)) + ((L : ℤ) - 1) / 2 =
      (c i + ((L : ℤ) - 1) / 2) + (L : ℤ) * (-((n : ℤ) * (c i / ((n * L : ℕ) : ℤ)))) := by
    push_cast
    ring
  rw [e, Int.add_mul_ediv_left _ _ hL.ne']
  push_cast
  simp
theorem siteOffset_siteOfInt (c : Fin 4 → ℤ) :
    siteOffset (siteOfInt c : TorusSite (n * L)) = offsetInBlock L c := by
  funext i
  simp only [siteOffset, offsetInBlock, siteOfInt]
  have hc : (((c i : ZMod (n * L))).cast : ℤ) = c i % ((n * L : ℕ) : ℤ) := ZMod.coe_intCast _
  have e : c i % ((n * L : ℕ) : ℤ) + ((L : ℤ) - 1) / 2 =
      (c i + ((L : ℤ) - 1) / 2) + (L : ℤ) * (-((n : ℤ) * (c i / ((n * L : ℕ) : ℤ)))) := by
    rw [Int.emod_def]
    push_cast
    ring
  rw [hc, e, Int.add_mul_emod_self_left]
theorem blockCentre_add_siteOfInt (y : TorusSite n) (h : Fin 4 → ℤ) :
    blockCentre L y + siteOfInt h = siteOfInt (fun i => (L : ℤ) * ((y i).cast : ℤ) + h i) := by
  funext i
  simp [blockCentre, siteOfInt]
theorem parentBlock_blockCentre_add (y : TorusSite n) (h : Fin 4 → ℤ) :
    parentBlock L (blockCentre L y + siteOfInt h : TorusSite (n * L)) = y + siteOfInt (coarseOffset L h) := by
  rw [blockCentre_add_siteOfInt, parentBlock_siteOfInt]
  funext i
  simp only [siteOfInt, coarseOffset, Pi.add_apply]
  have hL : (0 : ℤ) < L := side_pos_int
  have e : (L : ℤ) * ((y i).cast : ℤ) + h i + ((L : ℤ) - 1) / 2 =
      (h i + ((L : ℤ) - 1) / 2) + (L : ℤ) * ((y i).cast : ℤ) := by ring
  rw [e, Int.add_mul_ediv_left _ _ hL.ne']
  push_cast
  exact add_comm _ _
theorem siteOffset_blockCentre_add (y : TorusSite n) (h : Fin 4 → ℤ) :
    siteOffset (blockCentre L y + siteOfInt h : TorusSite (n * L)) = offsetInBlock L h := by
  rw [blockCentre_add_siteOfInt, siteOffset_siteOfInt]
  funext i
  simp only [offsetInBlock]
  have e : (L : ℤ) * ((y i).cast : ℤ) + h i + ((L : ℤ) - 1) / 2 =
      (h i + ((L : ℤ) - 1) / 2) + (L : ℤ) * ((y i).cast : ℤ) := by ring
  rw [e, Int.add_mul_emod_self_left]
theorem intCast_mul_congr {c c' : ℤ} (h : (c : ZMod n) = c') :
    (((L : ℤ) * c : ℤ) : ZMod (n * L)) = (((L : ℤ) * c' : ℤ) : ZMod (n * L)) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h ⊢
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  push_cast
  linear_combination (L : ℤ) * hk
theorem blockCentre_add (y : TorusSite n) (a : Fin 4 → ℤ) :
    blockCentre L (y + siteOfInt a) = blockCentre L y + siteOfInt (fun i => (L : ℤ) * a i) := by
  rw [blockCentre_add_siteOfInt]
  funext i
  simp only [blockCentre, siteOfInt]
  rw [← mul_add]
  refine intCast_mul_congr ?_
  simp [siteOfInt]
theorem blockSite_eq_blockCentre_add (y : TorusSite n) (o : BlockOffset L) :
    (blockSite y o : TorusSite (n * L)) = blockCentre L y + siteOfInt (refinedOffset L 0 o) := by
  rw [blockCentre_add_siteOfInt]
  funext i
  simp [blockSite, refinedOffset, siteOfInt]
theorem blockSite_add_eq (y : TorusSite n) (a : Fin 4 → ℤ) (o : BlockOffset L) :
    (blockSite (y + siteOfInt a) o : TorusSite (n * L)) = blockCentre L y + siteOfInt (refinedOffset L a o) := by
  rw [blockSite_eq_blockCentre_add, blockCentre_add, add_assoc, ← siteOfInt_add]
  congr 2
  funext i
  simp [refinedOffset]
theorem eq_blockCentre_add_of_parentBlock {y : TorusSite n} {a : Fin 4 → ℤ} {x : TorusSite (n * L)}
    (h : parentBlock L x = y + siteOfInt a) :
    x = blockCentre L y + siteOfInt (refinedOffset L a (siteOffset x)) := by
  rw [← blockSite_add_eq, ← h, blockSite_parentBlock_siteOffset]
theorem coarseOffset_refinedOffset (a : Fin 4 → ℤ) (o : BlockOffset L) :
    coarseOffset L (refinedOffset L a o) = a := by
  funext i
  simp only [coarseOffset, refinedOffset]
  have hL : (0 : ℤ) < L := side_pos_int
  have e : (L : ℤ) * a i + (((o i : ℕ) : ℤ) - ((L : ℤ) - 1) / 2) + ((L : ℤ) - 1) / 2 =
      ((o i : ℕ) : ℤ) + (L : ℤ) * a i := by ring
  rw [e, Int.add_mul_ediv_left _ _ hL.ne', Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast (o i).2)]
  ring
section OddSide
variable (hL : Odd L)
include hL
theorem natCast_half : (((L - 1) / 2 : ℕ) : ℤ) = ((L : ℤ) - 1) / 2 := by
  obtain ⟨s, hs⟩ := hL
  subst hs
  have : 2 * s + 1 - 1 = 2 * s := by omega
  rw [this]
  push_cast
  omega
theorem offsetInBox_refinedRadius_iff {m : ℕ} {h : Fin 4 → ℤ} :
    OffsetInBox (refinedRadius L m) h ↔ OffsetInBox m (coarseOffset L h) := by
  obtain ⟨s, hs⟩ := hL
  have hhalf : ((L : ℤ) - 1) / 2 = s := by omega
  have hfr : ((refinedRadius L m : ℕ) : ℤ) = (L : ℤ) * m + s := by
    unfold refinedRadius
    have : (L - 1) / 2 = s := by omega
    rw [this]
    push_cast
    ring
  have hpos : (0 : ℤ) < L := side_pos_int
  constructor
  · intro hb i
    have h1 := abs_le.mp (hb i)
    rw [hfr] at h1
    simp only [coarseOffset, hhalf]
    rw [abs_le]
    constructor
    · refine (Int.le_ediv_iff_mul_le hpos).mpr ?_
      nlinarith [h1.1]
    · refine Int.lt_add_one_iff.mp ((Int.ediv_lt_iff_lt_mul hpos).mpr ?_)
      nlinarith [h1.2]
  · intro hb i
    have h1 := abs_le.mp (hb i)
    simp only [coarseOffset, hhalf] at h1
    rw [hfr, abs_le]
    have e1 := Int.emod_add_mul_ediv (h i + s) (L : ℤ)
    have e2 := Int.emod_nonneg (h i + s) hpos.ne'
    have e3 := Int.emod_lt_of_pos (h i + s) hpos
    set q := (h i + s) / (L : ℤ) with hq
    have h2 : (L : ℤ) * q ≤ (L : ℤ) * m := mul_le_mul_of_nonneg_left h1.2 hpos.le
    have h3 : (L : ℤ) * (-(m : ℤ)) ≤ (L : ℤ) * q := mul_le_mul_of_nonneg_left h1.1 hpos.le
    constructor <;> nlinarith
theorem offsetInBox_refinedOffset {m : ℕ} {a : Fin 4 → ℤ} (ha : OffsetInBox m a) (o : BlockOffset L) :
    OffsetInBox (refinedRadius L m) (refinedOffset L a o) :=
  (offsetInBox_refinedRadius_iff hL).mpr (by rwa [coarseOffset_refinedOffset])
end OddSide
theorem abs_coarseOffset_add_sub_le {h e : Fin 4 → ℤ} {ρ : ℕ} {i : Fin 4} (he : |e i| + L ≤ (L : ℤ) * ρ) :
    |coarseOffset L (h + e) i - coarseOffset L h i| ≤ (ρ : ℤ) := by
  have hpos : (0 : ℤ) < L := side_pos_int
  simp only [coarseOffset, Pi.add_apply]
  set u := h i + ((L : ℤ) - 1) / 2 with hu
  have ev : h i + e i + ((L : ℤ) - 1) / 2 = u + e i := by rw [hu]; ring
  rw [ev]
  have e1 := Int.emod_add_mul_ediv u (L : ℤ)
  have e2 := Int.emod_nonneg u hpos.ne'
  have e3 := Int.emod_lt_of_pos u hpos
  have f1 := Int.emod_add_mul_ediv (u + e i) (L : ℤ)
  have f2 := Int.emod_nonneg (u + e i) hpos.ne'
  have f3 := Int.emod_lt_of_pos (u + e i) hpos
  set q := u / (L : ℤ)
  set q' := (u + e i) / (L : ℤ)
  have hb := abs_le.mp (le_refl |e i|)
  have k1 : (L : ℤ) * (q' - q) ≤ (L : ℤ) * ρ := by nlinarith
  have k2 : (L : ℤ) * (-(ρ : ℤ)) ≤ (L : ℤ) * (q' - q) := by nlinarith
  rw [abs_le]
  exact ⟨le_of_mul_le_mul_left k2 hpos, le_of_mul_le_mul_left k1 hpos⟩
theorem refinedRadius_lt_side (hL : Odd L) {m : ℕ} (hn : 2 * m + 2 < n) : 2 * refinedRadius L m + 2 < n * L := by
  obtain ⟨s, hs⟩ := hL
  have h0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hL1 : 2 ≤ L ∨ L = 1 := by omega
  unfold refinedRadius
  have : (L - 1) / 2 = s := by omega
  rw [this]
  have h3 : (2 * m + 3) * L ≤ n * L := Nat.mul_le_mul_right _ (by omega)
  rcases hL1 with h | h
  · have : s < L := by omega
    nlinarith
  · subst h
    have : s = 0 := by omega
    subst this
    omega
section SitesOfBlocks
variable {y : TorusSite n} {y' : TorusSite n'} {m : ℕ} {Z : Finset (TorusSite n)} {Z' : Finset (TorusSite n')}
theorem mem_sitesInBlocks {x : TorusSite (n * L)} : x ∈ sitesInBlocks L Z ↔ parentBlock L x ∈ Z := by
  classical
  simp [sitesInBlocks]
theorem congruentInBoxes_sitesInBlocks (hL : Odd L) (hZ : CongruentInBoxes Z Z' y y' m) :
    CongruentInBoxes (sitesInBlocks L Z) (sitesInBlocks L Z') (blockCentre L y) (blockCentre L y')
      (refinedRadius L m) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun h hh => ?_⟩
  · obtain ⟨a, ha, he⟩ := hZ.1 _ (mem_sitesInBlocks.mp hx)
    exact ⟨_, offsetInBox_refinedOffset hL ha _, eq_blockCentre_add_of_parentBlock he⟩
  · obtain ⟨a, ha, he⟩ := hZ.2.1 _ (mem_sitesInBlocks.mp hx)
    exact ⟨_, offsetInBox_refinedOffset hL ha _, eq_blockCentre_add_of_parentBlock he⟩
  · rw [mem_sitesInBlocks, mem_sitesInBlocks, parentBlock_blockCentre_add, parentBlock_blockCentre_add]
    exact hZ.2.2 _ ((offsetInBox_refinedRadius_iff hL).mp hh)
theorem ballsInBox_sitesInBlocks (hL : Odd L) {ρ ρ' : ℕ} (hρ : ρ' + L ≤ L * ρ) (hZ : BallsInBox y m Z ρ) :
    BallsInBox (blockCentre L y) (refinedRadius L m) (sitesInBlocks L Z) ρ' := by
  intro h hh hx e he
  have hb := (offsetInBox_refinedRadius_iff hL).mp hh
  have hin : y + siteOfInt (coarseOffset L h) ∈ Z := by
    rw [← parentBlock_blockCentre_add]
    exact mem_sitesInBlocks.mp hx
  have hball := hZ _ hb hin
  refine (offsetInBox_refinedRadius_iff hL).mpr ?_
  have key : ∀ i, |coarseOffset L (h + e) i - coarseOffset L h i| ≤ (ρ : ℤ) := fun i =>
    abs_coarseOffset_add_sub_le (by
      have h1 := he i
      have h2 : ((ρ' + L : ℕ) : ℤ) ≤ ((L * ρ : ℕ) : ℤ) := by exact_mod_cast hρ
      push_cast at h2
      linarith)
  have := hball (coarseOffset L (h + e) - coarseOffset L h) key
  simpa using this
end SitesOfBlocks
end YangMills.Construction.CongruentBoxes
end
