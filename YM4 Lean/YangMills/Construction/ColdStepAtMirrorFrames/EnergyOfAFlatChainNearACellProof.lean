import YangMills.Construction.ClusterExpansionOfAStep.ChainOnATorus
import YangMills.Construction.ColdStepAtMirrorFrames.EnergyOfAFlatChainNearACell
import YangMills.Construction.ColdStepAtMirrorFrames.GaugeOfAFormAtTheScaleOfACell
import YangMills.Construction.HoleBesideASecondHole.DistancesBlocksAndLumpsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace FlatChainEnergy
variable {F : BlockFrame}
theorem period_pos (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) (j : ℕ) (i : Fin 4) :
    0 < F.period j i := by apply _root_.YangMills.Construction.LumpContours.period_pos <;> assumption
theorem period_succ {j : ℕ} (hj : j < F.top) (i : Fin 4) :
    F.period j i = F.blockSide * F.period (j + 1) i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.period_succ <;> assumption
theorem period_eq_pow_mul (j : ℕ) (i : Fin 4) :
    F.period j i = F.blockSide ^ (F.top - j) * F.period F.top i := by
  unfold BlockFrame.period
  simp only [Nat.sub_self, pow_zero, mul_one]
  ring
theorem siteOfCoords_add (j : ℕ) (u v : Fin 4 → ℤ) :
    (siteOfCoords j (u + v) : F.Site j) = siteOfCoords j u + siteOfCoords j v := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem siteOfCoords_siteCoords {j : ℕ} (x : F.Site j) : siteOfCoords j (siteCoords x) = x := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
theorem siteOfCoords_eq_iff {j : ℕ} (u v : Fin 4 → ℤ) :
    (siteOfCoords j u : F.Site j) = siteOfCoords j v ↔ ∀ i, ∃ k : ℤ, v i = u i + k * F.period j i := by
  constructor
  · intro h i
    have h1 : ((u i : ℤ) : ZMod (F.period j i)) = (v i : ℤ) := congrFun h i
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
    exact ⟨k, by linarith [mul_comm (k : ℤ) (F.period j i : ℤ)]⟩
  · intro h
    funext i
    obtain ⟨k, hk⟩ := h i
    refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 ⟨k, ?_⟩
    show v i - u i = _
    rw [hk]; ring
theorem siteCoords_siteOfCoords {j : ℕ} (u : Fin 4 → ℤ) (i : Fin 4) :
    ∃ k : ℤ, siteCoords (siteOfCoords j u : F.Site j) i = u i + k * F.period j i :=
  (siteOfCoords_eq_iff u (siteCoords (siteOfCoords j u : F.Site j))).1 (siteOfCoords_siteCoords _).symm i
theorem siteOfCoords_scale {j j' : ℕ} {M : ℕ} (hper : ∀ i, F.period j i = M * F.period j' i)
    (u : Fin 4 → ℤ) :
    (siteOfCoords j (fun i => (M : ℤ) * siteCoords (siteOfCoords j' u : F.Site j') i) : F.Site j) =
      siteOfCoords j (fun i => (M : ℤ) * u i) := by
  refine (siteOfCoords_eq_iff _ _).2 fun i => ?_
  obtain ⟨k, hk⟩ := siteCoords_siteOfCoords (F := F) (j := j') u i
  refine ⟨-k, ?_⟩
  rw [hk, hper i]; push_cast; ring
theorem refineSite_eq {j : ℕ} (y : F.Site (j + 1)) :
    refineSite y = siteOfCoords j (fun i => (F.blockSide : ℤ) * siteCoords y i) := rfl
theorem refineSite_add {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (u : Fin 4 → ℤ) :
    refineSite (y + siteOfCoords (j + 1) u) =
      refineSite y + siteOfCoords j (fun i => (F.blockSide : ℤ) * u i) := by
  have h1 : y + siteOfCoords (j + 1) u = siteOfCoords (j + 1) (siteCoords y + u) := by
    rw [siteOfCoords_add, siteOfCoords_siteCoords]
  rw [h1, refineSite_eq, siteOfCoords_scale (fun i => period_succ hj i), refineSite_eq,
    ← siteOfCoords_add]
  congr 1
  funext i
  simp [mul_add]
theorem mem_centredCube_iff {M : ℕ} (h : Fin 4 → ℤ) :
    h ∈ centredCube M ↔ ∀ i, -(((M : ℤ) - 1) / 2) ≤ h i ∧ h i ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.CutAction.mem_centredCube <;> assumption
theorem card_centredCube {M : ℕ} (hM : Odd M) : (centredCube M).card = M ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
def centredQuot (M : ℕ) (a : ℤ) : ℤ := (a + ((M : ℤ) - 1) / 2) / M
def centredRem (M : ℕ) (a : ℤ) : ℤ := (a + ((M : ℤ) - 1) / 2) % M - ((M : ℤ) - 1) / 2
theorem centredQuot_add_centredRem (M : ℕ) (a : ℤ) : a = M * centredQuot M a + centredRem M a := by
  have := Int.mul_ediv_add_emod (a + ((M : ℤ) - 1) / 2) M
  unfold centredQuot centredRem
  linarith
theorem centredRem_bounds {M : ℕ} (hM : Odd M) (a : ℤ) :
    -(((M : ℤ) - 1) / 2) ≤ centredRem M a ∧ centredRem M a ≤ ((M : ℤ) - 1) / 2 := by
  obtain ⟨m, rfl⟩ := hM
  have h : (((2 * m + 1 : ℕ) : ℤ) - 1) / 2 = m := by push_cast; omega
  have hp : (0 : ℤ) < ((2 * m + 1 : ℕ) : ℤ) := by positivity
  have h1 := Int.emod_nonneg (a + (((2 * m + 1 : ℕ) : ℤ) - 1) / 2) hp.ne'
  have h2 := Int.emod_lt_of_pos (a + (((2 * m + 1 : ℕ) : ℤ) - 1) / 2) hp
  unfold centredRem
  rw [h] at *
  push_cast at *
  constructor <;> omega
theorem centredQuot_unique {M : ℕ} (hM : Odd M) {a q r : ℤ} (h : a = M * q + r)
    (h1 : -(((M : ℤ) - 1) / 2) ≤ r) (h2 : r ≤ ((M : ℤ) - 1) / 2) :
    centredQuot M a = q ∧ centredRem M a = r := by
  obtain ⟨m, rfl⟩ := hM
  have hh : (((2 * m + 1 : ℕ) : ℤ) - 1) / 2 = m := by push_cast; omega
  have hp : (0 : ℤ) < ((2 * m + 1 : ℕ) : ℤ) := by positivity
  rw [hh] at h1 h2
  have e : a + (((2 * m + 1 : ℕ) : ℤ) - 1) / 2 = (r + m) + ((2 * m + 1 : ℕ) : ℤ) * q := by
    rw [hh, h]; ring
  have hr0 : 0 ≤ r + m := by omega
  have hr1 : r + m < ((2 * m + 1 : ℕ) : ℤ) := by push_cast; omega
  have e1 : (a + (((2 * m + 1 : ℕ) : ℤ) - 1) / 2) / ((2 * m + 1 : ℕ) : ℤ) = q := by
    rw [e, Int.add_mul_ediv_left _ _ hp.ne', Int.ediv_eq_zero_of_lt hr0 hr1]; simp
  have e2 : (a + (((2 * m + 1 : ℕ) : ℤ) - 1) / 2) % ((2 * m + 1 : ℕ) : ℤ) = r + m := by
    rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hr0 hr1]
  unfold centredQuot centredRem
  refine ⟨e1, ?_⟩
  rw [e2, hh]; ring
theorem block_recompose {j j' : ℕ} {M : ℕ} (hper : ∀ i, F.period j i = M * F.period j' i)
    (x : F.Site j) :
    siteOfCoords j (fun i => (M : ℤ) *
        siteCoords (siteOfCoords j' (fun i => centredQuot M (siteCoords x i)) : F.Site j') i) +
      siteOfCoords j (fun i => centredRem M (siteCoords x i)) = x := by
  rw [siteOfCoords_scale hper, ← siteOfCoords_add]
  conv_rhs => rw [← siteOfCoords_siteCoords x]
  congr 1
  funext i
  simpa using (centredQuot_add_centredRem M (siteCoords x i)).symm
theorem block_decompose {j j' : ℕ} {M : ℕ} (hM : Odd M) (hper : ∀ i, F.period j i = M * F.period j' i)
    (y : F.Site j') (h : Fin 4 → ℤ) (hh : h ∈ centredCube M) :
    siteOfCoords j' (fun i => centredQuot M (siteCoords (siteOfCoords j (fun i => (M : ℤ) * siteCoords y i) +
        siteOfCoords j h : F.Site j) i)) = y ∧
      (fun i => centredRem M (siteCoords (siteOfCoords j (fun i => (M : ℤ) * siteCoords y i) +
        siteOfCoords j h : F.Site j) i)) = h := by
  have key : ∀ i, ∃ k : ℤ,
      centredQuot M (siteCoords (siteOfCoords j (fun i => (M : ℤ) * siteCoords y i) +
          siteOfCoords j h : F.Site j) i) = siteCoords y i + k * F.period j' i ∧
      centredRem M (siteCoords (siteOfCoords j (fun i => (M : ℤ) * siteCoords y i) +
          siteOfCoords j h : F.Site j) i) = h i := by
    intro i
    rw [← siteOfCoords_add]
    obtain ⟨k, hk⟩ := siteCoords_siteOfCoords (F := F) (j := j) ((fun i => (M : ℤ) * siteCoords y i) + h) i
    have hb := (mem_centredCube_iff h).1 hh i
    have e : siteCoords (siteOfCoords j ((fun i => (M : ℤ) * siteCoords y i) + h) : F.Site j) i =
        M * (siteCoords y i + k * F.period j' i) + h i := by
      rw [hk, hper i]; simp only [Pi.add_apply]; push_cast; ring
    obtain ⟨e1, e2⟩ := centredQuot_unique hM e hb.1 hb.2
    exact ⟨k, e1, e2⟩
  constructor
  · conv_rhs => rw [← siteOfCoords_siteCoords y]
    refine (siteOfCoords_eq_iff _ _).2 fun i => ?_
    obtain ⟨k, e1, -⟩ := key i
    exact ⟨-k, by rw [e1]; ring⟩
  · funext i
    obtain ⟨k, -, e2⟩ := key i
    exact e2
theorem sum_over_blocks {j j' : ℕ} {M : ℕ} (hM : Odd M) (hper : ∀ i, F.period j i = M * F.period j' i)
    (S : Finset (F.Site j)) (S' : Finset (F.Site j')) (hS : ∀ x, x ∈ S) (hS' : ∀ y, y ∈ S')
    (g : F.Site j → ℝ) :
    ∑ y ∈ S', ∑ h ∈ centredCube M, g (siteOfCoords j (fun i => (M : ℤ) * siteCoords y i) + siteOfCoords j h) =
      ∑ x ∈ S, g x := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij'
    (fun p => siteOfCoords j (fun i => (M : ℤ) * siteCoords p.1 i) + siteOfCoords j p.2)
    (fun x => (siteOfCoords j' (fun i => centredQuot M (siteCoords x i)), fun i => centredRem M (siteCoords x i)))
    (fun _ _ => hS _) (fun x _ => ?_) (fun p hp => ?_) (fun x _ => block_recompose hper x) (fun _ _ => rfl)
  · exact Finset.mem_product.2 ⟨hS' _, (mem_centredCube_iff _).2 fun i => centredRem_bounds hM _⟩
  · obtain ⟨e1, e2⟩ := block_decompose hM hper p.1 p.2 (Finset.mem_product.1 hp).2
    exact Prod.ext e1 e2
theorem mem_finiteCells (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) (z : F.Cell) :
    z ∈ finiteCells F := by
  haveI : ∀ i, NeZero (F.period F.top i) := fun i => ⟨(period_pos hL hs F.top i).ne'⟩
  have h : Finite F.Cell := inferInstance
  rw [finiteCells, dif_pos h]
  exact @Finset.mem_univ _ (Fintype.ofFinite _) z
theorem mem_sitesOfCells_finite (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (x : F.Site j) :
    x ∈ sitesOfCells (finiteCells F) j := by
  have hL0 : 0 < F.blockSide := hL.pos
  have hM : Odd (F.blockSide ^ (F.top - j)) := hL.pow
  unfold sitesOfCells
  refine Finset.mem_biUnion.2 ⟨siteOfCoords F.top (fun i => centredQuot (F.blockSide ^ (F.top - j)) (siteCoords x i)),
    mem_finiteCells hL0 hs _, Finset.mem_image.2 ⟨fun i => centredRem (F.blockSide ^ (F.top - j)) (siteCoords x i),
      (mem_centredCube_iff _).2 fun i => centredRem_bounds hM _, ?_⟩⟩
  have h := block_recompose (F := F) (j := j) (j' := F.top) (M := F.blockSide ^ (F.top - j))
    (fun i => period_eq_pow_mul j i) x
  unfold cellCentre
  simpa using h
theorem sum_translate (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (u : F.Site j)
    (g : F.Site j → ℝ) :
    ∑ x ∈ sitesOfCells (finiteCells F) j, g (x + u) = ∑ x ∈ sitesOfCells (finiteCells F) j, g x :=
  Finset.sum_nbij' (fun x => x + u) (fun x => x - u) (fun _ _ => mem_sitesOfCells_finite hL hs _)
    (fun _ _ => mem_sitesOfCells_finite hL hs _) (fun x _ => by simp) (fun x _ => by simp) (fun _ _ => rfl)
theorem distToMultiples_le {n : ℝ} (hn : 0 < n) (u : ℝ) (k : ℤ) : distToMultiples n u ≤ |u - n * k| := by
  unfold distToMultiples
  have h := round_le (u / n) k
  have e1 : u - n * round (u / n) = n * (u / n - round (u / n)) := by field_simp
  have e2 : u - n * k = n * (u / n - k) := by field_simp
  rw [e1, e2, abs_mul, abs_mul, abs_of_pos hn]
  exact mul_le_mul_of_nonneg_left h hn.le
theorem distToMultiples_add_le {n : ℝ} (hn : 0 < n) (u v : ℝ) :
    distToMultiples n (u + v) ≤ distToMultiples n u + |v| := by
  refine (distToMultiples_le hn (u + v) (round (u / n))).trans ?_
  have e : u + v - n * round (u / n) = (u - n * round (u / n)) + v := by ring
  rw [e]
  exact abs_add_le _ _
theorem distToMultiples_add_mul {n : ℝ} (hn : 0 < n) (u : ℝ) (k : ℤ) :
    distToMultiples n (u + n * k) = distToMultiples n u := by
  apply le_antisymm
  · refine (distToMultiples_le hn (u + n * k) (k + round (u / n))).trans (le_of_eq ?_)
    unfold distToMultiples
    push_cast
    congr 1
    ring
  · refine (distToMultiples_le hn u (round ((u + n * k) / n) - k)).trans (le_of_eq ?_)
    unfold distToMultiples
    push_cast
    congr 1
    ring
theorem extent_pos_real (hs : ∀ i, 0 < F.extent i) (i : Fin 4) : (0 : ℝ) < F.extent i := by
  exact_mod_cast hs i
theorem distToMultiples_cellCoordinate (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (u : Fin 4 → ℤ) (i : Fin 4) (c : ℝ) :
    distToMultiples (F.extent i) (cellCoordinate (siteOfCoords j u : F.Site j) i - c) =
      distToMultiples (F.extent i) ((u i : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) - c) := by
  obtain ⟨k, hk⟩ := siteCoords_siteOfCoords (F := F) (j := j) u i
  have e : cellCoordinate (siteOfCoords j u : F.Site j) i - c =
      ((u i : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) - c) + (F.extent i : ℝ) * k := by
    unfold cellCoordinate
    rw [hk]
    unfold BlockFrame.period
    push_cast
    field_simp
    ring
  rw [e, distToMultiples_add_mul (extent_pos_real hs i)]
theorem torusSupDist_add_le (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (x : F.Site j)
    (z : F.Cell) (u : Fin 4 → ℤ) (A : ℝ) (hA : ∀ i, |(u i : ℝ)| ≤ A) :
    torusSupDist (x + siteOfCoords j u) z ≤ torusSupDist x z + A / (F.blockSide : ℝ) ^ (F.top - j) := by
  have hM : (0 : ℝ) < (F.blockSide : ℝ) ^ (F.top - j) := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
    positivity
  unfold torusSupDist
  refine Finset.sup'_le _ _ fun i _ => ?_
  have h1 : x + siteOfCoords j u = siteOfCoords j (siteCoords x + u) := by
    rw [siteOfCoords_add, siteOfCoords_siteCoords]
  rw [h1, distToMultiples_cellCoordinate hL hs]
  have e : (((siteCoords x + u) i : ℤ) : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) - (siteCoords z i : ℝ) =
      (cellCoordinate x i - siteCoords z i) + (u i : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) := by
    unfold cellCoordinate
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [e]
  refine (distToMultiples_add_le (extent_pos_real hs i) _ _).trans (add_le_add ?_ ?_)
  · exact Finset.le_sup' (fun i => distToMultiples (F.extent i) (cellCoordinate x i - siteCoords z i))
      (Finset.mem_univ i)
  · rw [abs_div, abs_of_pos hM]
    exact div_le_div_of_nonneg_right (hA i) hM.le
theorem torusSupDist_le_add (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (x : F.Site j)
    (z : F.Cell) (u : Fin 4 → ℤ) (A : ℝ) (hA : ∀ i, |(u i : ℝ)| ≤ A) :
    torusSupDist x z ≤ torusSupDist (x + siteOfCoords j u) z + A / (F.blockSide : ℝ) ^ (F.top - j) := by
  have h := torusSupDist_add_le hL hs (x + siteOfCoords j u) z (-u) A (fun i => by simpa using hA i)
  have e : x + siteOfCoords j u + siteOfCoords j (-u) = x := by
    rw [add_assoc, ← siteOfCoords_add]
    simp only [add_neg_cancel]
    have : (siteOfCoords j 0 : F.Site j) = 0 := by funext i; simp [siteOfCoords]
    rw [this, add_zero]
  rwa [e] at h
theorem torusSupDist_refineSite (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (hj : j < F.top)
    (y : F.Site (j + 1)) (z : F.Cell) : torusSupDist (refineSite y) z = torusSupDist y z := by
  unfold torusSupDist
  refine Finset.sup'_congr _ rfl fun i _ => ?_
  rw [refineSite_eq, distToMultiples_cellCoordinate hL hs]
  have e : (((F.blockSide : ℤ) * siteCoords y i : ℤ) : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) =
      cellCoordinate y i := by
    unfold cellCoordinate
    have h1 : F.top - j = (F.top - (j + 1)) + 1 := by omega
    rw [h1, pow_succ]
    push_cast
    field_simp
  rw [e]
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
theorem torusSupDist_le_of_cellSupDist (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (x : F.Site j) (z : F.Cell) (r : ℕ) (h : cellSupDist (enclosingCell x) z ≤ r) :
    torusSupDist x z ≤ r + 1 := by
  unfold torusSupDist
  refine Finset.sup'_le _ _ fun i _ => ?_
  set M : ℤ := (F.blockSide : ℤ) ^ (F.top - j) with hMdef
  have hM : 0 < M := by
    have : (0 : ℤ) < F.blockSide := by exact_mod_cast hL
    positivity
  set q : ℤ := (siteCoords x i + (M - 1) / 2) / M with hq
  set d : ℤ := (((enclosingCell x : F.Cell) i - z i).valMinAbs) with hd
  have hdr : (d.natAbs : ℝ) ≤ r := by
    have h1 : d.natAbs ≤ cellSupDist (enclosingCell x) z :=
      Finset.le_sup (f := fun i => (((enclosingCell x : F.Cell) i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
    exact_mod_cast h1.trans h
  have hcast : ((d : ℤ) : ZMod (F.period F.top i)) = ((q - siteCoords z i : ℤ) : ZMod (F.period F.top i)) := by
    rw [hd, ZMod.coe_valMinAbs]
    push_cast
    simp [enclosingCell, siteOfCoords, siteCoords, hq, hMdef]
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hcast
  rw [period_top] at hk
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hε : |(siteCoords x i : ℝ) / M - q| ≤ 1 := by
    have h0 := Int.emod_nonneg (siteCoords x i + (M - 1) / 2) hM.ne'
    have h1 := Int.emod_lt_of_pos (siteCoords x i + (M - 1) / 2) hM
    have h2 := Int.mul_ediv_add_emod (siteCoords x i + (M - 1) / 2) M
    have h3 : 0 ≤ (M - 1) / 2 := by omega
    have h4 : (M - 1) / 2 < M := by omega
    have h5 : -M ≤ siteCoords x i - M * q := by rw [hq]; omega
    have h6 : siteCoords x i - M * q ≤ M := by rw [hq]; omega
    have h5r : -(M : ℝ) ≤ (siteCoords x i : ℝ) - M * q := by exact_mod_cast h5
    have h6r : (siteCoords x i : ℝ) - M * q ≤ M := by exact_mod_cast h6
    have e : (siteCoords x i : ℝ) / M - q = ((siteCoords x i : ℝ) - M * q) / M := by field_simp
    rw [e, abs_div, abs_of_pos hMr, div_le_one hMr]
    exact abs_le.2 ⟨h5r, h6r⟩
  have e : cellCoordinate x i - (siteCoords z i : ℝ) =
      (((siteCoords x i : ℝ) / M - q) + d) + (F.extent i : ℝ) * k := by
    have hk' : (q : ℝ) - siteCoords z i - d = (F.extent i : ℝ) * k := by exact_mod_cast hk
    unfold cellCoordinate
    have : ((F.blockSide : ℝ) ^ (F.top - j)) = (M : ℝ) := by rw [hMdef]; push_cast; rfl
    rw [this]
    linarith
  rw [e, distToMultiples_add_mul (extent_pos_real hs i)]
  refine (distToMultiples_le (extent_pos_real hs i) _ 0).trans ?_
  simp only [Int.cast_zero, mul_zero, sub_zero]
  refine (abs_add_le _ _).trans ?_
  have : |(d : ℝ)| = d.natAbs := by
    rw [Nat.cast_natAbs]; push_cast; rfl
  rw [this]
  linarith
theorem cellSupDist_le_torusSupDist (hs : ∀ i, 0 < F.extent i) (c z : F.Cell) :
    (cellSupDist z c : ℝ) ≤ torusSupDist c z := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun i => ((z i - c i).valMinAbs).natAbs)
  have hle : distToMultiples (F.extent i) (cellCoordinate c i - siteCoords z i) ≤ torusSupDist c z :=
    Finset.le_sup' (fun i => distToMultiples (F.extent i) (cellCoordinate c i - siteCoords z i))
      (Finset.mem_univ i)
  refine le_trans ?_ hle
  unfold cellSupDist
  rw [hi]
  set u : ℤ := siteCoords c i - siteCoords z i with hu
  have hpos : cellCoordinate c i - (siteCoords z i : ℝ) = (u : ℝ) := by
    unfold cellCoordinate
    simp [hu]
  rw [hpos]
  set k : ℤ := round ((u : ℝ) / (F.extent i : ℝ)) with hk
  set m : ℤ := u - (F.extent i : ℤ) * k with hm
  have hgap : distToMultiples (F.extent i) (u : ℝ) = ((m.natAbs : ℕ) : ℝ) := by
    unfold distToMultiples
    rw [← hk, Nat.cast_natAbs, hm]
    push_cast
    rfl
  rw [hgap]
  have hside : ((F.extent i : ℕ) : ZMod (F.period F.top i)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (period_top i).dvd
  haveI : NeZero (F.period F.top i) := ⟨by rw [period_top]; exact (hs i).ne'⟩
  have hc : ((((z i - c i).valMinAbs : ℤ)) : ZMod (F.period F.top i)) =
      ((-m : ℤ) : ZMod (F.period F.top i)) := by
    rw [ZMod.coe_valMinAbs, hm, hu]
    push_cast
    rw [hside]
    simp [siteCoords]
  have := ZMod.natAbs_min_of_le_div_two _ _ _ hc (ZMod.natAbs_valMinAbs_le _)
  rw [Int.natAbs_neg] at this
  exact_mod_cast this
abbrev allSites (F : BlockFrame) (j : ℕ) : Finset (F.Site j) := sitesOfCells (finiteCells F) j
def readSite {j : ℕ} (y : F.Site (j + 1)) (h : Fin 4 → ℤ) (l : ℕ) (i : Fin 4) : F.Site j :=
  refineSite y + siteOfCoords j h + siteOfCoords j (Pi.single i (l : ℤ))
theorem lineAverage_eq {j : ℕ} (B : LevelForm F j) (y : F.Site (j + 1)) (i : Fin 4) :
    lineAverage B y i = (1 / (F.blockSide : ℝ) ^ 4) *
      ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide, B (readSite y h l i) i := rfl
theorem sum_readSite (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (hj : j < F.top) (i : Fin 4)
    (g : F.Site j → ℝ) :
    ∑ y ∈ allSites F (j + 1), ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
        g (readSite y h l i) = F.blockSide * ∑ x ∈ allSites F j, g x := by
  have h1 : ∀ l : ℕ, ∑ y ∈ allSites F (j + 1), ∑ h ∈ centredCube F.blockSide, g (readSite y h l i) =
      ∑ x ∈ allSites F j, g x := by
    intro l
    have := sum_over_blocks hL (fun i => period_succ hj i) (allSites F j) (allSites F (j + 1))
      (mem_sitesOfCells_finite hL hs) (mem_sitesOfCells_finite hL hs)
      (fun x => g (x + siteOfCoords j (Pi.single i (l : ℤ))))
    rw [sum_translate hL hs] at this
    exact this
  calc ∑ y ∈ allSites F (j + 1), ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
        g (readSite y h l i)
      = ∑ y ∈ allSites F (j + 1), ∑ l ∈ Finset.range F.blockSide, ∑ h ∈ centredCube F.blockSide,
          g (readSite y h l i) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ l ∈ Finset.range F.blockSide, ∑ y ∈ allSites F (j + 1), ∑ h ∈ centredCube F.blockSide,
          g (readSite y h l i) :=
        Finset.sum_comm
    _ = ∑ l ∈ Finset.range F.blockSide, ∑ x ∈ allSites F j, g x := Finset.sum_congr rfl fun l _ => h1 l
    _ = F.blockSide * ∑ x ∈ allSites F j, g x := by simp
def readRadius (F : BlockFrame) (j : ℕ) : ℝ := 2 * (F.blockSide : ℝ) / (F.blockSide : ℝ) ^ (F.top - j)
theorem readSite_dist (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (hj : j < F.top)
    (y : F.Site (j + 1)) {h : Fin 4 → ℤ} (hh : h ∈ centredCube F.blockSide) {l : ℕ} (hl : l < F.blockSide)
    (i : Fin 4) (z : F.Cell) :
    |torusSupDist (readSite y h l i) z - torusSupDist y z| ≤ readRadius F j := by
  have hL0 := hL.pos
  have e : readSite y h l i = refineSite y + siteOfCoords j (h + (Pi.single i (l : ℤ) : Fin 4 → ℤ)) := by
    unfold readSite
    rw [siteOfCoords_add, add_assoc]
  have hb : ∀ k, |(((h + (Pi.single i (l : ℤ) : Fin 4 → ℤ)) k : ℤ) : ℝ)| ≤ 2 * (F.blockSide : ℝ) := by
    intro k
    have h1 := (mem_centredCube_iff h).1 hh k
    have h3 : |(h + (Pi.single i (l : ℤ) : Fin 4 → ℤ)) k| ≤ 2 * (F.blockSide : ℤ) := by
      have h4 : (0 : ℤ) ≤ (Pi.single i (l : ℤ) : Fin 4 → ℤ) k ∧
          (Pi.single i (l : ℤ) : Fin 4 → ℤ) k ≤ F.blockSide := by
        by_cases hk : k = i
        · subst hk
          simp only [Pi.single_eq_same]
          omega
        · simp only [Pi.single_apply, if_neg hk]
          omega
      simp only [Pi.add_apply]
      rw [abs_le]
      constructor <;> omega
    exact_mod_cast h3
  rw [e, ← torusSupDist_refineSite hL0 hs hj y z]
  unfold readRadius
  rw [abs_le]
  constructor
  · have := torusSupDist_le_add hL0 hs (refineSite y) z _ _ hb
    linarith
  · have := torusSupDist_add_le hL0 hs (refineSite y) z _ _ hb
    linarith
theorem sq_kernel_average_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (hj : j < F.top)
    (κ : F.Site (j + 1) → F.Site j → ℝ) (u : F.Site j → ℝ) (A : ℝ) (hA : 0 ≤ A) (hu : ∀ x, 0 ≤ u x)
    (hk : ∀ (y : F.Site (j + 1)) (h : Fin 4 → ℤ) (l : ℕ) (i : Fin 4), h ∈ centredCube F.blockSide →
      l < F.blockSide → |κ y (readSite y h l i)| ≤ A * u (readSite y h l i)) (B : LevelForm F j) :
    ∑ y ∈ allSites F (j + 1), ∑ i : Fin 4,
        ((1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
          κ y (readSite y h l i) * B (readSite y h l i) i) ^ 2 ≤
      (A / F.blockSide) ^ 2 * ∑ x ∈ allSites F j, ∑ i : Fin 4, (u x * B x i) ^ 2 := by
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have step : ∀ (y : F.Site (j + 1)) (i : Fin 4),
      ((1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
          κ y (readSite y h l i) * B (readSite y h l i) i) ^ 2 ≤
        (A ^ 2 / (F.blockSide : ℝ) ^ 3) * ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
          (u (readSite y h l i) * B (readSite y h l i) i) ^ 2 := by
    intro y i
    have c1 : (∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
          κ y (readSite y h l i) * B (readSite y h l i) i) ^ 2 ≤
        (F.blockSide : ℝ) ^ 5 * ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
          (κ y (readSite y h l i) * B (readSite y h l i) i) ^ 2 := by
      rw [← Finset.sum_product', ← Finset.sum_product']
      have c0 : (∑ p ∈ centredCube F.blockSide ×ˢ Finset.range F.blockSide,
            κ y (readSite y p.1 p.2 i) * B (readSite y p.1 p.2 i) i) ^ 2 ≤
          ((centredCube F.blockSide ×ˢ Finset.range F.blockSide).card : ℝ) *
            ∑ p ∈ centredCube F.blockSide ×ˢ Finset.range F.blockSide,
              (κ y (readSite y p.1 p.2 i) * B (readSite y p.1 p.2 i) i) ^ 2 := sq_sum_le_card_mul_sum_sq
      refine c0.trans (le_of_eq ?_)
      rw [Finset.card_product, card_centredCube hL, Finset.card_range]
      push_cast
      ring
    have c2 : ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
          (κ y (readSite y h l i) * B (readSite y h l i) i) ^ 2 ≤
        A ^ 2 * ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
          (u (readSite y h l i) * B (readSite y h l i) i) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun h hh => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun l hl => ?_
      have h1 := hk y h l i hh (Finset.mem_range.1 hl)
      have h2 : κ y (readSite y h l i) ^ 2 ≤ (A * u (readSite y h l i)) ^ 2 :=
        sq_le_sq.2 (h1.trans (le_abs_self (A * u (readSite y h l i))))
      have e2 : A ^ 2 * (u (readSite y h l i) * B (readSite y h l i) i) ^ 2 =
          (A * u (readSite y h l i)) ^ 2 * B (readSite y h l i) i ^ 2 := by ring
      rw [e2, mul_pow]
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg (B (readSite y h l i) i))
    rw [mul_pow]
    have e : (1 / (F.blockSide : ℝ) ^ 4) ^ 2 * ((F.blockSide : ℝ) ^ 5 * A ^ 2) =
        A ^ 2 / (F.blockSide : ℝ) ^ 3 := by
      field_simp
    calc _ ≤ (1 / (F.blockSide : ℝ) ^ 4) ^ 2 * ((F.blockSide : ℝ) ^ 5 * (A ^ 2 *
          ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
            (u (readSite y h l i) * B (readSite y h l i) i) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (c1.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left c2 (by positivity)
      _ = _ := by rw [← e]; ring
  calc _ ≤ ∑ y ∈ allSites F (j + 1), ∑ i : Fin 4, (A ^ 2 / (F.blockSide : ℝ) ^ 3) *
        ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
          (u (readSite y h l i) * B (readSite y h l i) i) ^ 2 :=
        Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun i _ => step y i
    _ = ∑ i : Fin 4, (A ^ 2 / (F.blockSide : ℝ) ^ 3) * ∑ y ∈ allSites F (j + 1),
        ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
          (u (readSite y h l i) * B (readSite y h l i) i) ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ i : Fin 4, (A ^ 2 / (F.blockSide : ℝ) ^ 3) *
        (F.blockSide * ∑ x ∈ allSites F j, (u x * B x i) ^ 2) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sum_readSite hL hs hj i (fun x => (u x * B x i) ^ 2)]
    _ = _ := by
        have e : (A / (F.blockSide : ℝ)) ^ 2 = A ^ 2 / (F.blockSide : ℝ) ^ 3 * F.blockSide := by
          field_simp
        simp only [← mul_assoc]
        rw [← Finset.mul_sum, e, Finset.sum_comm]
def weightedNorm {j : ℕ} (u : F.Site j → ℝ) (X : LevelForm F j) : ℝ :=
  Real.sqrt (∑ x ∈ allSites F j, ∑ i : Fin 4, (u x * X x i) ^ 2)
theorem weightedNorm_nonneg {j : ℕ} (u : F.Site j → ℝ) (X : LevelForm F j) : 0 ≤ weightedNorm u X :=
  Real.sqrt_nonneg _
theorem double_sum_sq_nonneg {α β : Type*} (s : Finset α) (t : Finset β) (f : α → β → ℝ) :
    0 ≤ ∑ x ∈ s, ∑ i ∈ t, f x i ^ 2 :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
theorem weightedNorm_sq {j : ℕ} (u : F.Site j → ℝ) (X : LevelForm F j) :
    weightedNorm u X ^ 2 = ∑ x ∈ allSites F j, ∑ i : Fin 4, (u x * X x i) ^ 2 :=
  Real.sq_sqrt (double_sum_sq_nonneg _ _ _)
theorem sqrt_sum_sq_add_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    Real.sqrt (∑ p ∈ s, (f p + g p) ^ 2) ≤
      Real.sqrt (∑ p ∈ s, f p ^ 2) + Real.sqrt (∑ p ∈ s, g p ^ 2) := by
  have hf : 0 ≤ ∑ p ∈ s, f p ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hg : 0 ≤ ∑ p ∈ s, g p ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h := Real.sum_mul_le_sqrt_mul_sqrt s f g
  have e : ∑ p ∈ s, (f p + g p) ^ 2 =
      ∑ p ∈ s, f p ^ 2 + 2 * ∑ p ∈ s, f p * g p + ∑ p ∈ s, g p ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e]
  have s1 := Real.sq_sqrt hf
  have s2 := Real.sq_sqrt hg
  nlinarith
theorem abs_double_sum_mul_le {α β : Type*} (s : Finset α) (t : Finset β) (f g : α → β → ℝ) :
    |∑ x ∈ s, ∑ i ∈ t, f x i * g x i| ≤
      Real.sqrt (∑ x ∈ s, ∑ i ∈ t, f x i ^ 2) * Real.sqrt (∑ x ∈ s, ∑ i ∈ t, g x i ^ 2) := by
  simp only [← Finset.sum_product']
  refine abs_le.2 ⟨?_, Real.sum_mul_le_sqrt_mul_sqrt _ _ _⟩
  have h := Real.sum_mul_le_sqrt_mul_sqrt (s ×ˢ t) (fun p => - f p.1 p.2) (fun p => g p.1 p.2)
  simp only [neg_mul, Finset.sum_neg_distrib, neg_sq] at h
  linarith
theorem weightedNorm_add_le {j : ℕ} (u : F.Site j → ℝ) (X Y : LevelForm F j) :
    weightedNorm u (X + Y) ≤ weightedNorm u X + weightedNorm u Y := by
  unfold weightedNorm
  simp only [← Finset.sum_product', Pi.add_apply, mul_add]
  exact sqrt_sum_sq_add_le _ _ _
theorem abs_pairing_le {j : ℕ} (u v : F.Site j → ℝ) (huv : ∀ x, u x * v x = 1) (X Y : LevelForm F j) :
    |∑ x ∈ allSites F j, ∑ i : Fin 4, X x i * Y x i| ≤ weightedNorm u X * weightedNorm v Y := by
  have h := abs_double_sum_mul_le (allSites F j) Finset.univ (fun x i => u x * X x i)
    (fun x i => v x * Y x i)
  have e : ∑ x ∈ allSites F j, ∑ i : Fin 4, (u x * X x i) * (v x * Y x i) =
      ∑ x ∈ allSites F j, ∑ i : Fin 4, X x i * Y x i := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    have := huv x
    calc u x * X x i * (v x * Y x i) = (u x * v x) * (X x i * Y x i) := by ring
      _ = _ := by rw [this, one_mul]
  rwa [e] at h
theorem weightedNorm_kernel_average_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j < F.top) (κ : F.Site (j + 1) → F.Site j → ℝ) (u : F.Site j → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hu : ∀ x, 0 ≤ u x)
    (hk : ∀ (y : F.Site (j + 1)) (h : Fin 4 → ℤ) (l : ℕ) (i : Fin 4), h ∈ centredCube F.blockSide →
      l < F.blockSide → |κ y (readSite y h l i)| ≤ A * u (readSite y h l i)) (B : LevelForm F j)
    (v : F.Site (j + 1) → ℝ) (T : LevelForm F (j + 1))
    (hT : ∀ y i, v y * T y i = (1 / (F.blockSide : ℝ) ^ 4) *
      ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
        κ y (readSite y h l i) * B (readSite y h l i) i) :
    weightedNorm v T ≤ (A / F.blockSide) * weightedNorm u B := by
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have h := sq_kernel_average_le hL hs hj κ u A hA hu hk B
  refine Real.sqrt_le_iff.2 ⟨mul_nonneg (by positivity) (weightedNorm_nonneg _ _), ?_⟩
  rw [mul_pow, weightedNorm_sq]
  refine le_trans (le_of_eq ?_) h
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => by rw [hT]
theorem weightedNorm_lineAverage_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j < F.top) (v : F.Site (j + 1) → ℝ) (u : F.Site j → ℝ) (θ : ℝ) (hθ : 0 ≤ θ) (hu : ∀ x, 0 ≤ u x)
    (hv : ∀ (y : F.Site (j + 1)) (h : Fin 4 → ℤ) (l : ℕ) (i : Fin 4), h ∈ centredCube F.blockSide →
      l < F.blockSide → |v y| ≤ θ * u (readSite y h l i)) (B : LevelForm F j) :
    weightedNorm v (lineAverage B) ≤ (θ / F.blockSide) * weightedNorm u B := by
  refine weightedNorm_kernel_average_le hL hs hj (fun y _ => v y) u θ hθ hu hv B v _ fun y i => ?_
  rw [lineAverage_eq]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun l _ => ?_
  ring
def expWeight (del : ℝ) (z : F.Cell) {j : ℕ} (x : F.Site j) : ℝ := Real.exp (-(del * torusSupDist x z))
def invWeight (del : ℝ) (z : F.Cell) {j : ℕ} (x : F.Site j) : ℝ := Real.exp (del * torusSupDist x z)
theorem expWeight_pos (del : ℝ) (z : F.Cell) {j : ℕ} (x : F.Site j) : 0 < expWeight del z x :=
  Real.exp_pos _
theorem invWeight_pos (del : ℝ) (z : F.Cell) {j : ℕ} (x : F.Site j) : 0 < invWeight del z x :=
  Real.exp_pos _
theorem expWeight_mul_invWeight (del : ℝ) (z : F.Cell) {j : ℕ} (x : F.Site j) :
    expWeight del z x * invWeight del z x = 1 := by
  unfold expWeight invWeight
  rw [← Real.exp_add]
  simp
theorem invWeight_mul_expWeight (del : ℝ) (z : F.Cell) {j : ℕ} (x : F.Site j) :
    invWeight del z x * expWeight del z x = 1 := by
  rw [mul_comm, expWeight_mul_invWeight]
theorem expWeight_le_of_dist {del : ℝ} (hdel : 0 ≤ del) (z : F.Cell) {j j' : ℕ} (x : F.Site j)
    (y : F.Site j') {ρ : ℝ} (h : |torusSupDist x z - torusSupDist y z| ≤ ρ) :
    expWeight del z y ≤ Real.exp (del * ρ) * expWeight del z x := by
  unfold expWeight
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have := (abs_le.1 h).2
  nlinarith
theorem invWeight_le_of_dist {del : ℝ} (hdel : 0 ≤ del) (z : F.Cell) {j j' : ℕ} (x : F.Site j)
    (y : F.Site j') {ρ : ℝ} (h : |torusSupDist x z - torusSupDist y z| ≤ ρ) :
    invWeight del z y ≤ Real.exp (del * ρ) * invWeight del z x := by
  unfold invWeight
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have := (abs_le.1 h).1
  nlinarith
theorem abs_exp_sub_exp_neg_le {v : ℝ} (h0 : 0 ≤ v) (h2 : v ≤ 2) :
    |Real.exp v - Real.exp (-v)| ≤ 16 * v := by
  have e1 : Real.exp (-v) ≤ Real.exp v := Real.exp_le_exp.2 (by linarith)
  rw [abs_of_nonneg (by linarith)]
  have a1 : 1 - v ≤ Real.exp (-v) := by linarith [Real.add_one_le_exp (-v)]
  have a2 : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
  have a3 : Real.exp v ≤ 15 := by
    have b1 : Real.exp v ≤ Real.exp 2 := Real.exp_le_exp.2 h2
    have b2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have b3 := Real.exp_one_lt_d9
    have b4 := Real.exp_pos 1
    nlinarith
  have a4 : Real.exp v * (1 - v) ≤ 1 := by
    calc Real.exp v * (1 - v) ≤ Real.exp v * Real.exp (-v) :=
          mul_le_mul_of_nonneg_left a1 (Real.exp_pos v).le
      _ = 1 := a2
  nlinarith
theorem abs_expWeight_sq_sub_le {del : ℝ} (hdel : 0 ≤ del) (z : F.Cell) {j j' : ℕ} (x : F.Site j)
    (y : F.Site j') {ρ : ℝ} (h : |torusSupDist x z - torusSupDist y z| ≤ ρ) (hρ : del * ρ ≤ 2) :
    |expWeight del z x ^ 2 - expWeight del z y ^ 2| ≤
      16 * del * ρ * (expWeight del z x * expWeight del z y) := by
  set v := del * (torusSupDist y z - torusSupDist x z) with hv
  have hvb : |v| ≤ del * ρ := by
    rw [hv, abs_mul, abs_of_nonneg hdel, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left h hdel
  have e1 : expWeight del z x = expWeight del z y * Real.exp v := by
    unfold expWeight
    rw [← Real.exp_add, hv]
    congr 1
    ring
  have e2 : expWeight del z y = expWeight del z x * Real.exp (-v) := by
    unfold expWeight
    rw [← Real.exp_add, hv]
    congr 1
    ring
  have e3 : expWeight del z x ^ 2 - expWeight del z y ^ 2 =
      (expWeight del z x * expWeight del z y) * (Real.exp v - Real.exp (-v)) := by
    have : expWeight del z x ^ 2 = (expWeight del z x * expWeight del z y) * Real.exp v := by
      rw [mul_assoc, ← e1]; ring
    have h2 : expWeight del z y ^ 2 = (expWeight del z x * expWeight del z y) * Real.exp (-v) := by
      rw [mul_comm (expWeight del z x), mul_assoc, ← e2]; ring
    rw [this, h2]; ring
  have hp : 0 < expWeight del z x * expWeight del z y := mul_pos (expWeight_pos _ _ _) (expWeight_pos _ _ _)
  have hs : |Real.exp v - Real.exp (-v)| ≤ 16 * |v| := by
    rcases le_total 0 v with hv0 | hv0
    · rw [abs_of_nonneg hv0]
      exact abs_exp_sub_exp_neg_le hv0 (by linarith [le_abs_self v])
    · have := abs_exp_sub_exp_neg_le (v := -v) (by linarith) (by linarith [neg_abs_le v])
      rw [neg_neg, abs_sub_comm] at this
      rwa [abs_of_nonpos hv0]
  rw [e3, abs_mul, abs_of_pos hp]
  calc _ ≤ (expWeight del z x * expWeight del z y) * (16 * (del * ρ)) :=
        mul_le_mul_of_nonneg_left (hs.trans (by linarith)) hp.le
    _ = _ := by ring
def meanCommutator (del : ℝ) (z : F.Cell) {j : ℕ} (X : LevelForm F j) : LevelForm F (j + 1) := fun y i =>
  lineAverage (fun x k => expWeight del z x ^ 2 * X x k) y i - expWeight del z y ^ 2 * lineAverage X y i
theorem weightedNorm_meanCommutator_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j < F.top) {del : ℝ} (hdel : 0 ≤ del) (z : F.Cell) (hρ : del * readRadius F j ≤ 2)
    (hρ0 : 0 ≤ readRadius F j) (X : LevelForm F j) :
    weightedNorm (invWeight del z) (meanCommutator del z X) ≤
      (16 * del * readRadius F j / F.blockSide) * weightedNorm (expWeight del z) X := by
  refine weightedNorm_kernel_average_le hL hs hj
    (fun y x => (expWeight del z x ^ 2 - expWeight del z y ^ 2) * invWeight del z y) (expWeight del z)
    (16 * del * readRadius F j) (by positivity) (fun x => (expWeight_pos _ _ x).le) ?_ X
    (invWeight del z) _ ?_
  · intro y h l i hh hl
    have h1 := abs_expWeight_sq_sub_le hdel z (readSite y h l i) y (readSite_dist hL hs hj y hh hl i z) hρ
    rw [abs_mul, abs_of_pos (invWeight_pos del z y)]
    calc _ ≤ (16 * del * readRadius F j * (expWeight del z (readSite y h l i) * expWeight del z y)) *
          invWeight del z y :=
          mul_le_mul_of_nonneg_right h1 (invWeight_pos del z y).le
      _ = 16 * del * readRadius F j * expWeight del z (readSite y h l i) *
          (expWeight del z y * invWeight del z y) := by ring
      _ = _ := by rw [expWeight_mul_invWeight, mul_one]
  · intro y i
    unfold meanCommutator
    rw [lineAverage_eq, lineAverage_eq]
    have e : ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
        (expWeight del z (readSite y h l i) ^ 2 - expWeight del z y ^ 2) * invWeight del z y *
          X (readSite y h l i) i =
        invWeight del z y * ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide,
          expWeight del z (readSite y h l i) ^ 2 * X (readSite y h l i) i -
        invWeight del z y * expWeight del z y ^ 2 *
          ∑ h ∈ centredCube F.blockSide, ∑ l ∈ Finset.range F.blockSide, X (readSite y h l i) i := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    ring
theorem weightedNorm_lineAverage_expWeight (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j < F.top) {del : ℝ} (hdel : 0 ≤ del) (z : F.Cell) (X : LevelForm F j) :
    weightedNorm (expWeight del z) (lineAverage X) ≤
      (Real.exp (del * readRadius F j) / F.blockSide) * weightedNorm (expWeight del z) X := by
  refine weightedNorm_lineAverage_le hL hs hj _ _ _ (Real.exp_pos _).le (fun x => (expWeight_pos _ _ x).le) ?_ X
  intro y h l i hh hl
  rw [abs_of_pos (expWeight_pos _ _ _)]
  exact expWeight_le_of_dist hdel z _ y (readSite_dist hL hs hj y hh hl i z)
theorem weightedNorm_lineAverage_invWeight (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j < F.top) {del : ℝ} (hdel : 0 ≤ del) (z : F.Cell) (X : LevelForm F j) :
    weightedNorm (invWeight del z) (lineAverage X) ≤
      (Real.exp (del * readRadius F j) / F.blockSide) * weightedNorm (invWeight del z) X := by
  refine weightedNorm_lineAverage_le hL hs hj _ _ _ (Real.exp_pos _).le (fun x => (invWeight_pos _ _ x).le) ?_ X
  intro y h l i hh hl
  rw [abs_of_pos (invWeight_pos _ _ _)]
  exact invWeight_le_of_dist hdel z _ y (readSite_dist hL hs hj y hh hl i z)
theorem lineAverage_add {j : ℕ} (X Y : LevelForm F j) :
    lineAverage (X + Y) = lineAverage X + lineAverage Y := by
  funext y i
  simp only [lineAverage_eq, Pi.add_apply, Finset.sum_add_distrib, mul_add]
theorem unitStep_eq (j : ℕ) (i : Fin 4) : (unitStep j i : F.Site j) = siteOfCoords j (Pi.single i 1) := rfl
theorem lineAverage_gradient {j : ℕ} (hj : j < F.top) (ψ : F.Site j → ℝ)
    (y : F.Site (j + 1)) (i : Fin 4) :
    lineAverage (fun x k => ψ (x + unitStep j k) - ψ x) y i =
      blockAverage ψ (y + unitStep (j + 1) i) - blockAverage ψ y := by
  rw [lineAverage_eq]
  unfold blockAverage
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  have hz : (siteOfCoords j (0 : Fin 4 → ℤ) : F.Site j) = 0 := by funext i; simp [siteOfCoords]
  have hstep : ∀ l : ℕ, readSite y h l i + unitStep j i = readSite y h (l + 1) i := by
    intro l
    unfold readSite
    rw [add_assoc, unitStep_eq, ← siteOfCoords_add]
    congr 2
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  have e : ∑ l ∈ Finset.range F.blockSide, (ψ (readSite y h l i + unitStep j i) - ψ (readSite y h l i)) =
      ψ (readSite y h F.blockSide i) - ψ (readSite y h 0 i) := by
    simp only [hstep]
    exact Finset.sum_range_sub (fun l => ψ (readSite y h l i)) F.blockSide
  rw [e]
  have e0 : readSite y h 0 i = refineSite y + siteOfCoords j h := by
    unfold readSite
    have : (Pi.single i ((0 : ℕ) : ℤ) : Fin 4 → ℤ) = 0 := by simp
    rw [this, hz, add_zero]
  have e1 : readSite y h F.blockSide i = refineSite (y + unitStep (j + 1) i) + siteOfCoords j h := by
    unfold readSite
    rw [unitStep_eq, refineSite_add hj, add_right_comm]
    congr 3
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  rw [e0, e1]
def iteratedBlockAverage (ψ : F.Site 0 → ℝ) : (j : ℕ) → F.Site j → ℝ
  | 0 => ψ
  | j + 1 => blockAverage (iteratedBlockAverage ψ j)
theorem centredCube_one : centredCube 1 = {0} := by apply _root_.YangMills.Construction.TorusChain.centredCube_one <;> assumption
theorem sum_centredCube_mul {M P : ℕ} (hM : Odd M) (hP : Odd P) (g : (Fin 4 → ℤ) → ℝ) :
    ∑ h ∈ centredCube P, ∑ k ∈ centredCube M, g (fun i => (M : ℤ) * h i + k i) =
      ∑ m ∈ centredCube (M * P), g m := by
  obtain ⟨a, ha⟩ := hM
  obtain ⟨b, hb⟩ := hP
  have h1 : ((M : ℤ) - 1) / 2 = a := by rw [ha]; push_cast; omega
  have h2 : ((P : ℤ) - 1) / 2 = b := by rw [hb]; push_cast; omega
  have hMz : (M : ℤ) = 2 * a + 1 := by rw [ha]; push_cast; ring
  have hPz : (P : ℤ) = 2 * b + 1 := by rw [hb]; push_cast; ring
  have h3 : (((M * P : ℕ) : ℤ) - 1) / 2 = 2 * a * b + a + b := by
    push_cast
    rw [hMz, hPz]
    have : (2 * (a : ℤ) + 1) * (2 * b + 1) - 1 = 2 * (2 * a * b + a + b) := by ring
    rw [this]
    simp
  have hOddM : Odd M := ⟨a, ha⟩
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun p i => (M : ℤ) * p.1 i + p.2 i)
    (fun m => (fun i => centredQuot M (m i), fun i => centredRem M (m i))) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
    refine (mem_centredCube_iff _).2 fun i => ?_
    have q1 := (mem_centredCube_iff _).1 hp1 i
    have q2 := (mem_centredCube_iff _).1 hp2 i
    rw [h2] at q1
    rw [h1] at q2
    rw [h3, hMz]
    constructor <;> nlinarith [q1.1, q1.2, q2.1, q2.2]
  · intro m hm
    refine Finset.mem_product.2 ⟨(mem_centredCube_iff _).2 fun i => ?_,
      (mem_centredCube_iff _).2 fun i => centredRem_bounds hOddM _⟩
    have q := (mem_centredCube_iff _).1 hm i
    rw [h3] at q
    have r1 := centredRem_bounds hOddM (m i)
    rw [h1] at r1
    have r2 := centredQuot_add_centredRem M (m i)
    rw [hMz] at r2
    show -(((P : ℤ) - 1) / 2) ≤ centredQuot M (m i) ∧ centredQuot M (m i) ≤ ((P : ℤ) - 1) / 2
    rw [h2]
    have ha0 : (0 : ℤ) ≤ a := by positivity
    have hb0 : (0 : ℤ) ≤ b := by positivity
    constructor
    · by_contra hc
      have : centredQuot M (m i) ≤ -(b : ℤ) - 1 := by omega
      nlinarith [q.1, q.2, r1.1, r1.2]
    · by_contra hc
      have : (b : ℤ) + 1 ≤ centredQuot M (m i) := by omega
      nlinarith [q.1, q.2, r1.1, r1.2]
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
    have key : ∀ i, centredQuot M ((M : ℤ) * p.1 i + p.2 i) = p.1 i ∧
        centredRem M ((M : ℤ) * p.1 i + p.2 i) = p.2 i := by
      intro i
      have q2 := (mem_centredCube_iff _).1 hp2 i
      exact centredQuot_unique hOddM rfl q2.1 q2.2
    exact Prod.ext (funext fun i => (key i).1) (funext fun i => (key i).2)
  · intro m _
    funext i
    exact (centredQuot_add_centredRem M (m i)).symm
theorem iteratedBlockAverage_eq (hL : Odd F.blockSide) (ψ : F.Site 0 → ℝ) (j : ℕ) (hj : j ≤ F.top)
    (y : F.Site j) :
    iteratedBlockAverage ψ j y = (1 / ((F.blockSide : ℝ) ^ j) ^ 4) *
      ∑ m ∈ centredCube (F.blockSide ^ j),
        ψ (siteOfCoords 0 (fun i => ((F.blockSide ^ j : ℕ) : ℤ) * siteCoords y i + m i)) := by
  induction j with
  | zero =>
    simp only [pow_zero, one_pow, div_one, one_mul, centredCube_one, Finset.sum_singleton, Nat.cast_one,
      Pi.zero_apply, add_zero, iteratedBlockAverage]
    congr 1
    exact (siteOfCoords_siteCoords y).symm
  | succ j ih =>
    have hj' : j ≤ F.top := by omega
    have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
    have hper : ∀ i, F.period 0 i = F.blockSide ^ j * F.period j i := by
      intro i
      unfold BlockFrame.period
      have : F.top - 0 = j + (F.top - j) := by omega
      rw [this, pow_add]
      ring
    have e1 : ∀ h : Fin 4 → ℤ, ∀ k : Fin 4 → ℤ,
        (siteOfCoords 0 (fun i => ((F.blockSide ^ j : ℕ) : ℤ) *
            siteCoords (refineSite y + siteOfCoords j h : F.Site j) i + k i) : F.Site 0) =
          siteOfCoords 0 (fun i => ((F.blockSide ^ (j + 1) : ℕ) : ℤ) * siteCoords y i +
            (((F.blockSide ^ j : ℕ) : ℤ) * h i + k i)) := by
      intro h k
      have e2 : (siteOfCoords 0 (fun i => ((F.blockSide ^ j : ℕ) : ℤ) *
            siteCoords (refineSite y + siteOfCoords j h : F.Site j) i + k i) : F.Site 0) =
          siteOfCoords 0 (fun i => ((F.blockSide ^ j : ℕ) : ℤ) *
            siteCoords (refineSite y + siteOfCoords j h : F.Site j) i) + siteOfCoords 0 k := by
        rw [← siteOfCoords_add]; rfl
      have e3 : refineSite y + siteOfCoords j h =
          siteOfCoords j ((fun i => (F.blockSide : ℤ) * siteCoords y i) + h) := by
        rw [siteOfCoords_add]; rfl
      rw [e2, e3, siteOfCoords_scale hper, ← siteOfCoords_add]
      congr 1
      funext i
      simp only [Pi.add_apply]
      push_cast
      ring
    show blockAverage (iteratedBlockAverage ψ j) y = _
    unfold blockAverage
    have e4 : ∀ h ∈ centredCube F.blockSide, iteratedBlockAverage ψ j (refineSite y + siteOfCoords j h) =
        (1 / ((F.blockSide : ℝ) ^ j) ^ 4) * ∑ k ∈ centredCube (F.blockSide ^ j),
          ψ (siteOfCoords 0 (fun i => ((F.blockSide ^ (j + 1) : ℕ) : ℤ) * siteCoords y i +
            (((F.blockSide ^ j : ℕ) : ℤ) * h i + k i))) := by
      intro h _
      rw [ih hj']
      congr 1
      exact Finset.sum_congr rfl fun k _ => by rw [e1]
    rw [Finset.sum_congr rfl e4, ← Finset.mul_sum, pow_succ F.blockSide j]
    have := sum_centredCube_mul (M := F.blockSide ^ j) hL.pow hL
      (fun m => ψ (siteOfCoords 0 (fun i => ((F.blockSide ^ j * F.blockSide : ℕ) : ℤ) * siteCoords y i + m i)))
    rw [this, ← mul_assoc]
    congr 1
    field_simp
    ring
theorem iteratedBlockAverage_top (hL : Odd F.blockSide) (ψ : F.Site 0 → ℝ) (z : F.Cell) :
    iteratedBlockAverage ψ F.top z = cellAverage ψ z := by
  rw [iteratedBlockAverage_eq hL ψ F.top le_rfl z]
  unfold cellAverage cellCentre
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← siteOfCoords_add]
  congr 2
def sqWeighted (del : ℝ) (z : F.Cell) {j : ℕ} (X : LevelForm F j) : LevelForm F j :=
  fun x k => expWeight del z x ^ 2 * X x k
theorem card_orientedPlanes : orientedPlanes.card = 6 := by decide
theorem torusSupDist_neighbour (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) (x : F.Site 0)
    (z : F.Cell) (μ : Fin 4) :
    |torusSupDist (x + unitStep 0 μ) z - torusSupDist x z| ≤ 1 / (F.blockSide : ℝ) ^ (F.top - 0) := by
  have hb : ∀ k, |(((Pi.single μ (1 : ℤ) : Fin 4 → ℤ) k : ℤ) : ℝ)| ≤ 1 := by
    intro k
    by_cases hk : k = μ
    · subst hk; simp
    · simp [hk]
  rw [abs_le]
  constructor
  · have := torusSupDist_le_add hL hs x z _ _ hb
    rw [unitStep_eq]
    linarith
  · have := torusSupDist_add_le hL hs x z _ _ hb
    rw [unitStep_eq]
    linarith
theorem curl_commutator_sq_le (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) {del : ℝ} (hdel : 0 ≤ del)
    (hdel1 : del ≤ 1) (z : F.Cell) (X : LevelForm F 0) (x : F.Site 0) (μ ν : Fin 4) :
    (invWeight del z x * (plaquetteCurl (sqWeighted del z X) x μ ν -
        expWeight del z x ^ 2 * plaquetteCurl X x μ ν)) ^ 2 ≤
      2 * (16 * del / (F.blockSide : ℝ) ^ (F.top - 0)) ^ 2 *
        ((expWeight del z (x + unitStep 0 μ) * X (x + unitStep 0 μ) ν) ^ 2 +
          (expWeight del z (x + unitStep 0 ν) * X (x + unitStep 0 ν) μ) ^ 2) := by
  have hLr : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
  have hN : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ (F.top - 0) := one_le_pow₀ hLr
  set ρ : ℝ := 1 / (F.blockSide : ℝ) ^ (F.top - 0) with hρ
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one (by linarith)]; exact hN
  have hdρ : del * ρ ≤ 2 := by nlinarith
  have key : ∀ μ : Fin 4, |invWeight del z x * (expWeight del z (x + unitStep 0 μ) ^ 2 -
      expWeight del z x ^ 2)| ≤ 16 * del * ρ * expWeight del z (x + unitStep 0 μ) := by
    intro μ
    have h1 := abs_expWeight_sq_sub_le hdel z (x + unitStep 0 μ) x (torusSupDist_neighbour hL hs x z μ) hdρ
    rw [abs_mul, abs_of_pos (invWeight_pos del z x)]
    calc _ ≤ invWeight del z x * (16 * del * ρ * (expWeight del z (x + unitStep 0 μ) * expWeight del z x)) :=
          mul_le_mul_of_nonneg_left h1 (invWeight_pos del z x).le
      _ = 16 * del * ρ * expWeight del z (x + unitStep 0 μ) * (invWeight del z x * expWeight del z x) := by
          ring
      _ = _ := by rw [invWeight_mul_expWeight, mul_one]
  set A1 := invWeight del z x * (expWeight del z (x + unitStep 0 μ) ^ 2 - expWeight del z x ^ 2) with hA1
  set A2 := invWeight del z x * (expWeight del z (x + unitStep 0 ν) ^ 2 - expWeight del z x ^ 2) with hA2
  have e : invWeight del z x * (plaquetteCurl (sqWeighted del z X) x μ ν -
      expWeight del z x ^ 2 * plaquetteCurl X x μ ν) =
      A1 * X (x + unitStep 0 μ) ν - A2 * X (x + unitStep 0 ν) μ := by
    unfold plaquetteCurl sqWeighted
    rw [hA1, hA2]
    ring
  rw [e]
  have k1 : (A1 * X (x + unitStep 0 μ) ν) ^ 2 ≤
      (16 * del * ρ) ^ 2 * (expWeight del z (x + unitStep 0 μ) * X (x + unitStep 0 μ) ν) ^ 2 := by
    have h2 : A1 ^ 2 ≤ (16 * del * ρ * expWeight del z (x + unitStep 0 μ)) ^ 2 :=
      sq_le_sq.2 ((key μ).trans (le_abs_self _))
    have e2 : (16 * del * ρ) ^ 2 * (expWeight del z (x + unitStep 0 μ) * X (x + unitStep 0 μ) ν) ^ 2 =
        (16 * del * ρ * expWeight del z (x + unitStep 0 μ)) ^ 2 * X (x + unitStep 0 μ) ν ^ 2 := by ring
    rw [e2, mul_pow]
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have k2 : (A2 * X (x + unitStep 0 ν) μ) ^ 2 ≤
      (16 * del * ρ) ^ 2 * (expWeight del z (x + unitStep 0 ν) * X (x + unitStep 0 ν) μ) ^ 2 := by
    have h2 : A2 ^ 2 ≤ (16 * del * ρ * expWeight del z (x + unitStep 0 ν)) ^ 2 :=
      sq_le_sq.2 ((key ν).trans (le_abs_self _))
    have e2 : (16 * del * ρ) ^ 2 * (expWeight del z (x + unitStep 0 ν) * X (x + unitStep 0 ν) μ) ^ 2 =
        (16 * del * ρ * expWeight del z (x + unitStep 0 ν)) ^ 2 * X (x + unitStep 0 ν) μ ^ 2 := by ring
    rw [e2, mul_pow]
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have e3 : 16 * del / (F.blockSide : ℝ) ^ (F.top - 0) = 16 * del * ρ := by rw [hρ]; ring
  rw [e3]
  nlinarith [sq_nonneg (A1 * X (x + unitStep 0 μ) ν + A2 * X (x + unitStep 0 ν) μ)]
theorem curl_commutator_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {del : ℝ} (hdel : 0 ≤ del)
    (hdel1 : del ≤ 1) (z : F.Cell) (X : LevelForm F 0) :
    Real.sqrt (∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes,
      (invWeight del z x * (plaquetteCurl (sqWeighted del z X) x e.1 e.2 -
        expWeight del z x ^ 2 * plaquetteCurl X x e.1 e.2)) ^ 2) ≤
    (80 * del / (F.blockSide : ℝ) ^ (F.top - 0)) * weightedNorm (expWeight del z) X := by
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  set K := 16 * del / (F.blockSide : ℝ) ^ (F.top - 0) with hK
  have e80 : 80 * del / (F.blockSide : ℝ) ^ (F.top - 0) = 5 * K := by rw [hK]; ring
  rw [e80]
  refine Real.sqrt_le_iff.2 ⟨mul_nonneg (by positivity) (weightedNorm_nonneg _ _), ?_⟩
  have single : ∀ ν : Fin 4, ∑ x ∈ allSites F 0, (expWeight del z x * X x ν) ^ 2 ≤
      weightedNorm (expWeight del z) X ^ 2 := by
    intro ν
    rw [weightedNorm_sq]
    refine Finset.sum_le_sum fun x _ => ?_
    exact Finset.single_le_sum (f := fun i => (expWeight del z x * X x i) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ ν)
  calc _ ≤ ∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, 2 * K ^ 2 *
        ((expWeight del z (x + unitStep 0 e.1) * X (x + unitStep 0 e.1) e.2) ^ 2 +
          (expWeight del z (x + unitStep 0 e.2) * X (x + unitStep 0 e.2) e.1) ^ 2) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun e _ =>
          curl_commutator_sq_le hL.pos hs hdel hdel1 z X x e.1 e.2
    _ = ∑ e ∈ orientedPlanes, 2 * K ^ 2 * (∑ x ∈ allSites F 0, (expWeight del z x * X x e.2) ^ 2 +
          ∑ x ∈ allSites F 0, (expWeight del z x * X x e.1) ^ 2) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [← Finset.mul_sum, Finset.sum_add_distrib,
          sum_translate hL hs (unitStep 0 e.1) (fun x => (expWeight del z x * X x e.2) ^ 2),
          sum_translate hL hs (unitStep 0 e.2) (fun x => (expWeight del z x * X x e.1) ^ 2)]
    _ ≤ ∑ e ∈ orientedPlanes, 2 * K ^ 2 *
          (weightedNorm (expWeight del z) X ^ 2 + weightedNorm (expWeight del z) X ^ 2) := by
        refine Finset.sum_le_sum fun e _ => ?_
        exact mul_le_mul_of_nonneg_left (add_le_add (single _) (single _)) (by positivity)
    _ = 24 * K ^ 2 * weightedNorm (expWeight del z) X ^ 2 := by
        rw [Finset.sum_const, card_orientedPlanes]
        simp only [nsmul_eq_mul]
        push_cast
        ring
    _ ≤ _ := by
        have : 0 ≤ K ^ 2 * weightedNorm (expWeight del z) X ^ 2 := by positivity
        nlinarith
theorem scale_invariant_growth (hL3 : 3 ≤ F.blockSide) {del : ℝ} (hdel : 0 ≤ del) (hdel1 : del ≤ 1)
    {p c : ℕ → ℝ} {E : ℝ} (hp0 : 0 ≤ p 0) (hE : 0 ≤ E) (hc : ∀ j, j < F.top → c j ≤ E)
    (hstep : ∀ j, j < F.top → p (j + 1) ≤ (Real.exp (del * readRadius F j) / F.blockSide) * p j + c j)
    (j : ℕ) (hj : j ≤ F.top) :
    (F.blockSide : ℝ) ^ j * p j ≤ Real.exp 3 * (p 0 + 3 / 2 * (F.blockSide : ℝ) ^ j * E) := by
  have hLr : (3 : ℝ) ≤ F.blockSide := by exact_mod_cast hL3
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  have hreach : ∀ i, i < F.top →
      readRadius F i = 2 * (F.blockSide : ℝ) ^ (i + 1) / (F.blockSide : ℝ) ^ F.top := by
    intro i hi
    have e : (F.blockSide : ℝ) ^ F.top = (F.blockSide : ℝ) ^ (F.top - i) * (F.blockSide : ℝ) ^ i := by
      rw [← pow_add]; congr 1; omega
    unfold readRadius
    rw [e, pow_succ]
    field_simp
  have hS : ∀ k, k ≤ F.top → ∑ i ∈ Finset.range k, readRadius F i ≤
      3 * (F.blockSide : ℝ) ^ k / (F.blockSide : ℝ) ^ F.top := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Finset.range_zero, Finset.sum_empty, pow_zero]
      positivity
    | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ, hreach k (by omega)]
      refine (add_le_add_left (ih (by omega)) _).trans ?_
      rw [← add_div]
      refine div_le_div_of_nonneg_right ?_ hN.le
      have : (0 : ℝ) < (F.blockSide : ℝ) ^ k := by positivity
      rw [pow_succ]
      nlinarith
  have main : ∀ k, k ≤ F.top → (F.blockSide : ℝ) ^ k * p k ≤
      Real.exp (del * ∑ i ∈ Finset.range k, readRadius F i) *
        (p 0 + 3 / 2 * (F.blockSide : ℝ) ^ k * E) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, mul_zero, Real.exp_zero]
      linarith
    | succ k ih =>
      intro hk
      have hk' : k < F.top := by omega
      have h1 := ih (by omega)
      have h2 := hstep k hk'
      have h3 := hc k hk'
      have hPk : (0 : ℝ) < (F.blockSide : ℝ) ^ k := by positivity
      have hexp : 1 ≤ Real.exp (del * ∑ i ∈ Finset.range (k + 1), readRadius F i) := by
        refine Real.one_le_exp (mul_nonneg hdel (Finset.sum_nonneg fun i _ => ?_))
        unfold readRadius
        positivity
      have e1 : Real.exp (del * ∑ i ∈ Finset.range (k + 1), readRadius F i) =
          Real.exp (del * readRadius F k) * Real.exp (del * ∑ i ∈ Finset.range k, readRadius F i) := by
        rw [Finset.sum_range_succ, ← Real.exp_add]
        congr 1
        ring
      calc (F.blockSide : ℝ) ^ (k + 1) * p (k + 1)
          ≤ (F.blockSide : ℝ) ^ (k + 1) * ((Real.exp (del * readRadius F k) / F.blockSide) * p k + E) :=
            mul_le_mul_of_nonneg_left (h2.trans (by linarith)) (by positivity)
        _ = Real.exp (del * readRadius F k) * ((F.blockSide : ℝ) ^ k * p k) +
              (F.blockSide : ℝ) ^ (k + 1) * E := by
            rw [pow_succ]; field_simp
        _ ≤ Real.exp (del * readRadius F k) * (Real.exp (del * ∑ i ∈ Finset.range k, readRadius F i) *
              (p 0 + 3 / 2 * (F.blockSide : ℝ) ^ k * E)) + (F.blockSide : ℝ) ^ (k + 1) * E := by
            have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (del * readRadius F k)).le
            linarith
        _ = Real.exp (del * ∑ i ∈ Finset.range (k + 1), readRadius F i) *
              (p 0 + 3 / 2 * (F.blockSide : ℝ) ^ k * E) + (F.blockSide : ℝ) ^ (k + 1) * E := by
            rw [e1]; ring
        _ ≤ Real.exp (del * ∑ i ∈ Finset.range (k + 1), readRadius F i) *
              (p 0 + 3 / 2 * (F.blockSide : ℝ) ^ k * E + (F.blockSide : ℝ) ^ (k + 1) * E) := by
            have h4 : 0 ≤ (F.blockSide : ℝ) ^ (k + 1) * E := by positivity
            nlinarith
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            have h5 : 3 / 2 * (F.blockSide : ℝ) ^ k * E + (F.blockSide : ℝ) ^ (k + 1) * E ≤
                3 / 2 * (F.blockSide : ℝ) ^ (k + 1) * E := by
              have : 3 * (F.blockSide : ℝ) ^ k ≤ (F.blockSide : ℝ) ^ (k + 1) := by
                rw [pow_succ]; nlinarith
              nlinarith
            linarith
  have hbig : Real.exp (del * ∑ i ∈ Finset.range j, readRadius F i) ≤ Real.exp 3 := by
    refine Real.exp_le_exp.2 ?_
    have h1 := hS j hj
    have h2 : 3 * (F.blockSide : ℝ) ^ j / (F.blockSide : ℝ) ^ F.top ≤ 3 := by
      rw [div_le_iff₀ hN]
      have : (F.blockSide : ℝ) ^ j ≤ (F.blockSide : ℝ) ^ F.top := pow_le_pow_right₀ (by linarith) hj
      linarith
    have h3 : 0 ≤ ∑ i ∈ Finset.range j, readRadius F i := Finset.sum_nonneg fun i _ => by
      unfold readRadius
      positivity
    nlinarith
  refine (main j hj).trans (mul_le_mul_of_nonneg_right hbig ?_)
  positivity
theorem absorb_linear {s w β A : ℝ} (hs : 0 ≤ s) (hw : 0 ≤ w) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2) (hA : 0 ≤ A)
    (h : s ^ 2 ≤ β * s * (s + w) + A * s * w) : s ≤ (1 + 2 * A) * w := by
  rcases hs.eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · have h1 : s * s ≤ s * (β * (s + w) + A * w) := by nlinarith
    have h2 : s ≤ β * (s + w) + A * w := le_of_mul_le_mul_left h1 h0
    nlinarith
def weightedCurl (del : ℝ) (z : F.Cell) (B : FormChain F) : ℝ :=
  Real.sqrt (∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, (expWeight del z x * plaquetteCurl (B 0) x e.1 e.2) ^ 2)
def weightedEnergy (a del : ℝ) (z : F.Cell) (B : FormChain F) : ℝ :=
  weightedCurl del z B ^ 2 +
    a * ∑ j ∈ Finset.range F.top, weightedNorm (expWeight del z) (chainMisfit B j) ^ 2
def testForm (del : ℝ) (z : F.Cell) (B G : FormChain F) : (j : ℕ) → LevelForm F j
  | 0 => sqWeighted del z (G 0)
  | j + 1 => fun y i => lineAverage (testForm del z B G j) y i - expWeight del z y ^ 2 * chainMisfit B j y i
def testChain (del : ℝ) (z : F.Cell) (B G : FormChain F) : FormChain F :=
  fun j => if j = F.top then 0 else testForm del z B G j
theorem testChain_top (del : ℝ) (z : F.Cell) (B G : FormChain F) : testChain del z B G F.top = 0 := by
  simp [testChain]
theorem testChain_of_ne (del : ℝ) (z : F.Cell) (B G : FormChain F) {j : ℕ} (hj : j ≠ F.top) :
    testChain del z B G j = testForm del z B G j := by
  simp [testChain, hj]
theorem misfit_testChain_low (del : ℝ) (z : F.Cell) (B G : FormChain F) {j : ℕ} (hj : j + 1 < F.top)
    (y : F.Site (j + 1)) (i : Fin 4) :
    chainMisfit (testChain del z B G) j y i = expWeight del z y ^ 2 * chainMisfit B j y i := by
  show lineAverage (testChain del z B G j) y i - testChain del z B G (j + 1) y i = _
  rw [testChain_of_ne del z B G (j := j) (by omega), testChain_of_ne del z B G hj.ne]
  show lineAverage (testForm del z B G j) y i -
    (lineAverage (testForm del z B G j) y i - expWeight del z y ^ 2 * chainMisfit B j y i) = _
  ring
theorem misfit_testChain_top (del : ℝ) (z : F.Cell) (B G : FormChain F) (y : F.Site F.top) (i : Fin 4) :
    chainMisfit (testChain del z B G) F.depth y i =
      testForm del z B G F.top y i + expWeight del z y ^ 2 * chainMisfit B F.depth y i := by
  show lineAverage (testChain del z B G F.depth) y i - testChain del z B G (F.depth + 1) y i = _
  have h1 : testChain del z B G (F.depth + 1) = 0 := testChain_top del z B G
  rw [testChain_of_ne del z B G (j := F.depth) (by simp), h1]
  show lineAverage (testForm del z B G F.depth) y i - 0 =
    (lineAverage (testForm del z B G F.depth) y i - expWeight del z y ^ 2 * chainMisfit B F.depth y i) +
      expWeight del z y ^ 2 * chainMisfit B F.depth y i
  ring
theorem pairing_sqWeighted (del : ℝ) (z : F.Cell) {j : ℕ} (X : LevelForm F j) :
    ∑ y ∈ allSites F j, ∑ i : Fin 4, X y i * (expWeight del z y ^ 2 * X y i) =
      weightedNorm (expWeight del z) X ^ 2 := by
  rw [weightedNorm_sq]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
theorem chainEnergyPolar_testChain (a del : ℝ) (z : F.Cell) (B G : FormChain F) :
    chainEnergyPolar a B (testChain del z B G) =
      (∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes,
        plaquetteCurl (B 0) x e.1 e.2 * plaquetteCurl (sqWeighted del z (G 0)) x e.1 e.2) +
      a * ∑ j ∈ Finset.range F.top, weightedNorm (expWeight del z) (chainMisfit B j) ^ 2 +
      a * ∑ y ∈ allSites F F.top, ∑ i : Fin 4, chainMisfit B F.depth y i * testForm del z B G F.top y i := by
  unfold chainEnergyPolar
  have h0 : testChain del z B G 0 = sqWeighted del z (G 0) := testChain_of_ne del z B G (by simp)
  rw [h0]
  have hlow : ∀ j ∈ Finset.range F.depth, ∑ y ∈ sitesOfCells (finiteCells F) (j + 1), ∑ i : Fin 4,
      chainMisfit B j y i * chainMisfit (testChain del z B G) j y i =
        weightedNorm (expWeight del z) (chainMisfit B j) ^ 2 := by
    intro j hj
    rw [← pairing_sqWeighted del z]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
    rw [misfit_testChain_low del z B G (by have := Finset.mem_range.1 hj; simp only [BlockFrame.top]; omega)]
  have htop : ∑ y ∈ sitesOfCells (finiteCells F) (F.depth + 1), ∑ i : Fin 4,
      chainMisfit B F.depth y i * chainMisfit (testChain del z B G) F.depth y i =
      weightedNorm (expWeight del z) (chainMisfit B F.depth) ^ 2 +
        ∑ y ∈ allSites F F.top, ∑ i : Fin 4, chainMisfit B F.depth y i * testForm del z B G F.top y i := by
    rw [← pairing_sqWeighted del z, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [misfit_testChain_top del z B G y i]
    ring
  have e1 : ∑ j ∈ Finset.range F.top, ∑ y ∈ sitesOfCells (finiteCells F) (j + 1), ∑ i : Fin 4,
      chainMisfit B j y i * chainMisfit (testChain del z B G) j y i =
      ∑ j ∈ Finset.range F.top, weightedNorm (expWeight del z) (chainMisfit B j) ^ 2 +
        ∑ y ∈ allSites F F.top, ∑ i : Fin 4, chainMisfit B F.depth y i * testForm del z B G F.top y i := by
    rw [show Finset.range F.top = Finset.range (F.depth + 1) from rfl, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_congr rfl hlow, htop]
    ring
  rw [e1]
  ring
def gaugeChain (B : FormChain F) (ψ : F.Site 0 → ℝ) : FormChain F :=
  fun j => addGradient (B j) (iteratedBlockAverage ψ j)
theorem gaugeChain_succ (B : FormChain F) (ψ : F.Site 0 → ℝ) {j : ℕ} (hj : j < F.top) :
    gaugeChain B ψ (j + 1) = lineAverage (gaugeChain B ψ j) - chainMisfit B j := by
  funext y i
  have hG : gaugeChain B ψ j = B j + fun x k =>
      iteratedBlockAverage ψ j (x + unitStep j k) - iteratedBlockAverage ψ j x := rfl
  rw [hG, lineAverage_add]
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [lineAverage_gradient hj]
  show B (j + 1) y i + (blockAverage (iteratedBlockAverage ψ j) (y + unitStep (j + 1) i) -
      blockAverage (iteratedBlockAverage ψ j) y) =
    lineAverage (B j) y i + (blockAverage (iteratedBlockAverage ψ j) (y + unitStep (j + 1) i) -
      blockAverage (iteratedBlockAverage ψ j) y) - (lineAverage (B j) y i - B (j + 1) y i)
  ring
theorem plaquetteCurl_addGradient (B : LevelForm F 0) (ψ : F.Site 0 → ℝ) (x : F.Site 0) (μ ν : Fin 4) :
    plaquetteCurl (addGradient B ψ) x μ ν = plaquetteCurl B x μ ν := by
  unfold plaquetteCurl addGradient
  rw [add_right_comm x (unitStep 0 μ) (unitStep 0 ν)]
  ring
theorem gaugeChain_top (hL : Odd F.blockSide) (B : FormChain F) (ψ : F.Site 0 → ℝ)
    (hψ : ∀ v, cellAverage ψ v = 0) : gaugeChain B ψ F.top = B F.top := by
  funext y i
  show B F.top y i + (iteratedBlockAverage ψ F.top (y + unitStep F.top i) -
    iteratedBlockAverage ψ F.top y) = B F.top y i
  rw [iteratedBlockAverage_top hL, iteratedBlockAverage_top hL, hψ, hψ]
  ring
theorem iterated_sub_succ (B : FormChain F) (j : ℕ) :
    iteratedLineAverage (B 0) (j + 1) - B (j + 1) =
      lineAverage (iteratedLineAverage (B 0) j - B j) + chainMisfit B j := by
  have e : iteratedLineAverage (B 0) j = (iteratedLineAverage (B 0) j - B j) + B j := by
    rw [sub_add_cancel]
  have e1 : iteratedLineAverage (B 0) (j + 1) =
      lineAverage (iteratedLineAverage (B 0) j - B j) + lineAverage (B j) := by
    rw [← lineAverage_add, ← e]
    rfl
  rw [e1]
  funext y i
  simp only [Pi.sub_apply, Pi.add_apply]
  unfold chainMisfit
  ring
theorem testForm_sub_succ (del : ℝ) (z : F.Cell) (B G : FormChain F) {j : ℕ}
    (hG : G (j + 1) = lineAverage (G j) - chainMisfit B j) :
    testForm del z B G (j + 1) - sqWeighted del z (G (j + 1)) =
      lineAverage (testForm del z B G j - sqWeighted del z (G j)) + meanCommutator del z (G j) := by
  have e : testForm del z B G j = (testForm del z B G j - sqWeighted del z (G j)) + sqWeighted del z (G j) := by
    rw [sub_add_cancel]
  have e1 : lineAverage (testForm del z B G j) =
      lineAverage (testForm del z B G j - sqWeighted del z (G j)) + lineAverage (sqWeighted del z (G j)) := by
    rw [← lineAverage_add, ← e]
  funext y i
  have e2 := congrFun (congrFun e1 y) i
  simp only [Pi.add_apply] at e2
  show lineAverage (testForm del z B G j) y i - expWeight del z y ^ 2 * chainMisfit B j y i -
      expWeight del z y ^ 2 * G (j + 1) y i =
    lineAverage (testForm del z B G j - sqWeighted del z (G j)) y i +
      (lineAverage (sqWeighted del z (G j)) y i - expWeight del z y ^ 2 * lineAverage (G j) y i)
  rw [e2, hG]
  simp only [Pi.sub_apply]
  ring
theorem weightedNorm_zero {j : ℕ} (u : F.Site j → ℝ) : weightedNorm u (0 : LevelForm F j) = 0 := by
  unfold weightedNorm
  simp
theorem weightedNorm_neg {j : ℕ} (u : F.Site j → ℝ) (X : LevelForm F j) :
    weightedNorm u (-X) = weightedNorm u X := by
  unfold weightedNorm
  simp
theorem weightedNorm_single {u : F.Site F.top → ℝ} (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (c : F.Site F.top × Fin 4) (v : ℝ) (X : LevelForm F F.top)
    (hX : ∀ y i, X y i = if (y, i) = c then v else 0) :
    weightedNorm u X = |u c.1 * v| := by
  unfold weightedNorm
  rw [← Real.sqrt_sq_eq_abs]
  congr 1
  rw [Finset.sum_eq_single c.1]
  · rw [Finset.sum_eq_single c.2]
    · rw [hX]
      simp
    · intro i _ hi
      rw [hX, if_neg]
      · simp
      · intro h
        exact hi (by rw [← h])
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro y _ hy
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hX, if_neg]
    · simp
    · intro h
      exact hy (by rw [← h])
  · intro h
    exact absurd (mem_sitesOfCells_finite hL hs _) h
theorem le_of_sq_le_sq_of_nonneg {x y : ℝ} (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  by_contra hc
  push_neg at hc
  nlinarith
theorem weightedEnergy_nonneg {a : ℝ} (ha : 0 ≤ a) (del : ℝ) (z : F.Cell) (B : FormChain F) :
    0 ≤ weightedEnergy a del z B :=
  add_nonneg (sq_nonneg _) (mul_nonneg ha (Finset.sum_nonneg fun _ _ => sq_nonneg _))
theorem weightedCurl_le {a : ℝ} (ha : 0 ≤ a) (del : ℝ) (z : F.Cell) (B : FormChain F) :
    weightedCurl del z B ≤ Real.sqrt (weightedEnergy a del z B) := by
  refine Real.le_sqrt_of_sq_le ?_
  exact le_add_of_nonneg_right (mul_nonneg ha (Finset.sum_nonneg fun _ _ => sq_nonneg _))
theorem misfit_sq_le {a : ℝ} (ha : 0 ≤ a) (del : ℝ) (z : F.Cell) (B : FormChain F) {j : ℕ}
    (hj : j < F.top) :
    a * weightedNorm (expWeight del z) (chainMisfit B j) ^ 2 ≤ Real.sqrt (weightedEnergy a del z B) ^ 2 := by
  rw [Real.sq_sqrt (weightedEnergy_nonneg ha del z B)]
  have h1 : weightedNorm (expWeight del z) (chainMisfit B j) ^ 2 ≤
      ∑ j ∈ Finset.range F.top, weightedNorm (expWeight del z) (chainMisfit B j) ^ 2 :=
    Finset.single_le_sum (f := fun j => weightedNorm (expWeight del z) (chainMisfit B j) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_range.2 hj)
  have h2 := mul_le_mul_of_nonneg_left h1 ha
  unfold weightedEnergy
  exact h2.trans (le_add_of_nonneg_left (sq_nonneg _))
theorem misfit_le {a : ℝ} (ha : 1 ≤ a) (del : ℝ) (z : F.Cell) (B : FormChain F) {j : ℕ} (hj : j < F.top) :
    weightedNorm (expWeight del z) (chainMisfit B j) ≤ Real.sqrt (weightedEnergy a del z B) :=
  le_of_sq_le_sq_of_nonneg (Real.sqrt_nonneg _) ((le_mul_of_one_le_left (sq_nonneg _) ha).trans
    (misfit_sq_le (by linarith) del z B hj))
theorem misfit_last_le {a : ℝ} (ha : 0 ≤ a) (del : ℝ) (z : F.Cell) (B : FormChain F) :
    a * weightedNorm (expWeight del z) (chainMisfit B F.depth) ≤
      Real.sqrt a * Real.sqrt (weightedEnergy a del z B) := by
  have hsa2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have h1 : Real.sqrt a * weightedNorm (expWeight del z) (chainMisfit B F.depth) ≤
      Real.sqrt (weightedEnergy a del z B) := by
    refine le_of_sq_le_sq_of_nonneg (Real.sqrt_nonneg _) ?_
    rw [mul_pow, hsa2]
    exact misfit_sq_le ha del z B (by simp)
  calc a * weightedNorm (expWeight del z) (chainMisfit B F.depth)
      = Real.sqrt a * (Real.sqrt a * weightedNorm (expWeight del z) (chainMisfit B F.depth)) := by
        rw [← mul_assoc, ← sq, hsa2]
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
theorem iteratedLineAverage_le {del s : ℝ} (hL : Odd F.blockSide) (hL3 : 3 ≤ F.blockSide)
    (hs : ∀ i, 0 < F.extent i) (hdel : 0 ≤ del) (hdel1 : del ≤ 1) (z : F.Cell) (B : FormChain F)
    (hs0 : 0 ≤ s) (hfs : ∀ j, j < F.top → weightedNorm (expWeight del z) (chainMisfit B j) ≤ s) :
    weightedNorm (expWeight del z) (iteratedLineAverage (B 0) F.top) ≤
      3 / 2 * Real.exp 3 * s + weightedNorm (expWeight del z) (B F.top) := by
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  have h := scale_invariant_growth (p := fun j => weightedNorm (expWeight del z) (iteratedLineAverage (B 0) j - B j))
    (c := fun j => weightedNorm (expWeight del z) (chainMisfit B j)) (E := s) hL3 hdel hdel1
    (weightedNorm_nonneg _ _) hs0 hfs
    (fun j hj => by
      show weightedNorm (expWeight del z) (iteratedLineAverage (B 0) (j + 1) - B (j + 1)) ≤ _
      rw [iterated_sub_succ]
      exact (weightedNorm_add_le _ _ _).trans
        (add_le_add (weightedNorm_lineAverage_expWeight hL hs hj hdel z _) le_rfl)) F.top le_rfl
  have h0 : weightedNorm (expWeight del z) (iteratedLineAverage (B 0) 0 - B 0) = 0 := by
    have : iteratedLineAverage (B 0) 0 - B 0 = 0 := sub_self _
    rw [this, weightedNorm_zero]
  simp only [h0, zero_add] at h
  have h1 : (F.blockSide : ℝ) ^ F.top * weightedNorm (expWeight del z) (iteratedLineAverage (B 0) F.top - B F.top) ≤
      (F.blockSide : ℝ) ^ F.top * (3 / 2 * Real.exp 3 * s) := by
    refine h.trans (le_of_eq ?_)
    ring
  have h2 := le_of_mul_le_mul_left h1 hN
  have e : iteratedLineAverage (B 0) F.top = (iteratedLineAverage (B 0) F.top - B F.top) + B F.top := by
    rw [sub_add_cancel]
  rw [e]
  exact (weightedNorm_add_le _ _ _).trans (add_le_add h2 le_rfl)
theorem meanCommutator_le {del s Y0 : ℝ} (hL : Odd F.blockSide) (hL3 : 3 ≤ F.blockSide)
    (hs : ∀ i, 0 < F.extent i) (hdel : 0 ≤ del) (hdel1 : del ≤ 1) (z : F.Cell) (B G : FormChain F)
    (hs0 : 0 ≤ s) (hY0 : 0 ≤ Y0)
    (hfs : ∀ j, j < F.top → weightedNorm (expWeight del z) (chainMisfit B j) ≤ s)
    (hG : ∀ j, j < F.top → G (j + 1) = lineAverage (G j) - chainMisfit B j)
    (hb0 : weightedNorm (expWeight del z) (G 0) ≤ (F.blockSide : ℝ) ^ F.top * Y0) {j : ℕ} (hj : j < F.top) :
    weightedNorm (invWeight del z) (meanCommutator del z (G j)) ≤ 32 * del * Real.exp 3 * (Y0 + 3 / 2 * s) := by
  have hLr : (3 : ℝ) ≤ F.blockSide := by exact_mod_cast hL3
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  have hΛ : (0 : ℝ) < Real.exp 3 := Real.exp_pos _
  have hb : (F.blockSide : ℝ) ^ j * weightedNorm (expWeight del z) (G j) ≤
      Real.exp 3 * (weightedNorm (expWeight del z) (G 0) + 3 / 2 * (F.blockSide : ℝ) ^ j * s) := by
    refine scale_invariant_growth (p := fun j => weightedNorm (expWeight del z) (G j))
      (c := fun j => weightedNorm (expWeight del z) (chainMisfit B j)) (E := s) hL3 hdel hdel1
      (weightedNorm_nonneg _ _) hs0 hfs (fun j hj => ?_) j hj.le
    show weightedNorm (expWeight del z) (G (j + 1)) ≤ _
    rw [hG j hj, sub_eq_add_neg]
    refine (weightedNorm_add_le _ _ _).trans
      (add_le_add (weightedNorm_lineAverage_expWeight hL hs hj hdel z _) ?_)
    rw [weightedNorm_neg]
  have hbY : (F.blockSide : ℝ) ^ j * weightedNorm (expWeight del z) (G j) ≤
      Real.exp 3 * ((F.blockSide : ℝ) ^ F.top * (Y0 + 3 / 2 * s)) := by
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hΛ.le)
    have : (F.blockSide : ℝ) ^ j ≤ (F.blockSide : ℝ) ^ F.top := pow_le_pow_right₀ (by linarith) hj.le
    rw [mul_add]
    refine add_le_add hb0 ?_
    nlinarith
  have hr : readRadius F j = 2 * (F.blockSide : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) := rfl
  have hM : (0 : ℝ) < (F.blockSide : ℝ) ^ (F.top - j) := by positivity
  have hM1 : (F.blockSide : ℝ) ≤ (F.blockSide : ℝ) ^ (F.top - j) := by
    have : (F.blockSide : ℝ) ^ 1 ≤ (F.blockSide : ℝ) ^ (F.top - j) := pow_le_pow_right₀ (by linarith) (by omega)
    simpa using this
  have hr0 : 0 ≤ readRadius F j := by rw [hr]; positivity
  have hr2 : readRadius F j ≤ 2 := by
    rw [hr, div_le_iff₀ hM]
    nlinarith
  have h1 := weightedNorm_meanCommutator_le hL hs hj hdel z (by nlinarith) hr0 (G j)
  refine h1.trans ?_
  have e : (F.blockSide : ℝ) ^ F.top = (F.blockSide : ℝ) ^ (F.top - j) * (F.blockSide : ℝ) ^ j := by
    rw [← pow_add]; congr 1; omega
  have e2 : 16 * del * readRadius F j / F.blockSide * weightedNorm (expWeight del z) (G j) =
      32 * del * ((F.blockSide : ℝ) ^ j * weightedNorm (expWeight del z) (G j)) / (F.blockSide : ℝ) ^ F.top := by
    rw [hr, e]
    field_simp
    ring
  rw [e2, div_le_iff₀ hN]
  have h3 : 32 * del * ((F.blockSide : ℝ) ^ j * weightedNorm (expWeight del z) (G j)) ≤
      32 * del * (Real.exp 3 * ((F.blockSide : ℝ) ^ F.top * (Y0 + 3 / 2 * s))) :=
    mul_le_mul_of_nonneg_left hbY (by positivity)
  refine h3.trans (le_of_eq ?_)
  ring
theorem testForm_defect_le {del E : ℝ} (hL : Odd F.blockSide) (hL3 : 3 ≤ F.blockSide)
    (hs : ∀ i, 0 < F.extent i) (hdel : 0 ≤ del) (hdel1 : del ≤ 1) (z : F.Cell) (B G : FormChain F)
    (hE : 0 ≤ E) (hG : ∀ j, j < F.top → G (j + 1) = lineAverage (G j) - chainMisfit B j)
    (hc : ∀ j, j < F.top → weightedNorm (invWeight del z) (meanCommutator del z (G j)) ≤ E) :
    weightedNorm (invWeight del z) (testForm del z B G F.top - sqWeighted del z (G F.top)) ≤
      3 / 2 * Real.exp 3 * E := by
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  have h := scale_invariant_growth
    (p := fun j => weightedNorm (invWeight del z) (testForm del z B G j - sqWeighted del z (G j)))
    (c := fun j => weightedNorm (invWeight del z) (meanCommutator del z (G j))) (E := E) hL3 hdel hdel1
    (weightedNorm_nonneg _ _) hE hc
    (fun j hj => by
      show weightedNorm (invWeight del z) (testForm del z B G (j + 1) - sqWeighted del z (G (j + 1))) ≤ _
      rw [testForm_sub_succ del z B G (hG j hj)]
      exact (weightedNorm_add_le _ _ _).trans
        (add_le_add (weightedNorm_lineAverage_invWeight hL hs hj hdel z _) le_rfl)) F.top le_rfl
  have h0 : weightedNorm (invWeight del z) (testForm del z B G 0 - sqWeighted del z (G 0)) = 0 := by
    have : testForm del z B G 0 - sqWeighted del z (G 0) = 0 := sub_self _
    rw [this, weightedNorm_zero]
  simp only [h0, zero_add] at h
  have h1 : (F.blockSide : ℝ) ^ F.top *
      weightedNorm (invWeight del z) (testForm del z B G F.top - sqWeighted del z (G F.top)) ≤
      (F.blockSide : ℝ) ^ F.top * (3 / 2 * Real.exp 3 * E) := by
    refine h.trans (le_of_eq ?_)
    ring
  exact le_of_mul_le_mul_left h1 hN
theorem curl_pairing_le {del s Y : ℝ} (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (hdel : 0 ≤ del) (hdel1 : del ≤ 1) (z : F.Cell) (B G : FormChain F) (hs0 : 0 ≤ s)
    (hDs : weightedCurl del z B ≤ s)
    (hb0 : weightedNorm (expWeight del z) (G 0) ≤ (F.blockSide : ℝ) ^ F.top * Y) :
    |∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, plaquetteCurl (B 0) x e.1 e.2 *
      (plaquetteCurl (sqWeighted del z (G 0)) x e.1 e.2 - expWeight del z x ^ 2 * plaquetteCurl (G 0) x e.1 e.2)| ≤
    s * (80 * del * Y) := by
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  have h1 := abs_double_sum_mul_le (allSites F 0) orientedPlanes
    (fun x e => expWeight del z x * plaquetteCurl (B 0) x e.1 e.2)
    (fun x e => invWeight del z x * (plaquetteCurl (sqWeighted del z (G 0)) x e.1 e.2 -
      expWeight del z x ^ 2 * plaquetteCurl (G 0) x e.1 e.2))
  have e : ∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, (expWeight del z x * plaquetteCurl (B 0) x e.1 e.2) *
      (invWeight del z x * (plaquetteCurl (sqWeighted del z (G 0)) x e.1 e.2 -
        expWeight del z x ^ 2 * plaquetteCurl (G 0) x e.1 e.2)) =
      ∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, plaquetteCurl (B 0) x e.1 e.2 *
      (plaquetteCurl (sqWeighted del z (G 0)) x e.1 e.2 - expWeight del z x ^ 2 * plaquetteCurl (G 0) x e.1 e.2) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun e _ => ?_
    calc _ = (expWeight del z x * invWeight del z x) * (plaquetteCurl (B 0) x e.1 e.2 *
          (plaquetteCurl (sqWeighted del z (G 0)) x e.1 e.2 -
            expWeight del z x ^ 2 * plaquetteCurl (G 0) x e.1 e.2)) := by ring
      _ = _ := by rw [expWeight_mul_invWeight, one_mul]
  rw [e] at h1
  have h2 := curl_commutator_le hL hs hdel hdel1 z (G 0)
  have hN0 : (F.blockSide : ℝ) ^ (F.top - 0) = (F.blockSide : ℝ) ^ F.top := by simp
  rw [hN0] at h2
  have h3 : 80 * del / (F.blockSide : ℝ) ^ F.top * weightedNorm (expWeight del z) (G 0) ≤ 80 * del * Y := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hN]
    have := mul_le_mul_of_nonneg_left hb0 (by positivity : 0 ≤ 80 * del)
    refine this.trans (le_of_eq ?_)
    ring
  refine h1.trans ?_
  exact mul_le_mul hDs (h2.trans h3) (Real.sqrt_nonneg _) hs0
theorem weightedNorm_sqWeighted_top (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (del : ℝ)
    (z : F.Cell) (c : F.Site F.top × Fin 4) :
    weightedNorm (invWeight del z) (sqWeighted del z (topBondIndicator c)) = expWeight del z c.1 := by
  rw [weightedNorm_single hL hs c (expWeight del z c.1 ^ 2) _ (fun y i => ?_)]
  · have : invWeight del z c.1 * expWeight del z c.1 ^ 2 = expWeight del z c.1 := by
      rw [sq, ← mul_assoc, invWeight_mul_expWeight, one_mul]
    rw [this, abs_of_pos (expWeight_pos _ _ _)]
  · unfold sqWeighted topBondIndicator
    by_cases h : (y, i) = c
    · rw [if_pos h, if_pos h, ← h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
theorem energy_arith {s wc sa a del C₇ Λ D Rm P ft Y Y0 S : ℝ} (hs0 : 0 ≤ s) (hwc0 : 0 ≤ wc)
    (hsa : 0 ≤ sa) (ha0 : 0 ≤ a) (hdel : 0 ≤ del) (hC : 0 ≤ C₇) (hΛ : 1 ≤ Λ) (hs2 : s ^ 2 = D ^ 2 + a * S)
    (hpol : D ^ 2 + Rm + a * S + a * P = 0) (hRmb : |Rm| ≤ s * (80 * del * Y))
    (hmE : |P| ≤ ft * (wc + 3 / 2 * Λ * (32 * del * Λ * Y))) (hfa2 : a * ft ≤ sa * s)
    (hY : Y = Y0 + 3 / 2 * s) (hY0 : Y0 = C₇ * (s + (3 / 2 * Λ * s + wc))) (hft : 0 ≤ ft) :
    s ^ 2 ≤ del * (C₇ * (1 + 3 / 2 * Λ) + 3 / 2) * (80 + 48 * Λ ^ 2 * sa) * s * (s + wc) + sa * s * wc := by
  have hK : Y ≤ (C₇ * (1 + 3 / 2 * Λ) + 3 / 2) * (s + wc) := by
    rw [hY, hY0]
    have h1 : 0 ≤ C₇ * (3 / 2 * Λ) * wc := by positivity
    have h2 : 0 ≤ 3 / 2 * wc := by positivity
    nlinarith
  have hY00 : 0 ≤ Y := by rw [hY, hY0]; positivity
  have h1 : s ^ 2 = -Rm - a * P := by linarith
  have h2 : -Rm ≤ s * (80 * del * Y) := by linarith [neg_abs_le Rm, neg_le_abs Rm]
  have h3 : -(a * P) ≤ sa * s * (wc + 48 * Λ ^ 2 * del * Y) := by
    have h4 : -P ≤ ft * (wc + 48 * Λ ^ 2 * del * Y) := by
      have e : 3 / 2 * Λ * (32 * del * Λ * Y) = 48 * Λ ^ 2 * del * Y := by ring
      rw [e] at hmE
      linarith [neg_le_abs P]
    have h5 : 0 ≤ wc + 48 * Λ ^ 2 * del * Y := by positivity
    calc -(a * P) = a * (-P) := by ring
      _ ≤ a * (ft * (wc + 48 * Λ ^ 2 * del * Y)) := mul_le_mul_of_nonneg_left h4 ha0
      _ = (a * ft) * (wc + 48 * Λ ^ 2 * del * Y) := by ring
      _ ≤ (sa * s) * (wc + 48 * Λ ^ 2 * del * Y) := mul_le_mul_of_nonneg_right hfa2 h5
  have hKb : s * (80 * del * Y) + sa * s * (48 * Λ ^ 2 * del * Y) ≤
      del * (C₇ * (1 + 3 / 2 * Λ) + 3 / 2) * (80 + 48 * Λ ^ 2 * sa) * s * (s + wc) := by
    have e : s * (80 * del * Y) + sa * s * (48 * Λ ^ 2 * del * Y) =
        (del * (80 + 48 * Λ ^ 2 * sa) * s) * Y := by ring
    have e2 : del * (C₇ * (1 + 3 / 2 * Λ) + 3 / 2) * (80 + 48 * Λ ^ 2 * sa) * s * (s + wc) =
        (del * (80 + 48 * Λ ^ 2 * sa) * s) * ((C₇ * (1 + 3 / 2 * Λ) + 3 / 2) * (s + wc)) := by ring
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left hK (by positivity)
  have e3 : sa * s * (wc + 48 * Λ ^ 2 * del * Y) = sa * s * wc + sa * s * (48 * Λ ^ 2 * del * Y) := by ring
  rw [e3] at h3
  linarith
theorem energy_sq_le {a del C₇ : ℝ} (hL : Odd F.blockSide) (hL3 : 3 ≤ F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (ha : 1 ≤ a) (hdel0 : 0 < del) (hdel1 : del ≤ 1) (hC : 0 ≤ C₇) (c : F.Site F.top × Fin 4)
    (B : FormChain F) (hB : IsFlatChain a c B) (z : F.Cell) (φ : F.Site 0 → ℝ)
    (hmean : ∀ v, cellAverage φ v = 0)
    (h7 : weightedNorm (expWeight del z) (addGradient (B 0) (fun y => - φ y)) ≤
      C₇ * (F.blockSide : ℝ) ^ F.top *
        (weightedCurl del z B + weightedNorm (expWeight del z) (iteratedLineAverage (B 0) F.top))) :
    Real.sqrt (weightedEnergy a del z B) ^ 2 ≤
      del * (C₇ * (1 + 3 / 2 * Real.exp 3) + 3 / 2) * (80 + 48 * Real.exp 3 ^ 2 * Real.sqrt a) *
        Real.sqrt (weightedEnergy a del z B) * (Real.sqrt (weightedEnergy a del z B) + expWeight del z c.1) +
      Real.sqrt a * Real.sqrt (weightedEnergy a del z B) * expWeight del z c.1 := by
  have hdel : 0 ≤ del := hdel0.le
  have ha0 : 0 ≤ a := by linarith
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  have hΛ : (1 : ℝ) ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  have hψ : ∀ v, cellAverage (fun y => - φ y) v = 0 := by
    intro v
    have := hmean v
    unfold cellAverage at this ⊢
    rw [Finset.sum_neg_distrib, mul_neg, this, neg_zero]
  obtain ⟨G, hGdef⟩ : ∃ G, G = gaugeChain B (fun y => - φ y) := ⟨_, rfl⟩
  have hG : ∀ j, j < F.top → G (j + 1) = lineAverage (G j) - chainMisfit B j := by
    intro j hj
    rw [hGdef]
    exact gaugeChain_succ B _ hj
  have hGtop : G F.top = topBondIndicator c := by
    rw [hGdef, gaugeChain_top hL B _ hψ, hB.top_eq]
  have hG0 : G 0 = addGradient (B 0) (fun y => - φ y) := by rw [hGdef]; rfl
  have hcurl : ∀ x μ ν, plaquetteCurl (G 0) x μ ν = plaquetteCurl (B 0) x μ ν := by
    intro x μ ν
    rw [hG0]
    exact plaquetteCurl_addGradient _ _ x μ ν
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (weightedEnergy a del z B) := ⟨_, rfl⟩
  obtain ⟨wc, hwc⟩ : ∃ wc, wc = expWeight del z c.1 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = weightedCurl del z B := ⟨_, rfl⟩
  rw [← hsdef, ← hwc]
  have hwc0 : 0 ≤ wc := by rw [hwc]; exact (expWeight_pos _ _ _).le
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg _
  have hD0 : 0 ≤ D := by rw [hD]; exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = D ^ 2 + a * ∑ j ∈ Finset.range F.top, weightedNorm (expWeight del z) (chainMisfit B j) ^ 2 := by
    rw [hsdef, Real.sq_sqrt (weightedEnergy_nonneg ha0 del z B), hD]
    rfl
  have hDs : D ≤ s := by rw [hD, hsdef]; exact weightedCurl_le ha0 del z B
  have hfs : ∀ j, j < F.top → weightedNorm (expWeight del z) (chainMisfit B j) ≤ s := by
    intro j hj
    rw [hsdef]
    exact misfit_le ha del z B hj
  have hfa2 : a * weightedNorm (expWeight del z) (chainMisfit B F.depth) ≤ Real.sqrt a * s := by
    rw [hsdef]
    exact misfit_last_le ha0 del z B
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hBc : weightedNorm (expWeight del z) (B F.top) = wc := by
    have h1 : weightedNorm (expWeight del z) (topBondIndicator c) = |expWeight del z c.1 * 1| :=
      weightedNorm_single hL hs c 1 _ (fun y i => rfl)
    rw [hB.top_eq, h1, mul_one, abs_of_pos (expWeight_pos _ _ _), hwc]
  have hT := iteratedLineAverage_le hL hL3 hs hdel hdel1 z B hs0 hfs
  rw [hBc] at hT
  obtain ⟨Y0, hY0⟩ : ∃ Y0, Y0 = C₇ * (s + (3 / 2 * Real.exp 3 * s + wc)) := ⟨_, rfl⟩
  have hY00 : 0 ≤ Y0 := by rw [hY0]; positivity
  have hb0 : weightedNorm (expWeight del z) (G 0) ≤ (F.blockSide : ℝ) ^ F.top * Y0 := by
    rw [hG0]
    refine h7.trans ?_
    rw [hY0, ← hD, mul_comm C₇, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add hDs hT) hC) hN.le
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Y0 + 3 / 2 * s := ⟨_, rfl⟩
  have hYpos : 0 ≤ Y := by rw [hY]; positivity
  have hb0Y : weightedNorm (expWeight del z) (G 0) ≤ (F.blockSide : ℝ) ^ F.top * Y := by
    refine hb0.trans (mul_le_mul_of_nonneg_left ?_ hN.le)
    rw [hY]
    linarith
  have hcomm : ∀ j, j < F.top →
      weightedNorm (invWeight del z) (meanCommutator del z (G j)) ≤ 32 * del * Real.exp 3 * Y := by
    intro j hj
    rw [hY]
    exact meanCommutator_le hL hL3 hs hdel hdel1 z B G hs0 hY00 hfs hG hb0 hj
  have hγ := testForm_defect_le hL hL3 hs hdel hdel1 z B G (by positivity) hG hcomm
  rw [hGtop] at hγ
  have hpol := hB.stationary (testChain del z B G) (testChain_top del z B G)
  rw [chainEnergyPolar_testChain] at hpol
  have hRmb := curl_pairing_le hL hs hdel hdel1 z B G hs0 (by rw [← hD]; exact hDs) hb0Y
  have hc1 : ∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes,
      plaquetteCurl (B 0) x e.1 e.2 * plaquetteCurl (sqWeighted del z (G 0)) x e.1 e.2 =
      D ^ 2 + ∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, plaquetteCurl (B 0) x e.1 e.2 *
      (plaquetteCurl (sqWeighted del z (G 0)) x e.1 e.2 - expWeight del z x ^ 2 * plaquetteCurl (G 0) x e.1 e.2) := by
    rw [hD]
    unfold weightedCurl
    rw [Real.sq_sqrt (double_sum_sq_nonneg _ _ _), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hcurl]
    ring
  have hmE : |∑ y ∈ allSites F F.top, ∑ i : Fin 4, chainMisfit B F.depth y i * testForm del z B G F.top y i| ≤
      weightedNorm (expWeight del z) (chainMisfit B F.depth) *
        (wc + 3 / 2 * Real.exp 3 * (32 * del * Real.exp 3 * Y)) := by
    refine (abs_pairing_le (expWeight del z) (invWeight del z) (expWeight_mul_invWeight del z) _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (weightedNorm_nonneg _ _)
    have hEn : testForm del z B G F.top = sqWeighted del z (topBondIndicator c) +
        (testForm del z B G F.top - sqWeighted del z (topBondIndicator c)) := by
      rw [add_sub_cancel]
    rw [hEn]
    refine (weightedNorm_add_le _ _ _).trans ?_
    rw [weightedNorm_sqWeighted_top hL hs, ← hwc]
    exact add_le_add le_rfl hγ
  rw [hc1] at hpol
  obtain ⟨Rm, hRm⟩ : ∃ Rm, Rm = ∑ x ∈ allSites F 0, ∑ e ∈ orientedPlanes, plaquetteCurl (B 0) x e.1 e.2 *
      (plaquetteCurl (sqWeighted del z (G 0)) x e.1 e.2 - expWeight del z x ^ 2 * plaquetteCurl (G 0) x e.1 e.2) :=
    ⟨_, rfl⟩
  rw [← hRm] at hpol hRmb
  obtain ⟨P, hP⟩ : ∃ P, P = ∑ y ∈ allSites F F.top, ∑ i : Fin 4,
      chainMisfit B F.depth y i * testForm del z B G F.top y i := ⟨_, rfl⟩
  rw [← hP] at hpol hmE
  obtain ⟨ft, hft⟩ : ∃ ft, ft = weightedNorm (expWeight del z) (chainMisfit B F.depth) := ⟨_, rfl⟩
  rw [← hft] at hmE hfa2
  exact energy_arith hs0 hwc0 hsa ha0 hdel hC hΛ hs2 hpol hRmb hmE hfa2 hY hY0
    (by rw [hft]; exact weightedNorm_nonneg _ _)
theorem sum_filter_le_weighted {j : ℕ} {β : Type*} {T : Finset β} (P : F.Site j → Prop) [DecidablePred P]
    {A : ℝ} (hA : 0 ≤ A) (u : F.Site j → ℝ) (hP : ∀ x, P x → 1 ≤ A * u x ^ 2) (g : F.Site j → β → ℝ) :
    ∑ x ∈ (allSites F j).filter P, ∑ e ∈ T, g x e ^ 2 ≤ A * ∑ x ∈ allSites F j, ∑ e ∈ T, (u x * g x e) ^ 2 := by
  rw [Finset.mul_sum]
  calc _ ≤ ∑ x ∈ (allSites F j).filter P, A * ∑ e ∈ T, (u x * g x e) ^ 2 := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun e _ => ?_
        have h1 := hP x (Finset.mem_filter.1 hx).2
        calc g x e ^ 2 ≤ (A * u x ^ 2) * g x e ^ 2 := le_mul_of_one_le_left (sq_nonneg _) h1
          _ = _ := by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ => ?_
        exact mul_nonneg hA (Finset.sum_nonneg fun _ _ => sq_nonneg _)
open Classical in
theorem chainEnergyOnCells_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {a del : ℝ} (ha : 0 ≤ a)
    (hdel : 0 ≤ del) (z : F.Cell) {r : ℕ} (hr : r ≤ 24) (B : FormChain F) :
    chainEnergyOnCells a B (cellBall z r) ≤ Real.exp (50 * del) * weightedEnergy a del z B := by
  have hP : ∀ {j : ℕ} (x : F.Site j), enclosingCell x ∈ cellBall z r →
      1 ≤ Real.exp (50 * del) * expWeight del z x ^ 2 := by
    intro j x hx
    have h := torusSupDist_le_of_cellSupDist hL.pos hs x z r hx
    have hr' : (r : ℝ) ≤ 24 := by exact_mod_cast hr
    unfold expWeight
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    refine Real.one_le_exp ?_
    nlinarith
  have hA : 0 ≤ Real.exp (50 * del) := (Real.exp_pos _).le
  unfold chainEnergyOnCells weightedEnergy
  rw [mul_add]
  refine add_le_add ?_ ?_
  · have h1 := sum_filter_le_weighted (T := orientedPlanes)
      (fun x : F.Site 0 => enclosingCell x ∈ cellBall z r) hA (expWeight del z)
      (fun x => hP x) (fun x e => plaquetteCurl (B 0) x e.1 e.2)
    unfold weightedCurl
    rw [Real.sq_sqrt (double_sum_sq_nonneg _ _ _)]
    exact h1
  · rw [mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ ha
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [weightedNorm_sq]
    exact sum_filter_le_weighted (T := Finset.univ)
      (fun y : F.Site (j + 1) => enclosingCell y ∈ cellBall z r) hA (expWeight del z)
      (fun x => hP x) (fun y i => chainMisfit B j y i)
end FlatChainEnergy
open FlatChainEnergy in
theorem flatChainEnergyNearCell_of_gaugeFixing (h7 : weightedGaugeFixingAtCellScale) :
    flatChainEnergyNearCell := by
  obtain ⟨C₇, hC, h⟩ := h7
  intro a ha
  have ha0 : 0 ≤ a := by linarith
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  obtain ⟨K, hK⟩ : ∃ K, K = C₇ * (1 + 3 / 2 * Real.exp 3) + 3 / 2 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨M, hM⟩ : ∃ M, M = K * (80 + 48 * Real.exp 3 ^ 2 * Real.sqrt a) := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; positivity
  obtain ⟨del, hd⟩ : ∃ del, del = min 1 (1 / (2 * M)) := ⟨_, rfl⟩
  have d0 : 0 < del := by rw [hd]; positivity
  have d1 : del ≤ 1 := by rw [hd]; exact min_le_left _ _
  have dM : del * M ≤ 1 / 2 := by
    have h1 : del ≤ 1 / (2 * M) := by rw [hd]; exact min_le_right _ _
    calc del * M ≤ 1 / (2 * M) * M := mul_le_mul_of_nonneg_right h1 hM0.le
      _ = 1 / 2 := by field_simp
  refine ⟨del, Real.exp 50 * (1 + 2 * Real.sqrt a) ^ 2, d0, d1, by positivity, 3, ?_⟩
  intro F c B hodd hL3 hcub hflat z r hr
  obtain ⟨n₀, hn, hside⟩ := id hcub
  have hs : ∀ i, 0 < F.extent i := fun i => by rw [hside i]; omega
  obtain ⟨φ, hmean, hb⟩ := h F (B 0) z del hodd hcub d0 d1
  have hcore := energy_sq_le hodd hL3 hs ha d0 d1 hC.le c B hflat z φ hmean hb
  rw [← hK] at hcore
  have hβ : del * K * (80 + 48 * Real.exp 3 ^ 2 * Real.sqrt a) = del * M := by rw [hM]; ring
  rw [hβ] at hcore
  have hwc0 : 0 ≤ expWeight del z c.1 := (expWeight_pos _ _ _).le
  have habs := absorb_linear (Real.sqrt_nonneg (weightedEnergy a del z B)) hwc0
    (mul_nonneg d0.le hM0.le) dM hsa hcore
  have hE : weightedEnergy a del z B ≤ (1 + 2 * Real.sqrt a) ^ 2 * expWeight del z c.1 ^ 2 := by
    have h1 := weightedEnergy_nonneg ha0 del z B
    rw [← mul_pow, ← Real.sq_sqrt h1]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) habs 2
  have hw2 : expWeight del z c.1 ^ 2 ≤ Real.exp (-(2 * del * cellSupDist z c.1)) := by
    unfold expWeight
    rw [sq, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := cellSupDist_le_torusSupDist hs c.1 z
    nlinarith
  have hexp : Real.exp (50 * del) ≤ Real.exp 50 := Real.exp_le_exp.2 (by linarith)
  calc chainEnergyOnCells a B (cellBall z r) ≤ Real.exp (50 * del) * weightedEnergy a del z B :=
        chainEnergyOnCells_le hodd hs ha0 d0.le z hr B
    _ ≤ Real.exp 50 * ((1 + 2 * Real.sqrt a) ^ 2 * Real.exp (-(2 * del * cellSupDist z c.1))) := by
        refine mul_le_mul hexp (hE.trans ?_) (weightedEnergy_nonneg ha0 del z B) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hw2 (by positivity)
    _ = _ := by ring
end ColdStepAtMirrorFrames
end YangMills.Construction
end
