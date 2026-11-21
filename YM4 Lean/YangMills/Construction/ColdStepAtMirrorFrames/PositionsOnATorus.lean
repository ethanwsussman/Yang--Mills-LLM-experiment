import YangMills.Construction.ColdStepAtMirrorFrames.SumsOverTheSitesOfATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
theorem distToMultiples_nonneg (n u : ℝ) : 0 ≤ distToMultiples n u := abs_nonneg _
theorem distToMultiples_add_mul_int {n : ℝ} (hn : n ≠ 0) (u : ℝ) (c : ℤ) :
    distToMultiples n (u + n * c) = distToMultiples n u := by
  unfold distToMultiples
  have e : (u + n * c) / n = u / n + c := by
    field_simp
  rw [e, round_add_intCast]
  push_cast
  congr 1
  ring
theorem distToMultiples_add_le {n : ℝ} (hn : 0 < n) (u t : ℝ) :
    distToMultiples n (u + t) ≤ distToMultiples n u + |t| := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatChainEnergy.distToMultiples_add_le <;> assumption
abbrev cellSideAt (F : BlockFrame) (j : ℕ) : ℕ := F.blockSide ^ (F.top - j)
theorem period_eq_extent_mul (j : ℕ) (i : Fin 4) : F.period j i = F.extent i * cellSideAt F j := rfl
theorem distToMultiples_cellCoordinate_siteOfCoords (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (v : Fin 4 → ℤ) (z : F.Cell) (i : Fin 4) :
    distToMultiples (F.extent i) (cellCoordinate (siteOfCoords j v : F.Site j) i - siteCoords z i) =
      distToMultiples (F.extent i) ((v i : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) - siteCoords z i) := by
  have hM : (0 : ℝ) < (F.blockSide : ℝ) ^ (F.top - j) := by
    have : 0 < F.blockSide := hL.pos
    positivity
  have hext : (F.extent i : ℝ) ≠ 0 := by
    have := hs i
    positivity
  unfold cellCoordinate
  rw [siteCoords_siteOfCoords]
  have e := Int.emod_add_mul_ediv (v i) (F.period j i : ℤ)
  have e' : ((v i % (F.period j i : ℤ) : ℤ) : ℝ) =
      (v i : ℝ) - (F.period j i : ℝ) * ((v i / (F.period j i : ℤ) : ℤ) : ℝ) := by
    have : ((v i % (F.period j i : ℤ) + (F.period j i : ℤ) * (v i / (F.period j i : ℤ)) : ℤ) : ℝ) = (v i : ℝ) := by
      rw [e]
    push_cast at this
    linarith
  rw [e']
  have hp : (F.period j i : ℝ) = (F.extent i : ℝ) * (F.blockSide : ℝ) ^ (F.top - j) := by
    rw [period_eq_extent_mul]
    push_cast
    rfl
  rw [hp]
  have e2 : ((v i : ℝ) - (F.extent i : ℝ) * (F.blockSide : ℝ) ^ (F.top - j) * ((v i / (F.period j i : ℤ) : ℤ) : ℝ)) /
      (F.blockSide : ℝ) ^ (F.top - j) - siteCoords z i =
        ((v i : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) - siteCoords z i) +
          (F.extent i : ℝ) * ((- (v i / (F.period j i : ℤ)) : ℤ) : ℝ) := by
    push_cast
    field_simp
    ring
  rw [e2, distToMultiples_add_mul_int hext]
theorem torusSupDist_add_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (x : F.Site j)
    (h : Fin 4 → ℤ) (z : F.Cell) (t : ℝ) (ht : ∀ i, |(h i : ℝ)| / (F.blockSide : ℝ) ^ (F.top - j) ≤ t) :
    torusSupDist (x + siteOfCoords j h) z ≤ torusSupDist x z + t := by
  have hM : (0 : ℝ) < (F.blockSide : ℝ) ^ (F.top - j) := by
    have : 0 < F.blockSide := hL.pos
    positivity
  unfold torusSupDist
  refine Finset.sup'_le _ _ fun i _ => ?_
  have e1 : x + siteOfCoords j h = siteOfCoords j (siteCoords x + h) := by
    rw [siteOfCoords_add, siteOfCoords_siteCoords]
  rw [e1, distToMultiples_cellCoordinate_siteOfCoords hL hs]
  have hsi : (0 : ℝ) < F.extent i := by exact_mod_cast hs i
  have e2 : (((siteCoords x + h) i : ℤ) : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) - siteCoords z i =
      ((siteCoords x i : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) - siteCoords z i) +
        (h i : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) := by
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [e2]
  refine (distToMultiples_add_le hsi _ _).trans ?_
  have e3 : distToMultiples (F.extent i) ((siteCoords x i : ℝ) / (F.blockSide : ℝ) ^ (F.top - j) - siteCoords z i) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => distToMultiples (F.extent i) (cellCoordinate x i - siteCoords z i)) := by
    refine le_trans (le_of_eq ?_)
      (Finset.le_sup' (fun i => distToMultiples (F.extent i) (cellCoordinate x i - siteCoords z i))
        (Finset.mem_univ i))
    rfl
  have e4 : |(h i : ℝ) / (F.blockSide : ℝ) ^ (F.top - j)| ≤ t := by
    rw [abs_div, abs_of_pos hM]
    exact ht i
  linarith
theorem torusSupDist_refineSite (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j l : ℕ} (hjl : j ≤ l)
    (hl : l ≤ F.top) (y : F.Site l) (z : F.Cell) : torusSupDist (refineSite j l y) z = torusSupDist y z := by
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  unfold torusSupDist refineSite
  congr 1
  funext i
  conv_rhs => rw [← siteOfCoords_siteCoords y]
  rw [distToMultiples_cellCoordinate_siteOfCoords hL hs, distToMultiples_cellCoordinate_siteOfCoords hL hs]
  congr 2
  have e : F.top - j = (F.top - l) + (l - j) := by omega
  rw [e, pow_add]
  push_cast
  field_simp
def expWeight (δ : ℝ) (z : F.Cell) {j : ℕ} (x : F.Site j) : ℝ := Real.exp (-(δ * torusSupDist x z))
theorem expWeight_sq_le {δ t : ℝ} (hδ : 0 ≤ δ) (z : F.Cell) {j l : ℕ} (x : F.Site j) (x' : F.Site l)
    (h : torusSupDist x' z ≤ torusSupDist x z + t) :
    expWeight δ z x ^ 2 ≤ Real.exp (2 * δ * t) * expWeight δ z x' ^ 2 := by
  unfold expWeight
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.2
  push_cast
  nlinarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
