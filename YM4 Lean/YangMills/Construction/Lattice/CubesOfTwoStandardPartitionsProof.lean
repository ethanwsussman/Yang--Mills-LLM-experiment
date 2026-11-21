import YangMills.Construction.Lattice.BlocksInTheCoordinatesOfAFinerLatticeProof
import YangMills.Construction.Lattice.CubesUnderRefinement
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CubeRefinement
open Set TorusMetric
variable {L m : ℕ}
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : _root_.YangMills.Construction.TorusMetric.torusSupNorm x = ‖x‖ := by
  choose a ha ha' using fun μ => exists_coe_eq_abs_eq_norm (x μ)
  have hproj : torusProj S a = x := funext ha
  have hbdd : BddBelow (supNormVec '' (torusProj S ⁻¹' {x})) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, -, rfl⟩
    exact (abs_nonneg (w 0)).trans (Finset.le_sup' (fun μ => |w μ|) (Finset.mem_univ 0))
  apply le_antisymm
  · refine (csInf_le hbdd ⟨a, hproj, rfl⟩).trans ?_
    refine Finset.sup'_le _ _ fun μ _ => ?_
    rw [ha' μ]
    exact norm_le_pi_norm x μ
  · refine le_csInf ⟨_, a, hproj, rfl⟩ ?_
    rintro _ ⟨w, hw, rfl⟩
    have hw' : torusProj S w = x := hw
    have hnonneg : 0 ≤ supNormVec w :=
      (abs_nonneg (w 0)).trans (Finset.le_sup' (fun μ => |w μ|) (Finset.mem_univ 0))
    refine (pi_norm_le_iff_of_nonneg hnonneg).2 fun μ => ?_
    rw [← hw']
    exact (addCircle_norm_coe_le_abs (w μ)).trans
      (Finset.le_sup' (fun μ => |w μ|) (Finset.mem_univ μ))
theorem norm_torusProj_le {S r : ℝ} (hr : 0 ≤ r) {w : Fin 4 → ℝ} (h : ∀ μ, |w μ| ≤ r) :
    ‖torusProj S w‖ ≤ r :=
  (pi_norm_le_iff_of_nonneg hr).2 fun μ => (addCircle_norm_coe_le_abs (w μ)).trans (h μ)
theorem exists_torusProj_eq_abs_eq_norm {S : ℝ} (d : Torus4 S) :
    ∃ w, torusProj S w = d ∧ ∀ μ, |w μ| = ‖d μ‖ := by
  choose a ha ha' using fun μ => exists_coe_eq_abs_eq_norm (d μ)
  exact ⟨a, funext ha, ha'⟩
theorem torusProj_sub {S : ℝ} (u w : Fin 4 → ℝ) :
    torusProj S (u - w) = torusProj S u - torusProj S w := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
theorem meshSize_pos (hL : 0 < L) (i : ℤ) : 0 < meshSize L i := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem meshSize_eq_pow_mul (hL : 0 < L) (i : ℤ) (n : ℕ) :
    meshSize L i = (L : ℝ) ^ n * meshSize L (i + n) := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.meshSize_eq_pow_mul <;> assumption
theorem mem_cubeAround {i : ℤ} {y : Site L m i} {x : FourTorus L m} :
    x ∈ cubeAround y ↔ ‖x - (y : FourTorus L m)‖ ≤ meshSize L i / 2 := by
  show _root_.YangMills.Construction.TorusMetric.torusSupNorm _ ≤ _ ↔ _
  rw [_root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm]
theorem sum_pointOnAxis (a : Fin 4 → ℝ) :
    ∑ μ, pointOnAxis L m μ (a μ) = torusProj (torusSide L m) a := by
  funext ν
  rw [Finset.sum_apply]
  simp [pointOnAxis, torusProj, Pi.single_apply]
theorem coordinatePoint_eq (s : ℤ) (y : FourTorus L m) (q : Fin 4 → ℤ) :
    coordinatePoint s y q = y + torusProj (torusSide L m) fun μ => (q μ : ℝ) * meshSize L s := by
  rw [coordinatePoint, sum_pointOnAxis]
theorem exists_near_multiple {c : ℤ} (hc : 0 ≤ c) {W u : ℝ} (hW : 0 < W)
    (hu : |u| ≤ (2 * (c : ℝ) + 1) * W / 2) :
    ∃ q : ℤ, |q| ≤ c ∧ |u - (q : ℝ) * W| ≤ W / 2 := by
  obtain ⟨h1, h2⟩ := abs_le.1 hu
  have hr := abs_sub_round (u / W)
  set r := round (u / W) with hrdef
  have hscale : ∀ q : ℤ, |u / W - (q : ℝ)| ≤ 1 / 2 → |u - (q : ℝ) * W| ≤ W / 2 := by
    intro q hq
    have : u - (q : ℝ) * W = (u / W - (q : ℝ)) * W := by field_simp
    rw [this, abs_mul, abs_of_pos hW]
    nlinarith
  have hlo : -(c : ℝ) - 1 / 2 ≤ u / W := by
    rw [le_div_iff₀ hW]; nlinarith
  have hhi : u / W ≤ (c : ℝ) + 1 / 2 := by
    rw [div_le_iff₀ hW]; nlinarith
  rw [abs_le] at hr
  by_cases hra : r < -c
  · refine ⟨-c, by rw [abs_neg, abs_of_nonneg hc], hscale (-c) ?_⟩
    have : (r : ℝ) + 1 ≤ -(c : ℝ) := by exact_mod_cast hra
    push_cast
    rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  by_cases hrb : c < r
  · refine ⟨c, by rw [abs_of_nonneg hc], hscale c ?_⟩
    have : (c : ℝ) + 1 ≤ r := by exact_mod_cast hrb
    rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  · exact ⟨r, abs_le.2 ⟨not_lt.1 hra, not_lt.1 hrb⟩, hscale r (abs_le.2 hr)⟩
theorem exists_mem_cubeAround (hL : 0 < L) (i : ℤ) (x : FourTorus L m) :
    ∃ y : Site L m i, x ∈ cubeAround y := by
  obtain ⟨w, hw, -⟩ := exists_torusProj_eq_abs_eq_norm x
  have hW := meshSize_pos hL i
  have hex : ∀ μ, ∃ q : ℤ, |w μ - (q : ℝ) * meshSize L i| ≤ meshSize L i / 2 := by
    intro μ
    have hdiv : w μ / meshSize L i * meshSize L i = w μ := by field_simp
    have hr := abs_sub_round (w μ / meshSize L i)
    refine ⟨round (w μ / meshSize L i), ?_⟩
    have : w μ - (round (w μ / meshSize L i) : ℝ) * meshSize L i =
        (w μ / meshSize L i - (round (w μ / meshSize L i) : ℝ)) * meshSize L i := by
      rw [sub_mul, hdiv]
    rw [this, abs_mul, abs_of_pos hW]
    nlinarith
  choose q hq using hex
  refine ⟨⟨torusProj (torusSide L m) fun μ => (q μ : ℝ) * meshSize L i, q, fun μ => rfl⟩, ?_⟩
  rw [mem_cubeAround]
  have : x - torusProj (torusSide L m) (fun μ => (q μ : ℝ) * meshSize L i) =
      torusProj (torusSide L m) (w - fun μ => (q μ : ℝ) * meshSize L i) := by
    rw [torusProj_sub, hw]
  simp only [this]
  exact norm_torusProj_le (half_pos hW).le hq
theorem cubeAround_eq_iUnion (hL : Odd L) {t : ℤ} (n : ℕ) (y : Site L m t)
    (hB : refinedBlock n y =
      coordinatePoint (t + n) (y : FourTorus L m) '' blockOffsets L n) :
    cubeAround y =
      ⋃ x : Site L m (t + n), ⋃ _ : (x : FourTorus L m) ∈ refinedBlock n y, cubeAround x := by
  have hL0 : 0 < L := hL.pos
  have hW' := meshSize_pos hL0 (t + n)
  have hW := meshSize_eq_pow_mul hL0 t n
  obtain ⟨c, hc⟩ : Odd (L ^ n) := hL.pow
  have hcR : (L : ℝ) ^ n = 2 * c + 1 := by exact_mod_cast hc
  have hcZ : (L : ℤ) ^ n = 2 * c + 1 := by exact_mod_cast hc
  rw [hcR] at hW
  have hoff : ∀ q : Fin 4 → ℤ, q ∈ blockOffsets L n ↔ ∀ μ, |q μ| ≤ c := by
    intro q
    refine forall_congr' fun μ => ?_
    rw [hcZ]
    omega
  apply subset_antisymm
  · intro x hx
    have hx' := mem_cubeAround.1 hx
    obtain ⟨w, hw, hw'⟩ := exists_torusProj_eq_abs_eq_norm (x - (y : FourTorus L m))
    have hex : ∀ μ, ∃ q : ℤ, |q| ≤ c ∧
        |w μ - (q : ℝ) * meshSize L (t + n)| ≤ meshSize L (t + n) / 2 := by
      intro μ
      refine exists_near_multiple (by omega) hW' ?_
      rw [hw' μ]
      have := (norm_le_pi_norm (x - (y : FourTorus L m)) μ).trans hx'
      rw [hW] at this
      exact_mod_cast this
    choose q hq1 hq2 using hex
    have hmem : coordinatePoint (t + n) (y : FourTorus L m) q ∈ refinedBlock n y := by
      rw [hB]
      exact ⟨q, (hoff q).2 hq1, rfl⟩
    refine mem_iUnion₂.2 ⟨⟨_, hmem.2⟩, hmem, ?_⟩
    rw [mem_cubeAround]
    have : x - coordinatePoint (t + n) (y : FourTorus L m) q =
        torusProj (torusSide L m) (w - fun μ => (q μ : ℝ) * meshSize L (t + n)) := by
      rw [coordinatePoint_eq, torusProj_sub, hw]
      abel
    simp only [this]
    exact norm_torusProj_le (half_pos hW').le hq2
  · refine iUnion₂_subset fun y' hy' x hx => ?_
    rw [hB] at hy'
    obtain ⟨q, hq, hqe⟩ := hy'
    have hq' := (hoff q).1 hq
    have hn : ‖(y' : FourTorus L m) - y‖ ≤ (c : ℝ) * meshSize L (t + n) := by
      rw [← hqe, coordinatePoint_eq, add_sub_cancel_left]
      refine norm_torusProj_le (by positivity) fun μ => ?_
      rw [abs_mul, abs_of_pos hW']
      refine mul_le_mul_of_nonneg_right ?_ hW'.le
      exact_mod_cast hq' μ
    rw [mem_cubeAround] at hx ⊢
    have e : x - (y : FourTorus L m) = (x - y') + ((y' : FourTorus L m) - y) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [hW]
    linarith
theorem isPartitionRegion_of_refinement {t t' : ℤ} (hcubes : ∀ y : Site L m t, cubeAround y =
      ⋃ x : Site L m t', ⋃ _ : (x : FourTorus L m) ∈ refinedBlock (t' - t).toNat y, cubeAround x)
    {X : Set (FourTorus L m)} (hX : IsPartitionRegion t X) : IsPartitionRegion t' X := by
  obtain ⟨C, hC, rfl⟩ := hX
  refine ⟨{Q' | Q' ∈ standardCubePartition L m t' ∧ ∃ Q ∈ C, Q' ⊆ Q}, fun Q hQ => hQ.1, ?_⟩
  apply subset_antisymm
  · rintro x ⟨Q, hQ, hx⟩
    obtain ⟨y, rfl⟩ := hC hQ
    rw [hcubes y] at hx
    obtain ⟨y', hy', hxy⟩ := mem_iUnion₂.1 hx
    refine ⟨cubeAround y', ⟨⟨y', rfl⟩, cubeAround y, hQ, ?_⟩, hxy⟩
    rw [hcubes y]
    exact subset_iUnion₂_of_subset y' hy' subset_rfl
  · rintro x ⟨Q', ⟨-, Q, hQ, hs⟩, hx⟩
    exact ⟨Q, hQ, hs hx⟩
theorem mem_complementRegion (hL : 0 < L) (t : ℤ) {X : Set (FourTorus L m)} {z : FourTorus L m}
    (hz : z ∉ X) : z ∈ complementRegion t X := by
  obtain ⟨y, hy⟩ := exists_mem_cubeAround hL t z
  exact ⟨cubeAround y, ⟨⟨y, rfl⟩, fun h => hz (h.2 hy)⟩, hy⟩
theorem cubesUnderRefinement_holds (hcoord : RefinedBlockCoordinatesHold) :
    CubesUnderRefinement := by
  intro L m hL h13 hm
  have hL0 : 0 < L := hL.pos
  have hcubes : ∀ t t' : ℤ, -(m : ℤ) ≤ t → t ≤ t' → ∀ y : Site L m t, cubeAround y =
      ⋃ x : Site L m t', ⋃ _ : (x : FourTorus L m) ∈ refinedBlock (t' - t).toNat y,
        cubeAround x := by
    intro t t' ht htt y
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, t' = t + n := ⟨(t' - t).toNat, by omega⟩
    have hn : (t + (n : ℤ) - t).toNat = n := by omega
    rw [hn]
    have hall := (hcoord L 1 m ⟨rfl, rfl, rfl, hL, h13, one_pos, hm, rfl⟩).1 t n ht
    exact cubeAround_eq_iUnion hL n y (hall.2.2.1 y).1
  refine ⟨fun t t' ht htt => ⟨hcubes t t' ht htt, ?_, fun X hX => ?_, fun X _ z hz => ?_⟩, ?_⟩
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨y, hy⟩ := exists_mem_cubeAround hL0 t x
    exact ⟨_, ⟨y, rfl⟩, hy⟩
  · exact isPartitionRegion_of_refinement (hcubes t t' ht htt) hX
  · exact mem_complementRegion hL0 t hz
  · intro K i j _ hij hjK y
    have hd : (levelDepth K i - levelDepth K j).toNat = j - i := by
      simp only [levelDepth]
      omega
    have := hcubes (levelDepth K j) (levelDepth K i) (by simp only [levelDepth]; omega)
      (by simp only [levelDepth]; omega) y
    rw [hd] at this
    exact this
end YangMills.Construction.PeriodicLattice.CubeRefinement
