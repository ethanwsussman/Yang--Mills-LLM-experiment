import YangMills.Construction.InfiniteLattice.DataOfADiagonalPictureProof
import YangMills.Construction.Lattice.CosetsCoordinatesAndDistances
import YangMills.Construction.Lattice.CubesVerticesAndEdgesOfThePartition
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open PeriodicLattice
namespace TorusBound.PartitionCells
open Coordinates
def signVec (b : Fin 4 → Bool) : Fin 4 → ℝ := fun μ => if b μ = true then 1 else -1
theorem signVec_isSigns (b : Fin 4 → Bool) :
    LevelUnitPartition.IsSigns (signVec b) := fun μ => by
  by_cases hb : b μ = true
  · left; simp [signVec, hb]
  · right; simp [signVec, hb]
theorem exists_eq_smul_signVec (s : ℝ) (d : Fin 4 → ℝ) (hd : ∀ μ, d μ = s ∨ d μ = -s) :
    ∃ b, d = s • signVec b := by
  classical
  refine ⟨fun μ => decide (d μ = s), ?_⟩
  funext μ
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases h2 : d μ = s
  · have hb : decide (d μ = s) = true := by simpa using h2
    simp only [signVec, hb, if_true, mul_one]
    exact h2
  · have hb : ¬ decide (d μ = s) = true := by simpa using h2
    simp only [signVec, if_neg hb]
    rcases hd μ with h1 | h1
    · exact absurd h1 h2
    · rw [h1]; ring
theorem eq_half_or_eq_neg_half {σ x : ℝ} (hσ : 0 < σ) {n : ℤ} (hx : x = σ * ((n : ℝ) + 1 / 2))
    (h1 : -(σ / 2) ≤ x) (h2 : x ≤ σ / 2) : x = σ / 2 ∨ x = -(σ / 2) := by
  have hn1 : (n : ℝ) ≤ 0 := by
    by_contra hh
    push Not at hh
    nlinarith
  have hn2 : (-1 : ℝ) ≤ n := by
    by_contra hh
    push Not at hh
    nlinarith
  have hn1' : n ≤ 0 := by exact_mod_cast hn1
  have hn2' : -1 ≤ n := by exact_mod_cast hn2
  have : n = 0 ∨ n = -1 := by omega
  rcases this with rfl | rfl
  · left; rw [hx]; push_cast; ring
  · right; rw [hx]; push_cast; ring
theorem ne_mul_intCast_of_lt {σ ℓ : ℝ} (hσ : 0 < σ) (hℓ : σ < ℓ) (k : ℤ) : σ ≠ ℓ * (k : ℝ) := by
  intro h
  rcases le_or_gt k 0 with hk | hk
  · have : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    nlinarith
  · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
theorem ne_mul_intCast_of_pos_of_lt {σ t : ℝ} (hσ : 0 < σ) (h0 : 0 < t) (h1 : t < σ) (n : ℤ) :
    t ≠ σ * (n : ℝ) := by
  intro h
  have hn0 : (0 : ℝ) < n := by
    by_contra hh
    push Not at hh
    nlinarith
  have hn1 : (n : ℝ) < 1 := by
    by_contra hh
    push Not at hh
    nlinarith
  have hn0' : 0 < n := by exact_mod_cast hn0
  have hn1' : n < 1 := by exact_mod_cast hn1
  omega
theorem eq_zero_of_eq_mul_intCast {σ t : ℝ} (hσ : 0 < σ) (h0 : -σ < t) (h1 : t < σ) (n : ℤ)
    (h : t = σ * (n : ℝ)) : t = 0 := by
  have hn0 : (-1 : ℝ) < n := by
    by_contra hh
    push Not at hh
    nlinarith
  have hn1 : (n : ℝ) < 1 := by
    by_contra hh
    push Not at hh
    nlinarith
  have hn0' : -1 < n := by exact_mod_cast hn0
  have hn1' : n < 1 := by exact_mod_cast hn1
  have : n = 0 := by omega
  rw [h, this]; simp
theorem halfShift_eq_neg_half_of_interior {σ t : ℝ} (hσ : 0 < σ) (h0 : 0 < t) (h1 : t < σ) {n : ℤ}
    (h2 : -(σ / 2) ≤ σ * ((n : ℝ) + 1 / 2) + t) (h3 : σ * ((n : ℝ) + 1 / 2) + t ≤ σ / 2) :
    σ * ((n : ℝ) + 1 / 2) = -(σ / 2) := by
  have hn1 : (n : ℝ) < 0 := by
    by_contra hh
    push Not at hh
    nlinarith
  have hn2 : (-2 : ℝ) < n := by
    by_contra hh
    push Not at hh
    nlinarith
  have hn1' : n < 0 := by exact_mod_cast hn1
  have hn2' : -2 < n := by exact_mod_cast hn2
  have : n = -1 := by omega
  rw [this]; push_cast; ring
theorem card_Icc_ceil_floor_le {α β : ℝ} (h : α ≤ β) :
    (((Finset.Icc ⌈α⌉ ⌊β⌋).card : ℕ) : ℝ) ≤ β - α + 1 := by
  rw [Int.card_Icc]
  rcases le_total 0 (⌊β⌋ + 1 - ⌈α⌉) with h0 | h0
  · have h1 : (((⌊β⌋ + 1 - ⌈α⌉).toNat : ℤ) : ℝ) = ((⌊β⌋ + 1 - ⌈α⌉ : ℤ) : ℝ) := by
      rw [Int.toNat_of_nonneg h0]
    have h2 : (((⌊β⌋ + 1 - ⌈α⌉).toNat : ℕ) : ℝ) = ((⌊β⌋ : ℝ) + 1 - (⌈α⌉ : ℝ)) := by
      rw [← Int.cast_natCast, h1]; push_cast; ring
    rw [h2]
    have := Int.floor_le β
    have := Int.le_ceil α
    linarith
  · have : (⌊β⌋ + 1 - ⌈α⌉).toNat = 0 := Int.toNat_of_nonpos h0
    rw [this]
    simp only [Nat.cast_zero]
    linarith
theorem euclidNormVec_of_single_axis {σ : ℝ} (hσ : 0 ≤ σ) (v : Fin 4 → ℝ) (ν : Fin 4)
    (hv : ∀ μ, v μ ^ 2 = if μ = ν then σ ^ 2 else 0) : TorusMetric.euclidNormVec v = σ := by
  unfold TorusMetric.euclidNormVec
  rw [Finset.sum_congr rfl (fun μ _ => hv μ), Finset.sum_ite_eq' Finset.univ ν (fun _ => σ ^ 2),
    if_pos (Finset.mem_univ ν), Real.sqrt_sq hσ]
variable {D : Setup} {j : ℕ}
theorem torusCover_add (u v : Fin 4 → ℝ) : D.torusCover u + D.torusCover v = D.torusCover (u + v) := by
  funext μ
  exact (AddCircle.coe_add _ _ _).symm
theorem exists_liftOfPoint (y : D.Torus) : ∃ w, D.IsLiftOfPoint y w :=
  ⟨TestFunctions.liftPoint y, TestFunctions.torusProj_liftPoint y⟩
theorem exists_latticeTranslate {u v : Fin 4 → ℝ} (h : D.torusCover u = D.torusCover v) :
    ∃ k, u = v + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k :=
  TestFunctions.exists_latticeTranslate_of_torusProj_eq h
theorem torusCover_add_latticeTranslate (v : Fin 4 → ℝ) (k : Fin 4 → ℤ) :
    D.torusCover (v + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k) =
      D.torusCover v :=
  TestFunctions.torusProj_add_latticeTranslate _ _ _
section Vertices
variable (hσ : 0 < D.physicalCubeSide j) (hCen : CentreLifts D j) (hCube : CubeMembershipByLifts D j)
include hσ hCube
theorem mem_cubeCentredAt_of_signs (c : Site D.L D.m (D.cubeScaleIndex j)) {wc wv : Fin 4 → ℝ}
    (hwc : D.IsLiftOfPoint (c : D.Torus) wc) {v : D.Torus} (hwv : D.IsLiftOfPoint v wv)
    (hd : ∀ μ, wc μ - wv μ = D.physicalCubeSide j / 2 ∨ wc μ - wv μ = -(D.physicalCubeSide j / 2)) :
    v ∈ D.cubeCentredAt c := by
  refine (hCube c wc hwc v).2 ⟨wv, hwv, fun μ => ?_⟩
  rw [Pi.sub_apply, mem_Icc]
  rcases hd μ with h1 | h1 <;> constructor <;> linarith
include hCen
theorem exists_signs_of_mem_cubeCentredAt {hj : j ≤ D.K} {h : D.LevelFits j}
    (hV : VertexIffHalfIntegral hj h)
    (c : Site D.L D.m (D.cubeScaleIndex j)) {wc : Fin 4 → ℝ} (hwc : D.IsLiftOfPoint (c : D.Torus) wc)
    {v : D.Torus} (hv : D.IsLevelVertex hj h v) (hm : v ∈ D.cubeCentredAt c) :
    ∃ wv, D.IsLiftOfPoint v wv ∧
      ∀ μ, wc μ - wv μ = D.physicalCubeSide j / 2 ∨ wc μ - wv μ = -(D.physicalCubeSide j / 2) := by
  obtain ⟨wv, hwv, hI⟩ := (hCube c wc hwc v).1 hm
  refine ⟨wv, hwv, fun μ => ?_⟩
  obtain ⟨b, hb⟩ := (hCen wc).1 ⟨c, hwc⟩ μ
  obtain ⟨a, ha⟩ := (hV v).1 hv μ wv hwv
  have hI' := hI μ
  rw [Pi.sub_apply, mem_Icc] at hI'
  refine eq_half_or_eq_neg_half hσ (n := b - a - 1) ?_ (by linarith [hI'.2]) (by linarith [hI'.1])
  rw [hb, ha]; push_cast; ring
end Vertices
theorem vertexCubeIncidence_holds (hj : j ≤ D.K) (h : D.LevelFits j) (hTwo : CosetProperties D j)
    (hCen : CentreLifts D j) (hCube : CubeMembershipByLifts D j) (hCorner : CubeVerticesByLifts hj h)
    (hV : VertexIffHalfIntegral hj h) : VertexCubeIncidence D hj h := by
  obtain ⟨-, hσ, hσℓ, -⟩ := hTwo
  have hσℓ' : D.physicalCubeSide j < PeriodicLattice.torusSide D.L D.m := hσℓ
  refine ⟨fun c v hv => ?_, fun Q hQ => ?_, fun v hv => ?_⟩
  · obtain ⟨wc, hwc⟩ := exists_liftOfPoint (D := D) (c : D.Torus)
    refine ⟨⟨fun hm => ?_, ?_⟩, ⟨fun hm => ?_, fun hc => ?_⟩⟩
    · obtain ⟨wv, hwv, hd⟩ := exists_signs_of_mem_cubeCentredAt hσ hCen hCube hV c hwc hv hm
      exact ⟨wc, wv, hwc, hwv, hd⟩
    · rintro ⟨wc', wv, hwc', hwv, hd⟩
      exact mem_cubeCentredAt_of_signs hσ hCube c hwc' hwv hd
    · obtain ⟨wv, hwv, hd⟩ := exists_signs_of_mem_cubeCentredAt hσ hCen hCube hV c hwc hv hm
      obtain ⟨b, hb⟩ := exists_eq_smul_signVec (D.physicalCubeSide j / 2) (wv - wc) (fun μ => by
        rw [Pi.sub_apply]
        rcases hd μ with h1 | h1
        · right; linarith
        · left; linarith)
      refine (hCorner c wc hwc v).2 ⟨signVec b, signVec_isSigns b, ?_⟩
      have h2 : wc + (D.physicalCubeSide j / 2) • signVec b = wv := by rw [← hb]; abel
      rw [h2]
      exact hwv.symm
    · obtain ⟨ε, hε, hv'⟩ := (hCorner c wc hwc v).1 hc
      refine mem_cubeCentredAt_of_signs hσ hCube c hwc (wv := wc + (D.physicalCubeSide j / 2) • ε)
        hv'.symm (fun μ => ?_)
      rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases hε μ with h1 | h1 <;> rw [h1]
      · right; ring
      · left; ring
  · obtain ⟨c, rfl⟩ := hQ
    obtain ⟨wc, hwc⟩ := exists_liftOfPoint (D := D) (c : D.Torus)
    have hset : {v : D.Torus | (D.levelUnitPartition hj h).IsCornerOf v (D.cubeCentredAt c)} =
        range (fun b : Fin 4 → Bool => D.torusCover (wc + (D.physicalCubeSide j / 2) • signVec b)) := by
      ext v
      constructor
      · intro hv
        obtain ⟨ε, hε, hv'⟩ := (hCorner c wc hwc v).1 hv
        obtain ⟨b, hb⟩ := exists_eq_smul_signVec 1 ε hε
        refine ⟨b, ?_⟩
        rw [hv', hb, one_smul]
      · rintro ⟨b, rfl⟩
        exact (hCorner c wc hwc _).2 ⟨signVec b, signVec_isSigns b, rfl⟩
    have hinj : Function.Injective
        (fun b : Fin 4 → Bool => D.torusCover (wc + (D.physicalCubeSide j / 2) • signVec b)) := by
      intro b b' hbb
      obtain ⟨k, hk⟩ := exists_latticeTranslate (D := D) hbb
      funext μ
      by_contra hne
      have hμ := congrFun hk μ
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, TestFunctions.latticeTranslate] at hμ
      by_cases hb : b μ = true
      · have hb' : b' μ = false := by
          cases hh : b' μ
          · rfl
          · exact absurd (hb.trans hh.symm) hne
        simp only [signVec, hb, hb', if_true, Bool.false_eq_true, if_false] at hμ
        exact ne_mul_intCast_of_lt hσ hσℓ' (k μ) (by linarith)
      · have hb1 : b μ = false := by simpa using hb
        have hb' : b' μ = true := by
          cases hh : b' μ
          · exact absurd (hb1.trans hh.symm) hne
          · rfl
        simp only [signVec, hb1, hb', if_true, Bool.false_eq_true, if_false] at hμ
        exact ne_mul_intCast_of_lt hσ hσℓ' (-k μ) (by push_cast; linarith)
    rw [hset, ← image_univ, hinj.injOn.encard_image, encard_univ, ENat.card_eq_coe_fintype_card]
    simp
  · obtain ⟨w₀, hw₀⟩ := exists_liftOfPoint (D := D) v
    let g : (Fin 4 → Bool) → Set D.Torus := fun b =>
      {x | TorusMetric.torusSupNorm (x - D.torusCover (w₀ + (D.physicalCubeSide j / 2) • signVec b)) ≤
        meshSize D.L (D.cubeScaleIndex j) / 2}
    have hsub : {Q : Set D.Torus | D.IsLevelCube j Q ∧ v ∈ Q} ⊆ g '' univ := by
      rintro Q ⟨hQ, hvQ⟩
      obtain ⟨c, rfl⟩ := hQ
      obtain ⟨wc, hwc⟩ := exists_liftOfPoint (D := D) (c : D.Torus)
      obtain ⟨wv, hwv, hd⟩ := exists_signs_of_mem_cubeCentredAt hσ hCen hCube hV c hwc hv hvQ
      obtain ⟨b, hb⟩ := exists_eq_smul_signVec (D.physicalCubeSide j / 2) (wc - wv) hd
      obtain ⟨k, hk⟩ := exists_latticeTranslate (D := D) (hwv.trans hw₀.symm)
      have hc : D.torusCover (w₀ + (D.physicalCubeSide j / 2) • signVec b) = (c : D.Torus) := by
        have h1 : wc = (w₀ + (D.physicalCubeSide j / 2) • signVec b) +
            TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k := by
          rw [← hb, ← sub_eq_iff_eq_add.2 hk]; abel
        rw [← torusCover_add_latticeTranslate _ k, ← h1]
        exact hwc
      refine ⟨b, mem_univ _, ?_⟩
      ext x
      simp only [g, hc]
      rfl
    calc {Q : Set D.Torus | D.IsLevelCube j Q ∧ v ∈ Q}.encard ≤ (g '' univ).encard :=
          encard_le_encard hsub
      _ ≤ (univ : Set (Fin 4 → Bool)).encard := encard_image_le _ _
      _ = 16 := by
        rw [encard_univ, ENat.card_eq_coe_fintype_card]
        simp
section Edges
variable {hj : j ≤ D.K} {h : D.LevelFits j}
theorem isEdgeEndpoint_start (hEnd : EdgeEndpointsByLifts hj h) {w : Fin 4 → ℝ} (ν : Fin 4)
    (hw : ∀ μ, w μ ∈ halfLatticeCoset D j) :
    (D.levelUnitPartition hj h).IsEdgeEndpoint
      (D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν) (D.torusCover w) := by
  have h1 := (hEnd w ν hw).1
  exact show D.torusCover w ∈ {x | (D.levelUnitPartition hj h).IsEdgeEndpoint
      (D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν) x} from by
    rw [h1]; exact Or.inl rfl
theorem isEdgeEndpoint_end (hEnd : EdgeEndpointsByLifts hj h) {w : Fin 4 → ℝ} (ν : Fin 4)
    (hw : ∀ μ, w μ ∈ halfLatticeCoset D j) :
    (D.levelUnitPartition hj h).IsEdgeEndpoint
      (D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν)
      (D.torusCover (w + D.physicalCubeSide j • coordVec ν)) := by
  have h1 := (hEnd w ν hw).1
  exact show D.torusCover (w + D.physicalCubeSide j • coordVec ν) ∈
      {x | (D.levelUnitPartition hj h).IsEdgeEndpoint
        (D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν) x} from by
    rw [h1]; exact Or.inr rfl
theorem coordVec_self (ν : Fin 4) : coordVec ν ν = 1 := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.basisVector_apply_self <;> assumption
theorem coordVec_of_ne {μ ν : Fin 4} (hμ : μ ≠ ν) : coordVec ν μ = 0 := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.basisVector_apply_of_ne <;> assumption
theorem edge_eq_of_interior_mem (hTwo : CosetProperties D j) {w w' : Fin 4 → ℝ} {ν ν' : Fin 4}
    (hw : ∀ μ, w μ ∈ halfLatticeCoset D j) (hw' : ∀ μ, w' μ ∈ halfLatticeCoset D j)
    {t t' : ℝ} (ht0 : 0 < t) (ht1 : t < D.physicalCubeSide j) (ht0' : 0 ≤ t')
    (ht1' : t' ≤ D.physicalCubeSide j)
    (hy : D.torusCover (w + t • coordVec ν) = D.torusCover (w' + t' • coordVec ν')) :
    D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν =
      D.torusCover '' Setup.axisSegment w' (D.physicalCubeSide j) ν' := by
  obtain ⟨⟨B, hB⟩, hσ, -⟩ := hTwo
  have hB' : PeriodicLattice.torusSide D.L D.m = D.physicalCubeSide j * (B : ℝ) := hB
  obtain ⟨k, hk⟩ := exists_latticeTranslate (D := D) hy
  have hcoord : ∀ μ, w μ + t * coordVec ν μ =
      w' μ + t' * coordVec ν' μ + D.physicalCubeSide j * (B : ℝ) * (k μ : ℝ) := fun μ => by
    have := congrFun hk μ
    simpa [TestFunctions.latticeTranslate, hB'] using this
  obtain ⟨a, ha⟩ := hw ν
  obtain ⟨a', ha'⟩ := hw' ν
  by_cases hνν : ν' = ν
  · subst hνν
    have h1 := hcoord ν'
    rw [coordVec_self, mul_one, mul_one, ha, ha'] at h1
    have h2 : t - t' = 0 :=
      eq_zero_of_eq_mul_intCast hσ (by linarith) (by linarith) (a' - a + B * k ν') (by
        push_cast; linarith)
    have htt : t = t' := by linarith
    subst htt
    have hww : w = w' + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k := by
      funext μ
      have := hcoord μ
      simp only [Pi.add_apply, TestFunctions.latticeTranslate, hB']
      linarith
    ext y
    constructor
    · rintro ⟨_, ⟨s, hs0, hs1, rfl⟩, rfl⟩
      refine ⟨w' + s • coordVec ν', ⟨s, hs0, hs1, rfl⟩, ?_⟩
      rw [hww, add_right_comm, torusCover_add_latticeTranslate]
    · rintro ⟨_, ⟨s, hs0, hs1, rfl⟩, rfl⟩
      refine ⟨w + s • coordVec ν', ⟨s, hs0, hs1, rfl⟩, ?_⟩
      rw [hww, add_right_comm, torusCover_add_latticeTranslate]
  · exfalso
    have h1 := hcoord ν
    rw [coordVec_self, mul_one, coordVec_of_ne (Ne.symm hνν), mul_zero, add_zero,
      ha, ha'] at h1
    exact ne_mul_intCast_of_pos_of_lt hσ ht0 ht1 (a' - a + B * k ν) (by push_cast; linarith)
theorem isEdgeEndpoint_of_mem_other (hTwo : CosetProperties D j) (hEnd : EdgeEndpointsByLifts hj h)
    {w w' : Fin 4 → ℝ} {ν ν' : Fin 4}
    (hw : ∀ μ, w μ ∈ halfLatticeCoset D j) (hw' : ∀ μ, w' μ ∈ halfLatticeCoset D j)
    (hne : D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν ≠
      D.torusCover '' Setup.axisSegment w' (D.physicalCubeSide j) ν')
    {t t' : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ D.physicalCubeSide j) (ht0' : 0 ≤ t')
    (ht1' : t' ≤ D.physicalCubeSide j)
    (hy : D.torusCover (w + t • coordVec ν) = D.torusCover (w' + t' • coordVec ν')) :
    (D.levelUnitPartition hj h).IsEdgeEndpoint
      (D.torusCover '' Setup.axisSegment w (D.physicalCubeSide j) ν)
      (D.torusCover (w + t • coordVec ν)) := by
  rcases ht0.eq_or_lt with h0 | h0
  · rw [← h0, zero_smul, add_zero]
    exact isEdgeEndpoint_start hEnd ν hw
  rcases ht1.eq_or_lt with h1 | h1
  · rw [h1]
    exact isEdgeEndpoint_end hEnd ν hw
  exact absurd (edge_eq_of_interior_mem hTwo hw hw' h0 h1 ht0' ht1' hy) hne
theorem edgesMeetAtEndpoints_holds (hTwo : CosetProperties D j) (hEdges : EdgeParametrization hj h)
    (hEnd : EdgeEndpointsByLifts hj h) : EdgesMeetAtEndpoints D hj h := by
  intro A A' hA hA' hne y hy
  obtain ⟨w, ν, hw, rfl⟩ := (hEdges A).1 hA
  obtain ⟨w', ν', hw', rfl⟩ := (hEdges A').1 hA'
  obtain ⟨⟨_, ⟨t, ht0, ht1, rfl⟩, hyt⟩, ⟨_, ⟨t', ht0', ht1', rfl⟩, hyt'⟩⟩ := hy
  have h1 := isEdgeEndpoint_of_mem_other hTwo hEnd hw hw' hne ht0 ht1 ht0' ht1'
    (hyt.trans hyt'.symm)
  have h2 := isEdgeEndpoint_of_mem_other hTwo hEnd hw' hw (Ne.symm hne) ht0' ht1' ht0 ht1
    (hyt'.trans hyt.symm)
  rw [hyt] at h1
  rw [hyt'] at h2
  exact ⟨h1, h2⟩
theorem cubeMeetingEdgeContainsEndpoint_holds (hTwo : CosetProperties D j) (hCen : CentreLifts D j)
    (hCube : CubeMembershipByLifts D j) (hEdges : EdgeParametrization hj h)
    (hEnd : EdgeEndpointsByLifts hj h) : CubeMeetingEdgeContainsEndpoint D hj h := by
  intro Q A hQ hA hQA
  obtain ⟨y, hyQ, hyA⟩ := hQA
  obtain ⟨c, rfl⟩ := hQ
  obtain ⟨w, ν, hw, rfl⟩ := (hEdges A).1 hA
  obtain ⟨_, ⟨t, ht0, ht1, rfl⟩, rfl⟩ := hyA
  rcases ht0.eq_or_lt with h0 | h0
  · rw [← h0, zero_smul, add_zero] at hyQ
    exact ⟨_, hyQ, isEdgeEndpoint_start hEnd ν hw⟩
  rcases ht1.eq_or_lt with h1 | h1
  · rw [h1] at hyQ
    exact ⟨_, hyQ, isEdgeEndpoint_end hEnd ν hw⟩
  have hσ : 0 < D.physicalCubeSide j := hTwo.2.1
  obtain ⟨wc, hwc⟩ := exists_liftOfPoint (D := D) (c : D.Torus)
  obtain ⟨w', hw'lift, hI⟩ := (hCube c wc hwc _).1 hyQ
  obtain ⟨k, hk⟩ := exists_latticeTranslate (D := D) hw'lift
  set P := TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k with hP
  have hwc' : D.IsLiftOfPoint (c : D.Torus) (wc - P) := by
    have h2 : D.torusCover (wc - P + P) = D.torusCover (wc - P) :=
      torusCover_add_latticeTranslate _ k
    rw [sub_add_cancel] at h2
    exact h2.symm.trans hwc
  refine ⟨D.torusCover w, (hCube c (wc - P) hwc' _).2 ⟨w, rfl, fun μ => ?_⟩,
    isEdgeEndpoint_start hEnd ν hw⟩
  have hIμ := hI μ
  rw [hk] at hIμ
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mem_Icc] at hIμ ⊢
  by_cases hμν : μ = ν
  · subst hμν
    rw [coordVec_self, mul_one] at hIμ
    obtain ⟨a, ha⟩ := hw μ
    obtain ⟨b, hb⟩ := (hCen (wc - P)).1 ⟨c, hwc'⟩ μ
    simp only [Pi.sub_apply] at hb
    have h3 : w μ - (wc μ - P μ) = D.physicalCubeSide j * (((a - b : ℤ) : ℝ) + 1 / 2) := by
      rw [hb, ha]; push_cast; ring
    have h4 := halfShift_eq_neg_half_of_interior hσ h0 h1 (n := a - b)
      (by rw [← h3]; linarith [hIμ.1]) (by rw [← h3]; linarith [hIμ.2])
    rw [h3, h4]
    constructor <;> linarith
  · rw [coordVec_of_ne hμν, mul_zero, add_zero] at hIμ
    constructor <;> linarith [hIμ.1, hIμ.2]
end Edges
theorem cubeDistanceBounds_holds {hj : j ≤ D.K} {h : D.LevelFits j} (hTwo : CosetProperties D j)
    (hEdges : EdgeParametrization hj h) (hEnd : EdgeEndpointsByLifts hj h) (hCmp : NormComparison D)
    (hLaws : MetricAxioms D) (hCov : ProjNonexpanding D) :
    CubeDistanceBounds D hj h := by
  have hσ : 0 < D.physicalCubeSide j := hTwo.2.1
  have hside : meshSize D.L (D.cubeScaleIndex j) = D.physicalCubeSide j :=
    (Setup.cubeSide_mul_meshSize j).symm
  have hhalf : ∀ (c : Site D.L D.m (D.cubeScaleIndex j)) (x : D.Torus), x ∈ D.cubeCentredAt c →
      TorusMetric.torusSupNorm (x - (c : D.Torus)) ≤ D.physicalCubeSide j / 2 := fun c x hx => by
    rw [← hside]; exact hx
  have hin : ∀ (c : Site D.L D.m (D.cubeScaleIndex j)) (x y : D.Torus), x ∈ D.cubeCentredAt c →
      y ∈ D.cubeCentredAt c → TorusMetric.torusSupNorm (x - y) ≤ D.physicalCubeSide j :=
    fun c x y hx hy => by
    have h1 := hhalf c x hx
    have h2 := hhalf c y hy
    have h3 := (hLaws x (c : D.Torus) y).2.2.1
    have h4 := (hLaws y (c : D.Torus) y).1
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rintro Q ⟨c, rfl⟩ x hx y hy
    exact hin c x y hx hy
  · rintro c Q ⟨c', rfl⟩ ⟨u, huQ, huc⟩ q hq
    have h1 := hin c' q u hq huQ
    have h2 := hhalf c u huc
    refine ⟨?_, fun y hy => ?_⟩
    · have h3 := (hLaws q u (c : D.Torus)).2.2.1
      linarith
    · have h3 := hin c u y huc hy
      have h4 := (hLaws q u y).2.2.1
      have h5 := (hCmp (q - y)).2
      exact ⟨by linarith, by linarith⟩
  · intro A hA u u' hu hu'
    obtain ⟨w, ν, hw, rfl⟩ := (hEdges A).1 hA
    have h1 := (hEnd w ν hw).1
    have hu2 := h1.subset hu
    have hu2' := h1.subset hu'
    have hsame : ∀ x : Fin 4 → ℝ,
        TorusMetric.torusEuclidNorm (D.torusCover x - D.torusCover x) ≤ D.physicalCubeSide j :=
      fun x => by
      have h2 := (hCov x x).2
      have h3 : Setup.l2Norm (x - x) = 0 := by
        rw [sub_self]; simp [TorusMetric.euclidNormVec]
      linarith
    have hone : TorusMetric.torusEuclidNorm
        (D.torusCover (w + D.physicalCubeSide j • coordVec ν) - D.torusCover w) ≤
          D.physicalCubeSide j := by
      have h2 := (hCov (w + D.physicalCubeSide j • coordVec ν) w).2
      have h3 : Setup.l2Norm ((w + D.physicalCubeSide j • coordVec ν) - w) =
          D.physicalCubeSide j := by
        refine euclidNormVec_of_single_axis hσ.le _ ν (fun μ => ?_)
        by_cases hμ : μ = ν
        · subst hμ
          simp [coordVec_self]
        · simp [coordVec_of_ne hμ, hμ]
      linarith
    rcases hu2 with rfl | rfl <;> rcases hu2' with rfl | rfl
    · exact hsame _
    · have := (hLaws (D.torusCover w) (D.torusCover (w + D.physicalCubeSide j • coordVec ν))
        (D.torusCover w)).2.1
      linarith
    · exact hone
    · exact hsame _
theorem cubeCountNearPoint_holds (hTwo : CosetProperties D j) (hCen : CentreLifts D j)
    (hMin : NormMinimaAttained D) : CubeCountNearPoint D j := by
  intro y₀ ρ' hρ
  have hσ : 0 < D.physicalCubeSide j := hTwo.2.1
  obtain ⟨w₀, hw₀⟩ := exists_liftOfPoint (D := D) y₀
  let I : Fin 4 → Finset ℤ := fun μ =>
    Finset.Icc ⌈(w₀ μ - ρ') / D.physicalCubeSide j⌉ ⌊(w₀ μ + ρ') / D.physicalCubeSide j⌋
  let P : Finset (Fin 4 → ℤ) := Fintype.piFinset I
  let G : (Fin 4 → ℤ) → Set D.Torus := fun n =>
    {x | TorusMetric.torusSupNorm
        (x - D.torusCover (fun μ => D.physicalCubeSide j * (n μ : ℝ))) ≤
      meshSize D.L (D.cubeScaleIndex j) / 2}
  have hsub : cubesWithinSupDist D j y₀ ρ' ⊆ G '' (P : Set (Fin 4 → ℤ)) := by
    rintro Q ⟨c, rfl, hc⟩
    obtain ⟨⟨d, hd, hde⟩, -⟩ := (hMin ((c : D.Torus) - y₀)).1
    have hd' : D.torusCover d = (c : D.Torus) - y₀ := hd
    have hwc : D.IsLiftOfPoint (c : D.Torus) (w₀ + d) := by
      have h1 : D.torusCover (w₀ + d) = D.torusCover w₀ + D.torusCover d :=
        (torusCover_add _ _).symm
      have h2 : D.torusCover w₀ = y₀ := hw₀
      show D.torusCover (w₀ + d) = (c : D.Torus)
      rw [h1, h2, hd']
      abel
    have hint := (hCen (w₀ + d)).1 ⟨c, hwc⟩
    choose n hn using hint
    have hle : ∀ μ, |d μ| ≤ ρ' := fun μ => by
      have h1 : |d μ| ≤ TorusMetric.supNormVec d :=
        Finset.le_sup' (fun μ => |d μ|) (Finset.mem_univ μ)
      linarith [hde.le]
    have hnP : n ∈ P := by
      refine Fintype.mem_piFinset.2 (fun μ => Finset.mem_Icc.2 ⟨?_, ?_⟩)
      · refine Int.ceil_le.2 ?_
        rw [div_le_iff₀ hσ]
        have h1 := hn μ
        have h2 := (abs_le.1 (hle μ)).1
        simp only [Pi.add_apply] at h1
        nlinarith
      · refine Int.le_floor.2 ?_
        rw [le_div_iff₀ hσ]
        have h1 := hn μ
        have h2 := (abs_le.1 (hle μ)).2
        simp only [Pi.add_apply] at h1
        nlinarith
    refine ⟨n, hnP, ?_⟩
    have hcov : D.torusCover (fun μ => D.physicalCubeSide j * (n μ : ℝ)) = (c : D.Torus) := by
      have h1 : (fun μ => D.physicalCubeSide j * (n μ : ℝ)) = w₀ + d := by
        funext μ
        exact (hn μ).symm
      rw [h1]
      exact hwc
    ext x
    simp only [G, hcov]
    rfl
  have hfin : (G '' (P : Set (Fin 4 → ℤ))).Finite := P.finite_toSet.image G
  refine ⟨hfin.subset hsub, ?_⟩
  have hcard : (cubesWithinSupDist D j y₀ ρ').ncard ≤ P.card := by
    calc (cubesWithinSupDist D j y₀ ρ').ncard ≤ (G '' (P : Set (Fin 4 → ℤ))).ncard :=
          ncard_le_ncard hsub hfin
      _ ≤ (P : Set (Fin 4 → ℤ)).ncard := ncard_image_le P.finite_toSet
      _ = P.card := ncard_coe_finset P
  have hI : ∀ μ, (((I μ).card : ℕ) : ℝ) ≤ 2 * ρ' / D.physicalCubeSide j + 1 := fun μ => by
    have hab : (w₀ μ - ρ') / D.physicalCubeSide j ≤ (w₀ μ + ρ') / D.physicalCubeSide j := by
      apply div_le_div_of_nonneg_right _ hσ.le
      linarith
    have h1 := card_Icc_ceil_floor_le hab
    have h2 : (w₀ μ + ρ') / D.physicalCubeSide j - (w₀ μ - ρ') / D.physicalCubeSide j =
        2 * ρ' / D.physicalCubeSide j := by ring
    rw [h2] at h1
    exact h1
  calc ((cubesWithinSupDist D j y₀ ρ').ncard : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hcard
    _ = ∏ μ, (((I μ).card : ℕ) : ℝ) := by
        rw [Fintype.card_piFinset]
        push_cast
        rfl
    _ ≤ ∏ _μ : Fin 4, (2 * ρ' / D.physicalCubeSide j + 1) :=
        Finset.prod_le_prod (fun μ _ => Nat.cast_nonneg _) (fun μ _ => hI μ)
    _ = (2 * ρ' / D.physicalCubeSide j + 1) ^ 4 := by simp
theorem holds_of_cosetsAndDistances (hL : CosetsAndDistancesStatement) : Holds := by
  intro D j hj h
  obtain ⟨hTwo, hCen, hCube, hCorner, hV, hEdges, -, -, hEnd, hMin, hCmp, hLaws, hCov, -⟩ :=
    hL D j hj h
  exact ⟨vertexCubeIncidence_holds hj h hTwo hCen hCube hCorner hV,
    edgesMeetAtEndpoints_holds hTwo hEdges hEnd,
    cubeMeetingEdgeContainsEndpoint_holds hTwo hCen hCube hEdges hEnd,
    cubeDistanceBounds_holds hTwo hEdges hEnd hCmp hLaws hCov,
    cubeCountNearPoint_holds hTwo hCen hMin⟩
end TorusBound.PartitionCells
end YangMills.Construction
end
