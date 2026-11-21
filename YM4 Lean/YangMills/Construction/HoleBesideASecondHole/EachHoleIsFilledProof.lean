import YangMills.Construction.HoleBesideASecondHole.CoreAndHolesAsSites
import YangMills.Construction.PeriodicLattice.WilsonMeasureIsometryInvarianceProof
import YangMills.Construction.ColdChainAtEveryLevel.PlaquettesNearAPoint
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyAtTheLeastChartProof
import YangMills.Construction.HoleBesideASecondHole.AShellIsFilled
import YangMills.Construction.HoleBesideASecondHole.DistancesBlocksAndLumpsProof
import YangMills.Construction.HoleBesideASecondHole.EachHoleIsFilled
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LatticeFractionalIntegration LumpContours ShellFilling Holes
namespace HoleFilling
variable {F : BlockFrame}
abbrev LatticePoint : Type := LatticeFractionalIntegration.Lattice4
def fineScale (F : BlockFrame) : ℕ := F.blockSide ^ F.depth
theorem odd_fineScale (hL : Odd F.blockSide) : Odd (fineScale F) := hL.pow
theorem period_depth (i : Fin 4) : F.period F.depth i = F.extent i * F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimizingChart.period_depth <;> assumption
theorem period_zero (i : Fin 4) : F.period 0 i = F.period F.depth i * fineScale F := by
  rw [period_depth]
  simp only [BlockFrame.period, BlockFrame.top, Nat.sub_zero, fineScale, pow_succ]
  ring
theorem siteCoords_cast {j : ℕ} (x : F.Site j) (i : Fin 4) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.siteCoords_cast <;> assumption
theorem mem_centredCube_iff {M : ℕ} {o : Fin 4 → ℤ} : o ∈ centredCube M ↔ ∀ m, |o m| ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.mem_centredCube_iff <;> assumption
theorem two_mul_half_add_one {L : ℕ} (hL : Odd L) : 2 * (((L : ℤ) - 1) / 2) + 1 = L := by apply _root_.YangMills.Construction.LumpContours.two_mul_half_pred_add_one_of_odd <;> assumption
def embedOffset (o : F.Site F.depth) (v : LatticePoint) : F.Site 0 :=
  siteOfCoords 0 fun i => (fineScale F : ℤ) * siteCoords o i + v i
theorem embedOffset_add (o : F.Site F.depth) (v d : LatticePoint) :
    embedOffset o (v + d) = embedOffset o v + siteOfCoords 0 d := by
  funext i
  simp [embedOffset, siteOfCoords, add_assoc]
theorem embedOffset_add_basisVector (o : F.Site F.depth) (v : LatticePoint) (i : Fin 4) :
    embedOffset o (v + basisVector i) = embedOffset o v + unitStep 0 i := by
  rw [embedOffset_add]
  rfl
def leastOffset (o : F.Site F.depth) (z : F.Site 0) : LatticePoint :=
  fun i => (z i - siteOfCoords 0 (fun k => (fineScale F : ℤ) * siteCoords o k) i).valMinAbs
theorem leastOffset_embedOffset (hp : ∀ i, 0 < F.period 0 i) (o : F.Site F.depth) (v : LatticePoint)
    (hv : ∀ i, 2 * |v i| < (F.period 0 i : ℤ)) : leastOffset o (embedOffset o v) = v := by
  funext i
  haveI : NeZero (F.period 0 i) := ⟨(hp i).ne'⟩
  have e : (embedOffset o v) i - siteOfCoords 0 (fun k => (fineScale F : ℤ) * siteCoords o k) i =
      ((v i : ℤ) : ZMod (F.period 0 i)) := by
    simp [embedOffset, siteOfCoords]
  simp only [leastOffset, e]
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  have h1 := hv i
  have h2 := le_abs_self (v i)
  have h3 := neg_abs_le (v i)
  constructor <;> omega
theorem siteOfCoords_eq_embedOffset (o : F.Site F.depth) (e r : LatticePoint) :
    (siteOfCoords 0 (fun k => (F.blockSide : ℤ) ^ (F.depth - 0) *
        siteCoords (o + siteOfCoords F.depth e : F.Site F.depth) k + r k) : F.Site 0) =
      embedOffset o (fun k => (fineScale F : ℤ) * e k + r k) := by
  funext i
  simp only [embedOffset, siteOfCoords]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have hd : ((F.period F.depth i : ℕ) : ℤ) ∣
      (siteCoords o i + e i) - siteCoords (o + siteOfCoords F.depth e : F.Site F.depth) i := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, siteCoords_cast]
    simp [siteOfCoords, siteCoords_cast]
  obtain ⟨q, hq⟩ := hd
  refine ⟨q, ?_⟩
  rw [period_zero]
  simp only [fineScale, Nat.sub_zero]
  push_cast
  linear_combination ((F.blockSide : ℤ) ^ F.depth) * hq
theorem embedOffset_mem_sitesBelow (o : F.Site F.depth) (e r : LatticePoint)
    (hr : ∀ i, |r i| ≤ ((fineScale F : ℤ) - 1) / 2) :
    embedOffset o (fun k => (fineScale F : ℤ) * e k + r k) ∈
      sitesBelow 0 (o + siteOfCoords F.depth e : F.Site F.depth) := by
  unfold sitesBelow
  refine Finset.mem_image.2 ⟨r, ?_, siteOfCoords_eq_embedOffset o e r⟩
  rw [mem_centredCube_iff]
  simpa [fineScale] using hr
theorem eq_of_mem_sitesBelow (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {z : F.Site 0}
    {x x' : F.Site F.depth} (h : z ∈ sitesBelow 0 x) (h' : z ∈ sitesBelow 0 x') : x = x' := by
  unfold sitesBelow at h h'
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
  obtain ⟨b, hb, hab⟩ := Finset.mem_image.1 h'
  have hMp : (0 : ℤ) < fineScale F := by exact_mod_cast (odd_fineScale hL).pos
  have hM2 := two_mul_half_add_one (odd_fineScale hL)
  have ha' := mem_centredCube_iff.1 ha
  have hb' := mem_centredCube_iff.1 hb
  simp only [Nat.sub_zero] at ha' hb'
  funext i
  have e1 := congrFun hab i
  simp only [siteOfCoords] at e1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at e1
  obtain ⟨q, hq⟩ := e1
  rw [period_zero] at hq
  simp only [Nat.sub_zero] at hq
  push_cast at hq
  set M : ℤ := (fineScale F : ℤ) with hM
  have hML : (F.blockSide : ℤ) ^ F.depth = M := by simp [hM, fineScale]
  rw [hML] at hq
  have hai := ha' i
  have hbi := hb' i
  have hML2 : (((F.blockSide ^ F.depth : ℕ) : ℤ) - 1) / 2 = (M - 1) / 2 := by simp [hM, fineScale]
  rw [hML2] at hai hbi
  rw [abs_le] at hai hbi
  have d1 : M ∣ a i - b i := by
    refine ⟨siteCoords x' i - siteCoords x i + (F.period F.depth i : ℤ) * q, ?_⟩
    linear_combination hq
  have d2 : a i - b i = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd d1 ?_
    rw [abs_lt]
    constructor <;> omega
  have d3 : M * (siteCoords x' i - siteCoords x i + (F.period F.depth i : ℤ) * q) = 0 := by
    linear_combination d2 - hq
  have d4 : siteCoords x' i - siteCoords x i + (F.period F.depth i : ℤ) * q = 0 :=
    (mul_eq_zero.1 d3).resolve_left hMp.ne'
  rw [← siteCoords_cast x i, ← siteCoords_cast x' i, ZMod.intCast_eq_intCast_iff_dvd_sub]
  exact ⟨-q, by linear_combination d4⟩
def ballRadius (H : Hole F) : ℝ := ((H.radius : ℝ) + 1) * (fineScale F : ℝ)
open Classical in
def latticeBall (l : ℝ) : Finset LatticePoint :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-⌈2 * l⌉) ⌈2 * l⌉).filter (IsWithinSupDist 0 (1.95 * l))
theorem mem_latticeBall {l : ℝ} (hl : 0 ≤ l) (x : LatticePoint) :
    x ∈ latticeBall l ↔ IsWithinSupDist 0 (1.95 * l) x := by
  classical
  unfold latticeBall
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, and_iff_right_iff_imp]
  intro h i
  have h1 := h i
  simp only [Pi.zero_apply, sub_zero] at h1
  have h2 : |(x i : ℝ)| ≤ 2 * l := by linarith
  rw [abs_le] at h2
  have h3 : (x i : ℝ) ≤ ⌈2 * l⌉ := h2.2.trans (Int.le_ceil _)
  have h4 : -((⌈2 * l⌉ : ℤ) : ℝ) ≤ x i := by
    have := Int.le_ceil (2 * l)
    linarith [h2.1]
  constructor
  · have : ((-⌈2 * l⌉ : ℤ) : ℝ) ≤ x i := by push_cast; exact h4
    exact_mod_cast this
  · exact_mod_cast h3
theorem ballRadius_nonneg (H : Hole F) : 0 ≤ ballRadius H := by
  unfold ballRadius
  positivity
theorem isWithin_iff_int (H : Hole F) (x : LatticePoint) :
    IsWithinSupDist 0 (1.95 * ballRadius H) x ↔
      ∀ i, 100 * |x i| ≤ 195 * (((H.radius : ℤ) + 1) * (fineScale F : ℤ)) := by
  refine forall_congr' fun i => ?_
  simp only [Pi.zero_apply, sub_zero, ballRadius]
  have e : ((|x i| : ℤ) : ℝ) = |(x i : ℝ)| := by push_cast; rfl
  rw [← e]
  constructor
  · intro h
    have : ((100 * |x i| : ℤ) : ℝ) ≤ ((195 * (((H.radius : ℤ) + 1) * (fineScale F : ℤ)) : ℤ) : ℝ) := by
      push_cast
      push_cast at h
      linarith
    exact_mod_cast this
  · intro h
    have : ((100 * |x i| : ℤ) : ℝ) ≤ ((195 * (((H.radius : ℤ) + 1) * (fineScale F : ℤ)) : ℤ) : ℝ) := by
      exact_mod_cast h
    push_cast at this
    push_cast
    linarith
theorem isBeyond_iff_int (H : Hole F) (x : LatticePoint) :
    IsBeyondSupDist 0 (ballRadius H) x ↔ ∃ i, ((H.radius : ℤ) + 1) * (fineScale F : ℤ) ≤ |x i| := by
  refine exists_congr fun i => ?_
  simp only [Pi.zero_apply, sub_zero, ballRadius]
  have e : ((|x i| : ℤ) : ℝ) = |(x i : ℝ)| := by push_cast; rfl
  rw [← e]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h
theorem isBeyond_of_int (H : Hole F) (x : LatticePoint)
    (h : ∃ i, 190 * (((H.radius : ℤ) + 1) * (fineScale F : ℤ)) ≤ 100 * |x i|) :
    IsBeyondSupDist 0 (1.9 * ballRadius H) x := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  simp only [Pi.zero_apply, sub_zero, ballRadius]
  have e : ((|x i| : ℤ) : ℝ) = |(x i : ℝ)| := by push_cast; rfl
  rw [← e]
  have : ((190 * (((H.radius : ℤ) + 1) * (fineScale F : ℤ)) : ℤ) : ℝ) ≤ ((100 * |x i| : ℤ) : ℝ) := by
    exact_mod_cast hi
  push_cast at this
  push_cast
  linarith
theorem exists_split_offset (hM : Odd (fineScale F)) (c : ℤ) :
    ∃ e r : ℤ, c = (fineScale F : ℤ) * e + r ∧ |r| ≤ ((fineScale F : ℤ) - 1) / 2 ∧
      e = (c + ((fineScale F : ℤ) - 1) / 2) / (fineScale F : ℤ) := by
  have h2 := two_mul_half_add_one hM
  have hp : (0 : ℤ) < fineScale F := by exact_mod_cast hM.pos
  set H : ℤ := ((fineScale F : ℤ) - 1) / 2
  have a1 := Int.emod_add_mul_ediv (c + H) (fineScale F : ℤ)
  have a2 := Int.emod_nonneg (c + H) hp.ne'
  have a3 := Int.emod_lt_of_pos (c + H) hp
  refine ⟨(c + H) / (fineScale F : ℤ), c - (fineScale F : ℤ) * ((c + H) / (fineScale F : ℤ)), by ring, ?_, rfl⟩
  rw [abs_le]
  constructor <;> linarith
theorem abs_fine_le (hM : Odd (fineScale F)) {c e r R : ℤ} (hR : 99 ≤ R) (hc : c = (fineScale F : ℤ) * e + r)
    (hr : |r| ≤ ((fineScale F : ℤ) - 1) / 2) (hb : 100 * |c| ≤ 195 * ((R + 1) * (fineScale F : ℤ))) :
    |e| ≤ 2 * R := by
  have h2 := two_mul_half_add_one hM
  have hp : (0 : ℤ) < fineScale F := by exact_mod_cast hM.pos
  set M : ℤ := (fineScale F : ℤ)
  set H : ℤ := (M - 1) / 2
  rw [abs_le] at hr
  have c1 := le_abs_self c
  have c2 := neg_abs_le c
  rw [abs_le]
  constructor
  · by_contra hcon
    push_neg at hcon
    have : M * (e + 2 * R + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp.le (by omega)
    nlinarith [mul_pos hp (show (0 : ℤ) < R - 90 by omega)]
  · by_contra hcon
    push_neg at hcon
    have : 0 ≤ M * (e - 2 * R - 1) := mul_nonneg hp.le (by omega)
    nlinarith [mul_pos hp (show (0 : ℤ) < R - 90 by omega)]
theorem abs_fine_ge (hM : Odd (fineScale F)) {c e r R : ℤ} (hR : 0 ≤ R) (hc : c = (fineScale F : ℤ) * e + r)
    (hr : |r| ≤ ((fineScale F : ℤ) - 1) / 2) (hb : (R + 1) * (fineScale F : ℤ) ≤ |c|) : R + 1 ≤ |e| := by
  have h2 := two_mul_half_add_one hM
  have hp : (0 : ℤ) < fineScale F := by exact_mod_cast hM.pos
  set M : ℤ := (fineScale F : ℤ)
  set H : ℤ := (M - 1) / 2
  rw [abs_le] at hr
  by_contra hcon
  push_neg at hcon
  have h3 : |e| ≤ R := by omega
  rw [abs_le] at h3
  have hc' : |c| < (R + 1) * M := by
    rw [abs_lt, hc]
    constructor <;> nlinarith
  omega
open Classical in
def torusBall (H : Hole F) : Finset (F.Site 0) := (latticeBall (ballRadius H)).image (embedOffset H.centre)
theorem mem_latticeBall_iff_int (H : Hole F) (v : LatticePoint) :
    v ∈ latticeBall (ballRadius H) ↔ ∀ i, 100 * |v i| ≤ 195 * (((H.radius : ℤ) + 1) * (fineScale F : ℤ)) :=
  (mem_latticeBall (ballRadius_nonneg H) v).trans (isWithin_iff_int H v)
theorem odd_nat_half (m : ℕ) : (((2 * m + 1 : ℕ) : ℤ) - 1) / 2 = m := by
  push_cast
  omega
theorem add_mem_thicken_singleton {o : F.Site F.depth} {e : LatticePoint} {m : ℕ} (he : ∀ i, |e i| ≤ (m : ℤ)) :
    (o + siteOfCoords F.depth e : F.Site F.depth) ∈ thicken m {o} := by
  unfold thicken
  rw [Finset.singleton_biUnion]
  refine Finset.mem_image.2 ⟨e, ?_, rfl⟩
  rw [mem_centredCube_iff, odd_nat_half]
  exact he
theorem exists_of_mem_thicken_singleton {o x : F.Site F.depth} {m : ℕ} (hx : x ∈ thicken m {o}) :
    ∃ e : LatticePoint, (∀ i, |e i| ≤ (m : ℤ)) ∧ x = o + siteOfCoords F.depth e := by
  unfold thicken at hx
  rw [Finset.singleton_biUnion] at hx
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
  rw [mem_centredCube_iff, odd_nat_half] at he
  exact ⟨e, he, rfl⟩
theorem embedOffset_mem_cutBelow_outer (hL : Odd F.blockSide) (H : Hole F) (hR : 99 ≤ H.radius) {v : LatticePoint}
    (hv : v ∈ latticeBall (ballRadius H)) : embedOffset H.centre v ∈ cutBelow 0 H.outerBox := by
  choose e r hc hr _ using fun i => exists_split_offset (odd_fineScale hL) (v i)
  have hvv : v = fun k => (fineScale F : ℤ) * e k + r k := funext hc
  have hb := (mem_latticeBall_iff_int H v).1 hv
  unfold cutBelow
  refine Finset.mem_biUnion.2 ⟨H.centre + siteOfCoords F.depth e, ?_, ?_⟩
  · refine add_mem_thicken_singleton fun i => ?_
    have := abs_fine_le (odd_fineScale hL) (R := (H.radius : ℤ)) (by exact_mod_cast hR) (hc i) (hr i) (hb i)
    push_cast
    exact this
  · rw [hvv]
    exact embedOffset_mem_sitesBelow _ e r hr
theorem period_depth_ge (hL : Odd F.blockSide) (hs : ∀ i, 64 ≤ F.extent i) (i : Fin 4) :
    64 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ) := by
  rw [period_depth]
  push_cast
  have : (64 : ℤ) ≤ F.extent i := by exact_mod_cast hs i
  nlinarith
theorem period_zero_ge (hL : Odd F.blockSide) (hs : ∀ i, 64 ≤ F.extent i) (i : Fin 4) :
    64 * ((F.blockSide : ℤ) * (fineScale F : ℤ)) ≤ (F.period 0 i : ℤ) := by
  rw [period_zero]
  push_cast
  have h1 := period_depth_ge hL hs i
  nlinarith
theorem embedOffset_mem_cutBelow_annulus (hL : Odd F.blockSide) (hs : ∀ i, 64 ≤ F.extent i) (H : Hole F)
    (hR : 99 ≤ H.radius) (hRL : H.radius + 1 ≤ F.blockSide) {v : LatticePoint} (hv : v ∈ latticeBall (ballRadius H))
    (hf : ∃ i, ((H.radius : ℤ) + 1) * (fineScale F : ℤ) ≤ |v i|) :
    embedOffset H.centre v ∈ cutBelow 0 H.annulus := by
  choose e r hc hr _ using fun i => exists_split_offset (odd_fineScale hL) (v i)
  have hvv : v = fun k => (fineScale F : ℤ) * e k + r k := funext hc
  have hb := (mem_latticeBall_iff_int H v).1 hv
  have he2 : ∀ i, |e i| ≤ 2 * (H.radius : ℤ) := fun i =>
    abs_fine_le (odd_fineScale hL) (R := (H.radius : ℤ)) (by exact_mod_cast hR) (hc i) (hr i) (hb i)
  obtain ⟨i₀, hi₀⟩ := hf
  have hfar := abs_fine_ge (odd_fineScale hL) (R := (H.radius : ℤ)) (by positivity) (hc i₀) (hr i₀) hi₀
  unfold cutBelow
  refine Finset.mem_biUnion.2 ⟨H.centre + siteOfCoords F.depth e, ?_, ?_⟩
  · unfold Hole.annulus
    refine Finset.mem_sdiff.2 ⟨add_mem_thicken_singleton fun i => ?_, fun hin => ?_⟩
    · push_cast
      exact he2 i
    · obtain ⟨e', he', heq⟩ := exists_of_mem_thicken_singleton hin
      have h1 := congrFun (add_left_cancel heq) i₀
      simp only [siteOfCoords] at h1
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
      have hb1 := period_depth_ge hL hs i₀
      have h0 : e' i₀ - e i₀ = 0 := by
        refine Int.eq_zero_of_abs_lt_dvd h1 ?_
        have a1 := he2 i₀
        have a2 := he' i₀
        rw [abs_le] at a1 a2
        rw [abs_lt]
        constructor <;> omega
      have : e' i₀ = e i₀ := by omega
      have a2 := he' i₀
      rw [this] at a2
      omega
  · rw [hvv]
    exact embedOffset_mem_sitesBelow _ e r hr
theorem exists_offset_of_mem_cutBelow_inner (hL : Odd F.blockSide) (H : Hole F) {z : F.Site 0}
    (hz : z ∈ cutBelow 0 H.innerBox) :
    ∃ v : LatticePoint, embedOffset H.centre v = z ∧ ∀ i, |v i| < ((H.radius : ℤ) + 1) * (fineScale F : ℤ) := by
  unfold cutBelow at hz
  obtain ⟨f, hf, hzf⟩ := Finset.mem_biUnion.1 hz
  obtain ⟨e, he, rfl⟩ := exists_of_mem_thicken_singleton hf
  unfold sitesBelow at hzf
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hzf
  refine ⟨fun k => (fineScale F : ℤ) * e k + h k, (siteOfCoords_eq_embedOffset _ e h).symm, fun i => ?_⟩
  have hM2 := two_mul_half_add_one (odd_fineScale hL)
  have hp : (0 : ℤ) < fineScale F := by exact_mod_cast (odd_fineScale hL).pos
  have h1 := mem_centredCube_iff.1 hh i
  simp only [Nat.sub_zero] at h1
  have h3 : (((F.blockSide ^ F.depth : ℕ) : ℤ) - 1) / 2 = ((fineScale F : ℤ) - 1) / 2 := by simp [fineScale]
  rw [h3] at h1
  have h2 := he i
  rw [abs_le] at h1 h2
  rw [abs_lt]
  constructor <;> nlinarith
theorem plaquetteHolonomy_eq {j : ℕ} (U : F.GaugeField j) (x : F.Site j) (μ ν : Fin 4) :
    plaquetteHolonomy U (x, μ, ν) =
      U x μ * U (x + unitStep j μ) ν * (U (x + unitStep j ν) μ)⁻¹ * (U x ν)⁻¹ := by apply _root_.YangMills.Construction.PlaquetteExpansion.plaquetteHolonomy_eq <;> assumption
theorem plaquetteHolonomy_embedOffset (U : F.GaugeField 0) (o : F.Site F.depth) (v : LatticePoint) (μ ν : Fin 4) :
    plaquetteHolonomy U (embedOffset o v, μ, ν) = latticePlaquette (fun v i => U (embedOffset o v) i) v μ ν := by
  rw [plaquetteHolonomy_eq]
  simp only [latticePlaquette, embedOffset_add_basisVector]
theorem norm_sub_one_sq_eq (g : UnitQuaternion) : ‖(g : ℍ[ℝ]) - 1‖ ^ 2 = 2 - 2 * ((g : ℍ[ℝ])).re := by apply _root_.YangMills.Construction.GaugeFixing.norm_coe_sub_one_sq <;> assumption
theorem plaquetteEnergy_eq (U : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) :
    plaquetteEnergy U p = ‖((plaquetteHolonomy U p : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 / 2 := by
  rw [norm_sub_one_sq_eq]
  unfold plaquetteEnergy
  ring
theorem plaquetteEnergy_nonneg (U : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) : 0 ≤ plaquetteEnergy U p := by apply _root_.YangMills.Construction.LumpContours.CutAction.plaquetteEnergy_nonneg <;> assumption
theorem norm_inv_sub_one (g : UnitQuaternion) : ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
theorem latticePlaquette_swap (X : LatticePoint → Fin 4 → UnitQuaternion) (v : LatticePoint) (μ ν : Fin 4) :
    latticePlaquette X v ν μ = (latticePlaquette X v μ ν)⁻¹ := by
  simp only [latticePlaquette, mul_inv_rev, inv_inv, mul_assoc]
theorem exists_of_mem_plaquetteCorners {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) (hp : p.2.1 ≠ p.2.2) {x : F.Site j}
    (hx : x ∈ plaquetteCorners p) :
    ∃ δ : LatticePoint, (∀ k, 0 ≤ δ k ∧ δ k ≤ 1) ∧ x = p.1 + siteOfCoords j δ := by apply _root_.YangMills.Construction.HoleSites.exists_offset_of_mem_plaquetteCorners <;> assumption
theorem exists_diff_of_mem_plaquetteCorners {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) (hp : p.2.1 ≠ p.2.2)
    {x y : F.Site j} (hx : x ∈ plaquetteCorners p) (hy : y ∈ plaquetteCorners p) :
    ∃ d : LatticePoint, (∀ k, |d k| ≤ 1) ∧ y = x + siteOfCoords j d := by apply _root_.YangMills.Construction.HoleSites.exists_step_of_mem_plaquetteCorners <;> assumption
open Classical in
def torusBallPlaquettes (H : Hole F) : Finset (F.Site 0 × Fin 4 × Fin 4) :=
  ((orientedPlaquettesOf (latticeBall (ballRadius H))).filter fun p => p.2.1 < p.2.2).image
    (fun p => (embedOffset H.centre p.1, p.2.1, p.2.2))
theorem abs_add_lt_period (hL : Odd F.blockSide) (hs : ∀ i, 64 ≤ F.extent i) (H : Hole F)
    (hRL : H.radius + 1 ≤ F.blockSide) {v : LatticePoint}
    (hv : ∀ i, 100 * |v i| ≤ 195 * (((H.radius : ℤ) + 1) * (fineScale F : ℤ))) (d : LatticePoint)
    (hd : ∀ i, |d i| ≤ 1) (i : Fin 4) : 8 * |v i + d i| < (F.period 0 i : ℤ) := by
  have h1 := period_zero_ge hL hs i
  have hM : (0 : ℤ) < fineScale F := by exact_mod_cast (odd_fineScale hL).pos
  have h3 : ((H.radius : ℤ) + 1) ≤ F.blockSide := by exact_mod_cast hRL
  have h4 : ((H.radius : ℤ) + 1) * (fineScale F : ℤ) ≤ (F.blockSide : ℤ) * (fineScale F : ℤ) :=
    mul_le_mul_of_nonneg_right h3 hM.le
  have h5 := hv i
  have h6 := hd i
  have h7 := abs_add_le (v i) (d i)
  have h8 : (1 : ℤ) ≤ (F.blockSide : ℤ) * (fineScale F : ℤ) := by
    have : (1 : ℤ) ≤ F.blockSide := by exact_mod_cast hL.pos
    nlinarith
  omega
theorem embedOffset_injective (hp : ∀ i, 0 < F.period 0 i) (o : F.Site F.depth) {v w : LatticePoint}
    (hv : ∀ i, 4 * |v i| < (F.period 0 i : ℤ)) (hw : ∀ i, 4 * |w i| < (F.period 0 i : ℤ))
    (h : embedOffset o v = embedOffset o w) : v = w := by
  have a : ∀ i, 2 * |v i| < (F.period 0 i : ℤ) := fun i => by
    have := hv i
    have := abs_nonneg (v i)
    omega
  have b : ∀ i, 2 * |w i| < (F.period 0 i : ℤ) := fun i => by
    have := hw i
    have := abs_nonneg (w i)
    omega
  rw [← leastOffset_embedOffset hp o v a, h, leastOffset_embedOffset hp o w b]
def pullbackField (U : F.GaugeField 0) (o : F.Site F.depth) : LatticePoint → Fin 4 → UnitQuaternion :=
  fun v i => U (embedOffset o v) i
theorem plaquetteDefect_eq_two_mul (X : LatticePoint → Fin 4 → UnitQuaternion) (P : Finset LatticePoint) :
    plaquetteDefect P X = 2 * ∑ p ∈ (orientedPlaquettesOf P).filter (fun p => p.2.1 < p.2.2),
      ‖((latticePlaquette X p.1 p.2.1 p.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 := by
  classical
  unfold ShellFilling.plaquetteDefect
  rw [← Finset.sum_filter_add_sum_filter_not (orientedPlaquettesOf P) (fun p => p.2.1 < p.2.2), two_mul]
  congr 1
  refine Finset.sum_nbij' (fun p => (p.1, p.2.2, p.2.1)) (fun p => (p.1, p.2.2, p.2.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, orientedPlaquettesOf, Finset.mem_product, Finset.mem_univ, and_true,
      not_lt] at hp ⊢
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩ := hp
    refine ⟨⟨h1, fun h => h2 h.symm, h4, h3, ?_⟩, lt_of_le_of_ne h6 fun h => h2 h.symm⟩
    rw [add_right_comm]
    exact h5
  · intro p hp
    simp only [Finset.mem_filter, orientedPlaquettesOf, Finset.mem_product, Finset.mem_univ, and_true,
      not_lt] at hp ⊢
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩ := hp
    refine ⟨⟨h1, fun h => h2 h.symm, h4, h3, ?_⟩, h6.le⟩
    rw [add_right_comm]
    exact h5
  · intro p _
    rfl
  · intro p _
    rfl
  · intro p _
    simp only
    rw [latticePlaquette_swap, norm_inv_sub_one]
theorem plaquetteDefect_shell_le (hL : Odd F.blockSide) (hs : ∀ i, 64 ≤ F.extent i) (H : Hole F)
    (hR : 99 ≤ H.radius) (hRL : H.radius + 1 ≤ F.blockSide) (U : F.GaugeField 0) (Sh : Finset LatticePoint)
    (hSh : ∀ x, x ∈ Sh ↔ x ∈ latticeBall (ballRadius H) ∧ IsBeyondSupDist 0 (ballRadius H) x) :
    plaquetteDefect Sh (pullbackField U H.centre) ≤ 4 * H.annulusEnergy U := by
  classical
  rw [plaquetteDefect_eq_two_mul]
  have hperpos : ∀ i, 0 < F.period 0 i := fun i => by
    have := period_zero_ge hL hs i
    have h1 : (1 : ℤ) ≤ F.blockSide := by exact_mod_cast hL.pos
    have h2 : (1 : ℤ) ≤ fineScale F := by exact_mod_cast (odd_fineScale hL).pos
    have h3 : (0 : ℤ) < (F.period 0 i : ℤ) := by nlinarith
    exact_mod_cast h3
  have key : ∑ p ∈ (orientedPlaquettesOf Sh).filter (fun p => p.2.1 < p.2.2),
      ‖((latticePlaquette (pullbackField U H.centre) p.1 p.2.1 p.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 ≤
        2 * H.annulusEnergy U := by
    have e : ∀ p ∈ (orientedPlaquettesOf Sh).filter (fun p => p.2.1 < p.2.2),
        ‖((latticePlaquette (pullbackField U H.centre) p.1 p.2.1 p.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 =
          2 * plaquetteEnergy U (embedOffset H.centre p.1, p.2.1, p.2.2) := by
      intro p _
      rw [plaquetteEnergy_eq, plaquetteHolonomy_embedOffset]
      have hpull : pullbackField U H.centre = fun v i => U (embedOffset H.centre v) i := rfl
      rw [hpull]
      ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    unfold Hole.annulusEnergy
    have hinj : Set.InjOn (fun p : LatticePoint × Fin 4 × Fin 4 => (embedOffset H.centre p.1, p.2.1, p.2.2))
        ((orientedPlaquettesOf Sh).filter (fun p => p.2.1 < p.2.2) : Finset (LatticePoint × Fin 4 × Fin 4)) := by
      rintro ⟨v, μ, ν⟩ hv ⟨w, μ', ν'⟩ hw h
      simp only [Finset.coe_filter, Set.mem_setOf_eq, orientedPlaquettesOf, Finset.mem_filter, Finset.mem_product,
        Finset.mem_univ, and_true] at hv hw
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, rfl, rfl⟩ := h
      have hv' := (mem_latticeBall_iff_int H v).1 ((hSh v).1 hv.1.1).1
      have hw' := (mem_latticeBall_iff_int H w).1 ((hSh w).1 hw.1.1).1
      have b1 : ∀ i, 4 * |v i| < (F.period 0 i : ℤ) := fun i => by
        have := abs_add_lt_period hL hs H hRL hv' 0 (by simp) i
        simp only [Pi.zero_apply, add_zero] at this
        have := abs_nonneg (v i)
        omega
      have b2 : ∀ i, 4 * |w i| < (F.period 0 i : ℤ) := fun i => by
        have := abs_add_lt_period hL hs H hRL hw' 0 (by simp) i
        simp only [Pi.zero_apply, add_zero] at this
        have := abs_nonneg (w i)
        omega
      rw [embedOffset_injective hperpos H.centre b1 b2 h1]
    rw [← Finset.sum_image (f := fun q => plaquetteEnergy U q) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => plaquetteEnergy_nonneg U q
    intro q hq
    obtain ⟨⟨v, μ, ν⟩, hp, rfl⟩ := Finset.mem_image.1 hq
    simp only [orientedPlaquettesOf, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩ := hp
    have ann : ∀ x ∈ Sh, embedOffset H.centre x ∈ cutBelow 0 H.annulus := fun x hx =>
      embedOffset_mem_cutBelow_annulus hL hs H hR hRL ((hSh x).1 hx).1 ((isBeyond_iff_int H x).1 ((hSh x).1 hx).2)
    simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    refine ⟨ann v h1, h6, ?_⟩
    intro x hx
    simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ann v h1
    · rw [← embedOffset_add_basisVector]; exact ann _ h3
    · rw [← embedOffset_add_basisVector]; exact ann _ h4
    · rw [← embedOffset_add_basisVector, ← embedOffset_add_basisVector]; exact ann _ h5
  linarith
theorem basisVector_bounds (i k : Fin 4) : 0 ≤ (basisVector i : LatticePoint) k ∧ (basisVector i : LatticePoint) k ≤ 1 := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.single_one_bounds <;> assumption
theorem mem_latticeBall_of_near (hM : Odd (fineScale F)) (H : Hole F) (hR : 99 ≤ H.radius) {v w : LatticePoint}
    (hb : ∀ i, |v i| < ((H.radius : ℤ) + 1) * (fineScale F : ℤ)) (hw : ∀ i, |w i - v i| ≤ 2) :
    w ∈ latticeBall (ballRadius H) := by
  rw [mem_latticeBall_iff_int]
  intro i
  have hM1 : (1 : ℤ) ≤ fineScale F := by exact_mod_cast hM.pos
  have h1 := hb i
  have h2 := hw i
  have h3 : |w i| ≤ |w i - v i| + |v i| := by
    have := abs_add_le (w i - v i) (v i)
    simpa using this
  have h5 : (100 : ℤ) ≤ ((H.radius : ℤ) + 1) * (fineScale F : ℤ) := by nlinarith
  omega
theorem isBeyond_of_add_not_mem (hM : Odd (fineScale F)) (H : Hole F) (hR : 99 ≤ H.radius) {w d : LatticePoint}
    (hd : ∀ k, |d k| ≤ 1) (hout : w + d ∉ latticeBall (ballRadius H)) :
    IsBeyondSupDist 0 (1.9 * ballRadius H) w := by
  refine isBeyond_of_int H w ?_
  rw [mem_latticeBall_iff_int] at hout
  push_neg at hout
  obtain ⟨i, hi⟩ := hout
  refine ⟨i, ?_⟩
  have hM1 : (1 : ℤ) ≤ fineScale F := by exact_mod_cast hM.pos
  have h2 := hd i
  have h3 : |(w + d) i| ≤ |w i| + |d i| := abs_add_le _ _
  have h5 : (100 : ℤ) ≤ ((H.radius : ℤ) + 1) * (fineScale F : ℤ) := by nlinarith
  omega
theorem mem_plaquetteCorners_base (z : F.Site 0) (μ ν : Fin 4) : z ∈ plaquetteCorners (z, μ, ν) := by
  simp [plaquetteCorners]
theorem mem_plaquetteCorners_first (z : F.Site 0) (μ ν : Fin 4) :
    z + unitStep 0 μ ∈ plaquetteCorners (z, μ, ν) := by
  simp [plaquetteCorners]
theorem mem_plaquetteCorners_second (z : F.Site 0) (μ ν : Fin 4) :
    z + unitStep 0 ν ∈ plaquetteCorners (z, μ, ν) := by
  simp [plaquetteCorners]
theorem mem_plaquetteCorners_opposite (z : F.Site 0) (μ ν : Fin 4) :
    z + unitStep 0 μ + unitStep 0 ν ∈ plaquetteCorners (z, μ, ν) := by
  simp [plaquetteCorners]
theorem supDist_self {j : ℕ} (x : F.Site j) : supDist x x = 0 := by
  simp [supDist]
theorem eachHoleFilled (hS : shellFillingStatement) : eachHoleFilledStatement := by
  obtain ⟨c, C, hc, hC, hS⟩ := hS
  refine ⟨c, C, hc, hC, ?_⟩
  intro F hL hs 𝓗 U₀ hH hApart
  classical
  have hM := odd_fineScale hL
  have hM1 : (1 : ℤ) ≤ fineScale F := by exact_mod_cast hM.pos
  have hRL : ∀ H ∈ 𝓗, H.radius + 1 ≤ F.blockSide := fun H hh => by
    obtain ⟨a, b, _⟩ := hH H hh
    nlinarith
  have hR : ∀ H ∈ 𝓗, 99 ≤ H.radius := fun H hh => (hH H hh).1
  have hperpos : ∀ i, 0 < F.period 0 i := fun i => by
    have := period_zero_ge hL hs i
    have h1 : (1 : ℤ) ≤ F.blockSide := by exact_mod_cast hL.pos
    have h3 : (0 : ℤ) < (F.period 0 i : ℤ) := by nlinarith
    exact_mod_cast h3
  have hE : ∀ H : Hole F, 0 ≤ H.annulusEnergy U₀ := fun H =>
    Finset.sum_nonneg fun p _ => plaquetteEnergy_nonneg U₀ p
  have hl : ∀ H ∈ 𝓗, (100 : ℝ) ≤ ballRadius H := fun H hh => by
    have h1 : (99 : ℝ) ≤ H.radius := by exact_mod_cast hR H hh
    have h2 : (1 : ℝ) ≤ fineScale F := by exact_mod_cast hM.pos
    unfold ballRadius
    nlinarith
  have one : ∀ H ∈ 𝓗, ∃ X' : LatticePoint → Fin 4 → UnitQuaternion,
      (∀ b ∈ bondsOf (latticeBall (ballRadius H)), IsBeyondSupDist 0 (1.9 * ballRadius H) b.1 →
        IsBeyondSupDist 0 (1.9 * ballRadius H) (b.1 + basisVector b.2) →
          X' b.1 b.2 = pullbackField U₀ H.centre b.1 b.2) ∧
      plaquetteDefect (latticeBall (ballRadius H)) X' ≤ C * (4 * H.annulusEnergy U₀) := by
    intro H hh
    have hnn : 0 ≤ 4 * H.annulusEnergy U₀ := by linarith [hE H]
    have hsq : Real.sqrt (4 * H.annulusEnergy U₀) ^ 2 = 4 * H.annulusEnergy U₀ := Real.sq_sqrt hnn
    obtain ⟨X', h1, h2⟩ := hS (ballRadius H) 0 (latticeBall (ballRadius H))
      ((latticeBall (ballRadius H)).filter (IsBeyondSupDist 0 (ballRadius H)))
      (pullbackField U₀ H.centre) (Real.sqrt (4 * H.annulusEnergy U₀)) (hl H hh)
      (mem_latticeBall (ballRadius_nonneg H))
      (fun x => by simp only [Finset.mem_filter]) (Real.sqrt_nonneg _) (by rw [hsq]; exact (hH H hh).2.2)
      (by
        rw [hsq]
        exact plaquetteDefect_shell_le hL hs H (hR H hh) (hRL H hh) U₀ _ fun x => by
          simp only [Finset.mem_filter])
    exact ⟨X', h1, by rwa [hsq] at h2⟩
  choose! Xf hXf1 hXf2 using one
  have hin : ∀ H ∈ 𝓗, ∀ z ∈ torusBall H, z ∈ cutBelow 0 H.outerBox := fun H hh z hz => by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hz
    exact embedOffset_mem_cutBelow_outer hL H (hR H hh) hv
  have hU : ∀ H ∈ 𝓗, ∀ H' ∈ 𝓗, ∀ z, z ∈ torusBall H → z ∈ torusBall H' → H = H' := by
    intro H hh H' hh' z hz hz'
    by_contra hne
    obtain ⟨f, hf, hzf⟩ := Finset.mem_biUnion.1 (hin H hh z hz)
    obtain ⟨f', hf', hzf'⟩ := Finset.mem_biUnion.1 (hin H' hh' z hz')
    have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
    have e := eq_of_mem_sitesBelow hL hs' hzf hzf'
    subst e
    exact hApart H hh H' hh' hne ⟨f, hf, f, hf', by rw [supDist_self]; norm_num⟩
  set U' : F.GaugeField 0 := fun z i =>
    if h : ∃ H ∈ 𝓗, z ∈ torusBall H ∧ z + unitStep 0 i ∈ torusBall H then
      Xf h.choose (leastOffset h.choose.centre z) i else U₀ z i with hU'
  have hsz : ∀ H ∈ 𝓗, ∀ v ∈ latticeBall (ballRadius H), ∀ i, 8 * |v i| < (F.period 0 i : ℤ) :=
    fun H hh v hv i => by
      have := abs_add_lt_period hL hs H (hRL H hh) ((mem_latticeBall_iff_int H v).1 hv) 0 (by simp) i
      simpa using this
  have hsz4 : ∀ H ∈ 𝓗, ∀ v ∈ latticeBall (ballRadius H), ∀ i, 4 * |v i| < (F.period 0 i : ℤ) :=
    fun H hh v hv i => by
      have := hsz H hh v hv i
      have := abs_nonneg (v i)
      omega
  have hsz2 : ∀ H ∈ 𝓗, ∀ v ∈ latticeBall (ballRadius H), ∀ i, 2 * |v i| < (F.period 0 i : ℤ) :=
    fun H hh v hv i => by
      have := hsz H hh v hv i
      have := abs_nonneg (v i)
      omega
  have hval : ∀ H ∈ 𝓗, ∀ v ∈ latticeBall (ballRadius H), ∀ i, v + basisVector i ∈ latticeBall (ballRadius H) →
      U' (embedOffset H.centre v) i = Xf H v i := by
    intro H hh v hv i hvi
    have m1 : embedOffset H.centre v ∈ torusBall H := Finset.mem_image_of_mem _ hv
    have m2 : embedOffset H.centre v + unitStep 0 i ∈ torusBall H := by
      rw [← embedOffset_add_basisVector]
      exact Finset.mem_image_of_mem _ hvi
    have hex : ∃ H' ∈ 𝓗, embedOffset H.centre v ∈ torusBall H' ∧
        embedOffset H.centre v + unitStep 0 i ∈ torusBall H' :=
      ⟨H, hh, m1, m2⟩
    have hch := hex.choose_spec
    have e := hU _ hch.1 H hh _ hch.2.1 m1
    simp only [hU']
    rw [dif_pos hex, e, leastOffset_embedOffset hperpos _ _ (hsz2 H hh v hv)]
  refine ⟨U', torusBallPlaquettes, ?_, ?_, ?_, ?_, ?_⟩
  · intro H hh p hp x hx
    obtain ⟨⟨v, μ, ν⟩, hq, rfl⟩ := Finset.mem_image.1 hp
    simp only [orientedPlaquettesOf, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hq
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩ := hq
    have bo := fun {w : LatticePoint} (hw : w ∈ latticeBall (ballRadius H)) =>
      embedOffset_mem_cutBelow_outer hL H (hR H hh) hw
    simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact bo h1
    · rw [← embedOffset_add_basisVector]; exact bo h3
    · rw [← embedOffset_add_basisVector]; exact bo h4
    · rw [← embedOffset_add_basisVector, ← embedOffset_add_basisVector]; exact bo h5
  · rintro H hh ⟨z, μ, ν⟩ hlt ⟨x, hx, hxi⟩
    simp only at hlt
    obtain ⟨v, rfl, hb⟩ := exists_offset_of_mem_cutBelow_inner hL H hxi
    obtain ⟨δ, hδ, hxe⟩ := exists_of_mem_plaquetteCorners (z, μ, ν) hlt.ne hx
    simp only at hxe
    have hz : z = embedOffset H.centre (v - δ) := by
      have e1 : embedOffset H.centre (v - δ + δ) = embedOffset H.centre (v - δ) + siteOfCoords 0 δ :=
        embedOffset_add _ _ _
      rw [sub_add_cancel] at e1
      rw [e1] at hxe
      exact (add_right_cancel hxe).symm
    have hball : ∀ w : LatticePoint, (∀ k, |w k - v k| ≤ 2) → w ∈ latticeBall (ballRadius H) := fun w hw =>
      mem_latticeBall_of_near hM H (hR H hh) hb hw
    refine Finset.mem_image.2 ⟨(v - δ, μ, ν), ?_, by rw [hz]⟩
    simp only [orientedPlaquettesOf, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    refine ⟨⟨hball _ fun k => ?_, hlt.ne, hball _ fun k => ?_, hball _ fun k => ?_, hball _ fun k => ?_⟩, hlt⟩
    all_goals
      have a1 := hδ k
      have a2 := basisVector_bounds μ k
      have a3 := basisVector_bounds ν k
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [abs_le]
      constructor <;> omega
  · rintro ⟨z, μ, ν⟩ hlt hno
    simp only at hlt
    have hne : μ ≠ ν := hlt.ne
    have bond : ∀ (y : F.Site 0) (i : Fin 4), y ∈ plaquetteCorners (z, μ, ν) →
        y + unitStep 0 i ∈ plaquetteCorners (z, μ, ν) → U' y i = U₀ y i := by
      intro y i hy hyi
      by_cases hex : ∃ H ∈ 𝓗, y ∈ torusBall H ∧ y + unitStep 0 i ∈ torusBall H
      · obtain ⟨H, hh, h1, h2⟩ := hex
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 h1
        obtain ⟨w2, hw2, e2⟩ := Finset.mem_image.1 h2
        have b2 : ∀ k, 4 * |(w + basisVector i) k| < (F.period 0 k : ℤ) := fun k => by
          have := abs_add_lt_period hL hs H (hRL H hh) ((mem_latticeBall_iff_int H w).1 hw) (basisVector i)
            (fun m => by
              have := basisVector_bounds i m
              rw [abs_le]
              constructor <;> omega) k
          have h0 := abs_nonneg ((w + basisVector i) k)
          simp only [Pi.add_apply] at this h0 ⊢
          omega
        have e3 : w2 = w + basisVector i :=
          embedOffset_injective hperpos H.centre (hsz4 H hh _ hw2) b2
            (e2.trans (embedOffset_add_basisVector _ _ _).symm)
        subst e3
        rw [hval H hh w hw i hw2]
        have hnot : ∃ q ∈ plaquetteCorners (z, μ, ν), q ∉ torusBall H := by
          by_contra hall
          push_neg at hall
          have c1 := hall z (by simp [plaquetteCorners])
          obtain ⟨v0, hv0, rfl⟩ := Finset.mem_image.1 c1
          have step : ∀ (u : LatticePoint) (e : F.Site 0), (∀ k, |u k| ≤ 2) →
              embedOffset H.centre v0 + siteOfCoords 0 u = e →
              e ∈ torusBall H → v0 + u ∈ latticeBall (ballRadius H) := by
            intro u e hu he hm
            obtain ⟨a, ha, ea⟩ := Finset.mem_image.1 hm
            have b3 : ∀ k, 4 * |(v0 + u) k| < (F.period 0 k : ℤ) := fun k => by
              have := hsz H hh v0 hv0 k
              have h4 := hu k
              have h5 : |(v0 + u) k| ≤ |v0 k| + |u k| := abs_add_le _ _
              have h6 : (1 : ℤ) ≤ F.blockSide := by exact_mod_cast hL.pos
              have h7 := period_zero_ge hL hs k
              have h8 : (1 : ℤ) ≤ (F.blockSide : ℤ) * fineScale F := by nlinarith
              omega
            have := embedOffset_injective hperpos H.centre (hsz4 H hh a ha) b3
              (ea.trans (he.symm.trans (embedOffset_add _ _ _).symm))
            rw [← this]
            exact ha
          have ubd : ∀ (i k : Fin 4), |(basisVector i : LatticePoint) k| ≤ 2 := fun i k => by
            have := basisVector_bounds i k
            rw [abs_le]
            constructor <;> omega
          have d1 := step (basisVector μ) _ (ubd μ) rfl (hall _ (mem_plaquetteCorners_first _ μ ν))
          have d2 := step (basisVector ν) _ (ubd ν) rfl (hall _ (mem_plaquetteCorners_second _ μ ν))
          have d3 := step (basisVector μ + basisVector ν)
            (embedOffset H.centre v0 + unitStep 0 μ + unitStep 0 ν)
            (fun k => by
              have a1 := basisVector_bounds μ k
              have a2 := basisVector_bounds ν k
              simp only [Pi.add_apply]
              rw [abs_le]
              constructor <;> omega)
            (by
              funext k
              simp [siteOfCoords, unitStep, add_assoc]
              rfl)
            (hall _ (mem_plaquetteCorners_opposite _ μ ν))
          refine hno H hh (Finset.mem_image.2 ⟨(v0, μ, ν), ?_, rfl⟩)
          simp only [orientedPlaquettesOf, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
          refine ⟨⟨hv0, hne, d1, d2, ?_⟩, hlt⟩
          rw [add_assoc]
          exact d3
        obtain ⟨q, hq, hqn⟩ := hnot
        obtain ⟨d, hd, hqd⟩ := exists_diff_of_mem_plaquetteCorners (z, μ, ν) hne hy hq
        obtain ⟨d', hd', hqd'⟩ := exists_diff_of_mem_plaquetteCorners (z, μ, ν) hne hyi hq
        have o1 : w + d ∉ latticeBall (ballRadius H) := fun hm => hqn (by
          rw [hqd, ← embedOffset_add]
          exact Finset.mem_image_of_mem _ hm)
        have o2 : w + basisVector i + d' ∉ latticeBall (ballRadius H) := fun hm => hqn (by
          rw [hqd', ← embedOffset_add_basisVector, ← embedOffset_add]
          exact Finset.mem_image_of_mem _ hm)
        have B1 := isBeyond_of_add_not_mem hM H (hR H hh) hd o1
        have B2 := isBeyond_of_add_not_mem hM H (hR H hh) hd' o2
        refine hXf1 H hh (w, i) ?_ B1 B2
        simp only [bondsOf, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
        exact ⟨hw, hw2⟩
      · simp only [hU']
        rw [dif_neg hex]
    have c1 := mem_plaquetteCorners_base z μ ν
    have c2 := mem_plaquetteCorners_first z μ ν
    have c3 := mem_plaquetteCorners_second z μ ν
    have c4 := mem_plaquetteCorners_opposite z μ ν
    have c4' : z + unitStep 0 ν + unitStep 0 μ ∈ plaquetteCorners (z, μ, ν) := by
      rw [add_right_comm]
      exact c4
    unfold plaquetteEnergy
    rw [plaquetteHolonomy_eq, plaquetteHolonomy_eq, bond z μ c1 c2, bond _ ν c2 c4, bond _ μ c3 c4',
      bond z ν c1 c3]
  · intro H hh
    have hinj : Set.InjOn (fun p : LatticePoint × Fin 4 × Fin 4 => (embedOffset H.centre p.1, p.2.1, p.2.2))
        ((orientedPlaquettesOf (latticeBall (ballRadius H))).filter (fun p => p.2.1 < p.2.2) :
          Finset (LatticePoint × Fin 4 × Fin 4)) := by
      rintro ⟨v, μ, ν⟩ hv ⟨w, μ', ν'⟩ hw h
      simp only [Finset.coe_filter, Set.mem_setOf_eq, orientedPlaquettesOf, Finset.mem_filter, Finset.mem_product,
        Finset.mem_univ, and_true] at hv hw
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, rfl, rfl⟩ := h
      rw [embedOffset_injective hperpos H.centre (hsz4 H hh _ hv.1.1) (hsz4 H hh _ hw.1.1) h1]
    have e : ∑ p ∈ torusBallPlaquettes H, plaquetteEnergy U' p =
        ∑ q ∈ (orientedPlaquettesOf (latticeBall (ballRadius H))).filter (fun p => p.2.1 < p.2.2),
          ‖((latticePlaquette (Xf H) q.1 q.2.1 q.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 / 2 := by
      unfold torusBallPlaquettes
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl ?_
      rintro ⟨v, μ, ν⟩ hq
      simp only [orientedPlaquettesOf, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hq
      obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩ := hq
      have h5' : v + basisVector ν + basisVector μ ∈ latticeBall (ballRadius H) := by
        rw [add_right_comm]
        exact h5
      rw [plaquetteEnergy_eq, plaquetteHolonomy_eq, hval H hh v h1 μ h3, ← embedOffset_add_basisVector,
        hval H hh _ h3 ν h5, ← embedOffset_add_basisVector, hval H hh _ h4 μ h5', hval H hh v h1 ν h4]
      rfl
    rw [e, ← Finset.sum_div]
    have h2 := hXf2 H hh
    rw [plaquetteDefect_eq_two_mul] at h2
    linarith
  · intro b hb
    simp only [hU']
    refine dif_neg ?_
    rintro ⟨H, hh, h1, h2⟩
    exact hb H hh ⟨hin H hh _ h1, hin H hh _ h2⟩
end HoleFilling
end YangMills.Construction
end
