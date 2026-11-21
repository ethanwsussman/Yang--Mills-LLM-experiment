import YangMills.Construction.LawInAState.PlaquettesAtASiteProof
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ResponseInTheExpansion.MeansOfAWeight
import YangMills.Construction.ResponseInTheExpansion.WeightsNearTheirMeans
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesAtARadiusWithNoLevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps BlockOffsets BlockAverages
namespace NearMeans
variable {L : ℕ} [NeZero L]
theorem fineBlock_mem_form (hodd : Odd L) : (t n : ℕ) → [NeZero n] → (y : TorusSite n) →
    (c : TorusSite (fineSide L t n)) →
    c ∈ fineBlock L t n y → ∃ e : Fin 4 → ℤ, (∀ i, 2 * |e i| ≤ (L : ℤ) ^ t - 1) ∧
      c = siteOfInt fun i => (L : ℤ) ^ t * ((y i).cast : ℤ) + e i
  | 0, n, _, y, c, hc => by
    have hcy : c = y := Finset.mem_singleton.mp hc
    refine ⟨0, by simp, ?_⟩
    rw [hcy]
    funext i
    simp only [siteOfInt, pow_zero, one_mul, Pi.zero_apply, add_zero]
    exact (ZMod.intCast_zmod_cast (y i)).symm
  | t + 1, n, _, Y, c, hc => by
    obtain ⟨z, hz, hcz⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨e, he, hce⟩ := fineBlock_mem_form hodd t (n * L) z c hcz
    have hzY : parentBlock L z = Y := by simpa [sitesInBlocks] using hz
    obtain ⟨o, ho, hzo⟩ := exists_fineSite_of_parentBlock hodd Y z hzY
    have hoi := (mem_centredCube_iff o).1 ho
    have hL1 : (1 : ℤ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hQ : (0 : ℤ) < (L : ℤ) ^ t := by positivity
    refine ⟨fun i => (L : ℤ) ^ t * o i + e i, fun i => ?_, ?_⟩
    · obtain ⟨H, hH⟩ := hodd
      have hLH : ((L : ℤ) - 1) / 2 = (H : ℤ) := by subst hH; push_cast; omega
      have hLe : (L : ℤ) = 2 * H + 1 := by subst hH; push_cast; ring
      have h1 := hoi i
      rw [hLH] at h1
      have h2 : |o i| ≤ H := abs_le.mpr h1
      have h3 : |(L : ℤ) ^ t * o i + e i| ≤ (L : ℤ) ^ t * H + |e i| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        rw [abs_mul, abs_of_pos hQ]
        exact mul_le_mul_of_nonneg_left h2 hQ.le
      have h4 := he i
      have hq : (L : ℤ) ^ t * L = (L : ℤ) ^ t * (2 * H + 1) := by rw [← hLe]
      show 2 * |(L : ℤ) ^ t * o i + e i| ≤ (L : ℤ) ^ (t + 1) - 1
      rw [pow_succ]
      linarith [h3, h4, hq]
    · rw [hce]
      funext i
      simp only [siteOfInt]
      haveI hNL : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
      have hzi : z i = (((L : ℤ) * (((Y i).cast : ℤ) + 0) + o i : ℤ) : ZMod (n * L)) := by
        rw [hzo]
        rfl
      set a : ℤ := (L : ℤ) * (((Y i).cast : ℤ) + 0) + o i with ha
      have hk : ((z i).cast : ℤ) = a + ((n * L : ℕ) : ℤ) * (-(a / ((n * L : ℕ) : ℤ))) := by
        rw [hzi, ZMod.coe_intCast, Int.emod_def]
        ring
      have hM : ((((n * L : ℕ) : ℤ) * (L : ℤ) ^ t : ℤ) : ZMod (fineSide L t (n * L))) = 0 := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨1, ?_⟩
        rw [fineSide_eq]
        push_cast
        ring
      have hring : (L : ℤ) ^ t * ((z i).cast : ℤ) + e i =
          ((L : ℤ) ^ (t + 1) * ((Y i).cast : ℤ) + ((L : ℤ) ^ t * o i + e i)) +
            (((n * L : ℕ) : ℤ) * (L : ℤ) ^ t) * (-(a / ((n * L : ℕ) : ℤ))) := by
        rw [hk, ha]
        ring
      rw [hring, Int.cast_add, Int.cast_mul _ (-(a / ((n * L : ℕ) : ℤ))), hM, zero_mul, add_zero]
      rfl
def directionCount (μ ν i : Fin 4) : ℤ := (if i = μ then 1 else 0) + (if i = ν then 1 else 0)
theorem plaquetteVertex_form {m : ℕ} (x : TorusSite m) (μ ν : Fin 4) (hlt : μ < ν) (c : TorusSite m)
    (hc : c ∈ plaquetteVertices x μ ν) :
    ∃ ε : Fin 4 → ℤ, (∀ i, |directionCount μ ν i - 2 * ε i| ≤ 1) ∧ c = x + siteOfInt ε := by apply _root_.YangMills.DeltaSharedProofs.p500648 <;> assumption
theorem doubledBarycentre_eq_siteOfInt {m : ℕ} [NeZero m] (p : TorusPlaquette m) (v : Fin 4 → ℤ)
    (hv : p.1 = siteOfInt v) :
    doubledBarycentre p = siteOfInt fun i => 2 * v i + directionCount p.2.1 p.2.2 i := by apply _root_.YangMills.DeltaSharedProofs.p501694 <;> assumption
theorem barycentreDist_le_one_of_same_site (hodd : Odd L) (t n : ℕ) [NeZero n] (y : TorusSite n)
    (p p' : TorusPlaquette (fineSide L t n))
    (hp : IsPlaquetteAt L t y p) (hp' : IsPlaquetteAt L t y p') : barycentreDist L t p p' ≤ 1 := by
  obtain ⟨hlt, c, hc, hcy⟩ := hp
  obtain ⟨hlt', c', hc', hcy'⟩ := hp'
  obtain ⟨e, he, hce⟩ := fineBlock_mem_form hodd t n y c hcy
  obtain ⟨e', he', hce'⟩ := fineBlock_mem_form hodd t n y c' hcy'
  obtain ⟨ε, hε, hcε⟩ := plaquetteVertex_form p.1 p.2.1 p.2.2 hlt c hc
  obtain ⟨ε', hε', hcε'⟩ := plaquetteVertex_form p'.1 p'.2.1 p'.2.2 hlt' c' hc'
  set A : Fin 4 → ℤ := fun i => (L : ℤ) ^ t * ((y i).cast : ℤ) with hA
  have hx : p.1 = siteOfInt fun i => A i + e i - ε i := by
    funext i
    have h1 := congrFun hce i
    have h2 := congrFun hcε i
    simp only [siteOfInt, Pi.add_apply] at h1 h2 ⊢
    have h3 : p.1 i = c i - ((ε i : ℤ) : ZMod (fineSide L t n)) := eq_sub_of_add_eq h2.symm
    rw [h3, h1, ← Int.cast_sub]
  have hx' : p'.1 = siteOfInt fun i => A i + e' i - ε' i := by
    funext i
    have h1 := congrFun hce' i
    have h2 := congrFun hcε' i
    simp only [siteOfInt, Pi.add_apply] at h1 h2 ⊢
    have h3 : p'.1 i = c' i - ((ε' i : ℤ) : ZMod (fineSide L t n)) := eq_sub_of_add_eq h2.symm
    rw [h3, h1, ← Int.cast_sub]
  haveI : NeZero (2 * fineSide L t n) := ⟨mul_ne_zero two_ne_zero (NeZero.ne _)⟩
  have hQ : (0 : ℝ) < (L : ℝ) ^ t := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hT : supDist (doubledBarycentre p) (doubledBarycentre p') ≤ 2 * L ^ t := by
    rw [supDist_le_iff]
    intro i
    rw [doubledBarycentre_eq_siteOfInt p _ hx, doubledBarycentre_eq_siteOfInt p' _ hx']
    simp only [siteOfInt]
    rw [← Int.cast_sub]
    refine (natAbs_valMinAbs_intCast_le _).trans ?_
    have b1 := he i
    have b2 := he' i
    have b3 := abs_le.mp (hε i)
    have b4 := abs_le.mp (hε' i)
    have b5 := abs_le.mp (show |e i| ≤ |e i| from le_rfl)
    have b6 := abs_le.mp (show |e' i| ≤ |e' i| from le_rfl)
    zify
    rw [abs_le]
    constructor <;> linarith [b1, b2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2]
  unfold barycentreDist
  rw [div_le_one (by positivity)]
  exact_mod_cast hT
theorem eq_of_doubledBarycentre_eq {m : ℕ} [NeZero m] (p p' : TorusPlaquette m) (hp : p.2.1 < p.2.2)
    (hp' : p'.2.1 < p'.2.2) (h : doubledBarycentre p = doubledBarycentre p') : p = p' := by apply _root_.YangMills.SharedProofs.p2545 <;> assumption
theorem barycentreDist_nonneg {m : ℕ} (t : ℕ) (p p' : TorusPlaquette m) :
    0 ≤ barycentreDist L t p p' := by
  unfold barycentreDist
  positivity
theorem weightLipschitz_nonneg {m : ℕ} (t : ℕ) (h : PlaquetteWeight m) : 0 ≤ weightLipschitz L t h :=
  Real.iSup_nonneg fun _ => div_nonneg (abs_nonneg _) (barycentreDist_nonneg t _ _)
theorem abs_sub_le_weightLipschitz {m : ℕ} [NeZero m] (t : ℕ) (h : PlaquetteWeight m)
    (p p' : TorusPlaquette m) (hp : p.2.1 < p.2.2) (hp' : p'.2.1 < p'.2.2)
    (hd : barycentreDist L t p p' ≤ 1) : |h p - h p'| ≤ weightLipschitz L t h := by
  by_cases heq : p = p'
  · rw [heq, sub_self, abs_zero]
    exact weightLipschitz_nonneg t h
  have hQ : (0 : ℝ) < (L : ℝ) ^ t := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  haveI : NeZero (2 * m) := ⟨mul_ne_zero two_ne_zero (NeZero.ne _)⟩
  have hT : supDist (doubledBarycentre p) (doubledBarycentre p') ≠ 0 := by
    intro h0
    have h1 := (supDist_le_iff (doubledBarycentre p) (doubledBarycentre p') 0).1 h0.le
    refine heq (eq_of_doubledBarycentre_eq p p' hp hp' ?_)
    funext i
    have h2 := h1 i
    have h3 : ((doubledBarycentre p i - doubledBarycentre p' i).valMinAbs) = 0 := by omega
    exact sub_eq_zero.mp ((ZMod.valMinAbs_eq_zero _).mp h3)
  have hdpos : 0 < barycentreDist L t p p' := by
    unfold barycentreDist
    have : (0 : ℝ) < supDist (doubledBarycentre p) (doubledBarycentre p') := by
      exact_mod_cast Nat.pos_of_ne_zero hT
    positivity
  have hle : |h p - h p'| / barycentreDist L t p p' ≤ weightLipschitz L t h := by
    have hb : BddAbove (Set.range fun pp : OrientedPlaquette m × OrientedPlaquette m =>
        |h pp.1.1 - h pp.2.1| / barycentreDist L t pp.1.1 pp.2.1) := Set.finite_range _ |>.bddAbove
    exact le_ciSup hb ((⟨p, hp⟩, ⟨p', hp'⟩) : OrientedPlaquette m × OrientedPlaquette m)
  rw [div_le_iff₀ hdpos] at hle
  calc |h p - h p'| ≤ weightLipschitz L t h * barycentreDist L t p p' := hle
    _ ≤ weightLipschitz L t h * 1 := mul_le_mul_of_nonneg_left hd (weightLipschitz_nonneg t h)
    _ = _ := mul_one _
theorem blockMean_nonneg (hodd : Odd L) : (t n : ℕ) → [NeZero n] → (y : TorusSite n) →
    (h : PlaquetteWeight (fineSide L t n)) →
    (∀ p, IsPlaquetteAt L t y p → 0 ≤ h p) → 0 ≤ blockMean L t n y h
  | 0, n, _, y, h, hh => by
    show 0 ≤ (1 / 24 : ℝ) * ∑ p ∈ plaquettesIn (n := n) Finset.univ, vertexMultiplicity y p * h p
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun p hp => ?_)
    by_cases hc : y ∈ plaquetteVertices p.1 p.2.1 p.2.2
    · have hlt : p.2.1 < p.2.2 := by
        simp only [plaquettesIn, Finset.mem_filter] at hp
        exact hp.2.1
      exact mul_nonneg (by simp [vertexMultiplicity]) (hh p ⟨hlt, y, hc, Finset.mem_singleton_self y⟩)
    · have h0 : vertexMultiplicity y p = 0 := by
        simp only [vertexMultiplicity]
        rw [List.count_eq_zero_of_not_mem hc]
        simp
      rw [h0, zero_mul]
  | t + 1, n, _, Y, h, hh => by
    show 0 ≤ ((L : ℝ) ^ 4)⁻¹ * ∑ z ∈ sitesInBlocks L {Y}, blockMean L t (n * L) z h
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun z hz => ?_)
    refine blockMean_nonneg hodd t (n * L) z h fun p hp => hh p ⟨hp.1, ?_⟩
    obtain ⟨c, hc, hcz⟩ := hp.2
    exact ⟨c, hc, Finset.mem_biUnion.mpr ⟨z, hz, hcz⟩⟩
theorem blockMean_between (hW : BlockMeanIsLinearAndLocal) (hodd : Odd L) (t n : ℕ) [NeZero n]
    (y : TorusSite n) (h : PlaquetteWeight (fineSide L t n)) (A B : ℝ)
    (hh : ∀ p, IsPlaquetteAt L t y p → A ≤ h p ∧ h p ≤ B) :
    A ≤ blockMean L t n y h ∧ blockMean L t n y h ≤ B := by
  obtain ⟨hone, hlin, -⟩ := hW L hodd t n y
  constructor
  · have h1 := blockMean_nonneg hodd t n y (fun p => 1 * h p + (-A) * constOneWeight _ p) fun p hp => by
      have := (hh p hp).1
      simp only [constOneWeight]
      linarith
    rw [hlin, hone] at h1
    linarith
  · have h1 := blockMean_nonneg hodd t n y (fun p => B * constOneWeight _ p + (-1) * h p) fun p hp => by
      have := (hh p hp).2
      simp only [constOneWeight]
      linarith
    rw [hlin, hone] at h1
    linarith
theorem abs_sub_blockMean_le (hW : BlockMeanIsLinearAndLocal) (hodd : Odd L) (t n : ℕ) [NeZero n]
    (y : TorusSite n) (h : PlaquetteWeight (fineSide L t n)) (p : TorusPlaquette (fineSide L t n))
    (hp : IsPlaquetteAt L t y p) :
    |h p - blockMean L t n y h| ≤ 3 * weightLipschitz L t h := by
  have hl := weightLipschitz_nonneg (L := L) t h
  have hb := blockMean_between hW hodd t n y h (h p - weightLipschitz L t h)
      (h p + weightLipschitz L t h) fun p' hp' => by
    have h1 := abs_sub_le_weightLipschitz (L := L) t h p p' hp.1 hp'.1
      (barycentreDist_le_one_of_same_site hodd t n y p p' hp hp')
    have h2 := abs_le.mp h1
    constructor <;> linarith [h2.1, h2.2]
  rw [abs_le]
  constructor <;> linarith [hb.1, hb.2]
theorem weightsCloseToBlockMeans (hW : BlockMeanIsLinearAndLocal) : WeightsCloseToBlockMeans := by
  intro L _ hodd t n _ y
  refine ⟨fun h => ?_, fun h p hp => abs_sub_blockMean_le hW hodd t n y h p hp, fun h z hz => ?_⟩
  · have hS : ∀ p : TorusPlaquette (fineSide L t n), p.2.1 < p.2.2 → |h p| ≤ weightSup h := by
      intro p hp
      have hb : BddAbove (Set.range fun q : OrientedPlaquette (fineSide L t n) => |h q.1|) :=
        Set.finite_range _ |>.bddAbove
      exact le_ciSup hb (⟨p, hp⟩ : OrientedPlaquette (fineSide L t n))
    have hb := blockMean_between hW hodd t n y h (-weightSup h) (weightSup h) fun p hp => by
      have := abs_le.mp (hS p hp.1)
      exact ⟨this.1, this.2⟩
    exact abs_le.mpr hb
  · have hup : ∀ p, IsPlaquetteAt L t z p → IsPlaquetteAt L (t + 1) y p := fun p hp => by
      obtain ⟨c, hc, hcz⟩ := hp.2
      exact ⟨hp.1, c, hc, Finset.mem_biUnion.mpr ⟨z, hz, hcz⟩⟩
    have hb := blockMean_between hW hodd t (n * L) z h
      (blockMean L (t + 1) n y h - 3 * weightLipschitz L (t + 1) h)
      (blockMean L (t + 1) n y h + 3 * weightLipschitz L (t + 1) h) fun p hp => by
        have h1 := abs_sub_blockMean_le hW hodd (t + 1) n y h p (hup p hp)
        have h2 := abs_le.mp h1
        constructor <;> linarith [h2.1, h2.2]
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2]
end NearMeans
end YangMills.Construction.WeightedResponses
end
