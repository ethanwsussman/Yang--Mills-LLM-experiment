import YangMills.Construction.LawByMomentsOfTheFlow.CoordinatesOnACircle
import YangMills.Construction.LawByMomentsOfTheFlow.PlacesOfTheSitesOfASupport
import YangMills.Construction.LawInAState.MomentsOfTheCentredResponsesProof
import YangMills.Construction.LawInAState.WeightsOfMarksOnTheLeastTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
open YangMills.Construction.TorusFields YangMills.Construction.WeightedResponses
open YangMills.Construction.ResponseInTheExpansion YangMills.Construction.BoxResponses
open YangMills.Construction.LevelTestFunctions (LevelData circleRep)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
private theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (a : Fin 4) : |v a| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem euclidNormVec_le_two_mul {v : Fin 4 → ℝ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ a, |v a| ≤ B) :
    euclidNormVec v ≤ 2 * B := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.euclidNormVec_le <;> assumption
section Periodization
variable {d : ℝ} {f : AmbientSpace → ℝ} {c : AmbientSpace}
private theorem abs_sub_center_le_of_ne_zero (hc : tsupport f ⊆ TestFunctions.closedBallR4 c d) {x : AmbientSpace}
    (hx : f x ≠ 0) (a : Fin 4) : |x a - c a| ≤ d := by
  have hm : x ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr hx)
  have h1 : euclidNormVec (x - c) ≤ d := hc hm
  exact (abs_apply_le_euclidNormVec (x - c) a).trans h1
private theorem periodize_shift_unique (hd : d ≤ 1 / 4) (hc : tsupport f ⊆ TestFunctions.closedBallR4 c d)
    {x : AmbientSpace} {z z' : Fin 4 → ℤ} (h : f (fun i => x i + 2 * (z i : ℝ)) ≠ 0)
    (h' : f (fun i => x i + 2 * (z' i : ℝ)) ≠ 0) : z = z' := by
  funext a
  have h1 := abs_sub_center_le_of_ne_zero hc h a
  have h2 := abs_sub_center_le_of_ne_zero hc h' a
  have h3 : |((z a - z' a : ℤ) : ℝ)| < 1 := by
    push_cast
    rw [abs_lt]
    have := abs_le.mp h1
    have := abs_le.mp h2
    constructor <;> linarith
  have h4 : |z a - z' a| < 1 := by exact_mod_cast h3
  have h5 := Int.abs_lt_one_iff.mp h4
  omega
private theorem periodize_eq_of_ne_zero (hd : d ≤ 1 / 4) (hc : tsupport f ⊆ TestFunctions.closedBallR4 c d)
    {x : AmbientSpace} {z : Fin 4 → ℤ} (h : f (fun i => x i + 2 * (z i : ℝ)) ≠ 0) :
    periodizeUnitTorus f x = f (fun i => x i + 2 * (z i : ℝ)) := by
  unfold periodizeUnitTorus
  refine finsum_eq_single _ z fun z' hz' => ?_
  by_contra hne
  exact hz' (periodize_shift_unique hd hc hne h)
private theorem periodize_eq_zero {x : AmbientSpace} (h : ∀ z : Fin 4 → ℤ, f (fun i => x i + 2 * (z i : ℝ)) = 0) :
    periodizeUnitTorus f x = 0 := by
  unfold periodizeUnitTorus
  simp only [h]
  exact finsum_zero
private theorem periodize_add_even (f : AmbientSpace → ℝ) (x : AmbientSpace) (e : Fin 4 → ℤ) :
    periodizeUnitTorus f (fun i => x i + 2 * (e i : ℝ)) = periodizeUnitTorus f x := by apply _root_.YangMills.SharedProofs.p63249 <;> assumption
private theorem abs_periodize_sub_le {vt : ℝ} (hd0 : 0 < d) (hd : d ≤ 1 / 4) (hv : 0 < vt)
    (hc : tsupport f ⊆ TestFunctions.closedBallR4 c d)
    (hs : ∀ x x', |f x - f x'| ≤ euclidNormVec (x - x') / (vt * d)) {X X' u : AmbientSpace} {w : Fin 4 → ℤ}
    (hX : ∀ a, X a = X' a + u a + 2 * (w a : ℝ)) (hu : ∀ a, |u a| ≤ 1) :
    |periodizeUnitTorus f X - periodizeUnitTorus f X'| ≤ euclidNormVec u / (vt * d) := by
  have hpos : 0 ≤ euclidNormVec u / (vt * d) := by
    unfold euclidNormVec
    positivity
  have hneg : euclidNormVec (-u) = euclidNormVec u := by
    unfold euclidNormVec
    simp
  by_cases hA : ∃ z : Fin 4 → ℤ, f (fun i => X i + 2 * (z i : ℝ)) ≠ 0
  · obtain ⟨z, hz⟩ := hA
    rw [periodize_eq_of_ne_zero hd hc hz]
    set x₁ : AmbientSpace := fun i => X i + 2 * (z i : ℝ) with hx₁
    set x₂ : AmbientSpace := fun i => X' i + 2 * ((w i + z i : ℤ) : ℝ) with hx₂
    have hdiff : x₁ - x₂ = u := by
      funext a
      simp only [hx₁, hx₂, Pi.sub_apply, hX a]
      push_cast
      ring
    have hper : periodizeUnitTorus f X' = f x₂ := by
      by_cases h2 : f x₂ ≠ 0
      · exact periodize_eq_of_ne_zero hd hc h2
      · have h2' : f x₂ = 0 := not_not.mp h2
        rw [h2']
        refine periodize_eq_zero fun z' => ?_
        by_contra h3
        have hz' : f (fun i => X' i + 2 * (z' i : ℝ)) ≠ 0 := h3
        have hne : z' ≠ w + z := by
          intro he
          apply h2
          have : (fun i => X' i + 2 * (z' i : ℝ)) = x₂ := by
            funext i
            simp only [hx₂, he, Pi.add_apply]
          rw [← this]
          exact hz'
        obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
        have h4 := abs_sub_center_le_of_ne_zero hc hz a
        have h5 := abs_sub_center_le_of_ne_zero hc hz' a
        have h6 : (z' a - (w a + z a) : ℤ) ≠ 0 := fun h => ha (by simp only [Pi.add_apply]; omega)
        have h7 : (1 : ℝ) ≤ |((z' a - (w a + z a) : ℤ) : ℝ)| := by
          have : (1 : ℤ) ≤ |z' a - (w a + z a)| := Int.one_le_abs h6
          exact_mod_cast this
        have h8 := abs_le.mp h4
        have h9 := abs_le.mp h5
        have h10 := abs_le.mp (hu a)
        have h11 := hX a
        have h12 : |((z' a - (w a + z a) : ℤ) : ℝ)| < 1 := by
          push_cast
          rw [abs_lt]
          constructor <;> linarith
        linarith
    rw [hper]
    have := hs x₁ x₂
    rwa [hdiff] at this
  · push_neg at hA
    rw [periodize_eq_zero hA, zero_sub, abs_neg]
    by_cases hB : ∃ z : Fin 4 → ℤ, f (fun i => X' i + 2 * (z i : ℝ)) ≠ 0
    · obtain ⟨z, hz⟩ := hB
      rw [periodize_eq_of_ne_zero hd hc hz]
      set x₁ : AmbientSpace := fun i => X' i + 2 * (z i : ℝ) with hx₁
      set x₂ : AmbientSpace := fun i => X i + 2 * ((z i - w i : ℤ) : ℝ) with hx₂
      have hdiff : x₁ - x₂ = -u := by
        funext a
        simp only [hx₁, hx₂, Pi.sub_apply, Pi.neg_apply, hX a]
        push_cast
        ring
      have h0 : f x₂ = 0 := hA _
      have := hs x₁ x₂
      rw [h0, sub_zero, hdiff, hneg] at this
      exact this
    · push_neg at hB
      rw [periodize_eq_zero hB, abs_zero]
      exact hpos
end Periodization
section PeriodizedLevelData
variable {L : ℕ} [NeZero L]
private def periodizedLevelData {p : ℕ} (φ : Fin p → AmbientSpace → ℝ) (K : ℕ) : LevelData p where
  fn i z := periodizeUnitTorus (φ i) (fun a => z a)
  windowLevel := K
  scaleLevel := K
  sideExponent := 0
  center := fun _ => 0
private theorem period_periodizedLevelData {p : ℕ} (φ : Fin p → AmbientSpace → ℝ) (K : ℕ) :
    (((periodizedLevelData φ K).period L : ℕ) : ℝ) = 2 := by
  simp [LevelData.period, periodizedLevelData]
private theorem sideAt_periodizedLevelData {p : ℕ} (φ : Fin p → AmbientSpace → ℝ) (K t : ℕ) :
    (periodizedLevelData φ K).sideAt L t = 2 * L ^ (K - t) := by
  simp [LevelData.sideAt, LevelData.period, periodizedLevelData]
private theorem natCast_pow_pos (K : ℕ) : (0 : ℝ) < (L : ℝ) ^ K := by
  have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  positivity
private theorem torusWeight_eq_testWeight {p : ℕ} (φ : Fin p → AmbientSpace → ℝ) (K : ℕ) {m : ℕ}
    (hm : m = 2 * L ^ K) (i : Fin p) (q : TorusPlaquette m) :
    torusWeightAtBarycentres L K m (φ i) q = (periodizedLevelData φ K).testWeight L i m q := by
  have hP := natCast_pow_pos (L := L) K
  have key : ∀ a, ∃ e : ℤ, ((doubledBarycentre q a).val : ℝ) / (2 * (L : ℝ) ^ K) =
      (L : ℝ) ^ K / (L : ℝ) ^ K * circleRep (((periodizedLevelData φ K).period L : ℕ) : ℝ)
        (LevelTestFunctions.barycenterCoord q a / (L : ℝ) ^ K - 0) + 2 * (e : ℝ) := by
    intro a
    rw [period_periodizedLevelData]
    obtain ⟨x, μ, ν⟩ := q
    set b : ℕ := 2 * (x a).val + (if a = μ then 1 else 0) + (if a = ν then 1 else 0) with hb
    have hval : (doubledBarycentre (x, μ, ν) a).val = b % (2 * m) := by
      show ((b : ℕ) : ZMod (2 * m)).val = _
      exact ZMod.val_natCast _ _
    have hdiv := Nat.div_add_mod b (2 * m)
    set w : ℕ := b / (2 * m) with hw
    have hbr : (b : ℝ) = 2 * LevelTestFunctions.barycenterCoord (x, μ, ν) a := by
      simp only [hb, LevelTestFunctions.barycenterCoord]
      push_cast
      split_ifs <;> simp <;> ring
    have hmr : (m : ℝ) = 2 * (L : ℝ) ^ K := by
      rw [hm]
      push_cast
      ring
    have hvr : ((b % (2 * m) : ℕ) : ℝ) = (b : ℝ) - 2 * m * w := by
      have : (((2 * m) * w + b % (2 * m) : ℕ) : ℝ) = (b : ℝ) := by exact_mod_cast hdiv
      push_cast at this
      linarith
    refine ⟨round ((LevelTestFunctions.barycenterCoord (x, μ, ν) a / (L : ℝ) ^ K - 0) / 2) - w, ?_⟩
    rw [hval, hvr, hbr, hmr]
    unfold circleRep
    push_cast
    field_simp
    ring
  choose e he using key
  show periodizeUnitTorus (φ i) (fun a => ((doubledBarycentre q a).val : ℝ) / (2 * (L : ℝ) ^ K)) =
    periodizeUnitTorus (φ i) (fun a => (L : ℝ) ^ K / (L : ℝ) ^ K *
      circleRep (((periodizedLevelData φ K).period L : ℕ) : ℝ)
        (LevelTestFunctions.barycenterCoord q a / (L : ℝ) ^ K - 0))
  rw [show (fun a => ((doubledBarycentre q a).val : ℝ) / (2 * (L : ℝ) ^ K)) = _ from funext he]
  exact periodize_add_even _ _ e
private theorem torusWeight_eq_fineWeight (f : AmbientSpace → ℝ) (K : ℕ) {m : ℕ} (hm : m = 2 * L ^ K) :
    torusWeightAtBarycentres L K m f = FreeEnergies.fineWeight
      (fun b => periodizeUnitTorus f fun a => b a / (L : ℝ) ^ K) m := by
  funext q
  have hP := natCast_pow_pos (L := L) K
  have key : ∀ a, ∃ e : ℤ, ((doubledBarycentre q a).val : ℝ) / (2 * (L : ℝ) ^ K) =
      LevelTestFunctions.barycenterCoord q a / (L : ℝ) ^ K + 2 * (e : ℝ) := by
    intro a
    obtain ⟨x, μ, ν⟩ := q
    set b : ℕ := 2 * (x a).val + (if a = μ then 1 else 0) + (if a = ν then 1 else 0) with hb
    have hval : (doubledBarycentre (x, μ, ν) a).val = b % (2 * m) := by
      show ((b : ℕ) : ZMod (2 * m)).val = _
      exact ZMod.val_natCast _ _
    have hdiv := Nat.div_add_mod b (2 * m)
    set w : ℕ := b / (2 * m) with hw
    have hbr : (b : ℝ) = 2 * LevelTestFunctions.barycenterCoord (x, μ, ν) a := by
      simp only [hb, LevelTestFunctions.barycenterCoord]
      push_cast
      split_ifs <;> simp <;> ring
    have hmr : (m : ℝ) = 2 * (L : ℝ) ^ K := by
      rw [hm]
      push_cast
      ring
    have hvr : ((b % (2 * m) : ℕ) : ℝ) = (b : ℝ) - 2 * m * w := by
      have : (((2 * m) * w + b % (2 * m) : ℕ) : ℝ) = (b : ℝ) := by exact_mod_cast hdiv
      push_cast at this
      linarith
    refine ⟨-(w : ℤ), ?_⟩
    rw [hval, hvr, hbr, hmr]
    push_cast
    field_simp
    ring
  choose e he using key
  show periodizeUnitTorus f (fun a => ((doubledBarycentre q a).val : ℝ) / (2 * (L : ℝ) ^ K)) =
    periodizeUnitTorus f (fun a => LevelTestFunctions.barycenterCoord q a / (L : ℝ) ^ K)
  rw [show (fun a => ((doubledBarycentre q a).val : ℝ) / (2 * (L : ℝ) ^ K)) = _ from funext he]
  exact periodize_add_even _ _ e
private theorem exists_near_of_mem_supportSites (hPl : LevelTestFunctions.supportSitesLocationStatement)
    (hC : LevelTestFunctions.CircleRepProperties) (hodd : Odd L) {p : ℕ} (φ : Fin p → AmbientSpace → ℝ)
    (K t : ℕ) (ht : t ≤ K) (n : ℕ) [NeZero n] (hs : n = (periodizedLevelData φ K).sideAt L t) (i : Fin p)
    {y : TorusSite n} (hy : y ∈ weightSupportSites L t n (torusWeightAtBarycentres L K (fineSide L t n) (φ i))) :
    ∃ x : AmbientSpace, φ i x ≠ 0 ∧ ∀ a, |circleRep 2 (((y a).val : ℝ) * ((L : ℝ) ^ t / (L : ℝ) ^ K) - x a)| ≤
      (L : ℝ) ^ t / (2 * (L : ℝ) ^ K) := by
  subst hs
  have hP := natCast_pow_pos (L := L) K
  have hm : fineSide L t ((periodizedLevelData φ K).sideAt L t) = 2 * L ^ K := by
    rw [fineSide_eq, sideAt_periodizedLevelData, mul_assoc, ← pow_add, Nat.sub_add_cancel ht]
  have hfun : torusWeightAtBarycentres L K (fineSide L t ((periodizedLevelData φ K).sideAt L t)) (φ i) =
      (periodizedLevelData φ K).testWeight L i _ :=
    funext (torusWeight_eq_testWeight φ K hm i)
  rw [hfun] at hy
  obtain ⟨z, hz, hplace⟩ := (hPl L hodd p (periodizedLevelData φ K) t ht i).1 y hy
  have hz' : periodizeUnitTorus (φ i) (fun a => z a) ≠ 0 := hz
  obtain ⟨q, hq⟩ : ∃ q : Fin 4 → ℤ, φ i (fun a => z a + 2 * (q a : ℝ)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hz' (periodize_eq_zero hcon)
  refine ⟨_, hq, fun a => ?_⟩
  have h1 : |circleRep (((periodizedLevelData φ K).period L : ℕ) : ℝ)
      (((y a).val : ℝ) * (L : ℝ) ^ t / (L : ℝ) ^ K - 0 - (L : ℝ) ^ K / (L : ℝ) ^ K * z a)| ≤
      (L : ℝ) ^ t / (2 * (L : ℝ) ^ K) := hplace a
  rw [period_periodizedLevelData] at h1
  have h2 := hC.1 2 two_pos (((y a).val : ℝ) * (L : ℝ) ^ t / (L : ℝ) ^ K - 0 -
      (L : ℝ) ^ K / (L : ℝ) ^ K * z a) (-q a)
  rw [← h2] at h1
  have h3 : ((y a).val : ℝ) * ((L : ℝ) ^ t / (L : ℝ) ^ K) - (z a + 2 * (q a : ℝ)) =
      ((y a).val : ℝ) * (L : ℝ) ^ t / (L : ℝ) ^ K - 0 - (L : ℝ) ^ K / (L : ℝ) ^ K * z a +
        2 * ((-q a : ℤ) : ℝ) := by
    rw [div_self (ne_of_gt hP)]
    push_cast
    ring
  rw [h3]
  exact h1
private theorem abs_circleRep_le_half {c : ℝ} (hc : 0 < c) (v : ℝ) : |circleRep c v| ≤ c / 2 := by
  have h1 : circleRep c v = c * (v / c - round (v / c)) := by
    unfold circleRep
    field_simp
  rw [h1, abs_mul, abs_of_pos hc]
  have := abs_sub_round (v / c)
  nlinarith
abbrev _root_.YangMills.SharedProofs.p64351 := @abs_circleRep_le_half
set_option maxHeartbeats 1600000 in
theorem markWeightsOnUnitTorusStatement_holds (hPl : LevelTestFunctions.supportSitesLocationStatement)
    (hC : LevelTestFunctions.CircleRepProperties) : markWeightsOnUnitTorusStatement := by
  intro L _ hodd K d vt hd0 hd hv p φ hφ t n _ ht hn
  obtain ⟨hper, hsh, hsub, hneg, -, hsc, hsite⟩ := id hC
  have hs : n = (periodizedLevelData φ K).sideAt L t := hn.trans (sideAt_periodizedLevelData φ K t).symm
  have hPK := natCast_pow_pos (L := L) K
  have hPt := natCast_pow_pos (L := L) t
  have hPQ := natCast_pow_pos (L := L) (K - t)
  have hQt : (L : ℝ) ^ (K - t) * (L : ℝ) ^ t = (L : ℝ) ^ K := by
    rw [← pow_add, Nat.sub_add_cancel ht]
  have hnr : (n : ℝ) = 2 * (L : ℝ) ^ (K - t) := by
    rw [hn]
    push_cast
    ring
  have hm : fineSide L t n = 2 * L ^ K := by
    rw [fineSide_eq, hn, mul_assoc, ← pow_add, Nat.sub_add_cancel ht]
  have hnM : (n : ℝ) * ((L : ℝ) ^ t / (L : ℝ) ^ K) = 2 := by
    rw [hnr, ← hQt]
    field_simp
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i j hij y hy y' hy' => ?_,
    fun i => torusWeight_eq_fineWeight _ K hm⟩
  · obtain ⟨c, hc⟩ := hφ.support_in_ball i
    unfold weightSup
    refine Real.iSup_le (fun q => ?_) (by norm_num)
    show |periodizeUnitTorus (φ i) _| ≤ 1
    by_cases hA : ∃ z : Fin 4 → ℤ,
        φ i (fun a => ((doubledBarycentre q.1 a).val : ℝ) / (2 * (L : ℝ) ^ K) + 2 * (z a : ℝ)) ≠ 0
    · obtain ⟨z, hz⟩ := hA
      rw [periodize_eq_of_ne_zero hd hc hz, abs_of_nonneg (hφ.nonneg i _)]
      exact hφ.le_one i _
    · push_neg at hA
      rw [periodize_eq_zero hA]
      simp
  · obtain ⟨c, hc⟩ := hφ.support_in_ball i
    have hbound : 0 ≤ 2 / (vt * (d * (L : ℝ) ^ (K - t))) := by positivity
    unfold weightLipschitz
    refine Real.iSup_le (fun pp => ?_) hbound
    obtain ⟨q, q'⟩ := pp
    have hmr : ((fineSide L t n : ℕ) : ℝ) = 2 * (L : ℝ) ^ K := by
      rw [hm]
      push_cast
      ring
    have hne2 : NeZero (2 * fineSide L t n) := ⟨by
      rw [hm]
      exact mul_ne_zero two_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (NeZero.ne L)))⟩
    set τ : ℕ := supDist (doubledBarycentre q.1) (doubledBarycentre q'.1) with hτ
    have hc2 : (0 : ℝ) < ((2 * fineSide L t n : ℕ) : ℝ) := by
      push_cast
      rw [hmr]
      positivity
    let A : Fin 4 → ℝ := fun a => ((doubledBarycentre q.1 a).val : ℝ)
    let A' : Fin 4 → ℝ := fun a => ((doubledBarycentre q'.1 a).val : ℝ)
    let u : AmbientSpace := fun a => circleRep ((2 * fineSide L t n : ℕ) : ℝ) (A a - A' a) / (2 * (L : ℝ) ^ K)
    let w : Fin 4 → ℤ := fun a => round ((A a - A' a) / ((2 * fineSide L t n : ℕ) : ℝ))
    have hX : ∀ a, A a / (2 * (L : ℝ) ^ K) = A' a / (2 * (L : ℝ) ^ K) + u a + 2 * (w a : ℝ) := by
      intro a
      show _ = _ + (A a - A' a - ((2 * fineSide L t n : ℕ) : ℝ) * (w a : ℝ)) / (2 * (L : ℝ) ^ K) + _
      push_cast
      rw [hmr]
      field_simp
      ring
    have hu1 : ∀ a, |u a| ≤ 1 := by
      intro a
      show |circleRep ((2 * fineSide L t n : ℕ) : ℝ) (A a - A' a) / (2 * (L : ℝ) ^ K)| ≤ 1
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (L : ℝ) ^ K), div_le_one (by positivity)]
      have h1 := abs_circleRep_le_half hc2 (A a - A' a)
      have h2 : ((2 * fineSide L t n : ℕ) : ℝ) / 2 = 2 * (L : ℝ) ^ K := by
        push_cast
        rw [hmr]
        ring
      linarith
    have hu2 : ∀ a, |u a| ≤ (τ : ℝ) / (2 * (L : ℝ) ^ K) := by
      intro a
      show |circleRep ((2 * fineSide L t n : ℕ) : ℝ) (A a - A' a) / (2 * (L : ℝ) ^ K)| ≤ _
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (L : ℝ) ^ K)]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have h1 := hsite (2 * fineSide L t n) (doubledBarycentre q.1 a) (doubledBarycentre q'.1 a)
      have h2 := (supDist_le_iff _ _ _).mp (le_refl τ) a
      have h3 : ((((doubledBarycentre q.1 a - doubledBarycentre q'.1 a).valMinAbs).natAbs : ℕ) : ℝ) ≤ τ := by
        exact_mod_cast h2
      exact h1.le.trans h3
    have hlip := abs_periodize_sub_le hd0 hd hv hc (fun x x' => hφ.lipschitz i x x')
      (X := fun a => A a / (2 * (L : ℝ) ^ K)) (X' := fun a => A' a / (2 * (L : ℝ) ^ K)) (u := u) (w := w) hX hu1
    have hE : euclidNormVec u ≤ 2 * ((τ : ℝ) / (2 * (L : ℝ) ^ K)) := euclidNormVec_le_two_mul (by positivity) hu2
    have hdiff : |torusWeightAtBarycentres L K (fineSide L t n) (φ i) q.1 -
        torusWeightAtBarycentres L K (fineSide L t n) (φ i) q'.1| ≤
        2 * ((τ : ℝ) / (2 * (L : ℝ) ^ K)) / (vt * d) :=
      hlip.trans (div_le_div_of_nonneg_right hE (by positivity))
    have hbd : barycentreDist L t q.1 q'.1 = (τ : ℝ) / (2 * (L : ℝ) ^ t) := rfl
    show |torusWeightAtBarycentres L K (fineSide L t n) (φ i) q.1 -
      torusWeightAtBarycentres L K (fineSide L t n) (φ i) q'.1| / barycentreDist L t q.1 q'.1 ≤ _
    rw [hbd]
    by_cases hτ0 : (τ : ℝ) = 0
    · rw [hτ0]
      simpa using hbound
    · have hτp : (0 : ℝ) < τ := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hτ0)
      rw [div_le_iff₀ (by positivity)]
      refine hdiff.trans (le_of_eq ?_)
      rw [← hQt]
      field_simp
  · obtain ⟨c, hc⟩ := hφ.support_in_ball i
    set Q : ℝ := (L : ℝ) ^ (K - t) with hQ
    have hMQ : ((L : ℝ) ^ t / (L : ℝ) ^ K) * Q = 1 := by
      rw [← hQt]
      field_simp
    let lo : Fin 4 → ℤ := fun a => ⌈c a * Q - 1 / 2 - d * Q⌉
    let hi : Fin 4 → ℤ := fun a => ⌊c a * Q + 1 / 2 + d * Q⌋
    have hsub' : weightSupportSites L t n (torusWeightAtBarycentres L K (fineSide L t n) (φ i)) ⊆
        Fintype.piFinset fun a => (Finset.Icc (lo a) (hi a)).image fun z : ℤ => (z : ZMod n) := by
      intro y hy
      obtain ⟨x, hx, hxp⟩ := exists_near_of_mem_supportSites hPl hC hodd φ K t ht n hs i hy
      refine Fintype.mem_piFinset.mpr fun a => ?_
      set M : ℝ := (L : ℝ) ^ t / (L : ℝ) ^ K with hM
      have h1 := hsub 2 two_pos (((y a).val : ℝ) * M - x a) (x a - c a)
      have h2 := hxp a
      have h3 := (hsh 2 two_pos (x a - c a)).trans (abs_sub_center_le_of_ne_zero hc hx a)
      have h4 : ((y a).val : ℝ) * M - x a + (x a - c a) = ((y a).val : ℝ) * M - c a := by ring
      rw [h4] at h1
      set v : ℝ := ((y a).val : ℝ) * M - c a with hv'
      set W : ℤ := round (v / 2) with hW
      have h5 : circleRep 2 v = v - 2 * (W : ℝ) := rfl
      have h6 : |v - 2 * (W : ℝ)| ≤ M / 2 + d := by
        rw [← h5]
        have : (L : ℝ) ^ t / (2 * (L : ℝ) ^ K) = M / 2 := by
          rw [hM]
          field_simp
        linarith
      have h7 := abs_le.mp h6
      have hQpos : 0 < Q := hPQ
      refine Finset.mem_image.mpr ⟨((y a).val : ℤ) - (n : ℤ) * W, ?_, ?_⟩
      · have hval : ((y a).val : ℝ) = (v + c a) * Q := by
          rw [hv']
          have : ((y a).val : ℝ) * M * Q = ((y a).val : ℝ) := by
            rw [mul_assoc, hMQ, mul_one]
          linarith
        have hz : ((((y a).val : ℤ) - (n : ℤ) * W : ℤ) : ℝ) = c a * Q + (v - 2 * (W : ℝ)) * Q := by
          push_cast
          rw [hval, hnr]
          ring
        have hb1 : (v - 2 * (W : ℝ)) * Q ≤ 1 / 2 + d * Q := by
          have := mul_le_mul_of_nonneg_right h7.2 hQpos.le
          have e : (M / 2 + d) * Q = 1 / 2 + d * Q := by
            have : M * Q = 1 := hMQ
            nlinarith
          linarith
        have hb2 : -(1 / 2 + d * Q) ≤ (v - 2 * (W : ℝ)) * Q := by
          have := mul_le_mul_of_nonneg_right h7.1 hQpos.le
          have e : -(M / 2 + d) * Q = -(1 / 2 + d * Q) := by
            have : M * Q = 1 := hMQ
            nlinarith
          linarith
        refine Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr ?_, Int.le_floor.mpr ?_⟩
        · rw [hz]
          linarith
        · rw [hz]
          linarith
      · show (((((y a).val : ℤ) - (n : ℤ) * W : ℤ)) : ZMod n) = y a
        rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_self, zero_mul, sub_zero,
          ZMod.natCast_zmod_val]
    have hcard := Finset.card_le_card hsub'
    rw [Fintype.card_piFinset] at hcard
    have hone : ∀ a, (((Finset.Icc (lo a) (hi a)).image fun z : ℤ => (z : ZMod n)).card : ℝ) ≤
        2 * (d * Q) + 2 := by
      intro a
      have h1 : ((Finset.Icc (lo a) (hi a)).image fun z : ℤ => (z : ZMod n)).card ≤
          (Finset.Icc (lo a) (hi a)).card :=
        Finset.card_image_le
      rw [Int.card_Icc] at h1
      have hqd : 0 ≤ 2 * (d * Q) + 2 := by positivity
      by_cases hle : hi a + 1 - lo a ≤ 0
      · have : (hi a + 1 - lo a).toNat = 0 := Int.toNat_of_nonpos hle
        rw [this] at h1
        have h0 : ((Finset.Icc (lo a) (hi a)).image fun z : ℤ => (z : ZMod n)).card = 0 := by omega
        rw [h0]
        simpa using hqd
      · have hpos : 0 ≤ hi a + 1 - lo a := by omega
        have h2 : (((Finset.Icc (lo a) (hi a)).image fun z : ℤ => (z : ZMod n)).card : ℤ) ≤ hi a + 1 - lo a := by
          have := Int.toNat_of_nonneg hpos
          omega
        have h3 : (((Finset.Icc (lo a) (hi a)).image fun z : ℤ => (z : ZMod n)).card : ℝ) ≤
            (hi a : ℝ) + 1 - (lo a : ℝ) := by
          exact_mod_cast h2
        have h4 : (hi a : ℝ) ≤ c a * Q + 1 / 2 + d * Q := Int.floor_le _
        have h5 : c a * Q - 1 / 2 - d * Q ≤ (lo a : ℝ) := Int.le_ceil _
        linarith
    calc ((weightSupportSites L t n (torusWeightAtBarycentres L K (fineSide L t n) (φ i))).card : ℝ)
        ≤ ((∏ a, ((Finset.Icc (lo a) (hi a)).image fun z : ℤ => (z : ZMod n)).card : ℕ) : ℝ) := by
          exact_mod_cast hcard
      _ = ∏ a, (((Finset.Icc (lo a) (hi a)).image fun z : ℤ => (z : ZMod n)).card : ℝ) := by push_cast; rfl
      _ ≤ ∏ _a : Fin 4, (2 * (d * Q) + 2) := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun a _ => hone a
      _ = (2 * (d * Q) + 2) ^ 4 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · obtain ⟨x, hx, hxp⟩ := exists_near_of_mem_supportSites hPl hC hodd φ K t ht n hs i hy
    obtain ⟨x', hx', hxp'⟩ := exists_near_of_mem_supportSites hPl hC hodd φ K t ht n hs j hy'
    set M : ℝ := (L : ℝ) ^ t / (L : ℝ) ^ K with hM
    have hMp : 0 < M := by positivity
    have hhalf : (L : ℝ) ^ t / (2 * (L : ℝ) ^ K) = M / 2 := by
      rw [hM]
      field_simp
    set e : ℕ := supDist y y' with he
    have hco : ∀ a, |circleRep 2 (x a - x' a)| ≤ ((e : ℝ) + 1) * M := by
      intro a
      have h1 : |circleRep 2 (((y a).val : ℝ) * M - ((y' a).val : ℝ) * M)| ≤ (e : ℝ) * M := by
        have h2 := hsc (n : ℝ) M (by rw [hnr]; positivity) hMp (((y a).val : ℝ) - ((y' a).val : ℝ))
        rw [hnM] at h2
        have h3 := hsite n (y a) (y' a)
        have h4 := (supDist_le_iff _ _ _).mp (le_refl e) a
        have h5 : ((((y a - y' a).valMinAbs).natAbs : ℕ) : ℝ) ≤ e := by exact_mod_cast h4
        rw [show ((y a).val : ℝ) * M - ((y' a).val : ℝ) * M = (((y a).val : ℝ) - ((y' a).val : ℝ)) * M by ring, h2,
          abs_mul, abs_of_pos hMp]
        exact mul_le_mul_of_nonneg_right (h3.le.trans h5) hMp.le
      have h6 := hxp a
      have h7 := hxp' a
      have h8 := hneg 2 two_pos (((y a).val : ℝ) * M - x a)
      have h9 := hsub 2 two_pos (-(((y a).val : ℝ) * M - x a)) (((y a).val : ℝ) * M - ((y' a).val : ℝ) * M)
      have h10 := hsub 2 two_pos (-(((y a).val : ℝ) * M - x a) + (((y a).val : ℝ) * M - ((y' a).val : ℝ) * M))
        (((y' a).val : ℝ) * M - x' a)
      have h11 : -(((y a).val : ℝ) * M - x a) + (((y a).val : ℝ) * M - ((y' a).val : ℝ) * M) +
          (((y' a).val : ℝ) * M - x' a) = x a - x' a := by ring
      rw [h11] at h10
      rw [hhalf] at h6 h7
      nlinarith
    have hxs : x ∈ tsupport (φ i) := subset_tsupport _ (Function.mem_support.mpr hx)
    have hxs' : x' ∈ tsupport (φ j) := subset_tsupport _ (Function.mem_support.mpr hx')
    have hap := hφ.separated i j hij x hxs x' hxs' fun a => -round ((x a - x' a) / 2)
    have hvec : euclidNormVec (fun a => x a - x' a + 2 * (((-round ((x a - x' a) / 2) : ℤ)) : ℝ)) ≤
        2 * (((e : ℝ) + 1) * M) := by
      refine euclidNormVec_le_two_mul (by positivity) fun a => ?_
      have : x a - x' a + 2 * (((-round ((x a - x' a) / 2) : ℤ)) : ℝ) = circleRep 2 (x a - x' a) := by
        unfold circleRep
        push_cast
        ring
      rw [this]
      exact hco a
    have hfin := hap.trans hvec
    have hMQ : M * (L : ℝ) ^ (K - t) = 1 := by
      rw [hM, ← hQt]
      field_simp
    have := mul_le_mul_of_nonneg_right hfin hPQ.le
    nlinarith
end PeriodizedLevelData
end YangMills.Construction.StateLaws
end
