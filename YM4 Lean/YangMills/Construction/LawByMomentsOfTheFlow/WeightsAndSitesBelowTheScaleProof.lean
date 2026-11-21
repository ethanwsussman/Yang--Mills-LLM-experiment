import YangMills.Construction.LawByMomentsOfTheFlow.DistanceOfTheSitesOfTwoSupports
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAtTheLastFarLevelInALimitFieldProof
import YangMills.Construction.LawInAState.WeightsOfMarksOnTheLeastTorusProof
import YangMills.Construction.ResponseInTheExpansion.RemainderOfTheResponseReturnsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
private theorem supDist_le_dist (x y : TestFunctions.EuclideanFourSpace) : supDist x y ≤ dist x y := by apply _root_.YangMills.SharedProofs.p2932 <;> assumption
private theorem norm_le_two_mul_of_abs_coord_le {x : TestFunctions.EuclideanFourSpace} {R : ℝ}
    (h : ∀ a, |x a| ≤ R) : ‖x‖ ≤ 2 * R := by apply _root_.YangMills.SharedProofs.p52306 <;> assumption
private theorem admissible_of_supAdmissible {k : ℕ} {P : LevelTestFunctions.LevelData k} {L : ℕ} {R d : ℝ}
    (h : P.SupAdmissible L R d) : P.Admissible L (2 * R) d where
  isTestFamily :=
    { lipschitzWith_one := fun i => LipschitzWith.of_dist_le_mul fun x y => by
        rw [NNReal.coe_one, one_mul, Real.dist_eq]
        exact (h.isSupTestFamily.lipschitz i x y).trans (supDist_le_dist x y)
      abs_le_one := h.isSupTestFamily.abs_le_one
      tsupport_subset_closedBall := fun i x hx => by
        rw [mem_closedBall_zero_iff]
        exact norm_le_two_mul_of_abs_coord_le (h.isSupTestFamily.abs_coord_le i x hx)
      le_dist_of_ne := fun i j hij x hx y hy =>
        (h.isSupTestFamily.le_supDist i j hij x hx y hy).trans (supDist_le_dist x y) }
  scaleLevel_le := h.scaleLevel_le
  support_small := h.support_small
  exists_ne_zero := h.exists_ne_zero
private theorem abs_circleRep_le {c : ℝ} (hc : 0 < c) (v : ℝ) : |LevelTestFunctions.circleRep c v| ≤ c / 2 := by apply _root_.YangMills.SharedProofs.p64351 <;> assumption
private theorem far_of_add_circleRep_ne {T w w' : ℝ} (hT : 0 < T) (hw : |w| ≤ T / 8) (hw' : |w'| ≤ T / 2)
    (hne : w + LevelTestFunctions.circleRep T (w' - w) ≠ w') :
    3 * T / 8 ≤ |w'| ∧ 3 * T / 8 ≤ |w + LevelTestFunctions.circleRep T (w' - w)| := by
  have ho := abs_circleRep_le hT (w' - w)
  obtain ⟨e, he⟩ : ∃ e : ℤ, e = round ((w' - w) / T) := ⟨_, rfl⟩
  have hdiff : w + LevelTestFunctions.circleRep T (w' - w) - w' = -(T * e) := by
    unfold LevelTestFunctions.circleRep
    rw [he]
    ring
  have he0 : e ≠ 0 := by
    intro h0
    apply hne
    rw [h0] at hdiff
    simp only [Int.cast_zero, mul_zero, neg_zero] at hdiff
    linarith
  have he1 : (1 : ℝ) ≤ |(e : ℝ)| := by
    have : (1 : ℤ) ≤ |e| := Int.one_le_abs he0
    exact_mod_cast this
  have hbig : T ≤ |w + LevelTestFunctions.circleRep T (w' - w) - w'| := by
    rw [hdiff, abs_neg, abs_mul, abs_of_pos hT]
    nlinarith
  have htri : |w + LevelTestFunctions.circleRep T (w' - w) - w'| ≤
      |w + LevelTestFunctions.circleRep T (w' - w)| + |w'| := abs_sub _ _
  have hsum : |w + LevelTestFunctions.circleRep T (w' - w)| ≤
      |w| + |LevelTestFunctions.circleRep T (w' - w)| := abs_add_le _ _
  constructor <;> linarith
private theorem two_mul_barycenterCoord {m : ℕ} [NeZero m] (p : TorusFields.TorusPlaquette m) (a : Fin 4) :
    ∃ e : ℤ, 2 * LevelTestFunctions.barycenterCoord p a =
      ((WeightedResponses.doubledBarycentre p a).val : ℝ) + ((2 * m : ℕ) : ℝ) * e := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = 2 * (p.1 a).val + (if a = p.2.1 then 1 else 0) + (if a = p.2.2 then 1 else 0) :=
    ⟨_, rfl⟩
  have hval : (WeightedResponses.doubledBarycentre p a).val = n % (2 * m) := by
    show (((2 * (p.1 a).val + (if a = p.2.1 then 1 else 0) + (if a = p.2.2 then 1 else 0) : ℕ)) :
      ZMod (2 * m)).val = _
    rw [← hn]
    have : NeZero (2 * m) := ⟨mul_ne_zero two_ne_zero (NeZero.ne m)⟩
    exact ZMod.val_natCast _ _
  refine ⟨((n / (2 * m) : ℕ) : ℤ), ?_⟩
  have hmod : n % (2 * m) + (2 * m) * (n / (2 * m)) = n := Nat.mod_add_div _ _
  have hcast : ((n : ℕ) : ℝ) = ((WeightedResponses.doubledBarycentre p a).val : ℝ) +
      ((2 * m : ℕ) : ℝ) * ((n / (2 * m) : ℕ) : ℝ) := by
    rw [hval]
    exact_mod_cast hmod.symm
  have h2 : 2 * LevelTestFunctions.barycenterCoord p a = (n : ℝ) := by
    rw [hn]
    unfold LevelTestFunctions.barycenterCoord
    split_ifs <;> push_cast <;> ring
  rw [h2, hcast, Int.cast_natCast]
private theorem two_mul_abs_circleRep_mul_le_supDist (hC : LevelTestFunctions.CircleRepProperties) {m : ℕ}
    [NeZero m] {T A : ℝ} (hT : 0 < T) (hA : 0 < A) (hm : (m : ℝ) = T * A)
    (p p' : TorusFields.TorusPlaquette m) (x : ℝ) (a : Fin 4) :
    2 * |LevelTestFunctions.circleRep T
        (LevelTestFunctions.circleRep T (LevelTestFunctions.barycenterCoord p' a / A - x) -
          LevelTestFunctions.circleRep T (LevelTestFunctions.barycenterCoord p a / A - x))| * A ≤
      (TorusFields.supDist (WeightedResponses.doubledBarycentre p)
        (WeightedResponses.doubledBarycentre p') : ℝ) := by
  obtain ⟨h1, -, -, -, -, h6, h7⟩ := hC
  have : NeZero (2 * m) := ⟨mul_ne_zero two_ne_zero (NeZero.ne m)⟩
  have hN : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by
    have : 0 < 2 * m := Nat.pos_of_ne_zero (NeZero.ne _)
    exact_mod_cast this
  have step1 : LevelTestFunctions.circleRep T
        (LevelTestFunctions.circleRep T (LevelTestFunctions.barycenterCoord p' a / A - x) -
          LevelTestFunctions.circleRep T (LevelTestFunctions.barycenterCoord p a / A - x)) =
      LevelTestFunctions.circleRep T
        ((LevelTestFunctions.barycenterCoord p' a - LevelTestFunctions.barycenterCoord p a) / A) := by
    rw [← h1 T hT ((LevelTestFunctions.barycenterCoord p' a - LevelTestFunctions.barycenterCoord p a) / A)
      (round ((LevelTestFunctions.barycenterCoord p a / A - x) / T) -
        round ((LevelTestFunctions.barycenterCoord p' a / A - x) / T))]
    congr 1
    unfold LevelTestFunctions.circleRep
    push_cast
    ring
  have step2 := h6 T (2 * A) hT (by positivity)
    ((LevelTestFunctions.barycenterCoord p' a - LevelTestFunctions.barycenterCoord p a) / A)
  have hc : T * (2 * A) = ((2 * m : ℕ) : ℝ) := by
    push_cast
    rw [hm]
    ring
  obtain ⟨e, he⟩ := two_mul_barycenterCoord p a
  obtain ⟨e', he'⟩ := two_mul_barycenterCoord p' a
  have hv : (LevelTestFunctions.barycenterCoord p' a - LevelTestFunctions.barycenterCoord p a) / A * (2 * A) =
      ((WeightedResponses.doubledBarycentre p' a).val : ℝ) - ((WeightedResponses.doubledBarycentre p a).val : ℝ) +
        ((2 * m : ℕ) : ℝ) * ((e' - e : ℤ) : ℝ) := by
    have : (LevelTestFunctions.barycenterCoord p' a - LevelTestFunctions.barycenterCoord p a) / A * (2 * A) =
        2 * LevelTestFunctions.barycenterCoord p' a - 2 * LevelTestFunctions.barycenterCoord p a := by
      field_simp
    rw [this, he, he']
    push_cast
    ring
  rw [hc, hv, h1 _ hN] at step2
  have step3 := h7 (2 * m) (WeightedResponses.doubledBarycentre p' a) (WeightedResponses.doubledBarycentre p a)
  have hle : (((WeightedResponses.doubledBarycentre p' a - WeightedResponses.doubledBarycentre p a).valMinAbs).natAbs
        : ℝ) ≤
      (TorusFields.supDist (WeightedResponses.doubledBarycentre p') (WeightedResponses.doubledBarycentre p) : ℝ) := by
    have : ((WeightedResponses.doubledBarycentre p' a - WeightedResponses.doubledBarycentre p a).valMinAbs).natAbs ≤
        TorusFields.supDist (WeightedResponses.doubledBarycentre p') (WeightedResponses.doubledBarycentre p) :=
      Finset.le_sup (f := fun i => ((WeightedResponses.doubledBarycentre p' i -
        WeightedResponses.doubledBarycentre p i).valMinAbs).natAbs) (Finset.mem_univ a)
    exact_mod_cast this
  rw [TorusFields.supDist_comm] at hle
  rw [step1]
  have h2 : 2 * |LevelTestFunctions.circleRep T
        ((LevelTestFunctions.barycenterCoord p' a - LevelTestFunctions.barycenterCoord p a) / A)| * A =
      |LevelTestFunctions.circleRep T
        ((LevelTestFunctions.barycenterCoord p' a - LevelTestFunctions.barycenterCoord p a) / A) * (2 * A)| := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * A)]
    ring
  rw [h2, ← step2, step3]
  exact hle
private def scaledPoint (M : ℝ) (w : Fin 4 → ℝ) : TestFunctions.EuclideanFourSpace :=
  WithLp.toLp 2 fun a => M * w a
private def circleCoords {k : ℕ} (P : LevelTestFunctions.LevelData k) (L : ℕ) {m : ℕ}
    (q : TorusFields.TorusPlaquette m) (a : Fin 4) : ℝ :=
  LevelTestFunctions.circleRep (P.period L) (LevelTestFunctions.barycenterCoord q a / (L : ℝ) ^ P.windowLevel - P.center a)
private theorem testWeight_eq {k : ℕ} (P : LevelTestFunctions.LevelData k) (L : ℕ) (i : Fin k) {m : ℕ}
    (q : TorusFields.TorusPlaquette m) :
    P.testWeight L i m q =
      P.fn i (scaledPoint ((L : ℝ) ^ P.windowLevel / (L : ℝ) ^ P.scaleLevel) (circleCoords P L q)) := rfl
private theorem fn_eq_zero_of_far {k : ℕ} {P : LevelTestFunctions.LevelData k} {L : ℕ} {R d : ℝ}
    (h : P.SupAdmissible L R d) (i : Fin k) {M T : ℝ} (hM : 0 < M) (hT : 0 < T) (hR : R ≤ T * M / 8)
    (w : Fin 4 → ℝ) (a : Fin 4) (hfar : 3 * T / 8 ≤ |w a|) : P.fn i (scaledPoint M w) = 0 := by
  by_contra hne
  have h1 : |(scaledPoint M w) a| ≤ R := h.isSupTestFamily.abs_coord_le i _ (subset_tsupport _ hne) a
  have h2 : (scaledPoint M w) a = M * w a := rfl
  rw [h2, abs_mul, abs_of_pos hM] at h1
  have h3 : 0 < T * M := mul_pos hT hM
  nlinarith
private theorem abs_coord_le_of_fn_ne_zero {k : ℕ} {P : LevelTestFunctions.LevelData k} {L : ℕ} {R d : ℝ}
    (h : P.SupAdmissible L R d) (i : Fin k) {M T : ℝ} (hM : 0 < M) (hR : R ≤ T * M / 8) (w : Fin 4 → ℝ)
    (hne : P.fn i (scaledPoint M w) ≠ 0) (a : Fin 4) : |w a| ≤ T / 8 := by
  have h1 : |(scaledPoint M w) a| ≤ R := h.isSupTestFamily.abs_coord_le i _ (subset_tsupport _ hne) a
  have h2 : (scaledPoint M w) a = M * w a := rfl
  rw [h2, abs_mul, abs_of_pos hM] at h1
  have h3 : M * |w a| ≤ M * (T / 8) := by linarith
  exact le_of_mul_le_mul_left h3 hM
private theorem abs_testWeight_sub_le_of_ne_zero {k : ℕ} {P : LevelTestFunctions.LevelData k} {L : ℕ} [NeZero L]
    {R d : ℝ} (hC : LevelTestFunctions.CircleRepProperties) (h : P.SupAdmissible L R d) {u : ℕ}
    (hu : u ≤ P.scaleLevel) (i : Fin k) {m : ℕ} [NeZero m] (hm : m = P.period L * L ^ P.windowLevel)
    (p p' : TorusFields.TorusPlaquette m) (hp : P.testWeight L i m p ≠ 0) :
    |P.testWeight L i m p - P.testWeight L i m p'| ≤ WeightedResponses.barycentreDist L u p p' := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hA : (0 : ℝ) < (L : ℝ) ^ P.windowLevel := by positivity
  have hB : (0 : ℝ) < (L : ℝ) ^ P.scaleLevel := by positivity
  have hT : (0 : ℝ) < (P.period L : ℝ) := by
    have : 0 < P.period L := Nat.pos_of_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (NeZero.ne L)))
    exact_mod_cast this
  have hmc : (m : ℝ) = (P.period L : ℝ) * (L : ℝ) ^ P.windowLevel := by
    rw [hm]
    push_cast
    ring
  have hUB : (L : ℝ) ^ u ≤ (L : ℝ) ^ P.scaleLevel := pow_le_pow_right₀ hL1 hu
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ P.scaleLevel := ⟨_, rfl⟩
  have hM : 0 < M := by
    rw [hMd]
    positivity
  have hMB : M * (L : ℝ) ^ P.scaleLevel = (L : ℝ) ^ P.windowLevel := by
    rw [hMd]
    field_simp
  have hR : R ≤ (P.period L : ℝ) * M / 8 := by
    have h1 := h.support_small
    have h2 : R * (L : ℝ) ^ P.scaleLevel ≤ ((P.period L : ℝ) * M / 8) * (L : ℝ) ^ P.scaleLevel := by
      have : ((P.period L : ℝ) * M / 8) * (L : ℝ) ^ P.scaleLevel =
          (P.period L : ℝ) / 8 * (M * (L : ℝ) ^ P.scaleLevel) := by ring
      rw [this, hMB]
      linarith
    exact le_of_mul_le_mul_right h2 hB
  rw [testWeight_eq, ← hMd] at hp
  rw [testWeight_eq, testWeight_eq, ← hMd]
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → ℝ, w = circleCoords P L p := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : Fin 4 → ℝ, w' = circleCoords P L p' := ⟨_, rfl⟩
  rw [← hw] at hp
  rw [← hw, ← hw']
  have hnear := abs_coord_le_of_fn_ne_zero h i hM hR w hp
  have hhalf : ∀ a, |w' a| ≤ (P.period L : ℝ) / 2 := fun a => by
    rw [hw']
    exact abs_circleRep_le hT _
  obtain ⟨o, ho⟩ : ∃ o : Fin 4 → ℝ, o = fun a => LevelTestFunctions.circleRep (P.period L) (w' a - w a) :=
    ⟨_, rfl⟩
  have heq : P.fn i (scaledPoint M fun a => w a + o a) = P.fn i (scaledPoint M w') := by
    by_cases hall : ∀ a, w a + o a = w' a
    · have : (fun a => w a + o a) = w' := funext hall
      rw [this]
    · obtain ⟨a, ha⟩ := not_forall.mp hall
      rw [ho] at ha
      obtain ⟨f1, f2⟩ := far_of_add_circleRep_ne hT (hnear a) (hhalf a) ha
      rw [fn_eq_zero_of_far h i hM hT hR w' a f1]
      refine fn_eq_zero_of_far h i hM hT hR _ a ?_
      rw [ho]
      exact f2
  rw [← heq]
  refine (h.isSupTestFamily.lipschitz i _ _).trans ?_
  unfold supDist
  refine ciSup_le fun a => ?_
  have hcoord : (scaledPoint M w) a - (scaledPoint M fun a => w a + o a) a = -(M * o a) := by
    show M * w a - M * (w a + o a) = _
    ring
  rw [hcoord, abs_neg, abs_mul, abs_of_pos hM]
  have htw := two_mul_abs_circleRep_mul_le_supDist hC hT hA hmc p p' (P.center a) a
  have hoa : o a = LevelTestFunctions.circleRep (P.period L)
      (LevelTestFunctions.circleRep (P.period L)
          (LevelTestFunctions.barycenterCoord p' a / (L : ℝ) ^ P.windowLevel - P.center a) -
        LevelTestFunctions.circleRep (P.period L)
          (LevelTestFunctions.barycenterCoord p a / (L : ℝ) ^ P.windowLevel - P.center a)) := by
    rw [ho, hw, hw']
    rfl
  rw [← hoa] at htw
  unfold WeightedResponses.barycentreDist
  rw [le_div_iff₀ (by positivity)]
  have hq : (L : ℝ) ^ u / (L : ℝ) ^ P.scaleLevel ≤ 1 := (div_le_one hB).mpr hUB
  have hnn : 0 ≤ 2 * |o a| * (L : ℝ) ^ P.windowLevel := by positivity
  calc M * |o a| * (2 * (L : ℝ) ^ u)
      = 2 * |o a| * (L : ℝ) ^ P.windowLevel * ((L : ℝ) ^ u / (L : ℝ) ^ P.scaleLevel) := by
        rw [hMd]
        field_simp
    _ ≤ 2 * |o a| * (L : ℝ) ^ P.windowLevel * 1 := mul_le_mul_of_nonneg_left hq hnn
    _ ≤ _ := by linarith
private theorem barycentreDist_nonneg (L u : ℕ) {m : ℕ} (p p' : TorusFields.TorusPlaquette m) :
    0 ≤ WeightedResponses.barycentreDist L u p p' := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.barycentreDist_nonneg <;> assumption
private theorem barycentreDist_comm (L u : ℕ) {m : ℕ} [NeZero m] (p p' : TorusFields.TorusPlaquette m) :
    WeightedResponses.barycentreDist L u p p' = WeightedResponses.barycentreDist L u p' p := by
  have : NeZero (2 * m) := ⟨mul_ne_zero two_ne_zero (NeZero.ne m)⟩
  unfold WeightedResponses.barycentreDist
  rw [TorusFields.supDist_comm]
private theorem abs_testWeight_sub_le {k : ℕ} {P : LevelTestFunctions.LevelData k} {L : ℕ} [NeZero L] {R d : ℝ}
    (hC : LevelTestFunctions.CircleRepProperties) (h : P.SupAdmissible L R d) {u : ℕ} (hu : u ≤ P.scaleLevel)
    (i : Fin k) {m : ℕ} [NeZero m] (hm : m = P.period L * L ^ P.windowLevel) (p p' : TorusFields.TorusPlaquette m) :
    |P.testWeight L i m p - P.testWeight L i m p'| ≤ WeightedResponses.barycentreDist L u p p' := by
  by_cases hp : P.testWeight L i m p = 0
  · by_cases hp' : P.testWeight L i m p' = 0
    · rw [hp, hp', sub_self, abs_zero]
      exact barycentreDist_nonneg L u p p'
    · rw [abs_sub_comm, barycentreDist_comm]
      exact abs_testWeight_sub_le_of_ne_zero hC h hu i hm p' p hp'
  · exact abs_testWeight_sub_le_of_ne_zero hC h hu i hm p p' hp
private theorem weightNorm_testWeight_le_one {k : ℕ} {P : LevelTestFunctions.LevelData k} {L : ℕ} [NeZero L]
    {R d : ℝ} (hC : LevelTestFunctions.CircleRepProperties) (h : P.SupAdmissible L R d) {u : ℕ}
    (hu : u ≤ P.scaleLevel) (i : Fin k) {m : ℕ} [NeZero m] (hm : m = P.period L * L ^ P.windowLevel) :
    WeightedResponses.weightNorm L u (P.testWeight L i m) ≤ 1 := by
  refine max_le (Real.iSup_le (fun q => h.isSupTestFamily.abs_le_one i _) zero_le_one)
    (Real.iSup_le (fun pp => ?_) zero_le_one)
  have h1 := abs_testWeight_sub_le hC h hu i hm pp.1.1 pp.2.1
  rcases eq_or_lt_of_le (barycentreDist_nonneg L u pp.1.1 pp.2.1) with h0 | h0
  · rw [← h0, div_zero]
    exact zero_le_one
  · exact (div_le_one h0).mpr h1
private theorem card_supportSites_le {k : ℕ} {P : LevelTestFunctions.LevelData k} {L : ℕ} [NeZero L] {R d : ℝ}
    (hL : Odd L) (hd : 0 < d) (hD : LevelTestFunctions.SupportSiteDistanceBounds) (h : P.SupAdmissible L R d)
    {u : ℕ} (hu : u ≤ P.scaleLevel) (i : Fin k) :
    ((P.supportSites L u i).card : ℝ) ≤ (8 * |R| + 5) ^ 4 * (L : ℝ) ^ (4 * (P.scaleLevel - u)) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨Z, hZd⟩ : ∃ Z : ℝ, Z = (L : ℝ) ^ (P.scaleLevel - u) := ⟨_, rfl⟩
  have hZ1 : 1 ≤ Z := by
    rw [hZd]
    exact one_le_pow₀ hL1
  have hzp : (L : ℝ) ^ ((P.scaleLevel : ℤ) - (u : ℤ)) = Z := by
    rw [hZd, ← Nat.cast_sub hu, zpow_natCast]
  have hpow : (L : ℝ) ^ (4 * (P.scaleLevel - u)) = Z ^ 4 := by
    rw [hZd, pow_mul']
  rw [hpow]
  have hpos : 0 ≤ (8 * |R| + 5) ^ 4 * Z ^ 4 := by positivity
  rcases (P.supportSites L u i).eq_empty_or_nonempty with he | ⟨y₀, hy₀⟩
  · rw [he]
    simpa using hpos
  · obtain ⟨r, hrd⟩ : ∃ r : ℕ, r = ⌈4 * |R| * Z + 1⌉₊ := ⟨_, rfl⟩
    have hr1 : 4 * |R| * Z + 1 ≤ (r : ℝ) := by
      rw [hrd]
      exact Nat.le_ceil _
    have hr2 : (r : ℝ) < 4 * |R| * Z + 1 + 1 := by
      rw [hrd]
      exact Nat.ceil_lt_add_one (by positivity)
    have hsubset : P.supportSites L u i ⊆
        TorusLumps.thickening r ({y₀} : Finset (TorusFields.TorusSite (P.sideAt L u))) := by
      intro y hy
      rw [TorusFields.mem_thickening]
      refine ⟨y₀, Finset.mem_singleton_self _, ?_⟩
      have h1 := (hD L hL k (2 * R) d hd P (admissible_of_supAdmissible h) u (hu.trans h.scaleLevel_le)
        i i y hy y₀ hy₀).1
      rw [hzp] at h1
      have h2 : 2 * (2 * R) * Z ≤ 4 * |R| * Z := by
        have := le_abs_self R
        nlinarith
      have h3 : (TorusFields.supDist y y₀ : ℝ) ≤ (r : ℝ) := by linarith
      exact_mod_cast h3
    have hcard := (Finset.card_le_card hsubset).trans (TorusBalls.card_thickening_singleton_le r y₀)
    have hcr : ((P.supportSites L u i).card : ℝ) ≤ (2 * (r : ℝ) + 1) ^ 4 := by exact_mod_cast hcard
    have h4 : 2 * (r : ℝ) + 1 ≤ (8 * |R| + 5) * Z := by
      have : 0 ≤ |R| := abs_nonneg R
      nlinarith
    have h5 : (2 * (r : ℝ) + 1) ^ 4 ≤ ((8 * |R| + 5) * Z) ^ 4 := pow_le_pow_left₀ (by positivity) h4 4
    rw [mul_pow] at h5
    exact hcr.trans h5
theorem weightsSitesBelowScaleStatement_holds (hC : LevelTestFunctions.CircleRepProperties)
    (hD : LevelTestFunctions.SupportSiteDistanceBounds) : weightsSitesBelowScaleStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L hL _ Tb _ hTL _ _ _ _ _ Kr _
  refine ⟨0, fun y _ _ _ g _ _ k _ _ _ R d hd => ?_⟩
  refine ⟨fun _ => (8 * |R| + 5) ^ 4, 1, y, one_pos, le_refl _, fun S u hu i => ?_⟩
  have hodd : Odd (Tb.stepParameters y).side := by
    show Odd Tb.side
    rw [hTL]
    exact hL
  refine ⟨weightNorm_testWeight_le_one hC S.supAdmissible hu i ?_,
    card_supportSites_le hodd hd hD S.supAdmissible hu i⟩
  rw [WeightedResponses.fineSide_eq]
  show S.data.period (Tb.stepParameters y).side * (Tb.stepParameters y).side ^ (S.data.windowLevel - u) *
    (Tb.stepParameters y).side ^ u = _
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (hu.trans S.supAdmissible.scaleLevel_le)]
end YangMills.Construction.MomentLaw
end
