import YangMills.Construction.Continuum.ChosenSmoothFunctionsPartitionsOfUnityRotationsAndIntegrabilityProof
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.TorusOrFourSpace.BoundOnTheDiameterBearsOnBoxesNotOnUnions
import YangMills.Construction.TorusOrFourSpace.CountableFamilyOfACountableChoice
import YangMills.Construction.TorusOrFourSpace.QuotientMapCompactSetsAndFunctionsOfClassC1
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace PeriodicSpace.BoxDiameter
open Kind
private theorem euclidNormVec_add_le (a b : Fin 4 → ℝ) :
    euclidNormVec (a + b) ≤ euclidNormVec a + euclidNormVec b := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
private theorem euclidNormVec_sub_comm (a b : Fin 4 → ℝ) :
    euclidNormVec (a - b) = euclidNormVec (b - a) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
private theorem euclidNormVec_smul {c : ℝ} (hc : 0 ≤ c) (v : Fin 4 → ℝ) :
    euclidNormVec (c • v) = c * euclidNormVec v := by apply _root_.YangMills.Construction.WightmanReconstruction.SmoothToolkit.euclidNormVec_smul_of_nonneg <;> assumption
private theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (i : Fin 4) :
    |v i| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem halfEdge_pos (P : Params) : 0 < P.halfEdge := by
  have hL : 13 ≤ P.L := P.isAdmissible.2
  have h0 : (0 : ℝ) < P.L := by exact_mod_cast (by omega : 0 < P.L)
  exact pow_pos h0 _
private theorem side_eq_two_mul_halfEdge (P : Params) : P.side = 2 * P.halfEdge := rfl
private theorem exists_int_of_quotMap_eq (P : Params) {a b : Fin 4 → ℝ}
    (h : quotMap P torus a = quotMap P torus b) :
    ∃ n : Fin 4 → ℤ, ∀ i, a i - b i = (n i : ℝ) * P.side := by
  have h' : torusProj P.side a = torusProj P.side b := h
  have hi : ∀ i, ∃ n : ℤ, a i - b i = (n : ℝ) * P.side := by
    intro i
    have h1 : ((a i : ℝ) : AddCircle P.side) = (b i : ℝ) := congrFun h' i
    have h2 : ((a i - b i : ℝ) : AddCircle P.side) = 0 := by
      rw [AddCircle.coe_sub, h1, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff P.side).1 h2
    exact ⟨n, by rw [← hn, zsmul_eq_mul]⟩
  choose n hn using hi
  exact ⟨n, hn⟩
private theorem quotMap_eq_of_int (P : Params) {a b : Fin 4 → ℝ} (n : Fin 4 → ℤ)
    (h : ∀ i, a i - b i = (n i : ℝ) * P.side) :
    quotMap P torus a = quotMap P torus b := by
  exact show torusProj P.side a = torusProj P.side b from by
    funext i
    have h1 : ((a i - b i : ℝ) : AddCircle P.side) = 0 :=
      (AddCircle.coe_eq_zero_iff P.side).2 ⟨n i, by rw [h, zsmul_eq_mul]⟩
    rw [AddCircle.coe_sub, sub_eq_zero] at h1
    exact h1
private theorem quotDist_eq_of_close (hq : Kind.QuotientCompactC1.Claim)
    (P : Params) (x y : Fin 4 → ℝ) (h : euclidNormVec (x - y) < P.halfEdge) :
    quotDist P torus (quotMap P torus x) (quotMap P torus y) = euclidNormVec (x - y) := by
  obtain ⟨⟨-, -, -, -, hle, hlift⟩, -⟩ := hq P torus
  have h1 := hle x y
  obtain ⟨z, hz, hzd⟩ := hlift (quotMap P torus x) (quotMap P torus y) x rfl
  obtain ⟨n, hn⟩ := exists_int_of_quotMap_eq P hz
  by_cases h0 : ∀ i, n i = 0
  · have hzy : z = y := funext fun i => by
      have h2 := hn i
      rw [h0 i] at h2
      simp only [Int.cast_zero, zero_mul] at h2
      linarith
    rw [← hzd, hzy]
  · exfalso
    push Not at h0
    obtain ⟨i, hi⟩ := h0
    have hs : 0 < P.side := by rw [side_eq_two_mul_halfEdge]; linarith [halfEdge_pos P]
    have h2 : P.side ≤ |z i - y i| := by
      rw [hn i, abs_mul, abs_of_pos hs]
      have h3 : (1 : ℝ) ≤ |(n i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
      nlinarith
    have h3 : |(z - y) i| ≤ euclidNormVec (z - y) := abs_apply_le_euclidNormVec _ _
    have h4 : euclidNormVec (z - y) ≤ euclidNormVec (z - x) + euclidNormVec (x - y) := by
      have h5 := euclidNormVec_add_le (z - x) (x - y)
      rwa [sub_add_sub_cancel] at h5
    rw [euclidNormVec_sub_comm z x, hzd] at h4
    simp only [Pi.sub_apply] at h3
    rw [side_eq_two_mul_halfEdge] at h2
    linarith
private theorem quotDist_le_setDiam (P : Params) {S : Set (torus.Pt P)} {z w : torus.Pt P}
    (hz : z ∈ S) (hw : w ∈ S) : ENNReal.ofReal (quotDist P torus z w) ≤ setDiam P torus S :=
  le_iSup₂_of_le z hz (le_iSup₂_of_le w hw le_rfl)
private theorem lo_mem_toSet (B : RationalBox) : (fun i => (B.lo i : ℝ)) ∈ B.toSet := by
  refine Set.mem_univ_pi.2 fun i => ⟨le_rfl, ?_⟩
  exact_mod_cast (B.lo_lt_hi i).le
private theorem hi_mem_toSet (B : RationalBox) : (fun i => (B.hi i : ℝ)) ∈ B.toSet := by
  refine Set.mem_univ_pi.2 fun i => ⟨?_, le_rfl⟩
  exact_mod_cast (B.lo_lt_hi i).le
private theorem euclidNormVec_sub_le_diam (B : RationalBox) {x y : Fin 4 → ℝ} (hx : x ∈ B.toSet)
    (hy : y ∈ B.toSet) : euclidNormVec (x - y) ≤ B.diam := by
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h1 := Set.mem_univ_pi.1 hx i
  have h2 := Set.mem_univ_pi.1 hy i
  refine sq_le_sq' ?_ ?_
  · simp only [Pi.sub_apply]
    linarith [h1.1, h1.2, h2.1, h2.2]
  · simp only [Pi.sub_apply]
    linarith [h1.1, h1.2, h2.1, h2.2]
private theorem diam_eq_corners (B : RationalBox) :
    B.diam = euclidNormVec ((fun i => (B.hi i : ℝ)) - fun i => (B.lo i : ℝ)) := rfl
private theorem image_of_small_box (hq : Kind.QuotientCompactC1.Claim)
    (P : Params) (B : RationalBox) (hB : B.diam < P.halfEdge) :
    (∀ x ∈ B.toSet, ∀ y ∈ B.toSet,
      quotDist P torus (quotMap P torus x) (quotMap P torus y) =
        euclidNormVec (x - y)) ∧
    Set.InjOn (quotMap P torus) B.toSet ∧
    setDiam P torus (quotMap P torus '' B.toSet) = ENNReal.ofReal B.diam := by
  have hd : ∀ x ∈ B.toSet, ∀ y ∈ B.toSet,
      quotDist P torus (quotMap P torus x) (quotMap P torus y) =
        euclidNormVec (x - y) := fun x hx y hy =>
    quotDist_eq_of_close hq P x y ((euclidNormVec_sub_le_diam B hx hy).trans_lt hB)
  refine ⟨hd, ?_, le_antisymm ?_ ?_⟩
  · intro x hx y hy hxy
    obtain ⟨⟨-, h0, -⟩, -⟩ := hq P torus
    have h1 := hd x hx y hy
    rw [(h0 _ _).2 hxy] at h1
    have h2 : ∑ i, (x - y) i ^ 2 = 0 := by
      have h3 : Real.sqrt (∑ i, (x - y) i ^ 2) = 0 := h1.symm
      exact le_antisymm (Real.sqrt_eq_zero'.1 h3) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    funext i
    have h3 : (x - y) i ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 h2 i (Finset.mem_univ i)
    have h4 : (x - y) i = 0 := by simpa using h3
    simp only [Pi.sub_apply] at h4
    linarith
  · refine iSup₂_le fun z hz => iSup₂_le fun w hw => ?_
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨y, hy, rfl⟩ := hw
    rw [hd x hx y hy]
    exact ENNReal.ofReal_le_ofReal (euclidNormVec_sub_le_diam B hx hy)
  · have h1 := quotDist_le_setDiam P (Set.mem_image_of_mem (quotMap P torus) (hi_mem_toSet B))
      (Set.mem_image_of_mem (quotMap P torus) (lo_mem_toSet B))
    rwa [hd _ (hi_mem_toSet B) _ (lo_mem_toSet B), ← diam_eq_corners] at h1
private theorem halfEdge_le_setDiam_image (hq : Kind.QuotientCompactC1.Claim)
    (P : Params) (B : RationalBox) (hB : P.halfEdge ≤ B.diam) :
    ENNReal.ofReal P.halfEdge ≤ setDiam P torus (quotMap P torus '' B.toSet) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  have hcTop : c ≠ ∞ := hc2.ne_top
  have hs : c.toReal < P.halfEdge :=
    (ENNReal.toReal_lt_of_lt_ofReal hc2)
  have hs0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  set s := c.toReal with hsdef
  have hdpos : 0 < B.diam := (halfEdge_pos P).trans_le hB
  set t := s / B.diam with htdef
  have ht0 : 0 ≤ t := div_nonneg hs0 hdpos.le
  have ht1 : t ≤ 1 := (div_le_one hdpos).2 (hs.le.trans hB)
  set a : Fin 4 → ℝ := fun i => (B.lo i : ℝ) with ha
  set b : Fin 4 → ℝ := fun i => (B.hi i : ℝ) with hb
  have hx : a + t • (b - a) ∈ B.toSet := by
    refine Set.mem_univ_pi.2 fun i => ?_
    have h1 : a i ≤ b i := by
      simp only [ha, hb]
      exact_mod_cast (B.lo_lt_hi i).le
    have h2 : (a + t • (b - a)) i = a i + t * (b i - a i) := rfl
    rw [h2]
    constructor
    · show a i ≤ _
      nlinarith
    · show _ ≤ b i
      nlinarith
  have hv : euclidNormVec ((a + t • (b - a)) - a) = s := by
    rw [add_sub_cancel_left, euclidNormVec_smul ht0, ← diam_eq_corners, htdef,
      div_mul_cancel₀ _ hdpos.ne']
  have h1 := quotDist_eq_of_close hq P (a + t • (b - a)) a (by rw [hv]; exact hs)
  have h2 := quotDist_le_setDiam P (Set.mem_image_of_mem (quotMap P torus) hx)
    (Set.mem_image_of_mem (quotMap P torus) (lo_mem_toSet B))
  rw [h1, hv, hsdef, ENNReal.ofReal_toReal hcTop] at h2
  exact absurd hc1 (not_lt.2 h2)
private theorem corner_sub_lattice (P : Params) (n : Fin 4 → ℤ) :
    (fun _ : Fin 4 => P.halfEdge) - (fun i => (n i : ℝ) * P.side) =
      P.halfEdge • fun i => 1 - 2 * (n i : ℝ) := by
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, side_eq_two_mul_halfEdge]
  ring
private theorem euclidNormVec_corner (P : Params) (n : Fin 4 → ℤ) :
    euclidNormVec ((fun _ : Fin 4 => P.halfEdge) - (fun i => (n i : ℝ) * P.side)) =
      P.halfEdge * Real.sqrt (∑ i, (1 - 2 * (n i : ℝ)) ^ 2) := by
  rw [corner_sub_lattice, euclidNormVec_smul (halfEdge_pos P).le]
  rfl
private theorem quotDist_corner_le (hq : Kind.QuotientCompactC1.Claim)
    (P : Params) (k : Fin 4 → ℤ) :
    quotDist P torus (quotMap P torus fun _ => P.halfEdge) (quotMap P torus 0) ≤
      P.halfEdge * Real.sqrt (∑ i, (1 - 2 * (k i : ℝ)) ^ 2) := by
  obtain ⟨⟨-, -, -, -, hle, -⟩, -⟩ := hq P torus
  have h1 : quotMap P torus (fun i => (k i : ℝ) * P.side) = quotMap P torus 0 :=
    quotMap_eq_of_int P k fun i => by simp
  rw [← h1, ← euclidNormVec_corner]
  exact hle _ _
private theorem exists_quotDist_corner_eq (hq : Kind.QuotientCompactC1.Claim)
    (P : Params) : ∃ n : Fin 4 → ℤ,
      P.halfEdge * Real.sqrt (∑ i, (1 - 2 * (n i : ℝ)) ^ 2) =
        quotDist P torus (quotMap P torus fun _ => P.halfEdge) (quotMap P torus 0) := by
  obtain ⟨⟨-, -, -, -, -, hlift⟩, -⟩ := hq P torus
  obtain ⟨z, hz, hzd⟩ := hlift (quotMap P torus fun _ => P.halfEdge) (quotMap P torus 0)
    (fun _ => P.halfEdge) rfl
  obtain ⟨n, hn⟩ := exists_int_of_quotMap_eq P hz
  have hzn : z = fun i => (n i : ℝ) * P.side := by
    funext i
    have h1 := hn i
    simpa using h1
  refine ⟨n, ?_⟩
  rw [← hzd, hzn, euclidNormVec_corner]
private theorem one_le_one_sub_two_mul_sq (n : ℤ) : (1 : ℝ) ≤ (1 - 2 * (n : ℝ)) ^ 2 := by
  have h : (0 : ℤ) ≤ n * (n - 1) := by
    rcases le_or_gt n 0 with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
    · exact mul_nonneg h.le (by omega)
  have h' : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by exact_mod_cast h
  nlinarith
private theorem quotDist_corner_eq (hq : Kind.QuotientCompactC1.Claim)
    (P : Params) :
    quotDist P torus (quotMap P torus fun _ => P.halfEdge) (quotMap P torus 0) =
      2 * P.halfEdge := by
  have hh := halfEdge_pos P
  refine le_antisymm ?_ ?_
  · have h1 := quotDist_corner_le hq P 0
    have h2 : Real.sqrt (∑ i : Fin 4, (1 - 2 * (((0 : Fin 4 → ℤ) i : ℤ) : ℝ)) ^ 2) = 2 := by
      have h3 : (∑ i : Fin 4, (1 - 2 * (((0 : Fin 4 → ℤ) i : ℤ) : ℝ)) ^ 2) = 2 ^ 2 := by
        simp
        norm_num
      rw [h3, Real.sqrt_sq (by norm_num)]
    rw [h2] at h1
    linarith
  · obtain ⟨n, hn⟩ := exists_quotDist_corner_eq hq P
    rw [← hn]
    have h1 : (2 : ℝ) ≤ Real.sqrt (∑ i, (1 - 2 * (n i : ℝ)) ^ 2) := by
      refine Real.le_sqrt' (by norm_num) |>.2 ?_
      have h2 : ∑ _i : Fin 4, (1 : ℝ) ≤ ∑ i, (1 - 2 * (n i : ℝ)) ^ 2 :=
        Finset.sum_le_sum fun i _ => one_le_one_sub_two_mul_sq (n i)
      have h3 : ∑ _i : Fin 4, (1 : ℝ) = 4 := by simp
      rw [h3] at h2
      linarith
    nlinarith
theorem torusBoxDiameterBound_holds (hq : Kind.QuotientCompactC1.Claim)
    (hF : CountableChoiceFamilyFacts) :
    TorusBoxDiameterBound := by
  intro P
  have hh := halfEdge_pos P
  have hadm : ∀ B : RationalBox, AdmitsBox P B torus ↔ B.diam < P.halfEdge := fun B => by
    have h1 : P.side / 2 = P.halfEdge := by rw [side_eq_two_mul_halfEdge]; ring
    show B.diam < P.side / 2 ↔ _
    rw [h1]
  have hcompact : IsCompactQ P torus Set.univ := (hq P torus).2.2.1
  have hopen : IsOpenQ P torus Set.univ := fun _ _ => ⟨1, one_pos, fun _ _ => trivial⟩
  have hdiam : ENNReal.ofReal (quotDist P torus (quotMap P torus fun _ => P.halfEdge)
      (quotMap P torus 0)) ≤ setDiam P torus Set.univ :=
    quotDist_le_setDiam P (Set.mem_univ _) (Set.mem_univ _)
  refine ⟨quotDist_eq_of_close hq P, hadm,
    fun B hB => image_of_small_box hq P B ((hadm B).1 hB),
    halfEdge_le_setDiam_image hq P, ?_, ?_, ?_, ?_, hdiam, ?_, quotDist_corner_eq hq P, ?_, ?_⟩
  · intro B
    constructor
    · intro hB
      rw [(image_of_small_box hq P B ((hadm B).1 hB)).2.2]
      exact (ENNReal.ofReal_lt_ofReal_iff hh).2 ((hadm B).1 hB)
    · intro hB
      by_contra hna
      have h1 : P.halfEdge ≤ B.diam := not_lt.1 fun h => hna ((hadm B).2 h)
      exact absurd hB (not_lt.2 (halfEdge_le_setDiam_image hq P B h1))
  · obtain ⟨-, -, h3, -⟩ := hF P torus
    obtain ⟨Q, hQ, h1, -⟩ := h3 Set.univ Set.univ hcompact hopen subset_rfl
    rwa [Set.univ_subset_iff.1 h1] at hQ
  · show ContDiff ℝ 1 _
    exact (contDiff_const : ContDiff ℝ 1 fun _ : Fin 4 → ℝ => (1 : ℝ))
  · obtain ⟨⟨-, h0, -⟩, -⟩ := hq P torus
    refine Set.eq_univ_of_forall fun y r hr => ⟨y, one_ne_zero, ?_⟩
    rw [(h0 y y).2 rfl]
    exact hr
  · obtain ⟨n, hn⟩ := exists_quotDist_corner_eq hq P
    refine ⟨⟨n, hn⟩, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact quotDist_corner_le hq P k
  · intro G hG hB
    obtain ⟨Q, hQ, h1, -⟩ := hB Set.univ Set.univ hcompact hopen subset_rfl
    have h2 := hG Q hQ
    rw [Set.univ_subset_iff.1 h1] at h2
    rw [quotDist_corner_eq hq P] at hdiam
    have h3 : ENNReal.ofReal P.halfEdge ≤ ENNReal.ofReal (2 * P.halfEdge) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    exact absurd h2 (not_lt.2 (h3.trans hdiam))
  · intro Q h1 _
    exact Set.univ_subset_iff.1 h1
end PeriodicSpace.BoxDiameter
end YangMills.Construction
