import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.LawInAState.ConcentrationInOneBox
import YangMills.Construction.LawInAState.MarksOnTheBox
import YangMills.Construction.LawInAState.ProductsInOneBox
import YangMills.Construction.LawInAState.TheCouplingOfTheLevelGrows
import YangMills.Construction.LawInAState.TheLevelOfTheLaw
import YangMills.Construction.LawOnABoxOfTheFlow.LawOnABox
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
private theorem natCast_val_eq_sub_mul (P : ℕ) (w : ℕ) :
    ∃ q : ℤ, (((w : ZMod P).val : ℕ) : ℤ) = (w : ℤ) - P * q := by
  refine ⟨(w : ℤ) / P, ?_⟩
  rw [ZMod.val_natCast]
  have := Int.emod_add_mul_ediv (w : ℤ) P
  push_cast
  linarith
private theorem exists_coarse_coord {n L : ℕ} [NeZero n] (hL : 0 < L) (c : ZMod (n * L)) :
    ∃ b : ℤ, (((((c.cast : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ)) : ZMod n) = (b : ZMod n) ∧
      |(c.val : ℤ) - L * b| ≤ L := by
  have hc : (c.cast : ℤ) = (c.val : ℤ) := by
    have : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) hL.ne'⟩
    exact (ZMod.natCast_val c).symm
  refine ⟨((c.val : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ), by rw [hc], ?_⟩
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  have h1 := Int.emod_add_mul_ediv ((c.val : ℤ) + ((L : ℤ) - 1) / 2) L
  have h2 := Int.emod_nonneg ((c.val : ℤ) + ((L : ℤ) - 1) / 2) hLz.ne'
  have h3 := Int.emod_lt_of_pos ((c.val : ℤ) + ((L : ℤ) - 1) / 2) hLz
  have h4 : 0 ≤ ((L : ℤ) - 1) / 2 := Int.ediv_nonneg (by omega) (by norm_num)
  have h5 : ((L : ℤ) - 1) / 2 ≤ L := by omega
  rw [abs_le]
  constructor <;> nlinarith
private theorem fineBlock_exists_coord {L : ℕ} [NeZero L] (hL : 2 ≤ L) :
    ∀ (t n : ℕ) [NeZero n] (y : TorusFields.TorusSite n)
      (c : TorusFields.TorusSite (WeightedResponses.fineSide L t n)), c ∈ WeightedResponses.fineBlock L t n y →
      ∀ i, ∃ a : ℤ, (a : ZMod n) = y i ∧ |((c i).val : ℤ) - (L : ℤ) ^ t * a| ≤ 2 * (L : ℤ) ^ t := by
  intro t
  induction t with
  | zero =>
    intro n _ y c hc i
    have hcy : c = y := Finset.mem_singleton.1 hc
    have hv : ZMod.val (n := n) (c i) = (y i).val := congrArg ZMod.val (congrFun hcy i)
    refine ⟨((y i).val : ℤ), by rw [Int.cast_natCast, ZMod.natCast_zmod_val], ?_⟩
    change |((ZMod.val (n := n) (c i) : ℕ) : ℤ) - (L : ℤ) ^ 0 * _| ≤ _
    rw [hv]
    simp
  | succ t ih =>
    intro n _ Y c hc i
    have hc' : c ∈ (TorusLumps.sitesInBlocks L {Y} : Finset (TorusFields.TorusSite (n * L))).biUnion
        fun y => WeightedResponses.fineBlock L t (n * L) y := hc
    obtain ⟨y, hy, hcy⟩ := Finset.mem_biUnion.1 hc'
    obtain ⟨a, ha, hle⟩ := ih (n * L) y c hcy i
    have hb : TorusLumps.parentBlock L y = Y := Finset.mem_singleton.1 (Finset.mem_filter.1 hy).2
    obtain ⟨b, hb1, hb2⟩ := exists_coarse_coord (n := n) (L := L) (by omega) (y i)
    have hz : ((a - ((y i).val : ℤ) : ℤ) : ZMod (n * L)) = 0 := by
      rw [Int.cast_sub, ha]; simp
    obtain ⟨q, hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hz
    refine ⟨b + n * q, ?_, ?_⟩
    · have : Y i = (b : ZMod n) := by rw [← hb]; exact hb1
      rw [this]; simp
    · have hLz : (0 : ℤ) < L := by exact_mod_cast (by omega : 0 < L)
      have hLt : (0 : ℤ) < (L : ℤ) ^ t := pow_pos hLz t
      have hq' : a = ((y i).val : ℤ) + (n : ℤ) * L * q := by push_cast at hq; linarith
      have e1 : ((c i).val : ℤ) - (L : ℤ) ^ (t + 1) * (b + n * q) =
          (((c i).val : ℤ) - (L : ℤ) ^ t * a) + (L : ℤ) ^ t * (((y i).val : ℤ) - L * b) := by
        rw [hq', pow_succ]; ring
      rw [e1]
      have h2 : |(L : ℤ) ^ t * (((y i).val : ℤ) - L * b)| ≤ (L : ℤ) ^ t * L := by
        rw [abs_mul, abs_of_pos hLt]
        exact mul_le_mul_of_nonneg_left hb2 hLt.le
      have h3 : 2 * (L : ℤ) ^ t ≤ (L : ℤ) ^ t * L := by
        have : (2 : ℤ) ≤ L := by exact_mod_cast hL
        nlinarith
      calc _ ≤ |((c i).val : ℤ) - (L : ℤ) ^ t * a| + |(L : ℤ) ^ t * (((y i).val : ℤ) - L * b)| := abs_add_le _ _
        _ ≤ 2 * (L : ℤ) ^ t + (L : ℤ) ^ t * L := add_le_add hle h2
        _ ≤ 2 * (L : ℤ) ^ (t + 1) := by rw [pow_succ]; linarith
private theorem abs_apply_le_euclidNormVec (y : Fin 4 → ℝ) (i : Fin 4) : |y i| ≤ TorusMetric.euclidNormVec y := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem plaquetteVertex_val {P : ℕ} [NeZero P] (x c : TorusFields.TorusSite P) (μ ν : Fin 4)
    (hc : c ∈ TorusFields.plaquetteVertices x μ ν) (i : Fin 4) :
    ∃ (e : ℕ) (q : ℤ), e ≤ 2 ∧ ((c i).val : ℤ) = ((x i).val : ℤ) + e - P * q := by
  have key : ∀ e : ℕ, e ≤ 2 → c i = x i + (e : ZMod P) →
      ∃ (e : ℕ) (q : ℤ), e ≤ 2 ∧ ((c i).val : ℤ) = ((x i).val : ℤ) + e - P * q := by
    intro e he h
    obtain ⟨q, hq⟩ := natCast_val_eq_sub_mul P ((x i).val + e)
    refine ⟨e, q, he, ?_⟩
    have h' : c i = (((x i).val + e : ℕ) : ZMod P) := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val]; exact h
    rw [h', hq]; push_cast; ring
  have hev : ∀ a : Fin 4, (TorusFields.unitStep P a) i = if i = a then 1 else 0 := fun a => by
    simp [TorusFields.unitStep, Pi.single_apply]
  simp only [TorusFields.plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact key 0 (by norm_num) (by simp)
  · by_cases h : i = μ
    · exact key 1 (by norm_num) (by rw [Pi.add_apply, hev, if_pos h]; simp)
    · exact key 0 (by norm_num) (by rw [Pi.add_apply, hev, if_neg h]; simp)
  · by_cases h : i = ν
    · exact key 1 (by norm_num) (by rw [Pi.add_apply, hev, if_pos h]; simp)
    · exact key 0 (by norm_num) (by rw [Pi.add_apply, hev, if_neg h]; simp)
  · by_cases h : i = μ <;> by_cases h' : i = ν
    · exact key 2 (by norm_num) (by
        rw [Pi.add_apply, Pi.add_apply, hev, hev, if_pos h, if_pos h']; push_cast; ring)
    · exact key 1 (by norm_num) (by
        rw [Pi.add_apply, Pi.add_apply, hev, hev, if_pos h, if_neg h']; push_cast; ring)
    · exact key 1 (by norm_num) (by
        rw [Pi.add_apply, Pi.add_apply, hev, hev, if_neg h, if_pos h']; push_cast; ring)
    · exact key 0 (by norm_num) (by
        rw [Pi.add_apply, Pi.add_apply, hev, hev, if_neg h, if_neg h']; push_cast; ring)
private theorem fineSide_boxSide (L K k : ℕ) (hk : k ≤ K) :
    WeightedResponses.fineSide L k (BoxResponses.boxSide L K k) = 2 * L ^ K := by
  rw [WeightedResponses.fineSide_eq, BoxResponses.boxSide, mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
private def floorSite (L K k : ℕ) (c : InfiniteLattice.AmbientSpace) : TorusFields.TorusSite (BoxResponses.boxSide L K k) :=
  TorusFields.siteOfInt fun i => ⌊c i * ((L : ℝ) ^ (K - k))⌋
private theorem exists_offset_of_mem_weightSites {L K k : ℕ} [NeZero L] (hL : 2 ≤ L) (hk : k ≤ K)
    (g : InfiniteLattice.AmbientSpace → ℝ) (ctr : InfiniteLattice.AmbientSpace) (ρ : ℝ) (m : ℕ)
    (hg : ∀ z, g z ≠ 0 → ∀ i, |z i - ctr i| ≤ ρ) (v : Fin 4 → ℤ) (hv : v ∈ shiftSet m)
    (y : TorusFields.TorusSite (BoxResponses.boxSide L K k))
    (hy : y ∈ BoxMarks.weightSitesOf L K k (translateBy L K k v g)) :
    ∃ T : Fin 4 → ℤ, y = floorSite L K k ctr + TorusFields.siteOfInt T ∧
      ∀ i, |(T i : ℝ)| ≤ ρ * (L : ℝ) ^ (K - k) + m + 6 := by
  classical
  have hLpos : 0 < L := by omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
  simp only [BoxMarks.weightSitesOf, ResponseInTheExpansion.weightSupportSites, Finset.mem_filter, Finset.mem_univ,
    true_and] at hy
  obtain ⟨p, ⟨-, c, hc, hcb⟩, hw⟩ := hy
  obtain ⟨z, hz⟩ : ∃ z : Fin 4 → ℤ, translateBy L K k v g
      ((fun i => (((WeightedResponses.doubledBarycentre p i).val : ℝ) / (2 * (L : ℝ) ^ K))) +
        fun i => 2 * (z i : ℝ)) ≠ 0 := by
    by_contra hall
    apply hw
    simp only [BoxResponses.unitTorusWeight, BoxResponses.periodizeUnitTorus]
    refine finsum_eq_zero_of_forall_eq_zero fun z => ?_
    exact not_not.1 fun hne => hall ⟨z, hne⟩
  have hbox := hg _ hz
  have hT : ∀ i, ∃ t : ℤ, y i = ((⌊ctr i * ((L : ℝ) ^ (K - k))⌋ + t : ℤ) : ZMod (BoxResponses.boxSide L K k)) ∧
      |(t : ℝ)| ≤ ρ * (L : ℝ) ^ (K - k) + m + 6 := by
    intro i
    obtain ⟨a, ha, hle⟩ := fineBlock_exists_coord hL k (BoxResponses.boxSide L K k) y c hcb i
    obtain ⟨e, q₂, he, hq₂⟩ := plaquetteVertex_val p.1 c p.2.1 p.2.2 hc i
    obtain ⟨q₁, hq₁⟩ := natCast_val_eq_sub_mul (2 * WeightedResponses.fineSide L k (BoxResponses.boxSide L K k))
      (2 * (p.1 i).val + (if i = p.2.1 then 1 else 0) + (if i = p.2.2 then 1 else 0))
    have hbi : |(((WeightedResponses.doubledBarycentre p i).val : ℝ) / (2 * (L : ℝ) ^ K) + 2 * (z i : ℝ)) -
        (v i : ℝ) * ((L : ℝ) ^ k / (L : ℝ) ^ K) - ctr i| ≤ ρ := hbox i
    have hvi : |(v i : ℝ)| ≤ m := by
      have : v i ∈ Finset.Icc (-(m : ℤ)) m := (Fintype.mem_piFinset.1 hv) i
      rw [Finset.mem_Icc] at this
      rw [abs_le]
      constructor
      · exact_mod_cast this.1
      · exact_mod_cast this.2
    have hle' : |(((c i).val : ℕ) : ℝ) - (L : ℝ) ^ k * (a : ℝ)| ≤ 2 * (L : ℝ) ^ k := by
      exact_mod_cast hle
    have hfl₁ := Int.floor_le (ctr i * (L : ℝ) ^ (K - k))
    have hfl₂ := Int.lt_floor_add_one (ctr i * (L : ℝ) ^ (K - k))
    set S : ℝ := (L : ℝ) ^ (K - k) with hS
    set D : ℝ := (L : ℝ) ^ k with hD
    have hSpos : 0 < S := pow_pos hLr _
    have hDpos : 0 < D := pow_pos hLr _
    have hD1 : 1 ≤ D := one_le_pow₀ (by exact_mod_cast hLpos)
    have hA : (L : ℝ) ^ K = S * D := by
      rw [hS, hD, ← pow_add, Nat.sub_add_cancel hk]
    have hP : (WeightedResponses.fineSide L k (BoxResponses.boxSide L K k) : ℝ) = 2 * (S * D) := by
      rw [fineSide_boxSide L K k hk, ← hA]; push_cast; ring
    obtain ⟨E, hE0, hE2, hW⟩ : ∃ E : ℝ, 0 ≤ E ∧ E ≤ 2 ∧
        (((WeightedResponses.doubledBarycentre p i).val : ℕ) : ℝ) =
          2 * ((p.1 i).val : ℝ) + E - 2 * (2 * (S * D)) * q₁ := by
      refine ⟨(if i = p.2.1 then 1 else 0) + (if i = p.2.2 then 1 else 0), ?_, ?_, ?_⟩
      · split_ifs <;> norm_num
      · split_ifs <;> norm_num
      · have h1 : (((WeightedResponses.doubledBarycentre p i).val : ℕ) : ℤ) = _ := hq₁
        have h2 := congrArg (Int.cast : ℤ → ℝ) h1
        push_cast at h2
        rw [h2, hP]
        ring
    have hvc : (((c i).val : ℕ) : ℝ) = ((p.1 i).val : ℝ) + e - 2 * (S * D) * q₂ := by
      have h1 := congrArg (Int.cast : ℤ → ℝ) hq₂
      push_cast at h1
      rw [h1, hP]
    have he2 : (e : ℝ) ≤ 2 := by exact_mod_cast he
    have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
    set U : ℝ := (((WeightedResponses.doubledBarycentre p i).val : ℝ) / (2 * (L : ℝ) ^ K) + 2 * (z i : ℝ)) -
        (v i : ℝ) * (D / (L : ℝ) ^ K) - ctr i with hU
    refine ⟨(a - ⌊ctr i * S⌋) + 2 * (L : ℤ) ^ (K - k) * (q₂ + z i - q₁), ?_, ?_⟩
    · have hN : ((2 * (L : ℤ) ^ (K - k) : ℤ) : ZMod (BoxResponses.boxSide L K k)) = 0 := by
        have : ((BoxResponses.boxSide L K k : ℕ) : ZMod (BoxResponses.boxSide L K k)) = 0 := ZMod.natCast_self _
        rw [BoxResponses.boxSide] at this ⊢
        exact_mod_cast this
      rw [← ha]
      push_cast at hN ⊢
      linear_combination (-(((q₂ : ℤ) : ZMod (BoxResponses.boxSide L K k)) +
        ((z i : ℤ) : ZMod (BoxResponses.boxSide L K k)) - ((q₁ : ℤ) : ZMod (BoxResponses.boxSide L K k)))) * hN
    · have hid : ((((a - ⌊ctr i * S⌋) + 2 * (L : ℤ) ^ (K - k) * (q₂ + z i - q₁) : ℤ)) : ℝ) =
          S * U + (v i : ℝ) + (ctr i * S - (⌊ctr i * S⌋ : ℝ)) -
            ((((c i).val : ℕ) : ℝ) - D * a) / D + (e : ℝ) / D - E / (2 * D) := by
        push_cast
        rw [hU, hW, hA, hvc]
        rw [← hS]
        field_simp
        ring
      rw [hid]
      have b1 : |S * U| ≤ ρ * S := by
        rw [abs_mul, abs_of_pos hSpos, mul_comm]
        exact mul_le_mul_of_nonneg_right hbi hSpos.le
      have b2 : |((((c i).val : ℕ) : ℝ) - D * a) / D| ≤ 2 := by
        rw [abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
        exact hle'
      have b3 : (e : ℝ) / D ≤ 2 := by
        rw [div_le_iff₀ hDpos]; nlinarith
      have b3' : 0 ≤ (e : ℝ) / D := by positivity
      have b4 : E / (2 * D) ≤ 1 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      have b4' : 0 ≤ E / (2 * D) := by positivity
      have c1 := abs_le.1 b1
      have c2 := abs_le.1 b2
      have c3 := abs_le.1 hvi
      rw [abs_le]
      constructor <;> linarith
  choose T hT1 hT2 using hT
  refine ⟨T, ?_, hT2⟩
  funext i
  rw [hT1 i]
  simp [floorSite, TorusFields.siteOfInt]
private theorem weightSites_subset_supBall {L K k m : ℕ} [NeZero L] (hL : 2 ≤ L) (hk : k ≤ K)
    (g : InfiniteLattice.AmbientSpace → ℝ) (ctr : InfiniteLattice.AmbientSpace) (ρ rad : ℝ)
    (hg : ∀ z, g z ≠ 0 → ∀ i, |z i - ctr i| ≤ ρ)
    (hb : ρ * (L : ℝ) ^ (K - k) + m + 6 ≤ rad) :
    ∀ v ∈ shiftSet m, BoxMarks.weightSitesOf L K k (translateBy L K k v g) ⊆
      ResponseInTheExpansion.supBall (floorSite L K k ctr) rad := by
  intro v hv y hy
  obtain ⟨T, rfl, hT⟩ := exists_offset_of_mem_weightSites hL hk g ctr ρ m hg v hv y hy
  have hB : 0 ≤ ρ * (L : ℝ) ^ (K - k) + m + 6 := (abs_nonneg _).trans (hT 0)
  have h1 := TorusFields.supDist_add_siteOfInt_le (floorSite L K k ctr) T ⌊ρ * (L : ℝ) ^ (K - k) + m + 6⌋₊ fun i => by
    apply Nat.le_floor
    rw [Nat.cast_natAbs]
    simpa using hT i
  have h2 : (TorusFields.supDist (floorSite L K k ctr + TorusFields.siteOfInt T) (floorSite L K k ctr) : ℝ) ≤
      ρ * (L : ℝ) ^ (K - k) + m + 6 := by
    rw [TorusFields.supDist_comm]
    exact (Nat.cast_le.2 h1).trans (Nat.floor_le hB)
  simp only [ResponseInTheExpansion.supBall, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h2.trans hb
private theorem exists_common_centre {d vt : ℝ} (hd : 0 < d) {f h : InfiniteLattice.AmbientSpace → ℝ}
    (hp : IsNormalizedTestPair d vt f h) :
    ∃ ctr : InfiniteLattice.AmbientSpace, (∀ z, f z ≠ 0 → ∀ i, |z i - ctr i| ≤ 10 * d) ∧
      (∀ z, h z ≠ 0 → ∀ i, |z i - ctr i| ≤ 10 * d) := by
  obtain ⟨x₁, x₂, hf, hh, -, hle⟩ := hp.mem_class
  have hfs := hf.2.2.2.1
  have hhs := hh.2.2.2.1
  have hlt : TestFunctions.setDistR4 (tsupport f) (tsupport h) < ENNReal.ofReal (7 * d) :=
    lt_of_le_of_lt hle ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))
  simp only [TestFunctions.setDistR4, iInf_lt_iff] at hlt
  obtain ⟨a, ha, b, hb, hab⟩ := hlt
  have hab' : TorusMetric.euclidNormVec (a - b) < 7 * d :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hab
  have hball : ∀ (g : InfiniteLattice.AmbientSpace → ℝ) (x : InfiniteLattice.AmbientSpace),
      tsupport g ⊆ TestFunctions.closedBallR4 x d → ∀ z ∈ tsupport g, ∀ i,
      |z i - x i| ≤ d := fun g x hs z hz i => (abs_apply_le_euclidNormVec (z - x) i).trans (hs hz)
  refine ⟨x₁, fun z hz i => ?_, fun z hz i => ?_⟩
  · have := hball _ _ hfs z (subset_tsupport f (Function.mem_support.2 hz)) i
    linarith
  · have h1 := abs_le.1 (hball _ _ hhs z (subset_tsupport h (Function.mem_support.2 hz)) i)
    have h2 := abs_le.1 (hball _ _ hhs b hb i)
    have h3 := abs_le.1 (hball _ _ hfs a ha i)
    have h4 := abs_le.1 ((abs_apply_le_euclidNormVec (a - b) i).trans hab'.le)
    simp only [Pi.sub_apply] at h4
    rw [abs_le]
    constructor <;> linarith
private theorem separation_numerics (L : ℕ) (Xi B₁ : ℝ) (hB₁ : 0 < B₁) : ∃ X₀ : ℝ, ∀ x, X₀ ≤ x → 2 ≤ L → 3 ≤ x ∧
    (∀ e : ℕ, x ≤ Xi + e * (2 * B₁) → 1 ≤ e ∧ x ^ (1 / 10 : ℝ) ≤ 2 * (L : ℝ) ^ e ∧
      (boxRadius x : ℝ) ^ (2 / 3 : ℝ) ≤ (L : ℝ) ^ (e - 1) ∧ 16 * (boxRadius x : ℝ) < 2 * (L : ℝ) ^ e) ∧
    10 * (2 ^ 13 * (L : ℝ) * (TorusLumps.clusterRange x : ℝ)) + (averagingRadius x : ℝ) + 6 ≤
      3 * (boxRadius x : ℝ) / 32 := by
  have e1 := tendsto_rpow_atTop (show (0 : ℝ) < 9 / 10 by norm_num)
  have e2 := tendsto_rpow_atTop (show (0 : ℝ) < 1 / 27 - 1 / 100 by norm_num)
  obtain ⟨X₁, h1⟩ := Filter.eventually_atTop.1 (e1.eventually_ge_atTop (128 * B₁))
  obtain ⟨X₂, h2⟩ := Filter.eventually_atTop.1 (e2.eventually_ge_atTop (32 * (20 * 2 ^ 13 * (L : ℝ) + 6)))
  refine ⟨max (max X₁ X₂) (max 3 (2 * |Xi| + 2)), fun x hx hL => ?_⟩
  have hx1 : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : X₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx4 : 2 * |Xi| + 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  set Pp : ℝ := x ^ (1 / 10 : ℝ) with hPp
  have hPp1 : 1 ≤ Pp := Real.one_le_rpow hxone (by norm_num)
  have hsplit : x = Pp * x ^ (9 / 10 : ℝ) := by
    rw [hPp, ← Real.rpow_add hxpos]; norm_num
  have hbig : 128 * B₁ * Pp ≤ x := by
    calc 128 * B₁ * Pp = Pp * (128 * B₁) := by ring
      _ ≤ Pp * x ^ (9 / 10 : ℝ) := mul_le_mul_of_nonneg_left (h1 x hx1) (by linarith)
      _ = x := hsplit.symm
  set Y : ℝ := x ^ (1 / 27 : ℝ) with hY
  have hY1 : 1 ≤ Y := Real.one_le_rpow hxone (by norm_num)
  have hYP : Y ≤ Pp := Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)
  have hR1 : Y ≤ (boxRadius x : ℝ) := Nat.le_ceil _
  have hR2 : (boxRadius x : ℝ) ≤ Y + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  refine ⟨hx3, fun e he => ?_, ?_⟩
  · have hXi : Xi ≤ x / 2 := by
      have := le_abs_self Xi
      linarith
    have h4 : 32 * Pp ≤ (e : ℝ) := by
      have : B₁ * (32 * Pp) ≤ B₁ * e := by nlinarith
      exact le_of_mul_le_mul_left this hB₁
    have he1 : 1 ≤ e := by
      have : (1 : ℝ) ≤ e := by linarith
      exact_mod_cast this
    have hpow : (e : ℝ) ≤ (L : ℝ) ^ (e - 1) := by
      have : e - 1 < L ^ (e - 1) := Nat.lt_pow_self (by omega)
      have h' : e ≤ L ^ (e - 1) := by omega
      exact_mod_cast h'
    have hLpow : (e : ℝ) < (L : ℝ) ^ e := by
      have : e < L ^ e := Nat.lt_pow_self (by omega)
      exact_mod_cast this
    refine ⟨he1, ?_, ?_, ?_⟩
    · nlinarith
    · have hRone : (1 : ℝ) ≤ (boxRadius x : ℝ) := by linarith
      have : (boxRadius x : ℝ) ^ (2 / 3 : ℝ) ≤ (boxRadius x : ℝ) := by
        calc (boxRadius x : ℝ) ^ (2 / 3 : ℝ) ≤ (boxRadius x : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hRone (by norm_num)
          _ = _ := Real.rpow_one _
      linarith
    · nlinarith
  · set t : ℝ := x ^ (1 / 100 : ℝ) with ht
    have ht1 : 1 ≤ t := Real.one_le_rpow hxone (by norm_num)
    have hYt : Y = t * x ^ (1 / 27 - 1 / 100 : ℝ) := by
      rw [ht, hY, ← Real.rpow_add hxpos]; norm_num
    have hA : 32 * (20 * 2 ^ 13 * (L : ℝ) + 6) * t ≤ Y := by
      rw [hYt, mul_comm]
      exact mul_le_mul_of_nonneg_left (h2 x hx2) (by linarith)
    have hr : (TorusLumps.clusterRange x : ℝ) ≤ t + 1 := (Nat.ceil_lt_add_one (by linarith)).le
    have hm : (averagingRadius x : ℝ) ≤ (boxRadius x : ℝ) / 16 := by
      have := @Nat.cast_div_le ℝ _ _ _ (boxRadius x) 16
      simpa [averagingRadius] using this
    have hr2 : 10 * (2 ^ 13 * (L : ℝ) * (TorusLumps.clusterRange x : ℝ)) ≤ 20 * 2 ^ 13 * (L : ℝ) * t := by
      have : (TorusLumps.clusterRange x : ℝ) ≤ 2 * t := by linarith
      have h3 : 2 ^ 13 * (L : ℝ) * (TorusLumps.clusterRange x : ℝ) ≤ 2 ^ 13 * (L : ℝ) * (2 * t) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      linarith
    nlinarith
private theorem flow_expansion_and_increment {ℓ : TorusLumps.StepParameters} (hR : StepReturn.ExpansionReturnsAt ℓ)
    {β : ℝ} (h0 : TorusLumps.HasExpansion ℓ 0 β (TorusLumps.wilsonWeight β)) (K : ℕ)
    (hfl : ∀ j ≤ K, ℓ.y₁ ≤ ResponseInTheExpansion.flowCouplings ℓ β j) :
    ∀ j, j < K → TorusLumps.HasExpansion ℓ j (TorusLumps.couplingFlow ℓ β j).1 (TorusLumps.couplingFlow ℓ β j).2 ∧
      |ResponseInTheExpansion.flowCouplings ℓ β (j + 1) - ResponseInTheExpansion.flowCouplings ℓ β j| ≤ 2 * ℓ.B := by
  have step : ∀ j, j < K →
      TorusLumps.HasExpansion ℓ j (TorusLumps.couplingFlow ℓ β j).1 (TorusLumps.couplingFlow ℓ β j).2 →
      TorusLumps.HasExpansion ℓ (j + 1) (TorusLumps.couplingFlow ℓ β (j + 1)).1
          (TorusLumps.couplingFlow ℓ β (j + 1)).2 ∧
        |ResponseInTheExpansion.flowCouplings ℓ β (j + 1) - ResponseInTheExpansion.flowCouplings ℓ β j| ≤ 2 * ℓ.B := by
    intro j hj hrow
    obtain ⟨x', ⟨h1, h2⟩, h3⟩ := hR j _ _ (hfl j hj.le) hrow
    have hex : ∃ x' : ℝ, TorusLumps.HasExpansion ℓ (j + 1) x'
        (TorusLumps.kernelImage ℓ (TorusLumps.couplingFlow ℓ β j).1 (TorusLumps.couplingFlow ℓ β j).2) := ⟨x', h1⟩
    have hn : TorusLumps.expansionCoupling ℓ j (TorusLumps.couplingFlow ℓ β j).1
        (TorusLumps.couplingFlow ℓ β j).2 = x' := by
      unfold TorusLumps.expansionCoupling
      rw [dif_pos hex]
      obtain ⟨_, f, hf, _⟩ := hex.choose_spec
      exact h3 _ f hf
    have hc : (TorusLumps.couplingFlow ℓ β (j + 1)).1 = x' := hn
    have hc' : (TorusLumps.couplingFlow ℓ β (j + 1)).2 =
        TorusLumps.kernelImage ℓ (TorusLumps.couplingFlow ℓ β j).1 (TorusLumps.couplingFlow ℓ β j).2 := rfl
    refine ⟨by rw [hc, hc']; exact h1, ?_⟩
    change |(TorusLumps.couplingFlow ℓ β (j + 1)).1 - (TorusLumps.couplingFlow ℓ β j).1| ≤ _
    rw [hc]
    exact h2
  have standingConstraints : ∀ j, j ≤ K →
      TorusLumps.HasExpansion ℓ j (TorusLumps.couplingFlow ℓ β j).1 (TorusLumps.couplingFlow ℓ β j).2 := by
    intro j
    induction j with
    | zero => exact fun _ => h0
    | succ j ih => exact fun hj => (step j (by omega) (ih (by omega))).1
  exact fun j hj => ⟨standingConstraints j hj.le, (step j hj (standingConstraints j hj.le)).2⟩
private theorem flowCouplings_le_add {ℓ : TorusLumps.StepParameters} {β : ℝ} {K k : ℕ} (hk : k ≤ K)
    (hmove : ∀ j, j < K →
      |ResponseInTheExpansion.flowCouplings ℓ β (j + 1) - ResponseInTheExpansion.flowCouplings ℓ β j| ≤ 2 * ℓ.B) :
    ResponseInTheExpansion.flowCouplings ℓ β k ≤
      ResponseInTheExpansion.flowCouplings ℓ β K + ((K - k : ℕ) : ℝ) * (2 * ℓ.B) := by
  have : ∀ e : ℕ, k + e ≤ K → ResponseInTheExpansion.flowCouplings ℓ β k ≤
      ResponseInTheExpansion.flowCouplings ℓ β (k + e) + (e : ℝ) * (2 * ℓ.B) := by
    intro e
    induction e with
    | zero => simp
    | succ e ih =>
      intro he
      have h1 := ih (by omega)
      have h2 := abs_le.1 (hmove (k + e) (by omega))
      have : k + (e + 1) = k + e + 1 := rfl
      rw [this]
      push_cast
      linarith [h2.1]
  have h := this (K - k) (by omega)
  rwa [Nat.add_sub_cancel' hk] at h
section MonotoneChart
variable {ℓ : TorusLumps.StepParameters} {T : WeightedResponses.StageTower ℓ} {n : ℕ} [NeZero n] {k : ℕ}
  {o : TorusFields.TorusSite n} {R : ℕ} {c : BoxGaussian.BoxChart T k o R}
private theorem isInGauge_mono {C C' δ c₀ : ℝ} (hC : C ≤ C') (hδ : 0 ≤ δ) (h : c.IsInGauge C δ c₀) :
    c.IsInGauge C' δ c₀ := by
  refine ⟨h.mem_chart, h.coord_unique, fun p hp => ?_⟩
  obtain ⟨γ, v, b, hγ, h1, h2, h3, h4⟩ := h.bounds p hp
  have hRn : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hle : C * (R : ℝ) ^ 3 * δ ≤ C' * (R : ℝ) ^ 3 * δ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) hδ
  refine ⟨γ, v, b, hγ, fun bd hb => ⟨(h1 bd hb).1, (h1 bd hb).2.1, (h1 bd hb).2.2.1, ?_, ?_, ?_⟩, ?_,
    fun q hq => ?_, ?_⟩
  · exact (h1 bd hb).2.2.2.1.trans hle
  · exact (h1 bd hb).2.2.2.2.1.trans hle
  · exact (h1 bd hb).2.2.2.2.2.trans hle
  · exact h2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) (sq_nonneg _))
  · exact (h3 q hq).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) hδ)
  · exact h4.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) (sq_nonneg _))
private theorem hasLaw_mono {P : Measure (WeightedResponses.MarkedSample ℓ k n)} {x c₀ ε ε' : ℝ} (hε : ε ≤ ε')
    (h : c.HasLaw P x c₀ ε) : c.HasLaw P x c₀ ε' :=
  ⟨h.integral_eq, fun q hq ζ hζ => ⟨(h.weight_bounds q hq ζ hζ).1, (h.weight_bounds q hq ζ hζ).2.trans hε⟩,
    h.ellipsoid_mass⟩
private theorem hasCurl_mono {x C C' δ φ φ' : ℝ} {Cj : ℕ → ℝ} (hC : C ≤ C') (hδ : 0 ≤ δ) (hφ : φ ≤ φ')
    (h : c.HasCurl x C δ φ Cj) : c.HasCurl x C' δ φ' Cj :=
  ⟨h.map_eq_gaussian, fun q hq p hp => (h.meanCurl_le q hq p hp).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) hδ),
    h.iteratedDiff_le, fun q hq p hp => (h.meanCurl_le_inner q hq p hp).trans hφ⟩
end MonotoneChart
section MonotoneKernels
variable {ℓ : TorusLumps.StepParameters}
private theorem isWeightKernel_mono {L k : ℕ} [NeZero L] {N : ℕ} [NeZero N] {al C C' c e e' : ℝ}
    {h : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide L k N)}
    {κ : TorusFields.TorusSite N → TorusFields.TorusPlaquette N → TorusFields.TorusPlaquette N → ℝ}
    (hC : C ≤ C') (he : e ≤ e') (H : BoxMarks.IsWeightKernel L k al C c e h κ) :
    BoxMarks.IsWeightKernel L k al C' c e' h κ :=
  ⟨H.symm, fun y p p' => (H.decay y p p').trans (mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le), H.vanish_far,
    fun y μ ν ρ τ h1 h2 => (H.plane_sums y μ ν ρ τ h1 h2).trans he⟩
private theorem isBoxKernelFamily_mono {T : WeightedResponses.StageTower ℓ} {β : ℝ} {al : ℕ → ℝ} {K k m : ℕ}
    {o : TorusFields.TorusSite (BoxResponses.boxSide ℓ.side K k)} {R : ℕ}
    {c : BoxGaussian.BoxChart T k o R} {C C' cc e₁ e₁' e₂ e₂' : ℝ}
    {w : (Fin 4 → ℤ) → InfiniteLattice.AmbientSpace → ℝ}
    {κ : (Fin 4 → ℤ) → TorusFields.TorusSite (BoxResponses.boxSide ℓ.side K k) →
      TorusFields.TorusPlaquette (BoxResponses.boxSide ℓ.side K k) →
      TorusFields.TorusPlaquette (BoxResponses.boxSide ℓ.side K k) → ℝ}
    {κ₀ : (Fin 4 → ℤ) → ℝ} (hC : C ≤ C') (h₁ : e₁ ≤ e₁') (h₂ : e₂ ≤ e₂')
    (H : BoxMarks.IsBoxKernelFamily T β al K k m c C cc e₁ e₂ w κ κ₀) :
    BoxMarks.IsBoxKernelFamily T β al K k m c C' cc e₁' e₂' w κ κ₀ := by
  refine ⟨fun v hv => isWeightKernel_mono hC h₁ (H.isWeightKernel v hv), ?_⟩
  filter_upwards [H.response_approx] with u hu hE v hv
  exact (hu hE v hv).trans h₂
end MonotoneKernels
private theorem holdsOnParameters_of_holdsAtAdmissible {P : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop}
    (hP : WeightedResponses.HoldsAtAdmissibleParameters P) : ResponseInTheExpansion.HoldsOnParameterFamilies P := by
  intro a ha
  obtain ⟨L₀, r₀, hr, h⟩ := hP a ha
  exact ⟨L₀, r₀, 0, hr, fun L hLo hL T hTa hTL hD _ _ hrt _ => h L hLo hL T hTa hTL hD hrt⟩
abbrev _root_.YangMills.SharedProofs.p23606 := @holdsOnParameters_of_holdsAtAdmissible
theorem boxConcentrationStatement_holds (hLaw : BoxGaussian.boxGaussianLawStatement)
    (hMarks : boxResponsesQuadraticStatement) (hProducts : boxProductsStatement)
    (hLevel : separationLevelStatement) (hGrow : couplingAtSeparation_tendsto_statement) :
    boxConcentrationStatement := by
  refine HoldsForShapes.mono (HoldsForShapes.and (HoldsForShapes.of_holdsOnParameters (holdsOnParameters_of_holdsAtAdmissible hLaw))
    (HoldsForShapes.and hMarks (HoldsForShapes.and hProducts (HoldsForShapes.and (HoldsForShapes.of_holdsOnParameters hLevel)
      (HoldsForShapes.and (HoldsForShapes.of_holdsOnParameters hGrow) HoldsForShapes.params))))) ?_
  rintro Tb y Kr Xi vt ⟨hL, hM, hP, hLv, hG, -, -, hRS, -, hXi, hvt, -⟩
  have hR := hRS.returns_at
  have hW := hRS.wilson_expansion
  obtain ⟨C, C₀, xs, Cj, xp, hchart⟩ := hL (1 / 27) le_rfl (by norm_num)
  set ℓ := Tb.stepParameters y with hℓ
  obtain ⟨Cm, cc, dm, hcc, hdm, hmarks⟩ := hM (max C (2 * Tb.coercivity)⁻¹) Cj xp
  obtain ⟨Cp, dp, hdp, hprod⟩ := hP (max (max (max C (2 * Tb.coercivity)⁻¹) Cm) 1) cc Cj xp hcc
  set C₁ := max C (2 * Tb.coercivity)⁻¹ with hC₁
  set C₂ := max (max C₁ Cm) 1 with hC₂
  have hCC₁ : C ≤ C₁ := le_max_left _ _
  have hC₁₂ : C₁ ≤ C₂ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCm₂ : Cm ≤ C₂ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC₂1 : 1 ≤ C₂ := le_max_right _ _
  obtain ⟨X₀, hX⟩ := separation_numerics ℓ.side Xi (max ℓ.B 1) (by positivity)
  obtain ⟨d₁, hd₁, hgrow⟩ := hG Xi hXi (max X₀ xs)
  refine ⟨Cp, min (min dm dp) (min d₁ (1 / 2)), by positivity, ?_⟩
  intro d hd hdle K β al T hchain k m x hk hx hm f h hpair
  have hdm' : d ≤ dm := hdle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hdp' : d ≤ dp := hdle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hd₁' : d ≤ d₁ := hdle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd1 : d < 1 := lt_of_le_of_lt (hdle.trans ((min_le_right _ _).trans (min_le_right _ _))) (by norm_num)
  have hdat := hchain.isFlowDatum
  obtain ⟨-, hkK, hn⟩ := hLv Xi hXi d hd hd1 K β hdat hchain.minimalCutoff_le
  have hxbig := hgrow d hd hd₁' K β hdat hchain.minimalCutoff_le
  rw [← hk] at hkK
  rw [← hk, ← hx] at hn
  rw [← hx] at hxbig
  have hxX : X₀ ≤ x := (le_max_left _ _).trans hxbig
  have hxs : xs ≤ x := (le_max_right _ _).trans hxbig
  have hLL : 2 ≤ ℓ.side := T.two_le_side
  obtain ⟨hx3, hnum, hroom⟩ := hX x hxX hLL
  have hxk : x = ResponseInTheExpansion.flowCouplings ℓ β k := by rw [hx, hk]; rfl
  have h0 : TorusLumps.HasExpansion ℓ 0 β (TorusLumps.wilsonWeight β) := hW β (hdat.le_coupling 0 (by omega))
  have hmove := fun j hj => (flow_expansion_and_increment hR h0 K hdat.le_coupling j hj).2
  have hle := flowCouplings_le_add hkK.le hmove
  have hB : ((K - k : ℕ) : ℝ) * (2 * ℓ.B) ≤ ((K - k : ℕ) : ℝ) * (2 * max ℓ.B 1) :=
    mul_le_mul_of_nonneg_left (by linarith [le_max_left ℓ.B 1]) (Nat.cast_nonneg _)
  obtain ⟨he1, hwide, hsteps, hside⟩ := hnum (K - k) (by rw [hxk]; linarith [hdat.coupling_le_top])
  set R := boxRadius x with hRdef
  have hRr : R = BoxGaussian.boxRadius (1 / 27) x := rfl
  have hstep : BoxGaussian.coarseningSteps (Tb.stepParameters y).side R ≤ K - k - 1 := Nat.sInf_le hsteps
  have hside' : 16 * R < BoxResponses.boxSide ℓ.side K k := by
    have : ((16 * R : ℕ) : ℝ) < ((BoxResponses.boxSide ℓ.side K k : ℕ) : ℝ) := by
      simpa [BoxResponses.boxSide] using hside
    exact_mod_cast this
  have hxc : x = BoxEvents.flowCoupling ℓ β k := hxk
  have hdatum : BoxEvents.IsBoxDatum Tb y T β (1 / 27) xs k (BoxResponses.boxSide ℓ.side K k) := by
    refine ⟨by rw [← hxc]; exact hxs, ?_, hchain.marksMeasurable, ⟨K - k, rfl⟩, ?_⟩
    · have hs := hchain.onFamily
      rw [← hxc, ← hRr]
      exact ⟨hs.startsAtWilson, fun j hj => hs.coupling_eq j (by omega), fun j hj => hs.onFamily j (by omega)⟩
    · rw [← hxc]
      simpa [BoxResponses.boxSide] using hwide
  obtain ⟨ctr, hcf, hch⟩ := exists_common_centre hd hpair
  have hroom' : 10 * d * (ℓ.side : ℝ) ^ (K - k) + m + 6 ≤ 3 * (R : ℝ) / 32 := by
    have : 10 * d * (ℓ.side : ℝ) ^ (K - k) = 10 * lengthInSites ℓ.side K k d := by
      simp only [lengthInSites]; ring
    rw [this, hm]
    linarith
  have hwf : IsWellLocalizedNear ℓ.side K k m R (floorSite ℓ.side K k ctr) f :=
    weightSites_subset_supBall hLL hkK.le f ctr (10 * d) _ hcf hroom'
  have hwh : IsWellLocalizedNear ℓ.side K k m R (floorSite ℓ.side K k ctr) h :=
    weightSites_subset_supBall hLL hkK.le h ctr (10 * d) _ hch hroom'
  have hroom'' : 10 * d * (ℓ.side : ℝ) ^ (K - k) + m + 6 ≤ (R : ℝ) / 8 :=
    hroom'.trans (by linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)])
  have hnf : BoxMarks.IsLocalizedNear ℓ.side K k m R (floorSite ℓ.side K k ctr) f :=
    weightSites_subset_supBall hLL hkK.le f ctr (10 * d) _ hcf hroom''
  have hnh : BoxMarks.IsLocalizedNear ℓ.side K k m R (floorSite ℓ.side K k ctr) h :=
    weightSites_subset_supBall hLL hkK.le h ctr (10 * d) _ hch hroom''
  set o := floorSite ℓ.side K k ctr with ho
  obtain ⟨c, cB, cLikely, cOff, cGauge, cLaw, cCurl, cKer⟩ :=
    hchart T β k (BoxResponses.boxSide ℓ.side K k) o x R hdatum hxc hRr
  set δ := BoxGaussian.boxScale x with hδdef
  have hxpos : 0 < x := by linarith
  have hlog : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hx3
  have hδ : 0 ≤ δ := by
    rw [hδdef, BoxGaussian.boxScale]
    have := Real.rpow_nonneg hxpos.le (-(1 / 2 : ℝ))
    positivity
  have hcKer : ∀ w : TorusFields.TorusPlaquette (BoxResponses.boxSide ℓ.side K k) → Fin 3 → ℝ,
      0 ≤ BoxGaussian.curlQuadForm ℓ.coupling ℓ.side k o R w ∧
      BoxGaussian.curlQuadForm ℓ.coupling ℓ.side k o R w ≤
        C₁ * ∑ e : Fin 3, ∑ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)), w p e ^ 2 := fun w =>
    ⟨(cKer w).1, (cKer w).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))⟩
  have hchart₁ : BoxMarks.IsGoodChart T β K k c x C₁ (C₀ * (R : ℝ) ^ 4 * δ ^ 2)
      (C * (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3) (C * (R : ℝ) ^ (-(2 / 3 : ℝ)) * δ) Cj xp :=
    ⟨cB, cLikely, fun u hu => cOff _ hu, isInGauge_mono hCC₁ hδ cGauge, cLaw, hasCurl_mono hCC₁ hδ le_rfl cCurl, hcKer⟩
  obtain ⟨κ, κ', κ₀, κ₀', hm₁, hm₂⟩ :=
    hmarks d hd (hdm') K β al T hchain k m R x hk hx rfl hm f h hpair o hnf hnh c _ _ _ hchart₁
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
  have hpowx : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hxpos.le _
  have hpowR : 0 ≤ (R : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg hRnn _
  have hlog0 : 0 ≤ Real.log x := by linarith
  have hε : C * (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3 ≤
      C₂ * (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3 := by
    have : C ≤ C₂ := hCC₁.trans hC₁₂
    gcongr
  have hφ : C * (R : ℝ) ^ (-(2 / 3 : ℝ)) * δ ≤ C₂ * (R : ℝ) ^ (-(2 / 3 : ℝ)) * δ * Real.log x := by
    have h1 : C * ((R : ℝ) ^ (-(2 / 3 : ℝ)) * δ) ≤ C₂ * ((R : ℝ) ^ (-(2 / 3 : ℝ)) * δ) :=
      mul_le_mul_of_nonneg_right (hCC₁.trans hC₁₂) (by positivity)
    have h2 : 0 ≤ C₂ * ((R : ℝ) ^ (-(2 / 3 : ℝ)) * δ) := by positivity
    nlinarith
  have hcKer₂ : ∀ w : TorusFields.TorusPlaquette (BoxResponses.boxSide ℓ.side K k) → Fin 3 → ℝ,
      0 ≤ BoxGaussian.curlQuadForm ℓ.coupling ℓ.side k o R w ∧
      BoxGaussian.curlQuadForm ℓ.coupling ℓ.side k o R w ≤
        C₂ * ∑ e : Fin 3, ∑ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)), w p e ^ 2 := fun w =>
    ⟨(hcKer w).1, (hcKer w).2.trans (mul_le_mul_of_nonneg_right hC₁₂
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))⟩
  have hchart₂ : BoxMarks.IsGoodChart T β K k c x C₂ (C₀ * (R : ℝ) ^ 4 * δ ^ 2)
      (C₂ * (R : ℝ) ^ 9 * x ^ (-(1 / 2) : ℝ) * Real.log x ^ 3)
      (C₂ * (R : ℝ) ^ (-(2 / 3) : ℝ) * δ * Real.log x) Cj xp :=
    ⟨cB, cLikely, fun u hu => cOff _ hu, isInGauge_mono (hCC₁.trans hC₁₂) hδ cGauge, hasLaw_mono hε cLaw,
      hasCurl_mono (hCC₁.trans hC₁₂) hδ hφ cCurl, hcKer₂⟩
  have hnpos : 0 ≤ lengthInSites ℓ.side K k d := by
    simp only [lengthInSites]; positivity
  have hE₁ : Cm * ((vt * lengthInSites ℓ.side K k d)⁻¹ + Real.exp (-(cc * R))) ≤
      C₂ * ((vt * lengthInSites ℓ.side K k d)⁻¹ + Real.exp (-(cc * R))) :=
    mul_le_mul_of_nonneg_right hCm₂ (by positivity)
  have hE₂ : Cm * lengthInSites ℓ.side K k d ^ 4 * (R : ℝ) ^ 8 * δ ^ 3 + Real.exp (-(cc * R)) ≤
      C₂ * lengthInSites ℓ.side K k d ^ 4 * (R : ℝ) ^ 8 * δ ^ 3 + Real.exp (-(cc * R)) := by
    gcongr
  obtain ⟨g₁, g₂, g₃⟩ := hprod d hd hdp' K β al T hchain k m R x hk hx rfl hm hside' f h hpair o hwf hwh c _ hchart₂
    κ κ' κ₀ κ₀' (isBoxKernelFamily_mono hCm₂ hE₁ hE₂ hm₁) (isBoxKernelFamily_mono hCm₂ hE₁ hE₂ hm₂)
  exact ⟨_, g₁, g₂, g₃⟩
end YangMills.Construction.StateLaws
end
