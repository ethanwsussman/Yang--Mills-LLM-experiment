import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import YangMills.Construction.LawInAState.SitesOfAPair
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
open BoxResponses ResponseInTheExpansion WeightedResponses TorusFields TorusMetric ReflectionKernel
open InfiniteLattice (AmbientSpace)
namespace PairSites
variable {L : ℕ} [NeZero L]
private theorem boxSide_mul_spacing {K k : ℕ} (hk : k ≤ K) :
    ((boxSide L K k : ℕ) : ℝ) * ((L : ℝ) ^ k / (L : ℝ) ^ K) = 2 := by apply _root_.YangMills.SharedProofs.p9522 <;> assumption
private theorem valMinAbs_intCast_of_small {N : ℕ} [NeZero N] (w : ℤ) (h : 2 * |w| < (N : ℤ)) :
    ((w : ZMod N)).valMinAbs = w := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
private theorem euclidNormVec_add_le (u v : AmbientSpace) :
    euclidNormVec (u + v) ≤ euclidNormVec u + euclidNormVec v := by apply _root_.YangMills.SharedProofs.p2091 <;> assumption
private theorem euclidNormVec_le_of_abs_le {v : AmbientSpace} {s : ℝ} (hs : 0 ≤ s) (h : ∀ i, |v i| ≤ s) :
    euclidNormVec v ≤ 2 * s := by apply _root_.YangMills.SharedProofs.p16936 <;> assumption
private theorem exists_lift_of_mem_support (hP : plaquetteWeightAtSiteStatement) (hodd : Odd L) {K k : ℕ}
    (hk : k ≤ K) (f : AmbientSpace → ℝ)
    (y : TorusSite (boxSide L K k)) (hy : y ∈ weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k f)) :
    ∃ (u : Fin 4 → ℤ) (x : AmbientSpace), (∀ i, ((u i : ℤ) : ZMod (boxSide L K k)) = y i) ∧ f x ≠ 0 ∧
      ∀ i, |(u i : ℝ) * ((L : ℝ) ^ k / (L : ℝ) ^ K) - x i| ≤ (L : ℝ) ^ k / (L : ℝ) ^ K / 2 := by
  classical
  obtain ⟨-, p, hp, hne⟩ := Finset.mem_filter.mp hy
  set a : ℝ := (L : ℝ) ^ k / (L : ℝ) ^ K with ha
  have hu₀ : ∀ i, (((((y i).cast : ℤ)) : ℤ) : ZMod (boxSide L K k)) = y i :=
    fun i => ZMod.intCast_zmod_cast (y i)
  obtain ⟨θ, hθ, hv⟩ := hP L hodd K k hk f y (fun i => ((y i).cast : ℤ)) hu₀ p hp
  rw [← ha] at hθ hv
  rw [hv] at hne
  unfold periodizeUnitTorus at hne
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Fin 4 → ℤ, f (fun i => (((y i).cast : ℤ) : ℝ) * a + θ i + 2 * (ζ i : ℝ)) ≠ 0 := by
    by_contra hall
    push_neg at hall
    refine hne ?_
    have e : (fun z : Fin 4 → ℤ => f fun i => (fun i => (((y i).cast : ℤ) : ℝ) * a + θ i) i + 2 * (z i : ℝ)) =
        fun _ => 0 :=
      funext fun z => hall z
    rw [e]
    simp
  have hN := boxSide_mul_spacing (L := L) hk
  rw [← ha] at hN
  refine ⟨fun i => ((y i).cast : ℤ) + ((boxSide L K k : ℕ) : ℤ) * ζ i, _, fun i => ?_, hζ, fun i => ?_⟩
  · simp [ZMod.intCast_zmod_cast]
  · have e : ((((y i).cast : ℤ) + ((boxSide L K k : ℕ) : ℤ) * ζ i : ℤ) : ℝ) * a -
        ((((y i).cast : ℤ) : ℝ) * a + θ i + 2 * (ζ i : ℝ)) = -θ i := by
      push_cast
      linear_combination (ζ i : ℝ) * hN
    rw [e, abs_neg]
    exact hθ i
private theorem exists_lift_of_mem_near (hP : plaquetteWeightAtSiteStatement) (hodd : Odd L) {K k : ℕ}
    (hk : k ≤ K) (f : AmbientSpace → ℝ)
    (y : TorusSite (boxSide L K k))
    (hy : y ∈ sitesWithinTwo (weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k f)))
    (ha0 : 0 < (L : ℝ) ^ k / (L : ℝ) ^ K) :
    ∃ (u : Fin 4 → ℤ) (x : AmbientSpace), (∀ i, ((u i : ℤ) : ZMod (boxSide L K k)) = y i) ∧ f x ≠ 0 ∧
      ∀ i, |(u i : ℝ) * ((L : ℝ) ^ k / (L : ℝ) ^ K) - x i| ≤ 3 * ((L : ℝ) ^ k / (L : ℝ) ^ K) := by
  classical
  obtain ⟨-, y', hy', hd⟩ := Finset.mem_filter.mp hy
  obtain ⟨u', x, hu', hx, hn⟩ := exists_lift_of_mem_support hP hodd hk f y' hy'
  refine ⟨fun i => u' i + (y i - y' i).valMinAbs, x, fun i => ?_, hx, fun i => ?_⟩
  · have := hu' i
    push_cast
    rw [this]
    ring
  · have h1 : ((y i - y' i).valMinAbs).natAbs ≤ supDist y y' :=
      Finset.le_sup (f := fun i => ((y i - y' i).valMinAbs).natAbs) (Finset.mem_univ i)
    have h2 : |(((y i - y' i).valMinAbs : ℤ) : ℝ)| ≤ 2 := by
      have : (((y i - y' i).valMinAbs).natAbs : ℝ) ≤ 2 := by exact_mod_cast h1.trans hd
      rwa [Nat.cast_natAbs, Int.cast_abs] at this
    set a : ℝ := (L : ℝ) ^ k / (L : ℝ) ^ K with ha
    have b1 := abs_le.mp (hn i)
    have b2 := abs_le.mp h2
    push_cast
    rw [abs_le]
    constructor <;> nlinarith [b1.1, b1.2, b2.1, b2.2]
private theorem blockMean_eq_zero_of_not_mem (hM : BlockMeanIsLinearAndLocal) (hodd : Odd L) {K k : ℕ}
    (f : AmbientSpace → ℝ)
    (y : TorusSite (boxSide L K k)) (hy : y ∉ weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k f)) :
    blockMean L k (boxSide L K k) y (unitTorusWeight L K k f) = 0 := by
  classical
  obtain ⟨-, hlin, hread⟩ := hM L hodd k (boxSide L K k) y
  have h1 := hlin 0 0 (unitTorusWeight L K k f) (unitTorusWeight L K k f)
  have h2 := hread (unitTorusWeight L K k f)
    (fun p => 0 * unitTorusWeight L K k f p + 0 * unitTorusWeight L K k f p) fun p hp => by
      by_contra hne
      refine hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, hp, ?_⟩)
      simpa using hne
  rw [h2, h1]
  ring
private theorem card_sitesWithinTwo_le (hP : plaquetteWeightAtSiteStatement) (hodd : Odd L) {K k : ℕ} (hk : k ≤ K)
    {c : AmbientSpace} {d : ℝ}
    {f : AmbientSpace → ℝ} (hf : ∀ x, f x ≠ 0 → ∀ i, |x i - c i| ≤ 6 * d) (hd : 0 < d)
    (ha0 : 0 < (L : ℝ) ^ k / (L : ℝ) ^ K) (ha64 : 64 * ((L : ℝ) ^ k / (L : ℝ) ^ K) ≤ d) :
    ((sitesWithinTwo (weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k f))).card : ℝ) ≤
      (15 * (d / ((L : ℝ) ^ k / (L : ℝ) ^ K))) ^ 4 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (L : ℝ) ^ k / (L : ℝ) ^ K := ⟨_, rfl⟩
  have hnear := exists_lift_of_mem_near hP hodd hk f
  rw [← ha] at ha0 ha64 hnear ⊢
  set n : ℝ := d / a with hn
  have hn64 : 64 ≤ n := by
    rw [hn, le_div_iff₀ ha0]
    exact ha64
  have hna : n * a = d := by rw [hn]; field_simp
  set e : Fin 4 → ℤ := fun i => ⌊c i / a⌋ with he
  set r : ℕ := ⌈7 * n⌉₊ with hr
  set B : Finset (Fin 4 → ℤ) := Fintype.piFinset fun i => Finset.Icc (e i - r) (e i + r) with hB
  have hsub : sitesWithinTwo (weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k f)) ⊆
      B.image fun u i => ((u i : ℤ) : ZMod (boxSide L K k)) := by
    intro y hy
    obtain ⟨u, x, hu, hx, hn'⟩ := hnear y hy ha0
    refine Finset.mem_image.mpr ⟨u, Fintype.mem_piFinset.mpr fun i => ?_, funext hu⟩
    have b1 := abs_le.mp (hn' i)
    have b2 := abs_le.mp (hf x hx i)
    have b3 := Int.floor_le (c i / a)
    have b4 := Int.lt_floor_add_one (c i / a)
    have ec : c i = (c i / a) * a := by field_simp
    have b5 : (7 * n) ≤ (r : ℝ) := Nat.le_ceil _
    have b6 : |(u i : ℝ) - (e i : ℝ)| ≤ r := by
      have t1 : ((e i : ℝ)) * a ≤ c i := by
        rw [ec]; exact mul_le_mul_of_nonneg_right b3 ha0.le
      have t2 : c i < ((e i : ℝ) + 1) * a := by
        conv_lhs => rw [ec]
        exact mul_lt_mul_of_pos_right b4 ha0
      have t3 : |(u i : ℝ) - (e i : ℝ)| * a ≤ (7 * n) * a := by
        rw [← abs_of_pos ha0, ← abs_mul, abs_of_pos ha0, sub_mul, abs_le]
        constructor <;> nlinarith [b1.1, b1.2, b2.1, b2.2]
      have := le_of_mul_le_mul_right t3 ha0
      linarith
    have b7 := abs_le.mp b6
    rw [Finset.mem_Icc]
    constructor
    · have : (e i : ℝ) - r ≤ u i := by linarith [b7.1]
      exact_mod_cast this
    · have : (u i : ℝ) ≤ e i + r := by linarith [b7.2]
      exact_mod_cast this
  have hc1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  have hc2 : B.card = (2 * r + 1) ^ 4 := by
    rw [hB, Fintype.card_piFinset]
    have : ∀ i : Fin 4, (Finset.Icc (e i - r) (e i + r)).card = 2 * r + 1 := by
      intro i
      rw [Int.card_Icc]
      omega
    simp [this]
  rw [hc2] at hc1
  have hc3 : ((sitesWithinTwo (weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k f))).card : ℝ) ≤
      (2 * (r : ℝ) + 1) ^ 4 := by
    exact_mod_cast hc1
  refine hc3.trans (pow_le_pow_left₀ (by positivity) ?_ 4)
  have := Nat.ceil_lt_add_one (show 0 ≤ 7 * n by positivity)
  linarith
end PairSites
open PairSites in
theorem pairSitesStatement_holds (hM : BlockMeanIsLinearAndLocal) (hP : plaquetteWeightAtSiteStatement) :
    pairSitesStatement := by
  intro L _ hodd K k hk c d Λ f h hp hd hd1 ha64
  have hLp : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have ha0 : 0 < (L : ℝ) ^ k / (L : ℝ) ^ K := by positivity
  refine ⟨blockMean_eq_zero_of_not_mem hM hodd f, blockMean_eq_zero_of_not_mem hM hodd h,
    card_sitesWithinTwo_le hP hodd hk hp.f_localized hd ha0 ha64,
    card_sitesWithinTwo_le hP hodd hk hp.h_localized hd ha0 ha64, fun y hy z hz => ?_⟩
  obtain ⟨u, x, hu, hx, hn⟩ := exists_lift_of_mem_near hP hodd hk f y hy ha0
  obtain ⟨u', x', hu', hx', hn'⟩ := exists_lift_of_mem_near hP hodd hk h z hz ha0
  have hN := boxSide_mul_spacing (L := L) hk
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (L : ℝ) ^ k / (L : ℝ) ^ K := ⟨_, rfl⟩
  rw [← ha] at ha0 ha64 hn hn' hN ⊢
  set n : ℝ := d / a with hnn
  have hna : n * a = d := by rw [hnn]; field_simp
  have hw : ∀ i, |((u i - u' i : ℤ) : ℝ)| ≤ 13 * n := by
    intro i
    have b1 := abs_le.mp (hn i)
    have b2 := abs_le.mp (hn' i)
    have b3 := abs_le.mp (hp.f_localized x hx i)
    have b4 := abs_le.mp (hp.h_localized x' hx' i)
    have t3 : |((u i - u' i : ℤ) : ℝ)| * a ≤ (13 * n) * a := by
      rw [← abs_of_pos ha0, ← abs_mul, abs_of_pos ha0, abs_le]
      push_cast
      constructor <;> nlinarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2]
    exact le_of_mul_le_mul_right t3 ha0
  have hD : ∀ i, minimalSiteDiff y z i = u i - u' i := by
    intro i
    simp only [minimalSiteDiff]
    rw [← hu i, ← hu' i, ← Int.cast_sub]
    refine valMinAbs_intCast_of_small _ ?_
    have h1 : 2 * |((u i - u' i : ℤ) : ℝ)| < ((boxSide L K k : ℕ) : ℝ) := by
      have h2 := hw i
      by_contra hcon
      push_neg at hcon
      have : ((boxSide L K k : ℕ) : ℝ) * a ≤ 2 * (13 * n) * a := by
        refine mul_le_mul_of_nonneg_right ?_ ha0.le
        linarith
      nlinarith
    have h3 : ((2 * |u i - u' i| : ℤ) : ℝ) < (((boxSide L K k : ℕ) : ℤ) : ℝ) := by
      push_cast
      push_cast at h1
      exact h1
    exact_mod_cast h3
  constructor
  · intro i
    rw [hD i]
    exact hw i
  · set v : AmbientSpace := fun i => ((u i - u' i : ℤ) : ℝ) * a with hv
    have d1 : d ≤ euclidNormVec (x - x') := hp.separated x x' hx hx'
    have d2 : euclidNormVec (x - x') ≤ euclidNormVec v + euclidNormVec ((x - x') - v) := by
      have := euclidNormVec_add_le v ((x - x') - v)
      rwa [add_sub_cancel] at this
    have d3 : euclidNormVec ((x - x') - v) ≤ 2 * (6 * a) := by
      refine euclidNormVec_le_of_abs_le (by positivity) fun i => ?_
      have b1 := abs_le.mp (hn i)
      have b2 := abs_le.mp (hn' i)
      simp only [Pi.sub_apply, hv]
      push_cast
      rw [abs_le]
      constructor <;> nlinarith [b1.1, b1.2, b2.1, b2.2]
    have d4 : d / 2 ≤ euclidNormVec v := by linarith
    have d5 : euclidNormVec v ^ 2 = a ^ 2 * normSq fun i => (minimalSiteDiff y z i : ℝ) := by
      rw [euclidNormVec, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      simp only [normSq, hv, hD, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have d6 : (d / 2) ^ 2 ≤ euclidNormVec v ^ 2 := pow_le_pow_left₀ (by positivity) d4 2
    rw [d5, ← hna] at d6
    have d7 : n ^ 2 / 4 * a ^ 2 ≤ (normSq fun i => (minimalSiteDiff y z i : ℝ)) * a ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right d7 (by positivity)
end YangMills.Construction.StateLaws
end
