import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import YangMills.Construction.ClusterExpansionOfAStep.MatchingClasses
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.ClusterExpansionOfAStep.ChartsOverTheTopOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.PlaquetteOfACutFieldProof
import YangMills.Construction.FormsOnATorus.InteriorRegularityProof
import YangMills.Construction.LawOnABoxOfTheFlow.AxialGaugeOfAColdFilling
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open YangMills.Construction.TorusFields (TorusSite TorusField TorusBond TorusPlaquette siteOfInt unitStep
  gaugeTransform holonomy curvature plaquettesIn plaquetteVertices supDist)
open YangMills.Construction.ResponseInTheExpansion (supBall lieFormCurl)
open YangMills.Construction.BlockAverages (UnitQuaternion imaginaryQuaternions expUnit)
private abbrev IntPoint : Type := Fin 4 → ℤ
private def basisVec (i : Fin 4) : IntPoint := Pi.single i 1
private def truncate (m : ℕ) (h : IntPoint) : IntPoint := fun k => if k.val < m then h k else 0
private def prodUp (f : ℤ → UnitQuaternion) : ℕ → UnitQuaternion
  | 0 => 1
  | t + 1 => prodUp f t * f t
private def prodDown (f : ℤ → UnitQuaternion) : ℕ → UnitQuaternion
  | 0 => 1
  | t + 1 => prodDown f t * (f (-(t : ℤ) - 1))⁻¹
private def lineTransport (f : ℤ → UnitQuaternion) (t : ℤ) : UnitQuaternion :=
  if 0 ≤ t then prodUp f t.toNat else prodDown f (-t).toNat
private theorem lineTransport_zero (f : ℤ → UnitQuaternion) : lineTransport f 0 = 1 := by
  simp [lineTransport, prodUp]
private theorem lineTransport_succ (f : ℤ → UnitQuaternion) (t : ℤ) :
    lineTransport f (t + 1) = lineTransport f t * f t := by
  rcases le_or_gt 0 t with ht | ht
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ht
    have h1 : (0 : ℤ) ≤ (m : ℤ) + 1 := by omega
    have h2 : ((m : ℤ) + 1).toNat = m + 1 := by omega
    simp only [lineTransport, h1, ht, if_true, h2, prodUp, Int.toNat_natCast]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, t = -(m : ℤ) - 1 := ⟨(-t - 1).toNat, by omega⟩
    have h1 : lineTransport f (-(m : ℤ) - 1) = prodDown f m * (f (-(m : ℤ) - 1))⁻¹ := by
      have h0 : ¬ (0 : ℤ) ≤ -(m : ℤ) - 1 := by omega
      have h2 : (-(-(m : ℤ) - 1)).toNat = m + 1 := by omega
      simp only [lineTransport, h0, if_false, h2, prodDown]
    have h3 : lineTransport f (-(m : ℤ) - 1 + 1) = prodDown f m := by
      have e : -(m : ℤ) - 1 + 1 = -(m : ℤ) := by ring
      rw [e]
      cases m with
      | zero => simp [lineTransport, prodUp, prodDown]
      | succ k =>
        have h0 : ¬ (0 : ℤ) ≤ -((k + 1 : ℕ) : ℤ) := by omega
        have h2 : (-(-((k + 1 : ℕ) : ℤ))).toNat = k + 1 := by omega
        simp only [lineTransport, h0, if_false, h2]
    rw [h1, h3, inv_mul_cancel_right]
private def axialSegment (U : IntPoint → Fin 4 → UnitQuaternion) (j : Fin 4) (h : IntPoint) : UnitQuaternion :=
  lineTransport (fun t => U (Function.update (truncate j h) j t) j) (h j)
private def axialGaugeInt (U : IntPoint → Fin 4 → UnitQuaternion) (h : IntPoint) : UnitQuaternion :=
  axialSegment U 0 h * axialSegment U 1 h * axialSegment U 2 h * axialSegment U 3 h
private theorem truncate_add_basisVec (k j : Fin 4) (hkj : k ≤ j) (h : IntPoint) :
    truncate k (h + basisVec j) = truncate k h := by
  funext l
  simp only [truncate, basisVec, Pi.add_apply]
  split_ifs with hl
  · have hne : l ≠ j := by
      intro e
      subst e
      omega
    simp [Pi.single_apply, hne]
  · rfl
private theorem axialSegment_of_lt (U : IntPoint → Fin 4 → UnitQuaternion) {k j : Fin 4} (hkj : k < j)
    (h : IntPoint) : axialSegment U k (h + basisVec j) = axialSegment U k h := by
  have h1 : (h + basisVec j) k = h k := by simp [basisVec, Pi.single_apply, hkj.ne]
  simp only [axialSegment, truncate_add_basisVec k j hkj.le, h1]
private theorem axialSegment_self (U : IntPoint → Fin 4 → UnitQuaternion) (j : Fin 4) (h : IntPoint)
    (hz : ∀ k, j < k → h k = 0) : axialSegment U j (h + basisVec j) = axialSegment U j h * U h j := by
  have h1 : (h + basisVec j) j = h j + 1 := by simp [basisVec]
  have h2 : Function.update (truncate j h) j (h j) = h := by
    funext l
    by_cases hl : l = j
    · subst hl
      simp
    · simp only [Function.update_of_ne hl, truncate]
      split_ifs with hlj
      · rfl
      · have hjl : j < l := by
          rw [Fin.lt_def]
          have : l.val ≠ j.val := fun e => hl (Fin.ext e)
          omega
        exact (hz l hjl).symm
  simp only [axialSegment, truncate_add_basisVec j j le_rfl, h1]
  rw [lineTransport_succ, h2]
private theorem axialSegment_of_eq_zero (U : IntPoint → Fin 4 → UnitQuaternion) {k : Fin 4} {h : IntPoint}
    (hz : h k = 0) : axialSegment U k h = 1 := by
  simp only [axialSegment, hz, lineTransport_zero]
private theorem axialGaugeInt_add_basisVec (U : IntPoint → Fin 4 → UnitQuaternion) (j : Fin 4) (h : IntPoint)
    (hz : ∀ k, j < k → h k = 0) : axialGaugeInt U (h + basisVec j) = axialGaugeInt U h * U h j := by
  have hz' : ∀ k, j < k → (h + basisVec j) k = 0 := fun k hk => by
    simp [basisVec, Pi.single_apply, hk.ne', hz k hk]
  have hs := axialSegment_self U j h hz
  obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  · simp only [axialGaugeInt, hs, axialSegment_of_eq_zero U (hz' 1 (by decide)),
      axialSegment_of_eq_zero U (hz' 2 (by decide)), axialSegment_of_eq_zero U (hz' 3 (by decide)),
      axialSegment_of_eq_zero U (hz 1 (by decide)), axialSegment_of_eq_zero U (hz 2 (by decide)),
      axialSegment_of_eq_zero U (hz 3 (by decide)), mul_one]
  · simp only [axialGaugeInt, hs, axialSegment_of_lt U (show (0 : Fin 4) < 1 by decide),
      axialSegment_of_eq_zero U (hz' 2 (by decide)), axialSegment_of_eq_zero U (hz' 3 (by decide)),
      axialSegment_of_eq_zero U (hz 2 (by decide)), axialSegment_of_eq_zero U (hz 3 (by decide)), mul_one,
      mul_assoc]
  · simp only [axialGaugeInt, hs, axialSegment_of_lt U (show (0 : Fin 4) < 2 by decide),
      axialSegment_of_lt U (show (1 : Fin 4) < 2 by decide), axialSegment_of_eq_zero U (hz' 3 (by decide)),
      axialSegment_of_eq_zero U (hz 3 (by decide)), mul_one, mul_assoc]
  · simp only [axialGaugeInt, hs, axialSegment_of_lt U (show (0 : Fin 4) < 3 by decide),
      axialSegment_of_lt U (show (1 : Fin 4) < 3 by decide), axialSegment_of_lt U (show (2 : Fin 4) < 3 by decide),
      mul_assoc]
private theorem axialGaugeInt_zero (U : IntPoint → Fin 4 → UnitQuaternion) : axialGaugeInt U 0 = 1 := by
  simp [axialGaugeInt, axialSegment_of_eq_zero]
private def axialGauged (U : IntPoint → Fin 4 → UnitQuaternion) (h : IntPoint) (i : Fin 4) : UnitQuaternion :=
  axialGaugeInt U h * U h i * (axialGaugeInt U (h + basisVec i))⁻¹
private theorem axialGauged_eq_one (U : IntPoint → Fin 4 → UnitQuaternion) (j : Fin 4) (h : IntPoint)
    (hz : ∀ k, j < k → h k = 0) : axialGauged U h j = 1 := by
  simp only [axialGauged, axialGaugeInt_add_basisVec U j h hz, mul_inv_cancel]
private def holonomyInt (U : IntPoint → Fin 4 → UnitQuaternion) (h : IntPoint) (i j : Fin 4) : UnitQuaternion :=
  U h i * U (h + basisVec i) j * (U (h + basisVec j) i)⁻¹ * (U h j)⁻¹
private theorem holonomy_conj {α ι : Type} [AddCommMonoid α] (γ : α → UnitQuaternion) (U : α → ι → UnitQuaternion)
    (e : ι → α) (x : α) (i j : ι) :
    (γ x * U x i * (γ (x + e i))⁻¹) * (γ (x + e i) * U (x + e i) j * (γ (x + e i + e j))⁻¹) *
        (γ (x + e j) * U (x + e j) i * (γ (x + e j + e i))⁻¹)⁻¹ * (γ x * U x j * (γ (x + e j))⁻¹)⁻¹ =
      γ x * (U x i * U (x + e i) j * (U (x + e j) i)⁻¹ * (U x j)⁻¹) * (γ x)⁻¹ := by
  rw [add_right_comm x (e j) (e i)]
  group
private def distOne (a : UnitQuaternion) : ℝ := ‖(a : ℍ[ℝ]) - 1‖
private theorem norm_coe_unit (a : UnitQuaternion) : ‖(a : ℍ[ℝ])‖ = 1 := CStarRing.norm_coe_unitary a
private theorem distOne_one : distOne 1 = 0 := by simp [distOne]
private theorem distOne_nonneg (a : UnitQuaternion) : 0 ≤ distOne a := norm_nonneg _
private theorem distOne_mul_le (a b : UnitQuaternion) : distOne (a * b) ≤ distOne a + distOne b := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
private theorem distOne_inv (a : UnitQuaternion) : distOne a⁻¹ = distOne a := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
private theorem distOne_conj (a q : UnitQuaternion) : distOne (a * q * a⁻¹) = distOne q := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
private theorem ladder_rung (U : IntPoint → Fin 4 → UnitQuaternion) (δ : ℝ) (i j : Fin 4) (hij : i < j)
    (x : IntPoint) (hz : ∀ k, j < k → x k = 0) (hP : distOne (holonomyInt U x i j) ≤ δ) :
    distOne (axialGauged U x i) ≤ δ + distOne (axialGauged U (x + basisVec j) i) ∧
      distOne (axialGauged U (x + basisVec j) i) ≤ δ + distOne (axialGauged U x i) := by
  have hz' : ∀ k, j < k → (x + basisVec i) k = 0 := fun k hk => by
    have : k ≠ i := (hij.trans hk).ne'
    simp [basisVec, Pi.single_apply, this, hz k hk]
  have h1 : axialGauged U x j = 1 := axialGauged_eq_one U j x hz
  have h2 : axialGauged U (x + basisVec i) j = 1 := axialGauged_eq_one U j _ hz'
  have hQ : axialGauged U x i * axialGauged U (x + basisVec i) j * (axialGauged U (x + basisVec j) i)⁻¹ *
      (axialGauged U x j)⁻¹ = axialGaugeInt U x * holonomyInt U x i j * (axialGaugeInt U x)⁻¹ :=
    holonomy_conj (axialGaugeInt U) U basisVec x i j
  rw [h1, h2, mul_one, inv_one, mul_one] at hQ
  have hQ' : distOne (axialGauged U x i * (axialGauged U (x + basisVec j) i)⁻¹) ≤ δ := by
    rw [hQ, distOne_conj]
    exact hP
  constructor
  · have e : axialGauged U x i =
        (axialGauged U x i * (axialGauged U (x + basisVec j) i)⁻¹) * axialGauged U (x + basisVec j) i := by group
    calc distOne (axialGauged U x i) =
          distOne ((axialGauged U x i * (axialGauged U (x + basisVec j) i)⁻¹) * axialGauged U (x + basisVec j) i) := by
          rw [← e]
      _ ≤ _ := (distOne_mul_le _ _).trans (by linarith)
  · have e : axialGauged U (x + basisVec j) i =
        (axialGauged U x i * (axialGauged U (x + basisVec j) i)⁻¹)⁻¹ * axialGauged U x i := by group
    calc distOne (axialGauged U (x + basisVec j) i) =
          distOne ((axialGauged U x i * (axialGauged U (x + basisVec j) i)⁻¹)⁻¹ * axialGauged U x i) := by
          rw [← e]
      _ ≤ _ := (distOne_mul_le _ _).trans (by rw [distOne_inv]; linarith)
private abbrev InCube (r : ℕ) (h : IntPoint) : Prop := ∀ i, |h i| ≤ (r : ℤ)
private theorem basisVec_apply_of_ne {i j : Fin 4} (h : i ≠ j) : basisVec i j = 0 := by simp [basisVec, h.symm]
private theorem ladder_bound (U : IntPoint → Fin 4 → UnitQuaternion) (B : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (i j : Fin 4)
    (hij : i < j)
    (hP : ∀ x : IntPoint, InCube B x → InCube B (x + basisVec i) → InCube B (x + basisVec j) →
      InCube B (x + basisVec i + basisVec j) → distOne (holonomyInt U x i j) ≤ δ)
    (h : IntPoint) (hz : ∀ k, j < k → h k = 0) (hb : InCube B h) (hb' : InCube B (h + basisVec i)) :
    distOne (axialGauged U h i) ≤ distOne (axialGauged U (Function.update h j 0) i) + B * δ := by
  have hne : i ≠ j := hij.ne
  let b : ℤ → IntPoint := fun t => Function.update h j t
  have bz : ∀ t k, j < k → b t k = 0 := fun t k hk => by
    simp [b, Function.update_of_ne hk.ne', hz k hk]
  have bstep : ∀ t, b t + basisVec j = b (t + 1) := fun t => by
    funext k
    by_cases hk : k = j
    · subst hk
      simp [b, basisVec]
    · simp [b, basisVec, Function.update_of_ne hk, hk]
  have box0 : ∀ t : ℤ, |t| ≤ B → InCube B (b t) := fun t ht k => by
    by_cases hk : k = j
    · subst hk
      simpa [b] using ht
    · simpa [b, Function.update_of_ne hk] using hb k
  have box1 : ∀ t : ℤ, |t| ≤ B → InCube B (b t + basisVec i) := fun t ht k => by
    by_cases hk : k = j
    · subst hk
      have h0 : basisVec i k = 0 := basisVec_apply_of_ne hne
      simpa [b, h0] using ht
    · have h1 := hb' k
      simpa [b, Function.update_of_ne hk] using h1
  have move : ∀ t : ℤ, |t| ≤ B → |t + 1| ≤ B →
      distOne (axialGauged U (b t) i) ≤ δ + distOne (axialGauged U (b (t + 1)) i) ∧
      distOne (axialGauged U (b (t + 1)) i) ≤ δ + distOne (axialGauged U (b t) i) := fun t h0 h1 => by
    have h2 := ladder_rung U δ i j hij (b t) (bz t) (hP _ (box0 t h0) (box1 t h0)
      (by rw [bstep]; exact box0 _ h1) (by rw [add_right_comm, bstep]; exact box1 _ h1))
    rwa [bstep] at h2
  have main : ∀ (m : ℕ) (t : ℤ), t.natAbs = m → m ≤ B →
      distOne (axialGauged U (b t) i) ≤ distOne (axialGauged U (b 0) i) + m * δ := by
    intro m
    induction m with
    | zero =>
      intro t ht _
      have h0 : t = 0 := by omega
      subst h0
      simp
    | succ m ih =>
      intro t ht hm
      rcases lt_trichotomy t 0 with hneg | h0 | hpos
      · have h1 := ih (t + 1) (by omega) (by omega)
        have h2 := (move t (abs_le.mpr ⟨by omega, by omega⟩) (abs_le.mpr ⟨by omega, by omega⟩)).1
        push_cast
        linarith
      · omega
      · have h1 := ih (t - 1) (by omega) (by omega)
        have h2 := (move (t - 1) (abs_le.mpr ⟨by omega, by omega⟩) (abs_le.mpr ⟨by omega, by omega⟩)).2
        rw [sub_add_cancel] at h2
        push_cast
        linarith
  have hjB : (h j).natAbs ≤ B := by
    have := abs_le.mp (hb j)
    omega
  have hm := main (h j).natAbs (h j) rfl hjB
  have e : b (h j) = h := Function.update_eq_self j h
  rw [e] at hm
  have h3 : ((h j).natAbs : ℝ) * δ ≤ B * δ := by
    have : ((h j).natAbs : ℝ) ≤ B := by exact_mod_cast hjB
    exact mul_le_mul_of_nonneg_right this hδ
  exact hm.trans (by simpa [b] using h3)
private theorem truncate_mem_cube (B m : ℕ) (h : IntPoint) (hb : InCube B h) : InCube B (truncate m h) :=
  fun k => by
  simp only [truncate]
  split_ifs
  · exact hb k
  · simp
private theorem truncate_add_mem_cube (B m : ℕ) (i : Fin 4) (hi : i.val < m) (h : IntPoint) (hb : InCube B h)
    (hb' : InCube B (h + basisVec i)) : InCube B (truncate m h + basisVec i) := fun k => by
  by_cases hk : k = i
  · subst hk
    have h1 := hb' k
    simpa [truncate, hi] using h1
  · have h1 := truncate_mem_cube B m h hb k
    simpa [basisVec_apply_of_ne (Ne.symm hk)] using h1
private theorem axialGauged_distOne_le (U : IntPoint → Fin 4 → UnitQuaternion) (B : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hP : ∀ i j : Fin 4, i < j → ∀ x : IntPoint, InCube B x → InCube B (x + basisVec i) →
      InCube B (x + basisVec j) → InCube B (x + basisVec i + basisVec j) → distOne (holonomyInt U x i j) ≤ δ)
    (i : Fin 4) (h : IntPoint) (hb : InCube B h) (hb' : InCube B (h + basisVec i)) :
    distOne (axialGauged U h i) ≤ 3 * (B * δ) := by
  have key : ∀ m : ℕ, m + 1 ≤ 4 → distOne (axialGauged U (truncate (m + 1) h) i) ≤ m * (B * δ) := by
    intro m
    induction m with
    | zero =>
      intro _
      have h1 : axialGauged U (truncate (0 + 1) h) i = 1 := axialGauged_eq_one U i _ fun k hk => by
        have h2 : i.val < k.val := hk
        simp only [truncate]
        rw [if_neg (by omega)]
      rw [h1, distOne_one]
      simp
    | succ m ih =>
      intro hm
      have ihm := ih (by omega)
      by_cases hmi : m + 1 ≤ i.val
      · have h1 : axialGauged U (truncate (m + 1 + 1) h) i = 1 := axialGauged_eq_one U i _ fun k hk => by
          have h2 : i.val < k.val := hk
          simp only [truncate]
          rw [if_neg (by omega)]
        rw [h1, distOne_one]
        positivity
      · let j : Fin 4 := ⟨m + 1, by omega⟩
        have hij : i < j := by
          rw [Fin.lt_def]
          show i.val < m + 1
          omega
        have hz : ∀ k, j < k → truncate (m + 1 + 1) h k = 0 := fun k hk => by
          have h2 : m + 1 < k.val := hk
          simp only [truncate]
          rw [if_neg (by omega)]
        have hl := ladder_bound U B δ hδ i j hij (hP i j hij) (truncate (m + 1 + 1) h) hz
          (truncate_mem_cube B _ h hb) (truncate_add_mem_cube B _ i (by omega) h hb hb')
        have hu : Function.update (truncate (m + 1 + 1) h) j 0 = truncate (m + 1) h := by
          funext l
          by_cases hl' : l = j
          · subst hl'
            simp [truncate, j]
          · have h2 : l.val ≠ m + 1 := fun e => hl' (Fin.ext e)
            simp only [Function.update_of_ne hl', truncate]
            by_cases h3 : l.val < m + 1
            · rw [if_pos h3, if_pos (by omega)]
            · rw [if_neg h3, if_neg (by omega)]
        rw [hu] at hl
        push_cast
        linarith
  have e : truncate 4 h = h := by
    funext k
    simp [truncate, k.isLt]
  have h3 := key 3 (by norm_num)
  simpa [e] using h3
private def imagPart (q : ℍ[ℝ]) : imaginaryQuaternions := ⟨q.im, by change q.im.re = 0; simp⟩
private def logUnit (a : UnitQuaternion) : imaginaryQuaternions :=
  (Real.arcsin ‖(a : ℍ[ℝ]).im‖ / ‖(a : ℍ[ℝ]).im‖) • imagPart (a : ℍ[ℝ])
private theorem norm_sq_eq_re_sq_add (q : ℍ[ℝ]) : ‖q‖ ^ 2 = q.re ^ 2 + ‖q.im‖ ^ 2 := by apply _root_.YangMills.Construction.TopLevelSites.norm_sq_eq_re_sq_add_norm_im_sq <;> assumption
private theorem coe_expUnit (A : imaginaryQuaternions) : ((expUnit A : UnitQuaternion) : ℍ[ℝ]) =
    ((Real.cos ‖A‖ : ℝ) : ℍ[ℝ]) + (Real.sin ‖A‖ / ‖A‖) • (A : ℍ[ℝ]) :=
  Quaternion.exp_of_re_eq_zero (A : ℍ[ℝ]) A.2
private theorem norm_imagPart (q : ℍ[ℝ]) : ‖imagPart q‖ = ‖q.im‖ := rfl
private theorem norm_logUnit (a : UnitQuaternion) : ‖logUnit a‖ = Real.arcsin ‖(a : ℍ[ℝ]).im‖ := by
  have hs0 : 0 ≤ ‖(a : ℍ[ℝ]).im‖ := norm_nonneg _
  by_cases h0 : ‖(a : ℍ[ℝ]).im‖ = 0
  · simp [logUnit, h0]
  · have hθ : 0 ≤ Real.arcsin ‖(a : ℍ[ℝ]).im‖ := Real.arcsin_nonneg.mpr hs0
    simp only [logUnit]
    rw [norm_smul, norm_imagPart, Real.norm_of_nonneg (div_nonneg hθ hs0), div_mul_cancel₀ _ h0]
private theorem expUnit_logUnit (a : UnitQuaternion) (ha : 0 < (a : ℍ[ℝ]).re) : expUnit (logUnit a) = a := by
  apply Subtype.ext
  have hsplit := norm_sq_eq_re_sq_add (a : ℍ[ℝ])
  rw [norm_coe_unit a] at hsplit
  have hs0 : 0 ≤ ‖(a : ℍ[ℝ]).im‖ := norm_nonneg _
  have hs1 : ‖(a : ℍ[ℝ]).im‖ ≤ 1 := by nlinarith
  by_cases h0 : ‖(a : ℍ[ℝ]).im‖ = 0
  · have hre : (a : ℍ[ℝ]).re = 1 := by
      rw [h0] at hsplit
      nlinarith
    have him : (a : ℍ[ℝ]).im = 0 := norm_eq_zero.mp h0
    have hl : logUnit a = 0 := by simp [logUnit, h0]
    have h1 : (a : ℍ[ℝ]) = 1 := by
      have := Quaternion.re_add_im (a : ℍ[ℝ])
      rw [hre, him] at this
      simpa using this.symm
    rw [hl, h1]
    show NormedSpace.exp (((0 : imaginaryQuaternions)) : ℍ[ℝ]) = 1
    simp
  · have hspos : 0 < ‖(a : ℍ[ℝ]).im‖ := lt_of_le_of_ne hs0 (Ne.symm h0)
    have hθ : 0 < Real.arcsin ‖(a : ℍ[ℝ]).im‖ := Real.arcsin_pos.mpr hspos
    have hsin : Real.sin (Real.arcsin ‖(a : ℍ[ℝ]).im‖) = ‖(a : ℍ[ℝ]).im‖ :=
      Real.sin_arcsin (by linarith) hs1
    have hcos : Real.cos (Real.arcsin ‖(a : ℍ[ℝ]).im‖) = (a : ℍ[ℝ]).re := by
      rw [Real.cos_arcsin, show (1 : ℝ) - ‖(a : ℍ[ℝ]).im‖ ^ 2 = (a : ℍ[ℝ]).re ^ 2 by linarith]
      exact Real.sqrt_sq ha.le
    rw [coe_expUnit, norm_logUnit, hcos, hsin]
    have h2 : ((logUnit a : imaginaryQuaternions) : ℍ[ℝ]) =
        (Real.arcsin ‖(a : ℍ[ℝ]).im‖ / ‖(a : ℍ[ℝ]).im‖) • (a : ℍ[ℝ]).im := rfl
    rw [h2, smul_smul, show ‖(a : ℍ[ℝ]).im‖ / Real.arcsin ‖(a : ℍ[ℝ]).im‖ *
      (Real.arcsin ‖(a : ℍ[ℝ]).im‖ / ‖(a : ℍ[ℝ]).im‖) = 1 by field_simp, one_smul]
    exact Quaternion.re_add_im _
private theorem arcsin_le_mul (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) : Real.arcsin s ≤ 7 / 6 * s := by
  rcases h0.eq_or_lt with rfl | hs
  · simp
  · have hθ : 0 < Real.arcsin s := Real.arcsin_pos.mpr hs
    have hθ' : Real.arcsin s < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr (by linarith)
    have ht := Real.lt_tan hθ hθ'
    have hcos : (6 / 7 : ℝ) ≤ Real.cos (Real.arcsin s) := by
      rw [Real.cos_arcsin]
      apply Real.le_sqrt_of_sq_le
      nlinarith
    have hcpos : 0 < Real.cos (Real.arcsin s) := by linarith
    rw [Real.tan_eq_sin_div_cos, Real.sin_arcsin (by linarith) (by linarith), lt_div_iff₀ hcpos] at ht
    nlinarith
private theorem logUnit_bound (a : UnitQuaternion) (ha : distOne a ≤ 1 / 2) :
    0 < (a : ℍ[ℝ]).re ∧ ‖logUnit a‖ ≤ 7 / 6 * distOne a := by
  have hs := norm_sq_eq_re_sq_add ((a : ℍ[ℝ]) - 1)
  have him : ((a : ℍ[ℝ]) - 1).im = (a : ℍ[ℝ]).im := by
    ext <;> simp
  have hre : ((a : ℍ[ℝ]) - 1).re = (a : ℍ[ℝ]).re - 1 := by simp
  rw [him, hre] at hs
  have he : distOne a = ‖(a : ℍ[ℝ]) - 1‖ := rfl
  rw [← he] at hs
  have he0 := distOne_nonneg a
  have hs0 : 0 ≤ ‖(a : ℍ[ℝ]).im‖ := norm_nonneg _
  have hle : ‖(a : ℍ[ℝ]).im‖ ≤ distOne a := by
    apply abs_le_of_sq_le_sq' _ he0 |>.2
    nlinarith [sq_nonneg ((a : ℍ[ℝ]).re - 1)]
  have hre1 : |(a : ℍ[ℝ]).re - 1| ≤ distOne a := by
    apply abs_le_of_sq_le_sq _ he0
    nlinarith [sq_nonneg ‖(a : ℍ[ℝ]).im‖]
  constructor
  · have := (abs_le.mp hre1).1
    linarith
  · rw [norm_logUnit]
    have := arcsin_le_mul _ hs0 (hle.trans ha)
    linarith
private theorem expUnit_sub_one_sub_le (A : imaginaryQuaternions) (h : ‖A‖ ≤ 1) :
    ‖((expUnit A : UnitQuaternion) : ℍ[ℝ]) - 1 - (A : ℍ[ℝ])‖ ≤ ‖A‖ ^ 2 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FourPlaquette.norm_expUnit_sub_one_sub_le_sq <;> assumption
private theorem expUnit_inv (A : imaginaryQuaternions) : (expUnit A)⁻¹ = expUnit (-A) := by apply _root_.YangMills.Construction.LeastQuarticGauge.expUnit_inv <;> assumption
private theorem norm_add_seven_le (a b c d e f g : ℍ[ℝ]) :
    ‖a + b + c + d + e + f + g‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ := by
  have h1 := norm_add_le (a + b + c + d + e + f) g
  have h2 := norm_add_le (a + b + c + d + e) f
  have h3 := norm_add_le (a + b + c + d) e
  have h4 := norm_add_le (a + b + c) d
  have h5 := norm_add_le (a + b) c
  have h6 := norm_add_le a b
  linarith
private theorem prod_four_sub_one_sub_le (E1 E2 E3 E4 Y1 Y2 Y3 Y4 : ℍ[ℝ]) (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1)
    (n3 : ‖E3‖ = 1) (n4 : ‖E4‖ = 1) (n2 : ‖E2‖ = 1)
    (h1 : ‖E1 - 1 - Y1‖ ≤ a ^ 2) (h2 : ‖E2 - 1 - Y2‖ ≤ a ^ 2) (h3 : ‖E3 - 1 - Y3‖ ≤ a ^ 2)
    (h4 : ‖E4 - 1 - Y4‖ ≤ a ^ 2) (y1 : ‖Y1‖ ≤ a) (y2 : ‖Y2‖ ≤ a) (y3 : ‖Y3‖ ≤ a) (y4 : ‖Y4‖ ≤ a) :
    ‖E1 * E2 * E3 * E4 - 1 - (Y1 + Y2 + Y3 + Y4)‖ ≤ 28 * a ^ 2 := by
  have w : ∀ E Y : ℍ[ℝ], ‖E - 1 - Y‖ ≤ a ^ 2 → ‖Y‖ ≤ a → ‖E - 1‖ ≤ 2 * a := fun E Y h y => by
    have e : E - 1 = (E - 1 - Y) + Y := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    nlinarith
  have w1 := w E1 Y1 h1 y1
  have w2 := w E2 Y2 h2 y2
  have w3 := w E3 Y3 h3 y3
  have w4 := w E4 Y4 h4 y4
  have p34 : ‖E3 * E4 - 1‖ ≤ 4 * a := by
    have e : E3 * E4 - 1 = (E3 - 1) * E4 + (E4 - 1) := by noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, n4, mul_one]
    linarith
  have p234 : ‖E2 * (E3 * E4) - 1‖ ≤ 6 * a := by
    have e : E2 * (E3 * E4) - 1 = (E2 - 1) * (E3 * E4) + (E3 * E4 - 1) := by noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul E3, n3, n4, one_mul, mul_one]
    linarith
  have e : E1 * E2 * E3 * E4 - 1 - (Y1 + Y2 + Y3 + Y4) =
      (E1 - 1) * (E2 * (E3 * E4) - 1) + (E2 - 1) * (E3 * E4 - 1) + (E3 - 1) * (E4 - 1) +
        (E1 - 1 - Y1) + (E2 - 1 - Y2) + (E3 - 1 - Y3) + (E4 - 1 - Y4) := by noncomm_ring
  rw [e]
  have t1 : ‖(E1 - 1) * (E2 * (E3 * E4) - 1)‖ ≤ 2 * a * (6 * a) := by
    rw [norm_mul]
    exact mul_le_mul w1 p234 (norm_nonneg _) (by positivity)
  have t2 : ‖(E2 - 1) * (E3 * E4 - 1)‖ ≤ 2 * a * (4 * a) := by
    rw [norm_mul]
    exact mul_le_mul w2 p34 (norm_nonneg _) (by positivity)
  have t3 : ‖(E3 - 1) * (E4 - 1)‖ ≤ 2 * a * (2 * a) := by
    rw [norm_mul]
    exact mul_le_mul w3 w4 (norm_nonneg _) (by positivity)
  calc _ ≤ ‖(E1 - 1) * (E2 * (E3 * E4) - 1)‖ + ‖(E2 - 1) * (E3 * E4 - 1)‖ + ‖(E3 - 1) * (E4 - 1)‖ +
        ‖E1 - 1 - Y1‖ + ‖E2 - 1 - Y2‖ + ‖E3 - 1 - Y3‖ + ‖E4 - 1 - Y4‖ := norm_add_seven_le ..
    _ ≤ 28 * a ^ 2 := by nlinarith
private theorem curl_le_distOne_holonomy (A1 A2 A3 A4 : imaginaryQuaternions) (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1)
    (h1 : ‖A1‖ ≤ a) (h2 : ‖A2‖ ≤ a) (h3 : ‖A3‖ ≤ a) (h4 : ‖A4‖ ≤ a) :
    ‖A1 + A2 - A3 - A4‖ ≤ distOne (expUnit A1 * expUnit A2 * (expUnit A3)⁻¹ * (expUnit A4)⁻¹) + 28 * a ^ 2 := by
  have second : ∀ A : imaginaryQuaternions, ‖A‖ ≤ a →
      ‖((expUnit A : UnitQuaternion) : ℍ[ℝ]) - 1 - (A : ℍ[ℝ])‖ ≤ a ^ 2 := fun A hA =>
    (expUnit_sub_one_sub_le A (hA.trans ha)).trans (pow_le_pow_left₀ (norm_nonneg _) hA 2)
  have hn3 : ‖-A3‖ ≤ a := by rwa [norm_neg]
  have hn4 : ‖-A4‖ ≤ a := by rwa [norm_neg]
  have key := prod_four_sub_one_sub_le (expUnit A1 : UnitQuaternion) (expUnit A2 : UnitQuaternion)
    (expUnit (-A3) : UnitQuaternion) (expUnit (-A4) : UnitQuaternion)
    (A1 : ℍ[ℝ]) (A2 : ℍ[ℝ]) ((-A3 : imaginaryQuaternions) : ℍ[ℝ]) ((-A4 : imaginaryQuaternions) : ℍ[ℝ]) a ha0 ha
    (norm_coe_unit _) (norm_coe_unit _) (norm_coe_unit _) (second _ h1) (second _ h2) (second _ hn3)
    (second _ hn4) h1 h2 hn3 hn4
  have hS : ‖A1 + A2 - A3 - A4‖ = ‖(A1 : ℍ[ℝ]) + (A2 : ℍ[ℝ]) + ((-A3 : imaginaryQuaternions) : ℍ[ℝ]) +
      ((-A4 : imaginaryQuaternions) : ℍ[ℝ])‖ := by
    have : ((A1 + A2 - A3 - A4 : imaginaryQuaternions) : ℍ[ℝ]) =
        (A1 : ℍ[ℝ]) + (A2 : ℍ[ℝ]) + ((-A3 : imaginaryQuaternions) : ℍ[ℝ]) +
          ((-A4 : imaginaryQuaternions) : ℍ[ℝ]) := by
      push_cast
      abel
    rw [← this]
    rfl
  have hP : distOne (expUnit A1 * expUnit A2 * (expUnit A3)⁻¹ * (expUnit A4)⁻¹) =
      ‖((expUnit A1 : UnitQuaternion) : ℍ[ℝ]) * (expUnit A2 : UnitQuaternion) *
        (expUnit (-A3) : UnitQuaternion) * (expUnit (-A4) : UnitQuaternion) - 1‖ := by
    rw [expUnit_inv, expUnit_inv]
    rfl
  rw [hS, hP]
  set P := ((expUnit A1 : UnitQuaternion) : ℍ[ℝ]) * (expUnit A2 : UnitQuaternion) *
    (expUnit (-A3) : UnitQuaternion) * (expUnit (-A4) : UnitQuaternion)
  set Y := (A1 : ℍ[ℝ]) + (A2 : ℍ[ℝ]) + ((-A3 : imaginaryQuaternions) : ℍ[ℝ]) +
    ((-A4 : imaginaryQuaternions) : ℍ[ℝ])
  have e : Y = (P - 1) - (P - 1 - Y) := by abel
  calc ‖Y‖ = ‖(P - 1) - (P - 1 - Y)‖ := by rw [← e]
    _ ≤ ‖P - 1‖ + ‖P - 1 - Y‖ := norm_sub_le _ _
    _ ≤ _ := by linarith
variable {n : ℕ} [NeZero n]
private theorem siteOfInt_add_int (h h' : IntPoint) :
    (siteOfInt (h + h') : TorusSite n) = siteOfInt h + siteOfInt h' := by apply _root_.YangMills.Construction.TorusFields.siteOfInt_add <;> assumption
private theorem unitStep_eq_siteOfInt (i : Fin 4) : unitStep n i = siteOfInt (basisVec i) := by apply _root_.YangMills.Construction.TorusLumps.unitStep_eq_siteOfInt <;> assumption
private def offsetFrom (o z : TorusSite n) : IntPoint := fun i => (z i - o i).valMinAbs
private theorem add_siteOfInt_offsetFrom (o z : TorusSite n) : o + siteOfInt (offsetFrom o z) = z := by apply _root_.YangMills.DeltaSharedProofs.p500399 <;> assumption
private theorem offsetFrom_add_siteOfInt (o : TorusSite n) (B : ℕ) (h : IntPoint) (hb : InCube B h)
    (hn : 2 * B < n) : offsetFrom o (o + siteOfInt h) = h := by
  funext k
  simp only [offsetFrom, siteOfInt, Pi.add_apply, add_sub_cancel_left]
  rw [ZMod.valMinAbs_spec]
  have h1 := abs_le.mp (hb k)
  refine ⟨rfl, ?_⟩
  constructor <;> omega
private theorem offsetFrom_self (o : TorusSite n) : offsetFrom o o = 0 := by
  funext k
  simp [offsetFrom]
private theorem offsetFrom_mem_cube (o z : TorusSite n) (R : ℕ) (hz : z ∈ supBall o (2 * R)) :
    InCube (2 * R) (offsetFrom o z) := by
  simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  have h1 : supDist z o ≤ 2 * R := by exact_mod_cast hz
  intro k
  have h2 : ((z k - o k).valMinAbs).natAbs ≤ supDist z o :=
    Finset.le_sup (f := fun i => ((z i - o i).valMinAbs).natAbs) (Finset.mem_univ k)
  have h3 := h2.trans h1
  simp only [offsetFrom]
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h3
private theorem add_siteOfInt_mem_supBall (o : TorusSite n) (R : ℕ) (h : IntPoint) (hb : InCube (2 * R) h)
    (hn : 2 * (2 * R) < n) : o + siteOfInt h ∈ supBall o (2 * R) := by
  simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : supDist (o + siteOfInt h) o ≤ 2 * R := by
    refine Finset.sup_le fun k _ => ?_
    have h2 : offsetFrom o (o + siteOfInt h) k = h k := congrFun (offsetFrom_add_siteOfInt o _ h hb hn) k
    have h3 := hb k
    simp only [offsetFrom] at h2
    rw [h2]
    rw [Int.abs_eq_natAbs] at h3
    exact_mod_cast h3
  exact_mod_cast h1
private def fieldIn (o : TorusSite n) (V : TorusField n) : IntPoint → Fin 4 → UnitQuaternion :=
  fun h i => V (o + siteOfInt h) i
private def axialGaugeAbout (o : TorusSite n) (V : TorusField n) (z : TorusSite n) : UnitQuaternion :=
  axialGaugeInt (fieldIn o V) (offsetFrom o z)
private def axialLogAbout (o : TorusSite n) (V : TorusField n) (b : TorusBond n) : imaginaryQuaternions :=
  logUnit (gaugeTransform (axialGaugeAbout o V) V b.1 b.2)
private theorem offsetFrom_add_unitStep (o z : TorusSite n) (B : ℕ) (i : Fin 4) (hb : InCube B (offsetFrom o z))
    (hn : 2 * (B + 1) < n) : offsetFrom o (z + unitStep n i) = offsetFrom o z + basisVec i := by
  have h1 : z + unitStep n i = o + siteOfInt (offsetFrom o z + basisVec i) := by
    rw [siteOfInt_add_int, ← add_assoc, add_siteOfInt_offsetFrom, unitStep_eq_siteOfInt]
  rw [h1]
  refine offsetFrom_add_siteOfInt o (B + 1) _ (fun k => ?_) hn
  have h2 := abs_le.mp (hb k)
  have h3 : basisVec i k = 0 ∨ basisVec i k = 1 := by
    by_cases hk : k = i
    · subst hk
      simp [basisVec]
    · simp [basisVec, hk]
  have h4 : (offsetFrom o z + basisVec i) k = offsetFrom o z k + basisVec i k := rfl
  rw [h4, abs_le]
  push_cast
  rcases h3 with h3 | h3 <;> rw [h3] <;> constructor <;> omega
private theorem gaugeTransform_axialGaugeAbout (o : TorusSite n) (V : TorusField n) (B : ℕ) (hn : 2 * (B + 1) < n)
    (z : TorusSite n) (i : Fin 4) (hz : InCube B (offsetFrom o z)) :
    gaugeTransform (axialGaugeAbout o V) V z i = axialGauged (fieldIn o V) (offsetFrom o z) i := by
  simp only [gaugeTransform, axialGaugeAbout, axialGauged, offsetFrom_add_unitStep o z B i hz hn]
  congr 2
  simp only [fieldIn, add_siteOfInt_offsetFrom]
private theorem holonomy_add_siteOfInt (o : TorusSite n) (V : TorusField n) (h : IntPoint) (i j : Fin 4) :
    holonomy V (o + siteOfInt h) i j = holonomyInt (fieldIn o V) h i j := by
  simp only [holonomy, holonomyInt, fieldIn, siteOfInt_add_int, unitStep_eq_siteOfInt, add_assoc]
private theorem curvature_gaugeTransform (g : TorusSite n → UnitQuaternion) (W : TorusField n) (x : TorusSite n)
    (i j : Fin 4) : curvature (gaugeTransform g W) x i j = curvature W x i j := by
  have h : holonomy (gaugeTransform g W) x i j = g x * holonomy W x i j * (g x)⁻¹ :=
    holonomy_conj g W (unitStep n) x i j
  have h2 := distOne_conj (g x) (holonomy W x i j)
  rw [← h] at h2
  exact h2
abbrev _root_.YangMills.SharedProofs.p70158 := @curvature_gaugeTransform
private theorem bonds_of_mem_plaquettesIn (S : Finset (TorusSite n)) (p : TorusPlaquette n)
    (hp : p ∈ plaquettesIn S) :
    (p.1, p.2.1) ∈ bondsWithin S ∧ (p.1 + unitStep n p.2.1, p.2.2) ∈ bondsWithin S ∧
      (p.1 + unitStep n p.2.2, p.2.1) ∈ bondsWithin S ∧ (p.1, p.2.2) ∈ bondsWithin S := by apply _root_.YangMills.SharedProofs.p50589 <;> assumption
open Classical in
private theorem card_supBall_le (o : TorusSite n) (R : ℕ) : (supBall o (2 * R)).card ≤ (4 * R + 1) ^ 4 := by
  have hsub : supBall o (2 * R) ⊆
      (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(2 * R : ℤ)) (2 * R)).image
        (fun h => o + siteOfInt h) := by
    intro z hz
    refine Finset.mem_image.mpr ⟨offsetFrom o z, ?_, add_siteOfInt_offsetFrom o z⟩
    rw [Fintype.mem_piFinset]
    intro k
    have h1 := abs_le.mp (offsetFrom_mem_cube o z R hz k)
    rw [Finset.mem_Icc]
    push_cast at h1
    exact h1
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  have h2 : (Finset.Icc (-(2 * R : ℤ)) (2 * R)).card = 4 * R + 1 := by
    rw [Int.card_Icc]
    omega
  rw [Fintype.card_piFinset]
  simp only [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact le_rfl
private theorem card_plaquettesIn_le (S : Finset (TorusSite n)) : (plaquettesIn S).card ≤ 6 * S.card := by
  classical
  have hsub : plaquettesIn S ⊆ S ×ˢ (Finset.univ.filter fun q : Fin 4 × Fin 4 => q.1 < q.2) := by
    intro p hp
    simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and, plaquetteVertices, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hp
    exact Finset.mem_product.mpr ⟨hp.2.1, by simpa using hp.1⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_product]
  have h6 : (Finset.univ.filter fun q : Fin 4 × Fin 4 => q.1 < q.2).card = 6 := by decide
  rw [h6, mul_comm]
private theorem card_bondsWithin_le (S : Finset (TorusSite n)) : (bondsWithin S).card ≤ 4 * S.card := by
  classical
  have hsub : bondsWithin S ⊆ S ×ˢ (Finset.univ : Finset (Fin 4)) := by
    intro b hb
    simp only [bondsWithin, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact Finset.mem_product.mpr ⟨hb.1, Finset.mem_univ _⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]
abbrev _root_.YangMills.SharedProofs.p64206 := @card_bondsWithin_le
private theorem eventually_boxRadius_bounds (κ₀ : ℝ) (h1 : 1 / 27 ≤ κ₀) (h2 : κ₀ ≤ 1 / 21) :
    ∃ xs : ℝ, ∀ x, xs ≤ x → 5 ≤ boxRadius κ₀ x ∧ 0 ≤ boxScale x ∧
      1372 * (boxRadius κ₀ x : ℝ) ^ 2 * boxScale x ≤ 1 := by
  have E1 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := Filter.eventually_ge_atTop 1
  have E2 : ∀ᶠ x : ℝ in Filter.atTop, (5 : ℝ) ≤ x ^ (1 / 27 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop 5
  have E3 : ∀ᶠ x : ℝ in Filter.atTop, (60000 : ℝ) ≤ x ^ (17 / 84 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop 60000
  obtain ⟨xs, hxs⟩ := Filter.eventually_atTop.mp (E1.and (E2.and E3))
  refine ⟨xs, fun x hx => ?_⟩
  obtain ⟨x1, x2, x3⟩ := hxs x hx
  have xpos : 0 < x := by linarith
  have y5 : 5 ≤ x ^ κ₀ := x2.trans (Real.rpow_le_rpow_of_exponent_le x1 h1)
  have yle : x ^ κ₀ ≤ x ^ (1 / 21 : ℝ) := Real.rpow_le_rpow_of_exponent_le x1 h2
  have Rge : x ^ κ₀ ≤ (boxRadius κ₀ x : ℝ) := Nat.le_ceil _
  have Rle : (boxRadius κ₀ x : ℝ) ≤ 2 * x ^ (1 / 21 : ℝ) := by
    have h3 := Nat.ceil_lt_add_one (show 0 ≤ x ^ κ₀ by linarith)
    simp only [boxRadius]
    linarith
  have R5 : 5 ≤ boxRadius κ₀ x := by
    have h3 : (5 : ℝ) ≤ (boxRadius κ₀ x : ℝ) := y5.trans Rge
    exact_mod_cast h3
  have lg0 : 0 ≤ Real.log x := Real.log_nonneg x1
  have apos : 0 < x ^ (2 / 21 : ℝ) := Real.rpow_pos_of_pos xpos _
  have bpos : 0 < x ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos xpos _
  have cpos : 0 < x ^ (17 / 84 : ℝ) := Real.rpow_pos_of_pos xpos _
  have δ0 : 0 ≤ boxScale x := by
    unfold boxScale
    positivity
  refine ⟨R5, δ0, ?_⟩
  have lg : Real.log x ≤ x ^ (17 / 84 : ℝ) / (17 / 84) := Real.log_le_rpow_div xpos.le (by norm_num)
  have hR2 : (boxRadius κ₀ x : ℝ) ^ 2 ≤ 4 * x ^ (2 / 21 : ℝ) := by
    have h3 : (x ^ (1 / 21 : ℝ)) ^ 2 = x ^ (2 / 21 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul xpos.le]
      norm_num
    have h4 := pow_le_pow_left₀ (Nat.cast_nonneg _) Rle 2
    rw [mul_pow, h3] at h4
    linarith
  have hδ : boxScale x ≤ 2 * x ^ (-(1 / 2) : ℝ) * (x ^ (17 / 84 : ℝ) / (17 / 84)) := by
    unfold boxScale
    exact mul_le_mul_of_nonneg_left lg (by positivity)
  have habc : x ^ (2 / 21 : ℝ) * x ^ (-(1 / 2) : ℝ) * x ^ (17 / 84 : ℝ) * x ^ (17 / 84 : ℝ) = 1 := by
    rw [← Real.rpow_add xpos, ← Real.rpow_add xpos, ← Real.rpow_add xpos]
    norm_num
  have hq : x ^ (2 / 21 : ℝ) * x ^ (-(1 / 2) : ℝ) * x ^ (17 / 84 : ℝ) * 60000 ≤ 1 := by
    calc _ ≤ x ^ (2 / 21 : ℝ) * x ^ (-(1 / 2) : ℝ) * x ^ (17 / 84 : ℝ) * x ^ (17 / 84 : ℝ) :=
          mul_le_mul_of_nonneg_left x3 (by positivity)
      _ = 1 := habc
  calc 1372 * (boxRadius κ₀ x : ℝ) ^ 2 * boxScale x
      ≤ 1372 * (4 * x ^ (2 / 21 : ℝ)) * (2 * x ^ (-(1 / 2) : ℝ) * (x ^ (17 / 84 : ℝ) / (17 / 84))) := by
        gcongr
    _ = 921984 / 17 * (x ^ (2 / 21 : ℝ) * x ^ (-(1 / 2) : ℝ) * x ^ (17 / 84 : ℝ)) := by ring
    _ ≤ 1 := by nlinarith [mul_pos (mul_pos apos bpos) cpos]
private theorem measurable_lineTransport {X : Type} [MeasurableSpace X] (F : X → ℤ → UnitQuaternion)
    (hF : ∀ s, Measurable fun v => F v s) (t : ℤ) : Measurable fun v => lineTransport (F v) t := by
  have up : ∀ m : ℕ, Measurable fun v => prodUp (F v) m := by
    intro m
    induction m with
    | zero => exact measurable_const
    | succ m ih => exact ih.mul (hF _)
  have down : ∀ m : ℕ, Measurable fun v => prodDown (F v) m := by
    intro m
    induction m with
    | zero => exact measurable_const
    | succ m ih => exact ih.mul (hF _).inv
  by_cases ht : 0 ≤ t
  · simp only [lineTransport, ht, if_true]
    exact up _
  · simp only [lineTransport, ht, if_false]
    exact down _
private theorem measurable_axialGaugeAbout (o z : TorusSite n) :
    Measurable fun V : TorusField n => axialGaugeAbout o V z := by
  have ev' : ∀ (y : TorusSite n) (i : Fin 4), Measurable fun V : TorusField n => V y i := fun y i =>
    (measurable_pi_apply i).comp (measurable_pi_apply y)
  have st : ∀ (j : Fin 4) (h : IntPoint), Measurable fun V : TorusField n => axialSegment (fieldIn o V) j h :=
    fun j h => measurable_lineTransport (fun V t => fieldIn o V (Function.update (truncate j h) j t) j)
      (fun _ => ev' _ _) _
  simp only [axialGaugeAbout, axialGaugeInt]
  exact (((st 0 _).mul (st 1 _)).mul (st 2 _)).mul (st 3 _)
private theorem measurable_logUnit : Measurable logUnit := by
  have him : Continuous fun a : UnitQuaternion => imagPart (a : ℍ[ℝ]) :=
    Continuous.subtype_mk (Quaternion.continuous_im.comp continuous_subtype_val) _
  have hn : Continuous fun a : UnitQuaternion => ‖(a : ℍ[ℝ]).im‖ :=
    (Quaternion.continuous_im.comp continuous_subtype_val).norm
  have hc : Measurable fun a : UnitQuaternion => Real.arcsin ‖(a : ℍ[ℝ]).im‖ / ‖(a : ℍ[ℝ]).im‖ :=
    (Real.continuous_arcsin.comp hn).measurable.div hn.measurable
  exact hc.smul him.measurable
private theorem measurable_axialLogAbout (o : TorusSite n) (b : TorusBond n) :
    Measurable fun V : TorusField n => axialLogAbout o V b := by
  refine measurable_logUnit.comp ?_
  simp only [gaugeTransform]
  exact ((measurable_axialGaugeAbout o b.1).mul
    ((measurable_pi_apply b.2).comp (measurable_pi_apply b.1))).mul (measurable_axialGaugeAbout o _).inv
private theorem axialGauge_of_cold (o : TorusSite n) (R : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hR : 5 ≤ R) (hn : 16 * R < n)
    (hs : 1372 * (R : ℝ) ^ 2 * δ ≤ 1) (V : TorusField n)
    (hV : ∀ p ∈ plaquettesIn (supBall o (2 * R)), curvature V p.1 p.2.1 p.2.2 ≤ δ) :
    (∀ b ∈ bondsWithin (supBall o (2 * R)),
      gaugeTransform (axialGaugeAbout o V) V b.1 b.2 = expUnit (axialLogAbout o V b)) ∧
      IsAxialSmall o R δ (axialLogAbout o V) := by
  have hn1 : 2 * (2 * R + 1) < n := by omega
  have hn0 : 2 * (2 * R) < n := by omega
  have hR1 : (5 : ℝ) ≤ R := by exact_mod_cast hR
  have hP : ∀ i j : Fin 4, i < j → ∀ x : IntPoint, InCube (2 * R) x → InCube (2 * R) (x + basisVec i) →
      InCube (2 * R) (x + basisVec j) → InCube (2 * R) (x + basisVec i + basisVec j) →
      distOne (holonomyInt (fieldIn o V) x i j) ≤ δ := by
    intro i j hij x b0 b1 b2 b3
    have hp : ((o + siteOfInt x, i, j) : TorusPlaquette n) ∈ plaquettesIn (supBall o (2 * R)) := by
      simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and, plaquetteVertices, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨hij, add_siteOfInt_mem_supBall o R x b0 hn0, ?_, ?_, ?_⟩
      · have h1 := add_siteOfInt_mem_supBall o R _ b1 hn0
        rwa [siteOfInt_add_int, ← unitStep_eq_siteOfInt, ← add_assoc] at h1
      · have h1 := add_siteOfInt_mem_supBall o R _ b2 hn0
        rwa [siteOfInt_add_int, ← unitStep_eq_siteOfInt, ← add_assoc] at h1
      · have h1 := add_siteOfInt_mem_supBall o R _ b3 hn0
        rwa [siteOfInt_add_int, siteOfInt_add_int, ← unitStep_eq_siteOfInt, ← unitStep_eq_siteOfInt,
          ← add_assoc, ← add_assoc] at h1
    have h2 := hV _ hp
    rw [← holonomy_add_siteOfInt]
    exact h2
  have hW : ∀ b ∈ bondsWithin (supBall o (2 * R)),
      distOne (gaugeTransform (axialGaugeAbout o V) V b.1 b.2) ≤ 6 * R * δ := by
    intro b hb
    simp only [bondsWithin, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have b0 := offsetFrom_mem_cube o b.1 R hb.1
    have b1 := offsetFrom_mem_cube o _ R hb.2
    rw [offsetFrom_add_unitStep o b.1 (2 * R) b.2 b0 hn1] at b1
    rw [gaugeTransform_axialGaugeAbout o V (2 * R) hn1 b.1 b.2 b0]
    have h1 := axialGauged_distOne_le (fieldIn o V) (2 * R) δ hδ hP b.2 _ b0 b1
    push_cast at h1
    linarith
  have hRδ : 1372 * ((R : ℝ) * δ) ≤ 1 := by
    have h1 : (R : ℝ) * δ ≤ (R : ℝ) ^ 2 * δ := by
      have : (R : ℝ) ≤ (R : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this hδ
    linarith
  have hlog : ∀ b ∈ bondsWithin (supBall o (2 * R)),
      0 < ((gaugeTransform (axialGaugeAbout o V) V b.1 b.2 : UnitQuaternion) : ℍ[ℝ]).re ∧
        ‖axialLogAbout o V b‖ ≤ 7 * R * δ := by
    intro b hb
    have h1 := hW b hb
    have h2 := logUnit_bound (gaugeTransform (axialGaugeAbout o V) V b.1 b.2) (by linarith)
    exact ⟨h2.1, h2.2.trans (by linarith)⟩
  have hexp : ∀ b ∈ bondsWithin (supBall o (2 * R)),
      gaugeTransform (axialGaugeAbout o V) V b.1 b.2 = expUnit (axialLogAbout o V b) := fun b hb =>
    (expUnit_logUnit _ (hlog b hb).1).symm
  have hcold : ∀ p ∈ plaquettesIn (supBall o (2 * R)),
      holonomy (exponentialField (axialLogAbout o V)) p.1 p.2.1 p.2.2 =
        holonomy (gaugeTransform (axialGaugeAbout o V) V) p.1 p.2.1 p.2.2 := by
    intro p hp
    obtain ⟨B1, B2, B3, B4⟩ := bonds_of_mem_plaquettesIn _ p hp
    simp only [holonomy, exponentialField]
    rw [← hexp _ B1, ← hexp _ B2, ← hexp _ B3, ← hexp _ B4]
  have hcurv : ∀ p ∈ plaquettesIn (supBall o (2 * R)),
      curvature (exponentialField (axialLogAbout o V)) p.1 p.2.1 p.2.2 ≤ δ := by
    intro p hp
    have h1 : curvature (exponentialField (axialLogAbout o V)) p.1 p.2.1 p.2.2 =
        curvature (gaugeTransform (axialGaugeAbout o V) V) p.1 p.2.1 p.2.2 := by
      simp only [curvature, hcold p hp]
    rw [h1, curvature_gaugeTransform]
    exact hV p hp
  have hcurl : ∀ p ∈ plaquettesIn (supBall o (2 * R)), ‖lieFormCurl (axialLogAbout o V) p‖ ≤ 2 * δ := by
    intro p hp
    obtain ⟨B1, B2, B3, B4⟩ := bonds_of_mem_plaquettesIn _ p hp
    have h1 := curl_le_distOne_holonomy _ _ _ _ (7 * R * δ) (by positivity) (by linarith)
      (hlog _ B1).2 (hlog _ B2).2 (hlog _ B3).2 (hlog _ B4).2
    have h2 : distOne (expUnit (axialLogAbout o V (p.1, p.2.1)) *
        expUnit (axialLogAbout o V (p.1 + unitStep n p.2.1, p.2.2)) *
        (expUnit (axialLogAbout o V (p.1 + unitStep n p.2.2, p.2.1)))⁻¹ *
        (expUnit (axialLogAbout o V (p.1, p.2.2)))⁻¹) ≤ δ :=
      hcurv p hp
    have h3 : 28 * (7 * (R : ℝ) * δ) ^ 2 ≤ δ := by
      have e : 28 * (7 * (R : ℝ) * δ) ^ 2 = (1372 * (R : ℝ) ^ 2 * δ) * δ := by ring
      rw [e]
      nlinarith
    have h4 : ‖lieFormCurl (axialLogAbout o V) p‖ ≤ _ := h1
    linarith
  have cardS : ((supBall o (2 * R)).card : ℝ) ≤ (21 / 5) ^ 4 * (R : ℝ) ^ 4 := by
    have h1 : ((supBall o (2 * R)).card : ℝ) ≤ ((4 * R + 1 : ℕ) : ℝ) ^ 4 := by
      exact_mod_cast card_supBall_le o R
    have h2 : ((4 * R + 1 : ℕ) : ℝ) ≤ 21 / 5 * R := by
      push_cast
      linarith
    have h3 := pow_le_pow_left₀ (Nat.cast_nonneg _) h2 4
    rw [mul_pow] at h3
    linarith
  have hpos : 0 ≤ (R : ℝ) ^ 4 * δ ^ 2 := by positivity
  refine ⟨hexp, hcurv, fun b hb => (hlog b hb).2, ?_, ?_⟩
  · have h1 := Finset.sum_le_card_nsmul (plaquettesIn (supBall o (2 * R)))
      (fun p => ‖lieFormCurl (axialLogAbout o V) p‖ ^ 2)
      ((2 * δ) ^ 2) (fun p hp => pow_le_pow_left₀ (norm_nonneg _) (hcurl p hp) 2)
    rw [nsmul_eq_mul] at h1
    have h2 : ((plaquettesIn (supBall o (2 * R))).card : ℝ) ≤ 6 * (supBall o (2 * R)).card := by
      exact_mod_cast card_plaquettesIn_le _
    have h3 : ((plaquettesIn (supBall o (2 * R))).card : ℝ) ≤ 6 * ((21 / 5) ^ 4 * (R : ℝ) ^ 4) := by linarith
    have h4 := mul_le_mul_of_nonneg_right h3 (sq_nonneg (2 * δ))
    unfold curlNormSq
    calc _ ≤ _ := h1
      _ ≤ _ := h4
      _ = (6 * 4 * (21 / 5) ^ 4) * ((R : ℝ) ^ 4 * δ ^ 2) := by ring
      _ ≤ 2 ^ 13 * ((R : ℝ) ^ 4 * δ ^ 2) := mul_le_mul_of_nonneg_right (by norm_num) hpos
      _ = _ := by ring
  · have h1 := Finset.sum_le_card_nsmul (bondsWithin (supBall o (2 * R))) (fun b => ‖axialLogAbout o V b‖ ^ 2)
      ((7 * R * δ) ^ 2) (fun b hb => pow_le_pow_left₀ (norm_nonneg _) (hlog b hb).2 2)
    rw [nsmul_eq_mul] at h1
    have h2 : ((bondsWithin (supBall o (2 * R))).card : ℝ) ≤ 4 * (supBall o (2 * R)).card := by
      exact_mod_cast card_bondsWithin_le _
    have h3 : ((bondsWithin (supBall o (2 * R))).card : ℝ) ≤ 4 * ((21 / 5) ^ 4 * (R : ℝ) ^ 4) := by linarith
    have h4 := mul_le_mul_of_nonneg_right h3 (sq_nonneg (7 * (R : ℝ) * δ))
    have hpos6 : 0 ≤ (R : ℝ) ^ 6 * δ ^ 2 := by positivity
    unfold bondNormSq
    calc _ ≤ _ := h1
      _ ≤ _ := h4
      _ = (4 * 49 * (21 / 5) ^ 4) * ((R : ℝ) ^ 6 * δ ^ 2) := by ring
      _ ≤ 2 ^ 16 * ((R : ℝ) ^ 6 * δ ^ 2) := mul_le_mul_of_nonneg_right (by norm_num) hpos6
      _ = _ := by ring
theorem coldAxialGauge : coldAxialGaugeStatement := by
  intro κ₀ h1 h2
  obtain ⟨xs, hxs⟩ := eventually_boxRadius_bounds κ₀ h1 h2
  refine ⟨xs, ?_⟩
  intro x R n _ o hx hR hn
  obtain ⟨hR5, hδ, hsm⟩ := hxs x hx
  rw [← hR] at hR5 hsm
  refine ⟨fun V => axialGaugeAbout o V, fun V => axialLogAbout o V, ?_⟩
  intro cold
  refine ⟨measurable_pi_lambda _ fun z => (measurable_axialGaugeAbout o z).comp measurable_subtype_coe,
    measurable_pi_lambda _ fun b => (measurable_axialLogAbout o b).comp measurable_subtype_coe, fun V hV => ?_⟩
  obtain ⟨c1, c2⟩ := axialGauge_of_cold o R _ hδ hR5 hn hsm V hV
  refine ⟨?_, c1, c2⟩
  simp [axialGaugeAbout, offsetFrom_self, axialGaugeInt_zero]
end YangMills.Construction.BoxGaussian
end
