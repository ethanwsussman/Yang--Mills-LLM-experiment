import YangMills.Construction.ColdChainAtEveryLevel.HolonomiesOnTheHullOfABond
import YangMills.Construction.ColdChainAtEveryLevel.MeanOfTheContoursOfABond
import YangMills.Construction.ColdChainAtEveryLevel.OneStepOfTheCoordinatesProof
import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheTerms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace BondAngle
open YangMills.Construction.LatticePaths
open YangMills.Construction.LatticeFractionalIntegration
variable {F : BlockFrame} {j : ℕ}
theorem quaternion_re_finset_sum {ι : Type} (s : Finset ι) (f : ι → ℍ[ℝ]) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by apply _root_.YangMills.Construction.BlockAverages.CoordinateStep.re_finset_sum <;> assumption
theorem quaternion_re_real_smul (r : ℝ) (q : ℍ[ℝ]) : (r • q).re = r * q.re := by simp
theorem adjacentBound_of_mem_twoBlockHull (hL : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {f : F.Site j → Fin 4 → ℝ} {c : F.Site (j + 1) × Fin 4} {t : ℝ}
    (hb : BoundedOnAdjacentBlocks f c t) {a : Lattice4} (ha : a ∈ FlatPairing.twoBlockHull F.blockSide c.2) {k : Fin 4}
    (hk : a + basisVector k ∈ FlatPairing.twoBlockHull F.blockSide c.2) :
    f (refineSite c.1 + siteOfCoords j a) k ≤ t := by apply _root_.YangMills.Construction.BondHull.le_of_mem_twoBlockHull <;> assumption
theorem inv_mul_inv_inv_eq_conj (x r : UnitQuaternion) : x⁻¹ * (r⁻¹)⁻¹ = r⁻¹ * (x * r⁻¹)⁻¹ * (r⁻¹)⁻¹ := by group
theorem norm_pathHolonomy_mul_inv_sub_one_le (X R : F.GaugeField j) (x : F.Site j) {H : Lattice4 → Prop} {t : ℝ}
    (hg : ∀ a, H a → ∀ k, H (a + basisVector k) →
      ‖((X (x + siteOfCoords j a) k * (R (x + siteOfCoords j a) k)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ t)
    (l : List PathStep) : ∀ v : Lattice4, AllAlong H v l →
      ‖((pathHolonomy X (x + siteOfCoords j v) l * (pathHolonomy R (x + siteOfCoords j v) l)⁻¹ : UnitQuaternion) :
        ℍ[ℝ]) - 1‖ ≤ l.length * t := by
  induction l with
  | nil =>
    intro v _
    simp [pathHolonomy]
  | cons st r ih =>
    intro v hp
    obtain ⟨hv, hr⟩ := hp
    have hnext : H (v + FlatPairing.stepDisplacement st) := allAlong_head hr
    have hstep : x + siteOfCoords j v + stepDisplacement j st = x + siteOfCoords j (v + FlatPairing.stepDisplacement st) := by
      rcases st with ⟨k, b⟩
      cases b <;> simp [stepDisplacement, FlatPairing.stepDisplacement, unitStep_eq, siteOfCoords_add, siteOfCoords_neg, add_assoc]
    have hrec := ih _ hr
    have e : pathHolonomy X (x + siteOfCoords j v) (st :: r) * (pathHolonomy R (x + siteOfCoords j v) (st :: r))⁻¹ =
        (linkValue X (x + siteOfCoords j v) st * (linkValue R (x + siteOfCoords j v) st)⁻¹) *
          (linkValue R (x + siteOfCoords j v) st *
          (pathHolonomy X (x + siteOfCoords j (v + FlatPairing.stepDisplacement st)) r *
          (pathHolonomy R (x + siteOfCoords j (v + FlatPairing.stepDisplacement st)) r)⁻¹) *
          (linkValue R (x + siteOfCoords j v) st)⁻¹) := by
      simp only [pathHolonomy, hstep]
      group
    have h1 : ‖((linkValue X (x + siteOfCoords j v) st * (linkValue R (x + siteOfCoords j v) st)⁻¹ : UnitQuaternion) :
        ℍ[ℝ]) - 1‖ ≤ t := by
      rcases st with ⟨k, b⟩
      cases b with
      | true =>
        have h := hg v hv k (by simpa [FlatPairing.stepDisplacement] using hnext)
        simpa [linkValue] using h
      | false =>
        have hn : H (v - basisVector k) := by simpa [FlatPairing.stepDisplacement, sub_eq_add_neg] using hnext
        have h := hg _ hn k (by simpa using hv)
        have e1 : x + siteOfCoords j (v - basisVector k) = x + siteOfCoords j v - unitStep j k := by
          rw [unitStep_eq, sub_eq_add_neg, siteOfCoords_add, siteOfCoords_neg]
          abel
        rw [e1] at h
        have eX : linkValue X (x + siteOfCoords j v) (k, false) = (X (x + siteOfCoords j v - unitStep j k) k)⁻¹ := by
          simp [linkValue]
        have eR : linkValue R (x + siteOfCoords j v) (k, false) = (R (x + siteOfCoords j v - unitStep j k) k)⁻¹ := by
          simp [linkValue]
        rw [eX, eR, inv_mul_inv_inv_eq_conj, norm_coe_conj_sub_one, norm_coe_inv_sub_one]
        exact h
    rw [e]
    refine (norm_coe_mul_sub_one_le _ _).trans ?_
    rw [norm_coe_conj_sub_one]
    have hlen : ((st :: r).length : ℝ) * t = t + (r.length : ℝ) * t := by
      simp
      ring
    rw [hlen]
    exact add_le_add h1 hrec
theorem norm_bondContour_holonomy_gap_le (hL : Odd F.blockSide) (X R : F.GaugeField j)
    {c : F.Site (j + 1) × Fin 4} {t : ℝ} (ht : 0 ≤ t)
    (hg : ∀ a ∈ FlatPairing.twoBlockHull F.blockSide c.2, ∀ k,
      a + basisVector k ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
      ‖((X (refineSite c.1 + siteOfCoords j a) k * (R (refineSite c.1 + siteOfCoords j a) k)⁻¹ : UnitQuaternion) :
        ℍ[ℝ]) - 1‖ ≤ t)
    {h : Lattice4} (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    ‖((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      5 * (F.blockSide : ℝ) * t := by
  have h1 := (bondContour_spec π c.2 hL.pos hh).1
  have h2 := norm_pathHolonomy_mul_inv_sub_one_le X R (refineSite c.1)
    (H := fun v => v ∈ FlatPairing.twoBlockHull F.blockSide c.2)
    (fun a ha k hk => hg a ha k hk) _ 0 h1
  have e : refineSite c.1 + siteOfCoords j (0 : Lattice4) = refineSite c.1 := by rw [siteOfCoords_zero, add_zero]
  rw [e] at h2
  refine h2.trans ?_
  have := length_bondContour_le π c.2 hL.pos hh
  have h3 : ((bondContour F.blockSide h π c.2).length : ℝ) ≤ 5 * (F.blockSide : ℝ) := by exact_mod_cast this
  exact mul_le_mul_of_nonneg_right h3 ht
theorem contourAverage_norm_near_one (hL : Odd F.blockSide) (X : F.GaugeField j) (c : F.Site (j + 1) × Fin 4)
    (u : UnitQuaternion) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ h' ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h' π c.2) * u⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ δ) :
    0 ≤ 1 - ‖contourAverage X c‖ ∧ 1 - ‖contourAverage X c‖ ≤ δ ^ 2 / 2 := by
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have hcount : (∑ _h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ)) =
      24 * (F.blockSide : ℝ) ^ 4 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, card_centredCube hL,
      nsmul_eq_mul, mul_one]
    simp [Nat.factorial]
    ring
  constructor
  · have : ‖contourAverage X c‖ ≤ 1 := by
      unfold contourAverage
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      have h1 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
          ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])‖ ≤
            24 * (F.blockSide : ℝ) ^ 4 := by
        rw [← hcount]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h' _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => ?_)
        rw [norm_coe_unitQuaternion]
      calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _ ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) * (24 * (F.blockSide : ℝ) ^ 4) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 1 := by field_simp
    linarith
  · have e1 : ‖contourAverage X c‖ = ‖contourAverage X c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ := by
      rw [norm_mul, norm_coe_unitQuaternion, mul_one]
    have e2 : (contourAverage X c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])).re =
        (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ h' ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
          ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h' π c.2) * u⁻¹ : UnitQuaternion) : ℍ[ℝ]).re := by
      unfold contourAverage
      rw [smul_mul_assoc, Finset.sum_mul]
      simp only [Finset.sum_mul]
      rw [quaternion_re_real_smul, quaternion_re_finset_sum]
      simp only [quaternion_re_finset_sum]
      rfl
    have e3 : ∀ h' ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4), 1 - δ ^ 2 / 2 ≤
        ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h' π c.2) * u⁻¹ : UnitQuaternion) : ℍ[ℝ]).re := by
      intro h' hh π
      have h1 := h h' hh π
      have h2 := norm_coe_sub_one_sq (pathHolonomy X (refineSite c.1) (bondContour F.blockSide h' π c.2) * u⁻¹)
      have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      linarith
    have e4 : (1 - δ ^ 2 / 2) * (24 * (F.blockSide : ℝ) ^ 4) ≤
        ∑ h' ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
          ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h' π c.2) * u⁻¹ : UnitQuaternion) : ℍ[ℝ]).re := by
      rw [← hcount, Finset.mul_sum]
      refine Finset.sum_le_sum fun h' hh => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun π _ => ?_
      rw [mul_one]
      exact e3 h' hh π
    have e5 : 1 - δ ^ 2 / 2 ≤ (contourAverage X c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := by
      rw [e2]
      calc 1 - δ ^ 2 / 2 = 1 / (24 * (F.blockSide : ℝ) ^ 4) * ((1 - δ ^ 2 / 2) * (24 * (F.blockSide : ℝ) ^ 4)) := by
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left e4 (by positivity)
    have e6 := quaternion_re_le_norm (contourAverage X c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]))
    rw [← e1] at e6
    linarith
theorem norm_gaugedContourAverage (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion)
    (c : F.Site (j + 1) × Fin 4) : ‖gaugedContourAverage X k c‖ = ‖contourAverage X c‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.norm_gaugedContourAverage <;> assumption
theorem parallelAverage_sub (R : F.GaugeField j) (f g : F.Site j → Fin 4 → ℍ[ℝ]) (c : F.Site (j + 1) × Fin 4) :
    parallelAverage R f c - parallelAverage R g c = parallelAverage R (fun x i => f x i - g x i) c := by
  unfold parallelAverage
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [adjointAction_sub]
theorem norm_parallelAverage_le_mul (hL : Odd F.blockSide) (R : F.GaugeField j) {f : F.Site j → Fin 4 → ℍ[ℝ]}
    {c : F.Site (j + 1) × Fin 4} {d : ℝ}
    (h : ∀ h' ∈ centredCube F.blockSide, ∀ r ∈ Finset.range F.blockSide,
      ‖f (refineSite c.1 + siteOfCoords j h' + (r : ℤ) • unitStep j c.2) c.2‖ ≤ d) :
    ‖parallelAverage R f c‖ ≤ (F.blockSide : ℝ) * d := by apply _root_.YangMills.Construction.BlockAverages.CoordinateStep.norm_parallelAverage_le_blockSide_mul <;> assumption
theorem re_parallelAverage (R : F.GaugeField j) {f : F.Site j → Fin 4 → ℍ[ℝ]} (hf : ∀ x i, (f x i).re = 0)
    (c : F.Site (j + 1) × Fin 4) : (parallelAverage R f c).re = 0 := by apply _root_.YangMills.Construction.BlockAverages.CoordinateStep.re_parallelAverage_eq_zero <;> assumption
theorem norm_unitQuaternionLog_sub_le {E : UnitQuaternion} {Q Q' : ℍ[ℝ]} (hQ : Q.re = 0) {τ ε C1 d : ℝ}
    (hτ0 : 0 ≤ τ) (hε0 : 0 ≤ ε) (hC1 : 0 < C1)
    (m1 : ‖pureComponent (E : ℍ[ℝ]) - Q'‖ ≤ C1 * τ * (τ + ε))
    (m2 : ‖(E : ℍ[ℝ]) - 1‖ ≤ 4 * ‖Q'‖ + C1 * τ * (τ + ε))
    (hQQ : ‖Q - Q'‖ ≤ d) (hQn : ‖Q‖ ≤ τ) (hQ'n : ‖Q'‖ ≤ τ) (hτ : (9 + 4 * C1) * τ ≤ 1 / 2) (hε : ε ≤ 1) :
    ‖unitQuaternionLog E - Q‖ ≤ 2 * (C1 * τ * (τ + ε) + d + τ ^ 2) := by
  have hτ1 : τ ≤ 1 / 18 := by nlinarith
  have b0 : C1 * τ * (τ + ε) ≤ 2 * C1 * τ := by
    have : C1 * τ * (τ + ε) ≤ C1 * τ * 2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hx : ‖unitQuaternionLog E‖ ≤ 2 * (4 * τ + 2 * C1 * τ) := by
    refine (norm_unitQuaternionLog_le_two_mul E).trans ?_
    linarith
  have h1 := norm_sub_le_two_mul_pureComponent_exp (re_unitQuaternionLog E) hQ (by nlinarith)
  rw [exp_unitQuaternionLog] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have e : pureComponent (E : ℍ[ℝ]) - pureComponent (NormedSpace.exp Q) =
      (pureComponent (E : ℍ[ℝ]) - Q') - (Q - Q') - (pureComponent (NormedSpace.exp Q) - Q) := by abel
  rw [e]
  have h2 := norm_pureComponent_exp_sub_self_le hQ (by linarith)
  have h3 : ‖Q‖ ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hQn 2
  calc _ ≤ ‖pureComponent (E : ℍ[ℝ]) - Q'‖ + ‖Q - Q'‖ + ‖pureComponent (NormedSpace.exp Q) - Q‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ _ := by linarith
theorem angle_constant_bound {Lr t y C1 C0 : ℝ} (hLr : 1 ≤ Lr) (ht : 0 ≤ t) (hy : 0 ≤ y) (hC1 : 0 ≤ C1)
    (hC0 : 0 ≤ C0) :
    2 * (C1 * (Lr * t) * (Lr * t + C0 * y) + Lr * t ^ 2 + (Lr * t) ^ 2) ≤
      (2 * (C1 + 2) * Lr ^ 2 + 2 * C1 * Lr * C0 + 25 * Lr ^ 2 + C0 ^ 2 + 1) * (t ^ 2 + y * t) := by
  set P := 2 * (C1 + 2) * Lr ^ 2 + 2 * C1 * Lr * C0 + 25 * Lr ^ 2 + C0 ^ 2 + 1 with hP
  have hLL : Lr ≤ Lr ^ 2 := by nlinarith
  have q1 : 0 ≤ C1 * Lr ^ 2 := by positivity
  have q2 : 0 ≤ C1 * Lr * C0 := by positivity
  have h1 : (2 * C1 + 2) * Lr ^ 2 + 2 * Lr ≤ P := by rw [hP]; nlinarith
  have h2 : 2 * C1 * Lr * C0 ≤ P := by rw [hP]; nlinarith
  have t2 : 0 ≤ t ^ 2 := by positivity
  have yt : 0 ≤ y * t := by positivity
  calc 2 * (C1 * (Lr * t) * (Lr * t + C0 * y) + Lr * t ^ 2 + (Lr * t) ^ 2)
      = ((2 * C1 + 2) * Lr ^ 2 + 2 * Lr) * t ^ 2 + (2 * C1 * Lr * C0) * (y * t) := by ring
    _ ≤ P * t ^ 2 + P * (y * t) :=
        add_le_add (mul_le_mul_of_nonneg_right h1 t2) (mul_le_mul_of_nonneg_right h2 yt)
    _ = P * (t ^ 2 + y * t) := by ring
theorem size_constant_bound {Lr t w C1 C0 : ℝ} (hLr : 1 ≤ Lr) (ht : 0 ≤ t) (hw : 0 ≤ w) (hC1 : 0 ≤ C1)
    (hC0 : 0 ≤ C0) :
    25 * Lr ^ 2 * t ^ 2 + C0 ^ 2 * w ≤
      (2 * (C1 + 2) * Lr ^ 2 + 2 * C1 * Lr * C0 + 25 * Lr ^ 2 + C0 ^ 2 + 1) * (t ^ 2 + w) := by
  set P := 2 * (C1 + 2) * Lr ^ 2 + 2 * C1 * Lr * C0 + 25 * Lr ^ 2 + C0 ^ 2 + 1 with hP
  have q1 : 0 ≤ (C1 + 2) * Lr ^ 2 := by positivity
  have q2 : 0 ≤ C1 * Lr * C0 := by positivity
  have h1 : 25 * Lr ^ 2 ≤ P := by rw [hP]; nlinarith
  have h2 : C0 ^ 2 ≤ P := by rw [hP]; nlinarith
  have t2 : 0 ≤ t ^ 2 := by positivity
  calc 25 * Lr ^ 2 * t ^ 2 + C0 ^ 2 * w ≤ P * t ^ 2 + P * w :=
        add_le_add (mul_le_mul_of_nonneg_right h1 t2) (mul_le_mul_of_nonneg_right h2 hw)
    _ = P * (t ^ 2 + w) := by ring
end BondAngle
open BondAngle in
open YangMills.Construction.LatticePaths in
open YangMills.Construction.LatticeFractionalIntegration in
theorem bondAngleAndAverageNorm_holds (hB : referenceBoundsStatement)
    (hM : contourMeanFirstOrderStatement) : bondAngleAndAverageNormStatement := by
  obtain ⟨C0, c0, L1, hC0, hc0, hB⟩ := hB
  obtain ⟨C1, c1, hC1, hc1, hM⟩ := hM
  refine ⟨max L1 1, fun L hodd hL0 => ?_⟩
  have hL1 : L1 ≤ L := le_trans (le_max_left _ _) hL0
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hodd.pos
  have hLp : (0 : ℝ) < L := by linarith
  obtain ⟨c, hcp, hcc0, hcs, hct, hct'⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ c0 ∧ (C0 + 1) * c ≤ min c1 1 ∧ (L : ℝ) * c ≤ c1 ∧
      (9 + 4 * C1) * ((L : ℝ) * c) ≤ 1 / 2 := by
    have p1 : 0 < min c1 1 / (C0 + 1) := div_pos (lt_min hc1 one_pos) (by positivity)
    have p2 : 0 < c1 / L := by positivity
    have p3 : 0 < 1 / (2 * (9 + 4 * C1)) / L := by positivity
    refine ⟨min c0 (min (min c1 1 / (C0 + 1)) (min (c1 / L) (1 / (2 * (9 + 4 * C1)) / L))),
      lt_min hc0 (lt_min p1 (lt_min p2 p3)), min_le_left _ _, ?_, ?_, ?_⟩
    · have h : min c0 (min (min c1 1 / (C0 + 1)) (min (c1 / L) (1 / (2 * (9 + 4 * C1)) / L))) ≤
          min c1 1 / (C0 + 1) :=
        (min_le_right _ _).trans (min_le_left _ _)
      calc _ ≤ (C0 + 1) * (min c1 1 / (C0 + 1)) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = min c1 1 := by field_simp
    · have h : min c0 (min (min c1 1 / (C0 + 1)) (min (c1 / L) (1 / (2 * (9 + 4 * C1)) / L))) ≤ c1 / L :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
      calc _ ≤ (L : ℝ) * (c1 / L) := mul_le_mul_of_nonneg_left h hLp.le
        _ = c1 := by field_simp
    · have h : min c0 (min (min c1 1 / (C0 + 1)) (min (c1 / L) (1 / (2 * (9 + 4 * C1)) / L))) ≤
          1 / (2 * (9 + 4 * C1)) / L := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
      calc _ ≤ (9 + 4 * C1) * ((L : ℝ) * (1 / (2 * (9 + 4 * C1)) / L)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h hLp.le) (by positivity)
        _ = 1 / 2 := by field_simp
  refine ⟨2 * (C1 + 2) * (L : ℝ) ^ 2 + 2 * C1 * L * C0 + 25 * (L : ℝ) ^ 2 + C0 ^ 2 + 1, c, by positivity, hcp, ?_⟩
  intro F m S hFL hamb hm hreg s V hs0 hs hcold U j b hj hb t ht0 ht hbl
  subst hFL
  have hj' : j + 1 ≤ F.top := hj
  obtain ⟨-, -, -, -, cl5, -⟩ := hB F m S hodd hL1 hamb hm hreg s V hs0 (hs.trans hcc0) hcold
  set R := referenceFieldChain S V with hR
  set X := chartField R U j with hX
  set l : ℝ := (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1)) with hl
  have hl0 : 0 ≤ l := by positivity
  have hl1 : l ≤ 1 := pow_le_one₀ (by positivity) (by rw [div_le_one hLp]; exact hLr)
  set ε : ℝ := C0 * s * l ^ 2 with hε
  have hε0 : 0 ≤ ε := by positivity
  have hl2 : l ^ 2 ≤ 1 := pow_le_one₀ hl0 hl1
  have hεs : ε ≤ C0 * s := by
    have : C0 * s * l ^ 2 ≤ C0 * s * 1 := mul_le_mul_of_nonneg_left hl2 (by positivity)
    linarith
  have hCs : C0 * s ≤ min c1 1 := by
    have : (C0 + 1) * s ≤ (C0 + 1) * c := mul_le_mul_of_nonneg_left hs (by positivity)
    nlinarith
  have hεc : ε ≤ c1 := (hεs.trans hCs).trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := (hεs.trans hCs).trans (min_le_right _ _)
  have hτ : (F.blockSide : ℝ) * t ≤ (F.blockSide : ℝ) * c := mul_le_mul_of_nonneg_left ht hLp.le
  have hspread : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy (R j) (refineSite b.1) (bondContour F.blockSide h π b.2) *
        (polarUnit (contourAverage (R j) b))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε :=
    fun h hh π => cl5 j hj b hb h hh π
  have hg : ∀ a ∈ FlatPairing.twoBlockHull F.blockSide b.2, ∀ k,
      a + basisVector k ∈ FlatPairing.twoBlockHull F.blockSide b.2 →
      ‖((X (refineSite b.1 + siteOfCoords j a) k * (R j (refineSite b.1 + siteOfCoords j a) k)⁻¹ : UnitQuaternion) :
        ℍ[ℝ]) - 1‖ ≤ t := by
    intro a ha k hk
    have h1 := adjacentBound_of_mem_twoBlockHull hodd hj' hbl ha hk
    exact (norm_coe_sub_one_le_norm_unitQuaternionLog _).trans h1
  obtain ⟨hQ'n, m1, m2⟩ := hM F j X (R j) b t ε hodd hj' ht0 hε0 (hτ.trans hct) hεc hg hspread
  have hline : ∀ h ∈ centredCube F.blockSide, ∀ r ∈ Finset.range F.blockSide,
      ‖levelCoordinate R U j (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2‖ ≤ t := hbl.2
  have hQn := norm_parallelAverage_le_mul hodd (R j) hline
  have ht1 : t ≤ 1 := by
    have h1 : (9 + 4 * C1) * ((F.blockSide : ℝ) * t) ≤ 1 / 2 := by
      refine le_trans (mul_le_mul_of_nonneg_left hτ (by positivity)) hct'
    nlinarith [mul_le_mul_of_nonneg_right hLr ht0]
  have hQQ : ‖parallelAverage (R j) (levelCoordinate R U j) b - parallelAverage (R j) (pureGap X (R j)) b‖ ≤
      (F.blockSide : ℝ) * t ^ 2 := by
    rw [parallelAverage_sub]
    refine norm_parallelAverage_le_mul hodd (R j) fun h hh r hr => ?_
    have h1 := hline h hh r hr
    have h2 := norm_pureComponent_exp_sub_self_le (re_unitQuaternionLog (chartGap R U j
      (refineSite b.1 + siteOfCoords j h + (r : ℤ) • unitStep j b.2) b.2)) (h1.trans ht1)
    rw [exp_unitQuaternionLog] at h2
    rw [norm_sub_rev]
    exact h2.trans (pow_le_pow_left₀ (norm_nonneg _) h1 2)
  have hQre : (parallelAverage (R j) (levelCoordinate R U j) b).re = 0 :=
    re_parallelAverage (R j) (fun x i => re_unitQuaternionLog _) b
  have hmain := norm_unitQuaternionLog_sub_le (E := bondAverageGap R U j b) hQre (by positivity) hε0 hC1 m1 m2
    hQQ hQn hQ'n (le_trans (mul_le_mul_of_nonneg_left hτ (by positivity)) hct') hε1
  have hsize : 0 ≤ 1 - ‖contourAverage X b‖ ∧
      1 - ‖contourAverage X b‖ ≤ (5 * (F.blockSide : ℝ) * t + ε) ^ 2 / 2 := by
    refine contourAverage_norm_near_one hodd X b (polarUnit (contourAverage (R j) b)) (by positivity)
      fun h hh π => ?_
    have e : pathHolonomy X (refineSite b.1) (bondContour F.blockSide h π b.2) *
          (polarUnit (contourAverage (R j) b))⁻¹ =
        (pathHolonomy X (refineSite b.1) (bondContour F.blockSide h π b.2) *
            (pathHolonomy (R j) (refineSite b.1) (bondContour F.blockSide h π b.2))⁻¹) *
          (pathHolonomy (R j) (refineSite b.1) (bondContour F.blockSide h π b.2) *
            (polarUnit (contourAverage (R j) b))⁻¹) := by
      group
    rw [e]
    refine (norm_coe_mul_sub_one_le _ _).trans (add_le_add ?_ (hspread h hh π))
    exact norm_bondContour_holonomy_gap_le hodd X (R j) ht0 hg hh π
  have hlm : ‖gaugedBondAverage R U j b‖ = ‖contourAverage X b‖ := norm_gaugedContourAverage _ _ _
  have hy : 0 ≤ s * l ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · refine hmain.trans ?_
    have e := angle_constant_bound hLr ht0 hy hC1.le hC0.le
    have e2 : ε = C0 * (s * l ^ 2) := by rw [hε]; ring
    rw [e2]
    exact e
  · rw [hlm]
    exact hsize.1
  · rw [hlm]
    refine hsize.2.trans ?_
    have e1 : (5 * (F.blockSide : ℝ) * t + ε) ^ 2 / 2 ≤ 25 * (F.blockSide : ℝ) ^ 2 * t ^ 2 + ε ^ 2 := by
      nlinarith [sq_nonneg (5 * (F.blockSide : ℝ) * t - ε)]
    have e2 : ε ^ 2 = C0 ^ 2 * (s ^ 2 * l ^ 4) := by rw [hε]; ring
    rw [e2] at e1
    exact e1.trans (size_constant_bound hLr ht0 (by positivity) hC1.le hC0.le)
end YangMills.Construction.BlockAverages
end
