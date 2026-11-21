import YangMills.Construction.ColdChainAtEveryLevel.DensityUnderAChangeOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheTerms
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionUnderAGaugeOfTheTopProof
import YangMills.Construction.LawOnABoxOfTheFlow.BoundsOnTheEllipsoid
import YangMills.Construction.LawOnABoxOfTheFlow.GapOfTheCoveredGradient
import YangMills.Construction.LawOnABoxOfTheFlow.OnePointInAnOrbit
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields ColdStepAtMirrorFrames ResponseInTheExpansion
open BlockAverages hiding adjointAction unitStep
namespace ChartOrbit
private def imPart (q : ℍ[ℝ]) : ℍ[ℝ] := ⟨0, q.imI, q.imJ, q.imK⟩
private theorem re_imPart (q : ℍ[ℝ]) : (imPart q).re = 0 := rfl
private theorem imI_imPart (q : ℍ[ℝ]) : (imPart q).imI = q.imI := rfl
private theorem imJ_imPart (q : ℍ[ℝ]) : (imPart q).imJ = q.imJ := rfl
private theorem imK_imPart (q : ℍ[ℝ]) : (imPart q).imK = q.imK := rfl
private theorem re_add_imPart (q : ℍ[ℝ]) : ((q.re : ℝ) : ℍ[ℝ]) + imPart q = q := by
  ext <;> simp [re_imPart, imI_imPart, imJ_imPart, imK_imPart]
private theorem norm_sq_eq_re_sq_add (q : ℍ[ℝ]) : ‖q‖ ^ 2 = q.re ^ 2 + ‖imPart q‖ ^ 2 := by
  have h1 := Quaternion.normSq_eq_norm_mul_self q
  have h2 := Quaternion.normSq_eq_norm_mul_self (imPart q)
  rw [Quaternion.normSq_def'] at h1 h2
  simp only [re_imPart, imI_imPart, imJ_imPart, imK_imPart] at h2
  rw [pow_two, pow_two ‖imPart q‖]
  linarith
private theorem norm_imPart_le (q : ℍ[ℝ]) : ‖imPart q‖ ≤ ‖q‖ := by
  have := norm_sq_eq_re_sq_add q
  exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg q.re]) (norm_nonneg q) |>.2
private theorem abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
private theorem norm_coe_unit (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
private theorem coe_unit_mul_star (g : UnitQuaternion) : (g : ℍ[ℝ]) * star (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.BlockAverages.GaugeChangeDensity.unitQuaternion_mul_star <;> assumption
private def imUnit (g : UnitQuaternion) : imaginaryQuaternions := ⟨imPart (g : ℍ[ℝ]), re_imPart _⟩
private theorem imUnit_one : imUnit (1 : UnitQuaternion) = 0 := by
  apply Subtype.ext
  ext <;> simp [imUnit, re_imPart, imI_imPart, imJ_imPart, imK_imPart]
private theorem re_sq_add_norm_imUnit_sq (g : UnitQuaternion) : (g : ℍ[ℝ]).re ^ 2 + ‖imUnit g‖ ^ 2 = 1 := by
  have h := norm_sq_eq_re_sq_add (g : ℍ[ℝ])
  rw [norm_coe_unit] at h
  have h' : ‖imUnit g‖ = ‖imPart (g : ℍ[ℝ])‖ := rfl
  rw [h']
  linarith
private theorem coe_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) :
    ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X : imaginaryQuaternions) : ℍ[ℝ]) = (g : ℍ[ℝ]) * (X : ℍ[ℝ]) * star (g : ℍ[ℝ]) := rfl
private theorem norm_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) : ‖adjointAction g X‖ = ‖X‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction <;> assumption
private theorem re_sq_add_norm_adjoint_sq (g h : UnitQuaternion) :
    (h : ℍ[ℝ]).re ^ 2 + ‖_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (imUnit h)‖ ^ 2 = 1 := by
  rw [norm_adjointAction]
  exact re_sq_add_norm_imUnit_sq h
private theorem conj_eq_re_add_adjoint (V h : UnitQuaternion) :
    (V : ℍ[ℝ]) * (h : ℍ[ℝ]) * star (V : ℍ[ℝ]) =
      (((h : ℍ[ℝ]).re : ℝ) : ℍ[ℝ]) + ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction V (imUnit h) : imaginaryQuaternions) : ℍ[ℝ]) := by
  rw [coe_adjointAction]
  have h1 : (imUnit h : ℍ[ℝ]) = imPart (h : ℍ[ℝ]) := rfl
  rw [h1]
  conv_lhs => rw [← re_add_imPart (h : ℍ[ℝ])]
  rw [mul_add, add_mul, ← Quaternion.coe_commutes, mul_assoc _ _ (star (V : ℍ[ℝ])), coe_unit_mul_star, mul_one]
private theorem one_sub_sqrt_bounds {s t : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ t) (ht : t ≤ 1) :
    0 ≤ 1 - Real.sqrt (1 - s ^ 2) ∧ 1 - Real.sqrt (1 - s ^ 2) ≤ t := by
  have h1 : s ^ 2 ≤ 1 := by nlinarith
  have hle : Real.sqrt (1 - s ^ 2) ≤ 1 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [sq_nonneg s]⟩
  have hge : 1 - s ^ 2 ≤ Real.sqrt (1 - s ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg s]
  constructor
  · linarith
  · nlinarith
private theorem one_sub_le_of_sq_add_sq {c y : ℝ} (hc : 0 ≤ c) (hy : 0 ≤ y) (h : c ^ 2 + y ^ 2 = 1) :
    0 ≤ 1 - c ∧ 1 - c ≤ y := by
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg y]
  have hy1 : y ≤ 1 := by nlinarith [sq_nonneg c]
  refine ⟨by linarith, ?_⟩
  nlinarith
private theorem bond_relation_error {c d m m' t : ℝ} {η ζ ζ' ξ : ℍ[ℝ]}
    (hη : η.re = 0) (hζ : ζ.re = 0) (hζ' : ζ'.re = 0) (hξ : ξ.re = 0)
    (H : ((c : ℍ[ℝ]) + η) * ((m : ℍ[ℝ]) + ζ) = ((m' : ℍ[ℝ]) + ζ') * ((d : ℍ[ℝ]) + ξ))
    (hc : 0 ≤ 1 - c ∧ 1 - c ≤ ‖η‖) (hd : 0 ≤ 1 - d ∧ 1 - d ≤ ‖ξ‖)
    (hm : 0 ≤ 1 - m ∧ 1 - m ≤ t) (hm' : 0 ≤ 1 - m' ∧ 1 - m' ≤ t) (ht : ‖ζ‖ ≤ t) (ht' : ‖ζ'‖ ≤ t) :
    ‖ζ' - ζ - (η - ξ)‖ ≤ 3 * t * (‖η‖ + ‖ξ‖) := by
  have hid : ζ' - ζ - (η - ξ) =
      (1 - d) • ζ' - (1 - c) • ζ - (1 - m) • η + (1 - m') • ξ + imPart (η * ζ) - imPart (ζ' * ξ) := by
    have hI := congrArg (fun q : ℍ[ℝ] => q.imI) H
    have hJ := congrArg (fun q : ℍ[ℝ] => q.imJ) H
    have hK := congrArg (fun q : ℍ[ℝ] => q.imK) H
    simp only [Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_add,
      Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add, Quaternion.re_coe,
      Quaternion.imI_coe, Quaternion.imJ_coe, Quaternion.imK_coe, hη, hζ, hζ', hξ] at hI hJ hK
    ext
    · simp [re_imPart, hη, hζ, hζ', hξ]
    · simp only [imI_imPart, Quaternion.imI_sub, Quaternion.imI_add, Quaternion.imI_smul, Quaternion.imI_mul,
        hη, hζ, hζ', hξ, smul_eq_mul]
      linear_combination -hI
    · simp only [imJ_imPart, Quaternion.imJ_sub, Quaternion.imJ_add, Quaternion.imJ_smul, Quaternion.imJ_mul,
        hη, hζ, hζ', hξ, smul_eq_mul]
      linear_combination -hJ
    · simp only [imK_imPart, Quaternion.imK_sub, Quaternion.imK_add, Quaternion.imK_smul, Quaternion.imK_mul,
        hη, hζ, hζ', hξ, smul_eq_mul]
      linear_combination -hK
  rw [hid]
  have n1 : ‖(1 - d) • ζ'‖ ≤ ‖ξ‖ * t := by
    rw [norm_smul, Real.norm_of_nonneg hd.1]
    exact mul_le_mul hd.2 ht' (norm_nonneg _) (norm_nonneg _)
  have n2 : ‖(1 - c) • ζ‖ ≤ ‖η‖ * t := by
    rw [norm_smul, Real.norm_of_nonneg hc.1]
    exact mul_le_mul hc.2 ht (norm_nonneg _) (norm_nonneg _)
  have n3 : ‖(1 - m) • η‖ ≤ t * ‖η‖ := by
    rw [norm_smul, Real.norm_of_nonneg hm.1]
    exact mul_le_mul_of_nonneg_right hm.2 (norm_nonneg _)
  have n4 : ‖(1 - m') • ξ‖ ≤ t * ‖ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg hm'.1]
    exact mul_le_mul_of_nonneg_right hm'.2 (norm_nonneg _)
  have n5 : ‖imPart (η * ζ)‖ ≤ ‖η‖ * t := by
    refine (norm_imPart_le _).trans ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)
  have n6 : ‖imPart (ζ' * ξ)‖ ≤ t * ‖ξ‖ := by
    refine (norm_imPart_le _).trans ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ht' (norm_nonneg _)
  have s1 := norm_sub_le ((1 - d) • ζ' - (1 - c) • ζ - (1 - m) • η + (1 - m') • ξ + imPart (η * ζ)) (imPart (ζ' * ξ))
  have s2 := norm_add_le ((1 - d) • ζ' - (1 - c) • ζ - (1 - m) • η + (1 - m') • ξ) (imPart (η * ζ))
  have s3 := norm_add_le ((1 - d) • ζ' - (1 - c) • ζ - (1 - m) • η) ((1 - m') • ξ)
  have s4 := norm_sub_le ((1 - d) • ζ' - (1 - c) • ζ) ((1 - m) • η)
  have s5 := norm_sub_le ((1 - d) • ζ') ((1 - c) • ζ)
  nlinarith
private theorem gauge_mul_chart {g h w w' V : UnitQuaternion} {M M' : ℍ[ℝ]}
    (hw : (w : ℍ[ℝ]) = M * (V : ℍ[ℝ])) (hw' : (w' : ℍ[ℝ]) = M' * (V : ℍ[ℝ]))
    (hg : w' = g * w * h⁻¹) :
    (g : ℍ[ℝ]) * M = M' * ((V : ℍ[ℝ]) * (h : ℍ[ℝ]) * star (V : ℍ[ℝ])) := by
  have e1 : (g : ℍ[ℝ]) * (w : ℍ[ℝ]) = (w' : ℍ[ℝ]) * (h : ℍ[ℝ]) := by
    have : w' * h = g * w := by rw [hg]; group
    exact (congrArg (fun u : UnitQuaternion => (u : ℍ[ℝ])) this).symm
  calc (g : ℍ[ℝ]) * M = ((g : ℍ[ℝ]) * (M * (V : ℍ[ℝ]))) * star (V : ℍ[ℝ]) := by
        rw [mul_assoc, mul_assoc, coe_unit_mul_star, mul_one]
    _ = (M' * (V : ℍ[ℝ]) * (h : ℍ[ℝ])) * star (V : ℍ[ℝ]) := by rw [← hw, e1, hw']
    _ = M' * ((V : ℍ[ℝ]) * (h : ℍ[ℝ]) * star (V : ℍ[ℝ])) := by simp only [mul_assoc]
private theorem norm_gauge_sub_one_le {g h w w' : UnitQuaternion} (hg : w' = g * w * h⁻¹) :
    ‖(g : ℍ[ℝ]) - 1‖ ≤ ‖(h : ℍ[ℝ]) - 1‖ + ‖(w' : ℍ[ℝ]) - (w : ℍ[ℝ])‖ := by
  have e1 : (g : ℍ[ℝ]) * (w : ℍ[ℝ]) = (w' : ℍ[ℝ]) * (h : ℍ[ℝ]) := by
    have : w' * h = g * w := by rw [hg]; group
    exact (congrArg (fun u : UnitQuaternion => (u : ℍ[ℝ])) this).symm
  have e2 : ((g : ℍ[ℝ]) - 1) * (w : ℍ[ℝ]) =
      (w' : ℍ[ℝ]) * ((h : ℍ[ℝ]) - 1) + ((w' : ℍ[ℝ]) - (w : ℍ[ℝ])) := by
    rw [sub_mul, e1, mul_sub]
    simp only [one_mul, mul_one]
    abel
  have e3 : ‖(g : ℍ[ℝ]) - 1‖ = ‖((g : ℍ[ℝ]) - 1) * (w : ℍ[ℝ])‖ := by
    rw [norm_mul, norm_coe_unit, mul_one]
  rw [e3, e2]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_coe_unit, one_mul]
private theorem norm_chartPoint_sub_le (A : imaginaryQuaternions) {ζ ζ' : imaginaryQuaternions} {t : ℝ}
    (h : ‖ζ‖ ≤ t) (h' : ‖ζ'‖ ≤ t) (ht : t ≤ 1) :
    ‖chartPoint A ζ' - chartPoint A ζ‖ ≤ 3 * t := by
  unfold chartPoint
  rw [← sub_mul, norm_mul, norm_coe_unit, mul_one]
  have hm := one_sub_sqrt_bounds (norm_nonneg ζ) h ht
  have hm' := one_sub_sqrt_bounds (norm_nonneg ζ') h' ht
  have e : (((Real.sqrt (1 - ‖ζ'‖ ^ 2) : ℝ) : ℍ[ℝ]) + (ζ' : ℍ[ℝ])) -
      (((Real.sqrt (1 - ‖ζ‖ ^ 2) : ℝ) : ℍ[ℝ]) + (ζ : ℍ[ℝ])) =
      ((Real.sqrt (1 - ‖ζ'‖ ^ 2) - Real.sqrt (1 - ‖ζ‖ ^ 2) : ℝ) : ℍ[ℝ]) + ((ζ' : ℍ[ℝ]) - (ζ : ℍ[ℝ])) := by
    rw [Quaternion.coe_sub]
    abel
  rw [e]
  have n1 : ‖((Real.sqrt (1 - ‖ζ'‖ ^ 2) - Real.sqrt (1 - ‖ζ‖ ^ 2) : ℝ) : ℍ[ℝ])‖ ≤ t := by
    rw [Quaternion.norm_coe, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hm.1, hm.2, hm'.1, hm'.2]
  have n2 := norm_sub_le (ζ' : ℍ[ℝ]) (ζ : ℍ[ℝ])
  have n3 : ‖(ζ : ℍ[ℝ])‖ = ‖ζ‖ := rfl
  have n4 : ‖(ζ' : ℍ[ℝ])‖ = ‖ζ'‖ := rfl
  have n5 := norm_add_le ((Real.sqrt (1 - ‖ζ'‖ ^ 2) - Real.sqrt (1 - ‖ζ‖ ^ 2) : ℝ) : ℍ[ℝ])
    ((ζ' : ℍ[ℝ]) - (ζ : ℍ[ℝ]))
  linarith
variable {n : ℕ}
private theorem natAbs_coord_le_supDist (z o : TorusSite n) (i : Fin 4) :
    ((z i - o i).valMinAbs).natAbs ≤ supDist z o :=
  Finset.le_sup (f := fun i => ((z i - o i).valMinAbs).natAbs) (Finset.mem_univ i)
private theorem supDist_le_of_coord {z o : TorusSite n} {m : ℕ}
    (h : ∀ i, ((z i - o i).valMinAbs).natAbs ≤ m) : supDist z o ≤ m :=
  Finset.sup_le fun i _ => h i
variable [NeZero n]
private theorem mem_supBall_natCast {o z : TorusSite n} {R : ℕ} :
    z ∈ supBall o (R : ℝ) ↔ supDist z o ≤ R := by
  simp [supBall]
private theorem mem_supBall_two_mul {o z : TorusSite n} {R : ℕ} :
    z ∈ supBall o (2 * (R : ℝ)) ↔ supDist z o ≤ 2 * R := by
  simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and]
  exact_mod_cast Iff.rfl
private theorem natAbs_unitStep_le (hn : 2 ≤ n) (i j : Fin 4) : ((unitStep n i j).valMinAbs).natAbs ≤ 1 := by
  by_cases h : j = i
  · subst h
    have e : (1 : ZMod n).valMinAbs = 1 := by
      rw [ZMod.valMinAbs_spec]
      refine ⟨by simp, ?_⟩
      constructor <;> push_cast <;> omega
    simp [unitStep, e]
  · simp [unitStep, Pi.single_eq_of_ne h]
private theorem supDist_add_unitStep_le (hn : 2 ≤ n) (z o : TorusSite n) (i : Fin 4) :
    supDist (z + unitStep n i) o ≤ supDist z o + 1 := by
  apply supDist_le_of_coord
  intro j
  have e : (z + unitStep n i) j - o j = (z j - o j) + unitStep n i j := by
    simp only [Pi.add_apply]
    ring
  rw [e]
  exact ((ZMod.natAbs_valMinAbs_add_le _ _).trans (Int.natAbs_add_le _ _)).trans
    (Nat.add_le_add (natAbs_coord_le_supDist z o j) (natAbs_unitStep_le hn i j))
private theorem supDist_le_add_unitStep (hn : 2 ≤ n) (z o : TorusSite n) (i : Fin 4) :
    supDist z o ≤ supDist (z + unitStep n i) o + 1 := by
  apply supDist_le_of_coord
  intro j
  have e : z j - o j = ((z + unitStep n i) j - o j) + -(unitStep n i j) := by
    simp only [Pi.add_apply]
    ring
  rw [e]
  refine ((ZMod.natAbs_valMinAbs_add_le _ _).trans (Int.natAbs_add_le _ _)).trans
    (Nat.add_le_add (natAbs_coord_le_supDist _ o j) ?_)
  rw [ZMod.natAbs_valMinAbs_neg]
  exact natAbs_unitStep_le hn i j
private theorem mem_bondsWithin_of_mem_bondsTouching {o : TorusSite n} {R : ℕ} (hR : 1 ≤ R) (hn : 2 ≤ n)
    {b : TorusBond n} (hb : b ∈ bondsTouching o R) : b ∈ bondsWithin (supBall o (2 * (R : ℝ))) := by
  simp only [bondsTouching, Finset.mem_filter, Finset.mem_univ, true_and, mem_supBall_natCast] at hb
  simp only [bondsWithin, Finset.mem_filter, Finset.mem_univ, true_and, mem_supBall_two_mul]
  have h1 := supDist_add_unitStep_le hn b.1 o b.2
  have h2 := supDist_le_add_unitStep hn b.1 o b.2
  omega
private theorem norm_gauge_sub_one_le_walk {o : TorusSite n} {R : ℕ} (hn : 16 * R < n) (hR : 1 ≤ R)
    {γ : TorusSite n → UnitQuaternion} (hγ : IsSupportedGauge o R γ) {s : ℝ}
    (hstep : ∀ w : TorusSite n, ((w, (0 : Fin 4)) : TorusBond n) ∈ bondsWithin (supBall o (2 * (R : ℝ))) →
      ‖(γ w : ℍ[ℝ]) - 1‖ ≤ ‖(γ (w + unitStep n 0) : ℍ[ℝ]) - 1‖ + s) :
    ∀ (m : ℕ) (w : TorusSite n), (∀ i, i ≠ 0 → ((w i - o i).valMinAbs).natAbs ≤ R) →
      -(R : ℤ) ≤ (w 0 - o 0).valMinAbs → (w 0 - o 0).valMinAbs + m = R + 1 →
      ‖(γ w : ℍ[ℝ]) - 1‖ ≤ m * s := by
  intro m
  induction m with
  | zero =>
    intro w _ _ ha
    have hw : w ∉ supBall o (R : ℝ) := by
      intro hmem
      have h1 := mem_supBall_natCast.mp hmem
      have h2 := natAbs_coord_le_supDist w o 0
      push_cast at ha
      omega
    rw [hγ w hw]
    simp
  | succ m ih =>
    intro w hi ha1 ha
    push_cast at ha
    have hc : (w + unitStep n 0) 0 - o 0 = (w 0 - o 0) + 1 := by
      simp only [Pi.add_apply, unitStep, Pi.single_eq_same]
      ring
    have ha' : ((w + unitStep n 0) 0 - o 0).valMinAbs = (w 0 - o 0).valMinAbs + 1 := by
      rw [ZMod.valMinAbs_spec]
      refine ⟨?_, ?_⟩
      · rw [hc]
        simp
      · constructor <;> omega
    have hi' : ∀ i, i ≠ 0 → (w + unitStep n 0) i - o i = w i - o i := by
      intro i hne
      simp [unitStep, Pi.single_eq_of_ne hne]
    have hd : supDist w o ≤ R := by
      apply supDist_le_of_coord
      intro i
      by_cases h0 : i = 0
      · subst h0
        omega
      · exact hi i h0
    have hd' := supDist_add_unitStep_le (by omega) w o 0
    have hb : ((w, (0 : Fin 4)) : TorusBond n) ∈ bondsWithin (supBall o (2 * (R : ℝ))) := by
      simp only [bondsWithin, Finset.mem_filter, Finset.mem_univ, true_and, mem_supBall_two_mul]
      omega
    have h1 := hstep w hb
    have h2 := ih (w + unitStep n 0) (fun i hne => by rw [hi' i hne]; exact hi i hne)
      (by rw [ha']; omega) (by rw [ha']; omega)
    push_cast
    linarith
private theorem re_gauge_pos {o : TorusSite n} {R : ℕ} (hn : 16 * R < n) (hR : 1 ≤ R)
    {γ : TorusSite n → UnitQuaternion} (hγ : IsSupportedGauge o R γ) {s : ℝ} (hs : 0 ≤ s)
    (hsmall : (2 * (R : ℝ) + 1) * s < 1)
    (hstep : ∀ w : TorusSite n, ((w, (0 : Fin 4)) : TorusBond n) ∈ bondsWithin (supBall o (2 * (R : ℝ))) →
      ‖(γ w : ℍ[ℝ]) - 1‖ ≤ ‖(γ (w + unitStep n 0) : ℍ[ℝ]) - 1‖ + s) (z : TorusSite n) :
    0 < (γ z : ℍ[ℝ]).re := by
  by_cases hz : z ∈ supBall o (R : ℝ)
  · have h1 := mem_supBall_natCast.mp hz
    have hco := fun i => (natAbs_coord_le_supDist z o i).trans h1
    have h0 := hco 0
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = R + 1 - (z 0 - o 0).valMinAbs :=
      ⟨(R + 1 - (z 0 - o 0).valMinAbs).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hw := norm_gauge_sub_one_le_walk hn hR hγ hstep m z (fun i _ => hco i) (by omega) (by omega)
    have hm' : (m : ℝ) ≤ 2 * R + 1 := by
      have : m ≤ 2 * R + 1 := by omega
      exact_mod_cast this
    have hlt : ‖(γ z : ℍ[ℝ]) - 1‖ < 1 := by
      have : (m : ℝ) * s ≤ (2 * R + 1) * s := mul_le_mul_of_nonneg_right hm' hs
      linarith
    have hre := abs_re_le_norm ((γ z : ℍ[ℝ]) - 1)
    have hre' : ((γ z : ℍ[ℝ]) - 1).re = (γ z : ℍ[ℝ]).re - 1 := by simp
    rw [hre'] at hre
    have := (abs_le.mp hre).1
    linarith
  · rw [hγ z hz]
    simp
private theorem sum_bond_ends (f : TorusSite n → ℝ) :
    ∑ b : TorusBond n, (f b.1 + f (b.1 + unitStep n b.2)) = 8 * ∑ z : TorusSite n, f z := by
  rw [Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type_right]
  have h1 : ∀ z : TorusSite n, ∑ _i : Fin 4, f z = 4 * f z := by
    intro z
    simp
  have h2 : ∀ i : Fin 4, ∑ z : TorusSite n, f (z + unitStep n i) = ∑ z : TorusSite n, f z := fun i =>
    Equiv.sum_comp (Equiv.addRight (unitStep n i)) f
  simp only [h1, h2, ← Finset.mul_sum]
  simp
  ring
private theorem adjointAction_zero (g : UnitQuaternion) : adjointAction g 0 = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_zero <;> assumption
private theorem gaugeSlice_vanish {o : TorusSite n} {R : ℕ} {A ζ : TorusBond n → imaginaryQuaternions}
    (h : ζ ∈ gaugeSlice o R A) : ∀ b, b ∉ bondsTouching o R → ζ b = 0 := h.1
private theorem gaugeSlice_orthogonal {o : TorusSite n} {R : ℕ} {A ζ : TorusBond n → imaginaryQuaternions}
    (h : ζ ∈ gaugeSlice o R A) :
    ∀ χ : TorusSite n → imaginaryQuaternions, (∀ z, z ∉ supBall o (R : ℝ) → χ z = 0) →
      ∑ b : TorusBond n, inner ℝ (ζ b) (covariantGrad A χ b) = 0 := h.2
private theorem eq_and_gauge_trivial (o : TorusSite n) (R : ℕ) (hR : 1 ≤ R) (hn : 16 * R < n)
    (A : TorusBond n → imaginaryQuaternions)
    (hgap : ∀ χ : TorusSite n → imaginaryQuaternions, (∀ z, z ∉ supBall o (R : ℝ) → χ z = 0) →
      4 * ((R : ℝ) + 1)⁻¹ ^ 2 * ∑ z : TorusSite n, ‖χ z‖ ^ 2 ≤ ∑ b : TorusBond n, ‖covariantGrad A χ b‖ ^ 2)
    (W : TorusField n) (γ : TorusSite n → UnitQuaternion) (ζ ζ' : TorusBond n → imaginaryQuaternions)
    (t : ℝ) (ht0 : 0 ≤ t) (h12 : 12 * (R : ℝ) * t < 1)
    (hγ : IsSupportedGauge o R γ) (hζ : ζ ∈ gaugeSlice o R A) (hζ' : ζ' ∈ gaugeSlice o R A)
    (htζ : ∀ b, ‖ζ b‖ ≤ t) (htζ' : ∀ b, ‖ζ' b‖ ≤ t)
    (hW : IsInChart (supBall o (2 * (R : ℝ))) A ζ W)
    (hW' : IsInChart (supBall o (2 * (R : ℝ))) A ζ' (gaugeTransform γ W)) :
    ζ' = ζ ∧ ∀ z, γ z = 1 := by
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hn2 : 2 ≤ n := by omega
  have ht1 : t ≤ 1 := by nlinarith
  have hstep : ∀ b : TorusBond n, b ∈ bondsWithin (supBall o (2 * (R : ℝ))) →
      ‖(γ b.1 : ℍ[ℝ]) - 1‖ ≤ ‖(γ (b.1 + unitStep n b.2) : ℍ[ℝ]) - 1‖ + 3 * t := by
    intro b hb
    have h1 := norm_gauge_sub_one_le (g := γ b.1) (h := γ (b.1 + unitStep n b.2)) (w := W b.1 b.2)
      (w' := gaugeTransform γ W b.1 b.2) rfl
    rw [hW b hb, hW' b hb] at h1
    have h2 := norm_chartPoint_sub_le (A b) (htζ b) (htζ' b) ht1
    linarith
  have hre : ∀ z, 0 < (γ z : ℍ[ℝ]).re := fun z =>
    re_gauge_pos hn hR hγ (s := 3 * t) (by positivity) (by nlinarith) (fun w hw => hstep (w, 0) hw) z
  set χ : TorusSite n → imaginaryQuaternions := fun z => imUnit (γ z) with hχ
  have hχ0 : ∀ z, z ∉ supBall o (R : ℝ) → χ z = 0 := by
    intro z hz
    simp only [hχ]
    rw [hγ z hz, imUnit_one]
  have hEb : ∀ b : TorusBond n, ‖ζ' b - ζ b - covariantGrad A χ b‖ ≤
      3 * t * (‖χ b.1‖ + ‖χ (b.1 + unitStep n b.2)‖) := by
    intro b
    by_cases hb : b ∈ bondsTouching o R
    · have hbS := mem_bondsWithin_of_mem_bondsTouching hR hn2 hb
      have H := gauge_mul_chart (g := γ b.1) (h := γ (b.1 + unitStep n b.2)) (w := W b.1 b.2)
        (w' := gaugeTransform γ W b.1 b.2) (V := expUnit (A b)) (hW b hbS) (hW' b hbS) rfl
      rw [conj_eq_re_add_adjoint] at H
      have H2 : ((((γ b.1 : ℍ[ℝ]).re : ℝ) : ℍ[ℝ]) + ((χ b.1 : imaginaryQuaternions) : ℍ[ℝ])) *
          (((Real.sqrt (1 - ‖ζ b‖ ^ 2) : ℝ) : ℍ[ℝ]) + (ζ b : ℍ[ℝ])) =
          (((Real.sqrt (1 - ‖ζ' b‖ ^ 2) : ℝ) : ℍ[ℝ]) + (ζ' b : ℍ[ℝ])) *
          ((((γ (b.1 + unitStep n b.2) : ℍ[ℝ]).re : ℝ) : ℍ[ℝ]) +
            ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A b)) (χ (b.1 + unitStep n b.2)) : imaginaryQuaternions) : ℍ[ℝ])) := by
        have e : ((((γ b.1 : ℍ[ℝ]).re : ℝ) : ℍ[ℝ]) + ((χ b.1 : imaginaryQuaternions) : ℍ[ℝ])) =
            (γ b.1 : ℍ[ℝ]) :=
          re_add_imPart _
        rw [e]
        exact H
      have hc := one_sub_le_of_sq_add_sq (hre b.1).le (norm_nonneg (χ b.1)) (re_sq_add_norm_imUnit_sq (γ b.1))
      have hd := one_sub_le_of_sq_add_sq (hre (b.1 + unitStep n b.2)).le
        (norm_nonneg (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A b)) (χ (b.1 + unitStep n b.2))))
        (re_sq_add_norm_adjoint_sq (expUnit (A b)) (γ (b.1 + unitStep n b.2)))
      have hm := one_sub_sqrt_bounds (norm_nonneg (ζ b)) (htζ b) ht1
      have hm' := one_sub_sqrt_bounds (norm_nonneg (ζ' b)) (htζ' b) ht1
      have := bond_relation_error (χ b.1).2 (ζ b).2 (ζ' b).2
        (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A b)) (χ (b.1 + unitStep n b.2))).2 H2 hc hd hm hm' (htζ b) (htζ' b)
      have hx : ‖((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (expUnit (A b)) (χ (b.1 + unitStep n b.2)) : imaginaryQuaternions) : ℍ[ℝ])‖ =
          ‖χ (b.1 + unitStep n b.2)‖ :=
        norm_adjointAction _ _
      rw [hx] at this
      exact this
    · have h1 := gaugeSlice_vanish hζ b hb
      have h2 := gaugeSlice_vanish hζ' b hb
      simp only [bondsTouching, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hb
      have h3 := hχ0 _ hb.1
      have h4 := hχ0 _ hb.2
      simp only [covariantGrad, h1, h2, h3, h4, adjointAction_zero]
      simp
  set D : TorusBond n → imaginaryQuaternions := fun b => covariantGrad A χ b with hD
  set e : TorusBond n → imaginaryQuaternions := fun b => ζ' b - ζ b - D b with he
  have hsum : ∑ b : TorusBond n, (inner ℝ (D b) (D b) + inner ℝ (e b) (D b)) = 0 := by
    have h1 := gaugeSlice_orthogonal hζ χ hχ0
    have h2 := gaugeSlice_orthogonal hζ' χ hχ0
    have h3 : ∀ b, inner ℝ (D b) (D b) + inner ℝ (e b) (D b) =
        inner ℝ (ζ' b) (covariantGrad A χ b) - inner ℝ (ζ b) (covariantGrad A χ b) := by
      intro b
      simp only [he, hD, inner_sub_left]
      ring
    simp only [h3, Finset.sum_sub_distrib, h1, h2, sub_zero]
  have hDe : ∑ b : TorusBond n, ‖D b‖ ^ 2 ≤ ∑ b : TorusBond n, ‖e b‖ ^ 2 := by
    have h1 : ∀ b, ‖D b‖ ^ 2 - ‖e b‖ ^ 2 ≤ 2 * (inner ℝ (D b) (D b) + inner ℝ (e b) (D b)) := by
      intro b
      have h2 := norm_add_sq_real (e b) (D b)
      have h3 := real_inner_self_eq_norm_sq (D b)
      nlinarith [sq_nonneg ‖e b + D b‖]
    have h4 := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => h1 b
    rw [← Finset.mul_sum, hsum, Finset.sum_sub_distrib] at h4
    linarith
  have he2 : ∀ b : TorusBond n, ‖e b‖ ^ 2 ≤
      18 * t ^ 2 * (‖χ b.1‖ ^ 2 + ‖χ (b.1 + unitStep n b.2)‖ ^ 2) := by
    intro b
    have h1 : ‖e b‖ ≤ 3 * t * (‖χ b.1‖ + ‖χ (b.1 + unitStep n b.2)‖) := hEb b
    have h2 := pow_le_pow_left₀ (norm_nonneg (e b)) h1 2
    have h3 : (3 * t * (‖χ b.1‖ + ‖χ (b.1 + unitStep n b.2)‖)) ^ 2 ≤
        18 * t ^ 2 * (‖χ b.1‖ ^ 2 + ‖χ (b.1 + unitStep n b.2)‖ ^ 2) := by
      have h4 : (‖χ b.1‖ + ‖χ (b.1 + unitStep n b.2)‖) ^ 2 ≤
          2 * (‖χ b.1‖ ^ 2 + ‖χ (b.1 + unitStep n b.2)‖ ^ 2) := by
        nlinarith [sq_nonneg (‖χ b.1‖ - ‖χ (b.1 + unitStep n b.2)‖)]
      have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 9 * t ^ 2)
      nlinarith
    linarith
  set Q : ℝ := ∑ z : TorusSite n, ‖χ z‖ ^ 2 with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun z _ => by positivity
  have hup : ∑ b : TorusBond n, ‖e b‖ ^ 2 ≤ 144 * t ^ 2 * Q := by
    have h1 := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => he2 b
    rw [← Finset.mul_sum, sum_bond_ends (fun z => ‖χ z‖ ^ 2)] at h1
    linarith
  have hlow := hgap χ hχ0
  have hQz : Q = 0 := by
    by_contra hne
    have hpos : 0 < Q := lt_of_le_of_ne hQ0 (Ne.symm hne)
    have h1 : 4 * ((R : ℝ) + 1)⁻¹ ^ 2 * Q ≤ 144 * t ^ 2 * Q := by
      have h2 : ∑ b : TorusBond n, ‖D b‖ ^ 2 = ∑ b : TorusBond n, ‖covariantGrad A χ b‖ ^ 2 := rfl
      linarith
    have h3 : 4 * ((R : ℝ) + 1)⁻¹ ^ 2 ≤ 144 * t ^ 2 := le_of_mul_le_mul_right h1 hpos
    have hu : ((R : ℝ) + 1)⁻¹ * ((R : ℝ) + 1) = 1 := inv_mul_cancel₀ (by positivity)
    have h4 : ((R : ℝ) + 1)⁻¹ ≤ 6 * t := by
      apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
      nlinarith
    have h5 : 6 * t * ((R : ℝ) + 1) < 1 := by nlinarith
    have h6 := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)
    linarith
  have hχz : ∀ z, χ z = 0 := by
    intro z
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => by positivity)).mp hQz z (Finset.mem_univ z)
    simpa using h1
  refine ⟨?_, ?_⟩
  · funext b
    have h1 := hEb b
    simp only [hχz, norm_zero, add_zero, mul_zero] at h1
    have h2 : ζ' b - ζ b - covariantGrad A χ b = 0 := norm_le_zero_iff.mp h1
    have h3 : covariantGrad A χ b = 0 := by
      simp only [covariantGrad, hχz, adjointAction_zero, sub_zero]
    rw [h3, sub_zero] at h2
    exact sub_eq_zero.mp h2
  · intro z
    have h1 := re_sq_add_norm_imUnit_sq (γ z)
    have h2 : imUnit (γ z) = 0 := hχz z
    rw [h2, norm_zero] at h1
    have h3 : (γ z : ℍ[ℝ]).re = 1 := by nlinarith [hre z]
    apply Subtype.ext
    rw [← re_add_imPart (γ z : ℍ[ℝ]), h3]
    have h4 : imPart (γ z : ℍ[ℝ]) = 0 := congrArg (fun X : imaginaryQuaternions => (X : ℍ[ℝ])) h2
    rw [h4]
    simp
private theorem eventually_radius_scale_small (K : ℝ) (hK : 1 ≤ K) (κ₀ : ℝ) (h2 : κ₀ ≤ 1 / 21) :
    ∃ xs : ℝ, ∀ x : ℝ, xs ≤ x → 1 ≤ boxRadius κ₀ x ∧ 0 ≤ boxScale x ∧
      12 * (boxRadius κ₀ x : ℝ) * (K * (boxRadius κ₀ x : ℝ) ^ 3 * boxScale x) < 1 := by
  have hlo := isLittleO_log_rpow_atTop (r := 13 / 42) (by norm_num)
  have hev := hlo.def (c := 1 / (768 * K)) (by positivity)
  obtain ⟨xs, hxs⟩ := Filter.eventually_atTop.mp (hev.and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨xs, fun x hx => ?_⟩
  obtain ⟨hl, h1x⟩ := hxs x hx
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg h1x
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg (by positivity)] at hl
  have hpow : 0 < x ^ κ₀ := Real.rpow_pos_of_pos hx0 _
  have hR1 : 1 ≤ boxRadius κ₀ x := Nat.one_le_iff_ne_zero.mpr (by
    simp only [boxRadius]
    exact (Nat.ceil_pos.mpr hpow).ne')
  have hsz : 0 ≤ boxScale x := by
    unfold boxScale
    positivity
  refine ⟨hR1, hsz, ?_⟩
  set R : ℝ := (boxRadius κ₀ x : ℝ) with hRdef
  have hRpos : 0 ≤ R := by positivity
  have hy1 : 1 ≤ x ^ (1 / 21 : ℝ) := Real.one_le_rpow h1x (by norm_num)
  have hle : x ^ κ₀ ≤ x ^ (1 / 21 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1x h2
  have hRle : R ≤ 2 * x ^ (1 / 21 : ℝ) := by
    have : R < x ^ κ₀ + 1 := Nat.ceil_lt_add_one hpow.le
    linarith
  have hR4 : R ^ 4 ≤ 16 * x ^ (4 / 21 : ℝ) := by
    have e : x ^ (4 / 21 : ℝ) = (x ^ (1 / 21 : ℝ)) ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    rw [e]
    have := pow_le_pow_left₀ hRpos hRle 4
    calc R ^ 4 ≤ (2 * x ^ (1 / 21 : ℝ)) ^ 4 := this
      _ = 16 * (x ^ (1 / 21 : ℝ)) ^ 4 := by ring
  have hexp : x ^ (4 / 21 : ℝ) * x ^ (-(1 / 2 : ℝ)) * x ^ (13 / 42 : ℝ) = 1 := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
    norm_num
  have hA : 0 ≤ x ^ (4 / 21 : ℝ) * x ^ (-(1 / 2 : ℝ)) := by positivity
  have hB : x ^ (4 / 21 : ℝ) * x ^ (-(1 / 2 : ℝ)) * Real.log x ≤ 1 / (768 * K) := by
    have := mul_le_mul_of_nonneg_left hl hA
    calc x ^ (4 / 21 : ℝ) * x ^ (-(1 / 2 : ℝ)) * Real.log x
        ≤ x ^ (4 / 21 : ℝ) * x ^ (-(1 / 2 : ℝ)) * (1 / (768 * K) * x ^ (13 / 42 : ℝ)) := this
      _ = 1 / (768 * K) * (x ^ (4 / 21 : ℝ) * x ^ (-(1 / 2 : ℝ)) * x ^ (13 / 42 : ℝ)) := by ring
      _ = 1 / (768 * K) := by rw [hexp, mul_one]
  have hC : R ^ 4 * boxScale x ≤ 16 * x ^ (4 / 21 : ℝ) * boxScale x :=
    mul_le_mul_of_nonneg_right hR4 hsz
  have hD : 16 * x ^ (4 / 21 : ℝ) * boxScale x =
      32 * (x ^ (4 / 21 : ℝ) * x ^ (-(1 / 2 : ℝ)) * Real.log x) := by
    unfold boxScale
    ring
  have hE : R ^ 4 * boxScale x ≤ 32 * (1 / (768 * K)) := by
    rw [hD] at hC
    linarith
  have hF : 12 * R * (K * R ^ 3 * boxScale x) = 12 * K * (R ^ 4 * boxScale x) := by ring
  rw [hF]
  have hG : 12 * K * (R ^ 4 * boxScale x) ≤ 12 * K * (32 * (1 / (768 * K))) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have hH : 12 * K * (32 * (1 / (768 * K))) = 1 / 2 := by
    field_simp
    norm_num
  linarith
end ChartOrbit
theorem chartMeetsOrbitOnce (hG : covariantGradientGapStatement) (hB : ellipsoidBoundsStatement) :
    chartMeetsOrbitOnceStatement := by
  intro Tb hT κ₀ h1 h2 C₀ hC
  obtain ⟨K, xs₁, hK, hb⟩ := hB Tb hT κ₀ h1 h2 C₀ hC
  obtain ⟨xs₂, hs⟩ := ChartOrbit.eventually_radius_scale_small K hK κ₀ h2
  refine ⟨max xs₁ xs₂, ?_⟩
  intro x R k n _ o A hx hR hn hA W γ ζ ζ' hγ hζ hζ' hW hW'
  obtain ⟨hR1, hsz, hsm⟩ := hs x ((le_max_right _ _).trans hx)
  rw [← hR] at hR1 hsm
  have hbd := (hb x R k n o A ((le_max_left _ _).trans hx) hR hn hA).2
  have hK0 : 0 ≤ K * (R : ℝ) ^ 3 * boxScale x := by positivity
  exact ChartOrbit.eq_and_gauge_trivial o R hR1 hn A (hG n o R hR1 (by omega) A).1 W γ ζ ζ' _ hK0 hsm hγ hζ.1 hζ'.1
    (hbd ζ hζ).2.1 (hbd ζ' hζ').2.1 hW hW'
end YangMills.Construction.BoxGaussian
end
