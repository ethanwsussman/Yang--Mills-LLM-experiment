import YangMills.Construction.ColdChainAtEveryLevel.LeastQuarticGaugeProof
import YangMills.Construction.ColdChainAtEveryLevel.PinnedQuarticGauge
import YangMills.Construction.ColdChainAtEveryLevel.TraceOfTheInverseCube
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.PinnedGauge
theorem add_pow_four_le (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.add_pow_four_le_eight_mul <;> assumption
open BlockAverages LatticeFractionalIntegration PinnedGaugeData
theorem pow_three_mul_le_of_young {a f : ℝ} (ha : 0 ≤ a) (hf : 0 ≤ f) : a ^ 3 * f ≤ 3 / 8 * a ^ 4 + 2 * f ^ 4 := by
  have h : 0 ≤ (a - 2 * f) ^ 2 * (3 / 8 * a ^ 2 + 1 / 2 * a * f + 1 / 2 * f ^ 2) := by positivity
  linarith
theorem norm_sub_one_sq_eq (g : UnitQuaternion) : ‖(g : ℍ[ℝ]) - 1‖ ^ 2 = 2 - 2 * (g : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.GaugeFixing.norm_coe_sub_one_sq <;> assumption
theorem norm_pureComponent_sq_eq (g : UnitQuaternion) :
    ‖pureComponent (g : ℍ[ℝ])‖ ^ 2 = ‖(g : ℍ[ℝ]) - 1‖ ^ 2 * (1 - ‖(g : ℍ[ℝ]) - 1‖ ^ 2 / 4) := by
  have h := re_sq_add_norm_pureComponent_sq g
  have h2 := norm_sub_one_sq_eq g
  have e : (g : ℍ[ℝ]).re = 1 - ‖(g : ℍ[ℝ]) - 1‖ ^ 2 / 2 := by linarith
  rw [e] at h
  nlinarith
theorem norm_pureComponent_le_norm_sub_one (g : UnitQuaternion) : ‖pureComponent (g : ℍ[ℝ])‖ ≤ ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockLines.norm_pureComponent_coe_le <;> assumption
theorem re_mul_pureComponent {u : ℍ[ℝ]} (hu : u.re = 0) (q : ℍ[ℝ]) : (u * q).re = (u * pureComponent q).re := by
  simp [pureComponent, Quaternion.re_mul, hu]
  ring
theorem quaternion_re_mul_comm (a b : ℍ[ℝ]) : (a * b).re = (b * a).re := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.quaternion_re_mul_comm <;> assumption
theorem re_mul_self_of_re_eq_zero {x : ℍ[ℝ]} (hx : x.re = 0) : (x * x).re = - ‖x‖ ^ 2 := by apply _root_.YangMills.Construction.LeastQuarticGauge.re_mul_self_of_re_eq_zero <;> assumption
theorem abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
theorem abs_re_mul_le_norm_mul (a b : ℍ[ℝ]) : |(a * b).re| ≤ ‖a‖ * ‖b‖ := by
  have h := abs_re_le_norm (a * b)
  rwa [norm_mul] at h
theorem re_conj_eq_zero (g : UnitQuaternion) {w : ℍ[ℝ]} (hw : w.re = 0) :
    ((g : ℍ[ℝ]) * w * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = 0 := by
  rw [quaternion_re_mul_comm, ← mul_assoc]
  have h1 : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    rfl
  rw [h1, one_mul, hw]
theorem re_commutator_variation {u v : ℍ[ℝ]} (hu : u.re = 0) (hv : v.re = 0) (g : ℍ[ℝ]) :
    (u * g - g * v).re = ((u - v) * pureComponent g).re := by
  rw [Quaternion.re_sub, sub_mul, Quaternion.re_sub, re_mul_pureComponent hu g, quaternion_re_mul_comm g v,
    re_mul_pureComponent hv g]
theorem compactSpace_unitQuaternion : CompactSpace UnitQuaternion := by
  haveI : ProperSpace ℍ[ℝ] := FiniteDimensional.proper_real _
  have e : ((unitary ℍ[ℝ] : Submonoid ℍ[ℝ]) : Set ℍ[ℝ]) = Metric.sphere 0 1 := by
    ext q
    simp only [SetLike.mem_coe, mem_sphere_zero_iff_norm]
    constructor
    · intro h
      exact norm_coe_unitQuaternion ⟨q, h⟩
    · intro h
      have hs : Quaternion.normSq q = 1 := by
        rw [Quaternion.normSq_eq_norm_mul_self, h]
        norm_num
      rw [Unitary.mem_iff, Quaternion.star_mul_self, Quaternion.self_mul_star, hs]
      simp
  have hc : IsCompact ((unitary ℍ[ℝ] : Submonoid ℍ[ℝ]) : Set ℍ[ℝ]) := by
    rw [e]
    exact isCompact_sphere 0 1
  exact isCompact_iff_compactSpace.1 hc
theorem hasDerivAt_expUnit (w : imaginaryQuaternions) :
    HasDerivAt (fun τ : ℝ => ((expUnit (τ • w) : UnitQuaternion) : ℍ[ℝ])) (w : ℍ[ℝ]) 0 := by apply _root_.YangMills.Construction.GaugedCriticality.hasDerivAt_expUnit_smul <;> assumption
theorem expUnit_zero_smul (w : imaginaryQuaternions) : expUnit ((0 : ℝ) • w) = 1 := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.expUnit_zero_smul <;> assumption
theorem hasDerivAt_star {q : ℝ → ℍ[ℝ]} {q' : ℍ[ℝ]} {t : ℝ} (h : HasDerivAt q q' t) :
    HasDerivAt (fun τ => star (q τ)) (star q') t := by apply _root_.YangMills.Construction.GaugedCriticality.hasDerivAt_quaternion_star <;> assumption
theorem star_eq_neg_of_re_eq_zero {w : ℍ[ℝ]} (hw : w.re = 0) : star w = - w := by apply _root_.YangMills.Construction.BlockAverages.star_eq_neg_of_re_eq_zero <;> assumption
theorem hasDerivAt_expUnit_inv (w : imaginaryQuaternions) :
    HasDerivAt (fun τ : ℝ => (((expUnit (τ • w))⁻¹ : UnitQuaternion) : ℍ[ℝ])) (- (w : ℍ[ℝ])) 0 := by
  simp only [coe_unitQuaternion_inv]
  have h := hasDerivAt_star (hasDerivAt_expUnit w)
  rwa [star_eq_neg_of_re_eq_zero w.2] at h
variable (D : PinnedGaugeData)
theorem defect_rotateAlong (ξ : Lattice4 → imaginaryQuaternions) (τ : ℝ) (γ : Lattice4 → UnitQuaternion)
    (x : Lattice4) (i : Fin 4) :
    ((D.defect (PinnedGaugeData.rotateAlong ξ τ γ) x i : UnitQuaternion) : ℍ[ℝ]) =
      ((expUnit (τ • ξ x) : UnitQuaternion) : ℍ[ℝ]) * ((latticeGaugeTransform γ D.field x i : UnitQuaternion) : ℍ[ℝ]) *
        (((expUnit (τ • ξ (x + basisVector i)))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          (((D.target x i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  simp only [defect, latticeGaugeTransform, rotateAlong, mul_inv_rev, Submonoid.coe_mul, mul_assoc]
theorem hasDerivAt_defect_rotateAlong (ξ : Lattice4 → imaginaryQuaternions) (γ : Lattice4 → UnitQuaternion)
    (x : Lattice4) (i : Fin 4) :
    HasDerivAt (fun τ : ℝ => ((D.defect (PinnedGaugeData.rotateAlong ξ τ γ) x i : UnitQuaternion) : ℍ[ℝ]))
      ((ξ x : ℍ[ℝ]) * ((D.defect γ x i : UnitQuaternion) : ℍ[ℝ]) - ((D.defect γ x i : UnitQuaternion) : ℍ[ℝ]) *
        (((D.target x i : UnitQuaternion) : ℍ[ℝ]) * (ξ (x + basisVector i) : ℍ[ℝ]) *
          (((D.target x i)⁻¹ : UnitQuaternion) : ℍ[ℝ]))) 0 := by
  have e : (fun τ : ℝ => ((D.defect (PinnedGaugeData.rotateAlong ξ τ γ) x i : UnitQuaternion) : ℍ[ℝ])) = fun τ : ℝ =>
      ((expUnit (τ • ξ x) : UnitQuaternion) : ℍ[ℝ]) * ((latticeGaugeTransform γ D.field x i : UnitQuaternion) : ℍ[ℝ]) *
        (((expUnit (τ • ξ (x + basisVector i)))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          (((D.target x i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    funext τ
    exact defect_rotateAlong D ξ τ γ x i
  rw [e]
  have h := (((hasDerivAt_expUnit (ξ x)).mul_const ((latticeGaugeTransform γ D.field x i : UnitQuaternion) : ℍ[ℝ])).mul
    (hasDerivAt_expUnit_inv (ξ (x + basisVector i)))).mul_const (((D.target x i)⁻¹ : UnitQuaternion) : ℍ[ℝ])
  refine h.congr_deriv ?_
  have hinv : (((D.target x i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((D.target x i : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    rfl
  have e3 : ((latticeGaugeTransform γ D.field x i : UnitQuaternion) : ℍ[ℝ]) *
      (((D.target x i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
      (((D.target x i : UnitQuaternion) : ℍ[ℝ]) * (ξ (x + basisVector i) : ℍ[ℝ]) *
        (((D.target x i)⁻¹ : UnitQuaternion) : ℍ[ℝ])) =
      ((latticeGaugeTransform γ D.field x i : UnitQuaternion) : ℍ[ℝ]) * (ξ (x + basisVector i) : ℍ[ℝ]) *
        (((D.target x i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    calc _ = ((latticeGaugeTransform γ D.field x i : UnitQuaternion) : ℍ[ℝ]) *
        ((((D.target x i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((D.target x i : UnitQuaternion) : ℍ[ℝ])) *
        (ξ (x + basisVector i) : ℍ[ℝ]) * (((D.target x i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by simp only [mul_assoc]
      _ = _ := by rw [hinv, mul_one]
  simp only [expUnit_zero_smul, inv_one, OneMemClass.coe_one, mul_one, one_mul, defect, Submonoid.coe_mul, add_mul,
    mul_neg, neg_mul]
  rw [e3]
  noncomm_ring
variable {D}
theorem defect_congr {γ γ' : Lattice4 → UnitQuaternion} (h : ∀ x ∈ D.region, γ x = γ' x) {b : Lattice4 × Fin 4}
    (hb : b ∈ bondsOf D.region) : D.defect γ b.1 b.2 = D.defect γ' b.1 b.2 := by
  have hb' := Finset.mem_filter.1 hb
  have h1 : b.1 ∈ D.region := (Finset.mem_product.1 hb'.1).1
  simp only [defect, latticeGaugeTransform, h _ h1, h _ hb'.2]
theorem defectQuarticSum_congr {γ γ' : Lattice4 → UnitQuaternion} (h : ∀ x ∈ D.region, γ x = γ' x) :
    D.defectQuarticSum γ = D.defectQuarticSum γ' := by
  unfold defectQuarticSum
  exact Finset.sum_congr rfl fun b hb => by rw [defect_congr h hb]
theorem extendByOne_of_mem (m : D.region → UnitQuaternion) {x : Lattice4} (hx : x ∈ D.region) :
    D.extendByOne m x = m ⟨x, hx⟩ := by
  simp [extendByOne, hx]
theorem continuous_defect_extendByOne {b : Lattice4 × Fin 4} (hb : b ∈ bondsOf D.region) :
    Continuous (fun m : D.region → UnitQuaternion => ((D.defect (D.extendByOne m) b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) := by
  have hb' := Finset.mem_filter.1 hb
  have h1 : b.1 ∈ D.region := (Finset.mem_product.1 hb'.1).1
  have h2 : b.1 + basisVector b.2 ∈ D.region := hb'.2
  have e : (fun m : D.region → UnitQuaternion => ((D.defect (D.extendByOne m) b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) =
      fun m : D.region → UnitQuaternion =>
      ((m ⟨b.1, h1⟩ : UnitQuaternion) : ℍ[ℝ]) * ((D.field b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) *
        star ((m ⟨_, h2⟩ : UnitQuaternion) : ℍ[ℝ]) * star ((D.target b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) := by
    funext m
    simp only [defect, latticeGaugeTransform, extendByOne_of_mem m h1, extendByOne_of_mem m h2, Submonoid.coe_mul,
      coe_unitQuaternion_inv]
  rw [e]
  have c1 : ∀ u : D.region, Continuous (fun m : D.region → UnitQuaternion => ((m u : UnitQuaternion) : ℍ[ℝ])) :=
    fun u => continuous_subtype_val.comp (continuous_apply u)
  exact (((c1 _).mul continuous_const).mul (continuous_star.comp (c1 _))).mul continuous_const
theorem continuous_defectQuarticSum_extendByOne :
    Continuous (fun m : D.region → UnitQuaternion => D.defectQuarticSum (D.extendByOne m)) := by
  unfold defectQuarticSum
  exact continuous_finset_sum _ fun b hb => ((continuous_defect_extendByOne hb).sub continuous_const).norm.pow 4
theorem norm_sub_one_pow_four_eq (g : UnitQuaternion) : ‖(g : ℍ[ℝ]) - 1‖ ^ 4 = (2 - 2 * (g : ℍ[ℝ]).re) ^ 2 := by
  rw [← norm_sub_one_sq_eq]
  ring
theorem hasDerivAt_quartic_term {q : ℝ → ℍ[ℝ]} {q' : ℍ[ℝ]} (h : HasDerivAt q q' 0) :
    HasDerivAt (fun τ => (2 - 2 * (q τ).re) ^ 2) (2 * (2 - 2 * (q 0).re) * (-(2 * q'.re))) 0 := by
  let R : ℍ[ℝ] →L[ℝ] ℝ := ⟨QuaternionAlgebra.reₗ _ _ _, Quaternion.continuous_re⟩
  have h1 : HasDerivAt (fun τ => (q τ).re) q'.re 0 := R.hasFDerivAt.comp_hasDerivAt 0 h
  have h2 := ((h1.const_mul 2).const_sub 2).fun_pow 2
  simpa using h2
theorem rotateAlong_zero (ξ : Lattice4 → imaginaryQuaternions) (γ : Lattice4 → UnitQuaternion) :
    PinnedGaugeData.rotateAlong ξ 0 γ = γ := by
  funext x
  have e : expUnit (0 : imaginaryQuaternions) = 1 := by
    apply Subtype.ext
    simp [expUnit, NormedSpace.exp_zero]
  simp [PinnedGaugeData.rotateAlong, e]
theorem exists_minimizer_firstVariation {θ C₂ C₃ n₀ n₁ r₀ A η b c₁ : ℝ} {d : (Lattice4 → UnitQuaternion) → ℝ}
    (h : IsPinnedGaugeProblem D θ C₂ C₃ n₀ n₁ r₀ A η b c₁ d) (hbc : b < c₁) :
    ∃ γ, D.pinnedQuarticSum γ ≤ b ∧ ∀ (ξ : Lattice4 → imaginaryQuaternions) (ζ : D.CellIndex → ℍ[ℝ]),
      (∀ y ∈ D.cells, HasDerivAt
        (fun τ : ℝ => ((D.pin (PinnedGaugeData.rotateAlong ξ τ γ) y : UnitQuaternion) : ℍ[ℝ]))
        (ζ y * ((D.pin γ y : UnitQuaternion) : ℍ[ℝ])) 0) →
      ∑ b ∈ bondsOf D.region, ‖((D.defect γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 *
          ((ξ b.1 : ℍ[ℝ]) * ((D.defect γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) -
            ((D.defect γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) *
            (((D.target b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) * (ξ (b.1 + basisVector b.2) : ℍ[ℝ]) *
              (((D.target b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]))).re +
        ∑ y ∈ D.cells, ‖((D.pin γ y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 *
          (ζ y * ((D.pin γ y : UnitQuaternion) : ℍ[ℝ])).re = 0 := by
  classical
  haveI := compactSpace_unitQuaternion
  have hpin_congr : ∀ {γ γ' : Lattice4 → UnitQuaternion}, (∀ x ∈ D.region, γ x = γ' x) →
      D.pinnedQuarticSum γ = D.pinnedQuarticSum γ' := by
    intro γ γ' e
    unfold pinnedQuarticSum
    rw [defectQuarticSum_congr e]
    congr 1
    exact Finset.sum_congr rfl fun y hy => by rw [h.pin_congr γ γ' e y hy]
  set Sset : Set (D.region → UnitQuaternion) := {m | D.defectQuarticSum (D.extendByOne m) ≤ c₁} with hS
  have hcl : IsClosed Sset := isClosed_le continuous_defectQuarticSum_extendByOne continuous_const
  have hcomp : IsCompact Sset := hcl.isCompact
  obtain ⟨γ₀, hγ₀⟩ := h.exists_start
  have hK0 : ∀ γ : Lattice4 → UnitQuaternion, 0 ≤ ∑ y ∈ D.cells, ‖((D.pin γ y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 :=
    fun γ => Finset.sum_nonneg fun y _ => by positivity
  have hle : ∀ γ, D.defectQuarticSum γ ≤ D.pinnedQuarticSum γ := fun γ => by
    unfold pinnedQuarticSum
    linarith [hK0 γ]
  let m₀ : D.region → UnitQuaternion := fun x => γ₀ x
  have hm₀ : ∀ x ∈ D.region, D.extendByOne m₀ x = γ₀ x := fun x hx => extendByOne_of_mem m₀ hx
  have hne : Sset.Nonempty := ⟨m₀, by
    show D.defectQuarticSum (D.extendByOne m₀) ≤ c₁
    rw [defectQuarticSum_congr hm₀]
    linarith [hle γ₀]⟩
  have hcont : ContinuousOn (fun m : D.region → UnitQuaternion => D.pinnedQuarticSum (D.extendByOne m)) Sset := by
    unfold pinnedQuarticSum
    refine continuous_defectQuarticSum_extendByOne.continuousOn.add (continuousOn_finset_sum _ fun y hy => ?_)
    exact (((h.pin_continuousOn y hy).sub continuousOn_const).norm).pow 4
  obtain ⟨m, hmS, hmin⟩ := hcomp.exists_isMinOn hne hcont
  have hmb : D.pinnedQuarticSum (D.extendByOne m) ≤ b := by
    have h1 : D.pinnedQuarticSum (D.extendByOne m) ≤ D.pinnedQuarticSum (D.extendByOne m₀) := hmin (show m₀ ∈ Sset by
      show D.defectQuarticSum (D.extendByOne m₀) ≤ c₁
      rw [defectQuarticSum_congr hm₀]
      linarith [hle γ₀])
    rw [hpin_congr hm₀] at h1
    linarith
  refine ⟨D.extendByOne m, hmb, ?_⟩
  set γ := D.extendByOne m with hγ
  intro ξ ζ hζ
  have hgd := fun b : Lattice4 × Fin 4 => hasDerivAt_defect_rotateAlong D ξ γ b.1 b.2
  have hΦ1 : HasDerivAt (fun τ : ℝ => D.defectQuarticSum (PinnedGaugeData.rotateAlong ξ τ γ))
      (∑ b ∈ bondsOf D.region, 2 *
        (2 - 2 * ((D.defect (PinnedGaugeData.rotateAlong ξ 0 γ) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]).re) *
        (-(2 * ((ξ b.1 : ℍ[ℝ]) * ((D.defect γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) -
            ((D.defect γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) *
            (((D.target b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) * (ξ (b.1 + basisVector b.2) : ℍ[ℝ]) *
              (((D.target b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]))).re))) 0 := by
    have e : (fun τ : ℝ => D.defectQuarticSum (PinnedGaugeData.rotateAlong ξ τ γ)) = fun τ : ℝ =>
        ∑ b ∈ bondsOf D.region,
          (2 - 2 * ((D.defect (PinnedGaugeData.rotateAlong ξ τ γ) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]).re) ^ 2 := by
      funext τ
      unfold defectQuarticSum
      exact Finset.sum_congr rfl fun b _ => norm_sub_one_pow_four_eq _
    rw [e]
    exact HasDerivAt.fun_sum fun b _ => hasDerivAt_quartic_term (hgd b)
  have hΦ2 : HasDerivAt (fun τ : ℝ => ∑ y ∈ D.cells,
      ‖((D.pin (PinnedGaugeData.rotateAlong ξ τ γ) y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4)
      (∑ y ∈ D.cells, 2 * (2 - 2 * ((D.pin (PinnedGaugeData.rotateAlong ξ 0 γ) y : UnitQuaternion) : ℍ[ℝ]).re) *
        (-(2 * (ζ y * ((D.pin γ y : UnitQuaternion) : ℍ[ℝ])).re))) 0 := by
    have e : (fun τ : ℝ => ∑ y ∈ D.cells,
        ‖((D.pin (PinnedGaugeData.rotateAlong ξ τ γ) y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4) = fun τ : ℝ =>
        ∑ y ∈ D.cells, (2 - 2 * ((D.pin (PinnedGaugeData.rotateAlong ξ τ γ) y : UnitQuaternion) : ℍ[ℝ]).re) ^ 2 := by
      funext τ
      exact Finset.sum_congr rfl fun y _ => norm_sub_one_pow_four_eq _
    rw [e]
    exact HasDerivAt.fun_sum fun y hy => hasDerivAt_quartic_term (hζ y hy)
  have hΦ := hΦ1.add hΦ2
  have hlm : IsLocalMin (fun τ : ℝ => D.defectQuarticSum (PinnedGaugeData.rotateAlong ξ τ γ) +
      ∑ y ∈ D.cells, ‖((D.pin (PinnedGaugeData.rotateAlong ξ τ γ) y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4) 0 := by
    have hlt : D.defectQuarticSum (PinnedGaugeData.rotateAlong ξ 0 γ) < c₁ := by
      rw [rotateAlong_zero]
      linarith [hle γ]
    have hev : ∀ᶠ τ : ℝ in nhds 0, D.defectQuarticSum (PinnedGaugeData.rotateAlong ξ τ γ) < c₁ :=
      hΦ1.continuousAt.eventually_lt continuousAt_const hlt
    filter_upwards [hev] with τ hτ
    let mτ : D.region → UnitQuaternion := fun x => PinnedGaugeData.rotateAlong ξ τ γ x
    have hmτ : ∀ x ∈ D.region, D.extendByOne mτ x = PinnedGaugeData.rotateAlong ξ τ γ x :=
      fun x hx => extendByOne_of_mem mτ hx
    have hin : mτ ∈ Sset := by
      show D.defectQuarticSum (D.extendByOne mτ) ≤ c₁
      rw [defectQuarticSum_congr hmτ]
      exact hτ.le
    have h1 : D.pinnedQuarticSum (D.extendByOne m) ≤ D.pinnedQuarticSum (D.extendByOne mτ) := hmin hin
    rw [hpin_congr hmτ] at h1
    simp only [rotateAlong_zero]
    exact h1
  have hz := hlm.hasDerivAt_eq_zero hΦ
  simp only [rotateAlong_zero] at hz
  have e1 : ∀ g : UnitQuaternion, 2 - 2 * (g : ℍ[ℝ]).re = ‖(g : ℍ[ℝ]) - 1‖ ^ 2 := fun g =>
    (norm_sub_one_sq_eq g).symm
  simp only [e1] at hz
  have e2 : ∀ (u v : ℝ), 2 * u * (-(2 * v)) = -4 * (u * v) := fun u v => by ring
  simp only [e2, ← Finset.mul_sum] at hz
  linarith
section Sums
theorem sum_pow_four_le {ι : Type} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, f i ^ 4 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := s) (f := f)
  have h2 := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => f i ^ 2)
  have e : ∀ i, (f i ^ 2) ^ 2 = f i ^ 4 := fun i => by ring
  simp only [e] at h2
  calc (∑ i ∈ s, f i) ^ 4 = ((∑ i ∈ s, f i) ^ 2) ^ 2 := by ring
    _ ≤ (s.card * ∑ i ∈ s, f i ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = (s.card : ℝ) ^ 2 * (∑ i ∈ s, f i ^ 2) ^ 2 := by ring
    _ ≤ (s.card : ℝ) ^ 2 * (s.card * ∑ i ∈ s, f i ^ 4) := by gcongr
    _ = _ := by ring
theorem sum_bondsOf_eq (P : Finset Lattice4) (φ : Lattice4 × Fin 4 → ℝ) :
    ∑ b ∈ bondsOf P, φ b = ∑ y ∈ P, ∑ i : Fin 4, if (y, i) ∈ bondsOf P then φ (y, i) else 0 := by
  classical
  rw [← Finset.sum_product' (s := P) (t := Finset.univ) (f := fun y i => if (y, i) ∈ bondsOf P then φ (y, i) else 0)]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun b _ => rfl
  ext b
  simp only [Finset.mem_filter, Prod.mk.eta]
  constructor
  · intro hb
    exact ⟨(Finset.mem_filter.1 hb).1, hb⟩
  · intro hb
    exact hb.2
theorem sum_orientedPlaquettesOf_eq (P : Finset Lattice4) (φ : Lattice4 × Fin 4 × Fin 4 → ℝ) :
    ∑ p ∈ orientedPlaquettesOf P, φ p =
      ∑ y ∈ P, ∑ q : Fin 4 × Fin 4, if (y, q) ∈ orientedPlaquettesOf P then φ (y, q) else 0 := by
  classical
  rw [← Finset.sum_product' (s := P) (t := Finset.univ)
    (f := fun y q => if (y, q) ∈ orientedPlaquettesOf P then φ (y, q) else 0)]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun b _ => rfl
  ext b
  simp only [Finset.mem_filter, Prod.mk.eta]
  constructor
  · intro hb
    refine ⟨?_, hb⟩
    have := (Finset.mem_filter.1 hb).1
    simpa [Finset.mem_product] using (Finset.mem_product.1 this).1
  · intro hb
    exact hb.2
theorem fractionalIntegration_pow_four (hF : hardyLittlewoodSobolevStatement) :
    ∃ CF : ℝ, 0 < CF ∧ ∀ (D E : Finset Lattice4) (f : Lattice4 → ℝ), (∀ y, 0 ≤ f y) →
      ∑ x ∈ E, (∑ y ∈ D, cubicKernel (x - y) * f y) ^ 4 ≤ CF * (∑ y ∈ D, f y ^ 2) ^ 2 := by apply _root_.YangMills.Construction.LeastQuarticGauge.exists_lattice_l4_bound <;> assumption
theorem card_le_of_isFilledToward {l : ℕ} {c : Lattice4} {P : Finset Lattice4} (h : IsFilledToward l c P)
    (hl : 1 ≤ l) : (P.card : ℝ) ≤ (81 * (l : ℝ)) ^ 4 := by
  have hs : P ⊆ Fintype.piFinset fun i => Finset.Icc (c i - 40 * l) (c i + 40 * l) := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro i
    have := abs_le.1 (h.2.1 x hx i)
    rw [Finset.mem_Icc]
    constructor <;> linarith [this.1, this.2]
  have hc := Finset.card_le_card hs
  rw [Fintype.card_piFinset] at hc
  have e : ∀ i : Fin 4, (Finset.Icc (c i - 40 * l) (c i + 40 * l)).card = 80 * l + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  simp only [e, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hc
  have h1 : (P.card : ℝ) ≤ ((80 * l + 1 : ℕ) : ℝ) ^ 4 := by exact_mod_cast hc
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  refine le_trans h1 (pow_le_pow_left₀ (by positivity) ?_ 4)
  push_cast
  linarith
theorem supNorm_sub_le_of_isFilledToward {l : ℕ} {c : Lattice4} {P : Finset Lattice4} (h : IsFilledToward l c P)
    {x y : Lattice4} (hx : x ∈ P) (hy : y ∈ P) : supNorm (x - y) ≤ 80 * l := by
  refine Finset.sup_le fun i _ => ?_
  have h1 := abs_le.1 (h.2.1 x hx i)
  have h2 := abs_le.1 (h.2.1 y hy i)
  show ((x - y) i).natAbs ≤ 80 * l
  have e : (x - y) i = x i - y i := rfl
  rw [e]
  omega
def bondNormSum (P : Finset Lattice4) (u : Lattice4 → Fin 4 → ℍ[ℝ]) (y : Lattice4) : ℝ := by
  classical exact ∑ i : Fin 4, if (y, i) ∈ bondsOf P then ‖u y i‖ else 0
theorem bondNormSum_nonneg (P : Finset Lattice4) (u : Lattice4 → Fin 4 → ℍ[ℝ]) (y : Lattice4) :
    0 ≤ bondNormSum P u y := by
  unfold bondNormSum
  exact Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
theorem norm_kernel_sum_bonds_le {P : Finset Lattice4} {G : Lattice4 × Fin 4 → ℝ} {C : ℝ} (hC : 0 ≤ C)
    {x : Lattice4} (hG : ∀ b, |G b| ≤ C * cubicKernel (x - b.1)) (u : Lattice4 → Fin 4 → ℍ[ℝ]) :
    ‖∑ b ∈ bondsOf P, G b • u b.1 b.2‖ ≤ C * ∑ y ∈ P, cubicKernel (x - y) * bondNormSum P u y := by
  classical
  calc ‖∑ b ∈ bondsOf P, G b • u b.1 b.2‖ ≤ ∑ b ∈ bondsOf P, ‖G b • u b.1 b.2‖ := norm_sum_le _ _
    _ ≤ ∑ b ∈ bondsOf P, C * (cubicKernel (x - b.1) * ‖u b.1 b.2‖) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_smul, Real.norm_eq_abs, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hG b) (norm_nonneg _)
    _ = C * ∑ y ∈ P, cubicKernel (x - y) * bondNormSum P u y := by
        rw [sum_bondsOf_eq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        unfold bondNormSum
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
theorem sum_bondNormSum_pow_four_le (P : Finset Lattice4) (u : Lattice4 → Fin 4 → ℍ[ℝ]) :
    ∑ y ∈ P, bondNormSum P u y ^ 4 ≤ 64 * ∑ b ∈ bondsOf P, ‖u b.1 b.2‖ ^ 4 := by
  classical
  rw [sum_bondsOf_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  unfold bondNormSum
  have h := sum_pow_four_le Finset.univ (fun i : Fin 4 => if (y, i) ∈ bondsOf P then ‖u y i‖ else 0)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  refine le_trans h (le_of_eq ?_)
  norm_num
def plaquetteNormSum (P : Finset Lattice4) (c : Lattice4 × Fin 4 × Fin 4 → ℍ[ℝ]) (y : Lattice4) : ℝ := by
  classical exact ∑ q : Fin 4 × Fin 4, if (y, q) ∈ orientedPlaquettesOf P then ‖c (y, q)‖ else 0
theorem plaquetteNormSum_nonneg (P : Finset Lattice4) (c : Lattice4 × Fin 4 × Fin 4 → ℍ[ℝ]) (y : Lattice4) :
    0 ≤ plaquetteNormSum P c y := by
  unfold plaquetteNormSum
  exact Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
theorem norm_kernel_sum_plaquettes_le {P : Finset Lattice4} {H : Lattice4 × Fin 4 × Fin 4 → ℝ} {C : ℝ}
    (hC : 0 ≤ C) {x : Lattice4} (hH : ∀ p, |H p| ≤ C * cubicKernel (x - p.1)) (c : Lattice4 × Fin 4 × Fin 4 → ℍ[ℝ]) :
    ‖∑ p ∈ orientedPlaquettesOf P, H p • c p‖ ≤ C * ∑ y ∈ P, cubicKernel (x - y) * plaquetteNormSum P c y := by
  classical
  calc ‖∑ p ∈ orientedPlaquettesOf P, H p • c p‖ ≤ ∑ p ∈ orientedPlaquettesOf P, ‖H p • c p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ orientedPlaquettesOf P, C * (cubicKernel (x - p.1) * ‖c p‖) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_smul, Real.norm_eq_abs, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hH b) (norm_nonneg _)
    _ = C * ∑ y ∈ P, cubicKernel (x - y) * plaquetteNormSum P c y := by
        rw [sum_orientedPlaquettesOf_eq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        unfold plaquetteNormSum
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
theorem sum_plaquetteNormSum_sq_le (P : Finset Lattice4) (c : Lattice4 × Fin 4 × Fin 4 → ℍ[ℝ]) :
    ∑ y ∈ P, plaquetteNormSum P c y ^ 2 ≤ 16 * ∑ p ∈ orientedPlaquettesOf P, ‖c p‖ ^ 2 := by
  classical
  rw [sum_orientedPlaquettesOf_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  unfold plaquetteNormSum
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 4 × Fin 4)))
    (f := fun q => if (y, q) ∈ orientedPlaquettesOf P then ‖c (y, q)‖ else 0)
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h
  refine le_trans h (le_of_eq ?_)
  norm_num
theorem sum_bondsOf_by_endpoint (P : Finset Lattice4) (F : Lattice4 × Fin 4 → ℝ) (v : Lattice4 → ℝ) :
    ∑ b ∈ bondsOf P, F b * v (b.1 + basisVector b.2) =
      ∑ x ∈ P, (∑ i : Fin 4, if (x - basisVector i, i) ∈ bondsOf P then F (x - basisVector i, i) else 0) * v x := by
  classical
  rw [sum_bondsOf_eq]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Finset.sum_comm (s := P)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun y => y + basisVector i) (fun x => x - basisVector i) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hy
    refine Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h2).2, ?_⟩
    simpa using h2
  · intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨(Finset.mem_product.1 (Finset.mem_filter.1 h2).1).1, h2⟩
  · intro y _
    simp
  · intro x _
    simp
  · intro y _
    simp
theorem norm_sub_conj_le (g : UnitQuaternion) (w : ℍ[ℝ]) :
    ‖w - (g : ℍ[ℝ]) * w * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ * ‖w‖ := by
  have h1 : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel]
    rfl
  have e : w - (g : ℍ[ℝ]) * w * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (w * ((g : ℍ[ℝ]) - 1) - ((g : ℍ[ℝ]) - 1) * w) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    have : w = w * ((g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by rw [h1, mul_one]
    calc w - (g : ℍ[ℝ]) * w * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
        w * ((g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) - (g : ℍ[ℝ]) * w * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
          rw [← this]
      _ = _ := by noncomm_ring
  rw [e, norm_mul, norm_coe_unitQuaternion, mul_one]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_mul, norm_mul]
  linarith
theorem re_sum_smul_eq_zero {ι : Type} (s : Finset ι) (c : ι → ℝ) (q : ι → ℍ[ℝ]) (hq : ∀ i ∈ s, (q i).re = 0) :
    (∑ i ∈ s, c i • q i).re = 0 := by
  have e : ∑ i ∈ s, c i • q i = pureComponent (∑ i ∈ s, c i • q i) := by
    rw [pureComponent_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [pureComponent_smul, pureComponent_of_re_eq_zero (hq i hi)]
  rw [e]
  exact re_pureComponent _
end Sums
theorem quartic_variation_lower_bound (g : UnitQuaternion) (h1 : ‖(g : ℍ[ℝ]) - 1‖ ^ 4 ≤ 1) (f r : ℝ) (hf : 0 ≤ f)
    (hr : |r| ≤ f * ‖pureComponent (g : ℍ[ℝ])‖) :
    3 / 8 * ‖(g : ℍ[ℝ]) - 1‖ ^ 4 - 2 * f ^ 4 ≤
      ‖(g : ℍ[ℝ]) - 1‖ ^ 2 * (‖pureComponent (g : ℍ[ℝ])‖ ^ 2 - r) := by
  set a := ‖(g : ℍ[ℝ]) - 1‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have ha2 : a ^ 2 ≤ 1 := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hp := norm_pureComponent_sq_eq g
  rw [← ha] at hp
  have hp2 := norm_pureComponent_le_norm_sub_one g
  rw [← ha] at hp2
  have hr2 : r ≤ f * a := le_trans (le_abs_self r)
    (le_trans hr (mul_le_mul_of_nonneg_left hp2 hf))
  have hy := pow_three_mul_le_of_young ha0 hf
  have e1 : a ^ 2 * ‖pureComponent (g : ℍ[ℝ])‖ ^ 2 ≥ 3 / 4 * a ^ 4 := by
    rw [hp]
    nlinarith [sq_nonneg a, mul_nonneg (sq_nonneg a) (sq_nonneg a)]
  have e2 : a ^ 2 * r ≤ a ^ 3 * f := by
    have := mul_le_mul_of_nonneg_left hr2 (sq_nonneg a)
    calc a ^ 2 * r ≤ a ^ 2 * (f * a) := this
      _ = a ^ 3 * f := by ring
  nlinarith
set_option maxHeartbeats 4000000 in
theorem pinnedQuarticGauge_holds (hH : randomStaircaseHomotopyStatement) (hF : hardyLittlewoodSobolevStatement)
    (hT : cubicKernelTraceStatement) : pinnedQuarticGaugeStatement := by
  classical
  intro θ C₂ C₃ n₀ n₁ r₀ hθ hC₂ hC₃ hn₀ hn₁ hr₀
  obtain ⟨C, hC, hHom⟩ := hH
  obtain ⟨CF, hCF, hFr⟩ := fractionalIntegration_pow_four hF
  obtain ⟨CT, hCT, hTr⟩ := hT θ hθ
  set Ch : ℝ := 1024 * C ^ 4 * CF with hCh
  set M : ℝ := C ^ 4 * CF * 81 ^ 4 * r₀ ^ 4 * 64 with hM
  set Cω : ℝ := 128 * (C ^ 4 * CT * 64 + 8 * (1 + M)) with hCω
  set Cd : ℝ := 16 / 3 * (8 * Ch + 64 * n₁ * n₀ * (C₂ + C₃ * Ch)) with hCd
  set CA : ℝ := 16 / 3 * (8 * Cω) with hCA
  set Cη : ℝ := 16 / 3 * (8 * Ch + 64 * n₁ * (9 * M + 8) + 64 * n₁ * n₀ * (1 + C₃ * Ch)) with hCη
  have hCh0 : 0 < Ch := by positivity
  have hM0 : 0 ≤ M := by positivity
  have hCA0 : 0 < CA := by positivity
  have hCη0 : 0 < Cη := by positivity
  refine ⟨2 * Cd + 1, min 1 (1 / (2 * (CA + Cη))), by positivity, by positivity, ?_⟩
  intro D A η b c₁ d hA hAc hη hηc hb hb1 hbc hd h
  obtain ⟨γ, hγb, hvar⟩ := exists_minimizer_firstVariation h hbc
  refine ⟨γ, hγb, ?_⟩
  obtain ⟨H, G, hHb, hGb, hEq⟩ := hHom D.scale D.corner D.region h.one_le_scale h.isFilled
  obtain ⟨hG1, hH1, -⟩ := hEq ℍ[ℝ]
  set u := D.defectForm γ with hu
  have hupure : ∀ x i, (u x i).re = 0 := fun x i => re_pureComponent _
  set E := D.defectQuarticSum γ with hE
  set Ek := ∑ y ∈ D.cells, ‖((D.pin γ y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 with hEk
  set Ψ := D.pinnedQuarticSum γ with hΨ
  have hΨE : Ψ = E + Ek := rfl
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun b _ => by positivity
  have hEk0 : 0 ≤ Ek := Finset.sum_nonneg fun b _ => by positivity
  have hΨ0 : 0 ≤ Ψ := by rw [hΨE]; positivity
  have hΨ1 : Ψ ≤ 1 := le_trans hγb hb1
  have huE : ∑ b ∈ bondsOf D.region, ‖u b.1 b.2‖ ^ 4 ≤ E := by
    refine Finset.sum_le_sum fun b _ => pow_le_pow_left₀ (norm_nonneg _) (norm_pureComponent_le_norm_sub_one _) 4
  let ξL : Lattice4 → ℍ[ℝ] := fun x => ∑ b ∈ bondsOf D.region, G x b • u b.1 b.2
  have hξLre : ∀ x, (ξL x).re = 0 := fun x => re_sum_smul_eq_zero _ _ _ fun b _ => hupure _ _
  have hN0 : (0 : ℝ) < D.cellSide := by exact_mod_cast h.one_le_cellSide
  have hl1 : (1 : ℝ) ≤ D.scale := by exact_mod_cast h.one_le_scale
  set c0 : ℍ[ℝ] := pureComponent ((D.pin γ D.base : UnitQuaternion) : ℍ[ℝ]) - D.cellMean D.base ξL with hc0
  have hmean_re : ∀ y (φ : Lattice4 → ℍ[ℝ]), (∀ x, (φ x).re = 0) → (D.cellMean y φ).re = 0 := by
    intro y φ hφ
    unfold PinnedGaugeData.cellMean
    rw [Finset.smul_sum]
    exact re_sum_smul_eq_zero _ _ _ fun x _ => hφ x
  have hc0re : c0.re = 0 := by
    rw [hc0, Quaternion.re_sub, re_pureComponent, hmean_re _ _ hξLre, sub_zero]
  let ξ : Lattice4 → imaginaryQuaternions := fun x => ⟨ξL x + c0, by
    show (ξL x + c0).re = 0
    rw [Quaternion.re_add, hξLre, hc0re, add_zero]⟩
  have hξ : ∀ x, (ξ x : ℍ[ℝ]) = ξL x + c0 := fun x => rfl
  have hbP : ∀ b ∈ bondsOf D.region, b.1 ∈ D.region ∧ b.1 + basisVector b.2 ∈ D.region := fun b hb =>
    ⟨(Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1, (Finset.mem_filter.1 hb).2⟩
  let cc : Lattice4 × Fin 4 × Fin 4 → ℍ[ℝ] := fun p => plaquetteCurl u p.1 p.2.1 p.2.2
  let hh : Lattice4 × Fin 4 → ℍ[ℝ] := fun b => ∑ p ∈ orientedPlaquettesOf D.region, H b p • cc p
  have hdiff : ∀ b ∈ bondsOf D.region,
      (ξ b.1 : ℍ[ℝ]) - (ξ (b.1 + basisVector b.2) : ℍ[ℝ]) = u b.1 b.2 - hh b := by
    intro b hb
    obtain ⟨h1, h2⟩ := hbP b hb
    have e := hH1 u b.1 b.2 h1 h2
    rw [hG1 u _ h1, hG1 u _ h2] at e
    have e' : hh b = u b.1 b.2 + (ξL (b.1 + basisVector b.2) - ξL b.1) := e.symm
    rw [hξ, hξ, e']
    abel
  set Sc := ∑ p ∈ orientedPlaquettesOf D.region, ‖plaquetteCurl u p.1 p.2.1 p.2.2‖ ^ 2 with hSc
  set Hs := ∑ b ∈ bondsOf D.region, ‖hh b‖ ^ 4 with hHs
  have hHsle : Hs ≤ Ch * Sc ^ 2 := by
    let f2 := plaquetteNormSum D.region cc
    let t : Lattice4 → ℝ := fun x => ∑ y ∈ D.region, cubicKernel (x - y) * f2 y
    have ht0 : ∀ x, 0 ≤ t x := fun x => Finset.sum_nonneg fun y _ =>
      mul_nonneg (by unfold cubicKernel; positivity) (plaquetteNormSum_nonneg _ _ _)
    have h1 : ∀ x i, ‖hh (x, i)‖ ≤ C * t x := fun x i =>
      norm_kernel_sum_plaquettes_le hC.le (fun p => hHb (x, i) p) cc
    have h2 : Hs ≤ ∑ x ∈ D.region, 4 * (C * t x) ^ 4 := by
      rw [hHs, sum_bondsOf_eq]
      refine Finset.sum_le_sum fun x _ => ?_
      calc ∑ i : Fin 4, (if (x, i) ∈ bondsOf D.region then ‖hh (x, i)‖ ^ 4 else 0)
          ≤ ∑ i : Fin 4, (C * t x) ^ 4 := by
            refine Finset.sum_le_sum fun i _ => ?_
            split_ifs
            · exact pow_le_pow_left₀ (norm_nonneg _) (h1 x i) 4
            · positivity
        _ = 4 * (C * t x) ^ 4 := by simp
    have h3 := hFr D.region D.region f2 (fun y => plaquetteNormSum_nonneg _ _ _)
    have h4 : ∑ y ∈ D.region, f2 y ^ 2 ≤ 16 * Sc := sum_plaquetteNormSum_sq_le D.region cc
    have h5 : (∑ y ∈ D.region, f2 y ^ 2) ^ 2 ≤ (16 * Sc) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) h4 2
    calc Hs ≤ ∑ x ∈ D.region, 4 * (C * t x) ^ 4 := h2
      _ = 4 * C ^ 4 * ∑ x ∈ D.region, t x ^ 4 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ ≤ 4 * C ^ 4 * (CF * (16 * Sc) ^ 2) := by
          refine mul_le_mul_of_nonneg_left (le_trans h3 ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left h5 hCF.le
      _ = Ch * Sc ^ 2 := by rw [hCh]; ring
  have hScle : Sc ^ 2 ≤ d γ ^ 4 + η ^ 4 * Ψ := h.curl_le γ hγb
  let f1 := bondNormSum D.region u
  have hf10 : ∀ y, 0 ≤ f1 y := fun y => bondNormSum_nonneg _ _ _
  let s : Lattice4 → ℝ := fun x => ∑ y ∈ D.region, cubicKernel (x - y) * f1 y
  have hs0 : ∀ x, 0 ≤ s x := fun x => Finset.sum_nonneg fun y _ =>
    mul_nonneg (by unfold cubicKernel; positivity) (hf10 y)
  have hξLs : ∀ x, ‖ξL x‖ ^ 4 ≤ C ^ 4 * s x ^ 4 := by
    intro x
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_kernel_sum_bonds_le hC.le (fun b => hGb x b) u) 4
  have hf1E : ∑ y ∈ D.region, f1 y ^ 4 ≤ 64 * E :=
    le_trans (sum_bondNormSum_pow_four_le D.region u) (by linarith)
  set SP := ∑ x ∈ D.region, ‖ξL x‖ ^ 4 with hSP
  have hN4 : (0 : ℝ) < (D.cellSide : ℝ) ^ 4 := by positivity
  have hSPle : SP ≤ M * (D.cellSide : ℝ) ^ 4 * E := by
    have h3 := hFr D.region D.region f1 hf10
    have h4 := sq_sum_le_card_mul_sum_sq (s := D.region) (f := fun y => f1 y ^ 2)
    have e : ∀ y, (f1 y ^ 2) ^ 2 = f1 y ^ 4 := fun y => by ring
    simp only [e] at h4
    have hcard := card_le_of_isFilledToward h.isFilled h.one_le_scale
    have hlN : (D.scale : ℝ) ^ 4 ≤ r₀ ^ 4 * (D.cellSide : ℝ) ^ 4 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h.scale_le 4
    have hcard2 : (D.region.card : ℝ) ≤ 81 ^ 4 * (r₀ ^ 4 * (D.cellSide : ℝ) ^ 4) := by
      refine le_trans hcard ?_
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hlN (by positivity)
    calc SP ≤ ∑ x ∈ D.region, C ^ 4 * s x ^ 4 := Finset.sum_le_sum fun x _ => hξLs x
      _ = C ^ 4 * ∑ x ∈ D.region, s x ^ 4 := by rw [Finset.mul_sum]
      _ ≤ C ^ 4 * (CF * (D.region.card * ∑ y ∈ D.region, f1 y ^ 4)) := by
          refine mul_le_mul_of_nonneg_left (le_trans h3 ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left h4 hCF.le
      _ ≤ C ^ 4 * (CF * ((81 ^ 4 * (r₀ ^ 4 * (D.cellSide : ℝ) ^ 4)) * (64 * E))) := by
          gcongr
      _ = M * (D.cellSide : ℝ) ^ 4 * E := by rw [hM]; ring
  have hw0 : ∀ x, 0 ≤ D.targetWeight x := fun x => by
    unfold PinnedGaugeData.targetWeight
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
  have hl80 : 1 ≤ 80 * D.scale := by have := h.one_le_scale; omega
  have hSw : ∑ x ∈ D.region, D.targetWeight x * ‖ξL x‖ ^ 4 ≤ C ^ 4 * (CT * A * (64 * E)) := by
    have h3 := hTr D.region D.region D.targetWeight f1 A (80 * D.scale) hl80 hA hw0 hf10
      (fun x hx y hy => supNorm_sub_le_of_isFilledToward h.isFilled hx hy) h.morrey_bound
    calc ∑ x ∈ D.region, D.targetWeight x * ‖ξL x‖ ^ 4 ≤ ∑ x ∈ D.region, D.targetWeight x * (C ^ 4 * s x ^ 4) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hξLs x) (hw0 x)
      _ = C ^ 4 * ∑ x ∈ D.region, D.targetWeight x * s x ^ 4 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ ≤ C ^ 4 * (CT * A * (64 * E)) := by
          refine mul_le_mul_of_nonneg_left (le_trans h3 ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left hf1E (by positivity)
  have hWs : ∑ x ∈ D.region, D.targetWeight x ≤ A := by
    have h3 := h.morrey_bound D.corner (80 * D.scale) hl80 le_rfl
    have e : D.region.filter (fun u => supNorm (u - D.corner) ≤ 80 * D.scale) = D.region := by
      refine Finset.filter_true_of_mem fun x hx => ?_
      refine Finset.sup_le fun i _ => ?_
      have h1 := abs_le.1 (h.isFilled.2.1 x hx i)
      show ((x - D.corner) i).natAbs ≤ 80 * D.scale
      have e : (x - D.corner) i = x i - D.corner i := rfl
      rw [e]
      omega
    rw [e] at h3
    have hR : (0 : ℝ) < ((80 * D.scale : ℕ) : ℝ) := by exact_mod_cast hl80
    rwa [div_self hR.ne', Real.one_rpow, mul_one] at h3
  have hmean_le : ∀ y ∈ D.cells, ∀ φ : Lattice4 → ℍ[ℝ],
      ‖D.cellMean y φ‖ ^ 4 ≤ (∑ x ∈ D.cellSites y, ‖φ x‖ ^ 4) / (D.cellSide : ℝ) ^ 4 := by
    intro y hy φ
    unfold PinnedGaugeData.cellMean
    have hc : ((D.cellSites y).card : ℝ) = (D.cellSide : ℝ) ^ 4 := by
      rw [h.card_cellSites y hy]; push_cast; rfl
    have h1 : ‖(1 / (D.cellSide : ℝ) ^ 4) • ∑ x ∈ D.cellSites y, φ x‖ ≤
        (1 / (D.cellSide : ℝ) ^ 4) * ∑ x ∈ D.cellSites y, ‖φ x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    have h2 := sum_pow_four_le (D.cellSites y) (fun x => ‖φ x‖)
    rw [hc] at h2
    calc ‖(1 / (D.cellSide : ℝ) ^ 4) • ∑ x ∈ D.cellSites y, φ x‖ ^ 4 ≤
          ((1 / (D.cellSide : ℝ) ^ 4) * ∑ x ∈ D.cellSites y, ‖φ x‖) ^ 4 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 4
      _ = (1 / (D.cellSide : ℝ) ^ 4) ^ 4 * (∑ x ∈ D.cellSites y, ‖φ x‖) ^ 4 := by ring
      _ ≤ (1 / (D.cellSide : ℝ) ^ 4) ^ 4 * (((D.cellSide : ℝ) ^ 4) ^ 3 * ∑ x ∈ D.cellSites y, ‖φ x‖ ^ 4) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by field_simp
  have hBSP : ∀ y ∈ D.cells, ∑ x ∈ D.cellSites y, ‖ξL x‖ ^ 4 ≤ SP := fun y hy =>
    Finset.sum_le_sum_of_subset_of_nonneg (h.cellSites_subset y hy) fun _ _ _ => by positivity
  have hME : SP / (D.cellSide : ℝ) ^ 4 ≤ M * E := by
    rw [div_le_iff₀ hN4]
    linarith
  have hc0le : ‖c0‖ ^ 4 ≤ 8 * (1 + M) * Ψ := by
    have h1 : ‖pureComponent ((D.pin γ D.base : UnitQuaternion) : ℍ[ℝ])‖ ^ 4 ≤ Ek := by
      refine le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_pureComponent_le_norm_sub_one _) 4) ?_
      exact Finset.single_le_sum (f := fun y => ‖((D.pin γ y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4)
        (fun _ _ => by positivity) h.base_mem
    have h2 : ‖D.cellMean D.base ξL‖ ^ 4 ≤ M * E := by
      refine le_trans (hmean_le _ h.base_mem ξL) (le_trans ?_ hME)
      exact div_le_div_of_nonneg_right (hBSP _ h.base_mem) hN4.le
    have h3 : ‖c0‖ ≤ ‖pureComponent ((D.pin γ D.base : UnitQuaternion) : ℍ[ℝ])‖ + ‖D.cellMean D.base ξL‖ :=
      norm_sub_le _ _
    calc ‖c0‖ ^ 4 ≤ (‖pureComponent ((D.pin γ D.base : UnitQuaternion) : ℍ[ℝ])‖ + ‖D.cellMean D.base ξL‖) ^ 4 :=
          pow_le_pow_left₀ (norm_nonneg _) h3 4
      _ ≤ 8 * (‖pureComponent ((D.pin γ D.base : UnitQuaternion) : ℍ[ℝ])‖ ^ 4 + ‖D.cellMean D.base ξL‖ ^ 4) :=
          add_pow_four_le _ _
      _ ≤ 8 * (Ek + M * E) := by linarith
      _ ≤ 8 * (1 + M) * Ψ := by
          have h4 : M * E ≤ M * Ψ := mul_le_mul_of_nonneg_left (by rw [hΨE]; linarith) hM0
          have h5 : Ek ≤ Ψ := by rw [hΨE]; linarith
          nlinarith
  have hξ4 : ∀ x, ‖(ξ x : ℍ[ℝ])‖ ^ 4 ≤ 8 * (‖ξL x‖ ^ 4 + ‖c0‖ ^ 4) := by
    intro x
    rw [hξ]
    exact le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 4) (add_pow_four_le _ _)
  let ω : Lattice4 × Fin 4 → ℍ[ℝ] := fun b => (ξ (b.1 + basisVector b.2) : ℍ[ℝ]) -
    ((D.target b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) * (ξ (b.1 + basisVector b.2) : ℍ[ℝ]) *
      (((D.target b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])
  set Sω := ∑ b ∈ bondsOf D.region, ‖ω b‖ ^ 4 with hSω
  have hSωle : Sω ≤ A * Cω * Ψ := by
    have h1 : ∀ b, ‖ω b‖ ^ 4 ≤ 16 * (‖((D.target b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 *
        ‖(ξ (b.1 + basisVector b.2) : ℍ[ℝ])‖ ^ 4) := by
      intro b
      have := pow_le_pow_left₀ (norm_nonneg _)
        (norm_sub_conj_le (D.target b.1 b.2) (ξ (b.1 + basisVector b.2) : ℍ[ℝ])) 4
      refine le_trans this (le_of_eq ?_)
      ring
    have h2 := sum_bondsOf_by_endpoint D.region
      (fun b => ‖((D.target b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4) (fun x => ‖(ξ x : ℍ[ℝ])‖ ^ 4)
    have h3 : ∑ x ∈ D.region, D.targetWeight x * ‖(ξ x : ℍ[ℝ])‖ ^ 4 ≤
        8 * (C ^ 4 * (CT * A * (64 * E)) + A * ‖c0‖ ^ 4) := by
      calc ∑ x ∈ D.region, D.targetWeight x * ‖(ξ x : ℍ[ℝ])‖ ^ 4
          ≤ ∑ x ∈ D.region, D.targetWeight x * (8 * (‖ξL x‖ ^ 4 + ‖c0‖ ^ 4)) :=
            Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hξ4 x) (hw0 x)
        _ = 8 * (∑ x ∈ D.region, D.targetWeight x * ‖ξL x‖ ^ 4 +
            (∑ x ∈ D.region, D.targetWeight x) * ‖c0‖ ^ 4) := by
            rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
        _ ≤ 8 * (C ^ 4 * (CT * A * (64 * E)) + A * ‖c0‖ ^ 4) := by
            gcongr
    have hEΨ : E ≤ Ψ := by rw [hΨE]; linarith
    calc Sω ≤ ∑ b ∈ bondsOf D.region, 16 * (‖((D.target b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 *
          ‖(ξ (b.1 + basisVector b.2) : ℍ[ℝ])‖ ^ 4) :=
          Finset.sum_le_sum fun b _ => h1 b
      _ = 16 * ∑ x ∈ D.region, D.targetWeight x * ‖(ξ x : ℍ[ℝ])‖ ^ 4 := by
          rw [← Finset.mul_sum, h2]
          rfl
      _ ≤ 16 * (8 * (C ^ 4 * (CT * A * (64 * E)) + A * ‖c0‖ ^ 4)) := by linarith
      _ ≤ 16 * (8 * (C ^ 4 * (CT * A * (64 * Ψ)) + A * (8 * (1 + M) * Ψ))) := by
          gcongr
      _ = A * Cω * Ψ := by rw [hCω]; ring
  have hder := h.pin_hasDerivAt γ hγb ξ
  choose! ζ hζ using hder
  have hv := hvar ξ ζ (fun y hy => (hζ y hy).2.1)
  have hξre : ∀ x, (ξ x : ℍ[ℝ]).re = 0 := fun x => (ξ x).2
  have hbond : ∀ b ∈ bondsOf D.region,
      ((ξ b.1 : ℍ[ℝ]) * ((D.defect γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) -
        ((D.defect γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) *
        (((D.target b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) * (ξ (b.1 + basisVector b.2) : ℍ[ℝ]) *
          (((D.target b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]))).re =
      - ‖u b.1 b.2‖ ^ 2 + ((ω b - hh b) * u b.1 b.2).re := by
    intro b hb
    rw [re_commutator_variation (hξre _) (re_conj_eq_zero _ (hξre _))]
    have e : (ξ b.1 : ℍ[ℝ]) - ((D.target b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) * (ξ (b.1 + basisVector b.2) : ℍ[ℝ]) *
        (((D.target b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = u b.1 b.2 + (ω b - hh b) := by
      have := hdiff b hb
      show _ = u b.1 b.2 + ((ξ (b.1 + basisVector b.2) : ℍ[ℝ]) - _ - hh b)
      rw [show (ξ b.1 : ℍ[ℝ]) = u b.1 b.2 - hh b + (ξ (b.1 + basisVector b.2) : ℍ[ℝ]) by rw [← this]; abel]
      abel
    rw [e]
    show ((u b.1 b.2 + (ω b - hh b)) * u b.1 b.2).re = _
    rw [add_mul, Quaternion.re_add, re_mul_self_of_re_eq_zero (hupure _ _)]
  let pK : D.CellIndex → ℍ[ℝ] := fun y => pureComponent ((D.pin γ y : UnitQuaternion) : ℍ[ℝ])
  have hpKre : ∀ y, (pK y).re = 0 := fun y => re_pureComponent _
  have hcell : ∀ y ∈ D.cells, (ζ y * ((D.pin γ y : UnitQuaternion) : ℍ[ℝ])).re =
      - ‖pK y‖ ^ 2 + ((ζ y - pK y) * pK y).re := by
    intro y hy
    rw [re_mul_pureComponent (hζ y hy).1]
    show (ζ y * pK y).re = _
    have e : ζ y = pK y + (ζ y - pK y) := by abel
    conv_lhs => rw [e]
    rw [add_mul, Quaternion.re_add, re_mul_self_of_re_eq_zero (hpKre y)]
  replace hv : ∑ b ∈ bondsOf D.region, ‖((D.defect γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 *
        (- ‖u b.1 b.2‖ ^ 2 + ((ω b - hh b) * u b.1 b.2).re) +
      ∑ y ∈ D.cells, ‖((D.pin γ y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 *
        (- ‖pK y‖ ^ 2 + ((ζ y - pK y) * pK y).re) = 0 := by
    refine Eq.trans ?_ hv
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun b hb => by rw [hbond b hb])
      (Finset.sum_congr rfl fun y hy => by rw [hcell y hy])
  have hsmall := quartic_variation_lower_bound
  have hrb : ∀ b, |((ω b - hh b) * u b.1 b.2).re| ≤ ‖ω b - hh b‖ * ‖u b.1 b.2‖ := fun b =>
    abs_re_mul_le_norm_mul _ _
  have hry : ∀ y, |((ζ y - pK y) * pK y).re| ≤ ‖ζ y - pK y‖ * ‖pK y‖ := fun y => abs_re_mul_le_norm_mul _ _
  have hEle1 : ∀ b ∈ bondsOf D.region, ‖((D.defect γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 ≤ 1 := by
    intro b hb
    have h1 := Finset.single_le_sum
      (f := fun b : Lattice4 × Fin 4 => ‖((D.defect γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4)
      (fun _ _ => by positivity) hb
    have : D.defectQuarticSum γ ≤ Ψ := by rw [hΨE]; linarith
    exact le_trans h1 (le_trans this hΨ1)
  have hKle1 : ∀ y ∈ D.cells, ‖((D.pin γ y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 ≤ 1 := by
    intro y hy
    have h1 := Finset.single_le_sum (f := fun y => ‖((D.pin γ y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4)
      (fun _ _ => by positivity) hy
    have : Ek ≤ Ψ := by rw [hΨE]; linarith
    exact le_trans h1 (le_trans this hΨ1)
  set Sfb := ∑ b ∈ bondsOf D.region, ‖ω b - hh b‖ ^ 4 with hSfb
  set Sfy := ∑ y ∈ D.cells, ‖ζ y - pK y‖ ^ 4 with hSfy
  have hΨle : Ψ ≤ 16 / 3 * (Sfb + Sfy) := by
    have h1 : 3 / 8 * E - 2 * Sfb ≤ ∑ b ∈ bondsOf D.region,
        ‖((D.defect γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 *
        (‖u b.1 b.2‖ ^ 2 - ((ω b - hh b) * u b.1 b.2).re) := by
      rw [hE, hSfb]
      unfold PinnedGaugeData.defectQuarticSum
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun b hb => hsmall _ (hEle1 b hb) _ _ (norm_nonneg _) (hrb b)
    have h2 : 3 / 8 * Ek - 2 * Sfy ≤ ∑ y ∈ D.cells, ‖((D.pin γ y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 *
        (‖pK y‖ ^ 2 - ((ζ y - pK y) * pK y).re) := by
      rw [hEk, hSfy, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun y hy => hsmall _ (hKle1 y hy) _ _ (norm_nonneg _) (hry y)
    have h3 : ∑ b ∈ bondsOf D.region, ‖((D.defect γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 *
          (‖u b.1 b.2‖ ^ 2 - ((ω b - hh b) * u b.1 b.2).re) +
        ∑ y ∈ D.cells, ‖((D.pin γ y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 *
          (‖pK y‖ ^ 2 - ((ζ y - pK y) * pK y).re) = 0 := by
      have e : ∀ a p r : ℝ, a * (p - r) = - (a * (- p + r)) := fun a p r => by ring
      simp only [e, Finset.sum_neg_distrib]
      linarith
    rw [hΨE]
    linarith
  have hSfble : Sfb ≤ 8 * (Sω + Hs) := by
    rw [hSfb, hSω, hHs, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    exact le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 4) (add_pow_four_le _ _)
  let ξq : Lattice4 → ℍ[ℝ] := fun x => (ξ x : ℍ[ℝ])
  let κ : D.CellIndex → ℍ[ℝ] := fun y => D.cellMean y ξq - pK y
  have hmean_add : ∀ y ∈ D.cells, D.cellMean y ξq = D.cellMean y ξL + c0 := by
    intro y hy
    unfold PinnedGaugeData.cellMean
    have hc : ((D.cellSites y).card : ℝ) = (D.cellSide : ℝ) ^ 4 := by
      rw [h.card_cellSites y hy]; push_cast; rfl
    have e : ∑ x ∈ D.cellSites y, ξq x = ∑ x ∈ D.cellSites y, ξL x + ((D.cellSites y).card : ℝ) • c0 := by
      simp only [ξq, hξ]
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.cast_smul_eq_nsmul]
    rw [e, smul_add, hc, smul_smul]
    have : 1 / (D.cellSide : ℝ) ^ 4 * (D.cellSide : ℝ) ^ 4 = 1 := by field_simp
    rw [this, one_smul]
  have hκz : κ D.base = 0 := by
    show D.cellMean D.base ξq - pK D.base = 0
    rw [hmean_add _ h.base_mem, hc0]
    show D.cellMean D.base ξL + (pK D.base - D.cellMean D.base ξL) - pK D.base = 0
    abel
  set T := 8 * (C₂ * d γ ^ 4 + η ^ 4 * Ψ + C₃ * Hs) with hT
  have hT0 : 0 ≤ T := by
    have := hd γ
    positivity
  have hadj : ∀ y ∈ D.cells, ∀ y' ∈ D.cells, D.Adj y y' → ‖κ y - κ y'‖ ^ 4 ≤ T := by
    intro y hy y' hy' hyy
    let hf : Lattice4 → Fin 4 → ℍ[ℝ] := fun x i => hh (x, i)
    have hAv0 : D.bondAverage y y' 0 = 0 := by
      have h1 := h.bondAverage_difference y hy y' hy' hyy 0
      have e0 : latticeDifference (0 : Lattice4 → ℍ[ℝ]) = 0 := by
        funext x i
        simp [latticeDifference]
      rw [e0] at h1
      rw [h1]
      simp [PinnedGaugeData.cellMean]
    have hneg : D.bondAverage y y' (-u) = - D.bondAverage y y' u := by
      have h1 := h.bondAverage_add y hy y' hy' hyy u (-u)
      rw [add_neg_cancel, hAv0] at h1
      exact (neg_eq_of_add_eq_zero_right h1.symm).symm
    have h1 : D.bondAverage y y' (latticeDifference ξq) = D.bondAverage y y' (-u + hf) := by
      refine h.bondAverage_congr y hy y' hy' hyy _ _ fun b hb => ?_
      have := hdiff b hb
      show ξq (b.1 + basisVector b.2) - ξq b.1 = - u b.1 b.2 + hh (b.1, b.2)
      have e : ξq b.1 - ξq (b.1 + basisVector b.2) = u b.1 b.2 - hh b := this
      rw [show ξq (b.1 + basisVector b.2) - ξq b.1 = - (ξq b.1 - ξq (b.1 + basisVector b.2)) by abel, e]
      simp only [Prod.mk.eta]
      abel
    rw [h.bondAverage_difference y hy y' hy' hyy, h.bondAverage_add y hy y' hy' hyy, hneg] at h1
    have e : κ y - κ y' = - (pK y - pK y' - D.bondAverage y y' u) - D.bondAverage y y' hf := by
      show D.cellMean y ξq - pK y - (D.cellMean y' ξq - pK y') = _
      have e2 : D.cellMean y ξq = D.cellMean y' ξq + D.bondAverage y y' u - D.bondAverage y y' hf := by
        rw [show D.cellMean y' ξq = D.cellMean y ξq + (D.cellMean y' ξq - D.cellMean y ξq) by abel, h1]
        abel
      rw [e2]
      abel
    rw [e]
    have h2 := h.pin_sub_le γ hγb y hy y' hy' hyy
    have h3 := h.bondAverage_le y hy y' hy' hyy hf
    calc ‖- (pK y - pK y' - D.bondAverage y y' u) - D.bondAverage y y' hf‖ ^ 4
        ≤ (‖pK y - pK y' - D.bondAverage y y' u‖ + ‖D.bondAverage y y' hf‖) ^ 4 := by
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 4
          refine le_trans (norm_sub_le _ _) ?_
          rw [norm_neg]
      _ ≤ 8 * (‖pK y - pK y' - D.bondAverage y y' u‖ ^ 4 + ‖D.bondAverage y y' hf‖ ^ 4) := add_pow_four_le _ _
      _ ≤ T := by
          rw [hT]
          have h4 : ‖pK y - pK y' - D.bondAverage y y' u‖ ^ 4 ≤ C₂ * d γ ^ 4 + η ^ 4 * Ψ := h2
          have h5 : ‖D.bondAverage y y' hf‖ ^ 4 ≤ C₃ * Hs := h3
          linarith
  have hκ := h.chain_bound κ T hT0 hadj hκz
  have hy1 : ∀ y ∈ D.cells, ‖ζ y - pK y‖ ^ 4 ≤ 8 * (η ^ 4 * (8 * (9 * M + 8) * Ψ) + n₀ * T) := by
    intro y hy
    have e : ζ y - pK y = (ζ y - D.cellMean y ξq) + κ y := by
      show _ = (ζ y - D.cellMean y ξq) + (D.cellMean y ξq - pK y)
      abel
    have h1 : ‖ζ y - D.cellMean y ξq‖ ^ 4 ≤ η ^ 4 * (8 * (9 * M + 8) * Ψ) := by
      refine le_trans (hζ y hy).2.2 ?_
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [div_le_iff₀ hN4]
      have h2 : ∑ x ∈ D.cellSites y, ‖(ξ x : ℍ[ℝ])‖ ^ 4 ≤ 8 * (SP + (D.cellSide : ℝ) ^ 4 * ‖c0‖ ^ 4) := by
        have hc : ((D.cellSites y).card : ℝ) = (D.cellSide : ℝ) ^ 4 := by
          rw [h.card_cellSites y hy]; push_cast; rfl
        calc ∑ x ∈ D.cellSites y, ‖(ξ x : ℍ[ℝ])‖ ^ 4 ≤ ∑ x ∈ D.cellSites y, 8 * (‖ξL x‖ ^ 4 + ‖c0‖ ^ 4) :=
              Finset.sum_le_sum fun x _ => hξ4 x
          _ = 8 * (∑ x ∈ D.cellSites y, ‖ξL x‖ ^ 4 + (D.cellSide : ℝ) ^ 4 * ‖c0‖ ^ 4) := by
              rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hc]
          _ ≤ _ := by
              have := hBSP y hy
              linarith
      have h3 : SP ≤ M * (D.cellSide : ℝ) ^ 4 * Ψ := by
        refine le_trans hSPle (mul_le_mul_of_nonneg_left (by rw [hΨE]; linarith) (by positivity))
      have h4 : (D.cellSide : ℝ) ^ 4 * ‖c0‖ ^ 4 ≤ (D.cellSide : ℝ) ^ 4 * (8 * (1 + M) * Ψ) :=
        mul_le_mul_of_nonneg_left hc0le hN4.le
      calc _ ≤ 8 * (SP + (D.cellSide : ℝ) ^ 4 * ‖c0‖ ^ 4) := h2
        _ ≤ 8 * (M * (D.cellSide : ℝ) ^ 4 * Ψ + (D.cellSide : ℝ) ^ 4 * (8 * (1 + M) * Ψ)) := by linarith
        _ = _ := by ring
    rw [e]
    refine le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 4) (le_trans (add_pow_four_le _ _) ?_)
    have h5 := hκ y hy
    linarith
  have hSfyle : Sfy ≤ n₁ * (8 * (η ^ 4 * (8 * (9 * M + 8) * Ψ) + n₀ * T)) := by
    have h0 : 0 ≤ 8 * (η ^ 4 * (8 * (9 * M + 8) * Ψ) + n₀ * T) := by positivity
    calc Sfy ≤ ∑ y ∈ D.cells, 8 * (η ^ 4 * (8 * (9 * M + 8) * Ψ) + n₀ * T) := Finset.sum_le_sum hy1
      _ = (D.cells.card : ℝ) * (8 * (η ^ 4 * (8 * (9 * M + 8) * Ψ) + n₀ * T)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right h.card_cells_le h0
  have hHs2 : Hs ≤ Ch * (d γ ^ 4 + η ^ 4 * Ψ) := le_trans hHsle (mul_le_mul_of_nonneg_left hScle hCh0.le)
  have hfin : Ψ ≤ Cd * d γ ^ 4 + CA * A * Ψ + Cη * η ^ 4 * Ψ := by
    have h1 : Ψ ≤ 16 / 3 * (8 * (A * Cω * Ψ + Hs) +
        n₁ * (8 * (η ^ 4 * (8 * (9 * M + 8) * Ψ) + n₀ * (8 * (C₂ * d γ ^ 4 + η ^ 4 * Ψ + C₃ * Hs))))) := by
      refine le_trans hΨle ?_
      have h2 : Sfb + Sfy ≤ 8 * (A * Cω * Ψ + Hs) +
          n₁ * (8 * (η ^ 4 * (8 * (9 * M + 8) * Ψ) + n₀ * T)) := by linarith
      linarith
    have h3 : 16 / 3 * (8 * (A * Cω * Ψ + Hs) +
        n₁ * (8 * (η ^ 4 * (8 * (9 * M + 8) * Ψ) + n₀ * (8 * (C₂ * d γ ^ 4 + η ^ 4 * Ψ + C₃ * Hs))))) ≤
        16 / 3 * (8 * (A * Cω * Ψ + Ch * (d γ ^ 4 + η ^ 4 * Ψ)) +
        n₁ * (8 * (η ^ 4 * (8 * (9 * M + 8) * Ψ) +
          n₀ * (8 * (C₂ * d γ ^ 4 + η ^ 4 * Ψ + C₃ * (Ch * (d γ ^ 4 + η ^ 4 * Ψ))))))) := by
      gcongr
    refine le_trans h1 (le_trans h3 (le_of_eq ?_))
    rw [hCd, hCA, hCη]
    ring
  have hcs1 : min 1 (1 / (2 * (CA + Cη))) ≤ 1 := min_le_left _ _
  have hcs2 : min 1 (1 / (2 * (CA + Cη))) ≤ 1 / (2 * (CA + Cη)) := min_le_right _ _
  set cs := min 1 (1 / (2 * (CA + Cη))) with hcs
  have hη4 : η ^ 4 ≤ cs := by
    have h1 : η ≤ 1 := le_trans hηc hcs1
    have h2 : η ^ 4 ≤ η := by
      calc η ^ 4 ≤ η ^ 1 := pow_le_pow_of_le_one hη h1 (by norm_num)
        _ = η := pow_one η
    exact le_trans h2 hηc
  have hsum : (CA + Cη) * cs ≤ 1 / 2 := by
    have h0 : 0 < CA + Cη := by positivity
    calc (CA + Cη) * cs ≤ (CA + Cη) * (1 / (2 * (CA + Cη))) := mul_le_mul_of_nonneg_left hcs2 h0.le
      _ = 1 / 2 := by field_simp
  have h1 : CA * A * Ψ + Cη * η ^ 4 * Ψ ≤ 1 / 2 * Ψ := by
    have h2 : CA * A + Cη * η ^ 4 ≤ (CA + Cη) * cs := by
      have := mul_le_mul_of_nonneg_left hAc hCA0.le
      have := mul_le_mul_of_nonneg_left hη4 hCη0.le
      linarith
    have := mul_le_mul_of_nonneg_right (le_trans h2 hsum) hΨ0
    linarith
  have hd4 : 0 ≤ d γ ^ 4 := by positivity
  linarith only [hfin, h1, hd4]
end YangMills.Construction.PinnedGauge
end
