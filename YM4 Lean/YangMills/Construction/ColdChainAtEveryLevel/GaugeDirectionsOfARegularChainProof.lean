import YangMills.Construction.ColdChainAtEveryLevel.GaugeMotionsOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.GaugeDirections
open BlockAverages QuaternionLog PlaquetteLinearization GaugeMotions
variable {F : BlockFrame}
def tangentForm (R : F.FieldChain) (U : ChainChart F) (ξ : F.Site 0 → imaginaryQuaternions) (x : F.Site 0)
    (i : Fin 4) : ℍ[ℝ] :=
  rightTransDeriv (U.fine x i) (ξ x) -
    rightTransDeriv (-(U.fine x i : ℍ[ℝ])) (_root_.YangMills.Construction.BlockAverages.adjointAction (R 0 x i) (ξ (x + unitStep 0 i)))
def correctionMap (R : F.FieldChain) (U : ChainChart F) :
    (F.Site 0 → imaginaryQuaternions) →ₗ[ℝ] (F.Site 0 → Fin 4 → imaginaryQuaternions) where
  toFun ξ := fun x i => pureComponentCLM (tangentForm R U ξ x i + covariantDiff (R 0) (fun x => ξ x) x i)
  map_add' ξ ξ' := by
    funext x i
    simp only [Pi.add_apply]
    rw [← map_add]
    congr 1
    simp only [tangentForm, covariantDiff, Pi.add_apply, Submodule.coe_add, _root_.YangMills.Construction.PlaquetteLinearization.adjointAction_add,
      rightTransDeriv_add]
    abel
  map_smul' t ξ := by
    funext x i
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [← map_smul]
    congr 1
    simp only [tangentForm, covariantDiff, Pi.smul_apply, Submodule.coe_smul, _root_.YangMills.Construction.PlaquetteLinearization.adjointAction_smul,
      rightTransDeriv_smul, smul_add, smul_sub]
theorem re_covariantDiff (R : F.GaugeField 0) (ξ : F.Site 0 → imaginaryQuaternions) (x : F.Site 0)
    (i : Fin 4) : (covariantDiff R (fun x => (ξ x : ℍ[ℝ])) x i).re = 0 := by
  have h1 : ((ξ x : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := (ξ x).2
  have h2 : ((ξ (x + unitStep 0 i) : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := (ξ (x + unitStep 0 i)).2
  have e : ∀ a b : ℍ[ℝ], (a - b).re = a.re - b.re := fun _ _ => rfl
  simp only [covariantDiff, e, _root_.YangMills.Construction.PlaquetteLinearization.adjointAction_re, h1, h2, sub_zero]
theorem re_neg_coe (w : imaginaryQuaternions) : (-(w : ℍ[ℝ])).re = 0 := by
  have h : ((w : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := w.2
  show -((w : imaginaryQuaternions) : ℍ[ℝ]).re = 0
  rw [h, neg_zero]
theorem isChartCurve_chartMove (S : Finset F.Cell) (U A : ChainChart F) :
    IsChartCurve S (chartMove U A) U A := by
  refine ⟨⟨fun b _ => by simp [chartMove], fun j _ b _ => by simp [chartMove]⟩, fun b _ => ?_, fun j _ b _ => ?_⟩
  · have h := ((hasDerivAt_id (0 : ℝ)).smul_const (A.fine b.1 b.2)).const_add (U.fine b.1 b.2)
    simpa [chartMove] using h
  · have h := ((hasDerivAt_id (0 : ℝ)).smul_const (A.coarse j b.1 b.2)).const_add (U.coarse j b.1 b.2)
    simpa [chartMove] using h
theorem curl_constant_bound {K₁ K₂ c₀ Cu Up Xp Dp x0 N e1 e2 e3 e4 : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hc0 : 0 < c₀) (hUp0 : 0 ≤ Up) (hXp0 : 0 ≤ Xp) (hDp0 : 0 ≤ Dp) (hCu0 : 0 ≤ Cu) (hx0 : x0 ≤ Xp)
    (hmain : N ≤ K₂ * (Cu * (2 * x0) + Up * (2 * Dp)) + (e1 + e2 + e3 + e4))
    (f1 : e1 ≤ K₁ * Up ^ 2 * Xp) (f2 : e2 ≤ K₁ * Up ^ 2 * Xp) (f3 : e3 ≤ K₁ * Up ^ 2 * Xp)
    (f4 : e4 ≤ K₁ * Up ^ 2 * Xp) :
    N ≤ (2 * K₂ + 4 * K₁ + K₁ * c₀ + 1) * ((Cu + Up ^ 2) * Xp + Up * Dp) := by
  have t1 : K₂ * (Cu * (2 * x0)) ≤ (2 * K₂) * (Cu * Xp) := by
    have : Cu * x0 ≤ Cu * Xp := mul_le_mul_of_nonneg_left hx0 hCu0
    nlinarith
  set Cst : ℝ := 2 * K₂ + 4 * K₁ + K₁ * c₀ + 1 with hCst
  have a1 : 0 ≤ Cu * Xp := by positivity
  have a2 : 0 ≤ Up ^ 2 * Xp := by positivity
  have a3 : 0 ≤ Up * Dp := by positivity
  have hk : 0 ≤ K₁ * c₀ := by positivity
  have p1 : (2 * K₂) * (Cu * Xp) ≤ Cst * (Cu * Xp) :=
    mul_le_mul_of_nonneg_right (by rw [hCst]; linarith) a1
  have p2 : (4 * K₁) * (Up ^ 2 * Xp) ≤ Cst * (Up ^ 2 * Xp) :=
    mul_le_mul_of_nonneg_right (by rw [hCst]; linarith) a2
  have p3 : (2 * K₂) * (Up * Dp) ≤ Cst * (Up * Dp) :=
    mul_le_mul_of_nonneg_right (by rw [hCst]; linarith) a3
  have e5 : K₂ * (Cu * (2 * x0) + Up * (2 * Dp)) = K₂ * (Cu * (2 * x0)) + (2 * K₂) * (Up * Dp) := by ring
  have e6 : Cst * ((Cu + Up ^ 2) * Xp + Up * Dp) = Cst * (Cu * Xp) + Cst * (Up ^ 2 * Xp) + Cst * (Up * Dp) := by
    ring
  rw [e6]
  rw [e5] at hmain
  linarith
theorem remainder_le_of_le {K₁ Up Xp : ℝ} (hK₁ : 0 < K₁) (e w s : ℝ)
    (hw : 0 ≤ w) (hs : 0 ≤ s) (h1 : w ≤ Up) (h2 : s ≤ Xp) (h3 : e ≤ K₁ * w ^ 2 * s) :
    e ≤ K₁ * Up ^ 2 * Xp := by
  refine h3.trans ?_
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw h1 2) hK₁.le) h2 hs (by positivity)
theorem norm_linearizedCurl_correctionMap_le {K₁ K₂ c₀ : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hB : ∀ q a : ℍ[ℝ], ‖linearPart q a‖ ≤ K₂ * ‖q‖ * ‖a‖) (hc0 : 0 < c₀) {S : Finset F.Cell}
    (R : F.FieldChain) (U : ChainChart F) (ξ : F.Site 0 → imaginaryQuaternions)
    {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S 0)
    (hsplit : ∀ b ∈ innerBonds S 0, ∃ e : ℍ[ℝ], ((correctionMap R U ξ b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) =
      linearPart (U.fine b.1 b.2) (ξ b.1 + adjointAction (R 0 b.1 b.2) (ξ (b.1 + unitStep 0 b.2))) + e ∧
      ‖e‖ ≤ K₁ * ‖U.fine b.1 b.2‖ ^ 2 * (‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖)) :
    ‖linearizedCurl (R 0) (correctionMap R U ξ) p‖ ≤ (2 * K₂ + 4 * K₁ + K₁ * c₀ + 1) *
      ((‖linearizedCurl (R 0) U.fine p‖ + plaquetteBondSum (fun x i => ‖U.fine x i‖) p ^ 2) *
          plaquetteCornerSum (fun x => ‖ξ x‖) p +
        plaquetteBondSum (fun x i => ‖U.fine x i‖) p *
          plaquetteBondSum (fun x i => ‖covariantDiff (R 0) (fun x => ξ x) x i‖) p) := by
  obtain ⟨x, μ, ν⟩ := p
  have hc := (Finset.mem_filter.1 hp).2.2
  have k1 : x ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have k2 : x + unitStep 0 μ ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have k3 : x + unitStep 0 ν ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have k4 : x + unitStep 0 μ + unitStep 0 ν ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have hcomm : x + unitStep 0 ν + unitStep 0 μ = x + unitStep 0 μ + unitStep 0 ν := add_right_comm _ _ _
  have b1 : (x, μ) ∈ innerBonds S 0 := ChartCoordinates.mem_innerBonds k1 k2
  have b2 : (x + unitStep 0 μ, ν) ∈ innerBonds S 0 := ChartCoordinates.mem_innerBonds k2 k4
  have b3 : (x + unitStep 0 ν, μ) ∈ innerBonds S 0 := ChartCoordinates.mem_innerBonds k3 (by rw [hcomm]; exact k4)
  have b4 : (x, ν) ∈ innerBonds S 0 := ChartCoordinates.mem_innerBonds k1 k3
  obtain ⟨e1, h1, g1⟩ := hsplit _ b1
  obtain ⟨e2, h2, g2⟩ := hsplit _ b2
  obtain ⟨e3, h3, g3⟩ := hsplit _ b3
  obtain ⟨e4, h4, g4⟩ := hsplit _ b4
  simp only at h1 h2 h3 h4 g1 g2 g3 g4
  rw [hcomm] at h3 g3
  have hmain := norm_plaquette_linearPart_le hK₂.le hB (R 0 x μ) (R 0 (x + unitStep 0 μ) ν)
    (R 0 (x + unitStep 0 ν) μ) (R 0 x ν)
    (ξ x) (ξ (x + unitStep 0 μ)) (ξ (x + unitStep 0 ν)) (ξ (x + unitStep 0 μ + unitStep 0 ν))
    (U.fine x μ) (U.fine (x + unitStep 0 μ) ν) (U.fine (x + unitStep 0 ν) μ) (U.fine x ν) e1 e2 e3 e4
  have ec : linearizedCurl (R 0) (correctionMap R U ξ) (x, μ, ν) =
      (linearPart (U.fine x μ) ((ξ x : ℍ[ℝ]) + _root_.YangMills.Construction.BlockAverages.adjointAction (R 0 x μ) (ξ (x + unitStep 0 μ))) + e1) +
      _root_.YangMills.Construction.BlockAverages.adjointAction (R 0 x μ) (linearPart (U.fine (x + unitStep 0 μ) ν) ((ξ (x + unitStep 0 μ) : ℍ[ℝ]) +
        _root_.YangMills.Construction.BlockAverages.adjointAction (R 0 (x + unitStep 0 μ) ν) (ξ (x + unitStep 0 μ + unitStep 0 ν))) + e2) -
      adjointAction (R 0 x μ * R 0 (x + unitStep 0 μ) ν * (R 0 (x + unitStep 0 ν) μ)⁻¹)
        (linearPart (U.fine (x + unitStep 0 ν) μ) ((ξ (x + unitStep 0 ν) : ℍ[ℝ]) +
          _root_.YangMills.Construction.BlockAverages.adjointAction (R 0 (x + unitStep 0 ν) μ) (ξ (x + unitStep 0 μ + unitStep 0 ν))) + e3) -
      adjointAction (R 0 x μ * R 0 (x + unitStep 0 μ) ν * (R 0 (x + unitStep 0 ν) μ)⁻¹ * (R 0 x ν)⁻¹)
        (linearPart (U.fine x ν) ((ξ x : ℍ[ℝ]) + _root_.YangMills.Construction.BlockAverages.adjointAction (R 0 x ν) (ξ (x + unitStep 0 ν))) + e4) := by
    simp only [linearizedCurl]
    rw [h1, h2, h3, h4]
  have eu : linearizedCurl (R 0) U.fine (x, μ, ν) =
      (U.fine x μ : ℍ[ℝ]) + _root_.YangMills.Construction.BlockAverages.adjointAction (R 0 x μ) (U.fine (x + unitStep 0 μ) ν) -
      adjointAction (R 0 x μ * R 0 (x + unitStep 0 μ) ν * (R 0 (x + unitStep 0 ν) μ)⁻¹)
        (U.fine (x + unitStep 0 ν) μ) -
      adjointAction (R 0 x μ * R 0 (x + unitStep 0 μ) ν * (R 0 (x + unitStep 0 ν) μ)⁻¹ * (R 0 x ν)⁻¹)
        (U.fine x ν) := rfl
  rw [ec]
  rw [← eu] at hmain
  set Up : ℝ := plaquetteBondSum (fun x i => ‖U.fine x i‖) (x, μ, ν) with hUp
  set Dp : ℝ := plaquetteBondSum (fun x i => ‖covariantDiff (R 0) (fun x => ξ x) x i‖) (x, μ, ν) with hDp
  set Xp : ℝ := plaquetteCornerSum (fun x => ‖ξ x‖) (x, μ, ν) with hXp
  set Cu : ℝ := ‖linearizedCurl (R 0) U.fine (x, μ, ν)‖ with hCu
  have n1 := norm_nonneg (U.fine x μ)
  have n2 := norm_nonneg (U.fine (x + unitStep 0 μ) ν)
  have n3 := norm_nonneg (U.fine (x + unitStep 0 ν) μ)
  have n4 := norm_nonneg (U.fine x ν)
  have m1 := norm_nonneg (ξ x)
  have m2 := norm_nonneg (ξ (x + unitStep 0 μ))
  have m3 := norm_nonneg (ξ (x + unitStep 0 ν))
  have m4 := norm_nonneg (ξ (x + unitStep 0 μ + unitStep 0 ν))
  have eUp : Up = ‖U.fine x μ‖ + ‖U.fine (x + unitStep 0 μ) ν‖ + ‖U.fine (x + unitStep 0 ν) μ‖ +
      ‖U.fine x ν‖ := rfl
  have eXp : Xp = ‖ξ x‖ + ‖ξ (x + unitStep 0 μ)‖ + ‖ξ (x + unitStep 0 ν)‖ +
      ‖ξ (x + unitStep 0 μ + unitStep 0 ν)‖ := rfl
  have hUp0 : 0 ≤ Up := by rw [eUp]; positivity
  have hXp0 : 0 ≤ Xp := by rw [eXp]; positivity
  have eDp : ‖_root_.YangMills.Construction.BlockAverages.adjointAction (R 0 x μ) (ξ (x + unitStep 0 μ)) - ξ x‖ +
      ‖_root_.YangMills.Construction.BlockAverages.adjointAction (R 0 (x + unitStep 0 μ) ν) (ξ (x + unitStep 0 μ + unitStep 0 ν)) - ξ (x + unitStep 0 μ)‖ +
      ‖_root_.YangMills.Construction.BlockAverages.adjointAction (R 0 (x + unitStep 0 ν) μ) (ξ (x + unitStep 0 μ + unitStep 0 ν)) - ξ (x + unitStep 0 ν)‖ +
      ‖_root_.YangMills.Construction.BlockAverages.adjointAction (R 0 x ν) (ξ (x + unitStep 0 ν)) - ξ x‖ = Dp := by
    rw [hDp]
    simp only [plaquetteBondSum, covariantDiff]
    rw [hcomm]
  have eUp' : ‖((U.fine x μ : imaginaryQuaternions) : ℍ[ℝ])‖ +
      ‖((U.fine (x + unitStep 0 μ) ν : imaginaryQuaternions) : ℍ[ℝ])‖ +
      ‖((U.fine (x + unitStep 0 ν) μ : imaginaryQuaternions) : ℍ[ℝ])‖ +
      ‖((U.fine x ν : imaginaryQuaternions) : ℍ[ℝ])‖ = Up := rfl
  rw [eDp, eUp'] at hmain
  have hDp0 : 0 ≤ Dp := by
    rw [← eDp]
    positivity
  have f1 := remainder_le_of_le (Up := Up) (Xp := Xp) hK₁ _ _ _ n1 (by positivity) (by linarith) (by linarith) g1
  have f2 := remainder_le_of_le (Up := Up) (Xp := Xp) hK₁ _ _ _ n2 (by positivity) (by linarith) (by linarith) g2
  have f3 := remainder_le_of_le (Up := Up) (Xp := Xp) hK₁ _ _ _ n3 (by positivity) (by linarith) (by linarith) g3
  have f4 := remainder_le_of_le (Up := Up) (Xp := Xp) hK₁ _ _ _ n4 (by positivity) (by linarith) (by linarith) g4
  have hx0 : ‖((ξ x : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ Xp := by
    show ‖ξ x‖ ≤ Xp
    linarith
  exact curl_constant_bound hK₁ hK₂ hc0 hUp0 hXp0 hDp0 (norm_nonneg _) hx0 hmain f1 f2 f3 f4
theorem regularChainGaugeDirections (hV : regularChainFirstVariationStatement) :
    regularChainGaugeDirectionsStatement := by
  obtain ⟨K₁, r₁, hK₁, hr₁, hT⟩ := exists_taylor_bound
  obtain ⟨K₂, hK₂, hB⟩ := exists_norm_linearPart_le
  obtain ⟨r₂, hr₂, hS⟩ := exists_norm_exp_sub_one_lt
  have hρ : 0 < leftRadius := qlogRadii_spec.left_pos
  set c₀ : ℝ := min (min r₁ r₂) leftRadius / 2 with hc₀
  have hc0 : 0 < c₀ := by
    have : 0 < min (min r₁ r₂) leftRadius := lt_min (lt_min hr₁ hr₂) hρ
    positivity
  have c1 : c₀ < r₁ := by
    have h1 : min (min r₁ r₂) leftRadius ≤ r₁ := (min_le_left _ _).trans (min_le_left _ _)
    have : 0 < min (min r₁ r₂) leftRadius := lt_min (lt_min hr₁ hr₂) hρ
    rw [hc₀]; linarith
  have c2 : c₀ < r₂ := by
    have h1 : min (min r₁ r₂) leftRadius ≤ r₂ := (min_le_left _ _).trans (min_le_right _ _)
    have : 0 < min (min r₁ r₂) leftRadius := lt_min (lt_min hr₁ hr₂) hρ
    rw [hc₀]; linarith
  have c3 : c₀ < leftRadius := by
    have h1 : min (min r₁ r₂) leftRadius ≤ leftRadius := min_le_right _ _
    have : 0 < min (min r₁ r₂) leftRadius := lt_min (lt_min hr₁ hr₂) hρ
    rw [hc₀]; linarith
  refine ⟨c₀, 2 * K₂ + 4 * K₁ + K₁ * c₀ + 1, hc0, by positivity, ?_⟩
  intro F a S R U W hodd hreg hu hmu
  have hsmall : ∀ w : imaginaryQuaternions, ‖w‖ ≤ c₀ →
      ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1‖ < rightRadius := fun w hw =>
    (hS _ (lt_of_le_of_lt hw c2)).1
  have hsmall' : ∀ w : imaginaryQuaternions, ‖w‖ ≤ c₀ →
      ‖NormedSpace.exp (-(w : ℍ[ℝ])) - 1‖ < rightRadius := fun w hw =>
    (hS _ (lt_of_le_of_lt hw c2)).2
  have hform : ∀ (ξ : F.Site 0 → imaginaryQuaternions), ∀ b ∈ innerBonds S 0,
      ((correctionMap R U ξ b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) =
      tangentForm R U ξ b.1 b.2 + covariantDiff (R 0) (fun x => ξ x) b.1 b.2 := by
    intro ξ b hb
    have hw := hu b hb
    have hre : (tangentForm R U ξ b.1 b.2 + covariantDiff (R 0) (fun x => ξ x) b.1 b.2).re = 0 := by
      have e1 : (rightTransDeriv (U.fine b.1 b.2) (ξ b.1)).re = 0 :=
        re_rightTransDeriv (U.fine b.1 b.2).2 (ξ b.1).2 (hsmall _ hw)
      have e2 : (rightTransDeriv (-(U.fine b.1 b.2 : ℍ[ℝ]))
          (adjointAction (R 0 b.1 b.2) (ξ (b.1 + unitStep 0 b.2)))).re = 0 :=
        re_rightTransDeriv (re_neg_coe _) (by rw [adjointAction_re]; exact (ξ (b.1 + unitStep 0 b.2)).2)
          (hsmall' _ hw)
      have e3 := re_covariantDiff (R 0) ξ b.1 b.2
      have e : ∀ p q : ℍ[ℝ], (p + q).re = p.re + q.re := fun _ _ => rfl
      have e' : ∀ p q : ℍ[ℝ], (p - q).re = p.re - q.re := fun _ _ => rfl
      rw [e, e3]
      simp only [tangentForm, e', e1, e2, sub_zero, add_zero]
    show pureComponent _ = _
    exact _root_.YangMills.Construction.GaugeMotions.pureComponent_of_re_eq_zero hre
  have hsplit : ∀ (ξ : F.Site 0 → imaginaryQuaternions), ∀ b ∈ innerBonds S 0, ∃ e : ℍ[ℝ],
      ((correctionMap R U ξ b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) =
      linearPart (U.fine b.1 b.2) (ξ b.1 + adjointAction (R 0 b.1 b.2) (ξ (b.1 + unitStep 0 b.2))) + e ∧
      ‖e‖ ≤ K₁ * ‖U.fine b.1 b.2‖ ^ 2 * (‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖) := by
    intro ξ b hb
    obtain ⟨e, h1, h2⟩ := exists_bond_linearPart_split hT (w := (U.fine b.1 b.2 : ℍ[ℝ])) (a := ξ b.1)
      (b := _root_.YangMills.Construction.BlockAverages.adjointAction (R 0 b.1 b.2) (ξ (b.1 + unitStep 0 b.2))) (lt_of_le_of_lt (hu b hb) c1)
    refine ⟨e, ?_, ?_⟩
    · rw [hform ξ b hb]
      exact h1
    · rw [_root_.YangMills.Construction.PlaquetteLinearization.norm_adjointAction] at h2
      exact h2
  refine ⟨correctionMap R U, ?_, ?_, ?_⟩
  · intro ξ htop
    have hU : ∀ b ∈ innerBonds S 0, ‖((expUnit (U.fine b.1 b.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ < rightRadius :=
      fun b hb => hsmall _ (hu b hb)
    have hM : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1),
        ‖((expUnit (U.coarse j b.1 b.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ < rightRadius :=
      fun j hj b hb => hsmall _ (hmu j hj b hb)
    have hJ := hasDerivAt_chartAction_gaugedChart R U ξ hodd hreg hU hM a W htop
    set C := gaugedChart R U ξ with hC
    set A : ChainChart F := ⟨fun x i => deriv (fun τ => (C τ).fine x i) 0,
      fun j y i => deriv (fun τ => (C τ).coarse j y i) 0⟩ with hA
    have hbase : ∀ b ∈ innerBonds S 0, HasDerivAt (fun τ => (C τ).fine b.1 b.2)
        (pureComponentCLM (fderiv ℝ qlog ((bottomBondElement R U ξ 0 b.1 b.2 : UnitQuaternion) : ℍ[ℝ])
          ((ξ b.1 : ℍ[ℝ]) * ((expUnit (U.fine b.1 b.2) : UnitQuaternion) : ℍ[ℝ]) -
            ((expUnit (U.fine b.1 b.2) : UnitQuaternion) : ℍ[ℝ]) *
              _root_.YangMills.Construction.BlockAverages.adjointAction (R 0 b.1 b.2) (ξ (b.1 + unitStep 0 b.2))))) 0 := by
      intro b hb
      refine hasDerivAt_logUnit_comp (g := fun τ => bottomBondElement R U ξ τ b.1 b.2)
        (hasDerivAt_bottomBondElement R U ξ hodd hreg hb) ?_
      rw [bottomBondElement_zero]
      exact hU b hb
    have hcurve : IsChartCurve S C U A := by
      refine ⟨⟨fun b hb => ?_, fun j hj b hb => ?_⟩, fun b hb => ?_, fun j hj b hb => ?_⟩
      · show logUnit (bottomBondElement R U ξ 0 b.1 b.2) = _
        rw [bottomBondElement_zero]
        exact logUnit_expUnit (lt_of_le_of_lt (hu b hb) c3)
      · show logUnit (upperBondElement R U ξ 0 j b.1 b.2) = _
        rw [upperBondElement_zero]
        exact logUnit_expUnit (lt_of_le_of_lt (hmu j hj b hb) c3)
      · exact (hbase b hb).differentiableAt.hasDerivAt
      · obtain ⟨dg, hdg⟩ := exists_hasDerivAt_upperBondElement R U ξ hodd hreg hj hb
        have h := hasDerivAt_logUnit_comp (g := fun τ => upperBondElement R U ξ τ j b.1 b.2) hdg (by
          rw [upperBondElement_zero]; exact hM j hj b hb)
        exact h.differentiableAt.hasDerivAt
    obtain ⟨D, _, _, hD⟩ := hV F a S R U W hodd hreg
    have e0 : D A = 0 := (hD C A hcurve).unique hJ
    have d2 := hD (chartMove U A) A (isChartCurve_chartMove S U A)
    rw [e0] at d2
    refine ⟨A, fun b hb => ?_, d2⟩
    have hval : ((A.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) = pureComponent (tangentForm R U ξ b.1 b.2) := by
      have h1 := (hbase b hb).deriv
      show ((deriv (fun τ => (C τ).fine b.1 b.2) 0 : imaginaryQuaternions) : ℍ[ℝ]) = _
      rw [h1, bottomBondElement_zero, coe_pureComponentCLM, map_sub]
      have hw := hu b hb
      have e1 : fderiv ℝ qlog ((expUnit (U.fine b.1 b.2) : UnitQuaternion) : ℍ[ℝ])
          ((expUnit (U.fine b.1 b.2) : UnitQuaternion) * _root_.YangMills.Construction.BlockAverages.adjointAction (R 0 b.1 b.2) (ξ (b.1 + unitStep 0 b.2))) =
          rightTransDeriv (-(U.fine b.1 b.2 : ℍ[ℝ])) (_root_.YangMills.Construction.BlockAverages.adjointAction (R 0 b.1 b.2) (ξ (b.1 + unitStep 0 b.2))) :=
        fderiv_qlog_left_mul (hsmall _ hw) (hsmall' _ hw) _
      rw [e1]
      rfl
    have hre : (tangentForm R U ξ b.1 b.2).re = 0 := by
      have hw := hu b hb
      have e1 : (rightTransDeriv (U.fine b.1 b.2) (ξ b.1)).re = 0 :=
        re_rightTransDeriv (U.fine b.1 b.2).2 (ξ b.1).2 (hsmall _ hw)
      have e2 : (rightTransDeriv (-(U.fine b.1 b.2 : ℍ[ℝ]))
          (adjointAction (R 0 b.1 b.2) (ξ (b.1 + unitStep 0 b.2)))).re = 0 :=
        re_rightTransDeriv (re_neg_coe _) (by rw [adjointAction_re]; exact (ξ (b.1 + unitStep 0 b.2)).2)
          (hsmall' _ hw)
      have e' : ∀ p q : ℍ[ℝ], (p - q).re = p.re - q.re := fun _ _ => rfl
      simp only [tangentForm, e', e1, e2, sub_zero]
    rw [hval, _root_.YangMills.Construction.GaugeMotions.pureComponent_of_re_eq_zero hre, hform ξ b hb]
    abel
  · intro ξ b hb
    obtain ⟨e, h1, h2⟩ := hsplit ξ b hb
    have hw := hu b hb
    have hw0 := norm_nonneg (U.fine b.1 b.2)
    have hs : ‖((ξ b.1 : imaginaryQuaternions) : ℍ[ℝ]) + _root_.YangMills.Construction.BlockAverages.adjointAction (R 0 b.1 b.2) (ξ (b.1 + unitStep 0 b.2))‖ ≤
        ‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖ := by
      have := norm_add_le ((ξ b.1 : imaginaryQuaternions) : ℍ[ℝ])
        (_root_.YangMills.Construction.BlockAverages.adjointAction (R 0 b.1 b.2) (ξ (b.1 + unitStep 0 b.2)))
      rw [_root_.YangMills.Construction.PlaquetteLinearization.norm_adjointAction] at this
      exact this
    have hn0 : 0 ≤ ‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖ := by positivity
    have b1 := hB (U.fine b.1 b.2)
      (((ξ b.1 : imaginaryQuaternions) : ℍ[ℝ]) + _root_.YangMills.Construction.BlockAverages.adjointAction (R 0 b.1 b.2) (ξ (b.1 + unitStep 0 b.2)))
    have nrm : ‖correctionMap R U ξ b.1 b.2‖ = ‖((correctionMap R U ξ b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ :=
      rfl
    have nu : ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ = ‖U.fine b.1 b.2‖ := rfl
    rw [nu] at b1
    rw [nrm, h1]
    have t1 : K₂ * ‖U.fine b.1 b.2‖ *
        ‖((ξ b.1 : imaginaryQuaternions) : ℍ[ℝ]) + _root_.YangMills.Construction.BlockAverages.adjointAction (R 0 b.1 b.2) (ξ (b.1 + unitStep 0 b.2))‖ ≤
        K₂ * ‖U.fine b.1 b.2‖ * (‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    have t2 : K₁ * ‖U.fine b.1 b.2‖ ^ 2 * (‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖) ≤
        (K₁ * c₀) * ‖U.fine b.1 b.2‖ * (‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖) := by
      refine mul_le_mul_of_nonneg_right ?_ hn0
      have : ‖U.fine b.1 b.2‖ ^ 2 ≤ c₀ * ‖U.fine b.1 b.2‖ := by nlinarith
      calc K₁ * ‖U.fine b.1 b.2‖ ^ 2 ≤ K₁ * (c₀ * ‖U.fine b.1 b.2‖) := mul_le_mul_of_nonneg_left this hK₁.le
        _ = _ := by ring
    have t3 : (K₂ + K₁ * c₀) * ‖U.fine b.1 b.2‖ * (‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖) ≤
        (2 * K₂ + 4 * K₁ + K₁ * c₀ + 1) * ‖U.fine b.1 b.2‖ * (‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖) := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hw0) hn0
      nlinarith
    have t4 := norm_add_le (linearPart (U.fine b.1 b.2)
      (((ξ b.1 : imaginaryQuaternions) : ℍ[ℝ]) + _root_.YangMills.Construction.BlockAverages.adjointAction (R 0 b.1 b.2) (ξ (b.1 + unitStep 0 b.2)))) e
    have e5 : (K₂ + K₁ * c₀) * ‖U.fine b.1 b.2‖ * (‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖) =
        K₂ * ‖U.fine b.1 b.2‖ * (‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖) +
          (K₁ * c₀) * ‖U.fine b.1 b.2‖ * (‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖) := by ring
    linarith
  · exact fun ξ p hp => norm_linearizedCurl_correctionMap_le hK₁ hK₂ hB hc0 R U ξ hp (hsplit ξ)
end YangMills.Construction.GaugeDirections
end
