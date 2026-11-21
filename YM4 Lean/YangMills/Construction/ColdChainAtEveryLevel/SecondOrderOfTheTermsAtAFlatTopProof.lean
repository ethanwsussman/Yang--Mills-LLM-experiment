import YangMills.Construction.ColdChainAtEveryLevel.SizesAtAGoodCellProof
import YangMills.Construction.ColdChainAtEveryLevel.FitsInCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.SecondOrderOfTheTermsAtAFlatTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction.BlockAverages
namespace FlatTopExpansion
open YangMills.Construction.BlockAverages.ChartCoordinates
variable {F : BlockFrame}
theorem one_sub_re_eq_half_norm_sub_one_sq (g : UnitQuaternion) :
    1 - (g : ℍ[ℝ]).re = (1 / 2) * ‖(g : ℍ[ℝ]) - 1‖ ^ 2 := by
  have hsq : ∀ q : ℍ[ℝ], ‖q‖ ^ 2 = q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 := fun q => by
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  have hunit : ‖(g : ℍ[ℝ])‖ ^ 2 = 1 := by rw [norm_coe_unitQuaternion]; norm_num
  rw [hsq] at hunit
  rw [hsq]
  have hre : ((g : ℍ[ℝ]) - 1).re = (g : ℍ[ℝ]).re - 1 := by simp
  have hi : ((g : ℍ[ℝ]) - 1).imI = (g : ℍ[ℝ]).imI := by simp
  have hj : ((g : ℍ[ℝ]) - 1).imJ = (g : ℍ[ℝ]).imJ := by simp
  have hk : ((g : ℍ[ℝ]) - 1).imK = (g : ℍ[ℝ]).imK := by simp
  rw [hre, hi, hj, hk]
  nlinarith
theorem tendsto_one_sub_re_div_sq {g : ℝ → UnitQuaternion} {d : ℍ[ℝ]}
    (hg : HasDerivAt (fun τ => ((g τ : UnitQuaternion) : ℍ[ℝ])) d 0) (hg0 : g 0 = 1) :
    Tendsto (fun τ : ℝ => (1 - ((g τ : UnitQuaternion) : ℍ[ℝ]).re) / τ ^ 2) (𝓝[≠] 0)
      (𝓝 ((1 / 2) * ‖d‖ ^ 2)) := by
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 hg
  have hlim : Tendsto (fun t : ℝ => (1 / 2) *
      ‖t⁻¹ • (((g (0 + t) : UnitQuaternion) : ℍ[ℝ]) - ((g 0 : UnitQuaternion) : ℍ[ℝ]))‖ ^ 2)
      (𝓝[≠] 0) (𝓝 ((1 / 2) * ‖d‖ ^ 2)) := ((hslope.norm).pow 2).const_mul _
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  rw [hg0, zero_add, one_sub_re_eq_half_norm_sub_one_sq, norm_smul, mul_pow, Real.norm_eq_abs, abs_inv,
    inv_pow, sq_abs]
  simp only [OneMemClass.coe_one]
  field_simp
theorem re_deriv_eq_zero {g : ℝ → UnitQuaternion} {d : ℍ[ℝ]}
    (hg : HasDerivAt (fun τ => ((g τ : UnitQuaternion) : ℍ[ℝ])) d 0) (hg0 : g 0 = 1) :
    d.re = 0 := by
  have hre : HasDerivAt (fun τ => ((g τ : UnitQuaternion) : ℍ[ℝ]).re) d.re 0 := reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg
  have hmax : IsLocalMax (fun τ => ((g τ : UnitQuaternion) : ℍ[ℝ]).re) 0 := by
    refine Eventually.of_forall fun τ => ?_
    have := quaternion_re_le_norm ((g τ : UnitQuaternion) : ℍ[ℝ])
    rw [norm_coe_unitQuaternion] at this
    simp only [hg0, OneMemClass.coe_one, Quaternion.re_one]
    exact this
  exact hmax.hasDerivAt_eq_zero hre
theorem star_eq_neg_of_re_eq_zero {d : ℍ[ℝ]} (hd : d.re = 0) : star d = -d := by apply _root_.YangMills.Construction.BlockAverages.star_eq_neg_of_re_eq_zero <;> assumption
theorem pureComponent_eq_self_of_re_eq_zero {d : ℍ[ℝ]} (hd : d.re = 0) : pureComponent d = d := by apply _root_.YangMills.Construction.BlockAverages.pureComponent_of_re_eq_zero <;> assumption
theorem hasDerivAt_expUnit {w : ℝ → imaginaryQuaternions} {d : ℍ[ℝ]}
    (hw : HasDerivAt (fun τ => ((w τ : imaginaryQuaternions) : ℍ[ℝ])) d 0) (hw0 : w 0 = 0) :
    HasDerivAt (fun τ => ((expUnit (w τ) : UnitQuaternion) : ℍ[ℝ])) d 0 := by
  have hexp : HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ])
      ((w 0 : imaginaryQuaternions) : ℍ[ℝ]) := by
    rw [hw0]
    simpa using hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := ℍ[ℝ])
  exact hexp.comp_hasDerivAt (0 : ℝ) hw
theorem hasDerivAt_mul_of_eq_one {g g' : ℝ → UnitQuaternion} {d d' : ℍ[ℝ]}
    (hg : HasDerivAt (fun τ => ((g τ : UnitQuaternion) : ℍ[ℝ])) d 0)
    (hg' : HasDerivAt (fun τ => ((g' τ : UnitQuaternion) : ℍ[ℝ])) d' 0) (hg0 : g 0 = 1) (hg0' : g' 0 = 1) :
    HasDerivAt (fun τ => ((g τ * g' τ : UnitQuaternion) : ℍ[ℝ])) (d + d') 0 := by
  have := hg.mul hg'
  simp only [hg0, hg0', OneMemClass.coe_one, mul_one, one_mul] at this
  exact this
theorem hasDerivAt_inv {g : ℝ → UnitQuaternion} {d : ℍ[ℝ]}
    (hg : HasDerivAt (fun τ => ((g τ : UnitQuaternion) : ℍ[ℝ])) d 0) :
    HasDerivAt (fun τ => (((g τ)⁻¹ : UnitQuaternion) : ℍ[ℝ])) (star d) 0 := by
  have := starCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg
  exact this
theorem gaugedBlockFit_eq {j : ℕ} (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion)
    (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    gaugedBlockFit X k X' c = ‖gaugedContourAverage X k c‖ *
      (1 - ((polarUnit (gaugedContourAverage X k c) * (X' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re) := by
  unfold gaugedBlockFit
  by_cases hz : gaugedContourAverage X k c = 0
  · simp [hz]
  · have hn : ‖gaugedContourAverage X k c‖ ≠ 0 := norm_ne_zero_iff.2 hz
    simp only [Submonoid.coe_mul]
    rw [coe_polarUnit hz, smul_mul_assoc, Quaternion.re_smul, mul_sub, mul_one, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hn, one_mul]
theorem tendsto_norm_mul_one_sub_re_div_sq {M : ℝ → ℍ[ℝ]} {h : ℝ → UnitQuaternion} {d : ℍ[ℝ]}
    (hM : Tendsto (fun τ => ‖M τ‖) (𝓝 0) (𝓝 1))
    (hd : HasDerivAt (fun τ => ((h τ : UnitQuaternion) : ℍ[ℝ])) d 0) (h0 : h 0 = 1) :
    Tendsto (fun τ : ℝ => ‖M τ‖ * (1 - ((h τ : UnitQuaternion) : ℍ[ℝ]).re) / τ ^ 2) (𝓝[≠] 0)
      (𝓝 ((1 / 2) * ‖d‖ ^ 2)) := by
  have hprod := (hM.mono_left nhdsWithin_le_nhds).mul (tendsto_one_sub_re_div_sq hd h0)
  rw [one_mul] at hprod
  refine hprod.congr fun τ => ?_
  ring
theorem pathHolonomy_one {j : ℕ} (l : List PathStep) (x : F.Site j) :
    pathHolonomy (fun _ _ => (1 : UnitQuaternion) : F.GaugeField j) x l = 1 := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.pathHolonomy_one <;> assumption
theorem polarUnit_one : polarUnit (1 : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.BlockAverages.ChartFits.polarUnit_one <;> assumption
theorem contourAverage_one (hL : Odd F.blockSide) {j : ℕ} (c : F.Site (j + 1) × Fin 4) :
    contourAverage (fun _ _ => (1 : UnitQuaternion) : F.GaugeField j) c = 1 := by apply _root_.YangMills.Construction.BlockAverages.LowCostPatch.contourAverage_trivialField <;> assumption
section BondStep
variable {S : Finset F.Cell} {j : ℕ}
theorem gaugeAgreeOnBonds_one {Rj : F.GaugeField j} (hR : ∀ b ∈ innerBonds S j, Rj b.1 b.2 = 1) :
    GaugeAgreeOnBonds S j Rj (fun _ _ => (1 : UnitQuaternion)) := fun x i hx hx' =>
  hR (x, i) (mem_innerBonds hx hx')
theorem contourAverage_eq_one_of_trivial (hodd : Odd F.blockSide) (hj : j < F.top) {Rj : F.GaugeField j}
    (hR : ∀ b ∈ innerBonds S j, Rj b.1 b.2 = 1) {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ innerBonds S (j + 1)) :
    contourAverage Rj c = 1 := by
  rw [contourAverage_congr hodd hj (gaugeAgreeOnBonds_one hR) hc, contourAverage_one hodd]
theorem pathHolonomy_bondContour_eq_one (hodd : Odd F.blockSide) (hj : j < F.top) {Rj : F.GaugeField j}
    (hR : ∀ b ∈ innerBonds S j, Rj b.1 b.2 = 1) {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ innerBonds S (j + 1)) {h : LatticeFractionalIntegration.Lattice4}
    (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    pathHolonomy Rj (refineSite c.1) (bondContour F.blockSide h π c.2) = 1 := by
  have := pathHolonomy_congr (D := (sitesOfCells S j : Set (F.Site j)))
    (fun x i hx hx' => gaugeAgreeOnBonds_one hR x i hx hx') (refineSite c.1) _ 0
    (allAlong_bondContour hodd hj hc hh π)
  rw [add_siteOfCoords_zero] at this
  rw [this, pathHolonomy_one]
def pureComponentCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] := (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ ℍ[ℝ] - starCLM)
theorem pureComponentCLM_apply (q : ℍ[ℝ]) : pureComponentCLM q = pureComponent q := rfl
theorem hasDerivAt_adjointAction (g : UnitQuaternion) {w : ℝ → ℍ[ℝ]} {d : ℍ[ℝ]} (hw : HasDerivAt w d 0) :
    HasDerivAt (fun τ => adjointAction g (w τ)) (adjointAction g d) 0 :=
  (hw.const_mul (g : ℍ[ℝ])).mul_const _
theorem hasDerivAt_pureGap {Rj : F.GaugeField j} {X : ℝ → F.GaugeField j} {f : F.Site j → Fin 4 → ℍ[ℝ]}
    (hR : ∀ b ∈ innerBonds S j, Rj b.1 b.2 = 1) (h0 : ∀ b ∈ innerBonds S j, X 0 b.1 b.2 = 1)
    (hd : ∀ b ∈ innerBonds S j, HasDerivAt (fun τ => ((X τ b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) (f b.1 b.2) 0)
    {b : F.Site j × Fin 4} (hb : b ∈ innerBonds S j) :
    HasDerivAt (fun τ => pureGap (X τ) Rj b.1 b.2) (f b.1 b.2) 0 := by
  have hcomp := pureComponentCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hd b hb)
  have hre := re_deriv_eq_zero (g := fun τ => X τ b.1 b.2) (hd b hb) (h0 b hb)
  have hpure : pureComponentCLM (f b.1 b.2) = f b.1 b.2 := by
    rw [pureComponentCLM_apply, pureComponent_eq_self_of_re_eq_zero hre]
  rw [hpure] at hcomp
  refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
  simp only [pureGap, hR b hb, inv_one, mul_one, Function.comp]
  rfl
set_option maxHeartbeats 1000000 in
theorem hasDerivAt_polarUnit_gaugedContourAverage (hM : contourMeanFirstOrderStatement)
    (hodd : Odd F.blockSide) (hj : j < F.top) {Rj : F.GaugeField j}
    (hR : ∀ b ∈ innerBonds S j, Rj b.1 b.2 = 1) {X : ℝ → F.GaugeField j} {f : F.Site j → Fin 4 → ℍ[ℝ]}
    (h0 : ∀ b ∈ innerBonds S j, X 0 b.1 b.2 = 1)
    (hd : ∀ b ∈ innerBonds S j, HasDerivAt (fun τ => ((X τ b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) (f b.1 b.2) 0)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1)) :
    HasDerivAt (fun τ => ((polarUnit (gaugedContourAverage (X τ) (balancingGauge (X τ) Rj) c) :
        UnitQuaternion) : ℍ[ℝ])) (parallelAverage Rj f c) 0 ∧
      polarUnit (gaugedContourAverage (X 0) (balancingGauge (X 0) Rj) c) = 1 ∧
      Tendsto (fun τ => ‖gaugedContourAverage (X τ) (balancingGauge (X τ) Rj) c‖) (𝓝 0) (𝓝 1) := by
  classical
  obtain ⟨C, c₀, hC, hc₀, hM⟩ := hM
  set t : ℝ → ℝ := fun τ => ∑ b ∈ innerBonds S j, ‖((X τ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ with ht
  have ht0 : ∀ τ, 0 ≤ t τ := fun τ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hle : ∀ τ, ∀ b ∈ innerBonds S j, ‖((X τ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ t τ :=
    fun τ b hb =>
    Finset.single_le_sum (f := fun b : F.Site j × Fin 4 => ‖((X τ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖)
      (fun _ _ => norm_nonneg _) hb
  have htz : t 0 = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    simp [h0 b hb]
  have hLpos : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have htO : t =O[𝓝 0] (fun τ : ℝ => τ) := by
    have : ∀ b ∈ innerBonds S j,
        (fun τ => ‖((X τ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖) =O[𝓝 0] (fun τ : ℝ => τ) := by
      intro b hb
      have := (hd b hb).isBigO_sub
      simp only [h0 b hb, OneMemClass.coe_one, sub_zero] at this
      exact this.norm_left
    exact (Asymptotics.IsBigO.sum this).congr_left fun τ => by simp [ht, Finset.sum_apply]
  have htt : Tendsto t (𝓝 0) (𝓝 0) := htO.trans_tendsto tendsto_id
  set p : ℝ → ℍ[ℝ] := fun τ => parallelAverage Rj (pureGap (X τ) Rj) c with hp
  set g : ℝ → UnitQuaternion := fun τ =>
    polarUnit (gaugedContourAverage (X τ) (balancingGauge (X τ) Rj) c) with hg
  have hcm : contourAverage Rj c = 1 := contourAverage_eq_one_of_trivial hodd hj hR hc
  have hfact : ∀ τ, (F.blockSide : ℝ) * t τ ≤ c₀ →
      ‖p τ‖ ≤ (F.blockSide : ℝ) * t τ ∧
      ‖pureComponent ((g τ : UnitQuaternion) : ℍ[ℝ]) - p τ‖ ≤
        C * ((F.blockSide : ℝ) * t τ) * ((F.blockSide : ℝ) * t τ) ∧
      ‖((g τ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        4 * ‖p τ‖ + C * ((F.blockSide : ℝ) * t τ) * ((F.blockSide : ℝ) * t τ) := by
    intro τ hτ
    have hbd : ∀ a ∈ FlatPairing.twoBlockHull F.blockSide c.2, ∀ k,
        a + LatticeFractionalIntegration.basisVector k ∈ FlatPairing.twoBlockHull F.blockSide c.2 →
        ‖((X τ (refineSite c.1 + siteOfCoords j a) k * (Rj (refineSite c.1 + siteOfCoords j a) k)⁻¹ :
          UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ t τ := by
      intro a ha k ha'
      have hb := BlockLines.bond_mem_innerBonds_of_mem_twoBlockHull hj hodd c hc a k ha ha'
      have hRb := hR _ hb
      simp only at hRb
      rw [hRb, inv_one, mul_one]
      exact hle τ (refineSite c.1 + siteOfCoords j a, k) hb
    have hsp : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
        ‖((pathHolonomy Rj (refineSite c.1) (bondContour F.blockSide h π c.2) *
          (polarUnit (contourAverage Rj c))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 0 := by
      intro h hh π
      rw [pathHolonomy_bondContour_eq_one hodd hj hR hc hh π, hcm, polarUnit_one]
      simp
    obtain ⟨h1, h2, h3⟩ := hM F j (X τ) Rj c (t τ) 0 hodd hj (ht0 τ) le_rfl hτ hc₀.le hbd hsp
    have hrel : relativeContourMean (X τ) Rj c = g τ := by
      simp [relativeContourMean, hcm, polarUnit_one, hg]
    rw [hrel] at h2 h3
    simp only [add_zero] at h2 h3
    exact ⟨h1, h2, h3⟩
  have hpd : HasDerivAt p (parallelAverage Rj f c) 0 := by
    simp only [hp, parallelAverage]
    refine HasDerivAt.const_smul (1 / (24 * (F.blockSide : ℝ) ^ 4) : ℝ) ?_
    refine HasDerivAt.fun_sum fun h hh => HasDerivAt.fun_sum fun π _ => HasDerivAt.fun_sum fun r hr => ?_
    refine hasDerivAt_adjointAction _ ?_
    exact hasDerivAt_pureGap hR h0 hd (b := BlockLines.lineBond c h r)
      (BlockLines.lineBond_mem_innerBonds hj hodd c hc h hh r (Finset.mem_range.1 hr))
  obtain ⟨z1, -, z3⟩ := hfact 0 (by rw [htz, mul_zero]; exact hc₀.le)
  have hp0 : p 0 = 0 := by
    rw [htz, mul_zero] at z1
    exact norm_le_zero_iff.1 z1
  have hg0 : g 0 = 1 := by
    rw [hp0, htz] at z3
    simp only [norm_zero, mul_zero, add_zero] at z3
    exact Subtype.ext (sub_eq_zero.1 (norm_le_zero_iff.1 z3))
  have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), (F.blockSide : ℝ) * t τ ≤ c₀ := by
    have : Tendsto (fun τ => (F.blockSide : ℝ) * t τ) (𝓝 0) (𝓝 0) := by
      simpa using htt.const_mul (F.blockSide : ℝ)
    exact this.eventually_le_const hc₀
  set K₁ : ℝ := 4 + C * c₀ with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set K : ℝ := (C + (1 / 2) * K₁ ^ 2) * (F.blockSide : ℝ) ^ 2 with hK
  have hbound : ∀ᶠ τ in 𝓝 (0 : ℝ), ‖((g τ : UnitQuaternion) : ℍ[ℝ]) - 1 - p τ‖ ≤ K * ‖t τ * t τ‖ := by
    filter_upwards [hev] with τ hτ
    obtain ⟨a1, a2, a3⟩ := hfact τ hτ
    set A : ℝ := (F.blockSide : ℝ) * t τ with hA
    have hA0 : 0 ≤ A := mul_nonneg hLpos.le (ht0 τ)
    have b1 : ‖((g τ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ K₁ * A := by
      have : C * A * A ≤ C * c₀ * A := by
        have := mul_le_mul_of_nonneg_left hτ (mul_nonneg hC.le hA0)
        nlinarith
      rw [hK₁]
      nlinarith
    have e1 : ((g τ : UnitQuaternion) : ℍ[ℝ]) - 1 - p τ =
        (pureComponent ((g τ : UnitQuaternion) : ℍ[ℝ]) - p τ) +
        (((((g τ : UnitQuaternion) : ℍ[ℝ]).re - 1 : ℝ)) : ℍ[ℝ]) := by
      have := re_add_pureComponent ((g τ : UnitQuaternion) : ℍ[ℝ])
      nth_rewrite 1 [← this]
      push_cast
      abel
    have e2 : ‖(((((g τ : UnitQuaternion) : ℍ[ℝ]).re - 1 : ℝ)) : ℍ[ℝ])‖ ≤ (1 / 2) * (K₁ * A) ^ 2 := by
      rw [Quaternion.norm_coe, Real.norm_eq_abs, abs_sub_comm, one_sub_re_eq_half_norm_sub_one_sq,
        abs_of_nonneg (by positivity)]
      have := pow_le_pow_left₀ (norm_nonneg _) b1 2
      linarith
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [Real.norm_of_nonneg (mul_nonneg (ht0 τ) (ht0 τ)), hK]
    have : C * A * A + (1 / 2) * (K₁ * A) ^ 2 =
        (C + (1 / 2) * K₁ ^ 2) * (F.blockSide : ℝ) ^ 2 * (t τ * t τ) := by
      rw [hA]
      ring
    linarith
  have hsq : (fun τ => t τ * t τ) =o[𝓝 0] (fun τ : ℝ => τ) := by
    have a1 : t =o[𝓝 0] (fun _ => (1 : ℝ)) := (Asymptotics.isLittleO_one_iff ℝ).2 htt
    simpa using a1.mul_isBigO htO
  have hlo : (fun τ => ((g τ : UnitQuaternion) : ℍ[ℝ]) - 1 - p τ) =o[𝓝 0] (fun τ : ℝ => τ) :=
    (Asymptotics.IsBigO.of_bound K hbound).trans_isLittleO hsq
  refine ⟨?_, hg0, ?_⟩
  · rw [hasDerivAt_iff_isLittleO] at hpd ⊢
    simp only [sub_zero, hp0] at hpd ⊢
    refine (hlo.add hpd).congr_left fun τ => ?_
    show ((g τ : UnitQuaternion) : ℍ[ℝ]) - 1 - p τ + (p τ - τ • parallelAverage Rj f c) =
      ((g τ : UnitQuaternion) : ℍ[ℝ]) - ((g 0 : UnitQuaternion) : ℍ[ℝ]) - τ • parallelAverage Rj f c
    rw [hg0]
    simp only [OneMemClass.coe_one]
    abel
  · have hdiff : GaugeDifferentiableOn X (0 : ℝ) (sitesOfCells S j : Set (F.Site j)) := fun x i hx hx' =>
      (hd (x, i) (mem_innerBonds hx hx')).differentiableAt
    have hcont := (differentiableAt_contourAverage hodd hj hdiff hc).continuousAt
    have e0 : contourAverage (X 0) c = 1 := by
      rw [contourAverage_congr hodd hj (gaugeAgreeOnBonds_one (Rj := X 0) h0) hc, contourAverage_one hodd]
    have hn : ∀ τ, ‖gaugedContourAverage (X τ) (balancingGauge (X τ) Rj) c‖ = ‖contourAverage (X τ) c‖ :=
      fun τ => by
      simp only [gaugedContourAverage, norm_mul, norm_coe_unitQuaternion, one_mul, mul_one]
    simp only [hn]
    have := hcont.norm
    simp only [ContinuousAt, e0, norm_one] at this
    exact this
end BondStep
section ChainTerms
variable {S : Finset F.Cell} {R : F.FieldChain} {T : ℝ → ChainChart F} {D : ChainChart F}
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem referenceDefect_eq_one (hodd : Odd F.blockSide)
    (hR : ∀ j, j < F.top → ∀ b ∈ innerBonds S j, R j b.1 b.2 = 1) {j : ℕ}
    (hj : j + 1 < F.top) {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1)) :
    referenceDefect R j c = 1 := by
  unfold referenceDefect
  rw [hR (j + 1) hj c hc, contourAverage_eq_one_of_trivial hodd (by omega) (hR j (by omega)) hc, polarUnit_one]
  simp
theorem chartField_firstOrder (hM : contourMeanFirstOrderStatement) (hodd : Odd F.blockSide)
    (hR : ∀ j, j < F.top → ∀ b ∈ innerBonds S j, R j b.1 b.2 = 1) (hT : HasFirstOrderOn S T D) :
    ∀ j, j < F.top → (∀ b ∈ innerBonds S j, chartField R (T 0) j b.1 b.2 = 1) ∧
      ∀ b ∈ innerBonds S j, HasDerivAt (fun τ => ((chartField R (T τ) j b.1 b.2 : UnitQuaternion) : ℍ[ℝ]))
        (linearPart R D j b.1 b.2) 0 := by
  intro j
  induction j with
  | zero =>
    intro h0
    constructor
    · intro b hb
      simp only [chartField]
      rw [hT.fine_zero b hb, hR 0 h0 b hb, expUnit_zero, mul_one]
    · intro b hb
      have := hasDerivAt_expUnit (hT.fine_deriv b hb) (hT.fine_zero b hb)
      refine this.congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
      simp only [chartField]
      rw [hR 0 h0 b hb, mul_one]
  | succ j ih =>
    intro hj
    obtain ⟨i0, i1⟩ := ih (by omega)
    have hs := fun (c : F.Site (j + 1) × Fin 4) (hc : c ∈ innerBonds S (j + 1)) =>
      hasDerivAt_polarUnit_gaugedContourAverage hM hodd (by omega : j < F.top) (hR j (by omega)) i0 i1 hc
    constructor
    · intro b hb
      obtain ⟨-, e, -⟩ := hs b hb
      have hdef : referenceDefect R j (b.1, b.2) = 1 := referenceDefect_eq_one hodd hR hj hb
      simp only [chartField]
      rw [hT.coarse_zero j hj b hb, hdef, expUnit_zero, mul_one, one_mul]
      exact e
    · intro b hb
      obtain ⟨d1, e, -⟩ := hs b hb
      have hdef : referenceDefect R j (b.1, b.2) = 1 := referenceDefect_eq_one hodd hR hj hb
      have h2 := hasDerivAt_mul_of_eq_one
        (hasDerivAt_expUnit (hT.coarse_deriv j hj b hb) (hT.coarse_zero j hj b hb)) d1
        (by rw [hT.coarse_zero j hj b hb, expUnit_zero]) e
      have hlin : linearPart R D (j + 1) b.1 b.2 = ((D.coarse j b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) +
          parallelAverage (R j) (linearPart R D j) b := by
        simp only [linearPart, if_pos hj]
        rw [add_comm]
      rw [hlin]
      refine h2.congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
      simp only [chartField]
      rw [hdef, mul_one]
theorem plaquetteHolonomy_eq (X : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) :
    plaquetteHolonomy X p = X p.1 p.2.1 * (X (p.1 + unitStep 0 p.2.1) p.2.2 *
      ((X (p.1 + unitStep 0 p.2.2) p.2.1)⁻¹ * (X p.1 p.2.2)⁻¹)) := by
  have e1 : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 - unitStep 0 p.2.1 = p.1 + unitStep 0 p.2.2 := by abel
  have e2 : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 + -unitStep 0 p.2.1 - unitStep 0 p.2.2 = p.1 := by abel
  simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
    if_false, e1, e2, mul_one]
theorem plaquetteHolonomy_firstOrder (hM : contourMeanFirstOrderStatement) (hodd : Odd F.blockSide)
    (hR : ∀ j, j < F.top → ∀ b ∈ innerBonds S j, R j b.1 b.2 = 1) (hT : HasFirstOrderOn S T D)
    {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S 0) :
    plaquetteHolonomy (chartField R (T 0) 0) p = 1 ∧
      HasDerivAt (fun τ => ((plaquetteHolonomy (chartField R (T τ) 0) p : UnitQuaternion) : ℍ[ℝ]))
        (linearizedCurl (R 0) D.fine p) 0 := by
  have h0n : 0 < F.top := Nat.succ_pos _
  obtain ⟨v0, vd⟩ := chartField_firstOrder hM hodd hR hT 0 h0n
  have hc := (Finset.mem_filter.1 hp).2.2
  have c1 : p.1 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c2 : p.1 + unitStep 0 p.2.1 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c3 : p.1 + unitStep 0 p.2.2 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c4 : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have b1 : (p.1, p.2.1) ∈ innerBonds S 0 := mem_innerBonds c1 c2
  have b2 : (p.1 + unitStep 0 p.2.1, p.2.2) ∈ innerBonds S 0 := mem_innerBonds c2 c4
  have b3 : (p.1 + unitStep 0 p.2.2, p.2.1) ∈ innerBonds S 0 :=
    mem_innerBonds c3 (by rw [add_right_comm]; exact c4)
  have b4 : (p.1, p.2.2) ∈ innerBonds S 0 := mem_innerBonds c1 c3
  have z1 := v0 _ b1
  have z2 := v0 _ b2
  have z3 := v0 _ b3
  have z4 := v0 _ b4
  simp only at z1 z2 z3 z4
  constructor
  · rw [plaquetteHolonomy_eq, z1, z2, z3, z4]
    simp
  · have d1 := vd _ b1
    have d2 := vd _ b2
    have d3 := vd _ b3
    have d4 := vd _ b4
    simp only at d1 d2 d3 d4
    have h34 := hasDerivAt_mul_of_eq_one (hasDerivAt_inv d3) (hasDerivAt_inv d4)
      (by rw [z3, inv_one]) (by rw [z4, inv_one])
    have h234 := hasDerivAt_mul_of_eq_one d2 h34 z2 (by rw [z3, z4, inv_one, one_mul])
    have h1234 := hasDerivAt_mul_of_eq_one d1 h234 z1 (by rw [z2, z3, z4, inv_one, one_mul, one_mul])
    have hcurl : linearizedCurl (R 0) D.fine p = linearPart R D 0 p.1 p.2.1 +
        (linearPart R D 0 (p.1 + unitStep 0 p.2.1) p.2.2 +
          (star (linearPart R D 0 (p.1 + unitStep 0 p.2.2) p.2.1) + star (linearPart R D 0 p.1 p.2.2))) := by
      have r1 := hR 0 h0n _ b1
      have r2 := hR 0 h0n _ b2
      have r3 := hR 0 h0n _ b3
      have r4 := hR 0 h0n _ b4
      simp only at r1 r2 r3 r4
      simp only [linearizedCurl, r1, r2, r3, r4, linearPart]
      rw [star_eq_neg_of_re_eq_zero (D.fine (p.1 + unitStep 0 p.2.2) p.2.1).2,
        star_eq_neg_of_re_eq_zero (D.fine p.1 p.2.2).2]
      simp [adjointAction]
      abel
    rw [hcurl]
    refine h1234.congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
    simp only [plaquetteHolonomy_eq]
theorem tendsto_plaquette_term (hM : contourMeanFirstOrderStatement) (hodd : Odd F.blockSide)
    (hR : ∀ j, j < F.top → ∀ b ∈ innerBonds S j, R j b.1 b.2 = 1) (hT : HasFirstOrderOn S T D)
    (W : ℝ → F.GaugeField F.top) {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S 0) :
    (1 - ((plaquetteHolonomy (chartChain R (T 0) (W 0) 0) p : UnitQuaternion) : ℍ[ℝ]).re = 0) ∧
    Tendsto (fun τ : ℝ =>
        (1 - ((plaquetteHolonomy (chartChain R (T τ) (W τ) 0) p : UnitQuaternion) : ℍ[ℝ]).re) / τ ^ 2)
      (𝓝[≠] 0) (𝓝 ((1 / 2) * ‖linearizedCurl (R 0) D.fine p‖ ^ 2)) := by
  have h0n : 0 < F.top := Nat.succ_pos _
  obtain ⟨e0, ed⟩ := plaquetteHolonomy_firstOrder hM hodd hR hT hp
  simp only [chartChain_of_lt R _ _ h0n]
  refine ⟨by rw [e0]; simp, ?_⟩
  exact tendsto_one_sub_re_div_sq (g := fun τ => plaquetteHolonomy (chartField R (T τ) 0) p) ed e0
theorem tendsto_interior_term (hM : contourMeanFirstOrderStatement) (hodd : Odd F.blockSide)
    (hR : ∀ j, j < F.top → ∀ b ∈ innerBonds S j, R j b.1 b.2 = 1) (hT : HasFirstOrderOn S T D)
    (W : ℝ → F.GaugeField F.top) {j : ℕ} (hj : j + 1 < F.top) {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ innerBonds S (j + 1)) :
    gaugedBlockFit (chartChain R (T 0) (W 0) j) (chartGauge R (T 0) (j + 1))
        (chartChain R (T 0) (W 0) (j + 1)) c = 0 ∧
    Tendsto (fun τ : ℝ => gaugedBlockFit (chartChain R (T τ) (W τ) j) (chartGauge R (T τ) (j + 1))
        (chartChain R (T τ) (W τ) (j + 1)) c / τ ^ 2)
      (𝓝[≠] 0) (𝓝 ((1 / 2) * ‖((D.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2)) := by
  have hj' : j < F.top := by omega
  obtain ⟨i0, i1⟩ := chartField_firstOrder hM hodd hR hT j hj'
  obtain ⟨-, -, hn⟩ := hasDerivAt_polarUnit_gaugedContourAverage hM hodd hj' (hR j hj') i0 i1 hc
  have hdef : referenceDefect R j (c.1, c.2) = 1 := referenceDefect_eq_one hodd hR hj hc
  have hterm : ∀ τ, gaugedBlockFit (chartChain R (T τ) (W τ) j) (chartGauge R (T τ) (j + 1))
      (chartChain R (T τ) (W τ) (j + 1)) c =
      ‖gaugedContourAverage (chartField R (T τ) j) (balancingGauge (chartField R (T τ) j) (R j)) c‖ *
        (1 - (((expUnit ((T τ).coarse j c.1 c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]).re) := by
    intro τ
    rw [chartChain_of_lt R _ _ hj', chartChain_of_lt R _ _ hj, gaugedBlockFit_eq]
    have e : chartGauge R (T τ) (j + 1) = balancingGauge (chartField R (T τ) j) (R j) := rfl
    rw [e]
    congr 3
    simp only [chartField]
    rw [hdef, mul_one, mul_inv_rev, mul_inv_cancel_left]
  simp only [hterm]
  have hz := hT.coarse_zero j hj c hc
  refine ⟨by rw [hz, expUnit_zero]; simp, ?_⟩
  have hd := hasDerivAt_inv (hasDerivAt_expUnit (hT.coarse_deriv j hj c hc) hz)
  have := tendsto_norm_mul_one_sub_re_div_sq hn hd (by rw [hz, expUnit_zero, inv_one])
  rwa [Quaternion.norm_star] at this
theorem tendsto_top_term (hM : contourMeanFirstOrderStatement) (hodd : Odd F.blockSide)
    (hR : ∀ j, j < F.top → ∀ b ∈ innerBonds S j, R j b.1 b.2 = 1) (hT : HasFirstOrderOn S T D)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) {c : F.Site F.top × Fin 4}
    (hc : c ∈ innerBonds S F.top) :
    gaugedBlockFit (chartChain R (T 0) (rotatedFlatField v 0) F.depth) (chartGauge R (T 0) F.top)
        (chartChain R (T 0) (rotatedFlatField v 0) F.top) c = 0 ∧
    Tendsto (fun τ : ℝ => gaugedBlockFit (chartChain R (T τ) (rotatedFlatField v τ) F.depth)
        (chartGauge R (T τ) F.top) (chartChain R (T τ) (rotatedFlatField v τ) F.top) c / τ ^ 2)
      (𝓝[≠] 0) (𝓝 ((1 / 2) *
        ‖((v c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) - linearPart R D F.top c.1 c.2‖ ^ 2)) := by
  have hj' : F.depth < F.top := Nat.lt_succ_self _
  obtain ⟨i0, i1⟩ := chartField_firstOrder hM hodd hR hT F.depth hj'
  obtain ⟨hd, hg0, hn⟩ := hasDerivAt_polarUnit_gaugedContourAverage hM hodd hj' (hR F.depth hj') i0 i1 hc
  have hterm : ∀ τ, gaugedBlockFit (chartChain R (T τ) (rotatedFlatField v τ) F.depth)
      (chartGauge R (T τ) F.top) (chartChain R (T τ) (rotatedFlatField v τ) F.top) c =
      ‖gaugedContourAverage (chartField R (T τ) F.depth)
        (balancingGauge (chartField R (T τ) F.depth) (R F.depth)) c‖ *
        (1 - ((polarUnit (gaugedContourAverage (chartField R (T τ) F.depth)
            (balancingGauge (chartField R (T τ) F.depth) (R F.depth)) c) *
              (expUnit (τ • v c.1 c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]).re) := by
    intro τ
    rw [chartChain_of_lt R _ _ hj', chartChain_top, gaugedBlockFit_eq]
    have e : chartGauge R (T τ) F.top = balancingGauge (chartField R (T τ) F.depth) (R F.depth) := rfl
    rw [e]
    simp [rotatedFlatField, rotatedField, flatTopField]
  simp only [hterm]
  have hw : HasDerivAt (fun τ : ℝ => (((τ • v c.1 c.2 : imaginaryQuaternions)) : ℍ[ℝ]))
      ((v c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) 0 := by
    have := (hasDerivAt_id (0 : ℝ)).smul_const ((v c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])
    simpa using this
  have he := hasDerivAt_inv (hasDerivAt_expUnit hw (by simp))
  have hz : expUnit ((0 : ℝ) • v c.1 c.2) = 1 := by rw [zero_smul, expUnit_zero]
  have hprod := hasDerivAt_mul_of_eq_one hd he hg0 (by rw [hz, inv_one])
  refine ⟨by rw [hg0, hz]; simp, ?_⟩
  have := tendsto_norm_mul_one_sub_re_div_sq hn hprod (by rw [hg0, hz]; simp)
  have hlin : linearPart R D F.top c.1 c.2 = parallelAverage (R F.depth) (linearPart R D F.depth) c := by
    show linearPart R D (F.depth + 1) c.1 c.2 = _
    simp only [linearPart, lt_self_iff_false, if_false, add_zero]
  have hnorm : ‖parallelAverage (R F.depth) (linearPart R D F.depth) c +
        star ((v c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ =
      ‖((v c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) - linearPart R D F.top c.1 c.2‖ := by
    rw [hlin, star_eq_neg_of_re_eq_zero (v c.1 c.2).2, ← norm_neg]
    congr 1
    abel
  rwa [hnorm] at this
end ChainTerms
end FlatTopExpansion
open FlatTopExpansion in
theorem secondOrderAtFlatTop_proof (hM : contourMeanFirstOrderStatement) :
    secondOrderAtFlatTopStatement := by
  intro F S R a wp wc T D v hodd hR hT
  have hsplit : ∀ τ, weightedChainTerms a S wp wc (chartChain R (T τ) (rotatedFlatField v τ))
      (chartGauge R (T τ)) =
      ∑ p ∈ innerPlaquettes S 0, wp p *
          (1 - ((plaquetteHolonomy (chartChain R (T τ) (rotatedFlatField v τ) 0) p : UnitQuaternion) :
            ℍ[ℝ]).re) +
        a * (∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), wc j c *
            gaugedBlockFit (chartChain R (T τ) (rotatedFlatField v τ) j) (chartGauge R (T τ) (j + 1))
              (chartChain R (T τ) (rotatedFlatField v τ) (j + 1)) c +
          ∑ c ∈ innerBonds S F.top, wc F.depth c *
            gaugedBlockFit (chartChain R (T τ) (rotatedFlatField v τ) F.depth) (chartGauge R (T τ) F.top)
              (chartChain R (T τ) (rotatedFlatField v τ) F.top) c) := by
    intro τ
    unfold weightedChainTerms
    rw [show Finset.range F.top = Finset.range (F.depth + 1) from rfl, Finset.sum_range_succ]
  constructor
  · rw [hsplit]
    have h1 : ∑ p ∈ innerPlaquettes S 0, wp p *
        (1 - ((plaquetteHolonomy (chartChain R (T 0) (rotatedFlatField v 0) 0) p : UnitQuaternion) :
          ℍ[ℝ]).re) = 0 :=
      Finset.sum_eq_zero fun p hp => by
        rw [(tendsto_plaquette_term hM hodd hR hT (rotatedFlatField v) hp).1, mul_zero]
    have h2 : ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), wc j c *
        gaugedBlockFit (chartChain R (T 0) (rotatedFlatField v 0) j) (chartGauge R (T 0) (j + 1))
          (chartChain R (T 0) (rotatedFlatField v 0) (j + 1)) c = 0 :=
      Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun c hc => by
        rw [(tendsto_interior_term hM hodd hR hT (rotatedFlatField v)
          (by have := Finset.mem_range.1 hj; have hn : F.top = F.depth + 1 := rfl; omega : j + 1 < F.top)
          hc).1, mul_zero]
    have h3 : ∑ c ∈ innerBonds S F.top, wc F.depth c *
        gaugedBlockFit (chartChain R (T 0) (rotatedFlatField v 0) F.depth) (chartGauge R (T 0) F.top)
          (chartChain R (T 0) (rotatedFlatField v 0) F.top) c = 0 :=
      Finset.sum_eq_zero fun c hc => by rw [(tendsto_top_term hM hodd hR hT v hc).1, mul_zero]
    rw [h1, h2, h3]
    simp
  · have lp := tendsto_finsetSum (innerPlaquettes S 0) fun p hp =>
      ((tendsto_plaquette_term hM hodd hR hT (rotatedFlatField v) hp).2).const_mul (wp p)
    have lm := tendsto_finsetSum (Finset.range F.depth) fun j hj =>
      tendsto_finsetSum (innerBonds S (j + 1)) fun c hc =>
        ((tendsto_interior_term hM hodd hR hT (rotatedFlatField v)
          (by have := Finset.mem_range.1 hj; have hn : F.top = F.depth + 1 := rfl; omega : j + 1 < F.top)
          hc).2).const_mul (wc j c)
    have lt := tendsto_finsetSum (innerBonds S F.top) fun c hc =>
      ((tendsto_top_term hM hodd hR hT v hc).2).const_mul (wc F.depth c)
    have hall := lp.add ((lm.add lt).const_mul a)
    have hval : (1 / 2) * weightedQuadraticEnergy a S wp wc R D v =
        ∑ p ∈ innerPlaquettes S 0, wp p * ((1 / 2) * ‖linearizedCurl (R 0) D.fine p‖ ^ 2) +
          a * (∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
              wc j c * ((1 / 2) * ‖((D.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2) +
            ∑ c ∈ innerBonds S F.top, wc F.depth c *
              ((1 / 2) * ‖((v c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) - linearPart R D F.top c.1 c.2‖ ^ 2)) := by
      unfold weightedQuadraticEnergy
      have e1 : ∑ p ∈ innerPlaquettes S 0, wp p * ((1 / 2) * ‖linearizedCurl (R 0) D.fine p‖ ^ 2) =
          (1 / 2) * ∑ p ∈ innerPlaquettes S 0, wp p * ‖linearizedCurl (R 0) D.fine p‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      have e2 : ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
          wc j c * ((1 / 2) * ‖((D.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2) =
          (1 / 2) * ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
            wc j c * ‖((D.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      have e3 : ∑ c ∈ innerBonds S F.top, wc F.depth c *
            ((1 / 2) * ‖((v c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) - linearPart R D F.top c.1 c.2‖ ^ 2) =
          (1 / 2) * ∑ c ∈ innerBonds S F.top, wc F.depth c *
            ‖((v c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) - linearPart R D F.top c.1 c.2‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [e1, e2, e3]
      ring
    rw [hval]
    refine hall.congr fun τ => ?_
    rw [hsplit, add_div, mul_div_assoc, add_div, Finset.sum_div, Finset.sum_div, Finset.sum_div]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ => by rw [mul_div_assoc]
    · congr 2
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun _ _ => by rw [mul_div_assoc]
      · exact Finset.sum_congr rfl fun _ _ => by rw [mul_div_assoc]
end YangMills.Construction.BlockAverages
end
