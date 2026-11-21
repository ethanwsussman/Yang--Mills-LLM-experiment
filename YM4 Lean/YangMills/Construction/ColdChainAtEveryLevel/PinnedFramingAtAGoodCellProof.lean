import YangMills.Construction.ColdChainAtEveryLevel.CoordinatesOfAFramingOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.CurlOfAGapOnAPatchProof
import YangMills.Construction.ColdChainAtEveryLevel.GapsOfAFramingOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.GaugeFixedCorrectionGenerator
import YangMills.Construction.ColdChainAtEveryLevel.MorreyOfTheCriticalChainOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.PinDifferenceAtABond
import YangMills.Construction.ColdChainAtEveryLevel.PinnedFramingAtAGoodCell
import YangMills.Construction.ColdChainAtEveryLevel.RelativeEnergyOfAFramingOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.StartOfAFramingOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.TopGapOfAFramingOnAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.PinnedGaugeAtGoodCell
open BlockAverages PinnedGauge LatticeFractionalIntegration PatchLatticeChart GaugeMap PatchMorrey PatchCurls
variable {F : BlockFrame}
theorem zero_le_distFromOne (a : UnitQuaternion) : 0 ≤ _root_.YangMills.Construction.BlockAverages.distFromOne a := norm_nonneg _
theorem sqrt_sqrt_pow_four {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) ^ 4 = x := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.sqrt_sqrt_pow_four <;> assumption
theorem add_four_pow_four_le (x1 x2 x3 x4 : ℝ) :
    (x1 + x2 + x3 + x4) ^ 4 ≤ 64 * (x1 ^ 4 + x2 ^ 4 + x3 ^ 4 + x4 ^ 4) := by apply _root_.YangMills.Construction.PatchCurls.add_add_add_pow_four_le <;> assumption
section GaugeData
variable {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell} {W : F.FieldChain} {kW : F.SiteGauge}
  {X : F.FieldChain} {k : F.SiteGauge}
theorem defectQuarticSum_eq {m : ℕ} (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hm : 32 ≤ m)
    (hreg : IsOrthantRegular S m) (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (γ : Lattice4 → UnitQuaternion) :
    (pinnedGaugeDataOfPatch S V z W kW X k).defectQuarticSum γ = ∑ b ∈ patchInnerBonds S z 0,
      _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0 b.1 b.2) ^ 4 := by
  rw [← PatchLatticeChart.Framing.sum_bondsOf_siteBond hamb hodd hm hreg hs (fun c =>
    _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0 c.1 c.2) ^ 4)]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' := Finset.mem_filter.1 hb
  have h1 := PatchLatticeChart.Framing.latticeGaugeTransform_mul_inv_framed (V := V) hamb hodd hs γ (X 0) (W 0)
    (Finset.mem_product.1 hb'.1).1 hb'.2
  have h2 := PatchLatticeChart.Framing.norm_latticeField_mul_inv_sub_one hs
    (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) (X 0)) (W 0) b
  show ‖((gaugedGap S V z (X 0) (W 0) γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 = _
  have e : gaugedGap S V z (X 0) (W 0) γ b.1 b.2 = (frameChange S V z (patchSite S z b.1))⁻¹ *
      (latticeField S z (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) (X 0)) b.1 b.2 *
        (latticeField S z (W 0) b.1 b.2)⁻¹) *
        ((frameChange S V z (patchSite S z b.1))⁻¹)⁻¹ := by
    rw [inv_inv]
    exact h1
  rw [e, norm_coe_conj_sub_one, h2]
  rfl
theorem distFromOne_pinnedTopCorrection (γ : Lattice4 → UnitQuaternion) (y : F.Cell) :
    _root_.YangMills.Construction.BlockAverages.distFromOne (pinnedTopCorrection S V z W kW X k γ y) =
    _root_.YangMills.Construction.BlockAverages.distFromOne (topCorrection W kW X k (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) y) := by
  unfold pinnedTopCorrection
  have e : (patchFrame S V z y)⁻¹ *
      topCorrection W kW X k (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) y * patchFrame S V z y =
      (patchFrame S V z y)⁻¹ *
        topCorrection W kW X k (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) y *
          ((patchFrame S V z y)⁻¹)⁻¹ := by
    rw [inv_inv]
  rw [e]
  exact norm_coe_conj_sub_one _ _
def gaugeRelativeEnergy (a : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (W : F.FieldChain)
    (kW : F.SiteGauge) (X : F.FieldChain) (k : F.SiteGauge) (γ : Lattice4 → UnitQuaternion) : ℝ :=
  relativeEnergy a S z W kW X k (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ))
def curlBound (a : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (W : F.FieldChain) (kW : F.SiteGauge)
    (X : F.FieldChain) (k : F.SiteGauge) (γ : Lattice4 → UnitQuaternion) : ℝ :=
  Real.sqrt (Real.sqrt 32) * Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ)
theorem curlBound_pow_four {a : ℝ} (ha : 0 ≤ a) (γ : Lattice4 → UnitQuaternion)
    (h0 : 0 ≤ gaugeRelativeEnergy a S V z W kW X k γ) :
    curlBound a S V z W kW X k γ ^ 4 = 32 * gaugeRelativeEnergy a S V z W kW X k γ ^ 2 := by
  unfold curlBound
  rw [mul_pow, sqrt_sqrt_pow_four (by norm_num)]
  have e : Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ) ^ 4 =
      (Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ) ^ 2) ^ 2 := by ring
  rw [e, Real.sq_sqrt h0]
theorem plaquetteSum_le_gaugeRelativeEnergy {a : ℝ} (ha : 0 ≤ a) (γ : Lattice4 → UnitQuaternion) :
    ∑ q ∈ patchPlaquettes S z,
      ‖((plaquetteHolonomy (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) (X 0)) q : UnitQuaternion) : ℍ[ℝ]) -
      ((plaquetteHolonomy (W 0) q : UnitQuaternion) : ℍ[ℝ])‖ ^ 2 ≤ gaugeRelativeEnergy a S V z W kW X k γ := by
  unfold gaugeRelativeEnergy relativeEnergy
  have h : 0 ≤ a * ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j,
      ‖((bondMisfit (gaugedChainFields X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) j)
        (balancedLinkAgainst W kW
          (gaugedChainFields X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ))) j)
        (framedUpperField W kW X k (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) j) c *
          (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)⁻¹ : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 :=
    mul_nonneg ha (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
  exact le_add_of_nonneg_right h
theorem gaugeRelativeEnergy_nonneg {a : ℝ} (ha : 0 ≤ a) (γ : Lattice4 → UnitQuaternion) :
    0 ≤ gaugeRelativeEnergy a S V z W kW X k γ :=
  le_trans (Finset.sum_nonneg fun _ _ => by positivity)
    (plaquetteSum_le_gaugeRelativeEnergy (S := S) (V := V) (z := z) (W := W) (kW := kW) (X := X) (k := k) ha γ)
end GaugeData
theorem correction_difference_bound {x sa δ Q s CT ε P Pb v k k' T Ψ Ew w4 C₃ E ra : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 4 * sa + CT * (Q + s + δ) * (Q + δ) + (k + 2 * v) * k' + T) (hsa : sa = δ / ra) (hra : 0 < ra)
    (hδ : 0 ≤ δ) (hQ0 : 0 ≤ Q) (hQ : Q ≤ P) (hk0 : 0 ≤ k) (hk : k ≤ P) (hk0' : 0 ≤ k') (hk' : k' ≤ P) (hPb : P ≤ Pb)
    (hv : 0 ≤ v) (hT0 : 0 ≤ T) (hT : T ^ 4 ≤ C₃ * (16 * Ew * E)) (hC₃ : 0 ≤ C₃) (hE0 : 0 ≤ E) (hE : E ≤ Ψ)
    (hEw0 : 0 ≤ Ew) (hEw : Ew ≤ w4) (hP4 : P ^ 4 = Ψ) (hε : Q + s + δ ≤ ε) (hs : 0 ≤ s) (hCT : 0 ≤ CT)
    (hCε : CT * ε ≤ 1) :
    x ^ 4 ≤ (2 * (4 / ra + 1) ^ 4) * (32 * δ ^ 4) + 64 * ((CT * ε) ^ 4 + (Pb + 2 * v) ^ 4 + 16 * C₃ * w4) * Ψ := by
  have hε0 : 0 ≤ ε := le_trans (by positivity) hε
  have h1 : CT * (Q + s + δ) * (Q + δ) ≤ (CT * ε) * (P + δ) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hε hCT) (by linarith) (by positivity) (by positivity)
  have h2 : (CT * ε) * δ ≤ δ := by nlinarith
  have h3 : (k + 2 * v) * k' ≤ (Pb + 2 * v) * P :=
    mul_le_mul (by linarith) hk' hk0' (by linarith)
  have e1 : 4 * sa = 4 / ra * δ := by rw [hsa]; ring
  have hsum : x ≤ (4 / ra + 1) * δ + (CT * ε) * P + (Pb + 2 * v) * P + T := by
    have e3 : (4 / ra + 1) * δ = 4 / ra * δ + δ := by ring
    rw [e3]
    rw [e1] at hx
    linarith
  have h4 := (pow_le_pow_left₀ hx0 hsum 4).trans (add_four_pow_four_le _ _ _ _)
  have e4 : ((CT * ε) * P) ^ 4 = (CT * ε) ^ 4 * Ψ := by rw [mul_pow, hP4]
  have e5 : ((Pb + 2 * v) * P) ^ 4 = (Pb + 2 * v) ^ 4 * Ψ := by rw [mul_pow, hP4]
  have e6 : ((4 / ra + 1) * δ) ^ 4 = (4 / ra + 1) ^ 4 * δ ^ 4 := by rw [mul_pow]
  have h5 : T ^ 4 ≤ 16 * C₃ * w4 * Ψ := by
    refine hT.trans ?_
    have : Ew * E ≤ w4 * Ψ := mul_le_mul hEw hE hE0 (hEw0.trans hEw)
    have h6 := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 16 * C₃)
    calc C₃ * (16 * Ew * E) = 16 * C₃ * (Ew * E) := by ring
      _ ≤ 16 * C₃ * (w4 * Ψ) := h6
      _ = _ := by ring
  rw [e4, e5, e6] at h4
  have e7 : 2 * (4 / ra + 1) ^ 4 * (32 * δ ^ 4) + 64 * ((CT * ε) ^ 4 + (Pb + 2 * v) ^ 4 + 16 * C₃ * w4) * Ψ =
      64 * ((4 / ra + 1) ^ 4 * δ ^ 4 + (CT * ε) ^ 4 * Ψ + (Pb + 2 * v) ^ 4 * Ψ + 16 * C₃ * w4 * Ψ) := by ring
  rw [e7]
  linarith only [h4, h5]
section GaugeProblem
variable {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell} {W : F.FieldChain} {kW : F.SiteGauge}
  {X : F.FieldChain} {k : F.SiteGauge}
theorem pow_four_le_pinnedQuarticSum {γ : Lattice4 → UnitQuaternion} {y : F.Cell} (hy : y ∈ patchCells S z) :
    _root_.YangMills.Construction.BlockAverages.distFromOne (pinnedTopCorrection S V z W kW X k γ y) ^ 4 ≤
      (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ := by
  have h1 := Finset.single_le_sum
    (f := fun y => ‖(((pinnedGaugeDataOfPatch S V z W kW X k).pin γ y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4)
    (s := (pinnedGaugeDataOfPatch S V z W kW X k).cells) (fun _ _ => by positivity) hy
  have h2 : 0 ≤ (pinnedGaugeDataOfPatch S V z W kW X k).defectQuarticSum γ :=
    Finset.sum_nonneg fun _ _ => by positivity
  exact h1.trans (le_add_of_nonneg_left h2)
theorem isPinnedGaugeProblem (hPT : pinnedCorrectionGeneratorStatement) (hPD : pinnedBondDifferenceStatement)
    (hRd : pinnedCorrectionLocalityStatement) {Ccu : ℝ}
    (hCu : ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell)
      (X W : F.GaugeField 0) (γ : Lattice4 → UnitQuaternion), Odd F.blockSide → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      (∑ p ∈ orientedPlaquettesOf (patchDomain S z),
        ‖plaquetteCurl (fun a i => pureComponent ((gaugedGap S V z X W γ a i : UnitQuaternion) : ℍ[ℝ]))
          p.1 p.2.1 p.2.2‖ ^ 2) ^ 2 ≤
        32 * (∑ q ∈ patchPlaquettes S z,
          ‖((plaquetteHolonomy (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X) q : UnitQuaternion) : ℍ[ℝ]) -
          ((plaquetteHolonomy W q : UnitQuaternion) : ℍ[ℝ])‖ ^ 2) ^ 2 +
        Ccu * (∑ b ∈ bondsOf (patchDomain S z), ‖((gaugedGap S V z X W γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4) *
          (∑ b ∈ bondsOf (patchDomain S z), (‖((gaugedGap S V z X W γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 +
            ‖((framedLatticeField S V z W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4)))
    (hCu0 : 0 ≤ Ccu) {m : ℕ} {θ a C₃ n₀ A η b c₁ qg r v w4 ε CT Pb s : ℝ} {E : (j : ℕ) → F.Site (j + 1) → ℝ}
    (ha : 0 < a) (hodd : Odd F.blockSide) (h5 : 5 ≤ F.blockSide) (hamb : IsAdmissibleAmbient F) (hm : 1024 ≤ m)
    (hreg : IsOrthantRegular S m) (hz : z ∈ S)
    (hXW : X F.top = W F.top) (hC₃ : 0 ≤ C₃)
    (hcells : HasPatchCellConditions (pinnedGaugeDataOfPatch S V z W kW X k) 9 (47 ^ 4) C₃ n₀)
    (hlev : ∀ f g : F.Site 0 → Fin 4 → ℍ[ℝ], (∀ b ∈ patchInnerBonds S z 0, f b.1 b.2 = g b.1 b.2) →
      ∀ c ∈ patchInnerBonds S z F.top, iteratedBlockAverage f F.top c.1 c.2 = iteratedBlockAverage g F.top c.1 c.2)
    (hmor : ∀ (x : Lattice4) (r : ℕ), 1 ≤ r → r ≤ 80 * (pinnedGaugeDataOfPatch S V z W kW X k).scale →
      ∑ u ∈ (pinnedGaugeDataOfPatch S V z W kW X k).region.filter (fun u => supNorm (u - x) ≤ r),
        (pinnedGaugeDataOfPatch S V z W kW X k).targetWeight u ≤
        A * ((r : ℝ) / ((80 * (pinnedGaugeDataOfPatch S V z W kW X k).scale : ℕ) : ℝ)) ^ (4 * θ))
    (hne : ∀ γ, (pinnedGaugeDataOfPatch S V z W kW X k).defectQuarticSum γ ≤ c₁ → ∀ j, j < F.top →
      ∀ y ∈ sitesOfCells (patchCells S z) (j + 1),
      relativePathAverage (gaugeTransform (pinnedGaugeLevel W kW X k (siteGaugeOfLatticeGauge S V z γ) j) (X j))
        (W j) y ≠ 0)
    (hbc : b ≤ c₁) (hqg : 0 ≤ qg) (hr : 0 ≤ r) (he8 : 36 * (F.blockSide : ℝ) * qg + 8 * r ≤ 1 / 8)
    (hgaps : ∀ γ, (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ ≤ b → ∀ j, j < F.top →
      ∑ c ∈ patchInnerBonds S z j,
      distFromOne (relativeDefect W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) j c.1 c.2) ^ 4 ≤
        qg ^ 4)
    (hE0 : ∀ j y, 0 ≤ E j y)
    (hEs : ∀ j, j < F.top → ∑ y ∈ sitesOfCells (patchCells S z) (j + 1), E j y ^ 4 ≤ r ^ 4)
    (hk : ∀ j, j < F.top → ∀ y ∈ sitesOfCells (patchCells S z) (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (kW (j + 1) y) ≤ E j y)
    (hleg : ∀ j, j < F.top → ∀ y ∈ sitesOfCells (patchCells S z) (j + 1), ∀ h ∈ centredCube F.blockSide,
      ∀ π : Equiv.Perm (Fin 4),
      distFromOne ((patchFrame S V z (refineSite y))⁻¹ * pathHolonomy (W j) (refineSite y) (axisPath h π) *
        patchFrame S V z (refineSite y + siteOfCoords j h)) ≤ E j y)
    (hη2 : 9 * (36 * (F.blockSide : ℝ) * qg + 8 * r) ^ 4 ≤ η ^ 4) (hη0 : 0 ≤ η)
    (hEw : ∑ c ∈ bondsOf (patchDomain S z),
      ‖((framedLatticeField S V z (W 0) c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 ≤ w4)
    (hη1 : Ccu * (b + w4) ≤ η ^ 4)
    (htop : ∀ γ, (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ ≤ b → ∀ c ∈ patchInnerBonds S z F.top,
      ‖adjointAction (frameChange S V z (baseSite c.1))⁻¹ (pureComponent ((topDefect W kW X k
          (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) c.1 c.2 : UnitQuaternion) : ℍ[ℝ])) -
        iteratedBlockAverage
          (framedPureDefect S V z W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0)
          F.top c.1 c.2‖ ≤
      4 * Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ / a) +
        CT * (quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0 + s +
          Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ)) *
          (quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0 +
            Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ)))
    (hv0 : 0 ≤ v) (hv : ∀ c ∈ innerBonds (patchCells S z) F.top,
      _root_.YangMills.Construction.BlockAverages.distFromOne ((patchFrame S V z c.1)⁻¹ * W F.top c.1 c.2 * patchFrame S V z (c.1 + unitStep F.top c.2)) ≤ v)
    (hε : ∀ γ, (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ ≤ b →
      quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0 + s +
        Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ) ≤ ε)
    (hs0 : 0 ≤ s) (hCT : 0 ≤ CT) (hCε : CT * ε ≤ 1) (hPb0 : 0 ≤ Pb) (hPb : b ≤ Pb ^ 4)
    (hη3 : 64 * ((CT * ε) ^ 4 + (Pb + 2 * v) ^ 4 + 16 * C₃ * w4) ≤ η ^ 4)
    (hstart : ∃ γ : Lattice4 → UnitQuaternion, (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ ≤ b) :
    IsPinnedGaugeProblem (pinnedGaugeDataOfPatch S V z W kW X k) θ (2 * (4 / Real.sqrt a + 1) ^ 4) C₃ n₀ (47 ^ 4) 9
      A η b c₁ (curlBound a S V z W kW X k) := by
  classical
  obtain ⟨hs, -⟩ := closedOrthant_spec hreg (by omega : 32 ≤ m) z
  have hm32 : 32 ≤ m := by omega
  have hRd' := hRd F m S V z W kW X k hodd hamb hm hreg
  have hgap0 : ∀ γ, 0 ≤ (pinnedGaugeDataOfPatch S V z W kW X k).defectQuarticSum γ := fun γ =>
    Finset.sum_nonneg fun _ _ => by positivity
  have hEw0 : 0 ≤ ∑ c ∈ bondsOf (patchDomain S z),
      ‖((framedLatticeField S V z (W 0) c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hpin_gap : ∀ γ, (pinnedGaugeDataOfPatch S V z W kW X k).defectQuarticSum γ ≤
      (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ := fun γ =>
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
  refine { isFilled := hcells.filledToward, one_le_scale := hcells.scale_pos, one_le_cellSide := hcells.cellSide_pos,
           scale_le := hcells.scale_le_mul, cellSites_subset := hcells.cellSites_sub,
           card_cellSites := hcells.cellSites_card, base_mem := hcells.base_mem_cells,
           card_cells_le := hcells.cells_card_le, morrey_bound := hmor, pin_congr := hRd'.1,
           pin_continuousOn := ?_, curl_le := ?_, pin_hasDerivAt := ?_, pin_sub_le := ?_,
           bondAverage_add := hcells.average_add, bondAverage_congr := hcells.average_congr,
           bondAverage_difference := hcells.average_difference, bondAverage_le := hcells.average_pow_le,
           chain_bound := hcells.joined, exists_start := hstart }
  · intro y hy
    exact hRd'.2 {γ | (pinnedGaugeDataOfPatch S V z W kW X k).defectQuarticSum
      ((pinnedGaugeDataOfPatch S V z W kW X k).extendByOne γ) ≤ c₁}
      (fun μ hμ => hne _ hμ) y hy
  · intro γ hγ
    have h1 := hCu F m S V z (X 0) (W 0) γ hodd hamb hm hreg
    have hrel := plaquetteSum_le_gaugeRelativeEnergy (S := S) (V := V) (z := z) (W := W) (kW := kW) (X := X) (k := k)
      ha.le γ
    have hrel0 := gaugeRelativeEnergy_nonneg (S := S) (V := V) (z := z) (W := W) (kW := kW) (X := X) (k := k) ha.le γ
    have hD0 : 0 ≤ ∑ q ∈ patchPlaquettes S z,
        ‖((plaquetteHolonomy (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) (X 0)) q : UnitQuaternion) : ℍ[ℝ]) -
        ((plaquetteHolonomy (W 0) q : UnitQuaternion) : ℍ[ℝ])‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have h2 := pow_le_pow_left₀ hD0 hrel 2
    rw [curlBound_pow_four ha.le γ hrel0]
    have h3 : (∑ b ∈ bondsOf (patchDomain S z),
        (‖((gaugedGap S V z (X 0) (W 0) γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 +
        ‖((framedLatticeField S V z (W 0) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4)) ≤ b + w4 := by
      rw [Finset.sum_add_distrib]
      exact add_le_add ((hpin_gap γ).trans hγ) hEw
    have hΨ0 : 0 ≤ (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ := (hgap0 γ).trans (hpin_gap γ)
    have h4 : Ccu * (∑ b ∈ bondsOf (patchDomain S z),
        ‖((gaugedGap S V z (X 0) (W 0) γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4) *
        (∑ b ∈ bondsOf (patchDomain S z),
          (‖((gaugedGap S V z (X 0) (W 0) γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 +
          ‖((framedLatticeField S V z (W 0) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4)) ≤
        η ^ 4 * (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ := by
      have h5 : (∑ b ∈ bondsOf (patchDomain S z),
          ‖((gaugedGap S V z (X 0) (W 0) γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4) ≤
          (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ := hpin_gap γ
      have h6 : 0 ≤ ∑ b ∈ bondsOf (patchDomain S z),
          ‖((gaugedGap S V z (X 0) (W 0) γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 :=
        hgap0 γ
      have he2 : 0 ≤ ∑ b ∈ bondsOf (patchDomain S z),
          (‖((gaugedGap S V z (X 0) (W 0) γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 +
          ‖((framedLatticeField S V z (W 0) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4) :=
        Finset.sum_nonneg fun _ _ => by positivity
      have h7 := mul_le_mul h5 h3 he2 hΨ0
      have h8 := mul_le_mul_of_nonneg_left h7 hCu0
      have h9 := mul_le_mul_of_nonneg_right hη1 hΨ0
      rw [mul_assoc Ccu]
      refine h8.trans ?_
      rw [mul_comm ((pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ), ← mul_assoc]
      exact h9
    exact h1.trans (by
      have h8 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 32)
      exact add_le_add h8 h4)
  · intro γ hγ ξ y hy
    obtain ⟨ζ, hz1, hz2, hz3⟩ := hPT F m S V W kW X k γ ξ z y qg r E hodd h5 hamb hm hreg hz hy hqg hr he8 hE0 hEs hk
      hleg (hgaps γ hγ) (hne γ ((hpin_gap γ).trans (hγ.trans hbc)))
    refine ⟨ζ, hz1, hz2, hz3.trans ?_⟩
    have hN : (0 : ℝ) < (((pinnedGaugeDataOfPatch S V z W kW X k).cellSide : ℕ) : ℝ) ^ 4 := by
      have := hcells.cellSide_pos
      have h1 : (0 : ℝ) < ((pinnedGaugeDataOfPatch S V z W kW X k).cellSide : ℕ) := by exact_mod_cast this
      positivity
    have hsum0 : 0 ≤ ∑ x ∈ (pinnedGaugeDataOfPatch S V z W kW X k).cellSites y, ‖(ξ x : ℍ[ℝ])‖ ^ 4 :=
      Finset.sum_nonneg fun _ _ => by positivity
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hη2 hsum0) hN.le
  · intro γ hγ y hy y' hy' hadj
    have hrel0 := gaugeRelativeEnergy_nonneg (S := S) (V := V) (z := z) (W := W) (kW := kW) (X := X) (k := k) ha.le γ
    have hΨ0 : 0 ≤ (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ := (hgap0 γ).trans (hpin_gap γ)
    obtain ⟨T, hT0, hT, hd⟩ := hPD C₃ n₀ F m S V W kW X k γ z y y' _ v hC₃ hodd hamb hm hreg hz hy hy' hadj hXW
      hcells hlev (htop γ hγ) hv
    set P := Real.sqrt (Real.sqrt ((pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ)) with hP
    have hP4 : P ^ 4 = (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ := sqrt_sqrt_pow_four hΨ0
    have hP0 : 0 ≤ P := Real.sqrt_nonneg _
    have hle : ∀ t : ℝ, 0 ≤ t → t ^ 4 ≤ (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ → t ≤ P :=
      fun t h0 h1 => by
        rw [← hP4] at h1
        exact (pow_le_pow_iff_left₀ h0 hP0 (by norm_num)).1 h1
    have hQ4 : quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0 ^ 4 =
        (pinnedGaugeDataOfPatch S V z W kW X k).defectQuarticSum γ := by
      unfold quarticDefectNorm
      rw [defectQuarticSum_eq hamb hodd hm32 hreg hs γ]
      exact sqrt_sqrt_pow_four (Finset.sum_nonneg fun _ _ => by positivity)
    have hQ0 : 0 ≤ quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0 :=
      Real.sqrt_nonneg _
    have hPbP : P ≤ Pb := by
      have h1 : P ^ 4 ≤ Pb ^ 4 := by
        rw [hP4]
        exact hγ.trans hPb
      exact (pow_le_pow_iff_left₀ hP0 hPb0 (by norm_num)).1 h1
    have hsqrt : Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ / a) =
        Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ) / Real.sqrt a :=
      Real.sqrt_div hrel0 a
    have hcore := correction_difference_bound (norm_nonneg _) hd hsqrt (Real.sqrt_pos.2 ha) (Real.sqrt_nonneg _) hQ0
      (hle _ hQ0 (hQ4 ▸ hpin_gap γ)) (zero_le_distFromOne _)
      (hle _ (zero_le_distFromOne _) (pow_four_le_pinnedQuarticSum hy)) (zero_le_distFromOne _)
      (hle _ (zero_le_distFromOne _) (pow_four_le_pinnedQuarticSum hy')) hPbP hv0 hT0 hT hC₃ (hgap0 γ) (hpin_gap γ)
      hEw0 hEw hP4 (hε γ hγ) hs0 hCT hCε
    refine (pow_le_pow_left₀ (norm_nonneg _) le_rfl 4).trans (hcore.trans ?_)
    rw [curlBound_pow_four ha.le γ hrel0]
    have e1 : Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ) ^ 4 = gaugeRelativeEnergy a S V z W kW X k γ ^ 2 := by
      have e : Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ) ^ 4 =
          (Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ) ^ 2) ^ 2 := by ring
      rw [e, Real.sq_sqrt hrel0]
    rw [e1]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hη3 hΨ0)
end GaugeProblem
section Assembly
variable {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
theorem norm_framedLatticeField_sub_one (hs : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (W : F.GaugeField 0) (b : Lattice4 × Fin 4) :
    ‖((framedLatticeField S V z W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ =
      _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform (fun x => (patchFrame S V z x)⁻¹) W (siteBond S z b).1 (siteBond S z b).2) := by
  obtain ⟨k1, k2⟩ := PatchForms.patchSite_add_basisVector_cases hs b.1 b.2
  have hfa : ∀ x : F.Site 0, patchFrame S V z x = frameChange S V z x := fun x => by
    unfold patchFrame
    rw [PatchLatticeChart.Framing.baseSite_eq_self]
  unfold framedLatticeField latticeField siteBond _root_.YangMills.Construction.BlockAverages.distFromOne
  rcases hs b.2 with h | h
  · simp only [h, if_true]
    unfold gaugeTransform
    simp only [hfa, inv_inv, ← k1 h]
  · have hne : closedOrthant S z b.2 ≠ 1 := by rw [h]; norm_num
    simp only [if_neg hne]
    unfold gaugeTransform
    simp only [hfa, inv_inv, ← k2 h]
    have e : (frameChange S V z (patchSite S z b.1))⁻¹ * (W (patchSite S z (b.1 + basisVector b.2)) b.2)⁻¹ *
        frameChange S V z (patchSite S z (b.1 + basisVector b.2)) =
        ((frameChange S V z (patchSite S z (b.1 + basisVector b.2)))⁻¹ *
          W (patchSite S z (b.1 + basisVector b.2)) b.2 *
          frameChange S V z (patchSite S z b.1))⁻¹ := by group
    rw [e, norm_coe_inv_sub_one]
theorem sqrt_sqrt_le_of_le_pow_four {x t : ℝ} (ht : 0 ≤ t) (h : x ≤ t ^ 4) (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) ≤ t := by
  have h1 := sqrt_sqrt_pow_four hx
  rw [← h1] at h
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) ht (by norm_num)).1 h
theorem ne_zero_of_norm_sub_one_le {A : ℍ[ℝ]} (h : ‖A - 1‖ ≤ 1 / 2) : A ≠ 0 := by
  intro h0
  rw [h0, zero_sub, norm_neg, norm_one] at h
  norm_num at h
theorem mul_pow_four_le {t u : ℝ} (ht : 0 ≤ t) (hu : 1 ≤ u) : u * t ^ 4 ≤ (u * t) ^ 4 := by
  rw [mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc u = u ^ 1 := (pow_one u).symm
    _ ≤ u ^ 4 := pow_le_pow_right₀ hu (by norm_num)
end Assembly
theorem constants_bounds {Lr CS CG CT CM CR Ccu C₃ cq cs e0 s Cp qK K2 A1 εK A3 Kc : ℝ} (hLr : 0 ≤ Lr) (hCS : 0 < CS)
    (hCG : 0 < CG) (hCT : 0 < CT) (hCM : 0 < CM) (hCR : 0 < CR) (hCcu : 0 < Ccu) (hC₃ : 0 ≤ C₃) (hcq : 0 < cq)
    (hcs : 0 < cs) (he0 : 0 < e0) (hs : 0 < s) (s7 : s ≤ e0) (hCp : Cp = CS * (1 + 47 ^ 4)) (hqK : qK = CG * (Cp + 2))
    (hK2 : K2 = 36 * Lr * qK + 8 * CR) (hA1 : A1 = Ccu * (Cp ^ 4 + CR ^ 4)) (hεK : εK = Cp + 5)
    (hA3 : A3 = 64 * ((CT * εK) ^ 4 + (Cp + 2 * CR) ^ 4 + 16 * C₃ * CR ^ 4)) (hKc : Kc = 1 + A1 + 2 * K2 + A3)
    (b5 : e0 ≤ 1 / (1 + Cp)) (b6 : e0 ≤ cq / (2 * (1 + Cp))) (b7 : e0 ≤ 1 / (8 * (1 + K2)))
    (b8 : e0 ≤ 1 / (1 + CT * εK)) (b9 : e0 ≤ cs / Kc) (b11 : e0 ≤ min 1 cs / (1 + CM)) :
    Cp * e0 ≤ 1 ∧ Cp * e0 < cq ∧ 36 * Lr * (qK * e0) + 8 * (CR * s) ≤ 1 / 8 ∧
      9 * (36 * Lr * (qK * e0) + 8 * (CR * s)) ^ 4 ≤ (Kc * e0) ^ 4 ∧
      Ccu * ((Cp * e0) ^ 4 + (CR * s) ^ 4) ≤ (Kc * e0) ^ 4 ∧
      64 * ((CT * (εK * e0)) ^ 4 + (Cp * e0 + 2 * (CR * s)) ^ 4 + 16 * C₃ * (CR * s) ^ 4) ≤ (Kc * e0) ^ 4 ∧
      CT * (εK * e0) ≤ 1 ∧ (CM * s) ^ 4 ≤ cs ∧ Kc * e0 ≤ cs := by
  have hCp0 : 0 < Cp := by rw [hCp]; positivity
  have hqK0 : 0 < qK := by rw [hqK]; positivity
  have hK20 : 0 < K2 := by rw [hK2]; positivity
  have hA10 : 0 < A1 := by rw [hA1]; positivity
  have hεK0 : 0 < εK := by rw [hεK]; positivity
  have hA30 : 0 ≤ A3 := by rw [hA3]; positivity
  have hKc1 : 1 ≤ Kc := by rw [hKc]; linarith
  have hKc0 : 0 < Kc := by linarith
  have hCe : Cp * e0 ≤ 1 := by
    have h1 := (le_div_iff₀ (by positivity)).1 b5
    nlinarith
  have hCq : Cp * e0 ≤ cq / 2 := by
    have h1 := (le_div_iff₀ (by positivity)).1 b6
    nlinarith
  have hCq' : Cp * e0 < cq := by linarith
  have hss : CR * s ≤ CR * e0 := mul_le_mul_of_nonneg_left s7 hCR.le
  have hcs0 : 0 ≤ CR * s := by positivity
  have he04 : 0 ≤ e0 ^ 4 := by positivity
  have hxK : 36 * Lr * (qK * e0) + 8 * (CR * s) ≤ K2 * e0 := by
    rw [hK2]
    nlinarith only [hss]
  have hK2e : 8 * (K2 * e0) ≤ 1 := by
    have h1 := (le_div_iff₀ (by positivity)).1 b7
    nlinarith only [h1, he0]
  have he8 : 36 * Lr * (qK * e0) + 8 * (CR * s) ≤ 1 / 8 := by linarith only [hxK, hK2e]
  have hKK : Kc ≤ Kc ^ 4 := by
    calc Kc = Kc ^ 1 := (pow_one _).symm
      _ ≤ Kc ^ 4 := pow_le_pow_right₀ hKc1 (by norm_num)
  have hη4 : (Kc * e0) ^ 4 = Kc ^ 4 * e0 ^ 4 := mul_pow _ _ _
  have hKe : ∀ t : ℝ, t ≤ Kc → t * e0 ^ 4 ≤ (Kc * e0) ^ 4 := fun t ht => by
    rw [hη4]
    exact mul_le_mul_of_nonneg_right (ht.trans hKK) he04
  have hη2 : 9 * (36 * Lr * (qK * e0) + 8 * (CR * s)) ^ 4 ≤ (Kc * e0) ^ 4 := by
    have h1 : 2 * (36 * Lr * (qK * e0) + 8 * (CR * s)) ≤ Kc * e0 := by
      have h2 : 2 * K2 ≤ Kc := by
        rw [hKc]
        linarith only [hA10, hA30]
      nlinarith only [h2, hxK, he0]
    have h3 := pow_le_pow_left₀ (by positivity) h1 4
    have h4 : 0 ≤ (36 * Lr * (qK * e0) + 8 * (CR * s)) ^ 4 := by positivity
    rw [mul_pow] at h3
    linarith only [h3, h4]
  have hw4 : (CR * s) ^ 4 ≤ CR ^ 4 * e0 ^ 4 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hcs0 hss 4
  have hη1 : Ccu * ((Cp * e0) ^ 4 + (CR * s) ^ 4) ≤ (Kc * e0) ^ 4 := by
    have h1 : Ccu * ((Cp * e0) ^ 4 + (CR * s) ^ 4) ≤ A1 * e0 ^ 4 := by
      rw [hA1, mul_pow]
      nlinarith only [mul_le_mul_of_nonneg_left hw4 hCcu.le]
    refine h1.trans (hKe A1 ?_)
    rw [hKc]
    linarith only [hK20, hA30]
  have hη3 : 64 * ((CT * (εK * e0)) ^ 4 + (Cp * e0 + 2 * (CR * s)) ^ 4 + 16 * C₃ * (CR * s) ^ 4) ≤
      (Kc * e0) ^ 4 := by
    have h1 : (Cp * e0 + 2 * (CR * s)) ^ 4 ≤ (Cp + 2 * CR) ^ 4 * e0 ^ 4 := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ 4
      nlinarith only [hss]
    have h2 : (CT * (εK * e0)) ^ 4 = (CT * εK) ^ 4 * e0 ^ 4 := by ring
    have h3 : 16 * C₃ * (CR * s) ^ 4 ≤ 16 * C₃ * (CR ^ 4 * e0 ^ 4) :=
      mul_le_mul_of_nonneg_left hw4 (by positivity)
    have h4 : 64 * ((CT * (εK * e0)) ^ 4 + (Cp * e0 + 2 * (CR * s)) ^ 4 + 16 * C₃ * (CR * s) ^ 4) ≤
        A3 * e0 ^ 4 := by
      rw [h2, hA3]
      nlinarith only [h1, h3]
    refine h4.trans (hKe A3 ?_)
    rw [hKc]
    linarith only [hK20, hA10]
  have hCε : CT * (εK * e0) ≤ 1 := by
    have h1 := (le_div_iff₀ (by positivity)).1 b8
    nlinarith only [h1, he0]
  have hAc : (CM * s) ^ 4 ≤ cs := by
    have h1 := (le_div_iff₀ (by positivity)).1 b11
    have h2 : CM * s ≤ min 1 cs := by
      have : CM * s ≤ CM * e0 := mul_le_mul_of_nonneg_left s7 hCM.le
      nlinarith only [this, h1, he0]
    have h3 : CM * s ≤ 1 := h2.trans (min_le_left _ _)
    have h4 : 0 ≤ CM * s := by positivity
    calc (CM * s) ^ 4 ≤ (CM * s) ^ 1 := pow_le_pow_of_le_one h4 h3 (by norm_num)
      _ = CM * s := pow_one _
      _ ≤ cs := h2.trans (min_le_right _ _)
  have hηc : Kc * e0 ≤ cs := by
    have h1 := (le_div_iff₀ hKc0).1 b9
    linarith only [h1]
  exact ⟨hCe, hCq', he8, hη2, hη1, hη3, hCε, hAc, hηc⟩
set_option maxHeartbeats 4000000 in
theorem exists_pinnedGauge_of_bounds (hPT : pinnedCorrectionGeneratorStatement) (hPD : pinnedBondDifferenceStatement)
    (hRd : pinnedCorrectionLocalityStatement) {Ccu : ℝ}
    (hCu : ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell)
      (X W : F.GaugeField 0) (γ : Lattice4 → UnitQuaternion), Odd F.blockSide → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      (∑ p ∈ orientedPlaquettesOf (patchDomain S z),
        ‖plaquetteCurl (fun a i => pureComponent ((gaugedGap S V z X W γ a i : UnitQuaternion) : ℍ[ℝ]))
          p.1 p.2.1 p.2.2‖ ^ 2) ^ 2 ≤
        32 * (∑ q ∈ patchPlaquettes S z,
          ‖((plaquetteHolonomy (gaugeTransform (siteGaugeOfLatticeGauge S V z γ) X) q : UnitQuaternion) : ℍ[ℝ]) -
          ((plaquetteHolonomy W q : UnitQuaternion) : ℍ[ℝ])‖ ^ 2) ^ 2 +
        Ccu * (∑ b ∈ bondsOf (patchDomain S z), ‖((gaugedGap S V z X W γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4) *
          (∑ b ∈ bondsOf (patchDomain S z), (‖((gaugedGap S V z X W γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 +
            ‖((framedLatticeField S V z W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4)))
    (hCu0 : 0 ≤ Ccu) {a θ C₃ n₀ Cs cs CG CT CS CM CR Cp qK εK Kc cq Cq Cf e0 s : ℝ}
    (hM : ∀ (D : PinnedGaugeData) (A η b c₁ : ℝ) (d : (Lattice4 → UnitQuaternion) → ℝ), 0 ≤ A → A ≤ cs → 0 ≤ η →
      η ≤ cs → 0 ≤ b → b ≤ 1 → b < c₁ →
      (∀ γ, 0 ≤ d γ) → IsPinnedGaugeProblem D θ (2 * (4 / Real.sqrt a + 1) ^ 4) C₃ n₀ (47 ^ 4) 9 A η b c₁ d →
      ∃ γ : Lattice4 → UnitQuaternion, D.pinnedQuarticSum γ ≤ b ∧ D.pinnedQuarticSum γ ≤ Cs * d γ ^ 4)
    {m : ℕ} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell} {W : F.FieldChain} {kW : F.SiteGauge}
    {X : F.FieldChain} {k : F.SiteGauge}
    (ha : 0 < a) (hCs : 0 < Cs) (hCG : 0 < CG) (hCT : 0 < CT) (hCS : 0 < CS) (hCM : 0 < CM) (hCR : 0 < CR)
    (hCp0 : 0 < Cp) (hqKd : qK = CG * (Cp + 2)) (hεKd : εK = Cp + 5) (hCpd : Cp = CS * (1 + 47 ^ 4)) (hcq0 : 0 < cq)
    (hKc0 : 0 < Kc) (hCqd : Cq = Real.sqrt (Real.sqrt (32 * Cs))) (hCfd : Cf = 4 * (Cq + Real.sqrt (2 / a)) + 1)
    (he0 : 0 < e0) (hs : 0 < s) (s7 : s ≤ e0) (hCe : Cp * e0 ≤ 1) (hCq' : Cp * e0 < cq)
    (he8 : 36 * (F.blockSide : ℝ) * (qK * e0) + 8 * (CR * s) ≤ 1 / 8)
    (hη2 : 9 * (36 * (F.blockSide : ℝ) * (qK * e0) + 8 * (CR * s)) ^ 4 ≤ (Kc * e0) ^ 4)
    (hη1 : Ccu * ((Cp * e0) ^ 4 + (CR * s) ^ 4) ≤ (Kc * e0) ^ 4)
    (hη3 : 64 * ((CT * (εK * e0)) ^ 4 + (Cp * e0 + 2 * (CR * s)) ^ 4 + 16 * C₃ * (CR * s) ^ 4) ≤ (Kc * e0) ^ 4)
    (hCε : CT * (εK * e0) ≤ 1) (hAc : (CM * s) ^ 4 ≤ cs) (hηc : Kc * e0 ≤ cs)
    (hodd : Odd F.blockSide) (h5 : 5 ≤ F.blockSide) (hamb : IsAdmissibleAmbient F) (hm : 1024 ≤ m)
    (hreg : IsOrthantRegular S m) (hz : z ∈ S)
    (hXW : X F.top = W F.top) (hC₃ : 0 ≤ C₃)
    (hPC1 : HasPatchCellConditions (pinnedGaugeDataOfPatch S V z W kW X k) 9 (47 ^ 4) C₃ n₀)
    (hlevel : ∀ f g : F.Site 0 → Fin 4 → ℍ[ℝ], (∀ b ∈ patchInnerBonds S z 0, f b.1 b.2 = g b.1 b.2) →
      ∀ c ∈ patchInnerBonds S z F.top, iteratedBlockAverage f F.top c.1 c.2 = iteratedBlockAverage g F.top c.1 c.2)
    (hGleg : ∀ γ : F.Site 0 → UnitQuaternion, quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k γ) 0 ≤ cq →
      ∀ j, j < F.top → ∀ y ∈ sitesOfCells S (j + 1), baseSite y ∈ patchBaseSites S z →
        ‖relativePathAverage (gaugedChainFields X (pinnedGaugeOfBase W kW X k γ) j) (W j) y - 1‖ ≤ 1 / 2)
    (hGlev : ∀ γ : F.Site 0 → UnitQuaternion, quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k γ) 0 ≤ cq →
      ∀ j, j < F.top →
      quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k γ) j ≤
        CG * (quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k γ) 0 + e0 + s))
    (hGlast : ∀ γ : F.Site 0 → UnitQuaternion, quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k γ) 0 ≤ cq →
      ∀ j, j < F.top →
      quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k γ) j ≤
        4 * (quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k γ) 0 +
        Real.sqrt (2 / a * relativeEnergy a S z W kW X k (pinnedGaugeOfBase W kW X k γ))))
    (hT2 : ∀ γ : F.Site 0 → UnitQuaternion, quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k γ) 0 ≤ cq →
      ∀ c ∈ patchInnerBonds S z F.top,
      ‖adjointAction (frameChange S V z (baseSite c.1))⁻¹
          (pureComponent ((topDefect W kW X k (pinnedGaugeOfBase W kW X k γ) c.1 c.2 : UnitQuaternion) : ℍ[ℝ])) -
        iteratedBlockAverage (framedPureDefect S V z W X (pinnedGaugeOfBase W kW X k γ) 0) F.top c.1 c.2‖ ≤
      4 * Real.sqrt (relativeEnergy a S z W kW X k (pinnedGaugeOfBase W kW X k γ) / a) +
        CT * (quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k γ) 0 + s +
          Real.sqrt (relativeEnergy a S z W kW X k (pinnedGaugeOfBase W kW X k γ))) *
        (quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k γ) 0 +
          Real.sqrt (relativeEnergy a S z W kW X k (pinnedGaugeOfBase W kW X k γ))))
    (hS2 : ∃ γ : F.Site 0 → UnitQuaternion, quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k γ) 0 ≤ CS * e0 ∧
      ∀ y : F.Site F.top, baseSite y ∈ patchBaseSites S z →
        _root_.YangMills.Construction.BlockAverages.distFromOne (topCorrection W kW X k (pinnedGaugeOfBase W kW X k γ) y) ≤ CS * e0)
    (hR2 : ∀ γ : F.Site 0 → UnitQuaternion,
      relativeEnergy a S z W kW X k (pinnedGaugeOfBase W kW X k γ) ≤ 16 * e0 ^ 2)
    (hM2 : ∀ (x : Lattice4) (r : ℕ), 1 ≤ r → r ≤ 80 * (9 * (cellSideLength F).toNat) →
      ∑ u ∈ (patchDomain S z).filter (fun u => supNorm (u - x) ≤ r), frameDefectWeight S V z (W 0) u ≤
        (CM * s) ^ 4 * ((r : ℝ) / ((80 * (9 * (cellSideLength F).toNat) : ℕ) : ℝ)) ^ (4 * θ))
    {E : (j : ℕ) → F.Site (j + 1) → ℝ} (hE0 : ∀ j y, 0 ≤ E j y)
    (hEs : ∀ j, j < F.top → ∑ y ∈ sitesOfCells (patchCells S z) (j + 1), E j y ^ 4 ≤ (CR * s) ^ 4)
    (hEk : ∀ j, j < F.top → ∀ y ∈ sitesOfCells (patchCells S z) (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (kW (j + 1) y) ≤ E j y)
    (hEl : ∀ j, j < F.top → ∀ y ∈ sitesOfCells (patchCells S z) (j + 1), ∀ h ∈ centredCube F.blockSide,
      ∀ π : Equiv.Perm (Fin 4),
      distFromOne ((patchFrame S V z (refineSite y))⁻¹ * pathHolonomy (W j) (refineSite y) (axisPath h π) *
        patchFrame S V z (refineSite y + siteOfCoords j h)) ≤ E j y)
    (hr2 : ∀ c ∈ innerBonds (patchCells S z) F.top,
      _root_.YangMills.Construction.BlockAverages.distFromOne ((patchFrame S V z c.1)⁻¹ * W F.top c.1 c.2 * patchFrame S V z (c.1 + unitStep F.top c.2)) ≤
        CR * s)
    (hr3 : ∑ b ∈ innerBonds (patchCells S z) 0,
      _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform (fun x => (patchFrame S V z x)⁻¹) (W 0) b.1 b.2) ^ 4 ≤ (CR * s) ^ 4) :
    ∃ Γ : F.SiteGauge, IsPinnedGauge a Cf S z W kW X k Γ ∧ relativeEnergy a S z W kW X k Γ ≤ 16 * e0 ^ 2 := by
  classical
  obtain ⟨hsg, -⟩ := closedOrthant_spec hreg (by omega : 32 ≤ m) z
  have hm32 : 32 ≤ m := by omega
  have hpe : 0 ≤ Cp * e0 := by positivity
  have hb1 : (Cp * e0) ^ 4 ≤ 1 := pow_le_one₀ hpe hCe
  have hbc : (Cp * e0) ^ 4 < cq ^ 4 := pow_lt_pow_left₀ hCq' hpe (by norm_num)
  have hqe : ∀ γ : Lattice4 → UnitQuaternion,
      quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0 =
      Real.sqrt (Real.sqrt ((pinnedGaugeDataOfPatch S V z W kW X k).defectQuarticSum γ)) := by
    intro γ
    unfold quarticDefectNorm
    rw [defectQuarticSum_eq hamb hodd hm32 hreg hsg γ]
    rfl
  have hgap0 : ∀ γ, 0 ≤ (pinnedGaugeDataOfPatch S V z W kW X k).defectQuarticSum γ := fun γ =>
    Finset.sum_nonneg fun _ _ => by positivity
  have hpin_gap : ∀ γ, (pinnedGaugeDataOfPatch S V z W kW X k).defectQuarticSum γ ≤
      (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ := fun γ =>
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
  have hq_le : ∀ γ, (pinnedGaugeDataOfPatch S V z W kW X k).defectQuarticSum γ ≤ cq ^ 4 →
      quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0 ≤ cq :=
    fun γ h => by
      rw [hqe]
      exact sqrt_sqrt_le_of_le_pow_four hcq0.le h (hgap0 γ)
  have hne : ∀ γ, (pinnedGaugeDataOfPatch S V z W kW X k).defectQuarticSum γ ≤ cq ^ 4 → ∀ j, j < F.top →
      ∀ y ∈ sitesOfCells (patchCells S z) (j + 1),
      relativePathAverage (gaugeTransform (pinnedGaugeLevel W kW X k (siteGaugeOfLatticeGauge S V z γ) j) (X j))
        (W j) y ≠ 0 := by
    intro γ h j hj y hy
    obtain ⟨hy1, hy2⟩ := (mem_sitesOfCells_patchCells_iff hamb hodd hsg hj).1 hy
    exact ne_zero_of_norm_sub_one_le (hGleg (siteGaugeOfLatticeGauge S V z γ) (hq_le γ h) j hj y hy1 hy2)
  have hq_small : ∀ γ, (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ ≤ (Cp * e0) ^ 4 →
      quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0 ≤ Cp * e0 :=
    fun γ h => by
      rw [hqe]
      exact sqrt_sqrt_le_of_le_pow_four hpe ((hpin_gap γ).trans h) (hgap0 γ)
  have hsmall : ∀ γ, (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ ≤ (Cp * e0) ^ 4 →
      (pinnedGaugeDataOfPatch S V z W kW X k).defectQuarticSum γ ≤ cq ^ 4 := fun γ h =>
    (hpin_gap γ).trans (h.trans hbc.le)
  have hgaps : ∀ γ, (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ ≤ (Cp * e0) ^ 4 → ∀ j, j < F.top →
      ∑ c ∈ patchInnerBonds S z j,
      distFromOne (relativeDefect W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) j c.1 c.2) ^ 4 ≤
        (qK * e0) ^ 4 := by
    intro γ h j hj
    have h1 := hGlev (siteGaugeOfLatticeGauge S V z γ) (hq_le γ (hsmall γ h)) j hj
    have h2 := hq_small γ h
    have h3 : quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) j ≤
        qK * e0 := by
      refine h1.trans ?_
      rw [hqKd, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hCG.le
      linarith only [h2, s7]
    have h4 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h3 4
    unfold quarticDefectNorm at h4
    rwa [sqrt_sqrt_pow_four (Finset.sum_nonneg fun _ _ => by positivity)] at h4
  have hrelle : ∀ γ, gaugeRelativeEnergy a S V z W kW X k γ ≤ 16 * e0 ^ 2 := fun γ =>
    hR2 (siteGaugeOfLatticeGauge S V z γ)
  have hδ : ∀ γ, Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ) ≤ 4 * e0 := fun γ => by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, (hrelle γ).trans (le_of_eq (by ring))⟩
  have hEw : ∑ c ∈ bondsOf (patchDomain S z),
      ‖((framedLatticeField S V z (W 0) c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 ≤ (CR * s) ^ 4 := by
    have h0 := hr3
    rw [innerBonds_patchCells hamb hodd hsg (Nat.zero_le _),
      ← PatchLatticeChart.Framing.sum_bondsOf_siteBond hamb hodd hm32 hreg hsg
        (fun c => _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform (fun x => (patchFrame S V z x)⁻¹) (W 0) c.1 c.2) ^ 4)] at h0
    refine le_trans (le_of_eq ?_) h0
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [norm_framedLatticeField_sub_one hsg]
  have hstart : ∃ γ : Lattice4 → UnitQuaternion,
      (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ ≤ (Cp * e0) ^ 4 := by
    obtain ⟨γ₀, hq₀, ht₀⟩ := hS2
    let γ1 : Lattice4 → UnitQuaternion := fun a => (frameChange S V z (patchSite S z a))⁻¹ * γ₀ (patchSite S z a)
    have hgo : siteGaugeOfLatticeGauge S V z γ1 = γ₀ := by
      funext t
      show frameChange S V z t * ((frameChange S V z (patchSite S z (patchChart S z t)))⁻¹ *
        γ₀ (patchSite S z (patchChart S z t))) = _
      rw [PatchPoints.patchSite_patchChart hsg]
      group
    refine ⟨γ1, ?_⟩
    have hc0' : 0 ≤ CS * e0 := by positivity
    have h1 : (pinnedGaugeDataOfPatch S V z W kW X k).defectQuarticSum γ1 ≤ (CS * e0) ^ 4 := by
      have h2 := hqe γ1
      rw [hgo] at h2
      have h3 := sqrt_sqrt_pow_four (hgap0 γ1)
      rw [← h2] at h3
      rw [← h3]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hq₀ 4
    have h2 : ∑ y ∈ (pinnedGaugeDataOfPatch S V z W kW X k).cells,
        ‖(((pinnedGaugeDataOfPatch S V z W kW X k).pin γ1 y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 ≤
        47 ^ 4 * (CS * e0) ^ 4 := by
      have h3 : ∀ y : F.Cell, y ∈ patchCells S z →
          ‖((pinnedTopCorrection S V z W kW X k γ1 y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 ≤ (CS * e0) ^ 4 := by
        intro y hy
        have hy2 : baseSite y ∈ patchBaseSites S z := by
          simp only [patchCells, Finset.mem_filter] at hy
          exact hy.2
        have h4 : _root_.YangMills.Construction.BlockAverages.distFromOne (pinnedTopCorrection S V z W kW X k γ1 y) ≤ CS * e0 := by
          rw [_root_.YangMills.Construction.PinnedGaugeAtGoodCell.distFromOne_pinnedTopCorrection, hgo]
          exact ht₀ y hy2
        exact pow_le_pow_left₀ (norm_nonneg _) h4 4
      refine (Finset.sum_le_sum fun y hy => h3 y hy).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hPC1.cells_card_le (by positivity)
    have h3 : (1 + 47 ^ 4 : ℝ) * (CS * e0) ^ 4 ≤ (Cp * e0) ^ 4 := by
      have h4 := mul_pow_four_le hc0' (by norm_num : (1 : ℝ) ≤ 1 + 47 ^ 4)
      refine h4.trans (le_of_eq ?_)
      rw [hCpd]
      ring
    show (pinnedGaugeDataOfPatch S V z W kW X k).defectQuarticSum γ1 + _ ≤ _
    linarith only [h1, h2, h3]
  have hmor : ∀ (x : Lattice4) (r : ℕ), 1 ≤ r → r ≤ 80 * (pinnedGaugeDataOfPatch S V z W kW X k).scale →
      ∑ u ∈ (pinnedGaugeDataOfPatch S V z W kW X k).region.filter (fun u => supNorm (u - x) ≤ r),
        (pinnedGaugeDataOfPatch S V z W kW X k).targetWeight u ≤
        (CM * s) ^ 4 * ((r : ℝ) / ((80 * (pinnedGaugeDataOfPatch S V z W kW X k).scale : ℕ) : ℝ)) ^ (4 * θ) :=
    fun x r h1 h2 => hM2 x r h1 h2
  have htop : ∀ γ, (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ ≤ (Cp * e0) ^ 4 →
      ∀ c ∈ patchInnerBonds S z F.top,
      ‖adjointAction (frameChange S V z (baseSite c.1))⁻¹ (pureComponent ((topDefect W kW X k
          (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) c.1 c.2 : UnitQuaternion) : ℍ[ℝ])) -
        iteratedBlockAverage
          (framedPureDefect S V z W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0)
          F.top c.1 c.2‖ ≤
      4 * Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ / a) +
        CT * (quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0 + s +
          Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ)) *
          (quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0 +
            Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ)) := by
    intro γ hγ c hc
    exact hT2 (siteGaugeOfLatticeGauge S V z γ) (hq_le γ (hsmall γ hγ)) c hc
  have hε : ∀ γ, (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ ≤ (Cp * e0) ^ 4 →
      quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0 + s +
        Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ) ≤ εK * e0 := by
    intro γ hγ
    have h1 := hq_small γ hγ
    have h2 := hδ γ
    rw [hεKd]
    nlinarith only [h1, h2, s7]
  have hcs0 : 0 ≤ CR * s := by positivity
  have hqK0 : 0 < qK := by rw [hqKd]; positivity
  have hprob := isPinnedGaugeProblem (θ := θ) (A := (CM * s) ^ 4) (s := s) hPT hPD hRd hCu hCu0
    ha hodd h5 hamb hm hreg hz hXW hC₃ hPC1 hlevel hmor hne hbc.le (by positivity) hcs0 he8 hgaps
    hE0 hEs hEk hEl hη2 (by positivity) hEw hη1 htop hcs0 hr2 hε hs.le hCT.le hCε hpe le_rfl hη3 hstart
  obtain ⟨γ, hγb, hγd⟩ := hM (pinnedGaugeDataOfPatch S V z W kW X k) ((CM * s) ^ 4) (Kc * e0) ((Cp * e0) ^ 4)
    (cq ^ 4) (curlBound a S V z W kW X k) (by positivity) hAc (by positivity) hηc (by positivity) hb1 hbc
    (fun γ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hprob
  have hCq0 : 0 ≤ Cq := by rw [hCqd]; exact Real.sqrt_nonneg _
  have hD0 := gaugeRelativeEnergy_nonneg (S := S) (V := V) (z := z) (W := W) (kW := kW) (X := X) (k := k) ha.le γ
  have hpinle : (pinnedGaugeDataOfPatch S V z W kW X k).pinnedQuarticSum γ ≤
      (Cq * Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ)) ^ 4 := by
    refine hγd.trans (le_of_eq ?_)
    rw [curlBound_pow_four ha.le γ hD0, mul_pow, hCqd, sqrt_sqrt_pow_four (by positivity)]
    have e : Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ) ^ 4 =
        (Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ) ^ 2) ^ 2 := by ring
    rw [e, Real.sq_sqrt hD0]
    ring
  set δ := Real.sqrt (gaugeRelativeEnergy a S V z W kW X k γ) with hδdef
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hCδ : 0 ≤ Cq * δ := by positivity
  have hq0 : quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) 0 ≤ Cq * δ := by
    rw [hqe]
    exact sqrt_sqrt_le_of_le_pow_four hCδ ((hpin_gap γ).trans hpinle) (hgap0 γ)
  have hqlast : ∀ j, j < F.top →
      quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ)) j ≤ Cf * δ := by
    intro j hj
    refine (hGlast (siteGaugeOfLatticeGauge S V z γ) (hq_le γ (hsmall γ hγb)) j hj).trans ?_
    have e : Real.sqrt (2 / a * relativeEnergy a S z W kW X k
        (pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ))) =
        Real.sqrt (2 / a) * δ := Real.sqrt_mul (by positivity) _
    rw [e, hCfd]
    nlinarith only [hq0, hδ0]
  refine ⟨pinnedGaugeOfBase W kW X k (siteGaugeOfLatticeGauge S V z γ), ⟨?_, ?_, ?_, ?_⟩, hrelle γ⟩
  · intro y
    show (if F.depth + 1 < F.top then _ else (1 : UnitQuaternion)) = 1
    exact if_neg (lt_irrefl _)
  · intro j hj y _
    have e : pinnedGaugeLevel W kW X k (siteGaugeOfLatticeGauge S V z γ) (j + 1) y = kW (j + 1) y *
        balancingGauge (gaugeTransform (pinnedGaugeLevel W kW X k (siteGaugeOfLatticeGauge S V z γ) j) (X j))
          (W j) y *
          pinnedGaugeLevel W kW X k (siteGaugeOfLatticeGauge S V z γ) j (refineSite y) * (k (j + 1) y)⁻¹ := if_pos hj
    show pinnedGaugeLevel W kW X k (siteGaugeOfLatticeGauge S V z γ) (j + 1) y * k (j + 1) y *
      (pinnedGaugeLevel W kW X k (siteGaugeOfLatticeGauge S V z γ) j (refineSite y))⁻¹ = kW (j + 1) y *
        balancingGauge (gaugeTransform (pinnedGaugeLevel W kW X k (siteGaugeOfLatticeGauge S V z γ) j) (X j))
          (W j) y
    rw [e]
    group
  · intro j hj
    have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hqlast j hj) 4
    unfold quarticDefectNorm at h1
    rw [sqrt_sqrt_pow_four (Finset.sum_nonneg fun _ _ => by positivity)] at h1
    rw [← Finset.sum_filter]
    exact h1
  · intro y hy
    have hyS : y ∈ S := by
      obtain ⟨a0, ha0, e0'⟩ := Finset.mem_image.1 hy
      have hb := PatchPoints.patchSite_mem_sitesOfCells hamb hodd hreg hm32 ha0
      rw [e0', baseSite_eq_cellCentre_zero] at hb
      obtain ⟨y', hy', h, hh, e⟩ := mem_sitesOfCells.1 hb
      have hh' : h ∈ centredCube (F.blockSide ^ F.top) := by simpa using hh
      have e1 := BlockAverages.LocalPartition.enclosingCell_cellCentre_add (j := 0) hodd y' h hh
      have e2 := BlockAverages.LocalPartition.enclosingCell_cellCentre_add (j := 0) hodd y 0
        (zero_mem_centredCube hodd.pow)
      rw [_root_.YangMills.Construction.BlockAverages.siteOfCoords_zero, add_zero, e, e1] at e2
      rw [← e2]
      exact hy'
    have hyc : y ∈ patchCells S z := by
      simp only [patchCells, Finset.mem_filter]
      exact ⟨hyS, hy⟩
    have h1 := (pow_four_le_pinnedQuarticSum (V := V) (W := W) (kW := kW) (X := X) (k := k) (γ := γ) hyc).trans
      hpinle
    have h2 : _root_.YangMills.Construction.BlockAverages.distFromOne (pinnedTopCorrection S V z W kW X k γ y) ≤ Cq * δ :=
      (pow_le_pow_iff_left₀ (zero_le_distFromOne _) hCδ (by norm_num)).1 h1
    rw [_root_.YangMills.Construction.PinnedGaugeAtGoodCell.distFromOne_pinnedTopCorrection] at h2
    refine h2.trans ?_
    have : Cq ≤ Cf := by
      rw [hCfd]
      have := Real.sqrt_nonneg (2 / a)
      linarith only [this, hCq0]
    exact mul_le_mul_of_nonneg_right this hδ0
set_option maxHeartbeats 4000000 in
theorem pinnedGaugeAtGoodCell (hQG : pinnedQuarticGaugeStatement) (hPT : pinnedCorrectionGeneratorStatement)
    (hPD : pinnedBondDifferenceStatement) (hRd : pinnedCorrectionLocalityStatement) (hCu : curlGapBoundStatement)
    (hCells : patchCellConditionsStatement) (hGaps : framingDefectsOnPatchStatement)
    (hTopG : topDefectAverageStatement) (hStart : pinnedGaugeStartStatement)
    (hRel : pinnedGaugeRelativeEnergyStatement) (hMor : criticalChainMorreyStatement)
    (hRates : criticalChainPatchRatesStatement) : pinnedGaugeAtGoodCellStatement := by
  classical
  intro a θ del Ca ha hθ hθ8 hdel hdel8 hCa
  obtain ⟨C₃, n₀, hC₃, hn₀, hPC⟩ := hCells
  obtain ⟨Ccu, hCcu, hCuF⟩ := hCu
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  obtain ⟨Cs, cs, hCs, hcs, hM⟩ := hQG θ (2 * (4 / Real.sqrt a + 1) ^ 4) C₃ n₀ (47 ^ 4) 9 hθ (by positivity) hC₃ hn₀
    (by norm_num) (by norm_num)
  obtain ⟨LG, hG0⟩ := hGaps a θ del Ca ha hθ hθ8 hdel hdel8 hCa
  obtain ⟨LT, hT0⟩ := hTopG a θ del Ca ha hθ hθ8 hdel hdel8 hCa
  obtain ⟨LS, hS0⟩ := hStart a θ del Ca ha hθ hθ8 hdel hdel8 hCa
  obtain ⟨LR, hR0⟩ := hRel a θ del Ca ha hθ hθ8 hdel hdel8 hCa
  obtain ⟨LM, hM0⟩ := hMor a θ del Ca ha hθ hθ8 hdel hdel8 hCa
  obtain ⟨LQ, hQ0⟩ := hRates a θ del Ca ha hθ hθ8 hdel hdel8 hCa
  refine ⟨16, by norm_num, max 5 (max LG (max LT (max LS (max LR (max LM LQ))))), ?_⟩
  intro L hL hLm C₁ hC₁
  have l5 : 5 ≤ L := le_trans (le_max_left _ _) hLm
  have hLm1 := le_trans (le_max_right _ _) hLm
  have lG : LG ≤ L := le_trans (le_max_left _ _) hLm1
  have hLm2 := le_trans (le_max_right _ _) hLm1
  have lT : LT ≤ L := le_trans (le_max_left _ _) hLm2
  have hLm3 := le_trans (le_max_right _ _) hLm2
  have lS : LS ≤ L := le_trans (le_max_left _ _) hLm3
  have hLm4 := le_trans (le_max_right _ _) hLm3
  have lR : LR ≤ L := le_trans (le_max_left _ _) hLm4
  have hLm5 := le_trans (le_max_right _ _) hLm4
  have lM : LM ≤ L := le_trans (le_max_left _ _) hLm5
  have lQ : LQ ≤ L := le_trans (le_max_right _ _) hLm5
  obtain ⟨CG, cG, hCG, hcG, hG⟩ := hG0 L hL lG C₁ hC₁
  obtain ⟨CT, cT, hCT, hcT, hT⟩ := hT0 L hL lT C₁ hC₁
  obtain ⟨CS, cS, hCS, hcS, hS⟩ := hS0 L hL lS C₁ hC₁
  obtain ⟨cR, hcR, hR⟩ := hR0 L hL lR C₁ hC₁
  obtain ⟨CM, cM, hCM, hcM, hMo⟩ := hM0 L hL lM C₁ hC₁
  obtain ⟨CR, cQ, hCR, hcQ, hQ⟩ := hQ0 L hL lQ C₁ hC₁
  obtain ⟨Cp, hCpd⟩ : ∃ Cp : ℝ, Cp = CS * (1 + 47 ^ 4) := ⟨_, rfl⟩
  have hCp0 : 0 < Cp := by rw [hCpd]; positivity
  obtain ⟨qK, hqKd⟩ : ∃ qK : ℝ, qK = CG * (Cp + 2) := ⟨_, rfl⟩
  have hqK0 : 0 < qK := by rw [hqKd]; positivity
  obtain ⟨K2, hK2d⟩ : ∃ K2 : ℝ, K2 = 36 * (L : ℝ) * qK + 8 * CR := ⟨_, rfl⟩
  have hK20 : 0 < K2 := by
    rw [hK2d]
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    positivity
  obtain ⟨A1, hA1d⟩ : ∃ A1 : ℝ, A1 = Ccu * (Cp ^ 4 + CR ^ 4) := ⟨_, rfl⟩
  have hA10 : 0 < A1 := by rw [hA1d]; positivity
  obtain ⟨εK, hεKd⟩ : ∃ εK : ℝ, εK = Cp + 5 := ⟨_, rfl⟩
  have hεK0 : 0 < εK := by rw [hεKd]; positivity
  obtain ⟨A3, hA3d⟩ : ∃ A3 : ℝ, A3 = 64 * ((CT * εK) ^ 4 + (Cp + 2 * CR) ^ 4 + 16 * C₃ * CR ^ 4) := ⟨_, rfl⟩
  have hA30 : 0 ≤ A3 := by rw [hA3d]; positivity
  obtain ⟨Kc, hKcd⟩ : ∃ Kc : ℝ, Kc = 1 + A1 + 2 * K2 + A3 := ⟨_, rfl⟩
  have hKc0 : 0 < Kc := by rw [hKcd]; positivity
  obtain ⟨cq, hcqd⟩ : ∃ cq : ℝ, cq = min cG cT := ⟨_, rfl⟩
  have hcq0 : 0 < cq := by rw [hcqd]; exact lt_min hcG hcT
  have hcqG : cq ≤ cG := by rw [hcqd]; exact min_le_left _ _
  have hcqT : cq ≤ cT := by rw [hcqd]; exact min_le_right _ _
  obtain ⟨Cq, hCqd⟩ : ∃ Cq : ℝ, Cq = Real.sqrt (Real.sqrt (32 * Cs)) := ⟨_, rfl⟩
  have hCq0 : 0 ≤ Cq := by rw [hCqd]; exact Real.sqrt_nonneg _
  obtain ⟨Cf, hCfd⟩ : ∃ Cf : ℝ, Cf = 4 * (Cq + Real.sqrt (2 / a)) + 1 := ⟨_, rfl⟩
  have hCf0 : 0 < Cf := by
    rw [hCfd]
    have := Real.sqrt_nonneg (2 / a)
    positivity
  have hmin0 : 0 < min 1 cs := lt_min one_pos hcs
  refine ⟨Cf, min cG (min cT (min cS (min cR (min (1 / (1 + Cp)) (min (cq / (2 * (1 + Cp)))
    (min (1 / (8 * (1 + K2))) (min (1 / (1 + CT * εK)) (min (cs / Kc) (min 1 cs / (1 + CM)))))))))), hCf0, ?_, ?_⟩
  · simp only [lt_min_iff]
    exact ⟨hcG, hcT, hcS, hcR, by positivity, by positivity, by positivity, by positivity, by positivity,
      by positivity⟩
  intro e0 he0 hec
  have b1 : e0 ≤ cG := hec.trans (min_le_left _ _)
  have hc1 := hec.trans (min_le_right _ _)
  have b2 : e0 ≤ cT := hc1.trans (min_le_left _ _)
  have hc2 := hc1.trans (min_le_right _ _)
  have b3 : e0 ≤ cS := hc2.trans (min_le_left _ _)
  have hc3 := hc2.trans (min_le_right _ _)
  have b4 : e0 ≤ cR := hc3.trans (min_le_left _ _)
  have hc4 := hc3.trans (min_le_right _ _)
  have b5 : e0 ≤ 1 / (1 + Cp) := hc4.trans (min_le_left _ _)
  have hc5 := hc4.trans (min_le_right _ _)
  have b6 : e0 ≤ cq / (2 * (1 + Cp)) := hc5.trans (min_le_left _ _)
  have hc6 := hc5.trans (min_le_right _ _)
  have b7 : e0 ≤ 1 / (8 * (1 + K2)) := hc6.trans (min_le_left _ _)
  have hc7 := hc6.trans (min_le_right _ _)
  have b8 : e0 ≤ 1 / (1 + CT * εK) := hc7.trans (min_le_left _ _)
  have hc8 := hc7.trans (min_le_right _ _)
  have b9 : e0 ≤ cs / Kc := hc8.trans (min_le_left _ _)
  have b11 : e0 ≤ min 1 cs / (1 + CM) := hc8.trans (min_le_right _ _)
  obtain ⟨σG, hσG, hG1⟩ := hG e0 he0 b1
  obtain ⟨σT, hσT, hT1⟩ := hT e0 he0 b2
  obtain ⟨σS, hσS, hS1⟩ := hS e0 he0 b3
  obtain ⟨σR, hσR, hR1⟩ := hR e0 he0 b4
  refine ⟨min σG (min σT (min σS (min σR (min cM (min cQ e0))))), by
    simp only [lt_min_iff]
    exact ⟨hσG, hσT, hσS, hσR, hcM, hcQ, he0⟩, ?_⟩
  intro F m S hFL hamb hm hreg s V v hs hsσ hcold hvs U hU X k z hXtop hz hterms
  have s1 : s ≤ σG := hsσ.trans (min_le_left _ _)
  have hs1 := hsσ.trans (min_le_right _ _)
  have s2 : s ≤ σT := hs1.trans (min_le_left _ _)
  have hs2 := hs1.trans (min_le_right _ _)
  have s3 : s ≤ σS := hs2.trans (min_le_left _ _)
  have hs3 := hs2.trans (min_le_right _ _)
  have s4 : s ≤ σR := hs3.trans (min_le_left _ _)
  have hs4 := hs3.trans (min_le_right _ _)
  have s5 : s ≤ cM := hs4.trans (min_le_left _ _)
  have hs5 := hs4.trans (min_le_right _ _)
  have s6 : s ≤ cQ := hs5.trans (min_le_left _ _)
  have s7 : s ≤ e0 := hs5.trans (min_le_right _ _)
  have hodd : Odd F.blockSide := by rw [hFL]; exact hL
  have h5' : 5 ≤ F.blockSide := by rw [hFL]; exact l5
  have hLe : (F.blockSide : ℝ) = L := by rw [hFL]
  obtain ⟨hCe, hCq', he8, hη2, hη1, hη3, hCε, hAc, hηc⟩ := constants_bounds (Lr := (F.blockSide : ℝ)) (CS := CS)
    (CG := CG) (CT := CT) (CM := CM) (CR := CR) (Ccu := Ccu) (C₃ := C₃) (cq := cq) (cs := cs) (e0 := e0) (s := s)
    (Cp := Cp) (qK := qK) (K2 := K2) (A1 := A1) (εK := εK) (A3 := A3) (Kc := Kc) (Nat.cast_nonneg _) hCS hCG hCT hCM
    hCR hCcu hC₃ hcq0 hcs he0 hs s7
    hCpd hqKd (by rw [hLe]; exact hK2d) hA1d hεKd hA3d hKcd b5 b6 b7 b8 b9 b11
  have hG2 := hG1 F m S hFL hamb hm hreg s V v hs s1 hcold hvs U hU X k z hXtop hz hterms
  have hT2 := hT1 F m S hFL hamb hm hreg s V v hs s2 hcold hvs U hU X k z hXtop hz hterms
  have hS2 := hS1 F m S hFL hamb hm hreg s V v hs s3 hcold hvs U hU X k z hXtop hz hterms
  have hR2 := hR1 F m S hFL hamb hm hreg s V v hs s4 hcold U hU X k z hz hterms
  have hM2 := hMo F m S hFL hamb hm hreg s V v hs s5 hcold U hU z hz
  obtain ⟨hr1, hr2, hr3⟩ := hQ F m S hFL hamb hm hreg s V v hs s6 hcold U hU z hz
  have hXW : X F.top = criticalFieldChain S V v U F.top := by
    rw [hXtop]
    exact (ChartCoordinates.chartChain_top _ _ _).symm
  obtain ⟨hPC1, hlevel⟩ := hPC F m S hodd hamb hm hreg V z (criticalFieldChain S V v U) (criticalGauge S V U) X k hz
  have hEex : ∀ j, ∃ E : F.Site (j + 1) → ℝ, (∀ y, 0 ≤ E y) ∧ (j < F.top →
      ∑ y ∈ sitesOfCells (patchCells S z) (j + 1), E y ^ 4 ≤ (CR * s) ^ 4 ∧
      (∀ y ∈ sitesOfCells (patchCells S z) (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (criticalGauge S V U (j + 1) y) ≤ E y) ∧
      (∀ y ∈ sitesOfCells (patchCells S z) (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
        _root_.YangMills.Construction.BlockAverages.distFromOne ((patchFrame S V z (refineSite y))⁻¹ *
          pathHolonomy (criticalFieldChain S V v U j) (refineSite y) (axisPath h π) *
          patchFrame S V z (refineSite y + siteOfCoords j h)) ≤ E y)) := by
    intro j
    by_cases hj : j < F.top
    · obtain ⟨E, e, hE, -, h1, -, -, hrate⟩ := hr1 j hj
      exact ⟨E, hE, fun _ => ⟨h1, hrate.gauge_le, hrate.axisPath_le⟩⟩
    · exact ⟨fun _ => 0, fun _ => le_rfl, fun h => absurd h hj⟩
  choose E hE0 hEp using hEex
  exact exists_pinnedGauge_of_bounds hPT hPD hRd hCuF hCcu.le hM ha hCs hCG hCT hCS hCM hCR hCp0 hqKd hεKd hCpd
    hcq0 hKc0 hCqd hCfd he0 hs s7
    hCe hCq' he8 hη2 hη1 hη3 hCε hAc hηc hodd h5' hamb hm hreg hz hXW hC₃ hPC1 hlevel
    (fun γ h => (hG2 γ (h.trans hcqG)).1) (fun γ h => (hG2 γ (h.trans hcqG)).2.1)
    (fun γ h => (hG2 γ (h.trans hcqG)).2.2.2.2) (fun γ h => hT2 γ (h.trans hcqT)) hS2 hR2 hM2
    hE0 (fun j hj => (hEp j hj).1) (fun j hj => (hEp j hj).2.1) (fun j hj => (hEp j hj).2.2) hr2
    (hr3 0 (Nat.succ_pos _))
end YangMills.Construction.PinnedGaugeAtGoodCell
end
