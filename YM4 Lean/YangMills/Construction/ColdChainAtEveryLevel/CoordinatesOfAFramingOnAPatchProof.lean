import YangMills.Construction.ColdChainAtEveryLevel.CoordinatesOfAFramingOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.RotationOfAFramingOfLevelZero
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.PinnedCorrectionLocality
open BlockAverages.ChartCoordinates BlockAverages.PinnedGaugeVariation GaugeMotions GaugeMap PatchPoints
  PatchLatticeChart PatchLatticeChart.Framing
variable {F : BlockFrame}
theorem patchChart_mem_and_patchSite_eq (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S : Finset F.Cell} {z : F.Cell}
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {x : F.Site 0}
    (hx : x ∈ sitesOfCells (patchCells S z) 0) :
    patchChart S z x ∈ patchDomain S z ∧ patchSite S z (patchChart S z x) = x := by
  classical
  have h1 := ((mem_sitesOfCells_patchCells_iff hamb hodd he (Nat.zero_le _)).1 hx).2
  rw [PatchLatticeChart.Framing.baseSite_eq_self] at h1
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h1
  rw [PatchPoints.patchChart_patchSite hamb hodd he (PatchPoints.patchDomain_coord_bounds ha)]
  exact ⟨ha, rfl⟩
theorem refineSite_mem_sitesOfCells (hodd : Odd F.blockSide) {D : Finset F.Cell} {j : ℕ}
    (hj : j + 1 ≤ F.top) {y : F.Site (j + 1)}
    (hy : y ∈ sitesOfCells D (j + 1)) : refineSite y ∈ sitesOfCells D j := by
  have h0 : (0 : LatticeFractionalIntegration.Lattice4) ∈ centredCube F.blockSide := zero_mem_centredCube hodd
  have := ChartCoordinates.refineSite_add_mem_sitesOfCells hodd hj hy h0
  rwa [ChartCoordinates.add_siteOfCoords_zero] at this
section Congr
variable {S : Finset F.Cell} {z : F.Cell} {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain}
  {k : F.SiteGauge}
theorem pinnedGaugeLevel_congr (hodd : Odd F.blockSide) {D : Finset F.Cell}
    {γ γ' : F.Site 0 → UnitQuaternion} (h : ∀ x ∈ sitesOfCells D 0, γ x = γ' x) (j : ℕ)
    (hj : j ≤ F.top) :
    ∀ x ∈ sitesOfCells D j, pinnedGaugeLevel W kW X k γ j x = pinnedGaugeLevel W kW X k γ' j x := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro y hy
    have ih' := ih (by omega)
    have hj1 : j + 1 ≤ F.top := hj
    show (if j + 1 < F.top then _ else (1 : UnitQuaternion)) = (if j + 1 < F.top then _ else (1 : UnitQuaternion))
    split_ifs with hlt
    · have hag : ChartCoordinates.GaugeAgreeOnBonds D j (gaugeTransform (pinnedGaugeLevel W kW X k γ j) (X j))
          (gaugeTransform (pinnedGaugeLevel W kW X k γ' j) (X j)) := by
        intro x i hx hx'
        simp only [gaugeTransform, ih' x hx, ih' _ hx']
      have e1 := ChartCoordinates.balancingGauge_congr hodd hj1 (W j) hag hy
      rw [e1, ih' _ (refineSite_mem_sitesOfCells hodd hj1 hy)]
    · rfl
theorem topCorrection_pinnedGaugeOfBase_congr (hodd : Odd F.blockSide) {D : Finset F.Cell}
    {γ γ' : F.Site 0 → UnitQuaternion} (h : ∀ x ∈ sitesOfCells D 0, γ x = γ' x)
    {y : F.Site F.top} (hy : y ∈ sitesOfCells D F.top) :
    topCorrection W kW X k (pinnedGaugeOfBase W kW X k γ) y =
      topCorrection W kW X k (pinnedGaugeOfBase W kW X k γ') y := by
  rw [PinnedGaugeVariation.topCorrection_eq, PinnedGaugeVariation.topCorrection_eq]
  have hj1 : F.depth + 1 ≤ F.top := le_rfl
  have ih' := pinnedGaugeLevel_congr (W := W) (kW := kW) (X := X) (k := k) hodd h F.depth (Nat.le_succ _)
  have hag : ChartCoordinates.GaugeAgreeOnBonds D F.depth
      (gaugeTransform (pinnedGaugeLevel W kW X k γ F.depth) (X F.depth))
      (gaugeTransform (pinnedGaugeLevel W kW X k γ' F.depth) (X F.depth)) := by
    intro x i hx hx'
    simp only [gaugeTransform, ih' x hx, ih' _ hx']
  rw [ChartCoordinates.balancingGauge_congr hodd hj1 (W F.depth) hag hy,
    ih' _ (refineSite_mem_sitesOfCells hodd hj1 hy)]
end Congr
section Cont
variable {P : Type} [TopologicalSpace P] {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain}
  {k : F.SiteGauge}
theorem continuousOn_coe_inv {g : P → UnitQuaternion} {R : Set P}
    (h : ContinuousOn (fun p => ((g p : UnitQuaternion) : ℍ[ℝ])) R) :
    ContinuousOn (fun p => (((g p)⁻¹ : UnitQuaternion) : ℍ[ℝ])) R := by
  simp only [coe_unitQuaternion_inv]
  exact continuous_star.comp_continuousOn h
theorem continuousOn_gaugedPathAverage (hodd : Odd F.blockSide) {j : ℕ} {D : Finset F.Cell}
    {Γ : P → F.Site j → UnitQuaternion} (X0 R0 : F.GaugeField j) {R : Set P}
    {y : F.Site (j + 1)} (hj : j + 1 ≤ F.top) (hy : y ∈ sitesOfCells D (j + 1))
    (h : ∀ x ∈ sitesOfCells D j, ContinuousOn (fun p => ((Γ p x : UnitQuaternion) : ℍ[ℝ])) R) :
    ContinuousOn (fun p => gaugedPathAverage (Γ p) X0 R0 y) R := by
  unfold gaugedPathAverage
  have hsum : ContinuousOn (fun p => ∑ a ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy X0 (refineSite y) (axisPath a π) * (Γ p (refineSite y + siteOfCoords j a))⁻¹ *
        (pathHolonomy R0 (refineSite y) (axisPath a π))⁻¹ : UnitQuaternion) : ℍ[ℝ])) R := by
    refine continuousOn_finset_sum _ fun a ha => ?_
    refine continuousOn_finset_sum _ fun π _ => ?_
    have hb := ChartCoordinates.refineSite_add_mem_sitesOfCells hodd hj hy ha
    have e : (fun p => ((pathHolonomy X0 (refineSite y) (axisPath a π) *
        (Γ p (refineSite y + siteOfCoords j a))⁻¹ *
        (pathHolonomy R0 (refineSite y) (axisPath a π))⁻¹ : UnitQuaternion) : ℍ[ℝ])) = fun p =>
        ((pathHolonomy X0 (refineSite y) (axisPath a π) : UnitQuaternion) : ℍ[ℝ]) *
          (((Γ p (refineSite y + siteOfCoords j a))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          (((pathHolonomy R0 (refineSite y) (axisPath a π))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      funext p
      simp only [Submonoid.coe_mul]
    rw [e]
    exact (continuousOn_const.mul (continuousOn_coe_inv (h _ hb))).mul continuousOn_const
  exact hsum.const_smul (1 / (24 * (F.blockSide : ℝ) ^ 4))
theorem continuousOn_coe_polarUnit {C : P → ℍ[ℝ]} {R : Set P} (h : ContinuousOn C R)
    (hne : ∀ p ∈ R, C p ≠ 0) :
    ContinuousOn (fun p => ((polarUnit (C p) : UnitQuaternion) : ℍ[ℝ])) R := by
  have e : ContinuousOn (fun p => ‖C p‖⁻¹ • C p) R :=
    (h.norm.inv₀ fun p hp => norm_ne_zero_iff.2 (hne p hp)).smul h
  exact e.congr fun p hp => coe_polarUnit (hne p hp)
theorem continuousOn_balancingStep (hodd : Odd F.blockSide) {j : ℕ} {D : Finset F.Cell}
    {Γ : P → F.Site j → UnitQuaternion} (X0 R0 : F.GaugeField j) {R : Set P}
    {y : F.Site (j + 1)} (hj : j + 1 ≤ F.top) (hy : y ∈ sitesOfCells D (j + 1)) (κ κ' : UnitQuaternion)
    (h : ∀ x ∈ sitesOfCells D j, ContinuousOn (fun p => ((Γ p x : UnitQuaternion) : ℍ[ℝ])) R)
    (hne : ∀ p ∈ R, relativePathAverage (gaugeTransform (Γ p) X0) R0 y ≠ 0) :
    ContinuousOn (fun p => ((κ * balancingGauge (gaugeTransform (Γ p) X0) R0 y * Γ p (refineSite y) * κ' :
      UnitQuaternion) : ℍ[ℝ])) R := by
  have h1 := continuousOn_coe_inv (continuousOn_coe_polarUnit
    (continuousOn_gaugedPathAverage hodd X0 R0 hj hy h)
    fun p hp => PinnedGaugeVariation.gaugedPathAverage_ne_zero (hne p hp))
  have h2 : ContinuousOn (fun p => (κ : ℍ[ℝ]) *
      (((polarUnit (gaugedPathAverage (Γ p) X0 R0 y))⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (κ' : ℍ[ℝ])) R :=
    (continuousOn_const.mul h1).mul continuousOn_const
  refine h2.congr fun p hp => ?_
  show ((κ * balancingGauge (gaugeTransform (Γ p) X0) R0 y * Γ p (refineSite y) * κ' : UnitQuaternion) :
    ℍ[ℝ]) = _
  rw [PinnedGaugeVariation.balancingGauge_mul_eq _ _ _ κ κ' y
    (PinnedGaugeVariation.gaugedPathAverage_ne_zero (hne p hp))]
  rfl
theorem continuousOn_pinnedGaugeLevel (hodd : Odd F.blockSide) {D : Finset F.Cell}
    {γ : P → F.Site 0 → UnitQuaternion} {R : Set P}
    (h0 : ∀ x ∈ sitesOfCells D 0, ContinuousOn (fun p => ((γ p x : UnitQuaternion) : ℍ[ℝ])) R)
    (hne : ∀ p ∈ R, ∀ j, j < F.top → ∀ y ∈ sitesOfCells D (j + 1),
      relativePathAverage (gaugeTransform (pinnedGaugeLevel W kW X k (γ p) j) (X j)) (W j) y ≠ 0)
    (j : ℕ) (hj : j ≤ F.top) :
    ∀ x ∈ sitesOfCells D j,
      ContinuousOn (fun p => ((pinnedGaugeLevel W kW X k (γ p) j x : UnitQuaternion) : ℍ[ℝ])) R := by
  induction j with
  | zero => exact h0
  | succ j ih =>
    intro y hy
    have hj1 : j + 1 ≤ F.top := hj
    by_cases hlt : j + 1 < F.top
    · have e : ∀ γ' : F.Site 0 → UnitQuaternion, pinnedGaugeLevel W kW X k γ' (j + 1) y = kW (j + 1) y *
          balancingGauge (gaugeTransform (pinnedGaugeLevel W kW X k γ' j) (X j)) (W j) y *
            pinnedGaugeLevel W kW X k γ' j (refineSite y) * (k (j + 1) y)⁻¹ := fun γ' => if_pos hlt
      simp only [e]
      exact continuousOn_balancingStep hodd (X j) (W j) hj1 hy _ _ (ih (by omega))
        fun p hp => hne p hp j hj1 y hy
    · have e : ∀ γ' : F.Site 0 → UnitQuaternion, pinnedGaugeLevel W kW X k γ' (j + 1) y = 1 :=
        fun γ' => if_neg hlt
      simp only [e]
      exact continuousOn_const
theorem continuousOn_topCorrection (hodd : Odd F.blockSide) {D : Finset F.Cell}
    {γ : P → F.Site 0 → UnitQuaternion} {R : Set P}
    (h0 : ∀ x ∈ sitesOfCells D 0, ContinuousOn (fun p => ((γ p x : UnitQuaternion) : ℍ[ℝ])) R)
    (hne : ∀ p ∈ R, ∀ j, j < F.top → ∀ y ∈ sitesOfCells D (j + 1),
      relativePathAverage (gaugeTransform (pinnedGaugeLevel W kW X k (γ p) j) (X j)) (W j) y ≠ 0)
    {y : F.Site F.top} (hy : y ∈ sitesOfCells D F.top) :
    ContinuousOn (fun p => ((topCorrection W kW X k (pinnedGaugeOfBase W kW X k (γ p)) y :
      UnitQuaternion) : ℍ[ℝ])) R := by
  simp only [PinnedGaugeVariation.topCorrection_eq]
  exact continuousOn_balancingStep hodd (X F.depth) (W F.depth) le_rfl hy _ _
    (continuousOn_pinnedGaugeLevel hodd h0 hne F.depth (Nat.le_succ _))
    fun p hp => hne p hp F.depth (Nat.lt_succ_self _) y hy
end Cont
theorem pinnedCorrectionLocality : BlockAverages.pinnedCorrectionLocalityStatement := by
  classical
  intro F m S V z W kW X k hodd hamb hm hreg
  obtain ⟨hs, -⟩ := closedOrthant_spec hreg (by omega : 32 ≤ m) z
  have hmem : ∀ y ∈ patchCells S z, y ∈ sitesOfCells (patchCells S z) F.top :=
    fun y hy => mem_sitesOfCells_top.2 hy
  refine ⟨fun γ γ' h y hy => ?_, fun R hne y hy => ?_⟩
  · unfold pinnedTopCorrection
    have h0 : ∀ x ∈ sitesOfCells (patchCells S z) 0,
        siteGaugeOfLatticeGauge S V z γ x = siteGaugeOfLatticeGauge S V z γ' x := by
      intro x hx
      unfold siteGaugeOfLatticeGauge
      rw [h _ (patchChart_mem_and_patchSite_eq hamb hodd hs hx).1]
    rw [topCorrection_pinnedGaugeOfBase_congr hodd h0 (hmem y hy)]
  · unfold pinnedTopCorrection
    simp only [Submonoid.coe_mul]
    have h0 : ∀ x ∈ sitesOfCells (patchCells S z) 0,
        ContinuousOn (fun μ : (pinnedGaugeDataOfPatch S V z W kW X k).region → UnitQuaternion =>
        ((siteGaugeOfLatticeGauge S V z ((pinnedGaugeDataOfPatch S V z W kW X k).extendByOne μ) x :
          UnitQuaternion) : ℍ[ℝ])) R := by
      intro x hx
      obtain ⟨hc, -⟩ := patchChart_mem_and_patchSite_eq hamb hodd hs hx
      have hc' : patchChart S z x ∈ (pinnedGaugeDataOfPatch S V z W kW X k).region := hc
      have e : (fun μ : (pinnedGaugeDataOfPatch S V z W kW X k).region → UnitQuaternion =>
          ((siteGaugeOfLatticeGauge S V z ((pinnedGaugeDataOfPatch S V z W kW X k).extendByOne μ) x :
            UnitQuaternion) : ℍ[ℝ])) = fun μ =>
          ((frameChange S V z x : UnitQuaternion) : ℍ[ℝ]) * ((μ ⟨_, hc'⟩ : UnitQuaternion) : ℍ[ℝ]) := by
        funext μ
        unfold siteGaugeOfLatticeGauge PinnedGauge.PinnedGaugeData.extendByOne
        simp only [dif_pos hc', Submonoid.coe_mul]
      rw [e]
      exact (continuousOn_const.mul (continuous_subtype_val.comp (continuous_apply _)).continuousOn)
    have h1 := continuousOn_topCorrection hodd h0 hne (hmem y hy)
    exact (continuousOn_const.mul h1).mul continuousOn_const
end YangMills.Construction.BlockAverages.PinnedCorrectionLocality
end
