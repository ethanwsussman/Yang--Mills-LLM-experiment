import YangMills.Construction.ColdChainAtEveryLevel.CellsOfAPatch
import YangMills.Construction.ColdChainAtEveryLevel.GaugeMotionsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.OneStepOfAFraming
import YangMills.Construction.ColdChainAtEveryLevel.QuarticGaugeOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.SizesAtAGoodCell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
namespace LowCostPatch
variable {F : BlockFrame}
def trivialField (j : ℕ) : F.GaugeField j := fun _ _ => 1
def chainGauge (X : F.FieldChain) (k : F.SiteGauge) (Γ0 : F.Site 0 → UnitQuaternion) :
    (j : ℕ) → F.Site j → UnitQuaternion
  | 0 => Γ0
  | j + 1 => fun y => balancedLinks (gaugeTransform (chainGauge X k Γ0 j) (X j)) (trivialField j) (fun _ => 1) y *
      chainGauge X k Γ0 j (refineSite y) * (k (j + 1) y)⁻¹
def gaugedChain (X : F.FieldChain) (k : F.SiteGauge) (Γ0 : F.Site 0 → UnitQuaternion) (j : ℕ) : F.GaugeField j :=
  gaugeTransform (chainGauge X k Γ0 j) (X j)
theorem pathHolonomy_trivialField {j : ℕ} (x : F.Site j) (l : List PathStep) :
    pathHolonomy (trivialField (F := F) j) x l = 1 := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    obtain ⟨i, b⟩ := st
    cases b <;> simp [pathHolonomy, linkValue, trivialField, ih]
theorem contourAverage_trivialField (hodd : Odd F.blockSide) {j : ℕ} (c : F.Site (j + 1) × Fin 4) :
    contourAverage (trivialField (F := F) j) c = 1 := by
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hcard : ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by
    rw [LatticePaths.card_centredCube hodd]
    push_cast
    rfl
  have hperm : (Fintype.card (Equiv.Perm (Fin 4)) : ℝ) = 24 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  unfold contourAverage
  simp only [pathHolonomy_trivialField, Finset.sum_const, Finset.card_univ, OneMemClass.coe_one]
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul, hcard, hperm]
  have : 1 / (24 * (F.blockSide : ℝ) ^ 4) * (F.blockSide : ℝ) ^ 4 * 24 = 1 := by field_simp
  rw [this, one_smul]
private theorem normSubOne_sq (g : UnitQuaternion) : normSubOne g ^ 2 = 2 - 2 * (g : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.BlockAverages.distFromOne_sq <;> assumption
theorem norm_sub_re_eq_mul_distFromOne_sq {q : ℍ[ℝ]} (hq : q ≠ 0) (g : UnitQuaternion) :
    ‖q‖ - (q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = ‖q‖ * (normSubOne (g * (polarUnit q)⁻¹) ^ 2 / 2) := by
  rw [normSubOne_sq]
  set u := polarUnit q with hu
  have hqu : q = ‖q‖ • (u : ℍ[ℝ]) := by
    rw [hu, coe_polarUnit hq, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hq), one_smul]
  have hre : ((g * u⁻¹ : UnitQuaternion) : ℍ[ℝ]).re = ((u : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := by
    have h1 : star ((u : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) = ((g * u⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      rw [star_mul, coe_unitQuaternion_inv, star_star, Submonoid.coe_mul, coe_unitQuaternion_inv]
    rw [← h1, Quaternion.re_star]
  rw [hre]
  conv_lhs => rw [hqu]
  rw [smul_mul_assoc, Quaternion.re_smul, norm_smul, norm_norm, norm_coe_unitQuaternion, smul_eq_mul]
  ring
theorem enclosingCell_mem_and_block_in_cell {S : Finset F.Cell} (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top)
    {x : F.Site j} (hx : x ∈ sitesOfCells S j) : enclosingCell x ∈ S ∧ ∀ h ∈ centredCube (F.blockSide ^ j),
      ∃ h' ∈ centredCube (F.blockSide ^ F.top),
      baseSite x + siteOfCoords 0 h = cellCentre 0 (enclosingCell x) + siteOfCoords 0 h' := by
  classical
  obtain ⟨y, hy, h₁, hh₁, rfl⟩ := mem_sitesOfCells.1 hx
  rw [BlockLines.enclosingCell_cellCentre_add hodd y h₁ hh₁]
  refine ⟨hy, fun h hh => ?_⟩
  have hx' : cellCentre j y + siteOfCoords j h₁ ∈ sitesOfCells ({y} : Finset F.Cell) j :=
    mem_sitesOfCells.2 ⟨y, Finset.mem_singleton_self y, h₁, hh₁, rfl⟩
  obtain ⟨y', hy', h', hh', e⟩ := PatchLocality.exists_cell_of_mem_sitesOfCells hodd hj hx' hh
  rw [Finset.mem_singleton.1 hy'] at e
  exact ⟨h', hh', e⟩
theorem zero_mem_centredCube (hodd : Odd F.blockSide) (e : ℕ) :
    (0 : LatticeFractionalIntegration.Lattice4) ∈ centredCube (F.blockSide ^ e) := by
  refine Fintype.mem_piFinset.2 fun i => ?_
  have : 0 < F.blockSide ^ e := by have := hodd.pos; positivity
  simp only [Pi.zero_apply, Finset.mem_Icc]
  omega
def patchCells (S : Finset F.Cell) (z : F.Cell) : Finset F.Cell := by
  classical exact S.filter fun y => baseSite y ∈ patchBaseSites S z
theorem baseSite_eq_cellCentre (y : F.Cell) : baseSite y = cellCentre 0 y := by apply _root_.YangMills.Construction.ReferenceBounds.baseSite_cell <;> assumption
theorem patchCells_subset {S : Finset F.Cell} {z : F.Cell} : patchCells S z ⊆ S := by
  classical
  exact Finset.filter_subset _ _
theorem baseSite_add_mem_patchBaseSites {S : Finset F.Cell} {z : F.Cell} (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {j : ℕ}
    (hj : j ≤ F.top) {x : F.Site j} (hx : x ∈ sitesOfCells (patchCells S z) j)
    {h : LatticeFractionalIntegration.Lattice4} (hh : h ∈ centredCube (F.blockSide ^ j)) :
    baseSite x + siteOfCoords 0 h ∈ patchBaseSites S z := by
  classical
  obtain ⟨hc, hall⟩ := enclosingCell_mem_and_block_in_cell hodd hj hx
  obtain ⟨h', hh', e⟩ := hall h hh
  rw [e]
  have h1 := (Finset.mem_filter.1 hc).2
  rw [baseSite_eq_cellCentre] at h1
  have h2 : cellCentre 0 (enclosingCell x) + siteOfCoords 0 (0 : LatticeFractionalIntegration.Lattice4) ∈
      patchBaseSites S z := by
    rw [siteOfCoords_zero, add_zero]
    exact h1
  exact PatchLocality.mem_patchBaseSites_of_same_cell hamb hodd he (zero_mem_centredCube hodd F.top) hh' h2
theorem innerBonds_patchCells_subset_patchFitBonds {S : Finset F.Cell} {z : F.Cell} (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {j : ℕ}
    (hj : j + 1 ≤ F.top) : innerBonds (patchCells S z) (j + 1) ⊆ patchFitBonds S z j := by
  classical
  intro c hc
  have h1 := Finset.mem_filter.1 hc
  have e1 : c.1 ∈ sitesOfCells (patchCells S z) (j + 1) := (Finset.mem_product.1 h1.1).1
  exact Finset.mem_filter.2 ⟨BlockLines.innerBonds_mono patchCells_subset _ hc, fun h hh =>
    ⟨baseSite_add_mem_patchBaseSites hamb hodd he hj e1 hh, baseSite_add_mem_patchBaseSites hamb hodd he hj h1.2 hh⟩⟩
theorem innerBonds_patchCells_zero_subset {S : Finset F.Cell} {z : F.Cell} (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) :
    innerBonds (patchCells S z) 0 ⊆ patchInnerBonds S z 0 := by
  classical
  intro c hc
  have h1 := Finset.mem_filter.1 hc
  have e1 : c.1 ∈ sitesOfCells (patchCells S z) 0 := (Finset.mem_product.1 h1.1).1
  have a1 := baseSite_add_mem_patchBaseSites hamb hodd he (Nat.zero_le _) e1 (zero_mem_centredCube hodd 0)
  have a2 := baseSite_add_mem_patchBaseSites hamb hodd he (Nat.zero_le _) h1.2 (zero_mem_centredCube hodd 0)
  rw [siteOfCoords_zero, add_zero] at a1 a2
  exact Finset.mem_filter.2 ⟨BlockLines.innerBonds_mono patchCells_subset _ hc, a1, a2⟩
theorem mem_sitesOfCells_patchCells_of_baseSite_mem {S : Finset F.Cell} {z : F.Cell} (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {j : ℕ}
    (hj : j + 1 ≤ F.top) {x : F.Site (j + 1)} (hx : x ∈ sitesOfCells S (j + 1))
    (hp : baseSite x ∈ patchBaseSites S z) : x ∈ sitesOfCells (patchCells S z) (j + 1) := by
  classical
  obtain ⟨hc, hall⟩ := enclosingCell_mem_and_block_in_cell hodd hj hx
  obtain ⟨h', hh', e⟩ := hall 0 (zero_mem_centredCube hodd _)
  rw [siteOfCoords_zero, add_zero] at e
  rw [e] at hp
  refine BlockLines.mem_sitesOfCells_of_enclosingCell_mem hodd hx (Finset.mem_filter.2 ⟨hc, ?_⟩)
  rw [baseSite_eq_cellCentre]
  have := PatchLocality.mem_patchBaseSites_of_same_cell hamb hodd he hh' (zero_mem_centredCube hodd F.top) hp
  rwa [siteOfCoords_zero, add_zero] at this
theorem patchFitBonds_subset_innerBonds {S : Finset F.Cell} {z : F.Cell} (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {j : ℕ}
    (hj : j + 1 ≤ F.top) : patchFitBonds S z j ⊆ innerBonds (patchCells S z) (j + 1) := by
  classical
  intro c hc
  obtain ⟨h0, h1⟩ := Finset.mem_filter.1 hc
  obtain ⟨a1, a2⟩ := h1 0 (zero_mem_centredCube hodd _)
  rw [siteOfCoords_zero, add_zero] at a1 a2
  have hb := Finset.mem_filter.1 h0
  exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨mem_sitesOfCells_patchCells_of_baseSite_mem hamb hodd he hj
    (Finset.mem_product.1 hb.1).1 a1, Finset.mem_univ _⟩,
    mem_sitesOfCells_patchCells_of_baseSite_mem hamb hodd he hj hb.2 a2⟩
theorem card_patchCells {S : Finset F.Cell} {z : F.Cell} (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) : (patchCells S z).card ≤ 47 ^ 4 := by apply _root_.YangMills.Construction.BlockAverages.card_patchCells_le <;> assumption
theorem boundedOnAdjacentBlocks_of_innerBonds {B : Finset F.Cell} (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top)
    {f : F.Site j → Fin 4 → ℝ} {t : ℝ} (hf : ∀ b ∈ innerBonds B j, f b.1 b.2 ≤ t)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds B (j + 1)) : BoundedOnAdjacentBlocks f c t := by
  classical
  have h1 := Finset.mem_filter.1 hc
  have e1 : c.1 ∈ sitesOfCells B (j + 1) := (Finset.mem_product.1 h1.1).1
  have e2 : c.1 + unitStep (j + 1) c.2 ∈ sitesOfCells B (j + 1) := h1.2
  have hk : ∀ {y : F.Site (j + 1)}, y ∈ sitesOfCells B (j + 1) → ∀ h ∈ centredCube F.blockSide, ∀ k,
      h + Pi.single k 1 ∈ centredCube F.blockSide → (refineSite y + siteOfCoords j h, k) ∈ innerBonds B j := by
    intro y hy h hh k hk
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨BlockLines.refineSite_add_mem_sitesOfCells hj hodd y hy h hh,
      Finset.mem_univ _⟩, ?_⟩
    have e : refineSite y + siteOfCoords j h + unitStep j k = refineSite y + siteOfCoords j (h + Pi.single k 1) := by
      rw [add_assoc, siteOfCoords_add]
      rfl
    show refineSite y + siteOfCoords j h + unitStep j k ∈ sitesOfCells B j
    rw [e]
    exact BlockLines.refineSite_add_mem_sitesOfCells hj hodd y hy _ hk
  refine ⟨fun h hh k hk' => ⟨hf _ (hk e1 h hh k hk'), hf _ (hk e2 h hh k hk')⟩, fun h hh r hr => ?_⟩
  exact hf _ (BlockLines.lineBond_mem_innerBonds hj hodd c hc h hh r (Finset.mem_range.1 hr))
theorem le_of_sqrt_sqrt_sum_pow_four_le {ι : Type} (s : Finset ι) (f : ι → ℝ) (hf : ∀ b, 0 ≤ f b) (B : ℝ)
    (h : Real.sqrt (Real.sqrt (∑ b ∈ s, f b ^ 4)) ≤ B) : ∀ b ∈ s, f b ≤ B := by
  intro b hb
  have h1 : f b ^ 4 ≤ ∑ b ∈ s, f b ^ 4 :=
    Finset.single_le_sum (f := fun b => f b ^ 4) (fun _ _ => by positivity) hb
  refine le_trans ?_ h
  have h2 : f b = Real.sqrt (Real.sqrt (f b ^ 4)) := by
    rw [show f b ^ 4 = (f b ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity), Real.sqrt_sq (hf b)]
  rw [h2]
  exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h1)
section ChainGauge
variable (X : F.FieldChain) (k : F.SiteGauge) (Γ0 : F.Site 0 → UnitQuaternion)
theorem gaugedContourAverage_gaugedChain (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide) {j : ℕ}
    (hj : j < F.top) (c : F.Site (j + 1) × Fin 4) :
    gaugedContourAverage (gaugedChain X k Γ0 j) (balancedLinks (gaugedChain X k Γ0 j) (trivialField j) (fun _ => 1)) c =
      ((chainGauge X k Γ0 (j + 1) c.1 : UnitQuaternion) : ℍ[ℝ]) * gaugedContourAverage (X j) (k (j + 1)) c *
        (((chainGauge X k Γ0 (j + 1) (c.1 + unitStep (j + 1) c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  have h1 := (hG F j hj hL).2.1 (chainGauge X k Γ0 j) (X j) c
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = balancedLinks (gaugedChain X k Γ0 j) (trivialField j) (fun _ => 1) := ⟨_, rfl⟩
  have hg : ∀ y : F.Site (j + 1),
      chainGauge X k Γ0 (j + 1) y = τ y * chainGauge X k Γ0 j (refineSite y) * (k (j + 1) y)⁻¹ := by
    intro y
    rw [hτ]
    rfl
  unfold gaugedContourAverage
  rw [← hτ]
  show (τ c.1 : ℍ[ℝ]) * contourAverage (gaugeTransform (chainGauge X k Γ0 j) (X j)) c * _ = _
  rw [h1, hg c.1, hg (c.1 + unitStep (j + 1) c.2)]
  obtain ⟨a, ha⟩ : ∃ a, a = τ c.1 := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a, a = τ (c.1 + unitStep (j + 1) c.2) := ⟨_, rfl⟩
  obtain ⟨g, hg'⟩ : ∃ g, g = chainGauge X k Γ0 j (refineSite c.1) := ⟨_, rfl⟩
  obtain ⟨g', hg''⟩ : ∃ g, g = chainGauge X k Γ0 j (refineSite (c.1 + unitStep (j + 1) c.2)) := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ g, g = k (j + 1) c.1 := ⟨_, rfl⟩
  obtain ⟨κ', hκ'⟩ : ∃ g, g = k (j + 1) (c.1 + unitStep (j + 1) c.2) := ⟨_, rfl⟩
  rw [← ha, ← ha', ← hg', ← hg'', ← hκ, ← hκ']
  have e1 : ∀ w : ℍ[ℝ], ((κ⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((κ : ℍ[ℝ]) * w) = w := by
    intro w
    rw [← mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel]
    simp
  have e2 : ∀ w : ℍ[ℝ], ((κ'⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((κ' : ℍ[ℝ]) * w) = w := by
    intro w
    rw [← mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel]
    simp
  simp only [mul_inv_rev, inv_inv, Submonoid.coe_mul, mul_assoc]
  rw [e1, e2]
theorem polarUnit_conj (g g' : UnitQuaternion) {q : ℍ[ℝ]} (h : q ≠ 0) :
    polarUnit ((g : ℍ[ℝ]) * q * ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ])) = g * polarUnit q * g'⁻¹ := by apply _root_.YangMills.Construction.GaugeMotions.polarUnit_coe_mul_mul_coe_inv <;> assumption
theorem distFromOne_bondMisfit_gaugedChain (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide) {j : ℕ}
    (hj : j < F.top) (c : F.Site (j + 1) × Fin 4) (hq : gaugedContourAverage (X j) (k (j + 1)) c ≠ 0) :
    normSubOne (bondMisfit (gaugedChain X k Γ0 j)
      (balancedLinks (gaugedChain X k Γ0 j) (trivialField j) (fun _ => 1)) (gaugedChain X k Γ0 (j + 1)) c) =
      normSubOne (bondMisfit (X j) (k (j + 1)) (X (j + 1)) c) := by
  obtain ⟨g, hg⟩ : ∃ g, g = chainGauge X k Γ0 (j + 1) c.1 := ⟨_, rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g, g = chainGauge X k Γ0 (j + 1) (c.1 + unitStep (j + 1) c.2) := ⟨_, rfl⟩
  have e : bondMisfit (gaugedChain X k Γ0 j) (balancedLinks (gaugedChain X k Γ0 j) (trivialField j) (fun _ => 1))
      (gaugedChain X k Γ0 (j + 1)) c = g * bondMisfit (X j) (k (j + 1)) (X (j + 1)) c * g⁻¹ := by
    unfold bondMisfit
    rw [gaugedContourAverage_gaugedChain X k Γ0 hG hL hj, ← hg, ← hg', polarUnit_conj g g' hq]
    have hT : gaugedChain X k Γ0 (j + 1) c.1 c.2 = g * X (j + 1) c.1 c.2 * g'⁻¹ := by
      rw [hg, hg']
      rfl
    rw [hT]
    group
  rw [e]
  unfold normSubOne
  exact norm_coe_conj_sub_one _ _
theorem norm_gaugedContourAverage_gaugedChain (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide) {j : ℕ}
    (hj : j < F.top) (c : F.Site (j + 1) × Fin 4) :
    ‖gaugedContourAverage (gaugedChain X k Γ0 j)
      (balancedLinks (gaugedChain X k Γ0 j) (trivialField j) (fun _ => 1)) c‖ =
      ‖gaugedContourAverage (X j) (k (j + 1)) c‖ := by
  rw [gaugedContourAverage_gaugedChain X k Γ0 hG hL hj, norm_mul, norm_mul, norm_coe_unitQuaternion,
    norm_coe_unitQuaternion, one_mul, mul_one]
end ChainGauge
theorem linkGap_trivialField {j : ℕ} (T : F.GaugeField j) (x : F.Site j) (i : Fin 4) :
    linkGap T (trivialField j) x i = normSubOne (T x i) := by
  simp [linkGap, trivialField]
theorem bondMisfit_trivialField (hodd : Odd F.blockSide) {j : ℕ} (c : F.Site (j + 1) × Fin 4) :
    bondMisfit (trivialField (F := F) j) (fun _ => (1 : UnitQuaternion)) (trivialField (j + 1)) c = 1 := by
  have h1 : gaugedContourAverage (trivialField (F := F) j) (fun _ => (1 : UnitQuaternion)) c =
      ((1 : UnitQuaternion) : ℍ[ℝ]) := by
    unfold gaugedContourAverage
    rw [contourAverage_trivialField hodd]
    simp
  unfold bondMisfit
  rw [h1, BlockLines.polarUnit_coe]
  simp [trivialField]
set_option maxHeartbeats 1600000 in
theorem lowCostPatchBounds (hQ : patchQuarticGaugeStatement) (hR : UniformQuarticBoundAcrossLevels)
    (hO : gaugedOneStepComparisonStatement) (hG : gaugeCovarianceStatement) :
    lowCostPatchBoundsStatement := by
  classical
  obtain ⟨C₆, c₆, hC₆, hc₆, hQ'⟩ := hQ
  obtain ⟨CO, cO, hCO, hcO, hO'⟩ := hO
  intro a ha
  refine ⟨5, fun L hodd hL5 => ?_⟩
  have hLR : (0 : ℝ) < L := by exact_mod_cast hodd.pos
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = cO / L := ⟨_, rfl⟩
  have hc0p : 0 < c0 := by rw [hc0]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = CO * (L : ℝ) ^ 2 := ⟨_, rfl⟩
  have hKp : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨c1, hc1, hR'⟩ := hR L (47 ^ 4) K c0 hodd hL5 hKp hc0p
  obtain ⟨Bm, hBm⟩ : ∃ Bm : ℝ, Bm = 2 * C₆ + 2 / Real.sqrt a := ⟨_, rfl⟩
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hBmp : 0 < Bm := by rw [hBm]; positivity
  refine ⟨min (min (c₆ / 2) (c1 / Bm)) (c0 / (4 * Bm)), lt_min (lt_min (by positivity) (by positivity))
    (by positivity), ?_⟩
  intro e0 he0 hec F m S hFL hamb hm hreg X k z hz hcost
  have hodd' : Odd F.blockSide := hFL ▸ hodd
  have hLpos : 0 < F.blockSide := hodd'.pos
  obtain ⟨hs, -⟩ := closedOrthant_spec hreg (by omega : 32 ≤ m) z
  have he1 : e0 ≤ c₆ / 2 := hec.trans ((min_le_left _ _).trans (min_le_left _ _))
  have he2 : e0 ≤ c1 / Bm := hec.trans ((min_le_left _ _).trans (min_le_right _ _))
  have he3 : e0 ≤ c0 / (4 * Bm) := hec.trans (min_le_right _ _)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = Bm * e0 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hBc1 : B ≤ c1 := by
    rw [hB]
    rw [le_div_iff₀ hBmp] at he2
    linarith
  have hBc0 : 4 * B ≤ c0 := by
    rw [hB]
    rw [le_div_iff₀ (by positivity)] at he3
    linarith
  have hpl0 : 0 ≤ ∑ p ∈ patchPlaquettes S z, (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) :=
    Finset.sum_nonneg fun p _ => by
      have := quaternion_re_le_norm ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ])
      rw [norm_coe_unitQuaternion] at this
      linarith
  have hfit0 : ∀ j, ∀ c, 0 ≤ gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c :=
    fun j c => PatchLocality.gaugedBlockFit_nonneg _ _ _ _
  have hfits0 : 0 ≤ ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j,
      gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => hfit0 j c
  have hcost' : ∑ p ∈ patchPlaquettes S z, (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) +
      a * ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j, gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c ≤
        e0 ^ 2 := hcost
  have hsq : ∑ p ∈ patchPlaquettes S z, normSubOne (plaquetteHolonomy (X 0) p) ^ 2 ≤ 2 * e0 ^ 2 := by
    have e1 : ∑ p ∈ patchPlaquettes S z, normSubOne (plaquetteHolonomy (X 0) p) ^ 2 =
        2 * ∑ p ∈ patchPlaquettes S z, (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by rw [normSubOne_sq]; ring
    rw [e1]
    have : 0 ≤ a * ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j,
        gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c :=
      mul_nonneg ha.le hfits0
    linarith
  have hfitsum : a * ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j,
      gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c ≤ e0 ^ 2 := by linarith
  obtain ⟨Γ0, hΓ0⟩ := hQ' F m S hodd' hamb hm hreg z (X 0) (2 * e0) hz (by positivity) (by linarith)
    (hsq.trans (by nlinarith [sq_nonneg e0]))
  obtain ⟨aF, haF⟩ : ∃ aF : (j : ℕ) → F.Site j → Fin 4 → ℝ, aF = fun j =>
    linkGap (gaugedChain X k Γ0 j) (trivialField j) := ⟨_, rfl⟩
  obtain ⟨mF, hmF⟩ : ∃ mF : (j : ℕ) → F.Site (j + 1) → Fin 4 → ℝ, mF = fun j y i =>
    2 * Real.sqrt (gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) (y, i)) := ⟨_, rfl⟩
  have haF0 : ∀ j x i, 0 ≤ aF j x i := by
    intro j x i
    rw [haF]
    exact norm_nonneg _
  have hmF0 : ∀ j x i, 0 ≤ mF j x i := by
    intro j x i
    rw [hmF]
    positivity
  have hone : ∀ j, j < F.top → ∀ (c : F.Site (j + 1) × Fin 4) (t : ℝ), 0 ≤ t → t ≤ c0 →
      BoundedOnAdjacentBlocks (aF j) c t → 1 / 2 ≤ ‖gaugedContourAverage (X j) (k (j + 1)) c‖ ∧
      normSubOne (gaugedChain X k Γ0 (j + 1) c.1 c.2) ≤
        normSubOne (bondMisfit (X j) (k (j + 1)) (X (j + 1)) c) + lineBlockAverage (aF j) c + K * t ^ 2 := by
    intro j hj c t ht0 htc hbl
    rw [haF] at hbl ⊢
    have hLt : (F.blockSide : ℝ) * t ≤ cO := by
      rw [hc0, le_div_iff₀ hLR] at htc
      rw [hFL]
      linarith
    have hsp : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
        normSubOne (pathHolonomy (trivialField j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
          (polarUnit (contourAverage (trivialField j) c))⁻¹) ≤ 0 := by
      intro h _ π
      have e1 : polarUnit (contourAverage (trivialField (F := F) j) c) = 1 := by
        rw [contourAverage_trivialField hodd']
        exact BlockLines.polarUnit_coe 1
      rw [e1, pathHolonomy_trivialField]
      simp [normSubOne]
    obtain ⟨r1, r2⟩ := hO' F j (gaugedChain X k Γ0 j) (trivialField j) (fun _ => 1) (gaugedChain X k Γ0 (j + 1))
      (trivialField (j + 1)) c t 0 hodd' hj ht0 le_rfl hLt hcO.le hbl hsp
    rw [norm_gaugedContourAverage_gaugedChain X k Γ0 hG hLpos hj] at r1
    have hq : gaugedContourAverage (X j) (k (j + 1)) c ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at r1
      linarith
    refine ⟨r1, ?_⟩
    rw [bondMisfit_trivialField hodd', inv_one, mul_one, distFromOne_bondMisfit_gaugedChain X k Γ0 hG hLpos hj c hq] at r2
    have e2 : normSubOne (gaugedChain X k Γ0 (j + 1) c.1 c.2 * (trivialField (j + 1) c.1 c.2)⁻¹) =
        normSubOne (gaugedChain X k Γ0 (j + 1) c.1 c.2) := by
      simp [trivialField]
    rw [e2] at r2
    have e3 : CO * ((F.blockSide : ℝ) * t) * ((F.blockSide : ℝ) * t + 0) = K * t ^ 2 := by
      rw [hK, hFL]
      ring
    rw [e3] at r2
    exact r2
  have hmis : ∀ j, j < F.top → ∀ c : F.Site (j + 1) × Fin 4,
      1 / 2 ≤ ‖gaugedContourAverage (X j) (k (j + 1)) c‖ →
      normSubOne (bondMisfit (X j) (k (j + 1)) (X (j + 1)) c) ^ 2 ≤
        4 * gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c := by
    intro j _ c hr
    have hq : gaugedContourAverage (X j) (k (j + 1)) c ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hr
      linarith
    have e1 := norm_sub_re_eq_mul_distFromOne_sq hq (X (j + 1) c.1 c.2)
    have e2 : gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c = ‖gaugedContourAverage (X j) (k (j + 1)) c‖ *
        (normSubOne (bondMisfit (X j) (k (j + 1)) (X (j + 1)) c) ^ 2 / 2) := e1
    rw [e2]
    have : 0 ≤ normSubOne (bondMisfit (X j) (k (j + 1)) (X (j + 1)) c) ^ 2 := sq_nonneg _
    nlinarith
  have hroot := hR' F (patchCells S z) aF mF 0 B hFL (card_patchCells hamb hodd' hs) le_rfl hc1.le hB0 hBc1 haF0 hmF0
    ?_ ?_ ?_
  · have hbond : ∀ j, j < F.top → ∀ b ∈ innerBonds (patchCells S z) j, aF j b.1 b.2 ≤ 4 * B := by
      intro j hj b hb
      exact le_of_sqrt_sqrt_sum_pow_four_le (innerBonds (patchCells S z) j) (fun b => aF j b.1 b.2)
        (fun b => haF0 j b.1 b.2) _ (hroot j hj) b hb
    have hmean : ∀ j, j < F.top → ∀ b ∈ patchFitBonds S z j,
        1 / 2 ≤ ‖gaugedContourAverage (X j) (k (j + 1)) b‖ := by
      intro j hj b hb
      exact (hone j hj b (4 * B) (by positivity) hBc0 (boundedOnAdjacentBlocks_of_innerBonds hodd' hj (hbond j hj)
        (patchFitBonds_subset_innerBonds hamb hodd' hs hj hb))).1
    refine ⟨hmean, ?_, hsq⟩
    have h1 : ∑ j ∈ Finset.range F.top, ∑ b ∈ patchFitBonds S z j,
        normSubOne (bondMisfit (X j) (k (j + 1)) (X (j + 1)) b) ^ 2 ≤
        4 * ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j,
          gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b hb => ?_
      exact hmis j (Finset.mem_range.1 hj) b (hmean j (Finset.mem_range.1 hj) b hb)
    refine h1.trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]
    nlinarith
  · have h1 : ∑ b ∈ innerBonds (patchCells S z) 0, aF 0 b.1 b.2 ^ 4 ≤ (C₆ * (2 * e0)) ^ 4 := by
      refine le_trans ?_ hΓ0
      have hsub := innerBonds_patchCells_zero_subset (S := S) (z := z) hamb hodd' hs
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => by positivity)
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [haF]
      simp only
      rw [linkGap_trivialField]
      rfl
    have h2 : C₆ * (2 * e0) ≤ B := by
      rw [hB, hBm]
      have : 0 ≤ 2 / Real.sqrt a * e0 := by positivity
      nlinarith
    have h3 : Real.sqrt (Real.sqrt (∑ b ∈ innerBonds (patchCells S z) 0, aF 0 b.1 b.2 ^ 4)) ≤ C₆ * (2 * e0) := by
      have hp : 0 ≤ C₆ * (2 * e0) := by positivity
      have e1 : (C₆ * (2 * e0)) = Real.sqrt (Real.sqrt ((C₆ * (2 * e0)) ^ 4)) := by
        rw [show (C₆ * (2 * e0)) ^ 4 = ((C₆ * (2 * e0)) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity),
          Real.sqrt_sq hp]
      rw [e1]
      exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h1)
    linarith
  · intro j hj
    have hj' : j < F.top := by omega
    have h1 : ∑ c ∈ innerBonds (patchCells S z) (j + 1), mF j c.1 c.2 ^ 2 ≤
        4 * ∑ c ∈ patchFitBonds S z j, gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c := by
      rw [Finset.mul_sum]
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg
        (innerBonds_patchCells_subset_patchFitBonds hamb hodd' hs (by omega : j + 1 ≤ F.top)) fun c _ _ => by
          have := hfit0 j c
          positivity)
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hmF]
      simp only
      rw [mul_pow, Real.sq_sqrt (hfit0 j _)]
      norm_num
    have h2 : ∑ c ∈ patchFitBonds S z j, gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c ≤
        ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j, gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c :=
      Finset.single_le_sum (f := fun j => ∑ c ∈ patchFitBonds S z j, gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c)
        (fun j _ => Finset.sum_nonneg fun c _ => hfit0 j c) (Finset.mem_range.2 hj')
    have h3 : ∑ c ∈ innerBonds (patchCells S z) (j + 1), mF j c.1 c.2 ^ 2 ≤ (2 / Real.sqrt a * e0) ^ 2 := by
      have e1 : (2 / Real.sqrt a * e0) ^ 2 = 4 * (e0 ^ 2 / a) := by
        rw [mul_pow, div_pow, Real.sq_sqrt ha.le]
        ring
      rw [e1]
      have h4 : ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j,
          gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c ≤ e0 ^ 2 / a := by
        rw [le_div_iff₀ ha]
        linarith
      linarith
    have h4 : Real.sqrt (∑ c ∈ innerBonds (patchCells S z) (j + 1), mF j c.1 c.2 ^ 2) ≤ 2 / Real.sqrt a * e0 := by
      refine (Real.sqrt_le_sqrt h3).trans ?_
      rw [Real.sqrt_sq (by positivity)]
    refine h4.trans ?_
    rw [hB, hBm]
    have : 0 ≤ 2 * C₆ * e0 := by positivity
    nlinarith
  · intro j hj c _ t ht0 htc hm' hbl
    have hj' : j < F.top := by omega
    have hjj : j + 1 < F.top := hj
    obtain ⟨r1, r2⟩ := hone j hj' c t ht0 htc hbl
    have hmm : normSubOne (bondMisfit (X j) (k (j + 1)) (X (j + 1)) c) ≤ mF j c.1 c.2 := by
      have h1 := hmis j hj' c r1
      rw [hmF]
      simp only
      have h2 : normSubOne (bondMisfit (X j) (k (j + 1)) (X (j + 1)) c) ≤
          Real.sqrt (4 * gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c) := Real.le_sqrt_of_sq_le h1
      have h3 : Real.sqrt (4 * gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c) =
          2 * Real.sqrt (gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) (c.1, c.2)) := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [← h3]
      exact h2
    have e1 : aF (j + 1) c.1 c.2 = normSubOne (gaugedChain X k Γ0 (j + 1) c.1 c.2) := by
      rw [haF]
      exact linkGap_trivialField _ _ _
    rw [e1]
    have h5 : K * t ^ 2 ≤ K * (t ^ 2 + (0 * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 + mF j c.1 c.2 +
        0 * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 3) * t) := by
      refine mul_le_mul_of_nonneg_left ?_ hKp
      have := mul_nonneg (hmF0 j c.1 c.2) ht0
      nlinarith
    linarith
end LowCostPatch
end BlockAverages
end YangMills.Construction
end
