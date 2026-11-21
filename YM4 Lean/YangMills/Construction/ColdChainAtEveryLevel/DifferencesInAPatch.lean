import YangMills.Construction.ColdChainAtEveryLevel.FramesOfAPatch
import YangMills.Construction.ColdChainAtEveryLevel.KernelsOnCells
import YangMills.Construction.ColdChainAtEveryLevel.SharesAcrossABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace PatchDifferences
open BlockAverages GaugeMap PatchFrames LatticeFractionalIntegration PatchPoints BondShares FiniteDifferences
variable {F : BlockFrame}
def localSection (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (ξ : F.Site 0 → ℍ[ℝ]) (a : Lattice4) :
    ℍ[ℝ] :=
  adjointAction (frameChange S V z (patchSite S z a))⁻¹ (ξ (patchSite S z a))
def sectionNormOn (S : Finset F.Cell) (ξ : F.Site 0 → ℍ[ℝ]) : F.Site 0 → ℝ := by
  classical exact fun t => if t ∈ sitesOfCells S 0 then ‖ξ t‖ else 0
def formNormOn (S : Finset F.Cell) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) : F.Site 0 → ℝ := by
  classical exact fun t => ∑ i, if (t, i) ∈ innerBonds S 0 then ‖f t i‖ else 0
structure PatchRemainder (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (ξ : F.Site 0 → ℍ[ℝ])
    (ρ : Lattice4 → ℍ[ℝ]) (D : F.Site 0 → ℝ) (C : ℝ) : Prop where
  stepBound_nonneg : ∀ t, 0 ≤ D t
  stepBound_eq_zero : ∀ t, t ∉ patchSiteSet S z → D t = 0
  localPotential_sub_mean : ∀ a ∈ patchDomain S z,
    localPotential S V (referenceFieldChain S V 0) z (covariantDiff (referenceFieldChain S V 0) ξ) a -
        localPotentialMean S V (referenceFieldChain S V 0) z (covariantDiff (referenceFieldChain S V 0) ξ) =
      - localSection S V z ξ a + ρ a
  norm_step_le : ∀ a ∈ patchDomain S z, ∀ i, a + basisVector i ∈ patchDomain S z →
    ‖ρ (a + basisVector i) - ρ a‖ ≤ D (patchSite S z a)
  norm_le : ∀ a ∈ patchDomain S z, ‖ρ a‖ ≤ C * patchCubicKernel S z D (patchSite S z a) +
    C * ((1 / (cellSideLength F : ℝ) ^ 4) * ∑ x ∈ cellOffsets F, patchCubicKernel S z D (patchSite S z x))
section Algebra
theorem adjointAction_mul (g h : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction (g * h) w = adjointAction g (adjointAction h w) := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_mul <;> assumption
theorem adjointAction_inv_apply_self (g : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction g⁻¹ (adjointAction g w) = w := by apply _root_.YangMills.Construction.CellBumps.adjointAction_inv_adjointAction <;> assumption
theorem adjointAction_sub_apply (g : UnitQuaternion) (p q : ℍ[ℝ]) :
    adjointAction g (p - q) = adjointAction g p - adjointAction g q := by apply _root_.YangMills.Construction.BlockLines.adjointAction_sub <;> assumption
theorem norm_adjointAction_apply (g : UnitQuaternion) (w : ℍ[ℝ]) : ‖adjointAction g w‖ = ‖w‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction <;> assumption
theorem norm_adjointAction_sub_self_le (g : UnitQuaternion) (q : ℍ[ℝ]) :
    ‖adjointAction g q - q‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ * ‖q‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction_sub_le <;> assumption
theorem norm_adjointAction_sub_adjointAction_le (g h : UnitQuaternion) (q : ℍ[ℝ]) :
    ‖adjointAction g q - adjointAction h q‖ ≤ 2 * ‖(g : ℍ[ℝ]) - (h : ℍ[ℝ])‖ * ‖q‖ := by
  have e : adjointAction g q - adjointAction h q =
      ((g : ℍ[ℝ]) - h) * q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
        (h : ℍ[ℝ]) * q * (((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((h⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by
    simp only [adjointAction, sub_mul, mul_sub]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, mul_one, one_mul]
  have h1 : ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((h⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(g : ℍ[ℝ]) - (h : ℍ[ℝ])‖ := by
    rw [coe_unitQuaternion_inv, coe_unitQuaternion_inv, ← star_sub, norm_star]
  rw [h1]
  have := mul_comm ‖q‖ ‖(g : ℍ[ℝ]) - (h : ℍ[ℝ])‖
  linarith
end Algebra
section Lines
variable {F : BlockFrame} {S : Finset F.Cell}
theorem quaternionPairing_swap (f g : F.Cell → ℍ[ℝ]) :
    quaternionPairing S g f = star (quaternionPairing S f g) := by
  simp only [quaternionPairing, star_sum, star_mul, star_star]
theorem leadingTransport_swap (V : F.GaugeField F.top) (s s' : F.Site 0) :
    leadingTransport S V s' s = (leadingTransport S V s s')⁻¹ := by
  simp only [leadingTransport]
  rw [quaternionPairing_swap, polarUnit_star]
theorem baseSite_zero_depth (x : F.Site 0) : baseSite x = x := by apply _root_.YangMills.Construction.CellBumps.baseSite_zero <;> assumption
theorem referenceFieldChain_zero_apply (V : F.GaugeField F.top) (x : F.Site 0) (i : Fin 4) :
    referenceFieldChain S V 0 x i = leadingTransport S V x (x + unitStep 0 i) := by
  have h0 : (0 : ℕ) ≠ F.top := by simp [BlockFrame.top]
  simp only [referenceFieldChain, Function.update_of_ne h0, referenceGaugeField, leadingTransport,
    baseSite_zero_depth]
end Lines
section Chart
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
theorem patchSite_add_basisVector (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (a : Lattice4)
    (i : Fin 4) :
    (closedOrthant S z i = 1 → patchSite S z (a + basisVector i) = patchSite S z a + unitStep 0 i) ∧
      (closedOrthant S z i = -1 → patchSite S z a = patchSite S z (a + basisVector i) + unitStep 0 i) := by
  have e : patchSite S z (a + basisVector i) =
      patchSite S z a + siteOfCoords 0 (fun k => closedOrthant S z k * basisVector i k) := by
    unfold patchSite
    rw [add_assoc, ← siteOfCoords_add]
    congr 2
    funext k
    simp only [Pi.add_apply]
    ring
  have e1 : (fun k => closedOrthant S z k * basisVector i k) = (closedOrthant S z i) • basisVector i := by
    funext k
    simp only [basisVector, Pi.smul_apply, smul_eq_mul]
    by_cases hk : k = i
    · subst hk; rfl
    · simp [hk]
  rw [e1] at e
  constructor
  · intro h
    rw [e, h, one_smul]
    rfl
  · intro h
    rw [e, h]
    have : siteOfCoords (F := F) 0 ((-1 : ℤ) • basisVector i) = - unitStep 0 i := by
      rw [neg_smul, one_smul, siteOfCoords_neg]
      rfl
    rw [this]
    abel
theorem covariantDiff_oriented (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (ξ : F.Site 0 → ℍ[ℝ]) (a : Lattice4) (i : Fin 4) :
    (if closedOrthant S z i = 1 then covariantDiff (referenceFieldChain S V 0) ξ (patchSite S z a) i
      else - adjointAction (referenceFieldChain S V 0 (patchSite S z (a + basisVector i)) i)⁻¹
        (covariantDiff (referenceFieldChain S V 0) ξ (patchSite S z (a + basisVector i)) i)) =
      adjointAction (leadingTransport S V (patchSite S z a) (patchSite S z (a + basisVector i)))
          (ξ (patchSite S z (a + basisVector i))) -
        ξ (patchSite S z a) := by
  obtain ⟨h1, h2⟩ := patchSite_add_basisVector he a i
  rcases he i with h | h
  · rw [if_pos h]
    have e := h1 h
    simp only [covariantDiff, referenceFieldChain_zero_apply, e]
  · have hne : closedOrthant S z i ≠ 1 := by rw [h]; norm_num
    rw [if_neg hne]
    have e := h2 h
    simp only [covariantDiff, referenceFieldChain_zero_apply]
    rw [← e, adjointAction_sub_apply, adjointAction_inv_apply_self,
      leadingTransport_swap V (patchSite S z a) (patchSite S z (a + basisVector i))]
    rw [inv_inv]
    abel
variable {R : Lattice4 → Lattice4 → UnitQuaternion} {Cs r : ℝ}
theorem supNorm_basisVector (i : Fin 4) : supNorm (basisVector i) = 1 := by apply _root_.YangMills.Construction.LatticePaths.supNorm_basisVector <;> assumption
theorem supNorm_add_basisVector_sub (a : Lattice4) (i : Fin 4) : supNorm (a + basisVector i - a) = 1 := by
  rw [add_sub_cancel_left]
  exact supNorm_basisVector i
def remainderForm (R : Lattice4 → Lattice4 → UnitQuaternion) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (z : F.Cell) (ξ : F.Site 0 → ℍ[ℝ]) : Lattice4 → Fin 4 → ℍ[ℝ] :=
  fun a i => adjointAction (R a (a + basisVector i)) (localSection S V z ξ (a + basisVector i)) -
    localSection S V z ξ (a + basisVector i)
theorem localForm_eq_latticeDifference_add (hF : IsPatchFrame S V z R Cs r) (hr1 : 1 ≤ r * cellSideLength F)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (ξ : F.Site 0 → ℍ[ℝ]) {a : Lattice4} {i : Fin 4}
    (ha : a ∈ patchDomain S z) (ha' : a + basisVector i ∈ patchDomain S z) :
    localForm S V (referenceFieldChain S V 0) z (covariantDiff (referenceFieldChain S V 0) ξ) a i =
      latticeDifference (localSection S V z ξ) a i + remainderForm R S V z ξ a i := by
  have hl := hF.leadingTransport_eq a ha (a + basisVector i) ha' (by rw [supNorm_add_basisVector_sub]; simpa using hr1)
  simp only [localForm, latticeDifference, remainderForm]
  rw [covariantDiff_oriented he ξ a i, hl, adjointAction_sub_apply]
  simp only [localSection]
  rw [← adjointAction_mul, ← adjointAction_mul]
  have e : (frameChange S V z (patchSite S z a))⁻¹ * (frameChange S V z (patchSite S z a) * R a (a + basisVector i) *
      (frameChange S V z (patchSite S z (a + basisVector i)))⁻¹) =
      R a (a + basisVector i) * (frameChange S V z (patchSite S z (a + basisVector i)))⁻¹ := by
    group
  rw [e]
  abel
theorem norm_localSection (ξ : F.Site 0 → ℍ[ℝ]) (a : Lattice4) :
    ‖localSection S V z ξ a‖ = ‖ξ (patchSite S z a)‖ := norm_adjointAction_apply _ _
theorem norm_remainderForm_le (hF : IsPatchFrame S V z R Cs r) (hr1 : 1 ≤ r * cellSideLength F)
    (ξ : F.Site 0 → ℍ[ℝ]) {a : Lattice4} {i : Fin 4}
    (ha : a ∈ patchDomain S z) (ha' : a + basisVector i ∈ patchDomain S z) (hC : 0 ≤ Cs) :
    ‖remainderForm R S V z ξ a i‖ ≤
      2 * Cs / (cellSideLength F : ℝ) * ‖ξ (patchSite S z (a + basisVector i))‖ := by
  have hn := hF.norm_sub_one_le a ha (a + basisVector i) ha'
    (by rw [supNorm_add_basisVector_sub]; simpa using hr1)
  rw [supNorm_add_basisVector_sub] at hn
  simp only [remainderForm]
  refine (norm_adjointAction_sub_self_le _ _).trans ?_
  rw [norm_localSection]
  have h1 : 0 ≤ ‖ξ (patchSite S z (a + basisVector i))‖ := norm_nonneg _
  have h2 : ‖((R a (a + basisVector i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Cs / (cellSideLength F : ℝ) := by
    simpa [div_eq_mul_inv] using hn
  calc _ ≤ 2 * (Cs / (cellSideLength F : ℝ)) * ‖ξ (patchSite S z (a + basisVector i))‖ := by
        exact mul_le_mul_of_nonneg_right (by linarith) h1
    _ = _ := by ring
end Chart
section Curl
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
  {R : Lattice4 → Lattice4 → UnitQuaternion} {Cs r : ℝ}
theorem norm_remainderForm_sub_le (hF : IsPatchFrame S V z R Cs r) (hr1 : 1 ≤ r * cellSideLength F) (hC : 0 ≤ Cs)
    (ξ : F.Site 0 → ℍ[ℝ]) {y : Lattice4} {μ ν : Fin 4} (h0 : y ∈ patchDomain S z)
    (h1 : y + basisVector μ ∈ patchDomain S z) (h2 : y + basisVector ν ∈ patchDomain S z)
    (h3 : y + basisVector ν + basisVector μ ∈ patchDomain S z) :
    ‖remainderForm R S V z ξ y μ - remainderForm R S V z ξ (y + basisVector ν) μ‖ ≤
      2 * Cs / (cellSideLength F : ℝ) ^ 2 * ‖ξ (patchSite S z (y + basisVector μ))‖ +
        2 * Cs / (cellSideLength F : ℝ) *
          ‖localSection S V z ξ (y + basisVector μ) - localSection S V z ξ (y + basisVector ν + basisVector μ)‖ := by
  set q := localSection S V z ξ (y + basisVector μ) with hq
  set q' := localSection S V z ξ (y + basisVector ν + basisVector μ) with hq'
  set T := R y (y + basisVector μ) with hT
  set T' := R (y + basisVector ν) (y + basisVector ν + basisVector μ) with hT'
  have e : remainderForm R S V z ξ y μ - remainderForm R S V z ξ (y + basisVector ν) μ =
      (adjointAction T q - adjointAction T' q) + (adjointAction T' (q - q') - (q - q')) := by
    simp only [remainderForm, adjointAction_sub_apply]
    rw [← hq, ← hq', ← hT, ← hT']
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have hs := hF.norm_second_diff_le hr1 y (basisVector μ) (basisVector ν) (supNorm_basisVector μ)
    (supNorm_basisVector ν) h0 h1 h2 h3
  have hn := hF.norm_sub_one_le (y + basisVector ν) h2 (y + basisVector ν + basisVector μ) h3
    (by rw [supNorm_add_basisVector_sub]; simpa using hr1)
  rw [supNorm_add_basisVector_sub] at hn
  have hn' : ‖((T' : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Cs / (cellSideLength F : ℝ) := by
    simpa [div_eq_mul_inv] using hn
  have a1 := norm_adjointAction_sub_adjointAction_le T T' q
  have a2 := norm_adjointAction_sub_self_le T' (q - q')
  have hqn : ‖q‖ = ‖ξ (patchSite S z (y + basisVector μ))‖ := norm_localSection ξ _
  rw [hqn] at a1
  have b1 : 2 * ‖((T : UnitQuaternion) : ℍ[ℝ]) - (T' : ℍ[ℝ])‖ * ‖ξ (patchSite S z (y + basisVector μ))‖ ≤
      2 * Cs / (cellSideLength F : ℝ) ^ 2 * ‖ξ (patchSite S z (y + basisVector μ))‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hs (by norm_num)
  have b2 : 2 * ‖((T' : UnitQuaternion) : ℍ[ℝ]) - 1‖ * ‖q - q'‖ ≤
      2 * Cs / (cellSideLength F : ℝ) * ‖q - q'‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hn' (by norm_num)
  linarith
theorem norm_plaquetteCurl_remainderForm_le (hF : IsPatchFrame S V z R Cs r) (hr1 : 1 ≤ r * cellSideLength F)
    (hC : 0 ≤ Cs) (ξ : F.Site 0 → ℍ[ℝ]) {y : Lattice4} {μ ν : Fin 4} (h0 : y ∈ patchDomain S z)
    (h1 : y + basisVector μ ∈ patchDomain S z) (h2 : y + basisVector ν ∈ patchDomain S z)
    (h3 : y + basisVector μ + basisVector ν ∈ patchDomain S z) :
    ‖plaquetteCurl (remainderForm R S V z ξ) y μ ν‖ ≤
      2 * Cs / (cellSideLength F : ℝ) ^ 2 *
          (‖ξ (patchSite S z (y + basisVector μ))‖ + ‖ξ (patchSite S z (y + basisVector ν))‖) +
        2 * Cs / (cellSideLength F : ℝ) *
          (‖latticeDifference (localSection S V z ξ) (y + basisVector μ) ν‖ +
            ‖latticeDifference (localSection S V z ξ) (y + basisVector ν) μ‖) := by
  have h3' : y + basisVector ν + basisVector μ ∈ patchDomain S z := by rwa [add_right_comm]
  have p1 := norm_remainderForm_sub_le hF hr1 hC ξ h0 h1 h2 h3'
  have p2 := norm_remainderForm_sub_le hF hr1 hC ξ h0 h2 h1 h3
  have e : plaquetteCurl (remainderForm R S V z ξ) y μ ν =
      (remainderForm R S V z ξ y μ - remainderForm R S V z ξ (y + basisVector ν) μ) -
        (remainderForm R S V z ξ y ν - remainderForm R S V z ξ (y + basisVector μ) ν) := by
    simp only [plaquetteCurl]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have d1 : ‖localSection S V z ξ (y + basisVector μ) - localSection S V z ξ (y + basisVector ν + basisVector μ)‖ =
      ‖latticeDifference (localSection S V z ξ) (y + basisVector μ) ν‖ := by
    simp only [latticeDifference]
    rw [norm_sub_rev, add_right_comm]
  have d2 : ‖localSection S V z ξ (y + basisVector ν) - localSection S V z ξ (y + basisVector μ + basisVector ν)‖ =
      ‖latticeDifference (localSection S V z ξ) (y + basisVector ν) μ‖ := by
    simp only [latticeDifference]
    rw [norm_sub_rev, add_right_comm]
  rw [d1] at p1
  rw [d2] at p2
  have e2 : 2 * Cs / (cellSideLength F : ℝ) ^ 2 *
          (‖ξ (patchSite S z (y + basisVector μ))‖ + ‖ξ (patchSite S z (y + basisVector ν))‖) +
        2 * Cs / (cellSideLength F : ℝ) *
          (‖latticeDifference (localSection S V z ξ) (y + basisVector μ) ν‖ +
            ‖latticeDifference (localSection S V z ξ) (y + basisVector ν) μ‖) =
      (2 * Cs / (cellSideLength F : ℝ) ^ 2 * ‖ξ (patchSite S z (y + basisVector μ))‖ +
        2 * Cs / (cellSideLength F : ℝ) * ‖latticeDifference (localSection S V z ξ) (y + basisVector μ) ν‖) +
      (2 * Cs / (cellSideLength F : ℝ) ^ 2 * ‖ξ (patchSite S z (y + basisVector ν))‖ +
        2 * Cs / (cellSideLength F : ℝ) * ‖latticeDifference (localSection S V z ξ) (y + basisVector ν) μ‖) := by
    ring
  rw [e2]
  exact add_le_add p1 p2
theorem norm_localForm_le (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (hP : patchSiteSet S z ⊆ sitesOfCells S 0) (ξ : F.Site 0 → ℍ[ℝ]) {a : Lattice4} {i : Fin 4}
    (ha : a ∈ patchDomain S z) (ha' : a + basisVector i ∈ patchDomain S z) :
    ‖localForm S V (referenceFieldChain S V 0) z (covariantDiff (referenceFieldChain S V 0) ξ) a i‖ ≤
      formNormOn S (covariantDiff (referenceFieldChain S V 0) ξ) (patchSite S z a) +
        formNormOn S (covariantDiff (referenceFieldChain S V 0) ξ) (patchSite S z (a + basisVector i)) := by
  classical
  obtain ⟨k1, k2⟩ := patchSite_add_basisVector he a i
  have hs : patchSite S z a ∈ sitesOfCells S 0 := hP (Finset.mem_image_of_mem _ ha)
  have hs' : patchSite S z (a + basisVector i) ∈ sitesOfCells S 0 := hP (Finset.mem_image_of_mem _ ha')
  have hform0 : ∀ t, 0 ≤ formNormOn S (covariantDiff (referenceFieldChain S V 0) ξ) t := fun t =>
    Finset.sum_nonneg fun _ _ => by split_ifs <;> simp
  have hone : ∀ t (k : Fin 4), (t, k) ∈ innerBonds S 0 →
      ‖covariantDiff (referenceFieldChain S V 0) ξ t k‖ ≤
        formNormOn S (covariantDiff (referenceFieldChain S V 0) ξ) t := by
    intro t k hb
    have := Finset.single_le_sum (f := fun k => if (t, k) ∈ innerBonds S 0 then
      ‖covariantDiff (referenceFieldChain S V 0) ξ t k‖ else 0)
      (fun _ _ => by split_ifs <;> simp) (Finset.mem_univ k)
    simpa [formNormOn, hb] using this
  simp only [localForm]
  rw [norm_adjointAction_apply]
  rcases he i with h | h
  · rw [if_pos h]
    have hb : (patchSite S z a, i) ∈ innerBonds S 0 := by
      refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hs, Finset.mem_univ _⟩, ?_⟩
      rw [← k1 h]
      exact hs'
    have := hform0 (patchSite S z (a + basisVector i))
    linarith [hone _ _ hb]
  · have hne : closedOrthant S z i ≠ 1 := by rw [h]; norm_num
    rw [if_neg hne, norm_neg, norm_adjointAction_apply]
    have hb : (patchSite S z (a + basisVector i), i) ∈ innerBonds S 0 := by
      refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hs', Finset.mem_univ _⟩, ?_⟩
      rw [← k2 h]
      exact hs
    have := hform0 (patchSite S z a)
    linarith [hone _ _ hb]
theorem norm_latticeDifference_localSection_le (hF : IsPatchFrame S V z R Cs r) (hr1 : 1 ≤ r * cellSideLength F)
    (hC : 0 ≤ Cs) (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (hP : patchSiteSet S z ⊆ sitesOfCells S 0) (ξ : F.Site 0 → ℍ[ℝ]) {a : Lattice4} {i : Fin 4}
    (ha : a ∈ patchDomain S z) (ha' : a + basisVector i ∈ patchDomain S z) :
    ‖latticeDifference (localSection S V z ξ) a i‖ ≤
      formNormOn S (covariantDiff (referenceFieldChain S V 0) ξ) (patchSite S z a) +
        formNormOn S (covariantDiff (referenceFieldChain S V 0) ξ) (patchSite S z (a + basisVector i)) +
          2 * Cs / (cellSideLength F : ℝ) * ‖ξ (patchSite S z (a + basisVector i))‖ := by
  have e := localForm_eq_latticeDifference_add hF hr1 he ξ ha ha'
  have h1 := norm_localForm_le (V := V) he hP ξ ha ha'
  have h2 := norm_remainderForm_le hF hr1 ξ ha ha' hC
  have e2 : latticeDifference (localSection S V z ξ) a i =
      localForm S V (referenceFieldChain S V 0) z (covariantDiff (referenceFieldChain S V 0) ξ) a i -
        remainderForm R S V z ξ a i := by
    rw [e]
    abel
  rw [e2]
  refine (norm_sub_le _ _).trans ?_
  linarith
end Curl
section Totals
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
def neighbourSum (S : Finset F.Cell) (z : F.Cell) (f : F.Site 0 → ℝ) : F.Site 0 → ℝ :=
  restrictToPatch S z (fun t => f t + ∑ st : PathStep, f (t + stepDisplacement 0 st))
theorem restrictToPatch_nonneg {f : F.Site 0 → ℝ} (hf : ∀ t, 0 ≤ f t) (t : F.Site 0) :
    0 ≤ restrictToPatch S z f t := by
  classical
  simp only [restrictToPatch]
  split_ifs
  · exact hf t
  · exact le_rfl
theorem neighbourSum_nonneg {f : F.Site 0 → ℝ} (hf : ∀ t, 0 ≤ f t) (t : F.Site 0) : 0 ≤ neighbourSum S z f t :=
  restrictToPatch_nonneg (fun t => add_nonneg (hf t) (Finset.sum_nonneg fun _ _ => hf _)) t
theorem restrictToPatch_of_mem {f : F.Site 0 → ℝ} {t : F.Site 0} (ht : t ∈ patchSiteSet S z) :
    restrictToPatch S z f t = f t := by
  classical
  simp [restrictToPatch, ht]
theorem restrictToPatch_of_not_mem {f : F.Site 0 → ℝ} {t : F.Site 0} (ht : t ∉ patchSiteSet S z) :
    restrictToPatch S z f t = 0 := by
  classical
  simp [restrictToPatch, ht]
theorem le_neighbourSum_self {f : F.Site 0 → ℝ} (hf : ∀ t, 0 ≤ f t) {t : F.Site 0} (ht : t ∈ patchSiteSet S z) :
    f t ≤ neighbourSum S z f t := by
  rw [neighbourSum, restrictToPatch_of_mem ht]
  have := Finset.sum_nonneg (s := (Finset.univ : Finset PathStep)) fun st _ => hf (t + stepDisplacement 0 st)
  linarith
theorem le_neighbourSum_step {f : F.Site 0 → ℝ} (hf : ∀ t, 0 ≤ f t) {t : F.Site 0} (ht : t ∈ patchSiteSet S z)
    (st : PathStep) : f (t + stepDisplacement 0 st) ≤ neighbourSum S z f t := by
  rw [neighbourSum, restrictToPatch_of_mem ht]
  have h1 : f (t + stepDisplacement 0 st) ≤ ∑ st : PathStep, f (t + stepDisplacement 0 st) :=
    Finset.single_le_sum (f := fun st : PathStep => f (t + stepDisplacement 0 st)) (fun _ _ => hf _)
      (Finset.mem_univ st)
  have h0 := hf t
  linarith
theorem le_neighbourSum_of_bond {f : F.Site 0 → ℝ} (hf : ∀ t, 0 ≤ f t)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {a : Lattice4} {i : Fin 4} (ha : a ∈ patchDomain S z) (ha' : a + basisVector i ∈ patchDomain S z) :
    f (patchSite S z (a + basisVector i)) ≤ neighbourSum S z f (patchSite S z a) ∧
      f (patchSite S z a) ≤ neighbourSum S z f (patchSite S z (a + basisVector i)) := by
  have hs : patchSite S z a ∈ patchSiteSet S z := Finset.mem_image_of_mem _ ha
  have hs' : patchSite S z (a + basisVector i) ∈ patchSiteSet S z := Finset.mem_image_of_mem _ ha'
  obtain ⟨k1, k2⟩ := patchSite_add_basisVector he a i
  have hpos : ∀ t : F.Site 0, t + stepDisplacement 0 (i, true) = t + unitStep 0 i := fun t => by
    simp [stepDisplacement]
  have hneg : ∀ t : F.Site 0, (t + unitStep 0 i) + stepDisplacement 0 (i, false) = t := fun t => by
    simp [stepDisplacement]
  rcases he i with h | h
  · have e := k1 h
    constructor
    · rw [e, ← hpos]
      exact le_neighbourSum_step hf hs _
    · have h1 := le_neighbourSum_step hf hs' (i, false) (f := f)
      have e2 : patchSite S z (a + basisVector i) + stepDisplacement 0 (i, false) = patchSite S z a := by
        rw [e, hneg]
      rwa [e2] at h1
  · have e := k2 h
    constructor
    · have h1 := le_neighbourSum_step hf hs (i, false) (f := f)
      have e2 : patchSite S z a + stepDisplacement 0 (i, false) = patchSite S z (a + basisVector i) := by
        conv_lhs => rw [e]
        exact hneg _
      rwa [e2] at h1
    · rw [e, ← hpos]
      exact le_neighbourSum_step hf hs' _
theorem cellSeminorm_eq_zero_of_vanish {M : (F.Site 0 → ℝ) → F.Cell → ℝ} (hM : IsCellSeminorm S M)
    {f : F.Site 0 → ℝ} {y : F.Cell} (h : ∀ x ∈ cellSites S y, f x = 0) : M f y = 0 := by
  have h0 : M (fun _ => 0) y = 0 := by
    have := hM.smul 0 (fun _ => 0) y
    simpa using this
  refine le_antisymm ?_ (hM.nonneg f y)
  rw [← h0]
  exact hM.mono_abs _ _ _ fun x hx => by simp [h x hx]
theorem card_le_of_cellSupDist_le (hamb : IsAdmissibleAmbient F) (y1 : F.Cell) (r : ℕ) (A : Finset F.Cell)
    (hA : ∀ y ∈ A, cellSupDist y1 y ≤ r) : A.card ≤ (2 * r + 1) ^ 4 := by
  classical
  have hinj : Set.InjOn (cellDisplacement y1) (A : Set F.Cell) := by
    intro y _ y' _ h
    rw [eq_add_siteOfCoords_cellDisplacement y1 y, eq_add_siteOfCoords_cellDisplacement y1 y', h]
  rw [← Finset.card_image_of_injOn hinj]
  have hsub : A.image (cellDisplacement y1) ⊆ Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(r : ℤ)) r := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hv
    refine Fintype.mem_piFinset.2 fun i => ?_
    have h1 := natAbs_valMinAbs_le_cellSupDist y y1 i
    rw [cellSupDist_symm] at h1
    have h2 := h1.trans (hA y hy)
    have h3 : |cellDisplacement y1 y i| ≤ r := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h2
    exact Finset.mem_Icc.2 (abs_le.1 h3)
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
  congr 1
  omega
theorem sum_sum_cellBall_one_le (hamb : IsAdmissibleAmbient F) (A : F.Cell → ℝ) (hA : ∀ y, 0 ≤ A y)
    (B : Finset F.Cell) (hB : B ⊆ S) (hoff : ∀ y ∈ S, y ∉ B → A y = 0) :
    ∑ y ∈ B, ∑ y1 ∈ cellBall S y 1, A y1 ≤ 81 * ∑ y1 ∈ B, A y1 := by
  classical
  have h1 : ∀ y ∈ B, ∑ y1 ∈ cellBall S y 1, A y1 = ∑ y1 ∈ B, if cellSupDist y y1 ≤ 1 then A y1 else 0 := by
    intro y _
    rw [← Finset.sum_filter]
    have hsub : B.filter (fun y1 => cellSupDist y y1 ≤ 1) ⊆ cellBall S y 1 := by
      intro y1 h
      obtain ⟨h2, h3⟩ := Finset.mem_filter.1 h
      exact Finset.mem_filter.2 ⟨hB h2, h3⟩
    refine (Finset.sum_subset hsub fun y1 hy1 hn => ?_).symm
    obtain ⟨h2, h3⟩ := Finset.mem_filter.1 hy1
    refine hoff y1 h2 fun h4 => hn (Finset.mem_filter.2 ⟨h4, h3⟩)
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun y1 _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hA y1)
  have := card_le_of_cellSupDist_le hamb y1 1 (B.filter fun y => cellSupDist y y1 ≤ 1) (fun y hy => by
    rw [cellSupDist_symm]
    exact (Finset.mem_filter.1 hy).2)
  have h3 : ((B.filter fun y => cellSupDist y y1 ≤ 1).card : ℝ) ≤ ((2 * 1 + 1) ^ 4 : ℕ) := by exact_mod_cast this
  norm_num at h3 ⊢
  exact h3
theorem card_pathStep : Fintype.card PathStep = 8 := by
  simp [PathStep]
theorem sum_cellBall_neighbourSum_le {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hN : CellNormFamily S Md Lf Sr σ K) (hamb : IsAdmissibleAmbient F) (hP : patchSiteSet S z ⊆ sitesOfCells S 0)
    (hcell : ∀ y ∈ S, y ∉ cellBall S z 20 → ∀ x ∈ cellSites S y, x ∉ patchSiteSet S z)
    {f : F.Site 0 → ℝ} (hf : ∀ t, t ∉ patchSiteSet S z → f t = 0) :
    ∑ y ∈ cellBall S z 20, Md (neighbourSum S z f) y ≤ (1 + 8 * K * 81) * ∑ y ∈ cellBall S z 20, Md f y := by
  classical
  have hoffS : ∀ x, x ∉ sitesOfCells S 0 → f x = 0 := fun x hx => hf x fun h => hx (hP h)
  have hstep : ∀ y, Md (neighbourSum S z f) y ≤ Md f y + 8 * (K * ∑ y1 ∈ cellBall S y 1, Md f y1) := by
    intro y
    have h1 : Md (neighbourSum S z f) y ≤ Md (fun t => f t + ∑ st : PathStep, f (t + stepDisplacement 0 st)) y := by
      refine hN.isSeminorm_base.mono_abs _ _ _ fun x _ => ?_
      by_cases hx : x ∈ patchSiteSet S z
      · rw [neighbourSum, restrictToPatch_of_mem hx]
      · rw [neighbourSum, restrictToPatch_of_not_mem hx]
        simp
    refine h1.trans ((hN.isSeminorm_base.add_le _ _ y).trans ?_)
    have h2 := hN.isSeminorm_base.sum_le Finset.univ (fun (st : PathStep) x => f (x + stepDisplacement 0 st)) y
    have h3 : ∑ st : PathStep, Md (fun x => f (x + stepDisplacement 0 st)) y ≤
        ∑ _st : PathStep, K * ∑ y1 ∈ cellBall S y 1, Md f y1 :=
      Finset.sum_le_sum fun st _ => hN.base_shift_le st f y hoffS
    rw [Finset.sum_const, Finset.card_univ, card_pathStep] at h3
    simp only [nsmul_eq_mul] at h3
    push_cast at h3
    linarith
  have hB : cellBall S z 20 ⊆ S := Finset.filter_subset _ _
  have hd := sum_sum_cellBall_one_le hamb (fun y => Md f y) (fun y => hN.isSeminorm_base.nonneg f y)
    (cellBall S z 20) hB
    (fun y hy hn => cellSeminorm_eq_zero_of_vanish hN.isSeminorm_base fun x hx => hf x (hcell y hy hn x hx))
  calc _ ≤ ∑ y ∈ cellBall S z 20, (Md f y + 8 * (K * ∑ y1 ∈ cellBall S y 1, Md f y1)) :=
        Finset.sum_le_sum fun y _ => hstep y
    _ = ∑ y ∈ cellBall S z 20, Md f y + 8 * K * ∑ y ∈ cellBall S z 20, ∑ y1 ∈ cellBall S y 1, Md f y1 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
    _ ≤ ∑ y ∈ cellBall S z 20, Md f y + 8 * K * (81 * ∑ y ∈ cellBall S z 20, Md f y) := by
        have := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 8 * K)
        linarith
    _ = _ := by ring
end Totals
section Means
variable {F : BlockFrame}
theorem card_cellOffsets_eq (hL : 0 < F.blockSide) :
    ((cellOffsets F).card : ℝ) = (cellSideLength F : ℝ) ^ 4 := by
  have hN := cellSideLength_pos (F := F) hL
  have : (cellOffsets F).card = (cellSideLength F).toNat ^ 4 := by
    simp [cellOffsets, Fintype.card_piFinset]
  rw [this]
  push_cast
  have e : (((cellSideLength F).toNat : ℕ) : ℝ) = (cellSideLength F : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hN.le
  rw [e]
def cellMean (F : BlockFrame) (g : Lattice4 → ℍ[ℝ]) : ℍ[ℝ] :=
  (1 / (cellSideLength F : ℝ) ^ 4) • ∑ x ∈ cellOffsets F, g x
theorem cellMean_const (hL : 0 < F.blockSide) (c : ℍ[ℝ]) : cellMean F (fun _ => c) = c := by
  have hN : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
  simp only [cellMean, Finset.sum_const]
  rw [← Nat.cast_smul_eq_nsmul ℝ, card_cellOffsets_eq hL, smul_smul]
  have : 1 / (cellSideLength F : ℝ) ^ 4 * (cellSideLength F : ℝ) ^ 4 = 1 := by field_simp
  rw [this, one_smul]
theorem cellMean_add (g g' : Lattice4 → ℍ[ℝ]) :
    cellMean F (fun x => g x + g' x) = cellMean F g + cellMean F g' := by
  simp only [cellMean, Finset.sum_add_distrib, smul_add]
theorem cellMean_neg (g : Lattice4 → ℍ[ℝ]) : cellMean F (fun x => - g x) = - cellMean F g := by
  simp only [cellMean, Finset.sum_neg_distrib, smul_neg]
theorem cellMean_congr {g g' : Lattice4 → ℍ[ℝ]} (h : ∀ x ∈ cellOffsets F, g x = g' x) :
    cellMean F g = cellMean F g' := by
  simp only [cellMean]
  rw [Finset.sum_congr rfl h]
theorem norm_cellMean_le (hL : 0 < F.blockSide) (g : Lattice4 → ℍ[ℝ]) (b : Lattice4 → ℝ)
    (h : ∀ x ∈ cellOffsets F, ‖g x‖ ≤ b x) :
    ‖cellMean F g‖ ≤ (1 / (cellSideLength F : ℝ) ^ 4) * ∑ x ∈ cellOffsets F, b x := by
  have hN : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
  simp only [cellMean]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum h)) (by positivity)
end Means
section Rest
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
  {R : Lattice4 → Lattice4 → UnitQuaternion} {Cs r : ℝ}
structure PatchPathKernels (S : Finset F.Cell) (z : F.Cell) (H : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ)
    (G : Lattice4 → Lattice4 × Fin 4 → ℝ) (Ch : ℝ) : Prop where
  abs_plaquetteKernel_le : ∀ b p, |H b p| ≤ Ch * cubicKernel (b.1 - p.1)
  abs_bondKernel_le : ∀ x b, |G x b| ≤ Ch * cubicKernel (x - b.1)
  randomPathMean_eq_sum : ∀ (w : Lattice4 → Fin 4 → ℍ[ℝ]), ∀ x ∈ patchDomain S z,
    randomPathMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) w x =
      ∑ b ∈ bondsOf (patchDomain S z), G x b • w b.1 b.2
  add_randomPathMean_sub_eq_sum : ∀ (w : Lattice4 → Fin 4 → ℍ[ℝ]) (x : Lattice4) (i : Fin 4),
    x ∈ patchDomain S z → x + basisVector i ∈ patchDomain S z →
    w x i + (randomPathMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) w (x + basisVector i) -
      randomPathMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) w x) =
      ∑ p ∈ orientedPlaquettesOf (patchDomain S z), H (x, i) p • plaquetteCurl w p.1 p.2.1 p.2.2
  sub_endpointMean_eq : ∀ (φ : Lattice4 → ℍ[ℝ]), ∀ x ∈ patchDomain S z,
    φ x - endpointMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) φ =
      - randomPathMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (latticeDifference φ) x
def remainderMean (R : Lattice4 → Lattice4 → UnitQuaternion) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (z : F.Cell) (ξ : F.Site 0 → ℍ[ℝ]) : Lattice4 → ℍ[ℝ] :=
  randomPathMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (remainderForm R S V z ξ)
open Classical in
def stepNorms (S : Finset F.Cell) (z : F.Cell) (η : Lattice4 → ℍ[ℝ]) : F.Site 0 → ℝ :=
  fun t => if t ∈ patchSiteSet S z then
    ∑ i, if patchChart S z t + basisVector i ∈ patchDomain S z then
      ‖η (patchChart S z t + basisVector i) - η (patchChart S z t)‖ else 0 else 0
theorem stepNorms_nonneg (η : Lattice4 → ℍ[ℝ]) (t : F.Site 0) : 0 ≤ stepNorms S z η t := by
  classical
  simp only [stepNorms]
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => by split_ifs <;> simp
  · exact le_rfl
theorem stepNorms_patchSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (η : Lattice4 → ℍ[ℝ]) {a : Lattice4} (ha : a ∈ patchDomain S z) :
    stepNorms S z η (patchSite S z a) =
      ∑ i, if a + basisVector i ∈ patchDomain S z then ‖η (a + basisVector i) - η a‖ else 0 := by
  classical
  have hs : patchSite S z a ∈ patchSiteSet S z := Finset.mem_image_of_mem _ ha
  simp only [stepNorms, if_pos hs, patchChart_patchSite hamb hodd he (patchDomain_coord_bounds ha)]
theorem localPotential_eq {H G Ch} (hk : PatchPathKernels S z H G Ch) (hF : IsPatchFrame S V z R Cs r)
    (hr1 : 1 ≤ r * cellSideLength F) (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (ξ : F.Site 0 → ℍ[ℝ]) {a : Lattice4} (ha : a ∈ patchDomain S z) :
    localPotential S V (referenceFieldChain S V 0) z (covariantDiff (referenceFieldChain S V 0) ξ) a =
      endpointMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (localSection S V z ξ) -
        localSection S V z ξ a + remainderMean R S V z ξ a := by
  classical
  have h3 := hk.sub_endpointMean_eq (localSection S V z ξ) a ha
  have hd : randomPathMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F)
        (latticeDifference (localSection S V z ξ)) a =
      endpointMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (localSection S V z ξ) -
        localSection S V z ξ a := by
    rw [sub_eq_iff_eq_add] at h3
    rw [h3]
    abel
  rw [← hd]
  simp only [localPotential, remainderMean]
  rw [hk.randomPathMean_eq_sum _ a ha, hk.randomPathMean_eq_sum _ a ha, hk.randomPathMean_eq_sum _ a ha,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
  have hb0 : b.1 ∈ patchDomain S z := (Finset.mem_product.1 hb1).1
  rw [localForm_eq_latticeDifference_add hF hr1 he ξ hb0 hb2, smul_add]
theorem localPotentialMean_eq {H G Ch} (hk : PatchPathKernels S z H G Ch) (hF : IsPatchFrame S V z R Cs r)
    (hr1 : 1 ≤ r * cellSideLength F) (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (hL : 0 < F.blockSide) (hz : z ∈ S) (ξ : F.Site 0 → ℍ[ℝ]) (hξ : CellMeanFree S V ξ) :
    localPotentialMean S V (referenceFieldChain S V 0) z (covariantDiff (referenceFieldChain S V 0) ξ) =
      endpointMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (localSection S V z ξ) +
        cellMean F (remainderMean R S V z ξ) := by
  have h0 : cellMean F (localSection S V z ξ) = 0 := hξ z hz
  have h1 : localPotentialMean S V (referenceFieldChain S V 0) z (covariantDiff (referenceFieldChain S V 0) ξ) =
      cellMean F (fun x =>
        endpointMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (localSection S V z ξ) +
          ((- localSection S V z ξ x) + remainderMean R S V z ξ x)) := by
    refine cellMean_congr fun x hx => ?_
    rw [localPotential_eq hk hF hr1 he ξ (mem_patchDomain_of_mem_cellOffsets hz hL hx)]
    abel
  rw [h1, cellMean_add, cellMean_const hL, cellMean_add, cellMean_neg, h0]
  simp
end Rest
section Sizes
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
  {R : Lattice4 → Lattice4 → UnitQuaternion} {Cs r : ℝ}
theorem cubicKernel_nonneg_apply (v : Lattice4) : 0 ≤ cubicKernel v := by
  unfold cubicKernel
  positivity
theorem sum_bondsOf {P : Finset Lattice4} (g : Lattice4 × Fin 4 → ℝ) :
    ∑ b ∈ bondsOf P, g b = ∑ y ∈ P, ∑ i, if y + basisVector i ∈ P then g (y, i) else 0 := by
  classical
  simp only [bondsOf]
  rw [Finset.sum_filter, Finset.sum_product]
theorem sum_orientedPlaquettesOf {P : Finset Lattice4} (g : Lattice4 × Fin 4 × Fin 4 → ℝ) :
    ∑ p ∈ orientedPlaquettesOf P, g p =
      ∑ y ∈ P, ∑ μ, ∑ ν, if (y, μ, ν) ∈ orientedPlaquettesOf P then g (y, μ, ν) else 0 := by
  classical
  have hsub : orientedPlaquettesOf P ⊆ P ×ˢ (Finset.univ ×ˢ Finset.univ) := Finset.filter_subset _ _
  calc ∑ p ∈ orientedPlaquettesOf P, g p =
        ∑ p ∈ orientedPlaquettesOf P, (if p ∈ orientedPlaquettesOf P then g p else 0) :=
        Finset.sum_congr rfl fun p hp => by simp [hp]
    _ = ∑ p ∈ P ×ˢ (Finset.univ ×ˢ Finset.univ), (if p ∈ orientedPlaquettesOf P then g p else 0) :=
        Finset.sum_subset hsub fun p _ hp => by simp [hp]
    _ = _ := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_product]
theorem norm_sub_endpointMean_le {H G Ch} (hk : PatchPathKernels S z H G Ch) (hCh : 0 ≤ Ch)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (η : Lattice4 → ℍ[ℝ]) {x : Lattice4}
    (hx : x ∈ patchDomain S z) :
    ‖η x - endpointMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) η‖ ≤
      Ch * patchCubicKernel S z (stepNorms S z η) (patchSite S z x) := by
  classical
  rw [hk.sub_endpointMean_eq η x hx, norm_neg, hk.randomPathMean_eq_sum _ x hx,
    patchCubicKernel_patchSite_eq hamb hodd he _ hx, Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ b ∈ bondsOf (patchDomain S z), ‖G x b • latticeDifference η b.1 b.2‖ ≤
      Ch * cubicKernel (x - b.1) * ‖η (b.1 + basisVector b.2) - η b.1‖ := by
    intro b _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hk.abs_bondKernel_le x b) (norm_nonneg _)
  refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
  rw [sum_bondsOf]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [stepNorms_patchSite hamb hodd he η hy, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · ring
  · simp
theorem norm_sub_cellMean_le {H G Ch} (hk : PatchPathKernels S z H G Ch) (hCh : 0 ≤ Ch)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (hz : z ∈ S) (η : Lattice4 → ℍ[ℝ])
    {a : Lattice4} (ha : a ∈ patchDomain S z) :
    ‖η a - cellMean F η‖ ≤ Ch * patchCubicKernel S z (stepNorms S z η) (patchSite S z a) +
      Ch * ((1 / (cellSideLength F : ℝ) ^ 4) *
        ∑ x ∈ cellOffsets F, patchCubicKernel S z (stepNorms S z η) (patchSite S z x)) := by
  have hL := hodd.pos
  set E := endpointMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) η with hE
  have e : η a - cellMean F η = (η a - E) - cellMean F (fun x => η x - E) := by
    have h1 : cellMean F (fun x => η x - E) = cellMean F η - E := by
      simp only [sub_eq_add_neg]
      rw [cellMean_add, cellMean_const hL]
    rw [h1]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add (norm_sub_endpointMean_le hk hCh hamb hodd he η ha) ?_)
  have h2 := norm_cellMean_le hL (fun x => η x - E)
    (fun x => Ch * patchCubicKernel S z (stepNorms S z η) (patchSite S z x))
    (fun x hx => norm_sub_endpointMean_le hk hCh hamb hodd he η (mem_patchDomain_of_mem_cellOffsets hz hL hx))
  refine h2.trans (le_of_eq ?_)
  rw [← Finset.mul_sum]
  ring
def curlNormAt (S : Finset F.Cell) (z : F.Cell) (w : Lattice4 → Fin 4 → ℍ[ℝ]) (y : Lattice4) : ℝ := by
  classical exact ∑ μ, ∑ ν, if (y, μ, ν) ∈ orientedPlaquettesOf (patchDomain S z) then ‖plaquetteCurl w y μ ν‖ else 0
theorem curlNormAt_nonneg (w : Lattice4 → Fin 4 → ℍ[ℝ]) (y : Lattice4) : 0 ≤ curlNormAt S z w y := by
  classical
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> simp
theorem norm_randomPathMean_step_le {H G Ch} (hk : PatchPathKernels S z H G Ch) (hCh : 0 ≤ Ch)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (w : Lattice4 → Fin 4 → ℍ[ℝ])
    {a : Lattice4} {i : Fin 4} (ha : a ∈ patchDomain S z) (ha' : a + basisVector i ∈ patchDomain S z) :
    ‖randomPathMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) w (a + basisVector i) -
        randomPathMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) w a‖ ≤
      ‖w a i‖ + Ch * patchCubicKernel S z
        (restrictToPatch S z fun t => curlNormAt S z w (patchChart S z t)) (patchSite S z a) := by
  classical
  have h2 := hk.add_randomPathMean_sub_eq_sum w a i ha ha'
  have e : randomPathMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) w (a + basisVector i) -
        randomPathMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) w a =
      (∑ p ∈ orientedPlaquettesOf (patchDomain S z), H (a, i) p • plaquetteCurl w p.1 p.2.1 p.2.2) - w a i := by
    rw [← h2]
    abel
  rw [e, add_comm]
  refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ p ∈ orientedPlaquettesOf (patchDomain S z), ‖H (a, i) p • plaquetteCurl w p.1 p.2.1 p.2.2‖ ≤
      Ch * cubicKernel (a - p.1) * ‖plaquetteCurl w p.1 p.2.1 p.2.2‖ := by
    intro p _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hk.abs_plaquetteKernel_le (a, i) p) (norm_nonneg _)
  refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
  rw [sum_orientedPlaquettesOf, patchCubicKernel_patchSite_eq hamb hodd he _ ha, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hs : patchSite S z y ∈ patchSiteSet S z := Finset.mem_image_of_mem _ hy
  rw [restrictToPatch_of_mem hs, patchChart_patchSite hamb hodd he (patchDomain_coord_bounds hy)]
  simp only [curlNormAt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  split_ifs
  · ring
  · simp
end Sizes
section Bound
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
  {R : Lattice4 → Lattice4 → UnitQuaternion} {Cs r : ℝ}
theorem norm_eq_restrictToPatch_sectionNormOn (hP : patchSiteSet S z ⊆ sitesOfCells S 0) (ξ : F.Site 0 → ℍ[ℝ])
    {t : F.Site 0} (ht : t ∈ patchSiteSet S z) : ‖ξ t‖ = restrictToPatch S z (sectionNormOn S ξ) t := by
  classical
  rw [restrictToPatch_of_mem ht]
  simp [sectionNormOn, hP ht]
theorem sectionNormOn_nonneg (ξ : F.Site 0 → ℍ[ℝ]) (t : F.Site 0) : 0 ≤ sectionNormOn S ξ t := by
  classical
  simp only [sectionNormOn]
  split_ifs <;> simp
theorem formNormOn_nonneg (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (t : F.Site 0) : 0 ≤ formNormOn S f t := by
  classical
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> simp
theorem curl_bound_nonneg {Cs N A B : ℝ} (hC : 0 ≤ Cs) (hN : 1 ≤ N) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) :
    0 ≤ 12 * Cs / N ^ 2 * A + 8 * Cs / N * B := by
  have : 0 < N := by linarith
  positivity
theorem curl_bound_arith {Cs N A B n1 n2 n3 n4 m1 m2 m3 m4 D1 D2 c : ℝ} (hC : 0 ≤ Cs) (hC1 : Cs ≤ 1) (hN : 1 ≤ N)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hb : c ≤ 2 * Cs / N ^ 2 * (n1 + n2) + 2 * Cs / N * (D1 + D2))
    (d1 : D1 ≤ m1 + m3 + 2 * Cs / N * n3) (d2 : D2 ≤ m2 + m4 + 2 * Cs / N * n4)
    (a1 : n1 ≤ A) (a2 : n2 ≤ A) (a3 : n3 ≤ A) (a4 : n4 ≤ A) (b1 : m1 ≤ B) (b2 : m2 ≤ B) (b3 : m3 ≤ B) (b4 : m4 ≤ B) :
    c ≤ 12 * Cs / N ^ 2 * A + 8 * Cs / N * B := by
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = Cs / N := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, l = Cs / N ^ 2 := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := hκ ▸ by positivity
  have hl0 : 0 ≤ l := hl ▸ by positivity
  have e1 : 2 * Cs / N = 2 * κ := by rw [hκ]; ring
  have e2 : 2 * Cs / N ^ 2 = 2 * l := by rw [hl]; ring
  have e3 : 12 * Cs / N ^ 2 = 12 * l := by rw [hl]; ring
  have e4 : 8 * Cs / N = 8 * κ := by rw [hκ]; ring
  rw [e1] at d1 d2
  rw [e1, e2] at hb
  rw [e3, e4]
  have hκκ : κ * κ ≤ l := by
    rw [hκ, hl, div_mul_div_comm, ← sq, ← sq]
    have h5 : Cs ^ 2 ≤ Cs := by nlinarith
    exact div_le_div_of_nonneg_right h5 (by positivity)
  have g1 : D1 ≤ 2 * B + 2 * κ * A := by
    have := mul_le_mul_of_nonneg_left a3 (by positivity : 0 ≤ 2 * κ)
    linarith
  have g2 : D2 ≤ 2 * B + 2 * κ * A := by
    have := mul_le_mul_of_nonneg_left a4 (by positivity : 0 ≤ 2 * κ)
    linarith
  have g3 : 2 * l * (n1 + n2) ≤ 2 * l * (2 * A) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have g4 : 2 * κ * (D1 + D2) ≤ 2 * κ * (2 * (2 * B + 2 * κ * A)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have g5 : κ * κ * A ≤ l * A := mul_le_mul_of_nonneg_right hκκ hA0
  have e5 : 2 * κ * (2 * (2 * B + 2 * κ * A)) = 8 * κ * B + 8 * (κ * κ * A) := by ring
  have e6 : 2 * l * (2 * A) = 4 * (l * A) := by ring
  have e7 : 12 * l * A = 12 * (l * A) := by ring
  rw [e5] at g4
  rw [e6] at g3
  rw [e7]
  linarith
theorem curlNormAt_remainderForm_le (hF : IsPatchFrame S V z R Cs r) (hr1 : 1 ≤ r * cellSideLength F)
    (hC : 0 ≤ Cs) (hC1 : Cs ≤ 1) (hN1 : (1 : ℝ) ≤ cellSideLength F)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (hP : patchSiteSet S z ⊆ sitesOfCells S 0)
    (ξ : F.Site 0 → ℍ[ℝ]) {y : Lattice4} (hy : y ∈ patchDomain S z) :
    curlNormAt S z (remainderForm R S V z ξ) y ≤
      192 * Cs / (cellSideLength F : ℝ) ^ 2 *
          neighbourSum S z (neighbourSum S z (restrictToPatch S z (sectionNormOn S ξ))) (patchSite S z y) +
        128 * Cs / (cellSideLength F : ℝ) *
          neighbourSum S z (neighbourSum S z
            (restrictToPatch S z (formNormOn S (covariantDiff (referenceFieldChain S V 0) ξ)))) (patchSite S z y) := by
  classical
  set nξ := restrictToPatch S z (sectionNormOn S ξ) with hnξ
  set nd := restrictToPatch S z (formNormOn S (covariantDiff (referenceFieldChain S V 0) ξ)) with hnd
  have hnξ0 : ∀ t, 0 ≤ nξ t := restrictToPatch_nonneg (sectionNormOn_nonneg ξ)
  have hnd0 : ∀ t, 0 ≤ nd t := restrictToPatch_nonneg (formNormOn_nonneg _)
  have hnb1 : ∀ t, 0 ≤ neighbourSum S z nξ t := neighbourSum_nonneg hnξ0
  have hnb2 : ∀ t, 0 ≤ neighbourSum S z nd t := neighbourSum_nonneg hnd0
  obtain ⟨A, hAd⟩ : ∃ A, A = neighbourSum S z (neighbourSum S z nξ) (patchSite S z y) := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = neighbourSum S z (neighbourSum S z nd) (patchSite S z y) := ⟨_, rfl⟩
  rw [← hAd, ← hBd]
  have hA0 : 0 ≤ A := hAd ▸ neighbourSum_nonneg hnb1 _
  have hB0 : 0 ≤ B := hBd ▸ neighbourSum_nonneg hnb2 _
  have hys : patchSite S z y ∈ patchSiteSet S z := Finset.mem_image_of_mem _ hy
  have one_step : ∀ {f : F.Site 0 → ℝ} (_ : ∀ t, 0 ≤ f t) (μ : Fin 4), y + basisVector μ ∈ patchDomain S z →
      f (patchSite S z (y + basisVector μ)) ≤ neighbourSum S z (neighbourSum S z f) (patchSite S z y) := by
    intro f hf μ h1
    exact ((le_neighbourSum_of_bond hf he hy h1).1).trans (le_neighbourSum_self (neighbourSum_nonneg hf) hys)
  have two_step : ∀ {f : F.Site 0 → ℝ} (_ : ∀ t, 0 ≤ f t) (μ ν : Fin 4), y + basisVector μ ∈ patchDomain S z →
      y + basisVector μ + basisVector ν ∈ patchDomain S z →
      f (patchSite S z (y + basisVector μ + basisVector ν)) ≤
        neighbourSum S z (neighbourSum S z f) (patchSite S z y) := by
    intro f hf μ ν h1 h2
    exact ((le_neighbourSum_of_bond hf he h1 h2).1).trans
      ((le_neighbourSum_of_bond (neighbourSum_nonneg hf) he hy h1).1)
  have hterm : ∀ μ ν, (if (y, μ, ν) ∈ orientedPlaquettesOf (patchDomain S z) then
      ‖plaquetteCurl (remainderForm R S V z ξ) y μ ν‖ else 0) ≤
      12 * Cs / (cellSideLength F : ℝ) ^ 2 * A + 8 * Cs / (cellSideLength F : ℝ) * B := by
    intro μ ν
    have hbound0 : 0 ≤ 12 * Cs / (cellSideLength F : ℝ) ^ 2 * A + 8 * Cs / (cellSideLength F : ℝ) * B :=
      curl_bound_nonneg hC hN1 hA0 hB0
    split_ifs with hp
    · obtain ⟨-, -, h1, h2, h3⟩ := Finset.mem_filter.1 hp
      have h3' : y + basisVector ν + basisVector μ ∈ patchDomain S z := by rwa [add_right_comm]
      have hb := norm_plaquetteCurl_remainderForm_le hF hr1 hC ξ hy h1 h2 h3
      have sz : ∀ {q : Lattice4}, q ∈ patchDomain S z → ‖ξ (patchSite S z q)‖ = nξ (patchSite S z q) := fun hq =>
        norm_eq_restrictToPatch_sectionNormOn hP ξ (Finset.mem_image_of_mem _ hq)
      have fz : ∀ {q : Lattice4}, q ∈ patchDomain S z →
          formNormOn S (covariantDiff (referenceFieldChain S V 0) ξ) (patchSite S z q) = nd (patchSite S z q) :=
        fun hq => (restrictToPatch_of_mem (Finset.mem_image_of_mem _ hq)).symm
      have d1 := norm_latticeDifference_localSection_le hF hr1 hC he hP ξ h1 h3
      have d2 := norm_latticeDifference_localSection_le hF hr1 hC he hP ξ h2 h3'
      rw [fz h1, fz h3, sz h3] at d1
      rw [fz h2, fz h3', sz h3'] at d2
      rw [sz h1, sz h2] at hb
      have a1 : nξ (patchSite S z (y + basisVector μ)) ≤ A := hAd ▸ one_step hnξ0 μ h1
      have a2 : nξ (patchSite S z (y + basisVector ν)) ≤ A := hAd ▸ one_step hnξ0 ν h2
      have a3 : nξ (patchSite S z (y + basisVector μ + basisVector ν)) ≤ A := hAd ▸ two_step hnξ0 μ ν h1 h3
      have a4 : nξ (patchSite S z (y + basisVector ν + basisVector μ)) ≤ A := hAd ▸ two_step hnξ0 ν μ h2 h3'
      have b1 : nd (patchSite S z (y + basisVector μ)) ≤ B := hBd ▸ one_step hnd0 μ h1
      have b2 : nd (patchSite S z (y + basisVector ν)) ≤ B := hBd ▸ one_step hnd0 ν h2
      have b3 : nd (patchSite S z (y + basisVector μ + basisVector ν)) ≤ B := hBd ▸ two_step hnd0 μ ν h1 h3
      have b4 : nd (patchSite S z (y + basisVector ν + basisVector μ)) ≤ B := hBd ▸ two_step hnd0 ν μ h2 h3'
      exact curl_bound_arith hC hC1 hN1 hA0 hB0 hb d1 d2 a1 a2 a3 a4 b1 b2 b3 b4
    · exact hbound0
  have hsum : curlNormAt S z (remainderForm R S V z ξ) y ≤ ∑ _μ : Fin 4, ∑ _ν : Fin 4,
      (12 * Cs / (cellSideLength F : ℝ) ^ 2 * A + 8 * Cs / (cellSideLength F : ℝ) * B) :=
    Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν _ => hterm μ ν
  refine hsum.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring
end Bound
end PatchDifferences
end YangMills.Construction
end
