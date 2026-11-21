import YangMills.Construction.ColdChainAtEveryLevel.DifferencesInAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace PatchForms
open BlockAverages GaugeMap PatchPoints PatchFrames LatticeFractionalIntegration
section Algebra
theorem adjointAction_mul_apply (g h : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction (g * h) w = adjointAction g (adjointAction h w) := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_mul <;> assumption
theorem adjointAction_one_apply (w : ℍ[ℝ]) : adjointAction (1 : UnitQuaternion) w = w := by
  simp [adjointAction]
theorem adjointAction_inv_apply_apply (g : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction g⁻¹ (adjointAction g w) = w := by apply _root_.YangMills.Construction.CellBumps.adjointAction_inv_adjointAction <;> assumption
theorem adjointAction_apply_inv_apply (g : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction g (adjointAction g⁻¹ w) = w := by
  rw [← adjointAction_mul_apply, mul_inv_cancel, adjointAction_one_apply]
theorem adjointAction_apply_add (g : UnitQuaternion) (p q : ℍ[ℝ]) :
    adjointAction g (p + q) = adjointAction g p + adjointAction g q := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_add <;> assumption
theorem adjointAction_apply_sub (g : UnitQuaternion) (p q : ℍ[ℝ]) :
    adjointAction g (p - q) = adjointAction g p - adjointAction g q := by apply _root_.YangMills.Construction.BlockLines.adjointAction_sub <;> assumption
theorem adjointAction_apply_neg (g : UnitQuaternion) (p : ℍ[ℝ]) :
    adjointAction g (-p) = - adjointAction g p := by
  simp only [adjointAction, mul_neg, neg_mul]
theorem adjointAction_apply_smul (g : UnitQuaternion) (c : ℝ) (p : ℍ[ℝ]) :
    adjointAction g (c • p) = c • adjointAction g p := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_smul <;> assumption
theorem adjointAction_apply_zero (g : UnitQuaternion) : adjointAction g 0 = 0 := by
  simp [adjointAction]
theorem adjointAction_apply_sum {ι : Type} (g : UnitQuaternion) (t : Finset ι) (f : ι → ℍ[ℝ]) :
    adjointAction g (∑ i ∈ t, f i) = ∑ i ∈ t, adjointAction g (f i) := by
  simp only [adjointAction, Finset.mul_sum, Finset.sum_mul]
theorem norm_adjointAction_apply (g : UnitQuaternion) (w : ℍ[ℝ]) : ‖adjointAction g w‖ = ‖w‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction <;> assumption
theorem norm_adjointAction_apply_sub_le (g : UnitQuaternion) (q : ℍ[ℝ]) :
    ‖adjointAction g q - q‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ * ‖q‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction_sub_le <;> assumption
theorem norm_adjointAction_sub_adjointAction_apply_le (g h : UnitQuaternion) (q : ℍ[ℝ]) :
    ‖adjointAction g q - adjointAction h q‖ ≤ 2 * ‖(g : ℍ[ℝ]) - (h : ℍ[ℝ])‖ * ‖q‖ := by apply _root_.YangMills.Construction.PatchDifferences.norm_adjointAction_sub_adjointAction_le <;> assumption
theorem norm_conjugatedLoop_sub_le (T1 T2 T3 T4 : UnitQuaternion) (q1 q2 q3 q4 : ℍ[ℝ]) {κ : ℝ}
    (h1 : ‖(T1 : ℍ[ℝ]) - 1‖ ≤ κ) (h2 : ‖(T2 : ℍ[ℝ]) - 1‖ ≤ κ)
    (h3 : ‖(T3 : ℍ[ℝ]) - 1‖ ≤ κ) (h4 : ‖(T4 : ℍ[ℝ]) - 1‖ ≤ κ) :
    ‖(q1 + adjointAction T1 q2 - adjointAction (T1 * T2 * T3⁻¹) q3 -
        adjointAction (T1 * T2 * T3⁻¹ * T4⁻¹) q4) - (q1 + q2 - q3 - q4)‖ ≤
      κ * (2 * ‖q2‖ + 6 * ‖q3‖ + 8 * ‖q4‖) := by
  have a1 : ‖((T1 * T2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ κ + κ :=
    (norm_coe_mul_sub_one_le _ _).trans (add_le_add h1 h2)
  have a2 : ‖((T1 * T2 * T3⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ κ + κ + κ := by
    refine (norm_coe_mul_sub_one_le _ _).trans (add_le_add a1 ?_)
    rwa [norm_coe_inv_sub_one]
  have a3 : ‖((T1 * T2 * T3⁻¹ * T4⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ κ + κ + κ + κ := by
    refine (norm_coe_mul_sub_one_le _ _).trans (add_le_add a2 ?_)
    rwa [norm_coe_inv_sub_one]
  have b1 := norm_adjointAction_apply_sub_le T1 q2
  have b2 := norm_adjointAction_apply_sub_le (T1 * T2 * T3⁻¹) q3
  have b3 := norm_adjointAction_apply_sub_le (T1 * T2 * T3⁻¹ * T4⁻¹) q4
  have c1 : 2 * ‖(T1 : ℍ[ℝ]) - 1‖ * ‖q2‖ ≤ 2 * κ * ‖q2‖ :=
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have c2 : 2 * ‖((T1 * T2 * T3⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ * ‖q3‖ ≤ 6 * κ * ‖q3‖ :=
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have c3 : 2 * ‖((T1 * T2 * T3⁻¹ * T4⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ * ‖q4‖ ≤ 8 * κ * ‖q4‖ :=
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have e : (q1 + adjointAction T1 q2 - adjointAction (T1 * T2 * T3⁻¹) q3 -
      adjointAction (T1 * T2 * T3⁻¹ * T4⁻¹) q4) - (q1 + q2 - q3 - q4) =
      (adjointAction T1 q2 - q2) - (adjointAction (T1 * T2 * T3⁻¹) q3 - q3) -
        (adjointAction (T1 * T2 * T3⁻¹ * T4⁻¹) q4 - q4) := by
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have := norm_sub_le (adjointAction T1 q2 - q2) (adjointAction (T1 * T2 * T3⁻¹) q3 - q3)
  nlinarith
end Algebra
section Lines
variable {F : BlockFrame} {S : Finset F.Cell}
theorem baseSite_depth_zero (x : F.Site 0) : baseSite x = x := by apply _root_.YangMills.Construction.CellBumps.baseSite_zero <;> assumption
theorem referenceFieldChain_zero_eq (V : F.GaugeField F.top) (x : F.Site 0) (i : Fin 4) :
    referenceFieldChain S V 0 x i = leadingTransport S V x (x + unitStep 0 i) := by apply _root_.YangMills.Construction.PatchDifferences.referenceFieldChain_zero_apply <;> assumption
end Lines
section Chart
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
theorem patchSite_add_basisVector_cases (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (a : Lattice4) (i : Fin 4) :
    (closedOrthant S z i = 1 → patchSite S z (a + basisVector i) = patchSite S z a + unitStep 0 i) ∧
      (closedOrthant S z i = -1 → patchSite S z a = patchSite S z (a + basisVector i) + unitStep 0 i) := by apply _root_.YangMills.Construction.PatchDifferences.patchSite_add_basisVector <;> assumption
theorem supNorm_basisVector_eq_one (i : Fin 4) : supNorm (basisVector i) = 1 := by apply _root_.YangMills.Construction.LatticePaths.supNorm_basisVector <;> assumption
theorem supNorm_add_basisVector_sub_self (a : Lattice4) (i : Fin 4) :
    supNorm (a + basisVector i - a) = 1 := by apply _root_.YangMills.Construction.PatchDifferences.supNorm_add_basisVector_sub <;> assumption
theorem supNorm_sub_add_basisVector (a : Lattice4) (i : Fin 4) :
    supNorm (a - (a + basisVector i)) = 1 := by
  have e : a - (a + basisVector i) = - basisVector i := by abel
  rw [e]
  have h2 : supNorm (- basisVector i) = supNorm (basisVector i) := by
    simp only [supNorm, Pi.neg_apply, Int.natAbs_neg]
  rw [h2]
  exact supNorm_basisVector_eq_one i
theorem localForm_of_sign_pos {R : F.GaugeField 0} {f : F.Site 0 → Fin 4 → ℍ[ℝ]} {i : Fin 4}
    (h : closedOrthant S z i = 1) (a : Lattice4) :
    localForm S V R z f a i =
      adjointAction (frameChange S V z (patchSite S z a))⁻¹ (f (patchSite S z a) i) := by
  simp only [localForm, if_pos h]
theorem localForm_of_sign_neg {R : F.GaugeField 0} {f : F.Site 0 → Fin 4 → ℍ[ℝ]} {i : Fin 4}
    (h : closedOrthant S z i = -1) (a : Lattice4) :
    localForm S V R z f a i = adjointAction (frameChange S V z (patchSite S z a))⁻¹
      (- adjointAction (R (patchSite S z (a + basisVector i)) i)⁻¹
        (f (patchSite S z (a + basisVector i)) i)) := by
  have hne : closedOrthant S z i ≠ 1 := by rw [h]; norm_num
  simp only [localForm, if_neg hne]
theorem localForm_apply_add_fun (R : F.GaugeField 0) (f g : F.Site 0 → Fin 4 → ℍ[ℝ]) (a : Lattice4)
    (i : Fin 4) :
    localForm S V R z (fun t k => f t k + g t k) a i = localForm S V R z f a i + localForm S V R z g a i := by
  simp only [localForm]
  split_ifs
  · rw [adjointAction_apply_add]
  · simp only [adjointAction_apply_add, adjointAction_apply_neg]
    abel
theorem exists_bond_in_patchChart (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {t : F.Site 0} {i : Fin 4} (ht : t ∈ patchSiteSet S z) (ht' : t + unitStep 0 i ∈ patchSiteSet S z) :
    ∃ a, a ∈ patchDomain S z ∧ a + basisVector i ∈ patchDomain S z ∧
      ((closedOrthant S z i = 1 ∧ patchSite S z a = t ∧
          patchSite S z (a + basisVector i) = t + unitStep 0 i) ∨
        (closedOrthant S z i = -1 ∧ patchSite S z a = t + unitStep 0 i ∧
          patchSite S z (a + basisVector i) = t)) := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
  obtain ⟨b, hb, eb⟩ := Finset.mem_image.1 ht'
  obtain ⟨k1, k2⟩ := patchSite_add_basisVector_cases he a i
  have hra := patchDomain_coord_bounds ha
  have hrb := patchDomain_coord_bounds hb
  have ca : patchChart S z (patchSite S z a) = a := patchChart_patchSite hamb hodd he hra
  have cb : patchChart S z (patchSite S z b) = b := patchChart_patchSite hamb hodd he hrb
  have hst : stepDisplacement (F := F) 0 ((i, true) : PathStep) = unitStep 0 i := by
    simp [stepDisplacement]
  have cs := BondShares.patchChart_add_stepDisplacement hamb hodd he (s := patchSite S z a) (i, true)
    (by rw [ca]; exact hra)
  rw [hst, ← eb, cb, ca] at cs
  have ho : BondShares.stepOffset ((i, true) : PathStep) = basisVector i := by
    simp [BondShares.stepOffset]
  rw [ho] at cs
  rcases he i with h | h
  · have e1 : b = a + basisVector i := by
      rw [cs]
      funext k
      simp only [Pi.add_apply]
      by_cases hk : k = i
      · subst hk; rw [h, one_mul]
      · simp [basisVector, hk]
    refine ⟨a, ha, e1 ▸ hb, Or.inl ⟨h, rfl, ?_⟩⟩
    rw [← e1, eb]
  · have e1 : a = b + basisVector i := by
      rw [cs]
      funext k
      simp only [Pi.add_apply]
      by_cases hk : k = i
      · subst hk; rw [h]; ring
      · simp [basisVector, hk]
    refine ⟨b, hb, e1 ▸ ha, Or.inr ⟨h, eb, ?_⟩⟩
    rw [← e1]
variable {R : Lattice4 → Lattice4 → UnitQuaternion} {Cs r : ℝ}
theorem exists_leadingTransport_near_one (hF : IsPatchFrame S V z R Cs r) (hr1 : 1 ≤ r * cellSideLength F)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {t : F.Site 0} {i : Fin 4}
    (ht : t ∈ patchSiteSet S z) (ht' : t + unitStep 0 i ∈ patchSiteSet S z) :
    ∃ T : UnitQuaternion, ‖(T : ℍ[ℝ]) - 1‖ ≤ Cs / (cellSideLength F : ℝ) ∧
      leadingTransport S V t (t + unitStep 0 i) =
        frameChange S V z t * T * (frameChange S V z (t + unitStep 0 i))⁻¹ := by
  obtain ⟨a, ha, ha', hc⟩ := exists_bond_in_patchChart hamb hodd he ht ht'
  rcases hc with ⟨-, e1, e2⟩ | ⟨-, e1, e2⟩
  · refine ⟨R a (a + basisVector i), ?_, ?_⟩
    · have hn := hF.norm_sub_one_le a ha (a + basisVector i) ha'
        (by rw [supNorm_add_basisVector_sub_self]; simpa using hr1)
      rw [supNorm_add_basisVector_sub_self] at hn
      simpa [div_eq_mul_inv] using hn
    · have hl := hF.leadingTransport_eq a ha (a + basisVector i) ha'
        (by rw [supNorm_add_basisVector_sub_self]; simpa using hr1)
      rwa [e1, e2] at hl
  · refine ⟨R (a + basisVector i) a, ?_, ?_⟩
    · have hn := hF.norm_sub_one_le (a + basisVector i) ha' a ha
        (by rw [supNorm_sub_add_basisVector]; simpa using hr1)
      rw [supNorm_sub_add_basisVector] at hn
      simpa [div_eq_mul_inv] using hn
    · have hl := hF.leadingTransport_eq (a + basisVector i) ha' a ha
        (by rw [supNorm_sub_add_basisVector]; simpa using hr1)
      rwa [e1, e2] at hl
end Chart
section Curl
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
theorem norm_le_formNormOn (f : F.Site 0 → Fin 4 → ℍ[ℝ]) {t : F.Site 0} {k : Fin 4}
    (hb : (t, k) ∈ innerBonds S 0) :
    ‖f t k‖ ≤ PatchDifferences.formNormOn S f t := by
  classical
  have := Finset.single_le_sum (f := fun k => if (t, k) ∈ innerBonds S 0 then ‖f t k‖ else 0)
    (fun _ _ => by split_ifs <;> simp) (Finset.mem_univ k)
  simpa [PatchDifferences.formNormOn, hb] using this
theorem zero_le_formNormOn (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (t : F.Site 0) :
    0 ≤ PatchDifferences.formNormOn S f t := by apply _root_.YangMills.Construction.PatchDifferences.formNormOn_nonneg <;> assumption
theorem mem_innerBonds_of_step {t t' : F.Site 0} {k : Fin 4} (h1 : t ∈ sitesOfCells S 0)
    (h2 : t' ∈ sitesOfCells S 0) (e : t + unitStep 0 k = t') :
    (t, k) ∈ innerBonds S 0 :=
  Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h1, Finset.mem_univ _⟩, by rw [e]; exact h2⟩
def patchFrameForm (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) :
    F.Site 0 → Fin 4 → ℍ[ℝ] :=
  fun t i => adjointAction (frameChange S V z t)⁻¹ (f t i)
def flatCurl (g : F.Site 0 → Fin 4 → ℍ[ℝ]) (x : F.Site 0) (μ ν : Fin 4) : ℍ[ℝ] :=
  g x μ + g (x + unitStep 0 μ) ν - g (x + unitStep 0 ν) μ - g x ν
theorem norm_linearizedCurl_sub_flatCurl_le {R : Lattice4 → Lattice4 → UnitQuaternion} {Cs r : ℝ}
    (hF : IsPatchFrame S V z R Cs r) (hr1 : 1 ≤ r * cellSideLength F)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    {x : F.Site 0} {μ ν : Fin 4} (h0 : x ∈ patchSiteSet S z) (h1 : x + unitStep 0 μ ∈ patchSiteSet S z)
    (h2 : x + unitStep 0 ν ∈ patchSiteSet S z) (h3 : x + unitStep 0 μ + unitStep 0 ν ∈ patchSiteSet S z) :
    ‖adjointAction (frameChange S V z x)⁻¹ (linearizedCurl (referenceFieldChain S V 0) u (x, μ, ν)) -
        flatCurl (patchFrameForm S V z fun t k => (u t k : ℍ[ℝ])) x μ ν‖ ≤
      Cs / (cellSideLength F : ℝ) * (2 * ‖(u (x + unitStep 0 μ) ν : ℍ[ℝ])‖ +
        6 * ‖(u (x + unitStep 0 ν) μ : ℍ[ℝ])‖ + 8 * ‖(u x ν : ℍ[ℝ])‖) := by
  have h3' : x + unitStep 0 ν + unitStep 0 μ ∈ patchSiteSet S z := by rwa [add_right_comm]
  obtain ⟨T1, n1, l1⟩ := exists_leadingTransport_near_one hF hr1 hamb hodd he h0 h1
  obtain ⟨T2, n2, l2⟩ := exists_leadingTransport_near_one hF hr1 hamb hodd he h1 h3
  obtain ⟨T3, n3, l3⟩ := exists_leadingTransport_near_one hF hr1 hamb hodd he h2 h3'
  obtain ⟨T4, n4, l4⟩ := exists_leadingTransport_near_one hF hr1 hamb hodd he h0 h2
  have hc : x + unitStep 0 ν + unitStep 0 μ = x + unitStep 0 μ + unitStep 0 ν := add_right_comm _ _ _
  rw [hc] at l3
  have key := norm_conjugatedLoop_sub_le T1 T2 T3 T4
    (adjointAction (frameChange S V z x)⁻¹ (u x μ : ℍ[ℝ]))
    (adjointAction (frameChange S V z (x + unitStep 0 μ))⁻¹ (u (x + unitStep 0 μ) ν : ℍ[ℝ]))
    (adjointAction (frameChange S V z (x + unitStep 0 ν))⁻¹ (u (x + unitStep 0 ν) μ : ℍ[ℝ]))
    (adjointAction (frameChange S V z x)⁻¹ (u x ν : ℍ[ℝ])) n1 n2 n3 n4
  simp only [norm_adjointAction_apply] at key
  refine le_trans (le_of_eq ?_) key
  congr 1
  simp only [linearizedCurl, flatCurl, patchFrameForm, referenceFieldChain_zero_eq]
  rw [hc, l1, l2, l3, l4]
  congr 1
  simp only [adjointAction_apply_sub, adjointAction_apply_add, ← adjointAction_mul_apply]
  have g1 : (frameChange S V z x)⁻¹ * (frameChange S V z x * T1 * (frameChange S V z (x + unitStep 0 μ))⁻¹) =
      T1 * (frameChange S V z (x + unitStep 0 μ))⁻¹ := by group
  have g2 : (frameChange S V z x)⁻¹ * (frameChange S V z x * T1 * (frameChange S V z (x + unitStep 0 μ))⁻¹ *
      (frameChange S V z (x + unitStep 0 μ) * T2 *
        (frameChange S V z (x + unitStep 0 μ + unitStep 0 ν))⁻¹) *
      (frameChange S V z (x + unitStep 0 ν) * T3 *
        (frameChange S V z (x + unitStep 0 μ + unitStep 0 ν))⁻¹)⁻¹) =
      T1 * T2 * T3⁻¹ * (frameChange S V z (x + unitStep 0 ν))⁻¹ := by group
  have g3 : (frameChange S V z x)⁻¹ * (frameChange S V z x * T1 * (frameChange S V z (x + unitStep 0 μ))⁻¹ *
      (frameChange S V z (x + unitStep 0 μ) * T2 *
        (frameChange S V z (x + unitStep 0 μ + unitStep 0 ν))⁻¹) *
      (frameChange S V z (x + unitStep 0 ν) * T3 *
        (frameChange S V z (x + unitStep 0 μ + unitStep 0 ν))⁻¹)⁻¹ *
      (frameChange S V z x * T4 * (frameChange S V z (x + unitStep 0 ν))⁻¹)⁻¹) =
      T1 * T2 * T3⁻¹ * T4⁻¹ * (frameChange S V z x)⁻¹ := by group
  rw [g1, g2, g3]
def signedChartForm (S : Finset F.Cell) (z : F.Cell) (g : F.Site 0 → Fin 4 → ℍ[ℝ]) (a : Lattice4)
    (i : Fin 4) : ℍ[ℝ] :=
  if closedOrthant S z i = 1 then g (patchSite S z a) i else - g (patchSite S z (a + basisVector i)) i
theorem norm_localForm_sub_signedChartForm_le {R : Lattice4 → Lattice4 → UnitQuaternion} {Cs r : ℝ}
    (hF : IsPatchFrame S V z R Cs r) (hr1 : 1 ≤ r * cellSideLength F)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (hC : 0 ≤ Cs)
    (hP : patchSiteSet S z ⊆ sitesOfCells S 0)
    (f : F.Site 0 → Fin 4 → ℍ[ℝ]) {a : Lattice4} {i : Fin 4} (ha : a ∈ patchDomain S z)
    (ha' : a + basisVector i ∈ patchDomain S z) :
    ‖localForm S V (referenceFieldChain S V 0) z f a i - signedChartForm S z (patchFrameForm S V z f) a i‖ ≤
      2 * (Cs / (cellSideLength F : ℝ)) *
        PatchDifferences.formNormOn S f (patchSite S z (a + basisVector i)) := by
  classical
  have hN : 0 ≤ 2 * (Cs / (cellSideLength F : ℝ)) *
      PatchDifferences.formNormOn S f (patchSite S z (a + basisVector i)) := by
    have : (0 : ℝ) ≤ cellSideLength F := by exact_mod_cast (cellSideLength_pos (F := F) hodd.pos).le
    have := zero_le_formNormOn (S := S) f (patchSite S z (a + basisVector i))
    positivity
  obtain ⟨k1, k2⟩ := patchSite_add_basisVector_cases he a i
  rcases he i with h | h
  · rw [localForm_of_sign_pos h, signedChartForm, if_pos h]
    simpa [patchFrameForm] using hN
  · have hne : closedOrthant S z i ≠ 1 := by rw [h]; norm_num
    have e := k2 h
    have hs : patchSite S z a ∈ patchSiteSet S z := Finset.mem_image_of_mem _ ha
    have hs' : patchSite S z (a + basisVector i) ∈ patchSiteSet S z := Finset.mem_image_of_mem _ ha'
    obtain ⟨T, hT, hl⟩ := exists_leadingTransport_near_one hF hr1 hamb hodd he hs' (e ▸ hs)
    rw [← e] at hl
    rw [localForm_of_sign_neg h, signedChartForm, if_neg hne, referenceFieldChain_zero_eq, ← e, hl]
    have e2 : adjointAction (frameChange S V z (patchSite S z a))⁻¹
        (- adjointAction (frameChange S V z (patchSite S z (a + basisVector i)) * T *
          (frameChange S V z (patchSite S z a))⁻¹)⁻¹ (f (patchSite S z (a + basisVector i)) i)) =
        - adjointAction T⁻¹ (patchFrameForm S V z f (patchSite S z (a + basisVector i)) i) := by
      rw [adjointAction_apply_neg, patchFrameForm, ← adjointAction_mul_apply, ← adjointAction_mul_apply]
      congr 2
      group
    rw [e2]
    have e3 : - adjointAction T⁻¹ (patchFrameForm S V z f (patchSite S z (a + basisVector i)) i) -
        - patchFrameForm S V z f (patchSite S z (a + basisVector i)) i =
        - (adjointAction T⁻¹ (patchFrameForm S V z f (patchSite S z (a + basisVector i)) i) -
          patchFrameForm S V z f (patchSite S z (a + basisVector i)) i) := by abel
    rw [e3, norm_neg]
    refine (norm_adjointAction_apply_sub_le _ _).trans ?_
    rw [norm_coe_inv_sub_one]
    simp only [patchFrameForm, norm_adjointAction_apply]
    have hb := norm_le_formNormOn (S := S) f (mem_innerBonds_of_step (hP hs') (hP hs) e.symm)
    have hk : 0 ≤ Cs / (cellSideLength F : ℝ) := le_trans (norm_nonneg _) hT
    calc _ ≤ 2 * (Cs / (cellSideLength F : ℝ)) * ‖f (patchSite S z (a + basisVector i)) i‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)
theorem exists_norm_plaquetteCurl_signedChartForm_eq
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (g : F.Site 0 → Fin 4 → ℍ[ℝ]) (y : Lattice4) (μ ν : Fin 4) :
    ∃ x A B D : F.Site 0,
      (∀ Q : F.Site 0 → Prop, Q (patchSite S z y) → Q (patchSite S z (y + basisVector μ)) →
        Q (patchSite S z (y + basisVector ν)) →
        Q (patchSite S z (y + basisVector μ + basisVector ν)) → Q x ∧ Q A ∧ Q B ∧ Q D) ∧
      A = x + unitStep 0 μ ∧ B = x + unitStep 0 ν ∧ D = x + unitStep 0 μ + unitStep 0 ν ∧
      ‖plaquetteCurl (signedChartForm S z g) y μ ν‖ = ‖flatCurl g x μ ν‖ := by
  obtain ⟨a1, a2⟩ := patchSite_add_basisVector_cases he y μ
  obtain ⟨b1, b2⟩ := patchSite_add_basisVector_cases he y ν
  obtain ⟨c1, c2⟩ := patchSite_add_basisVector_cases he (y + basisVector μ) ν
  obtain ⟨d1, d2⟩ := patchSite_add_basisVector_cases he (y + basisVector ν) μ
  have hcomm : y + basisVector ν + basisVector μ = y + basisVector μ + basisVector ν := add_right_comm _ _ _
  rw [hcomm] at d1 d2
  have hcurl : plaquetteCurl (signedChartForm S z g) y μ ν =
      signedChartForm S z g y μ + signedChartForm S z g (y + basisVector μ) ν -
      signedChartForm S z g (y + basisVector ν) μ - signedChartForm S z g y ν := rfl
  rcases he μ with hμ | hμ <;> rcases he ν with hν | hν
  · refine ⟨patchSite S z y, patchSite S z (y + basisVector μ), patchSite S z (y + basisVector ν),
      patchSite S z (y + basisVector μ + basisVector ν), fun Q q0 q1 q2 q3 => ⟨q0, q1, q2, q3⟩,
      a1 hμ, b1 hν, ?_, ?_⟩
    · rw [c1 hν, a1 hμ]
    · rw [hcurl]
      simp only [signedChartForm, flatCurl, if_pos hμ, if_pos hν]
      rw [a1 hμ, b1 hν]
  · have hne : closedOrthant S z ν ≠ 1 := by rw [hν]; norm_num
    have e1 := b2 hν
    have e2 := d1 hμ
    refine ⟨patchSite S z (y + basisVector ν), patchSite S z (y + basisVector μ + basisVector ν),
      patchSite S z y, patchSite S z (y + basisVector μ), fun Q q0 q1 q2 q3 => ⟨q2, q3, q0, q1⟩,
      e2, e1, ?_, ?_⟩
    · rw [c2 hν, e2]
    · have e : signedChartForm S z g y μ + signedChartForm S z g (y + basisVector μ) ν -
          signedChartForm S z g (y + basisVector ν) μ - signedChartForm S z g y ν =
          - flatCurl g (patchSite S z (y + basisVector ν)) μ ν := by
        simp only [signedChartForm, flatCurl, if_pos hμ, if_neg hne, ← e1, ← e2]
        abel
      rw [hcurl, e, norm_neg]
  · have hne : closedOrthant S z μ ≠ 1 := by rw [hμ]; norm_num
    have e1 := a2 hμ
    have e2 := c1 hν
    refine ⟨patchSite S z (y + basisVector μ), patchSite S z y,
      patchSite S z (y + basisVector μ + basisVector ν), patchSite S z (y + basisVector ν),
      fun Q q0 q1 q2 q3 => ⟨q1, q0, q3, q2⟩, e1, e2, ?_, ?_⟩
    · rw [← e1, b1 hν]
    · have e : signedChartForm S z g y μ + signedChartForm S z g (y + basisVector μ) ν -
          signedChartForm S z g (y + basisVector ν) μ - signedChartForm S z g y ν =
          - flatCurl g (patchSite S z (y + basisVector μ)) μ ν := by
        simp only [signedChartForm, flatCurl, if_pos hν, if_neg hne, ← e1, ← e2, hcomm]
        abel
      rw [hcurl, e, norm_neg]
  · have hne1 : closedOrthant S z μ ≠ 1 := by rw [hμ]; norm_num
    have hne2 : closedOrthant S z ν ≠ 1 := by rw [hν]; norm_num
    have e1 := c2 hν
    have e2 := d2 hμ
    refine ⟨patchSite S z (y + basisVector μ + basisVector ν), patchSite S z (y + basisVector ν),
      patchSite S z (y + basisVector μ), patchSite S z y, fun Q q0 q1 q2 q3 => ⟨q3, q2, q1, q0⟩,
      e2, e1, ?_, ?_⟩
    · rw [a2 hμ, e1, add_right_comm]
    · have e : signedChartForm S z g y μ + signedChartForm S z g (y + basisVector μ) ν -
          signedChartForm S z g (y + basisVector ν) μ - signedChartForm S z g y ν =
          flatCurl g (patchSite S z (y + basisVector μ + basisVector ν)) μ ν := by
        simp only [signedChartForm, flatCurl, if_neg hne1, if_neg hne2, ← e1, ← e2, hcomm]
        abel
      rw [hcurl, e]
end Curl
end PatchForms
end YangMills.Construction
end
