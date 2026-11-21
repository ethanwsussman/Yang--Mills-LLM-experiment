import YangMills.Construction.Lattice.AveragingMapIsABorelMapProof
import YangMills.Construction.Lattice.BoxesOfSitesFromACorner
import YangMills.Construction.Lattice.CombGaugeOfABox
import YangMills.Construction.Lattice.CombGaugeRoundACoarsePlaquette
import YangMills.Construction.Lattice.ElementaryBoundsOfOneStep
import YangMills.Construction.Lattice.GaugeCovarianceOfTheTwoSchemes
import YangMills.Construction.Lattice.GaugeSizeAnglesAndBlockMean
import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import YangMills.Construction.Lattice.SchemeAverageDependsOnTheDoubleBlockAlone
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
namespace CoarsePlaquetteGauge
variable {L m K n : ℕ} {j : ℤ}
theorem det_isUnit_of_mem_specialUnitary {A : ComplexMatrix2}
    (h : A ∈ ComplexMatrix2.specialUnitary) : IsUnit A.det := by
  rw [(Matrix.mem_specialUnitaryGroup_iff.mp h).2]
  exact isUnit_one
theorem inv_mul_cancel_of_mem_specialUnitary {A : ComplexMatrix2}
    (h : A ∈ ComplexMatrix2.specialUnitary) : A⁻¹ * A = 1 := by apply _root_.YangMills.SharedProofs.p1227 <;> assumption
theorem inv_inv_of_mem_specialUnitary {A : ComplexMatrix2}
    (h : A ∈ ComplexMatrix2.specialUnitary) : A⁻¹⁻¹ = A := by apply _root_.YangMills.SharedProofs.p318 <;> assumption
theorem norm_conj_sub_one {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary)
    (X : ComplexMatrix2) : ‖g * X * g⁻¹ - 1‖ = ‖X - 1‖ := by
  have hu : g ∈ unitary ComplexMatrix2 := (Matrix.mem_specialUnitaryGroup_iff.mp hg).1
  have hi : g⁻¹ = star g := Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hu)
  have hone : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (det_isUnit_of_mem_specialUnitary hg)
  have heq : g * X * g⁻¹ - 1 = g * (X - 1) * star g := by
    rw [← hi, mul_sub, sub_mul, mul_one, hone]
  rw [heq, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hu),
    CStarRing.norm_mem_unitary_mul _ hu]
theorem conj_prod_four {g₀ g₁ g₂ g₃ A B C D : ComplexMatrix2}
    (h₁ : g₁ ∈ ComplexMatrix2.specialUnitary) (h₂ : g₂ ∈ ComplexMatrix2.specialUnitary)
    (h₃ : g₃ ∈ ComplexMatrix2.specialUnitary) :
    g₀ * A * g₁⁻¹ * (g₁ * B * g₂⁻¹) * (g₂ * C * g₃⁻¹) * (g₃ * D * g₀⁻¹) =
      g₀ * (A * B * C * D) * g₀⁻¹ := by
  have c₁ : ∀ X : ComplexMatrix2, g₁⁻¹ * (g₁ * X) = X := fun X => by
    rw [← mul_assoc, inv_mul_cancel_of_mem_specialUnitary h₁, one_mul]
  have c₂ : ∀ X : ComplexMatrix2, g₂⁻¹ * (g₂ * X) = X := fun X => by
    rw [← mul_assoc, inv_mul_cancel_of_mem_specialUnitary h₂, one_mul]
  have c₃ : ∀ X : ComplexMatrix2, g₃⁻¹ * (g₃ * X) = X := fun X => by
    rw [← mul_assoc, inv_mul_cancel_of_mem_specialUnitary h₃, one_mul]
  simp only [mul_assoc, c₁, c₂, c₃]
theorem inv_conj_eq {g g' M : ComplexMatrix2} (h : g' ∈ ComplexMatrix2.specialUnitary) :
    (g * M * g'⁻¹)⁻¹ = g' * M⁻¹ * g⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_inv_of_mem_specialUnitary h, mul_assoc]
theorem bond_finite (hL : 0 < L) (m : ℕ) (j : ℤ) : Finite (Bond L m j) := by
  have := SeparatedSequences.BaseParameters.site_finite hL m j
  exact Finite.of_injective (fun b : Bond L m j => (b.source, b.target)) fun b b' h => by
    simp only [Prod.mk.injEq] at h
    exact Bond.ext h.1 h.2
theorem plaquette_finite (hL : 0 < L) (m : ℕ) (j : ℤ) : Finite (Plaquette L m j) := by
  have := SeparatedSequences.BaseParameters.site_finite hL m j
  exact Finite.of_injective (fun q : Plaquette L m j => (q.origin, q.firstAxis, q.secondAxis))
    fun q q' h => by
      simp only [Prod.mk.injEq] at h
      exact Plaquette.ext h.1 h.2.1 h.2.2
theorem le_maxPlaquetteDeviation (hL : 0 < L) {Y : Set (SiteAtLevel L m K n)}
    (V : BondAtLevel L m K n → ComplexMatrix2) {q : PlaquetteAtLevel L m K n} (hq : q.LiesIn Y) :
    ComplexMatrix2.operatorNorm (plaquetteHolonomy V q - 1) ≤ maxPlaquetteDeviation Y V := by
  have := plaquette_finite hL m (levelDepth K n)
  exact le_csSup ((Set.toFinite {p : PlaquetteAtLevel L m K n | p.LiesIn Y}).image _).bddAbove
    ⟨q, hq, rfl⟩
theorem offsetSite_coord (z : Site L m j) (t : Fin 4 → ℤ) (μ : Fin 4) :
    ((offsetSite z t : Site L m j) : FourTorus L m) μ =
      (z : FourTorus L m) μ + t μ • ((meshSize L j : ℝ) : AddCircle (torusSide L m)) := by
  have hstep : ∀ κ, ((unitStep L m j κ : Site L m j) : FourTorus L m) μ =
      if μ = κ then ((meshSize L j : ℝ) : AddCircle (torusSide L m)) else 0 := fun κ => by
    by_cases hk : μ = κ
    · subst hk; simp [unitStep, pointOnAxis]
    · simp [unitStep, pointOnAxis, hk]
  simp only [offsetSite, AddSubgroup.coe_add, Pi.add_apply, AddSubgroup.val_finsetSum,
    Finset.sum_apply, AddSubgroup.coe_zsmul, Pi.smul_apply, hstep]
  simp
theorem coordCount_sitesFromCorner_le (z : Site L m j) (N : Fin 4 → ℤ) (μ : Fin 4) {M : ℕ}
    (hM : N μ ≤ M) : coordCount μ (sitesFromCorner z N) ≤ (M : ℕ∞) := by
  have hsub : (fun x : Site L m j => (x : FourTorus L m) μ) '' sitesFromCorner z N ⊆
      (fun c : ℤ => (z : FourTorus L m) μ + c • ((meshSize L j : ℝ) : AddCircle (torusSide L m))) ''
        Ico 0 (N μ) := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t μ, ⟨(ht μ).1, (ht μ).2⟩, (offsetSite_coord z t μ).symm⟩
  have hcard : (Ico 0 (N μ)).encard ≤ (M : ℕ∞) := by
    rw [← Finset.coe_Ico, Set.encard_coe_eq_coe_finsetCard, Int.card_Ico]
    have : (N μ - 0).toNat ≤ M := by omega
    exact_mod_cast this
  exact (Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans hcard)
theorem unitStep_add_unitStep_ne_zero (hL : 1 < L) (hm : 0 < m) {j : ℤ} (hj : 0 ≤ j)
    (μ ν : Fin 4) : unitStep L m j μ + unitStep L m j ν ≠ 0 := by
  intro h
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL.le
  have hs0 : 0 < meshSize L j := by
    unfold meshSize
    positivity
  have hs1 : meshSize L j ≤ 1 := by
    unfold meshSize
    rw [zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ hL' hj)
  have hP : (1 : ℝ) < (L : ℝ) ^ m := one_lt_pow₀ (by exact_mod_cast hL) hm.ne'
  have hcoord := congrFun (congrArg Subtype.val h) μ
  have hstep : ∀ κ, ((unitStep L m j κ : Site L m j) : FourTorus L m) μ =
      if μ = κ then ((meshSize L j : ℝ) : AddCircle (torusSide L m)) else 0 := fun κ => by
    by_cases hk : μ = κ
    · subst hk; simp [unitStep, pointOnAxis]
    · simp [unitStep, pointOnAxis, hk]
  have hc : ((unitStep L m j μ : Site L m j) : FourTorus L m) μ +
      ((unitStep L m j ν : Site L m j) : FourTorus L m) μ = 0 := hcoord
  rw [hstep μ, hstep ν] at hc
  have key : ∀ t : ℝ, 0 < t → t ≤ 2 → ((t : ℝ) : AddCircle (torusSide L m)) ≠ 0 := by
    intro t ht0 ht2 hz
    obtain ⟨q, hq⟩ := (AddCircle.coe_eq_zero_iff (torusSide L m)).1 hz
    have hq' : (q : ℝ) * (2 * (L : ℝ) ^ m) = t := by
      simpa [torusSide, zsmul_eq_mul] using hq
    have hqpos : 0 < q := by
      by_contra hneg
      have : (q : ℝ) ≤ 0 := by exact_mod_cast not_lt.1 hneg
      nlinarith
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
    nlinarith
  by_cases hk : μ = ν
  · subst hk
    simp only [if_true] at hc
    have h2 : (((meshSize L j + meshSize L j : ℝ)) : AddCircle (torusSide L m)) = 0 := by
      rw [AddCircle.coe_add]; exact hc
    exact key _ (by linarith) (by linarith) h2
  · simp only [if_true, if_neg hk, add_zero] at hc
    exact key _ hs0 (by linarith) hc
theorem not_isPositivelyOriented_opposite (hL : 1 < L) (hm : 0 < m) {j : ℤ} (hj : 0 ≤ j)
    {b : Bond L m j} (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := hb
  rintro ⟨ν, hν⟩
  apply unitStep_add_unitStep_ne_zero hL hm hj μ ν
  rw [← hμ, ← hν]
  change b.target - b.source + (b.source - b.target) = 0
  abel
theorem forwardFrom_isPositivelyOriented (x : Site L m j) (μ : Fin 4) :
    (Bond.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [Bond.forwardFrom]⟩
theorem schemeBlockAverage_opposite {j j' : ℤ} (s : AveragingScheme)
    (W : Bond L m j' → ComplexMatrix2) {c : Bond L m j}
    (hc : c.IsPositivelyOriented) (hr : ¬c.opposite.IsPositivelyOriented) :
    schemeBlockAverage s W c.opposite = (schemeBlockAverage s W c)⁻¹ := by
  unfold schemeBlockAverage
  rw [if_neg hr, if_pos hc]
  rfl
open Classical in
def extendByOne (Y : Set (SiteAtLevel L m K n)) (W : BondAtLevel L m K n → ComplexMatrix2) :
    BondAtLevel L m K n → ComplexMatrix2 :=
  fun b => if b.LiesIn Y then W b else 1
theorem extendByOne_of_liesIn {Y : Set (SiteAtLevel L m K n)}
    {W : BondAtLevel L m K n → ComplexMatrix2}
    {b : BondAtLevel L m K n} (hb : b.LiesIn Y) : extendByOne Y W b = W b :=
  if_pos hb
theorem extendByOne_isGaugeField {Y : Set (SiteAtLevel L m K n)}
    {W : BondAtLevel L m K n → ComplexMatrix2}
    (hW : IsGaugeFieldWithin Y W) : IsGaugeField compactGaugeGroup univ (extendByOne Y W) := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · unfold extendByOne
    split_ifs with h
    · exact hW.1 b h
    · exact ComplexMatrix2.specialUnitary.one_mem
  · by_cases h : b.LiesIn Y
    · have hr : b.opposite.LiesIn Y := ⟨h.2, h.1⟩
      rw [extendByOne_of_liesIn hr, extendByOne_of_liesIn h]
      exact hW.2 b h
    · have hr : ¬ b.opposite.LiesIn Y := fun h' => h ⟨h'.2, h'.1⟩
      simp [extendByOne, h, hr]
theorem pathHolonomy_mem {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ b, U b ∈ ComplexMatrix2.specialUnitary)
    (Γ : List (Bond L m j)) : pathHolonomy U Γ ∈ ComplexMatrix2.specialUnitary :=
  Submonoid.list_prod_mem _ (by
    intro x hx
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
    exact hU b)
theorem gaugeTransform_isGaugeField {h : Site L m j → ComplexMatrix2}
    {U : Bond L m j → ComplexMatrix2}
    (hh : ∀ x, h x ∈ ComplexMatrix2.specialUnitary) (hU : IsGaugeField compactGaugeGroup univ U) :
    IsGaugeField compactGaugeGroup univ (gaugeTransform h U) := by
  refine ⟨fun b _ => ComplexMatrix2.specialUnitary.mul_mem
    (ComplexMatrix2.specialUnitary.mul_mem (hh _) (hU.1 b (mem_univ b)))
    (inv_mem_specialUnitary (hh _)), fun b _ => ?_⟩
  have hr := hU.2 b (mem_univ b)
  change h b.target * U b.opposite * (h b.source)⁻¹ = (h b.source * U b * (h b.target)⁻¹)⁻¹
  rw [hr, inv_conj_eq (hh _)]
theorem plaquetteHolonomy_gaugeTransform {h : Site L m j → ComplexMatrix2}
    (hh : ∀ x, h x ∈ ComplexMatrix2.specialUnitary)
    (U : Bond L m j → ComplexMatrix2) (q : Plaquette L m j) :
    plaquetteHolonomy (gaugeTransform h U) q =
      h q.origin * plaquetteHolonomy U q * (h q.origin)⁻¹ := by
  have hcomm : q.origin + unitStep L m j q.secondAxis + unitStep L m j q.firstAxis =
      q.origin + unitStep L m j q.firstAxis + unitStep L m j q.secondAxis := add_right_comm _ _ _
  have h₁ := conj_prod_four (g₀ := h q.origin) (g₁ := h (q.origin + unitStep L m j q.firstAxis))
    (g₂ := h (q.origin + unitStep L m j q.firstAxis + unitStep L m j q.secondAxis))
    (g₃ := h (q.origin + unitStep L m j q.secondAxis))
    (A := U (Bond.forwardFrom q.origin q.firstAxis))
    (B := U (Bond.forwardFrom (q.origin + unitStep L m j q.firstAxis) q.secondAxis))
    (C := U (Bond.forwardFrom (q.origin + unitStep L m j q.secondAxis) q.firstAxis).opposite)
    (D := U (Bond.forwardFrom q.origin q.secondAxis).opposite) (hh _) (hh _) (hh _)
  have e₁ : gaugeTransform h U (Bond.forwardFrom q.origin q.firstAxis) =
      h q.origin * U (Bond.forwardFrom q.origin q.firstAxis) *
        (h (q.origin + unitStep L m j q.firstAxis))⁻¹ := rfl
  have e₂ : gaugeTransform h U (Bond.forwardFrom (q.origin + unitStep L m j q.firstAxis) q.secondAxis) =
      h (q.origin + unitStep L m j q.firstAxis) *
        U (Bond.forwardFrom (q.origin + unitStep L m j q.firstAxis) q.secondAxis) *
        (h (q.origin + unitStep L m j q.firstAxis + unitStep L m j q.secondAxis))⁻¹ := rfl
  have e₃ : gaugeTransform h U
        (Bond.forwardFrom (q.origin + unitStep L m j q.secondAxis) q.firstAxis).opposite =
      h (q.origin + unitStep L m j q.firstAxis + unitStep L m j q.secondAxis) *
        U (Bond.forwardFrom (q.origin + unitStep L m j q.secondAxis) q.firstAxis).opposite *
        (h (q.origin + unitStep L m j q.secondAxis))⁻¹ := by
    rw [← hcomm]
    rfl
  have e₄ : gaugeTransform h U (Bond.forwardFrom q.origin q.secondAxis).opposite =
      h (q.origin + unitStep L m j q.secondAxis) * U (Bond.forwardFrom q.origin q.secondAxis).opposite *
        (h q.origin)⁻¹ := rfl
  simp only [plaquetteHolonomy, pathHolonomy, Plaquette.boundaryBonds, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  rw [e₁, e₂, e₃, e₄]
  simpa only [mul_assoc] using h₁
theorem expTwist_eq {V A : Bond L m j → ComplexMatrix2} {Z : Set (Bond L m j)}
    (hrev : ∀ b ∈ Z, b.opposite ∈ Z) (hV : ∀ b ∈ Z, V b.opposite = (V b)⁻¹)
    (h : ∀ b ∈ Z, b.IsPositivelyOriented → V b = ComplexMatrix2.matExp (Complex.I • A b)) :
    ∀ b ∈ Z, expTwist A trivialGaugeField b = V b := by
  intro b hb
  unfold expTwist
  by_cases hp : b.IsPositivelyOriented
  · rw [if_pos hp, h b hb hp]
    simp [trivialGaugeField]
  · have hr := Bond.opposite_isPositivelyOriented hp
    rw [if_neg hp]
    simp only [trivialGaugeField, mul_one]
    rw [← h _ (hrev b hb) hr]
    exact (hV b.opposite (hrev b hb)).symm
theorem mem_complexGaugeGroup_of_mem_compact {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    V ∈ complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hV).2
theorem cornerBlockSites_isSiteBox (hBoxes : CornerBoxProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (p : PlaquetteAtLevel L m K (n + 1)) :
    IsSiteBox (levelDepth K n) (fourCornerBlockSites p) ∧
      (∀ μ, coordCount μ (fourCornerBlockSites p) ≤ ((2 * L - 1 : ℕ) : ℕ∞) + 1) ∧
      (fourCornerBlockSites p).Nonempty := by
  obtain ⟨hfrom, hB⟩ := hBoxes L m K hL hm (by omega) n hn.le
  obtain ⟨-, -, hP⟩ := hB (n + 1) (by omega) (by omega) p.origin
  obtain ⟨hset, hle, hlt⟩ := hP p rfl
  have e : n + 1 - n = 1 := by omega
  rw [e] at hset hle hlt
  simp only [pow_one] at hset hle hlt
  have h13 : (13 : ℤ) ≤ L := by exact_mod_cast hL.2
  set z : SiteAtLevel L m K n := blockCorner (j' := levelDepth K n) (L : ℤ) p.origin with hz
  set N : Fin 4 → ℤ := plaquetteCounts (L : ℤ) p.firstAxis p.secondAxis with hNdef
  have hN1 : ∀ μ, 1 ≤ N μ := by
    intro μ
    simp only [hNdef, plaquetteCounts, doubledCounts, uniformCounts, Function.update_apply]
    split_ifs <;> omega
  have hY : fourCornerBlockSites p = sitesFromCorner z N := by
    ext x
    constructor
    · intro hx
      have hx' : (x : FourTorus L m) ∈ sitesAsTorusPoints (sitesFromCorner z N) := by
        rw [← hset]
        exact hx
      obtain ⟨x', hx'', he⟩ := hx'
      rwa [← Subtype.coe_injective he]
    · intro hx
      exact show (x : FourTorus L m) ∈ ⋃ c ∈ p.vertices, refinedBlock 1 c from by
        rw [hset]
        exact ⟨x, hx, rfl⟩
  rw [hY]
  refine ⟨(hfrom z N fun μ => ⟨hN1 μ, (hle μ).trans_lt hlt⟩).1, fun μ => ?_,
    ⟨z, 0, fun μ => ⟨le_rfl, by have := hN1 μ; simpa using (by omega : 0 < N μ)⟩, ?_⟩⟩
  · have hcast : ((2 * L - 1 : ℕ) : ℕ∞) + 1 = ((2 * L : ℕ) : ℕ∞) := by
      have : 2 * L - 1 + 1 = 2 * L := by have := hL.2; omega
      exact_mod_cast this
    rw [hcast]
    exact coordCount_sitesFromCorner_le z N μ (by have := hle μ; push_cast; omega)
  · simp [offsetSite]
theorem deviation_bounds (hUniversal : stepCovarianceDomainsStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {ϖ : ℝ} (h0 : 0 ≤ ϖ)
    (hϖ : ϖ ≤ stepCurvatureBound L) :
    3 * ((2 * L - 1 : ℕ) : ℝ) * ϖ < 2 ∧
      3 * Real.pi / 2 * ((2 * L - 1 : ℕ) : ℝ) * ϖ ≤ 3 * Real.pi * L * ϖ ∧
      ϖ < min (Averaging.smoothingRadius L) (Averaging.SingleStep.loopVariableConstant L)⁻¹ := by
  have hR : IsStepRadius L (stepRadius L) := (hUniversal L hL).2.1
  have hr16 : stepRadius L ≤ 1 / 16 := hR.le
  have hL0 : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hω : 0 < Averaging.smoothingRadius L :=
    (Averaging.isSmoothingRadius_smoothingRadius hL.1 hL.2).1
  have hκ : 0 < Averaging.SingleStep.loopVariableConstant L := by
    have h1 : (0 : ℝ) < (L : ℝ) - 1 := by linarith
    unfold Averaging.SingleStep.loopVariableConstant Averaging.SingleStep.loopAngleConstant
    positivity
  have hcast : ((2 * L - 1 : ℕ) : ℝ) = 2 * (L : ℝ) - 1 := by
    have h1 : 1 ≤ 2 * L := by have := hL.2; omega
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have hb₁ : ϖ ≤ Averaging.smoothingRadius L / 2 := hϖ.trans (min_le_left _ _)
  have hb₂ : ϖ ≤ (Averaging.SingleStep.loopVariableConstant L)⁻¹ / 2 :=
    hϖ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb₃ : ϖ ≤ stepRadius L / (6 * Real.pi * (L : ℝ)) :=
    hϖ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hpos : 0 < 6 * Real.pi * (L : ℝ) := by positivity
  rw [le_div_iff₀ hpos] at hb₃
  have hLϖ : 0 ≤ (L : ℝ) * ϖ := by positivity
  have hκ' : 0 < (Averaging.SingleStep.loopVariableConstant L)⁻¹ := inv_pos.mpr hκ
  refine ⟨?_, ?_, lt_min (by linarith) (by linarith)⟩
  · rw [hcast]
    nlinarith
  · rw [hcast]
    have : 0 ≤ Real.pi * ϖ := by positivity
    nlinarith
theorem expBondField_eq_on_doubleBlock {Y : Set (SiteAtLevel L m K n)}
    {V : BondAtLevel L m K n → ComplexMatrix2} {h : SiteAtLevel L m K n → ComplexMatrix2}
    {a : LieBondFieldWithin Y}
    (hWh : IsGaugeField compactGaugeGroup univ (gaugeTransform h V))
    (hval : ∀ b ∈ (bondsWithin Y).bonds,
      gaugeTransform h V b = ComplexMatrix2.matExp (Complex.I • (a.eval b : ComplexMatrix2)))
    {c : BondAtLevel L m K (n + 1)}
    (hD : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), b.LiesIn Y) :
    ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)),
      expBondField c (LieBondField.restrictToDoubleBlock c a) b = gaugeTransform h V b := by
  intro b hb
  have hval' : ∀ b' ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)),
      b'.IsPositivelyOriented →
      gaugeTransform h V b' = ComplexMatrix2.matExp
        (Complex.I • ((LieBondField.restrictToDoubleBlock c a).eval b' : ComplexMatrix2)) := by
    intro b' hb' hp
    have e : (LieBondField.restrictToDoubleBlock c a).eval b' = a.eval b' :=
      LieBondField.eval_of_positive (LieBondField.restrictToDoubleBlock c a) ⟨b', hb', hp⟩
    rw [hval b' (hD b' hb'), e]
  exact expTwist_eq
    (A := fun b' => ((LieBondField.restrictToDoubleBlock c a).eval b' : ComplexMatrix2))
    (V := gaugeTransform h V) (Z := bondsInDoubleBlock c) (fun b' hb' => ⟨hb'.2, hb'.1⟩)
    (fun b' _ => hWh.2 b' (mem_univ b')) hval' b hb
theorem edge_average_covariant (hStep : SingleStepBounds)
    (hGauge : GaugeCovarianceStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K) (s : AveragingScheme)
    {V : BondAtLevel L m K n → ComplexMatrix2} {h : SiteAtLevel L m K n → ComplexMatrix2}
    (hV : IsGaugeField compactGaugeGroup univ V) (hh : ∀ x, h x ∈ ComplexMatrix2.specialUnitary)
    {c : BondAtLevel L m K (n + 1)} (hc : c.IsPositivelyOriented)
    (hsize : doubleBlockCurvature V c <
      min (Averaging.smoothingRadius L) (Averaging.SingleStep.loopVariableConstant L)⁻¹) :
    IsSchemeAverageDefined s V c ∧ IsSchemeAverageDefined s (gaugeTransform h V) c ∧
      schemeBlockAverage s (gaugeTransform h V) c =
        h (schemeBaseSite s (levelDepth K n) c.source) * schemeBlockAverage s V c *
          (h (schemeBaseSite s (levelDepth K n) c.target))⁻¹ := by
  have hVc : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) V :=
    ⟨fun b _ => hV.1 b (mem_univ b), fun b _ => hV.2 b (mem_univ b)⟩
  have hVcc : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) V :=
    ⟨fun b _ => mem_complexGaugeGroup_of_mem_compact (hV.1 b (mem_univ b)),
      fun b _ => hV.2 b (mem_univ b)⟩
  have hdef : IsSchemeAverageDefined s V c := (hStep L hL m K n hm hn c hc s V hVc hsize).defined
  have cov := (hGauge L hL m K n hm hn s c hc h V (fun x _ => hh x) hVcc).average hdef
  exact ⟨hdef, cov.1, cov.2⟩
theorem edge_restrictedAverage_eq (hStep : SingleStepBounds)
    (hGauge : GaugeCovarianceStatement)
    (hLocal : OneStepAverageIsLocal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K) (s : AveragingScheme)
    {Y : Set (SiteAtLevel L m K n)} {W V : BondAtLevel L m K n → ComplexMatrix2}
    {h : SiteAtLevel L m K n → ComplexMatrix2} {a : LieBondFieldWithin Y}
    (hW : IsGaugeFieldWithin Y W) (hV : IsGaugeField compactGaugeGroup univ V)
    (hVW : ∀ b : BondAtLevel L m K n, b.LiesIn Y → V b = W b)
    (hh : ∀ x, h x ∈ ComplexMatrix2.specialUnitary)
    (hval : ∀ b ∈ (bondsWithin Y).bonds,
      gaugeTransform h V b = ComplexMatrix2.matExp (Complex.I • (a.eval b : ComplexMatrix2)))
    {c : BondAtLevel L m K (n + 1)} (hc : c.IsPositivelyOriented)
    (hD : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), b.LiesIn Y)
    (hsize : doubleBlockCurvature V c <
      min (Averaging.smoothingRadius L) (Averaging.SingleStep.loopVariableConstant L)⁻¹) :
    restrictedSchemeAverage s a c =
      h (schemeBaseSite s (levelDepth K n) c.source) * schemeBlockAverage s W c *
        (h (schemeBaseSite s (levelDepth K n) c.target))⁻¹ := by
  obtain ⟨hdef, hdefh, hcov⟩ := edge_average_covariant hStep hGauge hL hm hn s hV hh hc hsize
  have hWh := gaugeTransform_isGaugeField hh hV
  have hE := expBondField_eq_on_doubleBlock (a := a) hWh hval hD
  have hVcc : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) V :=
    ⟨fun b _ => mem_complexGaugeGroup_of_mem_compact (hV.1 b (mem_univ b)),
      fun b _ => hV.2 b (mem_univ b)⟩
  have hWhc : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) (gaugeTransform h V) :=
    ⟨fun b _ => mem_complexGaugeGroup_of_mem_compact (hWh.1 b (mem_univ b)),
      fun b _ => hWh.2 b (mem_univ b)⟩
  have hEc : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c)
      (expBondField c (LieBondField.restrictToDoubleBlock c a)) := by
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · rw [hE b hb]
      exact hWhc.1 b hb
    · rw [hE b hb, hE b.opposite ⟨hb.2, hb.1⟩]
      exact hWhc.2 b hb
  have hWc : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) W :=
    ⟨fun b hb => mem_complexGaugeGroup_of_mem_compact (hW.1 b (hD b hb)),
      fun b hb => hW.2 b (hD b hb)⟩
  have l₁ : schemeBlockAverage s (gaugeTransform h V) c =
      schemeBlockAverage s (expBondField c (LieBondField.restrictToDoubleBlock c a)) c :=
    ((hLocal L hL m K n hm hn s c hc _ _ hWhc hEc (fun b hb => (hE b hb).symm)).2 hdefh).1
  have l₂ : schemeBlockAverage s V c = schemeBlockAverage s W c :=
    ((hLocal L hL m K n hm hn s c hc V W hVcc hWc (fun b hb => hVW b (hD b hb))).2 hdef).1
  have l₃ : restrictedSchemeAverage s a c =
      schemeBlockAverage s (expBondField c (LieBondField.restrictToDoubleBlock c a)) c := rfl
  rw [l₃, ← l₁, hcov, l₂]
end CoarsePlaquetteGauge
open CoarsePlaquetteGauge in
theorem coarsePlaquetteCombGauge_holds
    (hComb : CombTransportOnBox.Statement)
    (hStep : SingleStepBounds)
    (hGauge : GaugeCovarianceStatement)
    (hBoxes : CornerBoxProperties)
    (hLocal : OneStepAverageIsLocal)
    (hUniversal : stepCovarianceDomainsStatement) :
    CoarsePlaquetteCombGauge := by
  intro L hL m K n hm hn s p W hW hϖ
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨hbox, hcount, z, hz⟩ := cornerBlockSites_isSiteBox hBoxes hL hm hn p
  set Y := fourCornerBlockSites p with hYdef
  set ϖ := maxPlaquetteDeviation Y W with hϖdef
  have hϖ0 : 0 ≤ ϖ := by
    refine Real.sSup_nonneg ?_
    rintro _ ⟨q, -, rfl⟩
    exact norm_nonneg _
  obtain ⟨h3, hsupnum, hmin⟩ := deviation_bounds hUniversal hL hϖ0 hϖ
  have hV := extendByOne_isGaugeField hW
  set V := CoarsePlaquetteGauge.extendByOne Y W with hVdef
  have hVW : ∀ b : BondAtLevel L m K n, b.LiesIn Y → V b = W b :=
    fun b hb => extendByOne_of_liesIn hb
  have hdefect : maxPlaquetteDeviation Y V = ϖ := maxPlaquetteDeviation_congr fun b hb => hVW b hb
  have hVin : IsGaugeFieldWithin Y V :=
    ⟨fun b _ => hV.1 b (mem_univ b), fun b _ => hV.2 b (mem_univ b)⟩
  have hq : ∀ q : PlaquetteAtLevel L m K n, q.LiesIn Y →
      ComplexMatrix2.operatorNorm (plaquetteHolonomy V q - 1) ≤ ϖ :=
    fun q hq => hdefect ▸ le_maxPlaquetteDeviation hL0 V hq
  obtain ⟨-, -, hexp, -⟩ :=
    hComb L hL m K n hm hn.le Y (2 * L - 1) z V ϖ hbox hcount hz hVin hϖ0 hq
  obtain ⟨a, hreal, hval, hsup⟩ := hexp h3
  have hh : ∀ x, combTransport V z x ∈ ComplexMatrix2.specialUnitary :=
    fun x => pathHolonomy_mem (fun b => hV.1 b (mem_univ b)) _
  generalize combTransport V z = h at hh hval
  have hWh := gaugeTransform_isGaugeField hh hV
  have hside : ∀ c : BondAtLevel L m K (n + 1), c.source ∈ p.vertices → c.target ∈ p.vertices →
      ∀ x : SiteAtLevel L m K n, (x : FourTorus L m) ∈ bondDoubleBlock c → x ∈ Y := by
    rintro c ht hd x (hx | hx)
    · exact mem_iUnion₂.mpr ⟨_, ht, hx⟩
    · exact mem_iUnion₂.mpr ⟨_, hd, hx⟩
  have hD : ∀ c : BondAtLevel L m K (n + 1), c.source ∈ p.vertices → c.target ∈ p.vertices →
      ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), b.LiesIn Y :=
    fun c ht hd b hb => ⟨hside c ht hd _ hb.1, hside c ht hd _ hb.2⟩
  have hsize : ∀ c : BondAtLevel L m K (n + 1), c.source ∈ p.vertices → c.target ∈ p.vertices →
      doubleBlockCurvature V c <
        min (Averaging.smoothingRadius L) (Averaging.SingleStep.loopVariableConstant L)⁻¹ :=
    fun c ht hd => lt_of_le_of_lt (Real.iSup_le (fun q => hq q.1
      (fun x hx => hside c ht hd x (q.2 x hx))) hϖ0) hmin
  have hc₀ : p.origin ∈ p.vertices := by simp [Plaquette.vertices]
  have hc₁ : p.origin + unitStep L m (levelDepth K (n + 1)) p.firstAxis ∈ p.vertices := by
    simp [Plaquette.vertices]
  have hc₂ : p.origin + unitStep L m (levelDepth K (n + 1)) p.firstAxis +
      unitStep L m (levelDepth K (n + 1)) p.secondAxis ∈ p.vertices := by
    simp [Plaquette.vertices]
  have hc₃ : p.origin + unitStep L m (levelDepth K (n + 1)) p.secondAxis ∈ p.vertices := by
    simp [Plaquette.vertices]
  have hcomm : p.origin + unitStep L m (levelDepth K (n + 1)) p.secondAxis +
      unitStep L m (levelDepth K (n + 1)) p.firstAxis =
      p.origin + unitStep L m (levelDepth K (n + 1)) p.firstAxis +
      unitStep L m (levelDepth K (n + 1)) p.secondAxis := add_right_comm _ _ _
  have hc₂' : p.origin + unitStep L m (levelDepth K (n + 1)) p.secondAxis +
      unitStep L m (levelDepth K (n + 1)) p.firstAxis ∈ p.vertices := by rw [hcomm]; exact hc₂
  have hends : ∀ c ∈ ({firstEdge p, secondEdge p, thirdEdge p,
      fourthEdge p} : Set (BondAtLevel L m K (n + 1))),
      c.source ∈ p.vertices ∧ c.target ∈ p.vertices := by
    intro c hc
    simp only [mem_insert_iff, mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨hc₀, hc₁⟩
    · exact ⟨hc₁, hc₂⟩
    · exact ⟨hc₃, hc₂'⟩
    · exact ⟨hc₀, hc₃⟩
  refine ⟨a, hreal, hsup.trans hsupnum, fun c hc => ?_, fun q hqin => ?_, ?_⟩
  · obtain ⟨ht, hd⟩ := hends c hc
    have := bond_finite hL0 m (levelDepth K n)
    refine le_trans ?_ (hsup.trans hsupnum)
    refine Real.iSup_le (fun b => ?_) (Real.iSup_nonneg fun _ => norm_nonneg _)
    have hb : b.1 ∈ (bondsWithin Y).bonds := hD c ht hd b.1 b.2.1
    have e : ((LieBondField.restrictToDoubleBlock c a b : ↥ComplexMatrix2.traceless) :
        ComplexMatrix2) = (a ⟨b.1, hb, b.2.2⟩ : ComplexMatrix2) :=
      congrArg Subtype.val (LieBondField.eval_of_positive a ⟨b.1, hb, b.2.2⟩)
    rw [e]
    exact le_ciSup (f := fun i => ComplexMatrix2.operatorNorm (a i : ComplexMatrix2))
      (Set.finite_range _).bddAbove _
  · have hE : ∀ b ∈ (bondsWithin Y).bonds,
        expTwist (LieBondField.matrixValues a) trivialGaugeField b = gaugeTransform h V b :=
      expTwist_eq (bondsWithin Y).opposite_mem (fun b _ => hWh.2 b (mem_univ b))
        (fun b hb _ => hval b hb)
    have e : plaquetteHolonomy (expTwist (LieBondField.matrixValues a) trivialGaugeField) q =
        plaquetteHolonomy (gaugeTransform h V) q := by
      have hb : q.boundaryBonds.map (expTwist (LieBondField.matrixValues a) trivialGaugeField) =
          q.boundaryBonds.map (gaugeTransform h V) :=
        List.map_congr_left fun b hb => hE b (Plaquette.LiesIn.boundaryBonds_liesIn hqin b hb)
      simp only [plaquetteHolonomy, pathHolonomy, hb]
    rw [e, plaquetteHolonomy_gaugeTransform hh]
    exact (norm_conj_sub_one (hh q.origin) (plaquetteHolonomy V q)).le.trans (hq q hqin)
  · have side : ∀ c ∈ ({firstEdge p, secondEdge p, thirdEdge p,
        fourthEdge p} : Set (BondAtLevel L m K (n + 1))), c.IsPositivelyOriented →
        restrictedSchemeAverage s a c =
          h (schemeBaseSite s (levelDepth K n) c.source) * schemeBlockAverage s W c *
            (h (schemeBaseSite s (levelDepth K n) c.target))⁻¹ := fun c hc hp =>
      edge_restrictedAverage_eq hStep hGauge hLocal hL hm hn s hW hV hVW hh hval hp
        (hD c (hends c hc).1 (hends c hc).2) (hsize c (hends c hc).1 (hends c hc).2)
    have hj : 0 ≤ levelDepth K (n + 1) := by
      simp only [levelDepth]
      omega
    have hL1 : 1 < L := by have := hL.2; omega
    have s₁ := side (firstEdge p) (by simp) (forwardFrom_isPositivelyOriented _ _)
    have s₂ := side (secondEdge p) (by simp) (forwardFrom_isPositivelyOriented _ _)
    have s₃ := side (thirdEdge p) (by simp) (forwardFrom_isPositivelyOriented _ _)
    have s₄ := side (fourthEdge p) (by simp) (forwardFrom_isPositivelyOriented _ _)
    have e₃ : (thirdEdge p).target = p.origin + unitStep L m (levelDepth K (n + 1)) p.firstAxis +
        unitStep L m (levelDepth K (n + 1)) p.secondAxis := hcomm
    rw [e₃] at s₃
    have hP : plaquetteHolonomy (schemeBlockAverage s W) p =
        schemeBlockAverage s W (firstEdge p) * schemeBlockAverage s W (secondEdge p) *
          (schemeBlockAverage s W (thirdEdge p))⁻¹ *
          (schemeBlockAverage s W (fourthEdge p))⁻¹ := by
      have r₃ := schemeBlockAverage_opposite s W (forwardFrom_isPositivelyOriented
        (p.origin + unitStep L m (levelDepth K (n + 1)) p.secondAxis) p.firstAxis)
        (not_isPositivelyOriented_opposite hL1 hm hj (forwardFrom_isPositivelyOriented _ _))
      have r₄ := schemeBlockAverage_opposite s W (forwardFrom_isPositivelyOriented p.origin p.secondAxis)
        (not_isPositivelyOriented_opposite hL1 hm hj (forwardFrom_isPositivelyOriented _ _))
      simp only [plaquetteHolonomy, pathHolonomy, Plaquette.boundaryBonds, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [r₃, r₄]
      simp only [firstEdge, secondEdge, thirdEdge, fourthEdge, mul_assoc]
    have hA : plaquetteAverageHolonomy s a p =
        h (schemeBaseSite s (levelDepth K n) p.origin) *
          (schemeBlockAverage s W (firstEdge p) * schemeBlockAverage s W (secondEdge p) *
            (schemeBlockAverage s W (thirdEdge p))⁻¹ *
            (schemeBlockAverage s W (fourthEdge p))⁻¹) *
          (h (schemeBaseSite s (levelDepth K n) p.origin))⁻¹ := by
      unfold plaquetteAverageHolonomy
      rw [s₁, s₂, s₃, s₄, inv_conj_eq (hh _), inv_conj_eq (hh _)]
      exact conj_prod_four (hh _) (hh _) (hh _)
    rw [hP, hA]
    exact (norm_conj_sub_one (hh _) _).symm
end YangMills.Construction.PeriodicLattice
