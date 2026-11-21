import YangMills.Construction.ClusterExpansionOfAStep.ContoursFromBases
import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.ClusterExpansionOfAStep.AdmissionReadsVOnItsHullProof
import YangMills.Construction.ClusterExpansionOfAStep.BondInCoordinates
import YangMills.Construction.ClusterExpansionOfAStep.ShareOfAChainSplits
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import YangMills.Construction.ColdChainAtEveryLevel.FloorOfTheChartFormProof
import YangMills.Construction.HoleBesideASecondHole.ContoursOfABondAreMostlyGoodProof
import YangMills.Construction.HoleBesideASecondHole.HotLumpsOfAStep
import YangMills.Construction.HoleBesideASecondHole.WhatAHoleSavesInTheBound
import YangMills.Construction.LawInAState.ProductsOfMarksAtOneLevelProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
namespace GroupMoves
variable {n : ℕ}
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := CStarRing.norm_coe_unitary g
theorem coe_mul_unitQuaternion (g h : UnitQuaternion) : ((g * h : UnitQuaternion) : ℍ[ℝ]) = (g : ℍ[ℝ]) * h := rfl
theorem norm_mul_sub_mul_le (g g' h h' : UnitQuaternion) :
    ‖(((g * h : UnitQuaternion) : ℍ[ℝ]) - ((g' * h' : UnitQuaternion) : ℍ[ℝ]))‖ ≤ ‖(g : ℍ[ℝ]) - g'‖ + ‖(h : ℍ[ℝ]) - h'‖ := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.coe_mul_sub_mul_le <;> assumption
theorem norm_inv_sub_inv (g g' : UnitQuaternion) :
    ‖(((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ]))‖ = ‖(g : ℍ[ℝ]) - g'‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
theorem norm_sub_eq_norm_mul_inv_sub_one (g h : UnitQuaternion) :
    ‖(g : ℍ[ℝ]) - h‖ = ‖((g * h⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.GaugedCriticality.norm_coe_sub_coe <;> assumption
theorem expUnit_zero_eq_one : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem norm_expUnit_sub_expUnit_le (f w : imaginaryQuaternions) :
    ‖((expUnit f : UnitQuaternion) : ℍ[ℝ]) - expUnit w‖ ≤ ‖(f : ℍ[ℝ]) - w‖ := by apply _root_.YangMills.Construction.TopLevelSites.norm_expUnit_sub_le <;> assumption
theorem exists_log_norm_le (g : UnitQuaternion) :
    ∃ v : imaginaryQuaternions, expUnit v = g ∧ ‖(v : ℍ[ℝ])‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.exists_expUnit_eq <;> assumption
theorem minimalLog_expUnit_of_norm_lt_pi {w : imaginaryQuaternions} (hw : ‖(w : ℍ[ℝ])‖ < Real.pi) :
    minimalLog (expUnit w) = w := by apply _root_.YangMills.Construction.GaugeFixing.minimalLog_expUnit <;> assumption
theorem curvature_le_add_four_mul (W W' : TorusField n) (x : TorusSite n) (μ ν : Fin 4) (ε : ℝ)
    (h : ∀ y i, ‖(W y i : ℍ[ℝ]) - W' y i‖ ≤ ε) : curvature W x μ ν ≤ curvature W' x μ ν + 4 * ε := by
  unfold curvature holonomy
  set a := W x μ
  set b := W (x + unitStep n μ) ν
  set c := W (x + unitStep n ν) μ
  set d := W x ν
  set a' := W' x μ
  set b' := W' (x + unitStep n μ) ν
  set c' := W' (x + unitStep n ν) μ
  set d' := W' x ν
  have h1 : ‖((a * b * c⁻¹ * d⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((a' * b' * c'⁻¹ * d'⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ ≤
      4 * ε := by
    have s1 := norm_mul_sub_mul_le (a * b * c⁻¹) (a' * b' * c'⁻¹) d⁻¹ d'⁻¹
    have s2 := norm_mul_sub_mul_le (a * b) (a' * b') c⁻¹ c'⁻¹
    have s3 := norm_mul_sub_mul_le a a' b b'
    rw [norm_inv_sub_inv] at s1 s2
    have := h x μ
    have := h (x + unitStep n μ) ν
    have := h (x + unitStep n ν) μ
    have := h x ν
    linarith
  calc ‖((a * b * c⁻¹ * d⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖
      = ‖(((a * b * c⁻¹ * d⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((a' * b' * c'⁻¹ * d'⁻¹ : UnitQuaternion) : ℍ[ℝ])) +
          (((a' * b' * c'⁻¹ * d'⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1)‖ := by congr 1; abel
    _ ≤ _ := (norm_add_le _ _).trans (by linarith)
end GroupMoves
end YangMills.Construction.ClusterExpansionOfAStep
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
namespace ShareStability
open GroupMoves
variable {m : ℕ}
def LeftMovedWithin (ε : ℝ) (G W : TorusField m) : Prop :=
  ∀ x i, ∃ v : imaginaryQuaternions, ‖(v : ℍ[ℝ])‖ ≤ ε ∧ G x i = expUnit v * W x i
theorem norm_mul_expUnit_sub_le (v : imaginaryQuaternions) (g : UnitQuaternion) :
    ‖((expUnit v * g : UnitQuaternion) : ℍ[ℝ]) - g‖ ≤ ‖(v : ℍ[ℝ])‖ := by
  have h := norm_expUnit_sub_expUnit_le v 0
  rw [_root_.YangMills.Construction.ClusterExpansionOfAStep.GroupMoves.expUnit_zero_eq_one] at h
  have e : ((expUnit v * g : UnitQuaternion) : ℍ[ℝ]) - g =
      (((expUnit v : UnitQuaternion) : ℍ[ℝ]) - ((1 : UnitQuaternion) : ℍ[ℝ])) * g := by
    rw [coe_mul_unitQuaternion, sub_mul]
    simp
  rw [e, norm_mul, _root_.YangMills.Construction.ClusterExpansionOfAStep.GroupMoves.norm_coe_unitQuaternion, mul_one]
  simpa using h
theorem isColdOn_of_leftMoved {X : Finset (TorusSite m)} {W G : TorusField m} {s s' ε : ℝ} (hW : IsColdOn X s' W)
    (hG : LeftMovedWithin ε G W) (hs : s' + 4 * ε ≤ s) : IsColdOn X s G := by
  intro x μ ν hμν hc
  have h1 : ∀ y i, ‖(G y i : ℍ[ℝ]) - W y i‖ ≤ ε := by
    intro y i
    obtain ⟨v, hv, e⟩ := hG y i
    rw [e]
    exact (norm_mul_expUnit_sub_le v _).trans hv
  have h2 := curvature_le_add_four_mul G W x μ ν ε h1
  have h3 := hW x μ ν hμν hc
  linarith
def bondsOfBox [NeZero m] (y : TorusSite m) (ρ : ℕ) : Finset (TorusBond m) :=
  open Classical in
  Finset.univ.filter fun b => ∃ e : (Fin 4 → ℤ) × Fin 4, BondOffsetInBox ρ e ∧ bondFrom y e = b
theorem mem_bondsOfBox [NeZero m] {y : TorusSite m} {ρ : ℕ} {b : TorusBond m} :
    b ∈ bondsOfBox y ρ ↔ ∃ e : (Fin 4 → ℤ) × Fin 4, BondOffsetInBox ρ e ∧ bondFrom y e = b := by
  classical
  simp [bondsOfBox]
open Classical in
def patchField (F : Finset (TorusBond m)) (G W : TorusField m) : TorusField m :=
  fun x i => if (x, i) ∈ F then G x i else W x i
theorem patchField_empty (G W : TorusField m) : patchField ∅ G W = W := by
  classical
  funext x i
  simp [patchField]
theorem patchField_insert {F : Finset (TorusBond m)} {G W : TorusField m} {b : TorusBond m} (hb : b ∉ F)
    {v : imaginaryQuaternions} (hv : G b.1 b.2 = expUnit v * W b.1 b.2) :
    patchField (insert b F) G W = multiplyAtBond b v (patchField F G W) := by
  classical
  funext x i
  by_cases h : (x, i) = b
  · subst h
    simp [patchField, multiplyAtBond, hb, hv]
  · simp [patchField, multiplyAtBond, h]
theorem leftMovedWithin_patchField {F : Finset (TorusBond m)} {G W : TorusField m} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ b ∈ F, ∃ v : imaginaryQuaternions, ‖(v : ℍ[ℝ])‖ ≤ ε ∧ G b.1 b.2 = expUnit v * W b.1 b.2) :
    LeftMovedWithin ε (patchField F G W) W := by
  classical
  intro x i
  by_cases hb : (x, i) ∈ F
  · obtain ⟨v, hv, e⟩ := h _ hb
    exact ⟨v, hv, by simp only [patchField, if_pos hb]; exact e⟩
  · exact ⟨0, by simpa using hε, by simp [patchField, hb, _root_.YangMills.Construction.ClusterExpansionOfAStep.GroupMoves.expUnit_zero_eq_one]⟩
theorem leftMovedWithin_multiplyAtBond {F : Finset (TorusBond m)} {G W : TorusField m} {ε : ℝ} (hε : 0 ≤ ε)
    {b : TorusBond m} (hb : b ∉ F) (hF : LeftMovedWithin ε (patchField F G W) W) {v : imaginaryQuaternions}
    (hv : ‖(v : ℍ[ℝ])‖ ≤ ε) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    LeftMovedWithin ε (multiplyAtBond b (τ • v) (patchField F G W)) W := by
  classical
  intro x i
  by_cases h : (x, i) = b
  · subst h
    refine ⟨τ • v, ?_, ?_⟩
    · have : ((τ • v : imaginaryQuaternions) : ℍ[ℝ]) = τ • (v : ℍ[ℝ]) := rfl
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
      nlinarith [norm_nonneg (v : ℍ[ℝ])]
    · simp [multiplyAtBond, patchField, hb]
  · obtain ⟨u, hu, e⟩ := hF x i
    exact ⟨u, hu, by simpa [multiplyAtBond, h] using e⟩
theorem abs_levelShare_patchField_sub_le {a : ℝ} {L : ℕ} {s₀ A δ : ℝ} (hS : ShareLocality a L s₀ A δ) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) [NeZero m] (t : ℕ) (X : Finset (TorusSite m)) (W G : TorusField m) (y : TorusSite m) (s s' ε : ℝ)
    (hm : 64 ≤ m) (hs0 : 0 < s) (hs : s ≤ s₀) (hε : 0 ≤ ε) (hX : IsLocallyOrthantClosed X 1024) (hW : IsColdOn X s' W)
    (hss : s' + 4 * ε ≤ s) (F : Finset (TorusBond m))
    (hF : ∀ b ∈ F, ∃ v : imaginaryQuaternions, ‖(v : ℍ[ℝ])‖ ≤ ε ∧ G b.1 b.2 = expUnit v * W b.1 b.2) :
    |levelShare a L t X y (patchField F G W) - levelShare a L t X y W| ≤ F.card * (A * ε) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [patchField_empty]
  | insert b F hb ih =>
    have hF' : ∀ c ∈ F, ∃ v : imaginaryQuaternions, ‖(v : ℍ[ℝ])‖ ≤ ε ∧ G c.1 c.2 = expUnit v * W c.1 c.2 :=
      fun c hc => hF c (Finset.mem_insert_of_mem hc)
    obtain ⟨v, hv, e⟩ := hF b (Finset.mem_insert_self _ _)
    have hmv := leftMovedWithin_patchField hε hF'
    have hstep := hS.twist_bound t m X (patchField F G W) b v y s hm hs0 hs hX (fun τ h0 h1 =>
      isColdOn_of_leftMoved hW (leftMovedWithin_multiplyAtBond hε hb hmv hv h0 h1) hss)
    rw [← patchField_insert hb e] at hstep
    have hexp : Real.exp (-(δ * _root_.YangMills.Construction.TorusFields.supDist y b.1)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ δ * (_root_.YangMills.Construction.TorusFields.supDist y b.1 : ℝ) := by positivity
      linarith
    have h2 : A * ‖(v : ℍ[ℝ])‖ * Real.exp (-(δ * _root_.YangMills.Construction.TorusFields.supDist y b.1)) ≤ A * ε := by
      calc A * ‖(v : ℍ[ℝ])‖ * Real.exp (-(δ * _root_.YangMills.Construction.TorusFields.supDist y b.1)) ≤ A * ‖(v : ℍ[ℝ])‖ * 1 :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ ≤ A * ε := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hv hA
    have h3 := ih hF'
    rw [Finset.card_insert_of_notMem hb]
    push_cast
    have h4 := abs_sub_le (levelShare a L t X y (patchField (insert b F) G W)) (levelShare a L t X y (patchField F G W))
      (levelShare a L t X y W)
    linarith
theorem abs_levelShare_sub_le_of_near {a : ℝ} {L : ℕ} {s₀ A δ : ℝ} (hS : ShareLocality a L s₀ A δ) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) [NeZero m] (t : ℕ) (X X' : Finset (TorusSite m)) (G W : TorusField m) (y : TorusSite m) (ρ : ℕ)
    (s s' ε : ℝ) (hm : 64 ≤ m) (hs0 : 0 < s) (hs : s ≤ s₀) (hε : 0 ≤ ε) (hX : IsLocallyOrthantClosed X 1024)
    (hX' : IsLocallyOrthantClosed X' 1024) (hG : IsColdOn X s G) (hW : IsColdOn X' s' W) (hss : s' + 4 * ε ≤ s)
    (hside : 2 * ρ + 2 < m)
    (hreg : ∀ h, OffsetInBox ρ h → (y + siteOfInt h ∈ X ↔ y + siteOfInt h ∈ X'))
    (hclose : ∀ b ∈ bondsOfBox y ρ, ∃ v : imaginaryQuaternions, ‖(v : ℍ[ℝ])‖ ≤ ε ∧ G b.1 b.2 = expUnit v * W b.1 b.2) :
    |levelShare a L t X y G - levelShare a L t X' y W| ≤
      A * Real.exp (-(δ * ρ)) + (bondsOfBox y ρ).card * (A * ε) := by
  classical
  set G' := patchField (bondsOfBox y ρ) G W with hG'
  have hmv : LeftMovedWithin ε G' W := leftMovedWithin_patchField hε hclose
  have hc' : IsColdOn X' s G' := isColdOn_of_leftMoved hW hmv hss
  have hagree : RegionsAgreeNear X X' G G' y ρ := by
    refine ⟨hside, hreg, fun b hb => ?_⟩
    have : bondFrom y b ∈ bondsOfBox y ρ := mem_bondsOfBox.mpr ⟨b, hb, rfl⟩
    have e : ((bondFrom y b).1, (bondFrom y b).2) ∈ bondsOfBox y ρ := this
    simp only [hG', patchField, if_pos e]
  have h1 := hS.decay_of_agreement t m X X' G G' y ρ s hm hs0 hs hX hX' hG hc' hagree
  have h2 := abs_levelShare_patchField_sub_le hS hA hδ t X' W G y s s' ε hm hs0 hs hε hX' hW hss (bondsOfBox y ρ) hclose
  have h3 := abs_sub_le (levelShare a L t X y G) (levelShare a L t X' y G') (levelShare a L t X' y W)
  linarith
theorem card_bondsOfBox_le [NeZero m] (y : TorusSite m) (ρ : ℕ) : (bondsOfBox y ρ).card ≤ 4 * (2 * ρ + 1) ^ 4 := by
  classical
  have hsub : bondsOfBox y ρ ⊆
      ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(ρ : ℤ)) ρ) ×ˢ (Finset.univ : Finset (Fin 4))).image
        (bondFrom y) := by
    intro b hb
    obtain ⟨e, he, rfl⟩ := mem_bondsOfBox.mp hb
    refine Finset.mem_image.mpr ⟨e, Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, Finset.mem_univ _⟩, rfl⟩
    have := he.1 i
    rw [Finset.mem_Icc]
    exact abs_le.mp this
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [Finset.card_product, Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have e : ((ρ : ℤ) + 1 - -(ρ : ℤ)).toNat = 2 * ρ + 1 := by omega
  rw [e, mul_comm]
end ShareStability
end YangMills.Construction.ClusterExpansionOfAStep
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
namespace ContourStability
variable {F : BlockFrame}
open GroupMoves
section Distance
variable {j : ℕ}
theorem frameSupDist_triangle (a b c : F.Site j) :
    LumpContours.supDist a c ≤ LumpContours.supDist a b + LumpContours.supDist b c := by apply _root_.YangMills.Construction.LumpContours.supDist_triangle <;> assumption
theorem frameSupDist_self (a : F.Site j) : LumpContours.supDist a a = 0 := by apply _root_.YangMills.Construction.HoleFilling.supDist_self <;> assumption
theorem frameSupDist_step_le_one (hper : ∀ i, NeZero (F.period j i)) (x : F.Site j) (st : PathStep) :
    LumpContours.supDist (x + stepDisplacement j st) x ≤ 1 := by
  unfold LumpContours.supDist
  apply Finset.sup_le
  intro i _
  have := hper i
  have e : (x + stepDisplacement j st : F.Site j) i - x i = ((if st.2 then (Pi.single st.1 1 : Fin 4 → ℤ) i
      else - (Pi.single st.1 1 : Fin 4 → ℤ) i : ℤ) : ZMod (F.period j i)) := by
    unfold stepDisplacement BlockAverages.unitStep siteOfCoords
    by_cases h : st.2 <;> simp [h]
  rw [e]
  refine (_root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le _).trans ?_
  by_cases h : st.2 <;> by_cases h' : i = st.1 <;> simp [h, h', Pi.single_apply]
end Distance
section Paths
variable {j : ℕ} {X X' : F.GaugeField j}
theorem norm_pathHolonomy_sub_le (hper : ∀ i, NeZero (F.period j i)) (ε : ℝ) (hε : 0 ≤ ε) (l : List PathStep)
    (x : F.Site j) (h : ∀ z, LumpContours.supDist z x ≤ l.length → ∀ i, ‖(X z i : ℍ[ℝ]) - X' z i‖ ≤ ε) :
    ‖((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ]) - pathHolonomy X' x l‖ ≤ l.length * ε := by
  induction l generalizing x with
  | nil => simp [pathHolonomy]
  | cons st r ih =>
    have hs : LumpContours.supDist (x + stepDisplacement j st) x ≤ 1 := frameSupDist_step_le_one hper x st
    have h1 := ih (x + stepDisplacement j st) (fun z hz i => h z (by
      have := frameSupDist_triangle z (x + stepDisplacement j st) x
      simp only [List.length_cons]
      omega) i)
    have h2 : ‖((linkValue X x st : UnitQuaternion) : ℍ[ℝ]) - linkValue X' x st‖ ≤ ε := by
      unfold linkValue
      by_cases hst : st.2
      · simp only [hst, if_true]
        exact h x (by rw [frameSupDist_self]; omega) _
      · simp only [hst, Bool.false_eq_true, if_false]
        rw [GroupMoves.norm_inv_sub_inv]
        refine h _ ?_ _
        have e : x - BlockAverages.unitStep j st.1 = x + stepDisplacement j st := by
          unfold stepDisplacement
          simp [hst, sub_eq_add_neg]
        rw [e]
        simp only [List.length_cons]
        omega
    have h3 := GroupMoves.norm_mul_sub_mul_le (linkValue X x st) (linkValue X' x st) (pathHolonomy X (x + stepDisplacement j st) r)
      (pathHolonomy X' (x + stepDisplacement j st) r)
    rw [coe_mul_unitQuaternion, coe_mul_unitQuaternion] at h3
    simp only [pathHolonomy, List.length_cons]
    rw [coe_mul_unitQuaternion, coe_mul_unitQuaternion]
    push_cast
    have e : ((r.length : ℝ) + 1) * ε = r.length * ε + ε := by ring
    rw [e]
    linarith
end Paths
theorem abs_re_le_norm_quaternion (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
theorem abs_fitForm_sub_le (m m' : ℍ[ℝ]) (g : UnitQuaternion) :
    |(‖m‖ - (m * (g : ℍ[ℝ])).re) - (‖m'‖ - (m' * (g : ℍ[ℝ])).re)| ≤ 2 * ‖m - m'‖ := by
  have h1 : |‖m‖ - ‖m'‖| ≤ ‖m - m'‖ := abs_norm_sub_norm_le _ _
  have h2 : |((m - m') * (g : ℍ[ℝ])).re| ≤ ‖m - m'‖ := by
    refine (abs_re_le_norm_quaternion _).trans ?_
    rw [norm_mul, _root_.YangMills.Construction.ClusterExpansionOfAStep.GroupMoves.norm_coe_unitQuaternion, mul_one]
  have e : (m * (g : ℍ[ℝ])).re - (m' * (g : ℍ[ℝ])).re = ((m - m') * (g : ℍ[ℝ])).re := by
    rw [sub_mul]
    simp
  have e2 : (‖m‖ - (m * (g : ℍ[ℝ])).re) - (‖m'‖ - (m' * (g : ℍ[ℝ])).re) =
      (‖m‖ - ‖m'‖) - ((m - m') * (g : ℍ[ℝ])).re := by
    rw [← e]; ring
  rw [e2]
  have := abs_sub (‖m‖ - ‖m'‖) (((m - m') * (g : ℍ[ℝ])).re)
  linarith
theorem card_centredCube_of_odd {M : ℕ} (hM : Odd M) : (centredCube M).card = M ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
theorem length_axisPath_le (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (M : ℕ) (hh : ∀ i, (h i).natAbs ≤ M) :
    (axisPath h π).length ≤ 4 * M := by apply _root_.YangMills.Construction.TorusContours.length_axisPath_le <;> assumption
theorem length_reversePath (l : List PathStep) : (reversePath l).length = l.length := by apply _root_.YangMills.Construction.BlockAverages.ChartFloor.length_reversePath <;> assumption
theorem length_bondContour_le (L : ℕ) (h : Fin 4 → ℤ) (hh : h ∈ centredCube L) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (bondContour L h π i).length ≤ 5 * L := by
  unfold bondContour
  have hb : ∀ k, (h k).natAbs ≤ L / 2 := by
    intro k
    have := Fintype.mem_piFinset.mp hh k
    rw [Finset.mem_Icc] at this
    omega
  have := _root_.YangMills.Construction.ClusterExpansionOfAStep.ContourStability.length_axisPath_le h π (L / 2) hb
  simp only [List.length_append, List.length_replicate, _root_.YangMills.Construction.ClusterExpansionOfAStep.ContourStability.length_reversePath]
  omega
theorem norm_contourAverage_sub_le (hL : Odd F.blockSide) (hper : ∀ i, NeZero (F.period F.depth i))
    (X X' : F.GaugeField F.depth) (c : F.Cell × Fin 4) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ z, LumpContours.supDist z (refineSite c.1) ≤ 5 * F.blockSide → ∀ i, ‖(X z i : ℍ[ℝ]) - X' z i‖ ≤ ε) :
    ‖_root_.YangMills.Construction.BlockAverages.contourAverage X c - _root_.YangMills.Construction.BlockAverages.contourAverage X' c‖ ≤ 5 * F.blockSide * ε := by
  unfold _root_.YangMills.Construction.BlockAverages.contourAverage
  rw [← smul_sub, norm_smul, ← Finset.sum_sub_distrib]
  have hLpos : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have hcard : ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by
    rw [card_centredCube_of_odd hL]; push_cast; rfl
  have hone : ∀ q ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy X (refineSite c.1) (bondContour F.blockSide q π c.2) : UnitQuaternion) : ℍ[ℝ]) -
        pathHolonomy X' (refineSite c.1) (bondContour F.blockSide q π c.2)‖ ≤ 5 * F.blockSide * ε := by
    intro q hq π
    have hlen := length_bondContour_le F.blockSide q hq π c.2
    have h1 := _root_.YangMills.Construction.ClusterExpansionOfAStep.ContourStability.norm_pathHolonomy_sub_le hper ε hε (bondContour F.blockSide q π c.2) (refineSite c.1)
      (fun z hz i => h z (hz.trans hlen) i)
    refine h1.trans ?_
    have : ((bondContour F.blockSide q π c.2).length : ℝ) ≤ 5 * F.blockSide := by exact_mod_cast hlen
    exact mul_le_mul_of_nonneg_right this hε
  have hsum : ‖∑ q ∈ centredCube F.blockSide,
      (∑ π : Equiv.Perm (Fin 4), ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide q π c.2) : UnitQuaternion) : ℍ[ℝ]) -
      ∑ π : Equiv.Perm (Fin 4), ((pathHolonomy X' (refineSite c.1) (bondContour F.blockSide q π c.2) : UnitQuaternion) : ℍ[ℝ]))‖ ≤
      ((centredCube F.blockSide).card : ℝ) * (24 * (5 * F.blockSide * ε)) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ q ∈ centredCube F.blockSide,
        ‖∑ π : Equiv.Perm (Fin 4), ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide q π c.2) : UnitQuaternion) : ℍ[ℝ]) -
        ∑ π : Equiv.Perm (Fin 4), ((pathHolonomy X' (refineSite c.1) (bondContour F.blockSide q π c.2) : UnitQuaternion) : ℍ[ℝ])‖ ≤
          24 * (5 * F.blockSide * ε) := by
      intro q hq
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun π _ => hone q hq π).trans ?_
      simp [Fintype.card_perm, Nat.factorial]
    refine (Finset.sum_le_sum this).trans ?_
    simp
  rw [Real.norm_of_nonneg (by positivity)]
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _ ≤
        1 / (24 * (F.blockSide : ℝ) ^ 4) * (((centredCube F.blockSide).card : ℝ) * (24 * (5 * F.blockSide * ε))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 5 * F.blockSide * ε := by
        rw [hcard]
        field_simp
theorem abs_blockFit_sub_le (hL : Odd F.blockSide) (hper : ∀ i, NeZero (F.period F.depth i)) (X X' : F.GaugeField F.depth)
    (V : F.GaugeField (F.depth + 1)) (c : F.Cell × Fin 4) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ z, LumpContours.supDist z (refineSite c.1) ≤ 5 * F.blockSide → ∀ i, ‖(X z i : ℍ[ℝ]) - X' z i‖ ≤ ε) :
    |blockFit X V c - blockFit X' V c| ≤ 10 * F.blockSide * ε := by
  unfold blockFit
  have h1 := norm_contourAverage_sub_le hL hper X X' c ε hε h
  have h2 := abs_fitForm_sub_le (_root_.YangMills.Construction.BlockAverages.contourAverage X c) (_root_.YangMills.Construction.BlockAverages.contourAverage X' c) ((V c.1 c.2)⁻¹)
  nlinarith
theorem excludedBoxes_eq_empty {J₀ : ℕ} {h : Finset (Finset (F.Site F.depth))} {y : F.Cell} (hy : nearbyLumps h y = ∅) :
    excludedBoxes J₀ h y = ∅ := by apply _root_.YangMills.Construction.BondContours.excludedBoxes_eq_empty <;> assumption
theorem usedContours_eq_allContours {J₀ : ℕ} {h : Finset (Finset (F.Site F.depth))} {b : F.Cell → F.Site F.depth}
    {c : F.Cell × Fin 4} (h1 : nearbyLumps h c.1 = ∅) (h2 : nearbyLumps h (c.1 + BlockAverages.unitStep F.top c.2) = ∅) :
    usedContours J₀ h b c = allContours F := by
  classical
  have hf : (allContours F).filter (fun e => IsGoodContour J₀ h b c e.1 e.2) = allContours F := by
    apply Finset.filter_true_of_mem
    intro e _ x _ B hB
    rw [excludedBoxes_eq_empty h1, excludedBoxes_eq_empty h2] at hB
    simp at hB
  unfold usedContours
  split_ifs
  · rfl
  · exact hf
theorem minimalOffset_centre_add {j : ℕ} (hper : ∀ i, NeZero (F.period j i)) (x : F.Site j) (q : Fin 4 → ℤ)
    (hq : ∀ i, 2 * |q i| < F.period j i) : _root_.YangMills.Construction.LumpContours.minimalOffset x (x + siteOfCoords j q) = q := by
  funext i
  have := hper i
  unfold _root_.YangMills.Construction.LumpContours.minimalOffset
  have e : (x + siteOfCoords j q - x : F.Site j) i = ((q i : ℤ) : ZMod (F.period j i)) := by
    simp [siteOfCoords]
  rw [e]
  have hi := hq i
  refine (ZMod.valMinAbs_spec _ _).mpr ⟨rfl, ?_⟩
  rw [Set.mem_Ioc]
  have a1 := le_abs_self (q i)
  have a2 := neg_abs_le (q i)
  constructor <;> omega
theorem refineSite_eq_cellCentre (y : F.Cell) : refineSite y = cellCentre F.depth y := by apply _root_.YangMills.Construction.GaugeFixing.refineSite_eq_cellCentre <;> assumption
theorem contourMean_eq_contourAverage (hL : Odd F.blockSide) (hper : ∀ i, NeZero (F.period F.depth i))
    (hbig : ∀ i, F.blockSide < F.period F.depth i) {J₀ : ℕ} {h : Finset (Finset (F.Site F.depth))}
    {b : F.Cell → F.Site F.depth} (W : F.GaugeField F.depth) (c : F.Cell × Fin 4)
    (h1 : nearbyLumps h c.1 = ∅) (h2 : nearbyLumps h (c.1 + BlockAverages.unitStep F.top c.2) = ∅)
    (b1 : b c.1 = cellCentre F.depth c.1)
    (b2 : b (c.1 + BlockAverages.unitStep F.top c.2) = cellCentre F.depth (c.1 + BlockAverages.unitStep F.top c.2)) :
    contourMean J₀ h b W c = _root_.YangMills.Construction.BlockAverages.contourAverage W c := by
  classical
  unfold contourMean _root_.YangMills.Construction.BlockAverages.contourAverage
  rw [usedContours_eq_allContours h1 h2]
  have hcard : ((allContours F).card : ℝ) = 24 * (F.blockSide : ℝ) ^ 4 := by
    unfold allContours
    rw [Finset.card_product, card_centredCube_of_odd hL]
    simp [Fintype.card_perm, Nat.factorial]
    ring
  rw [hcard]
  congr 1
  unfold allContours
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun π _ => ?_
  have hq' : ∀ i, 2 * |q i| < ((F.period F.depth i : ℕ) : ℤ) := by
    intro i
    have h3 := Fintype.mem_piFinset.mp hq i
    rw [Finset.mem_Icc] at h3
    have h4 := hbig i
    have h5 : |q i| ≤ ((F.blockSide : ℤ) - 1) / 2 := abs_le.mpr h3
    omega
  simp only
  unfold contourPath bondContour
  rw [b1, b2, minimalOffset_centre_add hper _ q hq', minimalOffset_centre_add hper _ q hq', refineSite_eq_cellCentre]
theorem contourFit_eq_blockFit (hL : Odd F.blockSide) (hper : ∀ i, NeZero (F.period F.depth i))
    (hbig : ∀ i, F.blockSide < F.period F.depth i) {J₀ : ℕ} {h : Finset (Finset (F.Site F.depth))}
    {b : F.Cell → F.Site F.depth} (W : F.GaugeField F.depth) (V : F.GaugeField F.top) (c : F.Cell × Fin 4)
    (h1 : nearbyLumps h c.1 = ∅) (h2 : nearbyLumps h (c.1 + BlockAverages.unitStep F.top c.2) = ∅)
    (b1 : b c.1 = cellCentre F.depth c.1)
    (b2 : b (c.1 + BlockAverages.unitStep F.top c.2) = cellCentre F.depth (c.1 + BlockAverages.unitStep F.top c.2)) :
    contourFit J₀ h b W V c = blockFit W V c := by
  unfold contourFit blockFit
  rw [contourMean_eq_contourAverage hL hper hbig W c h1 h2 b1 b2]
end ContourStability
end YangMills.Construction.ClusterExpansionOfAStep
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
namespace TorusMinimizer
open GroupMoves
variable {n L : ℕ} [NeZero n] [NeZero L]
instance (t : ℕ) : NeZero (n * (torusFrame L t n).blockSide) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
instance : NeZero (n * (stepBlockFrame L n).blockSide) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
theorem period_torusFrame_depth (t : ℕ) (i : Fin 4) :
    (torusFrame L t n).period (torusFrame L t n).depth i = n * L :=
  period_depth_of_extent (fun _ => rfl) i
theorem period_stepBlockFrame_zero (i : Fin 4) : (stepBlockFrame L n).period 0 i = n * L :=
  period_depth_of_extent (F := stepBlockFrame L n) (fun _ => rfl) i
theorem period_torusFrame_top (t : ℕ) (i : Fin 4) : (torusFrame L t n).period (torusFrame L t n).top i = n :=
  period_top_of_extent (fun _ => rfl) i
theorem period_stepBlockFrame_one (i : Fin 4) : (stepBlockFrame L n).period 1 i = n :=
  period_top_of_extent (F := stepBlockFrame L n) (fun _ => rfl) i
theorem readAtLevel_minimizingField (a ρ : ℝ) (t : ℕ) (S : Finset (TorusSite n)) (V : TorusField n) :
    readAtLevel (torusFrame L t n) (torusFrame L t n).depth (minimizingField a ρ L t S V) =
      chartedField (minimizingCoordinates a (cellsOfSites (torusFrame L t n) S)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by
  funext z i
  change minimizingField a ρ L t S V (toTorusSite (n * L) z) i = _
  unfold minimizingField
  rw [torusSiteInFrame_toTorusSite (period_torusFrame_depth t) z]
theorem isAxialTreeBond_frames_iff (hL : Odd L) (h2 : 2 ≤ n) (t : ℕ) (x : TorusSite (n * L)) (i : Fin 4) :
    IsAxialTreeBond (F := torusFrame L t n) (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth x, i) ↔
      IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 x, i) := by
  have h1 := isAxialTreeBond_torusSiteInFrame_iff (F := torusFrame L t n) (n := n) (fun _ => rfl) hL h2 x i
  have h3 := isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame L n) (n := n) (fun _ => rfl) hL h2 x i
  exact h1.trans h3.symm
theorem isCrossingBond_frames_iff (hL : Odd L) (h2 : 2 ≤ n) (t : ℕ) (x : TorusSite (n * L)) (i : Fin 4) :
    IsCrossingBond (F := torusFrame L t n) (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth x, i) ↔
      IsCrossingBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 x, i) := by
  have h1 := isCrossingBond_torusSiteInFrame_iff (F := torusFrame L t n) (n := n) (fun _ => rfl) hL h2 x i
  have h3 := isCrossingBond_torusSiteInFrame_iff (F := stepBlockFrame L n) (n := n) (fun _ => rfl) hL h2 x i
  exact h1.trans h3.symm
open Classical in
theorem minimizingField_apply (hL : Odd L) (h2 : 2 ≤ n) (a ρ : ℝ) (t : ℕ) (S : Finset (TorusSite n)) (V : TorusField n)
    (x : TorusSite (n * L)) (i : Fin 4) :
    minimizingField a ρ L t S V x i =
      if IsCrossingBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 x, i)
      then expUnit (minimizerCoord a ρ L t S V (x, i)) * V (parentBlock L x) i
      else if IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 x, i) then 1
      else expUnit (minimizerCoord a ρ L t S V (x, i)) := by
  have hc := isCrossingBond_frames_iff hL h2 t x i
  have ht := isAxialTreeBond_frames_iff hL h2 t x i
  have hcell : readAtLevel (torusFrame L t n) (torusFrame L t n).top V
      (enclosingCell (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth x)) i = V (parentBlock L x) i := by
    have e : enclosingCell (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth x) =
        torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (parentBlock L x) :=
      enclosingCell_torusSiteInFrame (F := torusFrame L t n) (n := n) (fun _ => rfl) x
    rw [e]
    exact readAtLevel_torusSiteInFrame (period_torusFrame_top t) V (parentBlock L x) i
  unfold minimizingField chartedField
  by_cases h1 : IsCrossingBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 x, i)
  · rw [if_pos (hc.mpr h1), if_pos h1, hcell]
    rfl
  · rw [if_neg (fun h => h1 (hc.mp h)), if_neg h1]
    by_cases h3 : IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 x, i)
    · rw [if_pos (ht.mpr h3), if_pos h3]
    · rw [if_neg (fun h => h3 (ht.mp h)), if_neg h3]
      rfl
end TorusMinimizer
end YangMills.Construction.ClusterExpansionOfAStep
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
open GroupMoves TorusMinimizer
variable {n : ℕ} [NeZero n]
section Blocks
variable {L : ℕ} [NeZero L]
theorem exists_cast_eq_side_mul_add (hL : Odd L) (x : TorusSite (n * L)) (i : Fin 4) :
    ∃ o : ℤ, |o| ≤ ((L : ℤ) - 1) / 2 ∧ ∃ q : ℤ, (q : ZMod n) = parentBlock L x i ∧ (x i).cast = (L : ℤ) * q + o := by
  have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨k, hk⟩ := hL
  have hLz : (L : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  set u : ℤ := (x i).cast with hu
  set q : ℤ := (u + ((L : ℤ) - 1) / 2) / (L : ℤ) with hq
  have h1 := Int.emod_add_mul_ediv (u + ((L : ℤ) - 1) / 2) (L : ℤ)
  have h2 := Int.emod_nonneg (u + ((L : ℤ) - 1) / 2) hLpos.ne'
  have h3 := Int.emod_lt_of_pos (u + ((L : ℤ) - 1) / 2) hLpos
  have hh : ((L : ℤ) - 1) / 2 = k := by rw [hLz]; omega
  rw [hh] at h1 h2 h3
  rw [hh] at hq
  rw [← hq] at h1
  refine ⟨u - (L : ℤ) * q, ?_, q, ?_, by ring⟩
  · rw [hh, abs_le]
    constructor <;> nlinarith
  · unfold parentBlock
    simp only [hq, hh, hu]
theorem supDist_le_side_mul_parentBlock_add (hL : Odd L) (z z' : TorusSite (n * L)) :
    _root_.YangMills.Construction.TorusFields.supDist z z' ≤ L * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L z) (parentBlock L z') + L := by
  rw [_root_.YangMills.Construction.TorusFields.supDist_le_iff]
  intro i
  obtain ⟨o, ho, q, hq, hz⟩ := exists_cast_eq_side_mul_add hL z i
  obtain ⟨o', ho', q', hq', hz'⟩ := exists_cast_eq_side_mul_add hL z' i
  set e : ℤ := (parentBlock L z i - parentBlock L z' i).valMinAbs with he
  have hed : e.natAbs ≤ _root_.YangMills.Construction.TorusFields.supDist (parentBlock L z) (parentBlock L z') :=
    (_root_.YangMills.Construction.TorusFields.supDist_le_iff _ _ _).mp le_rfl i
  have hce : (e : ZMod n) = parentBlock L z i - parentBlock L z' i := by
    rw [he]; simp
  have hdvd : (n : ℤ) ∣ (q - q') - e := by
    have : (((q - q') - e : ℤ) : ZMod n) = 0 := by
      push_cast
      rw [hq, hq', hce]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  obtain ⟨k, hk⟩ := hdvd
  have hcast : z i - z' i = (((L : ℤ) * e + (o - o') : ℤ) : ZMod (n * L)) := by
    have h1 : z i = (((z i).cast : ℤ) : ZMod (n * L)) := by
      rw [ZMod.intCast_zmod_cast]
    have h2 : z' i = (((z' i).cast : ℤ) : ZMod (n * L)) := by
      rw [ZMod.intCast_zmod_cast]
    rw [h1, h2, hz, hz', ← Int.cast_sub]
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨-k, ?_⟩
    push_cast
    have : (q - q') = e + (n : ℤ) * k := by linarith
    have e2 : (L : ℤ) * e + (o - o') - ((L : ℤ) * q + o - ((L : ℤ) * q' + o')) = - ((L : ℤ) * ((q - q') - e)) := by ring
    rw [e2, hk]
    ring
  rw [hcast]
  refine (_root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le _).trans ?_
  have hb : |(L : ℤ) * e + (o - o')| ≤ (L : ℤ) * e.natAbs + L := by
    have h1 : |(L : ℤ) * e| = (L : ℤ) * e.natAbs := by
      rw [abs_mul, Nat.abs_cast, Int.abs_eq_natAbs]
    have h2 : |o - o'| ≤ |o| + |o'| := abs_sub _ _
    have h3 := abs_add_le ((L : ℤ) * e) (o - o')
    omega
  have hb2 : (((L : ℤ) * e + (o - o')).natAbs : ℤ) ≤ (L : ℤ) * e.natAbs + L := by
    rw [Int.natCast_natAbs]; exact hb
  have hb3 : ((L : ℤ) * e.natAbs + L) ≤ ((L * _root_.YangMills.Construction.TorusFields.supDist (parentBlock L z) (parentBlock L z') + L : ℕ) : ℤ) := by
    push_cast
    have : (e.natAbs : ℤ) ≤ _root_.YangMills.Construction.TorusFields.supDist (parentBlock L z) (parentBlock L z') := by exact_mod_cast hed
    nlinarith
  exact_mod_cast hb2.trans hb3
theorem exists_parentBlock_eq (hL : Odd L) (h2 : 2 ≤ n) (Y : TorusSite n) :
    ∃ z : TorusSite (n * L), parentBlock L z = Y := by
  set F := stepBlockFrame L n
  have hs : ∀ i, 2 ≤ F.extent i := fun _ => h2
  have hc := enclosingCell_centre_add (F := F) hL hs (torusSiteInFrame F F.top Y) 0
    ((_root_.YangMills.Construction.TopLevelSites.mem_centredCube_iff _).mpr fun i => by
      have : (0 : ℤ) ≤ halfWidth F.blockSide := by
        unfold halfWidth
        have : 0 < F.blockSide := Nat.pos_of_ne_zero (NeZero.ne L)
        omega
      simpa using this)
  obtain ⟨z, hz⟩ : ∃ z : TorusSite (n * L),
      z = toTorusSite (n * L) (cellCentre F.depth (torusSiteInFrame F F.top Y) + siteOfCoords F.depth 0 : F.Site F.depth) :=
    ⟨_, rfl⟩
  refine ⟨z, ?_⟩
  have e : enclosingCell (torusSiteInFrame F F.depth z) = torusSiteInFrame F F.top (parentBlock L z) :=
    enclosingCell_torusSiteInFrame (F := F) (n := n) (fun _ => rfl) z
  have e2 : torusSiteInFrame F F.depth z =
      (cellCentre F.depth (torusSiteInFrame F F.top Y) + siteOfCoords F.depth 0 : F.Site F.depth) := by
    rw [hz]
    exact torusSiteInFrame_toTorusSite period_stepBlockFrame_zero _
  rw [e2, hc] at e
  have e3 := congrArg (toTorusSite n) e
  have h3 : ∀ u : TorusSite n, toTorusSite n (torusSiteInFrame F F.top u) = u := fun u =>
    toTorusSite_torusSiteInFrame (F := F) (j := F.top) (period_top_of_extent (fun _ => rfl)) u
  rw [h3, h3] at e3
  exact e3.symm
end Blocks
section Places
variable {R : StepSetup} (s : ChartSetting R n) (c : SettingCore R n)
abbrev pieceSites : Finset (TorusSite (n * R.params.side)) :=
  open Classical in c.badBonds.image Prod.fst ∪ s.support ∪ sitesInBlocks R.params.side c.core
theorem storedComponents_eq : s.storedComponents c = chainComponents (10 * R.range) (pieceSites s c) := rfl
theorem mem_storedBlockSet {Y : TorusSite n} : Y ∈ s.storedBlockSet c ↔
    Y ∈ c.core ∨ ∃ z : TorusSite (n * R.params.side), parentBlock R.params.side z = Y ∧
      ∃ v ∈ pieceSites s c, _root_.YangMills.Construction.TorusFields.supDist z v ≤ 4 * R.range := by
  classical
  unfold ChartSetting.storedBlockSet coreBlocks
  rw [storedComponents_eq, biUnion_chainComponents, Finset.mem_union, Finset.mem_filter]
  refine or_congr Iff.rfl ?_
  constructor
  · rintro ⟨-, z, hz⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hz
    refine ⟨z, ?_, (mem_thickening _ _ _).mp h2⟩
    have := (Finset.mem_filter.mp h1).2
    simpa using this
  · rintro ⟨z, rfl, h⟩
    refine ⟨Finset.mem_univ _, z, Finset.mem_inter.mpr ⟨?_, (mem_thickening _ _ _).mpr h⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩
variable {s c} {K : Finset (TorusSite (n * R.params.side))}
theorem piece_subset_pieceSites (hK : s.IsPiece c K) : K ⊆ pieceSites s c := by
  classical
  rcases hK with ⟨P, hP, rfl⟩ | ⟨Q, hQ, rfl⟩
  · intro u hu
    obtain ⟨X, hX, huX⟩ := Finset.mem_biUnion.mp hu
    have hX' : X ∈ chainComponents (10 * R.range) (pieceSites s c) := (Finset.mem_filter.mp (hP hX)).1
    exact subset_of_mem_chainComponents hX' huX
  · intro u hu
    obtain ⟨X, hX, huX⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hu).1
    have hX' : X ∈ chainComponents (10 * R.range) (pieceSites s c) := (Finset.mem_filter.mp hX).1
    exact subset_of_mem_chainComponents hX' huX
theorem mem_piece_of_supDist_le (hK : s.IsPiece c K)
    (hrr : 10 * R.range / R.params.side + 1 ≤ clusterRange R.nextCoupling) {u v : TorusSite (n * R.params.side)}
    (hu : u ∈ K) (hv : v ∈ pieceSites s c) (huv : _root_.YangMills.Construction.TorusFields.supDist u v ≤ 10 * R.range) : v ∈ K := by
  classical
  have hsub := piece_subset_pieceSites hK
  have hj : ChainConnected (10 * R.range) (pieceSites s c) u v := chainConnected_of_supDist_le (hsub hu) hv huv
  rcases hK with ⟨P, hP, rfl⟩ | ⟨Q, hQ, rfl⟩
  · obtain ⟨X, hX, huX⟩ := Finset.mem_biUnion.mp hu
    have hX' : X ∈ chainComponents (10 * R.range) (pieceSites s c) := (Finset.mem_filter.mp (hP hX)).1
    exact Finset.mem_biUnion.mpr ⟨X, hX, mem_of_chainConnected_of_mem_chainComponents hX' huX hv hj⟩
  · obtain ⟨hu1, hu2⟩ := Finset.mem_inter.mp hu
    obtain ⟨X, hX, huX⟩ := Finset.mem_biUnion.mp hu1
    have hXc : X ∈ chainComponents (10 * R.range) (pieceSites s c) := (Finset.mem_filter.mp hX).1
    have hvX : v ∈ X := mem_of_chainConnected_of_mem_chainComponents hXc huX hv hj
    have hv1 : v ∈ s.attachedPart c := Finset.mem_biUnion.mpr ⟨X, hX, hvX⟩
    refine Finset.mem_inter.mpr ⟨hv1, ?_⟩
    obtain ⟨X', hX', hbu⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hu2).2
    have hXq : X' ∈ chainComponents (clusterRange R.nextCoupling) (s.coarseHullOf c) := hQ hX'
    have hbv : parentBlock R.params.side v ∈ s.coarseHullOf c := by
      refine (mem_thickening _ _ _).mpr ⟨parentBlock R.params.side v, ?_, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩
      refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, ?_⟩)
      refine Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩, ?_⟩
      exact (mem_thickening _ _ _).mpr ⟨v, hv1, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩
    have hd : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side u) (parentBlock R.params.side v) ≤ clusterRange R.nextCoupling := by
      refine (_root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one _ u v).trans (le_trans ?_ hrr)
      have := Nat.div_le_div_right (c := R.params.side) huv
      omega
    have hjj : ChainConnected (clusterRange R.nextCoupling) (s.coarseHullOf c) (parentBlock R.params.side u)
        (parentBlock R.params.side v) :=
      chainConnected_of_supDist_le (subset_of_mem_chainComponents hXq hbu) hbv hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨X', hX', mem_of_chainConnected_of_mem_chainComponents hXq hbu hbv hjj⟩⟩
end Places
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
variable {n : ℕ} [NeZero n] {R : StepSetup}
open GroupMoves TorusMinimizer
structure Sizes (R : StepSetup) (D : ℕ) : Prop where
  admissible : R.params.Admissible
  range_le : 10 * R.range / R.params.side + 1 ≤ clusterRange R.nextCoupling
  zone_le : R.params.side * (D + 8) ≤ R.range
  range_large : 2 ^ 16 ≤ R.range
  nextRange_large : 2 ^ 16 ≤ clusterRange R.nextCoupling
section
variable {s : ChartSetting R n} {c : SettingCore R n} {K : Finset (TorusSite (n * R.params.side))} {D : ℕ}
theorem mem_blocksNear {L r : ℕ} [NeZero L] {K : Finset (TorusSite (n * L))} {Y : TorusSite n} :
    Y ∈ blocksNear L r K ↔ ∃ z : TorusSite (n * L), parentBlock L z = Y ∧ ∃ u ∈ K, _root_.YangMills.Construction.TorusFields.supDist z u ≤ 5 * r := by
  classical
  unfold blocksNear
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hz
    refine ⟨z, ?_, (mem_thickening _ _ _).mp h2⟩
    simpa using (Finset.mem_filter.mp h1).2
  · rintro ⟨z, rfl, h⟩
    exact ⟨z, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩, (mem_thickening _ _ _).mpr h⟩⟩
theorem exists_near_of_mem_thickening (hS : Sizes R D) {Z : TorusSite n} {D' : ℕ} (hD' : D' ≤ D + 4)
    (hz : Z ∈ thickening D' (blocksNear R.params.side R.range K)) :
    ∃ u ∈ K, ∀ z : TorusSite (n * R.params.side), parentBlock R.params.side z = Z → _root_.YangMills.Construction.TorusFields.supDist z u ≤ 6 * R.range := by
  classical
  obtain ⟨Y, hY, hZY⟩ := (mem_thickening _ _ _).mp hz
  obtain ⟨z₁, rfl, u, hu, hd⟩ := mem_blocksNear.mp hY
  refine ⟨u, hu, fun z hzZ => ?_⟩
  have h1 := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_le_side_mul_parentBlock_add hS.admissible.L_odd z z₁
  rw [hzZ] at h1
  have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle z z₁ u
  have h3 : R.params.side * _root_.YangMills.Construction.TorusFields.supDist Z (parentBlock R.params.side z₁) ≤ R.params.side * (D + 4) :=
    Nat.mul_le_mul_left _ (hZY.trans hD')
  have h4 := hS.zone_le
  have h5 : R.params.side * (D + 8) = R.params.side * (D + 4) + 4 * R.params.side := by ring
  omega
theorem not_mem_storedBlockSet (hS : Sizes R D) (hK : s.IsPiece c K) {Z : TorusSite n}
    {u : TorusSite (n * R.params.side)} (hu : u ∈ K)
    (hnear : ∀ z : TorusSite (n * R.params.side), parentBlock R.params.side z = Z → _root_.YangMills.Construction.TorusFields.supDist z u ≤ 6 * R.range)
    (hfar : ∀ z : TorusSite (n * R.params.side), parentBlock R.params.side z = Z → ∀ v ∈ K, 4 * R.range < _root_.YangMills.Construction.TorusFields.supDist z v)
    (h2 : 2 ≤ n) : Z ∉ s.storedBlockSet c := by
  classical
  intro hZ
  rcases (mem_storedBlockSet s c).mp hZ with hC | ⟨z, hz, v, hv, hzv⟩
  · obtain ⟨z₀, hz₀⟩ := exists_parentBlock_eq (L := R.params.side) hS.admissible.L_odd h2 Z
    have hp : z₀ ∈ pieceSites s c :=
      Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz₀ ▸ hC⟩)
    have hd : _root_.YangMills.Construction.TorusFields.supDist u z₀ ≤ 10 * R.range := by
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
      have := hnear z₀ hz₀
      omega
    have hin := mem_piece_of_supDist_le hK hS.range_le hu hp hd
    have := hfar z₀ hz₀ z₀ hin
    rw [_root_.YangMills.Construction.TorusFields.supDist_self] at this
    omega
  · have hd : _root_.YangMills.Construction.TorusFields.supDist u v ≤ 10 * R.range := by
      have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle u z v
      have h3 := hnear z hz
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h3
      omega
    have hin := mem_piece_of_supDist_le hK hS.range_le hu hv hd
    have := hfar z hz v hin
    omega
theorem not_mem_storedBlockSet_of_zone (hS : Sizes R D) (hK : s.IsPiece c K) (h2 : 2 ≤ n) {Z Y₁ : TorusSite n}
    (hz : Z ∈ thickening (D + 4) (blocksNear R.params.side R.range K)) (hY₁ : Y₁ ∉ blocksNear R.params.side R.range K)
    (hZY : _root_.YangMills.Construction.TorusFields.supDist Z Y₁ ≤ D + 4) : Z ∉ s.storedBlockSet c := by
  classical
  obtain ⟨u, hu, hnear⟩ := exists_near_of_mem_thickening hS le_rfl hz
  refine not_mem_storedBlockSet hS hK hu hnear (fun z hzZ v hv => ?_) h2
  obtain ⟨y₁, hy₁⟩ := exists_parentBlock_eq (L := R.params.side) hS.admissible.L_odd h2 Y₁
  have h1 : 5 * R.range < _root_.YangMills.Construction.TorusFields.supDist y₁ v := by
    by_contra hcon
    exact hY₁ (mem_blocksNear.mpr ⟨y₁, hy₁, v, hv, not_lt.mp hcon⟩)
  have h3 := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_le_side_mul_parentBlock_add hS.admissible.L_odd y₁ z
  rw [hy₁, hzZ, _root_.YangMills.Construction.TorusFields.supDist_comm Y₁ Z] at h3
  have h4 : R.params.side * _root_.YangMills.Construction.TorusFields.supDist Z Y₁ ≤ R.params.side * (D + 4) := Nat.mul_le_mul_left _ hZY
  have h5 := _root_.YangMills.Construction.TorusFields.supDist_triangle y₁ z v
  have h6 := hS.zone_le
  have h7 : R.params.side * (D + 8) = R.params.side * (D + 4) + 4 * R.params.side := by ring
  omega
end
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
variable {n : ℕ} [NeZero n] {R : StepSetup}
theorem toImaginary_zero : toImaginary (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by apply _root_.YangMills.Construction.BondCoordinates.toImaginary_zero <;> assumption
open GroupMoves TorusMinimizer
section Tree
variable {s : ChartSetting R n} {c : SettingCore R n}
theorem gaugeAt_eq_one_of (hL : Odd R.params.side) (h2 : 2 ≤ n) (Wf : TorusField (n * R.params.side))
    (x : TorusSite (n * R.params.side))
    (hWf : ∀ b : TorusBond (n * R.params.side), parentBlock R.params.side b.1 = parentBlock R.params.side x →
      IsAxialTreeBond (F := stepBlockFrame R.params.side n) (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1, b.2) →
        Wf b.1 b.2 = 1) :
    gaugeAt (R := R) Wf x = 1 := by
  classical
  set F := stepBlockFrame R.params.side n with hF
  have hs : ∀ i, 2 ≤ F.extent i := fun _ => h2
  have hL' : Odd F.blockSide := hL
  set W : F.GaugeField F.depth := readAtLevel F 0 Wf with hW
  set γ : F.Site F.depth → UnitQuaternion := axialGauge 1 W with hγ
  have hbl : torusSiteInFrame F F.top (parentBlock R.params.side x) = enclosingCell (torusSiteInFrame F F.depth x) :=
    (enclosingCell_torusSiteInFrame (F := F) (n := n) (fun _ => rfl) x).symm
  have h1 : ∀ z : F.Cell, γ (cellCentre F.depth z) = 1 := by
    intro z
    have hc : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := (_root_.YangMills.Construction.TopLevelSites.mem_centredCube_iff _).mpr fun i => by
      have : (0 : ℤ) ≤ halfWidth F.blockSide := by
        unfold halfWidth
        have : 0 < F.blockSide := Nat.pos_of_ne_zero (NeZero.ne R.params.side)
        omega
      simpa using this
    have ho := cellOffset_centre_add hL' hs z 0 hc
    have e0 : (cellCentre F.depth z + siteOfCoords F.depth 0 : F.Site F.depth) = cellCentre F.depth z := by
      have : (siteOfCoords F.depth (0 : Fin 4 → ℤ) : F.Site F.depth) = 0 := by
        funext i
        simp [siteOfCoords]
      rw [this, add_zero]
    rw [e0] at ho
    have e1 : axisPath (0 : Fin 4 → ℤ) (1 : Equiv.Perm (Fin 4)) = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp [axisPath]
    simp only [hγ, axialGauge, ho, e1]
    rfl
  have hb : ∀ b ∈ innerBonds ({torusSiteInFrame F F.top (parentBlock R.params.side x)} : Finset F.Cell) F.depth,
      IsAxialTreeBond b → γ b.1 = γ (b.1 + BlockAverages.unitStep F.depth b.2) := by
    intro b hb ht
    have hb1 : b.1 ∈ sitesOfCells ({torusSiteInFrame F F.top (parentBlock R.params.side x)} : Finset F.Cell) F.depth :=
      (Finset.mem_product.mp (Finset.mem_filter.mp hb).1).1
    obtain ⟨y, hy, h, hh, e⟩ := BlockAverages.mem_sitesOfCells.mp hb1
    rw [Finset.mem_singleton] at hy
    have hh' : h ∈ centredCube F.blockSide := by
      have : F.blockSide ^ (F.top - F.depth) = F.blockSide := by rw [_root_.YangMills.Construction.TopLevelSites.top_sub_depth, pow_one]
      rwa [this] at hh
    have hcell : enclosingCell b.1 = torusSiteInFrame F F.top (parentBlock R.params.side x) := by
      rw [e, enclosingCell_centre_add hL' hs y h hh', hy]
    set b' : TorusSite (n * R.params.side) := toTorusSite (n * R.params.side) b.1 with hb'
    have hof : torusSiteInFrame F F.depth b' = b.1 := torusSiteInFrame_toTorusSite period_stepBlockFrame_zero b.1
    have hblock : parentBlock R.params.side b' = parentBlock R.params.side x := by
      have e1 : enclosingCell (torusSiteInFrame F F.depth b') = torusSiteInFrame F F.top (parentBlock R.params.side b') :=
        enclosingCell_torusSiteInFrame (F := F) (n := n) (fun _ => rfl) b'
      rw [hof, hcell] at e1
      have e3 := congrArg (toTorusSite n) e1
      have h3 : ∀ u : TorusSite n, toTorusSite n (torusSiteInFrame F F.top u) = u := fun u =>
        toTorusSite_torusSiteInFrame (F := F) (j := F.top) (period_top_of_extent (fun _ => rfl)) u
      rw [h3, h3] at e3
      exact e3.symm
    have ht' : IsAxialTreeBond (F := stepBlockFrame R.params.side n)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b', b.2) := by
      have : torusSiteInFrame (stepBlockFrame R.params.side n) 0 b' = b.1 := hof
      rw [this]
      exact ht
    have hone : Wf b' b.2 = 1 := hWf (b', b.2) hblock ht'
    have hv := axialGauge_treeBond hL' hs W b.1 b.2 ht
    have hWb : W b.1 b.2 = 1 := hone
    simp only [BlockAverages.gaugeTransform, hWb, mul_one] at hv
    exact mul_inv_eq_one.mp hv
  obtain ⟨ho, he⟩ := centre_cellOffset hL' hs (torusSiteInFrame F F.depth x)
  have key := gauge_eq_one_on_sites hL' hs γ h1 hb (torusSiteInFrame F F.top (parentBlock R.params.side x))
    (Finset.mem_singleton_self _) (cellOffset (torusSiteInFrame F F.depth x)) ho
  rw [hbl, he] at key
  exact key
theorem gaugeAt_fine_eq_one (hL : Odd R.params.side) (h2 : 2 ≤ n) (hm : s.IsMarked c) (x : TorusSite (n * R.params.side))
    (hx : parentBlock R.params.side x ∉ s.storedBlockSet c) : gaugeAt s.fine x = 1 :=
  gaugeAt_eq_one_of hL h2 s.fine x fun b hb ht => hm.fine_on_trees b (by rw [hb]; exact hx) ht
end Tree
section Values
variable {s : ChartSetting R n} {c : SettingCore R n}
theorem mem_free_of_chart (hst : s.IsCoreOf c) {b : TorusBond (n * R.params.side)}
    (hch : b ∈ StepCosts.chartBonds R.params.side n) (hb : parentBlock R.params.side b.1 ∉ s.storedBlockSet c) :
    b ∈ s.free := by
  classical
  rw [hst.free_eq]
  refine Finset.mem_filter.mpr ⟨hch, ?_, fun h => hb h.1⟩
  intro hC
  exact hb (Finset.mem_union_left _ hC)
theorem mem_chartBonds_iff {b : TorusBond (n * R.params.side)} : b ∈ StepCosts.chartBonds R.params.side n ↔
    ¬ IsAxialTreeBond (F := stepBlockFrame R.params.side n) (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1, b.2) := by
  classical
  simp [StepCosts.chartBonds]
def FramesNearMinimizer (s : ChartSetting R n) (C S : Finset (TorusSite n)) (g : ℝ) : Prop :=
  ∀ b ∈ StepCosts.chartBonds R.params.side n, parentBlock R.params.side b.1 ∉ C →
    ‖(s.frame b : ℍ[ℝ]) - (minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse b : ℍ[ℝ])‖ ≤ g
theorem exists_field_zero_eq (hL : Odd R.params.side) (h2 : 2 ≤ n) (hs : s.IsAdmissible) (hst : s.IsCoreOf c)
    (hm : s.IsMarked c) {S : Finset (TorusSite n)} {g : ℝ} (hg : 0 ≤ g) (hf : FramesNearMinimizer s c.core S g)
    (x : TorusSite (n * R.params.side)) (i : Fin 4) (h1 : parentBlock R.params.side x ∉ s.storedBlockSet c)
    (h3 : parentBlock R.params.side (x + unitStep (n * R.params.side) i) ∉ s.storedBlockSet c) :
    ∃ v : imaginaryQuaternions, ‖(v : ℍ[ℝ])‖ ≤ 2 * g ∧
      s.field 0 x i = expUnit v * minimizingField R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse x i := by
  classical
  rw [minimizingField_apply hL h2]
  by_cases htree : IsAxialTreeBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)
  · refine ⟨0, by simpa using hg, ?_⟩
    have hnc : ¬ IsCrossingBond (F := stepBlockFrame R.params.side n)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i) := htree.1
    have hnf : (x, i) ∉ s.free := fun h => (mem_chartBonds_iff.mp (hs.subset_chart h)) htree
    rw [if_neg hnc, if_pos htree, _root_.YangMills.Construction.ClusterExpansionOfAStep.GroupMoves.expUnit_zero_eq_one, one_mul]
    simp only [ChartSetting.field, dif_neg hnf]
    exact hm.fine_on_trees (x, i) h1 htree
  · have hch : (x, i) ∈ StepCosts.chartBonds R.params.side n := mem_chartBonds_iff.mpr htree
    have hfree := mem_free_of_chart hst hch h1
    have hnC : parentBlock R.params.side x ∉ c.core := fun h => h1 (Finset.mem_union_left _ h)
    have hgap := hf (x, i) hch hnC
    set f : imaginaryQuaternions := s.frame (x, i) with hfdef
    set w : imaginaryQuaternions :=
      minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse (x, i) with hw
    obtain ⟨v, hlog, hv⟩ := exists_log_norm_le (expUnit f * (expUnit w)⁻¹)
    refine ⟨v, ?_, ?_⟩
    · refine hv.trans ?_
      rw [← norm_sub_eq_norm_mul_inv_sub_one]
      have := norm_expUnit_sub_expUnit_le f w
      linarith
    · have hval : s.field 0 x i = chartLink s x i f := by
        simp only [ChartSetting.field, dif_pos hfree]
        have : toImaginary ((0 : FreeCoords s.free) ⟨(x, i), hfree⟩) = 0 := toImaginary_zero
        rw [this, add_zero]
      rw [hval, hlog]
      unfold chartLink
      rw [gaugeAt_fine_eq_one hL h2 hm x h1, gaugeAt_fine_eq_one hL h2 hm _ h3]
      by_cases hc : IsCrossingBond (F := stepBlockFrame R.params.side n)
          (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)
      · rw [if_pos hc, if_pos hc]
        group
      · rw [if_neg hc, if_neg hc, if_neg htree]
        group
end Values
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
open GroupMoves TorusMinimizer ShareStability
section Read
variable {F : BlockFrame} {j N : ℕ} [NeZero N] {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters}
theorem mem_plaquetteCorners_iff_toTorusSite (hp : ∀ i, F.period j i = N) (x : F.Site j) (μ ν : Fin 4) (c : F.Site j) :
    c ∈ plaquetteCorners (x, μ, ν) ↔ toTorusSite N c ∈ plaquetteVertices (toTorusSite N x) μ ν := by
  classical
  have hq : ∀ a b : F.Site j, toTorusSite N a = toTorusSite N b → a = b := fun a b h => toTorusSite_injective hp h
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton, plaquetteVertices, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (by rw [toTorusSite_add hp, toTorusSite_unitStep hp]))
    · exact Or.inr (Or.inr (Or.inl (by rw [toTorusSite_add hp, toTorusSite_unitStep hp])))
    · exact Or.inr (Or.inr (Or.inr (by
        rw [toTorusSite_add hp, toTorusSite_add hp, toTorusSite_unitStep hp, toTorusSite_unitStep hp])))
  · rintro (h | h | h | h)
    · exact Or.inl (hq _ _ h)
    · exact Or.inr (Or.inl (hq _ _ (by rw [h, toTorusSite_add hp, toTorusSite_unitStep hp])))
    · exact Or.inr (Or.inr (Or.inl (hq _ _ (by rw [h, toTorusSite_add hp, toTorusSite_unitStep hp]))))
    · exact Or.inr (Or.inr (Or.inr (hq _ _ (by
        rw [h, toTorusSite_add hp, toTorusSite_add hp, toTorusSite_unitStep hp, toTorusSite_unitStep hp]))))
theorem mem_hotLumps_readAtLevel_iff (hfit : ℓ.Admissible) (hLN : ℓ.side ∣ N) (hp : ∀ i, F.period j i = N)
    (X : Finset (TorusSite N)) (W : TorusField N) (l : Finset (F.Site j)) :
    l ∈ hotLumps ℓ.grid ℓ.threshold (X.image (torusSiteInFrame F j)) (readAtLevel F j W) ↔
      ∃ (x : TorusSite N) (μ ν : Fin 4), μ < ν ∧ (∀ z ∈ plaquetteVertices x μ ν, z ∈ X) ∧
        ℓ.threshold ≤ curvature W x μ ν ∧
        ∃ z ∈ plaquetteVertices x μ ν, (open Classical in l.image (toTorusSite N)) = torusLumpOf ℓ z := by
  classical
  have hin : ∀ c : F.Site j, c ∈ X.image (torusSiteInFrame F j) ↔ toTorusSite N c ∈ X := by
    intro c
    constructor
    · intro h
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
      rwa [toTorusSite_torusSiteInFrame hp]
    · intro h
      exact Finset.mem_image.mpr ⟨_, h, torusSiteInFrame_toTorusSite hp c⟩
  unfold hotLumps
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, μ, ν⟩, ⟨hpl, hs⟩, z₀, hz₀, rfl⟩
    obtain ⟨-, hlt, hsub⟩ := Finset.mem_filter.mp hpl
    refine ⟨toTorusSite N x, μ, ν, hlt, fun z hz => ?_, ?_, toTorusSite N z₀,
      (mem_plaquetteCorners_iff_toTorusSite hp x μ ν z₀).mp hz₀, image_lumpOf_toTorusSite hfit hLN hp z₀⟩
    · have hc : torusSiteInFrame F j z ∈ plaquetteCorners (x, μ, ν) := by
        rw [mem_plaquetteCorners_iff_toTorusSite hp, toTorusSite_torusSiteInFrame hp]
        exact hz
      have := (hin _).mp (hsub hc)
      rwa [toTorusSite_torusSiteInFrame hp] at this
    · rw [← plaquetteDefect_readAtLevel_eq hp]
      exact hs
  · rintro ⟨x, μ, ν, hlt, hX, hs, z, hz, hl⟩
    have hox : toTorusSite N (torusSiteInFrame F j x) = x := toTorusSite_torusSiteInFrame hp x
    refine ⟨(torusSiteInFrame F j x, μ, ν), ⟨?_, ?_⟩, torusSiteInFrame F j z, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, hlt, fun c hc => ?_⟩
      · refine Finset.mem_product.mpr ⟨?_, by simp⟩
        refine (hin _).mpr ?_
        rw [hox]
        exact hX x (by simp [plaquetteVertices])
      · refine (hin _).mpr (hX _ ?_)
        rw [← hox]
        exact (mem_plaquetteCorners_iff_toTorusSite hp _ μ ν c).mp hc
    · rw [plaquetteDefect_readAtLevel_eq hp, hox]
      exact hs
    · rw [mem_plaquetteCorners_iff_toTorusSite hp, toTorusSite_torusSiteInFrame hp, toTorusSite_torusSiteInFrame hp]
      exact hz
    · have e := image_lumpOf_toTorusSite hfit hLN hp (torusSiteInFrame F j z)
      rw [toTorusSite_torusSiteInFrame hp, ← hl] at e
      exact Finset.image_injective (fun a b h => toTorusSite_injective hp h) e
end Read
variable {n : ℕ} [NeZero n] {R : StepSetup}
def glueFields (L : ℕ) [NeZero L] (Z : Finset (TorusSite n)) (W Wl : TorusField (n * L)) : TorusField (n * L) :=
  open Classical in fun x i => if parentBlock L x ∈ Z then W x i else Wl x i
structure NearPieceData (s : ChartSetting R n) (c : SettingCore R n) (K : Finset (TorusSite (n * R.params.side))) (D : ℕ)
    (S₀ S : Finset (TorusSite n)) (g s' : ℝ) : Prop where
  sizes : Sizes R D
  two_le : 2 ≤ n
  depth_ge : 16 ≤ D
  admissible : s.IsAdmissible
  core : s.IsCoreOf c
  marked : s.IsMarked c
  piece : s.IsPiece c K
  gap_nonneg : 0 ≤ g
  frames_near : FramesNearMinimizer s c.core S g
  cold : IsColdOn (sitesInBlocks R.params.side S) s'
    (minimizingField R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse)
  small : s' + 8 * g < R.params.threshold
  zone_sub : ∀ Z ∈ thickening (D + 6) (blocksNear R.params.side R.range K), Z ∈ S₀
  rest_sub : ∀ Z ∈ S₀, Z ∉ blocksNear R.params.side R.range K → Z ∈ S
  cut_sub : S ⊆ S₀
  mem_cut_of_not_core : ∀ Z, Z ∉ c.core → Z ∈ S
  mem_cut_of_near_not_core : ∀ Z, Z ∉ c.core → ∀ Z', _root_.YangMills.Construction.TorusFields.supDist Z' Z ≤ 1 → Z' ∈ S
  gap_le : g ≤ R.ballRadius / 8
  minimizer_small : ∀ b : TorusBond (n * R.params.side),
    ‖(minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse b : ℍ[ℝ])‖ < Real.pi
  regular_outer : IsLocallyOrthantClosed S₀ 2047
  regular_cut : IsLocallyOrthantClosed S 2047
section Glue
variable {s : ChartSetting R n} {c : SettingCore R n} {K : Finset (TorusSite (n * R.params.side))} {D : ℕ}
  {S₀ S : Finset (TorusSite n)} {g s' : ℝ}
theorem field_extendByZero_of_not_mem (Nb : Finset (TorusSite n)) (ζ : s.freeNear Nb → EuclideanSpace ℝ (Fin 3))
    (x : TorusSite (n * R.params.side)) (i : Fin 4) (hx : parentBlock R.params.side x ∉ Nb) :
    s.field (s.extendByZero Nb ζ) x i = s.field 0 x i := by
  classical
  unfold ChartSetting.field
  split_ifs with h
  · have hn : (⟨(x, i), h⟩ : s.free) ∉ s.freeNear Nb := by
      intro hm
      exact hx (Finset.mem_filter.mp hm).2
    have e : s.extendByZero Nb ζ ⟨(x, i), h⟩ = 0 := by
      unfold ChartSetting.extendByZero
      rw [dif_neg hn]
    rw [e]
    rfl
  · rfl
theorem inBalls_zero (hρ : 0 ≤ R.ballRadius) : s.InBalls 0 := by
  intro b
  change ‖((toImaginary (0 : EuclideanSpace ℝ (Fin 3)) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ R.ballRadius
  rw [toImaginary_zero]
  simpa using hρ
theorem mem_pieceSites_of_mem_hotSites (hb : NearPieceData s c K D S₀ S g s') {z : TorusSite (n * R.params.side)}
    (hz : z ∈ torusHotSites R.params s.fine) : z ∈ pieceSites s c := by
  classical
  have hρ : 0 ≤ R.ballRadius := by
    have := hb.sizes.admissible.σ_pos
    unfold StepSetup.ballRadius
    positivity
  have hh := hb.admissible.isHull 0 (inBalls_zero hρ)
  have hsame := hb.admissible.hotLumps_eq 0 (inBalls_zero hρ)
  have hz' : z ∈ torusHotSites R.params (s.field 0) := by
    unfold torusHotSites
    rw [hsame]
    exact hz
  have : z ∈ s.support := hh.1 ((mem_thickening _ _ _).mpr ⟨z, hz', by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
  exact Finset.mem_union_left _ (Finset.mem_union_right _ this)
theorem side_dvd_fine : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
theorem lump_subset_piece (hb : NearPieceData s c K D S₀ S g s') {l : Finset (TorusSite (n * R.params.side))}
    (hl : l ∈ torusHotLumps R.params s.fine) {z : TorusSite (n * R.params.side)} (hz : z ∈ l)
    {u : TorusSite (n * R.params.side)} (hu : u ∈ K) (hd : _root_.YangMills.Construction.TorusFields.supDist z u ≤ 9 * R.range) : l ⊆ K := by
  intro z' hz'
  have h1 := _root_.YangMills.Construction.TorusLumps.supDist_lt_of_mem_torusHotLumps hb.sizes.admissible side_dvd_fine hl hz hz'
  have hbig := hb.sizes.range_large
  have h2 : _root_.YangMills.Construction.TorusFields.supDist u z' ≤ 10 * R.range := by
    have := _root_.YangMills.Construction.TorusFields.supDist_triangle u z z'
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm u z] at this
    omega
  exact mem_piece_of_supDist_le hb.piece hb.sizes.range_le hu
    (mem_pieceSites_of_mem_hotSites hb (TorusLumps.mem_torusHotSites_iff.mpr ⟨l, hl, hz'⟩)) h2
end Glue
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
variable {n : ℕ} [NeZero n] {R : StepSetup} {s : ChartSetting R n} {c : SettingCore R n}
  {K : Finset (TorusSite (n * R.params.side))} {D : ℕ} {S₀ S : Finset (TorusSite n)} {g s' : ℝ}
open GroupMoves TorusMinimizer ShareStability
theorem supDist_parentBlock_add_unitStep_le (hb : NearPieceData s c K D S₀ S g s') (x : TorusSite (n * R.params.side))
    (i : Fin 4) :
    _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side (x + unitStep (n * R.params.side) i)) (parentBlock R.params.side x) ≤ 1 := by
  have h1 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one R.params.side (x + unitStep (n * R.params.side) i) x
  have h2 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le x i
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h2
  have hL := hb.sizes.admissible.L_ge
  have h3 : _root_.YangMills.Construction.TorusFields.supDist (x + unitStep (n * R.params.side) i) x / R.params.side = 0 := Nat.div_eq_of_lt (by omega)
  omega
theorem thickening_mono {m m' : ℕ} (h : m ≤ m') {X : Finset (TorusSite n)} : thickening m X ⊆ thickening m' X := by
  intro z hz
  obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp hz
  exact (mem_thickening _ _ _).mpr ⟨x, hx, hd.trans h⟩
theorem mem_thickening_add {m e : ℕ} {X : Finset (TorusSite n)} {z z' : TorusSite n} (hz : z ∈ thickening m X)
    (hd : _root_.YangMills.Construction.TorusFields.supDist z' z ≤ e) : z' ∈ thickening (m + e) X := by
  obtain ⟨x, hx, h⟩ := (mem_thickening _ _ _).mp hz
  refine (mem_thickening _ _ _).mpr ⟨x, hx, ?_⟩
  have := _root_.YangMills.Construction.TorusFields.supDist_triangle z' z x
  omega
theorem mem_thickening_self (m : ℕ) {X : Finset (TorusSite n)} {z : TorusSite n} (hz : z ∈ X) : z ∈ thickening m X :=
  (mem_thickening _ _ _).mpr ⟨z, hz, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩
abbrev nearPieceField (s : ChartSetting R n) (Nb : Finset (TorusSite n)) (ζ : s.freeNear Nb → EuclideanSpace ℝ (Fin 3)) :
    TorusField (n * R.params.side) := s.field (s.extendByZero Nb ζ)
abbrev minimizerOn (s : ChartSetting R n) (S : Finset (TorusSite n)) : TorusField (n * R.params.side) :=
  minimizingField R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse
abbrev splicedField (s : ChartSetting R n) (K : Finset (TorusSite (n * R.params.side))) (D : ℕ) (S : Finset (TorusSite n))
    (ζ : s.freeNear (blocksNear R.params.side R.range K) → EuclideanSpace ℝ (Fin 3)) : TorusField (n * R.params.side) :=
  glueFields R.params.side (thickening D (blocksNear R.params.side R.range K)) (nearPieceField s _ ζ) (minimizerOn s S)
variable (ζ : s.freeNear (blocksNear R.params.side R.range K) → EuclideanSpace ℝ (Fin 3))
theorem splicedField_of_mem (x : TorusSite (n * R.params.side)) (i : Fin 4)
    (h : parentBlock R.params.side x ∈ thickening D (blocksNear R.params.side R.range K)) :
    splicedField s K D S ζ x i = nearPieceField s _ ζ x i := by
  classical
  simp only [splicedField, glueFields, if_pos h]
theorem splicedField_of_not_mem (x : TorusSite (n * R.params.side)) (i : Fin 4)
    (h : parentBlock R.params.side x ∉ thickening D (blocksNear R.params.side R.range K)) :
    splicedField s K D S ζ x i = minimizerOn s S x i := by
  classical
  simp only [splicedField, glueFields, if_neg h]
theorem exists_splicedField_eq (hb : NearPieceData s c K D S₀ S g s') (x : TorusSite (n * R.params.side)) (i : Fin 4)
    (h1 : parentBlock R.params.side x ∉ blocksNear R.params.side R.range K)
    (h3 : parentBlock R.params.side (x + unitStep (n * R.params.side) i) ∉ blocksNear R.params.side R.range K) :
    ∃ v : imaginaryQuaternions, ‖(v : ℍ[ℝ])‖ ≤ 2 * g ∧ splicedField s K D S ζ x i = expUnit v * minimizerOn s S x i := by
  classical
  by_cases hz : parentBlock R.params.side x ∈ thickening D (blocksNear R.params.side R.range K)
  · rw [splicedField_of_mem ζ x i hz, nearPieceField, field_extendByZero_of_not_mem _ _ x i h1]
    have hz4 := thickening_mono (by omega : D ≤ D + 4) hz
    have hz' : parentBlock R.params.side (x + unitStep (n * R.params.side) i) ∈
        thickening (D + 4) (blocksNear R.params.side R.range K) :=
      thickening_mono (by omega) (mem_thickening_add hz (_root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_add_unitStep_le hb x i))
    have n1 := not_mem_storedBlockSet_of_zone (s := s) (c := c) hb.sizes hb.piece hb.two_le hz4 h1
      (by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega)
    have n2 := not_mem_storedBlockSet_of_zone (s := s) (c := c) hb.sizes hb.piece hb.two_le hz' h3
      (by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega)
    exact exists_field_zero_eq hb.sizes.admissible.L_odd hb.two_le hb.admissible hb.core hb.marked hb.gap_nonneg
      hb.frames_near x i n1 n2
  · rw [splicedField_of_not_mem ζ x i hz]
    refine ⟨0, by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb.gap_nonneg, ?_⟩
    rw [_root_.YangMills.Construction.ClusterExpansionOfAStep.GroupMoves.expUnit_zero_eq_one, one_mul]
theorem norm_sub_le_of_eq_mul {v : imaginaryQuaternions} {ε : ℝ} (hv : ‖(v : ℍ[ℝ])‖ ≤ ε) {A B : UnitQuaternion}
    (h : A = expUnit v * B) : ‖(A : ℍ[ℝ]) - B‖ ≤ ε := by
  rw [h]
  exact (norm_mul_expUnit_sub_le v B).trans hv
theorem curvature_splicedField_cases (hb : NearPieceData s c K D S₀ S g s') (x : TorusSite (n * R.params.side))
    (μ ν : Fin 4) :
    (curvature (splicedField s K D S ζ) x μ ν = curvature (nearPieceField s _ ζ) x μ ν ∧
        parentBlock R.params.side x ∈ thickening (D - 2) (blocksNear R.params.side R.range K)) ∨
      (curvature (splicedField s K D S ζ) x μ ν ≤ curvature (minimizerOn s S) x μ ν + 8 * g ∧
        ∀ z ∈ plaquetteVertices x μ ν, parentBlock R.params.side z ∉ blocksNear R.params.side R.range K) := by
  classical
  have hD := hb.depth_ge
  have bm : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side (x + unitStep (n * R.params.side) μ)) (parentBlock R.params.side x) ≤ 1 :=
    _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_add_unitStep_le hb x μ
  have bn : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side (x + unitStep (n * R.params.side) ν)) (parentBlock R.params.side x) ≤ 1 :=
    _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_add_unitStep_le hb x ν
  have bmn : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side (x + unitStep (n * R.params.side) μ + unitStep (n * R.params.side) ν))
      (parentBlock R.params.side x) ≤ 2 := by
    have := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_add_unitStep_le hb (x + unitStep (n * R.params.side) μ) ν
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle
      (parentBlock R.params.side (x + unitStep (n * R.params.side) μ + unitStep (n * R.params.side) ν))
      (parentBlock R.params.side (x + unitStep (n * R.params.side) μ)) (parentBlock R.params.side x)
    omega
  have bnm : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side (x + unitStep (n * R.params.side) ν + unitStep (n * R.params.side) μ))
      (parentBlock R.params.side x) ≤ 2 := by
    have := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_add_unitStep_le hb (x + unitStep (n * R.params.side) ν) μ
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle
      (parentBlock R.params.side (x + unitStep (n * R.params.side) ν + unitStep (n * R.params.side) μ))
      (parentBlock R.params.side (x + unitStep (n * R.params.side) ν)) (parentBlock R.params.side x)
    omega
  by_cases hz : parentBlock R.params.side x ∈ thickening (D - 2) (blocksNear R.params.side R.range K)
  · left
    refine ⟨?_, hz⟩
    have e1 := splicedField_of_mem (S := S) (D := D) ζ x μ (thickening_mono (by omega) hz)
    have e2 := splicedField_of_mem (S := S) (D := D) ζ (x + unitStep (n * R.params.side) μ) ν
      (thickening_mono (by omega) (mem_thickening_add hz bm))
    have e3 := splicedField_of_mem (S := S) (D := D) ζ (x + unitStep (n * R.params.side) ν) μ
      (thickening_mono (by omega) (mem_thickening_add hz bn))
    have e4 := splicedField_of_mem (S := S) (D := D) ζ x ν (thickening_mono (by omega) hz)
    unfold curvature holonomy
    rw [e1, e2, e3, e4]
  · right
    have off : ∀ Z : TorusSite n, _root_.YangMills.Construction.TorusFields.supDist Z (parentBlock R.params.side x) ≤ 2 → Z ∉ blocksNear R.params.side R.range K := by
      intro Z hZ hin
      apply hz
      refine (mem_thickening _ _ _).mpr ⟨Z, hin, ?_⟩
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
      omega
    have o0 : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side x) (parentBlock R.params.side x) ≤ 2 := by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega
    have hc : ∀ z ∈ plaquetteVertices x μ ν, parentBlock R.params.side z ∉ blocksNear R.params.side R.range K := by
      intro z hz'
      simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz'
      rcases hz' with rfl | rfl | rfl | rfl
      · exact off _ o0
      · exact off _ (by omega)
      · exact off _ (by omega)
      · exact off _ bmn
    refine ⟨?_, hc⟩
    obtain ⟨v1, hv1, m1⟩ := exists_splicedField_eq (S := S) ζ hb x μ (off _ o0) (off _ (by omega))
    obtain ⟨v2, hv2, m2⟩ := exists_splicedField_eq (S := S) ζ hb (x + unitStep (n * R.params.side) μ) ν
      (off _ (by omega)) (off _ bmn)
    obtain ⟨v3, hv3, m3⟩ := exists_splicedField_eq (S := S) ζ hb (x + unitStep (n * R.params.side) ν) μ
      (off _ (by omega)) (off _ bnm)
    obtain ⟨v4, hv4, m4⟩ := exists_splicedField_eq (S := S) ζ hb x ν (off _ o0) (off _ (by omega))
    have := TopLevelSites.curvature_le_add (splicedField s K D S ζ) (minimizerOn s S) x μ ν
    have n1 := norm_sub_le_of_eq_mul hv1 m1
    have n2 := norm_sub_le_of_eq_mul hv2 m2
    have n3 := norm_sub_le_of_eq_mul hv3 m3
    have n4 := norm_sub_le_of_eq_mul hv4 m4
    linarith
theorem mem_sitesInBlocks {L : ℕ} [NeZero L] {X : Finset (TorusSite n)} {z : TorusSite (n * L)} :
    z ∈ sitesInBlocks L X ↔ parentBlock L z ∈ X := by apply _root_.YangMills.Construction.CongruentBoxes.mem_sitesInBlocks <;> assumption
theorem hot_of_splicedField (hb : NearPieceData s c K D S₀ S g s') {x : TorusSite (n * R.params.side)} {μ ν : Fin 4}
    (hμν : μ < ν) (hcorner : ∀ z ∈ plaquetteVertices x μ ν, z ∈ sitesInBlocks R.params.side S₀)
    (hhot : R.params.threshold ≤ curvature (splicedField s K D S ζ) x μ ν) :
    R.params.threshold ≤ curvature (nearPieceField s _ ζ) x μ ν ∧
      parentBlock R.params.side x ∈ thickening (D - 2) (blocksNear R.params.side R.range K) := by
  rcases curvature_splicedField_cases ζ hb x μ ν with ⟨e, h⟩ | ⟨hle, hoff⟩
  · exact ⟨e ▸ hhot, h⟩
  · exfalso
    have hc := hb.cold x μ ν hμν (fun z hz => mem_sitesInBlocks.mpr
      (hb.rest_sub _ (mem_sitesInBlocks.mp (hcorner z hz)) (hoff z hz)))
    have := hb.small
    linarith
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
variable {n : ℕ} [NeZero n] {R : StepSetup} {s : ChartSetting R n} {c : SettingCore R n}
  {K : Finset (TorusSite (n * R.params.side))} {D : ℕ} {S₀ S : Finset (TorusSite n)} {g s' : ℝ}
variable (ζ : s.freeNear (blocksNear R.params.side R.range K) → EuclideanSpace ℝ (Fin 3))
open GroupMoves TorusMinimizer ShareStability
theorem supDist_parentBlock_corner_le (hb : NearPieceData s c K D S₀ S g s') {x z : TorusSite (n * R.params.side)}
    {μ ν : Fin 4} (hz : z ∈ plaquetteVertices x μ ν) :
    _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side z) (parentBlock R.params.side x) ≤ 2 := by
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
  have bm := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_add_unitStep_le hb x μ
  have bn := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_add_unitStep_le hb x ν
  rcases hz with rfl | rfl | rfl | rfl
  · rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega
  · omega
  · omega
  · have := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_add_unitStep_le hb (x + unitStep (n * R.params.side) μ) ν
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle
      (parentBlock R.params.side (x + unitStep (n * R.params.side) μ + unitStep (n * R.params.side) ν))
      (parentBlock R.params.side (x + unitStep (n * R.params.side) μ)) (parentBlock R.params.side x)
    omega
theorem mem_splicedLumps_iff (hb : NearPieceData s c K D S₀ S g s') (hζ : s.InBalls (s.extendByZero _ ζ))
    (l : Finset ((stepBlockFrame R.params.side n).Site 0)) :
    l ∈ HoleOnTori.stepHotLumps R.params (sitesInBlocks R.params.side S₀) (splicedField s K D S ζ) ↔
      (open Classical in l.image (toTorusSite (n * R.params.side))) ∈ s.lumpsInPiece K := by
  classical
  have hfit := hb.sizes.admissible
  have hLn : R.params.side ∣ n * R.params.side := side_dvd_fine
  unfold HoleOnTori.stepHotLumps
  rw [mem_hotLumps_readAtLevel_iff hfit hLn period_stepBlockFrame_zero]
  have hsame := hb.admissible.hotLumps_eq _ hζ
  constructor
  · rintro ⟨x, μ, ν, hlt, hX, hσ, z, hz, hl⟩
    obtain ⟨h1, h3⟩ := hot_of_splicedField ζ hb hlt hX hσ
    have hzD : parentBlock R.params.side z ∈ thickening (D + 4) (blocksNear R.params.side R.range K) :=
      thickening_mono (by have := hb.depth_ge; omega) (mem_thickening_add h3 (_root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_corner_le hb hz))
    obtain ⟨u, hu, hnear⟩ := exists_near_of_mem_thickening hb.sizes le_rfl hzD
    have hlump : torusLumpOf R.params z ∈ torusHotLumps R.params s.fine := by
      rw [← hsame]
      exact (mem_torusHotLumps_iff R.params hfit hLn _ _).mpr ⟨x, μ, ν, hlt, h1, z, hz, rfl⟩
    have hsub := lump_subset_piece hb hlump (mem_torusLumpOf_self z) hu
      (by have := hnear z rfl; have := hb.sizes.range_large; omega)
    rw [hl]
    exact Finset.mem_filter.mpr ⟨hlump, hsub⟩
  · intro hl
    obtain ⟨h1, hsub⟩ := Finset.mem_filter.mp hl
    rw [← hsame] at h1
    obtain ⟨x, μ, ν, hlt, hσ, z, hz, e⟩ := (mem_torusHotLumps_iff R.params hfit hLn _ _).mp h1
    have hzK : z ∈ K := hsub (e ▸ mem_torusLumpOf_self z)
    have hzN : parentBlock R.params.side z ∈ blocksNear R.params.side R.range K :=
      mem_blocksNear.mpr ⟨z, rfl, z, hzK, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩
    have hcb := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_corner_le hb hz
    refine ⟨x, μ, ν, hlt, fun z' hz' => ?_, ?_, z, hz, e⟩
    · refine mem_sitesInBlocks.mpr (hb.zone_sub _ ?_)
      have h3 := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_corner_le hb hz'
      refine (mem_thickening _ _ _).mpr ⟨_, hzN, ?_⟩
      have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side z') (parentBlock R.params.side x) (parentBlock R.params.side z)
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm (parentBlock R.params.side x) (parentBlock R.params.side z)] at h4
      have := hb.depth_ge
      omega
    · rcases curvature_splicedField_cases (S := S) ζ hb x μ ν with ⟨h5, -⟩ | ⟨-, hoff⟩
      · rw [h5]
        exact hσ
      · exact absurd hzN (hoff z hz)
theorem image_toTorusSite_injective :
    Function.Injective (fun l : Finset ((stepBlockFrame R.params.side n).Site 0) =>
      (open Classical in l.image (toTorusSite (n * R.params.side)))) := by
  classical
  exact Finset.image_injective fun a b h => toTorusSite_injective period_stepBlockFrame_zero h
theorem image_toTorusSite_image (l : Finset (TorusSite (n * R.params.side))) :
    (open Classical in (l.image (torusSiteInFrame (stepBlockFrame R.params.side n) 0)).image
      (toTorusSite (n * R.params.side))) = l := by
  classical
  rw [Finset.image_image]
  have : (toTorusSite (n * R.params.side) ∘ torusSiteInFrame (stepBlockFrame R.params.side n) 0 :
      TorusSite (n * R.params.side) → _) = id := by
    funext x
    exact toTorusSite_torusSiteInFrame period_stepBlockFrame_zero x
  rw [this, Finset.image_id]
theorem card_splicedLumps (hb : NearPieceData s c K D S₀ S g s') (hζ : s.InBalls (s.extendByZero _ ζ)) :
    (HoleOnTori.stepHotLumps R.params (sitesInBlocks R.params.side S₀) (splicedField s K D S ζ)).card =
      (s.lumpsInPiece K).card := by
  classical
  refine Finset.card_bij (fun l _ => l.image (toTorusSite (n * R.params.side)))
    (fun l hl => (mem_splicedLumps_iff ζ hb hζ l).mp hl)
    (fun a _ b _ h => image_toTorusSite_injective h) (fun l' hl' => ?_)
  refine ⟨l'.image (torusSiteInFrame (stepBlockFrame R.params.side n) 0), ?_, image_toTorusSite_image l'⟩
  rw [mem_splicedLumps_iff ζ hb hζ, image_toTorusSite_image]
  exact hl'
theorem stepLumpSites_splicedLumps (hb : NearPieceData s c K D S₀ S g s') (hζ : s.InBalls (s.extendByZero _ ζ)) :
    stepLumpSites R.params (HoleOnTori.stepHotLumps R.params (sitesInBlocks R.params.side S₀) (splicedField s K D S ζ)) =
      (s.lumpsInPiece K).biUnion id := by
  classical
  ext z
  simp only [stepLumpSites, Finset.mem_biUnion, id]
  constructor
  · rintro ⟨l, hl, hz⟩
    exact ⟨_, (mem_splicedLumps_iff ζ hb hζ l).mp hl, hz⟩
  · rintro ⟨l', hl', hz⟩
    refine ⟨l'.image (torusSiteInFrame (stepBlockFrame R.params.side n) 0), ?_, ?_⟩
    · rw [mem_splicedLumps_iff ζ hb hζ, image_toTorusSite_image]
      exact hl'
    · rw [image_toTorusSite_image]
      exact hz
section Generic
variable {F : BlockFrame} [NeZero (n * F.blockSide)]
theorem parentBlock_toTorusSite (hn : ∀ i, F.extent i = n) (x : F.Site F.depth) :
    parentBlock F.blockSide (toTorusSite (n * F.blockSide) x) = toTorusSite n (enclosingCell x) := by
  have e1 : enclosingCell (torusSiteInFrame F F.depth (toTorusSite (n * F.blockSide) x)) =
      torusSiteInFrame F F.top (parentBlock F.blockSide (toTorusSite (n * F.blockSide) x)) :=
    enclosingCell_torusSiteInFrame (F := F) (n := n) hn _
  have e2 : torusSiteInFrame F F.depth (toTorusSite (n * F.blockSide) x) = x :=
    torusSiteInFrame_toTorusSite (period_depth_of_extent hn) x
  rw [e2] at e1
  have e3 : toTorusSite n (torusSiteInFrame F F.top (parentBlock F.blockSide (toTorusSite (n * F.blockSide) x))) =
      parentBlock F.blockSide (toTorusSite (n * F.blockSide) x) :=
    toTorusSite_torusSiteInFrame (F := F) (j := F.top) (period_top_of_extent hn) _
  exact e3.symm.trans (congrArg (toTorusSite n) e1.symm)
theorem supDist_parentBlock_of_mem_cutBelow (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (h2 : 2 ≤ n)
    {y : F.Cell} {z : F.Site F.depth} {r : ℕ} (hz : z ∈ cutBelow F.depth (cellBall y r)) :
    _root_.YangMills.Construction.TorusFields.supDist (parentBlock F.blockSide (toTorusSite (n * F.blockSide) z)) (toTorusSite n y) ≤ r := by
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; exact h2
  unfold cutBelow at hz
  obtain ⟨y', hy', hzu⟩ := Finset.mem_biUnion.mp hz
  unfold sitesBelow at hzu
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hzu
  unfold LumpContours.cellBall at hy'
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy'
  have hs1 : F.top - F.depth = 1 := _root_.YangMills.Construction.TopLevelSites.top_sub_depth
  have hcube : h ∈ centredCube F.blockSide := by simpa [hs1] using hh
  have hz' : (siteOfCoords F.depth fun k => (F.blockSide : ℤ) ^ (F.top - F.depth) *
      siteCoords (y + siteOfCoords F.top e) k + h k : F.Site F.depth) =
      cellCentre F.depth (y + siteOfCoords F.top e) + siteOfCoords F.depth h := by
    funext i
    simp [cellCentre, siteOfCoords]
  rw [hz', parentBlock_toTorusSite hn, enclosingCell_centre_add hL hs _ h hcube, toTorusSite_add (period_top_of_extent hn),
    toTorusSite_siteOfCoords (period_top_of_extent hn), _root_.YangMills.Construction.TorusFields.supDist_comm]
  refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => ?_
  have := (_root_.YangMills.Construction.TopLevelSites.mem_centredCube_iff e).mp he i
  rw [halfWidth_two_mul_add_one] at this
  omega
theorem mem_and_subset_iff (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (h2 : 2 ≤ n)
    {h h' : Finset (Finset (F.Site F.depth))} {y : F.Cell} (r : ℕ)
    (key : ∀ l : Finset (F.Site F.depth),
      (∀ z ∈ l, _root_.YangMills.Construction.TorusFields.supDist (parentBlock F.blockSide (toTorusSite (n * F.blockSide) z)) (toTorusSite n y) ≤ r) →
      (l ∈ h ↔ l ∈ h')) (l : Finset (F.Site F.depth)) :
    (l ∈ h ∧ l ⊆ cutBelow F.depth (cellBall y r)) ↔ (l ∈ h' ∧ l ⊆ cutBelow F.depth (cellBall y r)) := by
  constructor
  · rintro ⟨a, b⟩
    exact ⟨(key l fun z hz => _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_of_mem_cutBelow hn hL h2 (b hz)).mp a, b⟩
  · rintro ⟨a, b⟩
    exact ⟨(key l fun z hz => _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_of_mem_cutBelow hn hL h2 (b hz)).mpr a, b⟩
theorem nearbyLumps_congr (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (h2 : 2 ≤ n)
    {h h' : Finset (Finset (F.Site F.depth))} {y : F.Cell}
    (key : ∀ l : Finset (F.Site F.depth),
      (∀ z ∈ l, _root_.YangMills.Construction.TorusFields.supDist (parentBlock F.blockSide (toTorusSite (n * F.blockSide) z)) (toTorusSite n y) ≤ 2) →
      (l ∈ h ↔ l ∈ h')) : nearbyLumps h y = nearbyLumps h' y := by
  classical
  ext l
  unfold nearbyLumps
  simp only [Finset.mem_filter]
  exact mem_and_subset_iff hn hL h2 2 key l
theorem supDist_le_of_subset_cutBelow (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (h2 : 2 ≤ n) {y : F.Cell}
    {r : ℕ} {l : Finset (F.Site F.depth)} (hsub : l ⊆ cutBelow F.depth (cellBall y r)) :
    ∀ z ∈ l, _root_.YangMills.Construction.TorusFields.supDist (parentBlock F.blockSide (toTorusSite (n * F.blockSide) z)) (toTorusSite n y) ≤ r :=
  fun z hz => _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_of_mem_cutBelow hn hL h2 (hsub hz)
theorem nearbyLumps_eq_empty (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (h2 : 2 ≤ n)
    {h : Finset (Finset (F.Site F.depth))} {y : F.Cell}
    (key : ∀ l ∈ h, l.Nonempty →
      ¬ ∀ z ∈ l, _root_.YangMills.Construction.TorusFields.supDist (parentBlock F.blockSide (toTorusSite (n * F.blockSide) z)) (toTorusSite n y) ≤ 2)
    (hne : ∀ l ∈ h, l.Nonempty) : nearbyLumps h y = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro l hl
  unfold nearbyLumps at hl
  obtain ⟨h1, hsub⟩ := Finset.mem_filter.mp hl
  exact key l h1 (hne l h1) (_root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_le_of_subset_cutBelow hn hL h2 hsub)
end Generic
theorem mem_stepHotLumps_iff (hH : TorusFrames.hotLumpsOfStepStatement) (W : TorusField (n * R.params.side))
    (l : Finset ((stepBlockFrame R.params.side n).Site 0)) :
    l ∈ StepCosts.stepHotLumps R.params W ↔
      (open Classical in l.image (toTorusSite (n * R.params.side))) ∈ torusHotLumps R.params W := by
  classical
  rw [((hH R.params n).1 W).1]
  constructor
  · intro h
    exact Finset.mem_image_of_mem _ h
  · intro h
    obtain ⟨l₀, h0, e⟩ := Finset.mem_image.mp h
    rwa [← image_toTorusSite_injective e]
theorem lump_nonempty (hb : NearPieceData s c K D S₀ S g s') {l : Finset (TorusSite (n * R.params.side))}
    (hl : l ∈ torusHotLumps R.params s.fine) : l.Nonempty := by
  obtain ⟨x, μ, ν, _, _, z, _, rfl⟩ := (mem_torusHotLumps_iff R.params hb.sizes.admissible side_dvd_fine _ _).mp hl
  exact ⟨z, mem_torusLumpOf_self z⟩
theorem nonempty_of_image_nonempty {l : Finset ((stepBlockFrame R.params.side n).Site 0)}
    (hl : (open Classical in l.image (toTorusSite (n * R.params.side))).Nonempty) : l.Nonempty := by
  classical
  exact Finset.image_nonempty.mp hl
theorem nearbyLumps_splicedField_of_mem (hH : TorusFrames.hotLumpsOfStepStatement) (hb : NearPieceData s c K D S₀ S g s')
    (hζ : s.InBalls (s.extendByZero _ ζ)) {y : (stepBlockFrame R.params.side n).Cell}
    (hy : toTorusSite n y ∈ thickening D (blocksNear R.params.side R.range K)) :
    nearbyLumps (HoleOnTori.stepHotLumps R.params (sitesInBlocks R.params.side S₀) (splicedField s K D S ζ)) y =
      nearbyLumps (StepCosts.stepHotLumps R.params s.fine) y := by
  classical
  have key : ∀ l : Finset ((stepBlockFrame R.params.side n).Site 0),
      (∀ z ∈ l, _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side (toTorusSite (n * R.params.side) z)) (toTorusSite n y) ≤ 2) →
      (l ∈ HoleOnTori.stepHotLumps R.params (sitesInBlocks R.params.side S₀) (splicedField s K D S ζ) ↔
        l ∈ StepCosts.stepHotLumps R.params s.fine) := by
    intro l hl'
    rw [mem_splicedLumps_iff ζ hb hζ, mem_stepHotLumps_iff hH]
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).1
    · intro h
      refine Finset.mem_filter.mpr ⟨h, ?_⟩
      obtain ⟨z', hz'⟩ := lump_nonempty hb h
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hz'
      have hbl := hl' z hz
      have hD : parentBlock R.params.side (toTorusSite (n * R.params.side) z) ∈
          thickening (D + 4) (blocksNear R.params.side R.range K) :=
        thickening_mono (by omega) (mem_thickening_add hy hbl)
      obtain ⟨u, hu, hnear⟩ := exists_near_of_mem_thickening hb.sizes le_rfl hD
      exact lump_subset_piece hb h hz' hu (by have := hnear _ rfl; have := hb.sizes.range_large; omega)
  exact nearbyLumps_congr (F := stepBlockFrame R.params.side n) (n := n) (fun _ => rfl) hb.sizes.admissible.L_odd
    hb.two_le key
theorem nearbyLumps_splicedField_of_not_mem (hb : NearPieceData s c K D S₀ S g s') (hζ : s.InBalls (s.extendByZero _ ζ))
    {y : (stepBlockFrame R.params.side n).Cell}
    (hy : toTorusSite n y ∉ thickening 2 (blocksNear R.params.side R.range K)) :
    nearbyLumps (HoleOnTori.stepHotLumps R.params (sitesInBlocks R.params.side S₀) (splicedField s K D S ζ)) y = ∅ := by
  classical
  have hne : ∀ l ∈ HoleOnTori.stepHotLumps R.params (sitesInBlocks R.params.side S₀) (splicedField s K D S ζ),
      l.Nonempty := by
    intro l hl
    have hl' := (mem_splicedLumps_iff ζ hb hζ l).mp hl
    exact nonempty_of_image_nonempty (lump_nonempty hb (Finset.mem_filter.mp hl').1)
  refine nearbyLumps_eq_empty (F := stepBlockFrame R.params.side n) (n := n) (fun _ => rfl) hb.sizes.admissible.L_odd
    hb.two_le (fun l h1 hnl hall => ?_) hne
  have hl' := (mem_splicedLumps_iff ζ hb hζ l).mp h1
  obtain ⟨h3, h4⟩ := Finset.mem_filter.mp hl'
  obtain ⟨z, hz⟩ := hnl
  have hall' : ∀ z ∈ l, _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side (toTorusSite (n * R.params.side) z)) (toTorusSite n y) ≤ 2 :=
    hall
  have hbl := hall' z hz
  have hz' : toTorusSite (n * R.params.side) z ∈ l.image (toTorusSite (n * R.params.side)) := Finset.mem_image_of_mem _ hz
  apply hy
  refine (mem_thickening _ _ _).mpr ⟨parentBlock R.params.side (toTorusSite (n * R.params.side) z), ?_, ?_⟩
  · exact mem_blocksNear.mpr ⟨_, rfl, _, h4 hz', by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩
  · rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
    omega
theorem nearbyLumps_fine_eq_empty (hH : TorusFrames.hotLumpsOfStepStatement) (hb : NearPieceData s c K D S₀ S g s')
    {y : (stepBlockFrame R.params.side n).Cell}
    (hy : ∀ Z : TorusSite n, _root_.YangMills.Construction.TorusFields.supDist Z (toTorusSite n y) ≤ 2 → Z ∉ s.storedBlockSet c) :
    nearbyLumps (StepCosts.stepHotLumps R.params s.fine) y = ∅ := by
  classical
  have hne : ∀ l ∈ StepCosts.stepHotLumps R.params s.fine, l.Nonempty := by
    intro l hl
    exact nonempty_of_image_nonempty (lump_nonempty hb ((mem_stepHotLumps_iff hH _ l).mp hl))
  refine nearbyLumps_eq_empty (F := stepBlockFrame R.params.side n) (n := n) (fun _ => rfl) hb.sizes.admissible.L_odd
    hb.two_le (fun l h1 hnl hall => ?_) hne
  have h3 := (mem_stepHotLumps_iff hH _ l).mp h1
  obtain ⟨z, hz⟩ := hnl
  have hz' : toTorusSite (n * R.params.side) z ∈ l.image (toTorusSite (n * R.params.side)) := Finset.mem_image_of_mem _ hz
  have hall' : ∀ z ∈ l, _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side (toTorusSite (n * R.params.side) z)) (toTorusSite n y) ≤ 2 :=
    hall
  refine hy _ (hall' z hz) ((mem_storedBlockSet s c).mpr (Or.inr ⟨_, rfl, _,
    mem_pieceSites_of_mem_hotSites hb (TorusLumps.mem_torusHotSites_iff.mpr ⟨_, h3, hz'⟩), ?_⟩))
  rw [_root_.YangMills.Construction.TorusFields.supDist_self]
  omega
theorem excludedBoxes_congr {F : BlockFrame} {J₀ : ℕ} {h h' : Finset (Finset (F.Site F.depth))} {y : F.Cell}
    (e : nearbyLumps h y = nearbyLumps h' y) : excludedBoxes J₀ h y = excludedBoxes J₀ h' y := by
  classical
  unfold excludedBoxes IsCrowded
  rw [e]
def splicedBases (s : ChartSetting R n) (Z : Finset (TorusSite n)) : BaseChoice R.params.side n :=
  open Classical in
  fun y => if toTorusSite n y ∈ Z then s.bases y else cellCentre (F := stepBlockFrame R.params.side n) 0 y
theorem splicedBases_isBaseChoice (hH : TorusFrames.hotLumpsOfStepStatement) (hb : NearPieceData s c K D S₀ S g s')
    (hζ : s.InBalls (s.extendByZero _ ζ)) :
    IsBaseChoice R.params.baseDepth
      (HoleOnTori.stepHotLumps R.params (sitesInBlocks R.params.side S₀) (splicedField s K D S ζ))
      (splicedBases s (thickening D (blocksNear R.params.side R.range K))) := by
  classical
  intro y
  by_cases hy : toTorusSite n y ∈ thickening D (blocksNear R.params.side R.range K)
  · have e := nearbyLumps_splicedField_of_mem ζ hH hb hζ hy
    have hbs := hb.marked.bases y
    have hv : splicedBases s (thickening D (blocksNear R.params.side R.range K)) y = s.bases y := by
      simp only [splicedBases, if_pos hy]
    rw [hv]
    unfold IsCrowded
    rw [e, excludedBoxes_congr e]
    exact hbs
  · have e := nearbyLumps_splicedField_of_not_mem ζ hb hζ (fun h => hy (thickening_mono (by have := hb.depth_ge; omega) h))
    have hv : splicedBases s (thickening D (blocksNear R.params.side R.range K)) y =
        cellCentre (F := stepBlockFrame R.params.side n) 0 y := by
      simp only [splicedBases, if_neg hy]
    rw [hv]
    exact ⟨fun _ => rfl, fun h => absurd (Or.inl e) h⟩
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
section Frames
variable {F : BlockFrame}
theorem valMinAbs_sub_cast {p q : ℕ} (hp : p = q) [NeZero p] (a b : ZMod p) :
    (a - b).valMinAbs = (((a.cast : ℤ) : ZMod q) - ((b.cast : ℤ) : ZMod q)).valMinAbs := by apply _root_.YangMills.Construction.TorusFrame.valMinAbs_sub_castInt <;> assumption
theorem frameSupDist_eq_supDist {j N : ℕ} [NeZero N] (hp : ∀ i, F.period j i = N) (x y : F.Site j) :
    LumpContours.supDist x y = _root_.YangMills.Construction.TorusFields.supDist (toTorusSite N x) (toTorusSite N y) := by
  unfold LumpContours.supDist TorusFields.supDist
  refine Finset.sup_congr rfl fun i _ => ?_
  have := period_neZero hp i
  rw [valMinAbs_sub_cast (hp i)]
  rfl
theorem mem_sitesBelow_iff (y : F.Cell) (x : F.Site F.depth) :
    x ∈ sitesBelow F.depth y ↔ ∃ h ∈ centredCube F.blockSide, x = cellCentre F.depth y + siteOfCoords F.depth h := by apply _root_.YangMills.Construction.TorusContours.mem_sitesBelow_iff <;> assumption
theorem enclosingCell_of_mem_sitesBelow (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {y : F.Cell}
    {x : F.Site F.depth} (hx : x ∈ sitesBelow F.depth y) : enclosingCell x = y := by
  obtain ⟨h, hh, rfl⟩ := (mem_sitesBelow_iff y x).mp hx
  exact enclosingCell_centre_add hL hs y h hh
theorem zero_mem_centredCube (hL : 0 < F.blockSide) : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.zero_mem_centredCube <;> assumption
theorem siteOfCoords_zero' {j : ℕ} : (siteOfCoords j (0 : Fin 4 → ℤ) : F.Site j) = 0 := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_zero <;> assumption
theorem cellCentre_mem_sitesBelow (hL : 0 < F.blockSide) (y : F.Cell) : cellCentre F.depth y ∈ sitesBelow F.depth y :=
  (mem_sitesBelow_iff y _).mpr ⟨0, zero_mem_centredCube hL, by rw [siteOfCoords_zero', add_zero]⟩
theorem mem_sitesBelow_of_isBaseChoice (hL : 0 < F.blockSide) {J₀ : ℕ} {h : Finset (Finset (F.Site F.depth))}
    {b : F.Cell → F.Site F.depth} (hB : IsBaseChoice J₀ h b) (y : F.Cell) : b y ∈ sitesBelow F.depth y := by
  by_cases hc : nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y
  · rw [(hB y).1 hc]
    exact cellCentre_mem_sitesBelow hL y
  · exact ((hB y).2 hc).1
theorem natAbs_minimalOffset_le (hper : ∀ i, NeZero (F.period F.depth i)) {y : F.Cell} {x : F.Site F.depth}
    (hx : x ∈ sitesBelow F.depth y) {q : Fin 4 → ℤ} (hq : q ∈ centredCube F.blockSide) (i : Fin 4) :
    (_root_.YangMills.Construction.LumpContours.minimalOffset x (cellCentre F.depth y + siteOfCoords F.depth q) i).natAbs ≤ F.blockSide := by
  obtain ⟨h, hh, rfl⟩ := (mem_sitesBelow_iff y x).mp hx
  haveI := hper i
  unfold _root_.YangMills.Construction.LumpContours.minimalOffset
  have e : (cellCentre F.depth y + siteOfCoords F.depth q - (cellCentre F.depth y + siteOfCoords F.depth h) :
      F.Site F.depth) i = ((q i - h i : ℤ) : ZMod (F.period F.depth i)) := by
    simp [siteOfCoords]
  rw [e]
  refine (_root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le _).trans ?_
  have h1 := (_root_.YangMills.Construction.TopLevelSites.mem_centredCube_iff q).mp hq i
  have h2 := (_root_.YangMills.Construction.TopLevelSites.mem_centredCube_iff h).mp hh i
  unfold halfWidth at h1 h2
  omega
theorem length_contourPath_le (hper : ∀ i, NeZero (F.period F.depth i)) {b : F.Cell → F.Site F.depth}
    {c : F.Cell × Fin 4} (h1 : b c.1 ∈ sitesBelow F.depth c.1)
    (h2 : b (c.1 + BlockAverages.unitStep F.top c.2) ∈ sitesBelow F.depth (c.1 + BlockAverages.unitStep F.top c.2))
    {q : Fin 4 → ℤ} (hq : q ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    (contourPath b c q π).length ≤ 9 * F.blockSide := by
  unfold contourPath
  simp only [List.length_append, List.length_replicate, _root_.YangMills.Construction.ClusterExpansionOfAStep.ContourStability.length_reversePath]
  have a1 := _root_.YangMills.Construction.ClusterExpansionOfAStep.ContourStability.length_axisPath_le _ π F.blockSide (natAbs_minimalOffset_le hper h1 hq)
  have a2 := _root_.YangMills.Construction.ClusterExpansionOfAStep.ContourStability.length_axisPath_le _ π F.blockSide (natAbs_minimalOffset_le hper h2 hq)
  omega
theorem pathHolonomy_eq_of_agree {j : ℕ} (hper : ∀ i, NeZero (F.period j i)) {X X' : F.GaugeField j}
    (l : List PathStep) (x : F.Site j)
    (h : ∀ z, LumpContours.supDist z x ≤ l.length → ∀ i, X z i = X' z i) : pathHolonomy X x l = pathHolonomy X' x l := by
  have := _root_.YangMills.Construction.ClusterExpansionOfAStep.ContourStability.norm_pathHolonomy_sub_le (X := X) (X' := X') hper 0 le_rfl l x (fun z hz i => by rw [h z hz i]; simp)
  simp only [mul_zero, norm_le_zero_iff, sub_eq_zero] at this
  exact Subtype.ext this
theorem usedContours_congr {J₀ : ℕ} {h h' : Finset (Finset (F.Site F.depth))} {b b' : F.Cell → F.Site F.depth}
    {c : F.Cell × Fin 4} (l1 : nearbyLumps h c.1 = nearbyLumps h' c.1)
    (l2 : nearbyLumps h (c.1 + BlockAverages.unitStep F.top c.2) = nearbyLumps h' (c.1 + BlockAverages.unitStep F.top c.2))
    (b1 : b c.1 = b' c.1)
    (b2 : b (c.1 + BlockAverages.unitStep F.top c.2) = b' (c.1 + BlockAverages.unitStep F.top c.2)) :
    usedContours J₀ h b c = usedContours J₀ h' b' c := by
  classical
  have hsteps : ∀ q π, contourPath b c q π = contourPath b' c q π := by
    intro q π
    unfold contourPath
    rw [b1, b2]
  have hgood : ∀ q π, IsGoodContour J₀ h b c q π ↔ IsGoodContour J₀ h' b' c q π := by
    intro q π
    unfold IsGoodContour
    rw [hsteps, b1, excludedBoxes_congr l1, excludedBoxes_congr l2]
  have hc1 : IsCrowded J₀ h c.1 ↔ IsCrowded J₀ h' c.1 := by
    unfold IsCrowded
    rw [l1]
  have hc2 : IsCrowded J₀ h (c.1 + BlockAverages.unitStep F.top c.2) ↔
      IsCrowded J₀ h' (c.1 + BlockAverages.unitStep F.top c.2) := by
    unfold IsCrowded
    rw [l2]
  have hf : (allContours F).filter (fun e => IsGoodContour J₀ h b c e.1 e.2) =
      (allContours F).filter (fun e => IsGoodContour J₀ h' b' c e.1 e.2) :=
    Finset.filter_congr fun e _ => hgood e.1 e.2
  unfold usedContours
  simp only [hc1, hc2, hf]
theorem contourMean_congr (hper : ∀ i, NeZero (F.period F.depth i)) {J₀ : ℕ} {h h' : Finset (Finset (F.Site F.depth))}
    {b b' : F.Cell → F.Site F.depth} {X X' : F.GaugeField F.depth} {c : F.Cell × Fin 4}
    (l1 : nearbyLumps h c.1 = nearbyLumps h' c.1)
    (l2 : nearbyLumps h (c.1 + BlockAverages.unitStep F.top c.2) = nearbyLumps h' (c.1 + BlockAverages.unitStep F.top c.2))
    (b1 : b c.1 = b' c.1)
    (b2 : b (c.1 + BlockAverages.unitStep F.top c.2) = b' (c.1 + BlockAverages.unitStep F.top c.2))
    (u1 : b c.1 ∈ sitesBelow F.depth c.1)
    (u2 : b (c.1 + BlockAverages.unitStep F.top c.2) ∈ sitesBelow F.depth (c.1 + BlockAverages.unitStep F.top c.2))
    (hX : ∀ z, LumpContours.supDist z (b c.1) ≤ 9 * F.blockSide → ∀ i, X z i = X' z i) :
    contourMean J₀ h b X c = contourMean J₀ h' b' X' c := by
  classical
  have hsteps : ∀ q π, contourPath b c q π = contourPath b' c q π := by
    intro q π
    unfold contourPath
    rw [b1, b2]
  unfold contourMean
  rw [← usedContours_congr l1 l2 b1 b2]
  congr 1
  refine Finset.sum_congr rfl fun e he => ?_
  have hq : e.1 ∈ centredCube F.blockSide := by
    have hall : e ∈ allContours F := by
      unfold usedContours at he
      split_ifs at he
      · exact he
      · exact (Finset.mem_filter.mp he).1
    exact (Finset.mem_product.mp hall).1
  rw [← hsteps, ← b1]
  rw [pathHolonomy_eq_of_agree hper (X' := X') _ _ fun z hz i =>
    hX z (hz.trans (length_contourPath_le hper u1 u2 hq e.2)) i]
theorem contourFit_congr (hper : ∀ i, NeZero (F.period F.depth i)) {J₀ : ℕ} {h h' : Finset (Finset (F.Site F.depth))}
    {b b' : F.Cell → F.Site F.depth} {X X' : F.GaugeField F.depth} (V : F.GaugeField F.top) {c : F.Cell × Fin 4}
    (l1 : nearbyLumps h c.1 = nearbyLumps h' c.1)
    (l2 : nearbyLumps h (c.1 + BlockAverages.unitStep F.top c.2) = nearbyLumps h' (c.1 + BlockAverages.unitStep F.top c.2))
    (b1 : b c.1 = b' c.1)
    (b2 : b (c.1 + BlockAverages.unitStep F.top c.2) = b' (c.1 + BlockAverages.unitStep F.top c.2))
    (u1 : b c.1 ∈ sitesBelow F.depth c.1)
    (u2 : b (c.1 + BlockAverages.unitStep F.top c.2) ∈ sitesBelow F.depth (c.1 + BlockAverages.unitStep F.top c.2))
    (hX : ∀ z, LumpContours.supDist z (b c.1) ≤ 9 * F.blockSide → ∀ i, X z i = X' z i) :
    contourFit J₀ h b X V c = contourFit J₀ h' b' X' V c := by
  unfold contourFit
  rw [contourMean_congr hper l1 l2 b1 b2 u1 u2 hX]
end Frames
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
variable {n : ℕ} [NeZero n] {R : StepSetup} {s : ChartSetting R n} {c : SettingCore R n}
  {K : Finset (TorusSite (n * R.params.side))} {D : ℕ} {S₀ S : Finset (TorusSite n)} {g s' : ℝ}
variable (ζ : s.freeNear (blocksNear R.params.side R.range K) → EuclideanSpace ℝ (Fin 3))
open GroupMoves TorusMinimizer ShareStability ContourStability
open GroupMoves TorusMinimizer ShareStability ContourStability
theorem period_stepBlockFrame_neZero (L : ℕ) [NeZero L] :
    ∀ i, NeZero ((stepBlockFrame L n).period (stepBlockFrame L n).depth i) :=
  fun i => period_neZero period_stepBlockFrame_zero i
theorem torusHotLumps_nearPieceField (hb : NearPieceData s c K D S₀ S g s') (hζ : s.InBalls (s.extendByZero _ ζ)) :
    torusHotLumps R.params (nearPieceField s _ ζ) = torusHotLumps R.params s.fine := hb.admissible.hotLumps_eq _ hζ
theorem stepHotLumps_congr (hH : TorusFrames.hotLumpsOfStepStatement) {W W' : TorusField (n * R.params.side)}
    (h : torusHotLumps R.params W = torusHotLumps R.params W') :
    StepCosts.stepHotLumps R.params W = StepCosts.stepHotLumps R.params W' := by
  classical
  ext l
  rw [mem_stepHotLumps_iff hH, mem_stepHotLumps_iff hH, h]
theorem toTorusSite_cell (y : TorusSite n) (L : ℕ) :
    toTorusSite n (torusSiteInFrame (stepBlockFrame L n) (stepBlockFrame L n).top y) = y :=
  toTorusSite_torusSiteInFrame (F := stepBlockFrame L n) (j := (stepBlockFrame L n).top)
    (period_top_of_extent (fun _ => rfl)) y
theorem toTorusSite_cell_add (y : TorusSite n) (L : ℕ) (i : Fin 4) :
    toTorusSite n (torusSiteInFrame (stepBlockFrame L n) (stepBlockFrame L n).top y +
      BlockAverages.unitStep (stepBlockFrame L n).top i : (stepBlockFrame L n).Cell) = y + unitStep n i := by
  rw [toTorusSite_add (F := stepBlockFrame L n) (period_top_of_extent (fun _ => rfl)),
    toTorusSite_unitStep (F := stepBlockFrame L n) (period_top_of_extent (fun _ => rfl)), toTorusSite_cell]
theorem supDist_parentBlock_le_ten (hb : NearPieceData s c K D S₀ S g s')
    {z x : (stepBlockFrame R.params.side n).Site (stepBlockFrame R.params.side n).depth} {Y : TorusSite n}
    (hx : x ∈ sitesBelow (stepBlockFrame R.params.side n).depth
      (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top Y))
    (hz : LumpContours.supDist z x ≤ 9 * R.params.side) :
    _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side (toTorusSite (n * R.params.side) z)) Y ≤ 10 := by
  have hL : Odd (stepBlockFrame R.params.side n).blockSide := hb.sizes.admissible.L_odd
  have hs : ∀ i, 2 ≤ (stepBlockFrame R.params.side n).extent i := fun _ => hb.two_le
  have h1 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one R.params.side (toTorusSite (n * R.params.side) z)
    (toTorusSite (n * R.params.side) x)
  have e1 : parentBlock R.params.side (toTorusSite (n * R.params.side) x) = Y := by
    have := parentBlock_toTorusSite (F := stepBlockFrame R.params.side n) (n := n) (fun _ => rfl) x
    have e2 : enclosingCell x = torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top Y :=
      enclosingCell_of_mem_sitesBelow hL hs hx
    rw [e2, toTorusSite_cell] at this
    exact this
  rw [e1] at h1
  have h3 : _root_.YangMills.Construction.TorusFields.supDist (toTorusSite (n * R.params.side) z) (toTorusSite (n * R.params.side) x) ≤ 9 * R.params.side := by
    have := frameSupDist_eq_supDist (F := stepBlockFrame R.params.side n) (j := (stepBlockFrame R.params.side n).depth)
      period_stepBlockFrame_zero z x
    rw [← this]
    exact hz
  have h4 : _root_.YangMills.Construction.TorusFields.supDist (toTorusSite (n * R.params.side) z) (toTorusSite (n * R.params.side) x) / R.params.side ≤ 9 := by
    exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm R.params.side 9]; exact h3)
  omega
theorem bondFit_nearPieceField_eq (hH : TorusFrames.hotLumpsOfStepStatement) (hb : NearPieceData s c K D S₀ S g s')
    (hζ : s.InBalls (s.extendByZero _ ζ)) (e : TorusBond n)
    (he : e.1 ∈ thickening (D - 12) (blocksNear R.params.side R.range K)) :
    StepCosts.bondFit R.params (nearPieceField s _ ζ) s.coarse s.bases e =
      HoleOnTori.bondFit R.params (HoleOnTori.stepHotLumps R.params (sitesInBlocks R.params.side S₀) (splicedField s K D S ζ))
        (splicedField s K D S ζ) s.coarse (splicedBases s (thickening D (blocksNear R.params.side R.range K))) e := by
  classical
  have hD := hb.depth_ge
  set F := stepBlockFrame R.params.side n with hF
  have hL0 : 0 < F.blockSide := Nat.pos_of_ne_zero (NeZero.ne R.params.side)
  set y : F.Cell := torusSiteInFrame F F.top e.1 with hy
  have hyT : toTorusSite n y = e.1 := toTorusSite_cell e.1 R.params.side
  have hy'T : toTorusSite n (y + BlockAverages.unitStep F.top e.2 : F.Cell) = e.1 + unitStep n e.2 :=
    toTorusSite_cell_add e.1 R.params.side e.2
  have hin1 : toTorusSite n y ∈ thickening D (blocksNear R.params.side R.range K) := by
    rw [hyT]
    exact thickening_mono (by omega) he
  have hin2 : toTorusSite n (y + BlockAverages.unitStep F.top e.2 : F.Cell) ∈
      thickening D (blocksNear R.params.side R.range K) := by
    rw [hy'T]
    have h1 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le e.1 e.2
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h1
    exact thickening_mono (by omega) (mem_thickening_add he h1)
  have hsame := stepHotLumps_congr hH (torusHotLumps_nearPieceField ζ hb hζ)
  have l1 : nearbyLumps (StepCosts.stepHotLumps R.params (nearPieceField s _ ζ)) y =
      nearbyLumps (HoleOnTori.stepHotLumps R.params (sitesInBlocks R.params.side S₀) (splicedField s K D S ζ)) y := by
    rw [hsame]
    exact (nearbyLumps_splicedField_of_mem ζ hH hb hζ hin1).symm
  have l2 : nearbyLumps (StepCosts.stepHotLumps R.params (nearPieceField s _ ζ)) (y + BlockAverages.unitStep F.top e.2 : F.Cell) =
      nearbyLumps (HoleOnTori.stepHotLumps R.params (sitesInBlocks R.params.side S₀) (splicedField s K D S ζ))
        (y + BlockAverages.unitStep F.top e.2 : F.Cell) := by
    rw [hsame]
    exact (nearbyLumps_splicedField_of_mem ζ hH hb hζ hin2).symm
  have b1 : s.bases y = splicedBases s (thickening D (blocksNear R.params.side R.range K)) y := by
    simp only [splicedBases, if_pos hin1]
  have b2 : s.bases (y + BlockAverages.unitStep F.top e.2 : F.Cell) =
      splicedBases s (thickening D (blocksNear R.params.side R.range K)) (y + BlockAverages.unitStep F.top e.2 : F.Cell) := by
    simp only [splicedBases, if_pos hin2]
  have u1 := mem_sitesBelow_of_isBaseChoice hL0 hb.marked.bases y
  have u2 := mem_sitesBelow_of_isBaseChoice hL0 hb.marked.bases (y + BlockAverages.unitStep F.top e.2 : F.Cell)
  unfold StepCosts.bondFit HoleOnTori.bondFit
  refine contourFit_congr (F := F) (c := (y, e.2)) (period_stepBlockFrame_neZero R.params.side) _ l1 l2 b1 b2 u1 u2
    fun z hz i => ?_
  have hbl := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_le_ten hb u1 hz
  have hin : parentBlock R.params.side (toTorusSite (n * R.params.side) z) ∈
      thickening D (blocksNear R.params.side R.range K) :=
    thickening_mono (by omega) (mem_thickening_add he hbl)
  exact (splicedField_of_mem ζ _ i hin).symm
theorem bondFit_spliced_eq_blockFitAt (hH : TorusFrames.hotLumpsOfStepStatement) (hb : NearPieceData s c K D S₀ S g s')
    (hζ : s.InBalls (s.extendByZero _ ζ)) (e : TorusBond n)
    (h1 : ∀ Z : TorusSite n, _root_.YangMills.Construction.TorusFields.supDist Z e.1 ≤ 4 → Z ∉ blocksNear R.params.side R.range K) :
    HoleOnTori.bondFit R.params (HoleOnTori.stepHotLumps R.params (sitesInBlocks R.params.side S₀) (splicedField s K D S ζ))
        (splicedField s K D S ζ) s.coarse (splicedBases s (thickening D (blocksNear R.params.side R.range K))) e =
      blockFitAt R.params.side (splicedField s K D S ζ) s.coarse e := by
  classical
  set F := stepBlockFrame R.params.side n with hF
  have hL : Odd F.blockSide := hb.sizes.admissible.L_odd
  set y : F.Cell := torusSiteInFrame F F.top e.1 with hy
  have hyT : toTorusSite n y = e.1 := toTorusSite_cell e.1 R.params.side
  have hy'T : toTorusSite n (y + BlockAverages.unitStep F.top e.2 : F.Cell) = e.1 + unitStep n e.2 :=
    toTorusSite_cell_add e.1 R.params.side e.2
  have o1 : toTorusSite n y ∉ thickening 2 (blocksNear R.params.side R.range K) := by
    intro h
    obtain ⟨Z, hZ, hd⟩ := (mem_thickening _ _ _).mp h
    rw [hyT, _root_.YangMills.Construction.TorusFields.supDist_comm] at hd
    exact h1 Z (by omega) hZ
  have o2 : toTorusSite n (y + BlockAverages.unitStep F.top e.2 : F.Cell) ∉ thickening 2 (blocksNear R.params.side R.range K) := by
    intro h
    obtain ⟨Z, hZ, hd⟩ := (mem_thickening _ _ _).mp h
    rw [hy'T] at hd
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le e.1 e.2
    have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle Z (e.1 + unitStep n e.2) e.1
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm (e.1 + unitStep n e.2) e.1] at h4
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at hd
    exact h1 Z (by omega) hZ
  have e1 := nearbyLumps_splicedField_of_not_mem ζ hb hζ o1
  have e2 := nearbyLumps_splicedField_of_not_mem ζ hb hζ o2
  have hB := splicedBases_isBaseChoice ζ hH hb hζ
  unfold HoleOnTori.bondFit blockFitAt
  refine contourFit_eq_blockFit (F := F) (c := (y, e.2)) hL (period_stepBlockFrame_neZero R.params.side) (fun i => ?_)
    _ _ e1 e2 ((hB y).1 (Or.inl e1)) ((hB _).1 (Or.inl e2))
  have : F.period F.depth i = n * R.params.side := period_stepBlockFrame_zero i
  rw [this]
  have h2 := hb.two_le
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  change R.params.side < n * R.params.side
  nlinarith
theorem bondFit_eq_blockFitAt (hH : TorusFrames.hotLumpsOfStepStatement) (hb : NearPieceData s c K D S₀ S g s')
    (W : TorusField (n * R.params.side)) (hW : torusHotLumps R.params W = torusHotLumps R.params s.fine) (e : TorusBond n)
    (h1 : ∀ Z : TorusSite n, _root_.YangMills.Construction.TorusFields.supDist Z e.1 ≤ 4 → Z ∉ s.storedBlockSet c) :
    StepCosts.bondFit R.params W s.coarse s.bases e = blockFitAt R.params.side W s.coarse e := by
  classical
  set F := stepBlockFrame R.params.side n with hF
  have hL : Odd F.blockSide := hb.sizes.admissible.L_odd
  set y : F.Cell := torusSiteInFrame F F.top e.1 with hy
  have hyT : toTorusSite n y = e.1 := toTorusSite_cell e.1 R.params.side
  have hy'T : toTorusSite n (y + BlockAverages.unitStep F.top e.2 : F.Cell) = e.1 + unitStep n e.2 :=
    toTorusSite_cell_add e.1 R.params.side e.2
  have e1 : nearbyLumps (StepCosts.stepHotLumps R.params s.fine) y = ∅ := nearbyLumps_fine_eq_empty hH hb fun Z hZ => by
    rw [hyT] at hZ
    exact h1 Z (by omega)
  have e2 : nearbyLumps (StepCosts.stepHotLumps R.params s.fine) (y + BlockAverages.unitStep F.top e.2 : F.Cell) = ∅ :=
    nearbyLumps_fine_eq_empty hH hb fun Z hZ => by
      rw [hy'T] at hZ
      have h3 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le e.1 e.2
      have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle Z (e.1 + unitStep n e.2) e.1
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm (e.1 + unitStep n e.2) e.1] at h4
      exact h1 Z (by omega)
  have hB := hb.marked.bases
  have hs := stepHotLumps_congr hH hW
  unfold StepCosts.bondFit blockFitAt
  rw [hs]
  refine contourFit_eq_blockFit (F := F) (c := (y, e.2)) hL (period_stepBlockFrame_neZero R.params.side) (fun i => ?_)
    _ _ e1 e2 ((hB y).1 (Or.inl e1)) ((hB _).1 (Or.inl e2))
  have : F.period F.depth i = n * R.params.side := period_stepBlockFrame_zero i
  rw [this]
  have h2 := hb.two_le
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  change R.params.side < n * R.params.side
  nlinarith
theorem abs_blockFitAt_sub_le (hb : NearPieceData s c K D S₀ S g s') (G G' : TorusField (n * R.params.side))
    (V : TorusField n) (e : TorusBond n) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ x i, _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side x) e.1 ≤ 10 → ‖(G x i : ℍ[ℝ]) - G' x i‖ ≤ ε) :
    |blockFitAt R.params.side G V e - blockFitAt R.params.side G' V e| ≤ 10 * R.params.side * ε := by
  set F := stepBlockFrame R.params.side n with hF
  have hL : Odd F.blockSide := hb.sizes.admissible.L_odd
  have hL0 : 0 < F.blockSide := Nat.pos_of_ne_zero (NeZero.ne R.params.side)
  unfold blockFitAt
  refine abs_blockFit_sub_le (F := F) hL (period_stepBlockFrame_neZero R.params.side) _ _ _ (torusSiteInFrame F F.top e.1, e.2)
    ε hε fun z hz i => h _ i ?_
  have hu : refineSite (torusSiteInFrame F F.top e.1) ∈ sitesBelow F.depth (torusSiteInFrame F F.top e.1) := by
    rw [refineSite_eq_cellCentre]
    exact cellCentre_mem_sitesBelow hL0 _
  exact _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_le_ten hb hu (hz.trans (by change 5 * R.params.side ≤ 9 * R.params.side; omega))
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
open GroupMoves TorusMinimizer ShareStability ContourStability
section Torus
variable {m : ℕ} [NeZero m]
theorem isLocallyOrthantClosed_of_cells {L t : ℕ} {X : Finset (TorusSite m)} {k k' : ℕ} (hk : k' ≤ k)
    (h : IsOrthantRegular (cellsOfSites (torusFrame L t m) X) k) : IsLocallyOrthantClosed X k' := by
  intro z
  obtain ⟨eps, he, hX⟩ := h (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top z)
  refine ⟨eps, he, fun q hq hd v hv hb => ?_⟩
  have hq' : torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top q ∈ cellsOfSites (torusFrame L t m) X := by
    rw [mem_cellsOfSites_torusFrame, siteOfCell_torusSiteInFrame]
    exact hq
  have hd' : cellSupDist (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top q)
      (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top z) ≤ k := by
    rw [cellSupDist_torusFrame, siteOfCell_torusSiteInFrame, siteOfCell_torusSiteInFrame]
    omega
  have := hX _ hq' hd' v hv (fun i => (hb i).trans (by exact_mod_cast hk))
  rw [mem_cellsOfSites_torusFrame, siteOfCell_add, siteOfCell_torusSiteInFrame, siteOfCell_siteOfCoords] at this
  exact this
theorem isLocallyOrthantClosed_compl_lumps {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} (hc : ComplementOfThickenedLumpsRegular)
    (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (𝓗 : Finset (Finset (TorusSite m)))
    (hl : ∀ l ∈ 𝓗, ∃ z, l = torusLumpOf ℓ z) :
    IsLocallyOrthantClosed (Finset.univ \ thickening lumpRange (𝓗.biUnion id)) 2047 := by
  classical
  set F := torusFrame ℓ.side 0 m with hF
  have hn : ∀ i, F.extent i = m := fun _ => rfl
  set H : Finset (Finset F.Cell) := 𝓗.image fun l => l.image (torusSiteInFrame F F.top) with hH
  have hs : ∀ i, 0 < F.extent i := fun i => by rw [hn]; exact Nat.pos_of_ne_zero (NeZero.ne m)
  have hlump : ∀ l ∈ H, IsLump ℓ.grid l := by
    intro l hl'
    obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.mp hl'
    obtain ⟨z, rfl⟩ := hl l₀ hl₀
    convert isLump_image_torusLumpOf hfit hLm hn z
  have hreg := hc.2 ℓ.side ℓ.grid F H hfit.L_odd hs (fun i => by rw [hn]; exact hLm) hlump
  have hnear : ∀ c : F.Cell, c ∈ lumpsNeighbourhood H ↔ toTorusSite m c ∈ thickening lumpRange (𝓗.biUnion id) :=
    fun c => mem_biUnion_thicken_iff hn lumpRange 𝓗 c
  have e : HoleBounds.cellsOffLumps F H = cellsOfSites F (Finset.univ \ thickening lumpRange (𝓗.biUnion id)) := by
    ext c
    rw [mem_cellsOfSites_iff hn]
    unfold HoleBounds.cellsOffLumps
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_torusCells_of_pos hs c, hnear]
  rw [e] at hreg
  exact isLocallyOrthantClosed_of_cells le_rfl hreg
theorem isLocallyOrthantClosed_sdiff {A Bc : Finset (TorusSite m)} (hA : IsLocallyOrthantClosed A 1024)
    (hB : IsLocallyOrthantClosed (Finset.univ \ Bc) 1024)
    (hsep : ∀ z : TorusSite m, (∃ w ∈ Bc, _root_.YangMills.Construction.TorusFields.supDist w z ≤ 2048) → ∀ p, _root_.YangMills.Construction.TorusFields.supDist p z ≤ 2048 → p ∈ A) :
    IsLocallyOrthantClosed (A \ Bc) 1024 := by
  classical
  intro z
  have hshift : ∀ (q : TorusSite m) (v : Fin 4 → ℤ), _root_.YangMills.Construction.TorusFields.supDist q z ≤ 1024 → (∀ i, |v i| ≤ (1024 : ℕ)) →
      _root_.YangMills.Construction.TorusFields.supDist (q + siteOfInt v) z ≤ 2048 := by
    intro q v hq hv
    have h1 := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le q v 1024 (fun i => by
      have := hv i
      rw [abs_le] at this
      omega)
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (q + siteOfInt v) q z
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm (q + siteOfInt v) q] at h2
    omega
  by_cases hz : ∃ w ∈ Bc, _root_.YangMills.Construction.TorusFields.supDist w z ≤ 2048
  · obtain ⟨eps, he, hX⟩ := hB z
    refine ⟨eps, he, fun q hq hd v hv hb => ?_⟩
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hq
    have h3 := hX q (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h2⟩) hd v hv hb
    exact Finset.mem_sdiff.mpr ⟨hsep z hz _ (hshift q v hd hb), (Finset.mem_sdiff.mp h3).2⟩
  · obtain ⟨eps, he, hX⟩ := hA z
    refine ⟨eps, he, fun q hq hd v hv hb => ?_⟩
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hq
    refine Finset.mem_sdiff.mpr ⟨hX q h1 hd v hv hb, fun hc => hz ⟨_, hc, hshift q v hd hb⟩⟩
end Torus
section Blocks
variable {n : ℕ} [NeZero n] {L : ℕ} [NeZero L]
theorem parentBlock_apply (x : TorusSite (n * L)) (i : Fin 4) (u : ℤ) (hu : (u : ZMod (n * L)) = x i) :
    parentBlock L x i = (((u + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ) : ZMod n) := by
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have h1 : (((x i).cast : ℤ) : ZMod (n * L)) = (u : ZMod (n * L)) := by
    rw [hu, ZMod.intCast_zmod_cast]
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
  push_cast at hk
  have e : (((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) = (u + ((L : ℤ) - 1) / 2) + (-(n : ℤ) * k) * L := by
    have : ((x i).cast : ℤ) = u - (n : ℤ) * L * k := by linarith
    rw [this]
    ring
  unfold parentBlock
  rw [e, Int.add_mul_ediv_right _ _ hL]
  push_cast
  simp
theorem exists_parentBlock_add (q : TorusSite (n * L)) (h : Fin 4 → ℤ) (hh : ∀ i, |h i| ≤ L) :
    ∃ e : Fin 4 → ℤ, (∀ i, 0 ≤ h i → 0 ≤ e i) ∧ (∀ i, h i ≤ 0 → e i ≤ 0) ∧ (∀ i, |e i| ≤ 1) ∧
      parentBlock L (q + siteOfInt h) = parentBlock L q + siteOfInt e := by
  have hL : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set a : Fin 4 → ℤ := fun i => (((q i).cast : ℤ) + ((L : ℤ) - 1) / 2) with ha
  refine ⟨fun i => (a i + h i) / (L : ℤ) - a i / (L : ℤ), fun i hi => ?_, fun i hi => ?_, fun i => ?_, ?_⟩
  · have : a i / (L : ℤ) ≤ (a i + h i) / (L : ℤ) := Int.ediv_le_ediv hL (by linarith)
    simp only
    linarith
  · have : (a i + h i) / (L : ℤ) ≤ a i / (L : ℤ) := Int.ediv_le_ediv hL (by linarith)
    simp only
    linarith
  · have h1 := abs_le.mp (hh i)
    have u1 : (a i + h i) / (L : ℤ) ≤ (a i + L) / (L : ℤ) := Int.ediv_le_ediv hL (by linarith)
    have u2 : (a i - L) / (L : ℤ) ≤ (a i + h i) / (L : ℤ) := Int.ediv_le_ediv hL (by linarith)
    have e1 : (a i + L) / (L : ℤ) = a i / (L : ℤ) + 1 := Int.add_ediv_of_dvd_right (dvd_refl _) |>.trans (by
      rw [Int.ediv_self hL.ne'])
    have e2 : (a i - L) / (L : ℤ) = a i / (L : ℤ) - 1 := by
      have : a i - L = a i + (-1) * L := by ring
      rw [this, Int.add_mul_ediv_right _ _ hL.ne']
      ring
    rw [abs_le]
    simp only
    constructor <;> linarith
  · funext i
    have hx : (((((q i).cast : ℤ) + h i : ℤ)) : ZMod (n * L)) = (q + siteOfInt h : TorusSite (n * L)) i := by
      simp [siteOfInt]
    rw [parentBlock_apply (q + siteOfInt h) i _ hx]
    have e : ((q i).cast : ℤ) + h i + ((L : ℤ) - 1) / 2 = a i + h i := by
      simp only [ha]
      ring
    rw [e]
    simp only [Pi.add_apply, siteOfInt, parentBlock, ha]
    push_cast
    ring
theorem isLocallyOrthantClosed_sitesInBlocks (hL : 1024 < L) {S : Finset (TorusSite n)}
    (hS : IsLocallyOrthantClosed S 2047) : IsLocallyOrthantClosed (sitesInBlocks L S) 1024 := by
  intro z
  obtain ⟨eps, he, hX⟩ := hS (parentBlock L z)
  refine ⟨eps, he, fun q hq hd v hv hb => ?_⟩
  have hq' : parentBlock L q ∈ S := mem_sitesInBlocks.mp hq
  obtain ⟨e, e1, e2, e3, e4⟩ := exists_parentBlock_add q v (fun i => (hb i).trans (by
    have : ((1024 : ℕ) : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL.le
    exact this))
  rw [mem_sitesInBlocks, e4]
  have hd' : _root_.YangMills.Construction.TorusFields.supDist (parentBlock L q) (parentBlock L z) ≤ 2047 := by
    have h1 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one L q z
    have h2 : _root_.YangMills.Construction.TorusFields.supDist q z / L = 0 := Nat.div_eq_of_lt (by omega)
    omega
  refine hX _ hq' hd' e (fun i => ?_) (fun i => (e3 i).trans (by norm_num))
  rcases he i with h | h
  · have := hv i
    rw [h] at this ⊢
    have h3 := e1 i (by linarith)
    linarith
  · have := hv i
    rw [h] at this ⊢
    have h3 := e2 i (by linarith)
    linarith
end Blocks
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
variable {n : ℕ} [NeZero n] {R : StepSetup} {s : ChartSetting R n} {c : SettingCore R n}
  {K : Finset (TorusSite (n * R.params.side))} {D : ℕ} {S₀ S : Finset (TorusSite n)} {g s' : ℝ}
variable (ζ : s.freeNear (blocksNear R.params.side R.range K) → EuclideanSpace ℝ (Fin 3))
open GroupMoves TorusMinimizer ShareStability ContourStability
abbrev settingRegion (s : ChartSetting R n) : Finset (TorusSite (n * R.params.side)) :=
  Finset.univ \ thickening lumpRange (torusHotSites R.params s.fine)
abbrev pieceLumpSites (s : ChartSetting R n) (K : Finset (TorusSite (n * R.params.side))) :
    Finset (TorusSite (n * R.params.side)) :=
  (s.lumpsInPiece K).biUnion id
abbrev splicedRegion (s : ChartSetting R n) (K : Finset (TorusSite (n * R.params.side))) (S₀ : Finset (TorusSite n)) :
    Finset (TorusSite (n * R.params.side)) :=
  sitesInBlocks R.params.side S₀ \ thickening lumpRange (pieceLumpSites s K)
theorem mem_pieceLumpSites {z : TorusSite (n * R.params.side)} :
    z ∈ pieceLumpSites s K ↔ ∃ l ∈ torusHotLumps R.params s.fine, l ⊆ K ∧ z ∈ l := by
  classical
  simp only [pieceLumpSites, ChartSetting.lumpsInPiece, Finset.mem_biUnion, Finset.mem_filter, id]
  constructor
  · rintro ⟨l, ⟨h1, h2⟩, h3⟩
    exact ⟨l, h1, h2, h3⟩
  · rintro ⟨l, h1, h2, h3⟩
    exact ⟨l, ⟨h1, h2⟩, h3⟩
theorem mem_piece_of_mem_pieceLumpSites {z : TorusSite (n * R.params.side)} (hz : z ∈ pieceLumpSites s K) : z ∈ K := by
  obtain ⟨l, -, h2, h3⟩ := mem_pieceLumpSites.mp hz
  exact h2 h3
theorem exists_eq_torusLumpOf (hb : NearPieceData s c K D S₀ S g s') {l : Finset (TorusSite (n * R.params.side))}
    (hl : l ∈ torusHotLumps R.params s.fine) : ∃ z, l = torusLumpOf R.params z := by
  obtain ⟨_, _, _, _, _, z, _, e⟩ := (mem_torusHotLumps_iff R.params hb.sizes.admissible side_dvd_fine _ _).mp hl
  exact ⟨z, e⟩
theorem isColdOn_settingRegion (hb : NearPieceData s c K D S₀ S g s') (W : TorusField (n * R.params.side))
    (hW : torusHotLumps R.params W = torusHotLumps R.params s.fine) :
    IsColdOn (settingRegion s) R.params.threshold W := by
  classical
  intro x μ ν hlt hc
  by_contra hcon
  rw [not_lt] at hcon
  have hz : x ∈ plaquetteVertices x μ ν := by simp [plaquetteVertices]
  have hl : torusLumpOf R.params x ∈ torusHotLumps R.params s.fine := by
    rw [← hW]
    exact (mem_torusHotLumps_iff R.params hb.sizes.admissible side_dvd_fine _ _).mpr ⟨x, μ, ν, hlt, hcon, x, hz, rfl⟩
  have h1 := (Finset.mem_sdiff.mp (hc x hz)).2
  exact h1 (mem_thickening_self _ (TorusLumps.mem_torusHotSites_iff.mpr ⟨_, hl, mem_torusLumpOf_self x⟩))
theorem regular_settingRegion (hc : ComplementOfThickenedLumpsRegular) (hb : NearPieceData s c K D S₀ S g s') :
    IsLocallyOrthantClosed (settingRegion s) 1024 := by
  have h := isLocallyOrthantClosed_compl_lumps hc hb.sizes.admissible side_dvd_fine (torusHotLumps R.params s.fine)
    fun l hl => exists_eq_torusLumpOf hb hl
  intro z
  obtain ⟨eps, he, hX⟩ := h z
  refine ⟨eps, he, fun q hq hd v hv hbd => hX q hq (by omega) v hv fun i => (hbd i).trans (by norm_num)⟩
theorem regular_sitesInBlocks (hb : NearPieceData s c K D S₀ S g s') {X : Finset (TorusSite n)}
    (hX : IsLocallyOrthantClosed X 2047) : IsLocallyOrthantClosed (sitesInBlocks R.params.side X) 1024 :=
  isLocallyOrthantClosed_sitesInBlocks (by have := hb.sizes.admissible.L_ge; omega) hX
theorem range_ge (hb : NearPieceData s c K D S₀ S g s') : 2 ^ 13 ≤ R.range := by
  have := hb.sizes.range_large
  omega
theorem regular_splicedRegion (hc : ComplementOfThickenedLumpsRegular) (hb : NearPieceData s c K D S₀ S g s') :
    IsLocallyOrthantClosed (splicedRegion s K S₀) 1024 := by
  classical
  have hK : IsLocallyOrthantClosed (Finset.univ \ thickening lumpRange (pieceLumpSites s K)) 1024 := by
    have h := isLocallyOrthantClosed_compl_lumps hc hb.sizes.admissible side_dvd_fine (s.lumpsInPiece K) fun l hl =>
      exists_eq_torusLumpOf hb (Finset.mem_filter.mp hl).1
    intro z
    obtain ⟨eps, he, hX⟩ := h z
    exact ⟨eps, he, fun q hq hd v hv hbd => hX q hq (by omega) v hv fun i => (hbd i).trans (by norm_num)⟩
  refine isLocallyOrthantClosed_sdiff (regular_sitesInBlocks hb hb.regular_outer) hK fun z ⟨w, hw, hd⟩ p hp => ?_
  obtain ⟨x, hx, hxw⟩ := (mem_thickening _ _ _).mp hw
  have hxK := mem_piece_of_mem_pieceLumpSites hx
  refine mem_sitesInBlocks.mpr (hb.zone_sub _ (mem_thickening_self _ (mem_blocksNear.mpr ⟨p, rfl, x, hxK, ?_⟩)))
  have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle p z x
  have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle z w x
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm z w] at h2
  have h3 := range_ge hb
  have hr : lumpRange = 2 ^ 12 := rfl
  omega
theorem isColdOn_splicedRegion (hH : TorusFrames.hotLumpsOfStepStatement) (hb : NearPieceData s c K D S₀ S g s')
    (hζ : s.InBalls (s.extendByZero _ ζ)) :
    IsColdOn (splicedRegion s K S₀) R.params.threshold (splicedField s K D S ζ) := by
  classical
  intro x μ ν hlt hc
  by_contra hcon
  rw [not_lt] at hcon
  have hz : x ∈ plaquetteVertices x μ ν := by simp [plaquetteVertices]
  have hX : ∀ z ∈ plaquetteVertices x μ ν, z ∈ sitesInBlocks R.params.side S₀ := fun z h => (Finset.mem_sdiff.mp (hc z h)).1
  obtain ⟨h1, h3⟩ := hot_of_splicedField ζ hb hlt hX hcon
  have hzD : parentBlock R.params.side x ∈ thickening (D + 4) (blocksNear R.params.side R.range K) :=
    thickening_mono (by omega) h3
  obtain ⟨u, hu, hnear⟩ := exists_near_of_mem_thickening hb.sizes le_rfl hzD
  have hlump : torusLumpOf R.params x ∈ torusHotLumps R.params s.fine := by
    rw [← torusHotLumps_nearPieceField ζ hb hζ]
    exact (mem_torusHotLumps_iff R.params hb.sizes.admissible side_dvd_fine _ _).mpr ⟨x, μ, ν, hlt, h1, x, hz, rfl⟩
  have hsub := lump_subset_piece hb hlump (mem_torusLumpOf_self x) hu
    (by have := hnear x rfl; have := hb.sizes.range_large; omega)
  exact (Finset.mem_sdiff.mp (hc x hz)).2
    (mem_thickening_self _ (mem_pieceLumpSites.mpr ⟨_, hlump, hsub, mem_torusLumpOf_self x⟩))
theorem supDist_parentBlock_box_le (hb : NearPieceData s c K D S₀ S g s') {y : TorusSite (n * R.params.side)} {ρ : ℕ}
    {h : Fin 4 → ℤ} (hh : OffsetInBox ρ h) :
    _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side (y + siteOfInt h)) (parentBlock R.params.side y) ≤ ρ / R.params.side + 1 := by
  have h1 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one R.params.side (y + siteOfInt h) y
  have h2 := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le y h ρ (fun i => by
    have := hh i
    rw [abs_le] at this
    omega)
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h2
  exact h1.trans (by have := Nat.div_le_div_right (c := R.params.side) h2; omega)
theorem siteOfInt_single {i : Fin 4} :
    (siteOfInt (Pi.single i 1 : Fin 4 → ℤ) : TorusSite (n * R.params.side)) = unitStep (n * R.params.side) i := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [siteOfInt, unitStep]
  · simp [siteOfInt, unitStep, Pi.single_eq_of_ne hk]
theorem bondFrom_add_unitStep (y : TorusSite (n * R.params.side)) (e : (Fin 4 → ℤ) × Fin 4) :
    (bondFrom y e).1 + unitStep (n * R.params.side) (bondFrom y e).2 = y + siteOfInt (e.1 + Pi.single e.2 1) := by
  simp only [bondFrom]
  rw [siteOfInt_add, add_assoc, siteOfInt_single]
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
variable {n : ℕ} [NeZero n] {R : StepSetup} {s : ChartSetting R n} {c : SettingCore R n}
  {K : Finset (TorusSite (n * R.params.side))} {D : ℕ} {S₀ S : Finset (TorusSite n)} {g s' : ℝ}
variable (ζ : s.freeNear (blocksNear R.params.side R.range K) → EuclideanSpace ℝ (Fin 3))
open GroupMoves TorusMinimizer ShareStability ContourStability
theorem mem_settingRegion_iff_of_near (hb : NearPieceData s c K D S₀ S g s') {z : TorusSite (n * R.params.side)}
    (hz : parentBlock R.params.side z ∈ thickening D (blocksNear R.params.side R.range K)) :
    z ∈ settingRegion s ↔ z ∈ splicedRegion s K S₀ := by
  classical
  have hin : parentBlock R.params.side z ∈ S₀ := hb.zone_sub _ (thickening_mono (by omega) hz)
  have hK : thickening lumpRange (pieceLumpSites s K) ⊆ thickening lumpRange (torusHotSites R.params s.fine) := by
    intro w hw
    obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp hw
    obtain ⟨l, hl, -, hxl⟩ := mem_pieceLumpSites.mp hx
    exact (mem_thickening _ _ _).mpr ⟨x, TorusLumps.mem_torusHotSites_iff.mpr ⟨l, hl, hxl⟩, hd⟩
  constructor
  · intro h
    exact Finset.mem_sdiff.mpr ⟨mem_sitesInBlocks.mpr hin, fun h2 => (Finset.mem_sdiff.mp h).2 (hK h2)⟩
  · intro h
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h2 => (Finset.mem_sdiff.mp h).2 ?_⟩
    obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp h2
    obtain ⟨l, hl, hxl⟩ := TorusLumps.mem_torusHotSites_iff.mp hx
    obtain ⟨u, hu, hnear⟩ := exists_near_of_mem_thickening hb.sizes (by omega) (thickening_mono (by omega : D ≤ D + 4) hz)
    have h3 := hnear z rfl
    have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle x z u
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm x z] at h4
    have h5 := range_ge hb
    have hr : lumpRange = 2 ^ 12 := rfl
    have hsub := lump_subset_piece hb hl hxl hu (by omega)
    exact (mem_thickening _ _ _).mpr ⟨x, mem_pieceLumpSites.mpr ⟨l, hl, hsub, hxl⟩, hd⟩
theorem mem_splicedRegion_iff_of_far (hb : NearPieceData s c K D S₀ S g s') {z : TorusSite (n * R.params.side)}
    (hz : parentBlock R.params.side z ∉ blocksNear R.params.side R.range K) :
    z ∈ splicedRegion s K S₀ ↔ z ∈ sitesInBlocks R.params.side S := by
  classical
  constructor
  · intro h
    exact mem_sitesInBlocks.mpr (hb.rest_sub _ (mem_sitesInBlocks.mp (Finset.mem_sdiff.mp h).1) hz)
  · intro h
    refine Finset.mem_sdiff.mpr ⟨mem_sitesInBlocks.mpr (hb.cut_sub (mem_sitesInBlocks.mp h)), fun h2 => hz ?_⟩
    obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp h2
    have h5 := range_ge hb
    have hr : lumpRange = 2 ^ 12 := rfl
    exact mem_blocksNear.mpr ⟨z, rfl, x, mem_piece_of_mem_pieceLumpSites hx, by omega⟩
theorem mem_settingRegion_iff_of_not_stored (hb : NearPieceData s c K D S₀ S g s') {z : TorusSite (n * R.params.side)}
    (hz : parentBlock R.params.side z ∉ s.storedBlockSet c) : z ∈ settingRegion s ↔ z ∈ sitesInBlocks R.params.side S := by
  classical
  have hC : parentBlock R.params.side z ∉ c.core := fun h => hz (Finset.mem_union_left _ h)
  have h1 : z ∉ thickening lumpRange (torusHotSites R.params s.fine) := by
    intro h
    obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp h
    have h5 := range_ge hb
    have hr : lumpRange = 2 ^ 12 := rfl
    exact hz ((mem_storedBlockSet s c).mpr (Or.inr ⟨z, rfl, x, mem_pieceSites_of_mem_hotSites hb hx, by omega⟩))
  constructor
  · intro _
    exact mem_sitesInBlocks.mpr (hb.mem_cut_of_not_core _ hC)
  · intro _
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1⟩
section Shares
variable {A δ s₀ : ℝ} (hSh : ShareLocality R.params.coupling R.params.side s₀ A δ) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
  (hs₀ : R.params.threshold ≤ s₀) (h64 : 64 ≤ n * R.params.side) (hc : ComplementOfThickenedLumpsRegular)
include hSh hs₀ h64 hc
theorem abs_share_near_sub_spliced_le (hH : TorusFrames.hotLumpsOfStepStatement) (hb : NearPieceData s c K D S₀ S g s')
    (hζ : s.InBalls (s.extendByZero _ ζ)) (t : ℕ) {y : TorusSite (n * R.params.side)} {ρ : ℕ}
    (hemb : 2 * ρ + 2 < n * R.params.side)
    (hbox : ∀ h, OffsetInBox ρ h →
      parentBlock R.params.side (y + siteOfInt h) ∈ thickening D (blocksNear R.params.side R.range K)) :
    |levelShare R.params.coupling R.params.side t (settingRegion s) y (nearPieceField s _ ζ) -
      levelShare R.params.coupling R.params.side t (splicedRegion s K S₀) y (splicedField s K D S ζ)| ≤
      A * Real.exp (-(δ * ρ)) := by
  refine hSh.decay_of_agreement t (n * R.params.side) _ _ _ _ y ρ R.params.threshold h64 hb.sizes.admissible.σ_pos hs₀
    (regular_settingRegion hc hb) (regular_splicedRegion hc hb)
    (isColdOn_settingRegion hb _ (torusHotLumps_nearPieceField ζ hb hζ)) (isColdOn_splicedRegion ζ hH hb hζ)
    ⟨hemb, fun h hh => mem_settingRegion_iff_of_near hb (hbox h hh), fun e he => ?_⟩
  exact (splicedField_of_mem ζ _ _ (hbox e.1 he.1)).symm
theorem isColdOn_cut (hb : NearPieceData s c K D S₀ S g s') :
    IsColdOn (sitesInBlocks R.params.side S) R.params.threshold (minimizerOn s S) := by
  intro x μ ν hlt hcn
  have := hb.cold x μ ν hlt hcn
  have h2 := hb.small
  have h3 := hb.gap_nonneg
  linarith
theorem abs_share_zero_sub_minimizer_le (hb : NearPieceData s c K D S₀ S g s') (t : ℕ) {y : TorusSite (n * R.params.side)}
    {ρ : ℕ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hW0 : torusHotLumps R.params (s.field 0) = torusHotLumps R.params s.fine)
    (hemb : 2 * ρ + 2 < n * R.params.side)
    (hbox : ∀ h, OffsetInBox (ρ + 1) h → parentBlock R.params.side (y + siteOfInt h) ∉ s.storedBlockSet c) :
    |levelShare R.params.coupling R.params.side t (settingRegion s) y (s.field 0) -
      levelShare R.params.coupling R.params.side t (sitesInBlocks R.params.side S) y (minimizerOn s S)| ≤
      A * Real.exp (-(δ * ρ)) + (bondsOfBox y ρ).card * (A * (2 * g)) := by
  have hfit := hb.sizes.admissible
  refine abs_levelShare_sub_le_of_near hSh hA hδ t _ _ _ _ y ρ R.params.threshold s' (2 * g) h64 hfit.σ_pos hs₀
    (by have := hb.gap_nonneg; linarith) (regular_settingRegion hc hb) (regular_sitesInBlocks hb hb.regular_cut)
    (isColdOn_settingRegion hb _ hW0) hb.cold (by have := hb.small; linarith) hemb
    (fun h hh => mem_settingRegion_iff_of_not_stored hb (hbox h fun i => (hh i).trans (by push_cast; omega)))
    fun b hbb => ?_
  obtain ⟨e, he, rfl⟩ := mem_bondsOfBox.mp hbb
  have h1 := hbox e.1 (fun i => (he.1 i).trans (by push_cast; omega))
  have h2 := hbox (e.1 + Pi.single e.2 1) (fun i => (he.2 i).trans (by push_cast; omega))
  rw [← bondFrom_add_unitStep] at h2
  exact exists_field_zero_eq hfit.L_odd hb.two_le hb.admissible hb.core hb.marked hb.gap_nonneg hb.frames_near _ _ h1 h2
theorem abs_share_spliced_sub_minimizer_le (hH : TorusFrames.hotLumpsOfStepStatement)
    (hb : NearPieceData s c K D S₀ S g s') (hζ : s.InBalls (s.extendByZero _ ζ)) (t : ℕ)
    {y : TorusSite (n * R.params.side)} {ρ : ℕ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hemb : 2 * ρ + 2 < n * R.params.side)
    (hbox : ∀ h, OffsetInBox (ρ + 1) h → parentBlock R.params.side (y + siteOfInt h) ∉ blocksNear R.params.side R.range K) :
    |levelShare R.params.coupling R.params.side t (splicedRegion s K S₀) y (splicedField s K D S ζ) -
      levelShare R.params.coupling R.params.side t (sitesInBlocks R.params.side S) y (minimizerOn s S)| ≤
      A * Real.exp (-(δ * ρ)) + (bondsOfBox y ρ).card * (A * (2 * g)) := by
  have hfit := hb.sizes.admissible
  refine abs_levelShare_sub_le_of_near hSh hA hδ t _ _ _ _ y ρ R.params.threshold s' (2 * g) h64 hfit.σ_pos hs₀
    (by have := hb.gap_nonneg; linarith) (regular_splicedRegion hc hb) (regular_sitesInBlocks hb hb.regular_cut)
    (isColdOn_splicedRegion ζ hH hb hζ) hb.cold (by have := hb.small; linarith) hemb
    (fun h hh => mem_splicedRegion_iff_of_far hb (hbox h fun i => (hh i).trans (by push_cast; omega))) fun b hbb => ?_
  obtain ⟨e, he, rfl⟩ := mem_bondsOfBox.mp hbb
  have h1 := hbox e.1 (fun i => (he.1 i).trans (by push_cast; omega))
  have h2 := hbox (e.1 + Pi.single e.2 1) (fun i => (he.2 i).trans (by push_cast; omega))
  rw [← bondFrom_add_unitStep] at h2
  exact exists_splicedField_eq ζ hb _ _ h1 h2
theorem abs_share_near_sub_zero_le (hb : NearPieceData s c K D S₀ S g s') (hζ : s.InBalls (s.extendByZero _ ζ)) (t : ℕ)
    {y : TorusSite (n * R.params.side)} {ρ : ℕ} (hW0 : torusHotLumps R.params (s.field 0) = torusHotLumps R.params s.fine)
    (hemb : 2 * ρ + 2 < n * R.params.side)
    (hbox : ∀ h, OffsetInBox ρ h → parentBlock R.params.side (y + siteOfInt h) ∉ blocksNear R.params.side R.range K) :
    |levelShare R.params.coupling R.params.side t (settingRegion s) y (nearPieceField s _ ζ) -
      levelShare R.params.coupling R.params.side t (settingRegion s) y (s.field 0)| ≤ A * Real.exp (-(δ * ρ)) := by
  refine hSh.decay_of_agreement t (n * R.params.side) _ _ _ _ y ρ R.params.threshold h64 hb.sizes.admissible.σ_pos hs₀
    (regular_settingRegion hc hb) (regular_settingRegion hc hb)
    (isColdOn_settingRegion hb _ (torusHotLumps_nearPieceField ζ hb hζ)) (isColdOn_settingRegion hb _ hW0)
    ⟨hemb, fun h hh => Iff.rfl, fun e he => ?_⟩
  exact field_extendByZero_of_not_mem _ _ _ _ (hbox e.1 he.1)
theorem abs_share_spliced_sub_minimizer_le_of_far (hH : TorusFrames.hotLumpsOfStepStatement)
    (hb : NearPieceData s c K D S₀ S g s') (hζ : s.InBalls (s.extendByZero _ ζ)) (t : ℕ)
    {y : TorusSite (n * R.params.side)} {ρ : ℕ} (hemb : 2 * ρ + 2 < n * R.params.side)
    (hbox : ∀ h, OffsetInBox ρ h →
      parentBlock R.params.side (y + siteOfInt h) ∉ thickening D (blocksNear R.params.side R.range K)) :
    |levelShare R.params.coupling R.params.side t (splicedRegion s K S₀) y (splicedField s K D S ζ) -
      levelShare R.params.coupling R.params.side t (sitesInBlocks R.params.side S) y (minimizerOn s S)| ≤
      A * Real.exp (-(δ * ρ)) := by
  refine hSh.decay_of_agreement t (n * R.params.side) _ _ _ _ y ρ R.params.threshold h64 hb.sizes.admissible.σ_pos hs₀
    (regular_splicedRegion hc hb) (regular_sitesInBlocks hb hb.regular_cut)
    (isColdOn_splicedRegion ζ hH hb hζ) (isColdOn_cut hSh hs₀ h64 hc hb)
    ⟨hemb, fun h hh => mem_splicedRegion_iff_of_far hb (fun h2 => hbox h hh (mem_thickening_self _ h2)), fun e he => ?_⟩
  exact splicedField_of_not_mem ζ _ _ (hbox e.1 he.1)
end Shares
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
section Shares
variable {m : ℕ} [NeZero m]
theorem levelShare_of_not_mem (a : ℝ) {L : ℕ} (hL : Odd L) (t : ℕ) (X : Finset (TorusSite m)) {y : TorusSite m}
    (hy : y ∉ X) (W : TorusField m) : levelShare a L t X y W = 0 := by
  cases t with
  | zero =>
    classical
    simp only [levelShare]
    refine Finset.sum_eq_zero fun p hp => ?_
    have h1 := (TorusFields.mem_plaquettesIn.mp hp).2
    have : (plaquetteVertices p.1 p.2.1 p.2.2).count y = 0 := List.count_eq_zero_of_not_mem fun h => hy (h1 y h)
    simp [this]
  | succ t =>
    simp only [levelShare, minimalCellShare]
    set F := torusFrame L t m with hF
    have hFL : Odd F.blockSide := hL
    have hYc : torusSiteInFrame F (t + 1) y ∉ cellsOfSites F X := by
      intro h
      have h2 := (mem_cellsOfSites_torusFrame (L := L) (t := t)).mp h
      rw [show siteOfCell (L := L) (t := t) (torusSiteInFrame F (t + 1) y) = y from siteOfCell_torusSiteInFrame y] at h2
      exact hy h2
    have hne : ∀ {j : ℕ}, j ≤ F.top → ∀ {x : F.Site j}, x ∈ sitesOfCells (cellsOfSites F X) j →
        enclosingCell x ≠ torusSiteInFrame F (t + 1) y := by
      intro j hj x hx e
      exact hYc (e ▸ LumpContours.BlockLevels.enclosingCell_mem_of_mem_sitesOfCells hj hFL hx)
    split_ifs with h
    · unfold cellShare
      have hA : ∀ u v : ℝ, u = 0 → v = 0 → u + a * v = 0 := by
        intro u v h1 h2
        rw [h1, h2]
        simp
      refine hA _ _ (Finset.sum_eq_zero fun p hp => ?_)
        (Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun c hc => ?_)
      · have hc := (Finset.mem_filter.mp hp).2.2
        exact mul_eq_zero_of_left (Finset.sum_eq_zero fun x hx => if_neg (hne (Nat.zero_le _) (hc hx))) _
      · have hj' : j + 1 ≤ F.top := Finset.mem_range.mp hj
        have h1 := (Finset.mem_product.mp (Finset.mem_filter.mp hc).1).1
        have h2 := (Finset.mem_filter.mp hc).2
        rw [if_neg (hne hj' h1), if_neg (hne hj' h2)]
        simp
    · rfl
theorem sum_levelShare_zero (a : ℝ) (L : ℕ) (X : Finset (TorusSite m)) (W : TorusField m) :
    ∑ y : TorusSite m, levelShare a L 0 X y W = actionAtLevel a L 0 X W := by apply _root_.YangMills.Construction.FreeBonds.sum_levelShare_zero <;> assumption
theorem sum_levelShare (hSA : SharesSumToAction) {a : ℝ} (ha : 0 ≤ a) {L : ℕ} (hL : 0 < L) (h2 : 2 ≤ m) (t : ℕ)
    (X : Finset (TorusSite m)) (W : TorusField m) :
    ∑ y : TorusSite m, levelShare a L t X y W = actionAtLevel a L t X W := by
  cases t with
  | zero => exact sum_levelShare_zero a L X W
  | succ t => exact hSA a L t m X W ha hL h2
end Shares
section Blocks
variable {n : ℕ} [NeZero n] {L : ℕ} [NeZero L]
theorem sum_sitesInBlocks (f : TorusSite (n * L) → ℝ) :
    ∑ Y : TorusSite n, ∑ y ∈ sitesInBlocks L {Y}, f y = ∑ y, f y := by apply _root_.YangMills.Construction.FreeBonds.sum_sitesInBlocks_singleton <;> assumption
def halfFitsWithin (X : Finset (TorusSite n)) (f : TorusBond n → ℝ) (Y : TorusSite n) : ℝ :=
  open Classical in
  (1 / 2 : ℝ) * ∑ i : Fin 4,
    ((if Y ∈ X ∧ Y + unitStep n i ∈ X then f (Y, i) else 0) +
      (if Y - unitStep n i ∈ X ∧ Y ∈ X then f (Y - unitStep n i, i) else 0))
theorem sum_halfFitsWithin (X : Finset (TorusSite n)) (f : TorusBond n → ℝ) :
    ∑ Y : TorusSite n, halfFitsWithin X f Y = ∑ e ∈ bondsWithin X, f e := by
  classical
  unfold halfFitsWithin bondsWithin
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [Finset.sum_add_distrib]
  have h1 : ∀ i : Fin 4, ∑ Y : TorusSite n, (if Y - unitStep n i ∈ X ∧ Y ∈ X then f (Y - unitStep n i, i) else 0) =
      ∑ Y : TorusSite n, (if Y ∈ X ∧ Y + unitStep n i ∈ X then f (Y, i) else 0) := by
    intro i
    exact Fintype.sum_equiv (Equiv.subRight (unitStep n i))
      (fun Y => if Y - unitStep n i ∈ X ∧ Y ∈ X then f (Y - unitStep n i, i) else 0)
      (fun Y => if Y ∈ X ∧ Y + unitStep n i ∈ X then f (Y, i) else 0) (fun Y => by simp)
  simp only [h1]
  have h2 : ∑ i : Fin 4, ∑ Y : TorusSite n, (if Y ∈ X ∧ Y + unitStep n i ∈ X then f (Y, i) else 0) =
      ∑ e ∈ Finset.univ.filter (fun e : TorusBond n => e.1 ∈ X ∧ e.1 + unitStep n e.2 ∈ X), f e := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [h2]
  ring
end Blocks
open GroupMoves TorusMinimizer ShareStability ContourStability
theorem sum_le_of_block_bounds {T : Type} [Fintype T] [DecidableEq T] (A B E a err : T → ℝ) (N : Finset T) (P : ℝ)
    (hN : ∀ Y ∈ N, |A Y - E Y| ≤ err Y) (hO : ∀ Y, Y ∉ N → |(A Y - B Y) - (E Y - a Y)| ≤ err Y)
    (hsave : ∑ Y, a Y + P ≤ ∑ Y, E Y) :
    ∑ Y ∈ N, a Y + P - ∑ Y, err Y ≤ ∑ Y ∈ N, A Y + ∑ Y ∈ Finset.univ \ N, (A Y - B Y) := by
  have hsplit : ∀ f : T → ℝ, ∑ Y, f Y = ∑ Y ∈ N, f Y + ∑ Y ∈ Finset.univ \ N, f Y := by
    intro f
    rw [add_comm, Finset.sum_sdiff (Finset.subset_univ N)]
  have h1 : ∑ Y ∈ N, (E Y - A Y) ≤ ∑ Y ∈ N, err Y :=
    Finset.sum_le_sum fun Y hY => by
      have := abs_le.mp (hN Y hY)
      linarith [this.1]
  have h2 : ∑ Y ∈ Finset.univ \ N, ((E Y - a Y) - (A Y - B Y)) ≤ ∑ Y ∈ Finset.univ \ N, err Y :=
    Finset.sum_le_sum fun Y hY => by
      have := abs_le.mp (hO Y (Finset.mem_sdiff.mp hY).2)
      linarith [this.1]
  rw [hsplit a, hsplit E] at hsave
  rw [hsplit err]
  simp only [Finset.sum_sub_distrib] at h1 h2 ⊢
  linarith
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
open GroupMoves TorusMinimizer ShareStability ContourStability
theorem abs_twoPart_sub_le {ι : Type} (B : Finset ι) (f g : ι → ℝ) (a e κ : ℝ) (u v u' v' : Fin 4 → ℝ) (ha : 0 ≤ a)
    (hfg : ∀ y ∈ B, |f y - g y| ≤ e) (hu : ∀ i, |u i - u' i| ≤ κ) (hv : ∀ i, |v i - v' i| ≤ κ) :
    |(∑ y ∈ B, f y + a * ((1 / 2 : ℝ) * ∑ i, (u i + v i))) - (∑ y ∈ B, g y + a * ((1 / 2 : ℝ) * ∑ i, (u' i + v' i)))| ≤
      B.card * e + a * (4 * κ) := by
  have h1 : |∑ y ∈ B, f y - ∑ y ∈ B, g y| ≤ B.card * e := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul B _ e hfg
    simpa using this
  have h2 : |(1 / 2 : ℝ) * ∑ i, (u i + v i) - (1 / 2 : ℝ) * ∑ i, (u' i + v' i)| ≤ 4 * κ := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul]
    have h3 : |∑ i : Fin 4, (u i + v i - (u' i + v' i))| ≤ 8 * κ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h4 : ∀ i ∈ (Finset.univ : Finset (Fin 4)), |u i + v i - (u' i + v' i)| ≤ 2 * κ := by
        intro i _
        have e1 : u i + v i - (u' i + v' i) = (u i - u' i) + (v i - v' i) := by ring
        rw [e1]
        exact (abs_add_le _ _).trans (by linarith [hu i, hv i])
      have := Finset.sum_le_card_nsmul _ _ (2 * κ) h4
      simp at this
      linarith
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have e1 : (∑ y ∈ B, f y + a * ((1 / 2 : ℝ) * ∑ i, (u i + v i))) -
      (∑ y ∈ B, g y + a * ((1 / 2 : ℝ) * ∑ i, (u' i + v' i))) =
      (∑ y ∈ B, f y - ∑ y ∈ B, g y) + a * ((1 / 2 : ℝ) * ∑ i, (u i + v i) - (1 / 2 : ℝ) * ∑ i, (u' i + v' i)) := by ring
  rw [e1]
  refine (abs_add_le _ _).trans (add_le_add h1 ?_)
  rw [abs_mul, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left h2 ha
variable {n : ℕ} [NeZero n] {R : StepSetup} {s : ChartSetting R n} {c : SettingCore R n}
  {K : Finset (TorusSite (n * R.params.side))} {D : ℕ} {S₀ S : Finset (TorusSite n)} {g s' : ℝ}
theorem card_sitesInBlocks_singleton_le (hL : Odd R.params.side) (h2 : 2 ≤ n) (Y : TorusSite n) :
    (sitesInBlocks R.params.side {Y} : Finset (TorusSite (n * R.params.side))).card ≤ (2 * R.params.side + 1) ^ 4 := by
  classical
  obtain ⟨z₀, hz₀⟩ := exists_parentBlock_eq (L := R.params.side) hL h2 Y
  refine (Finset.card_le_card ?_).trans (card_thickening_singleton_le R.params.side z₀)
  intro z hz
  have h1 : parentBlock R.params.side z = Y := by simpa using mem_sitesInBlocks.mp hz
  refine (mem_thickening _ _ _).mpr ⟨z₀, Finset.mem_singleton_self _, ?_⟩
  have := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_le_side_mul_parentBlock_add hL z z₀
  rw [h1, hz₀, _root_.YangMills.Construction.TorusFields.supDist_self] at this
  omega
variable (ζ : s.freeNear (blocksNear R.params.side R.range K) → EuclideanSpace ℝ (Fin 3))
abbrev splicedFit (s : ChartSetting R n) (K : Finset (TorusSite (n * R.params.side))) (D : ℕ) (S₀ S : Finset (TorusSite n))
    (ζ : s.freeNear (blocksNear R.params.side R.range K) → EuclideanSpace ℝ (Fin 3)) : TorusBond n → ℝ :=
  HoleOnTori.bondFit R.params (HoleOnTori.stepHotLumps R.params (sitesInBlocks R.params.side S₀) (splicedField s K D S ζ))
    (splicedField s K D S ζ) s.coarse (splicedBases s (thickening D (blocksNear R.params.side R.range K)))
def splicedCost (s : ChartSetting R n) (K : Finset (TorusSite (n * R.params.side))) (D : ℕ) (S₀ S : Finset (TorusSite n))
    (ζ : s.freeNear (blocksNear R.params.side R.range K) → EuclideanSpace ℝ (Fin 3)) (Y : TorusSite n) : ℝ :=
  ∑ y ∈ sitesInBlocks R.params.side {Y},
      levelShare R.params.coupling R.params.side R.depth (splicedRegion s K S₀) y (splicedField s K D S ζ) +
    R.params.coupling * halfFitsWithin S₀ (splicedFit s K D S₀ S ζ) Y
theorem blockCost_eq (hb : NearPieceData s c K D S₀ S g s') (W : TorusField (n * R.params.side))
    (hW : torusHotLumps R.params W = torusHotLumps R.params s.fine) (Y : TorusSite n) :
    blockCost R.params R.depth W s.coarse s.bases Y =
      ∑ y ∈ sitesInBlocks R.params.side {Y}, levelShare R.params.coupling R.params.side R.depth (settingRegion s) y W +
      R.params.coupling * ((1 / 2 : ℝ) * ∑ i : Fin 4, (StepCosts.bondFit R.params W s.coarse s.bases (Y, i) +
        StepCosts.bondFit R.params W s.coarse s.bases (Y - unitStep n i, i))) := by
  have e : torusHotSites R.params W = torusHotSites R.params s.fine := by
    unfold torusHotSites
    rw [hW]
  unfold blockCost
  rw [e]
  ring
theorem abs_blockCost_sub_splicedCost_le (hH : TorusFrames.hotLumpsOfStepStatement) (hb : NearPieceData s c K D S₀ S g s')
    (hζ : s.InBalls (s.extendByZero _ ζ)) {Y : TorusSite n}
    (hY : Y ∈ thickening (D - 13) (blocksNear R.params.side R.range K)) {e : ℝ} (he : 0 ≤ e)
    (hsh : ∀ y : TorusSite (n * R.params.side), parentBlock R.params.side y = Y →
      |levelShare R.params.coupling R.params.side R.depth (settingRegion s) y (nearPieceField s _ ζ) -
        levelShare R.params.coupling R.params.side R.depth (splicedRegion s K S₀) y (splicedField s K D S ζ)| ≤ e) :
    |blockCost R.params R.depth (nearPieceField s _ ζ) s.coarse s.bases Y - splicedCost s K D S₀ S ζ Y| ≤
      (2 * R.params.side + 1) ^ 4 * e := by
  classical
  have hD := hb.depth_ge
  have ha : 0 ≤ R.params.coupling := by have := hb.sizes.admissible.a_ge; linarith
  rw [blockCost_eq hb _ (torusHotLumps_nearPieceField ζ hb hζ)]
  unfold splicedCost halfFitsWithin
  have hY1 : Y ∈ thickening (D - 12) (blocksNear R.params.side R.range K) := thickening_mono (by omega) hY
  have hnext : ∀ i : Fin 4, Y + unitStep n i ∈ thickening (D - 12) (blocksNear R.params.side R.range K) := fun i => by
    have h1 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le Y i
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h1
    exact thickening_mono (by omega) (mem_thickening_add hY h1)
  have hprev : ∀ i : Fin 4, Y - unitStep n i ∈ thickening (D - 12) (blocksNear R.params.side R.range K) := fun i => by
    have h1 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (Y - unitStep n i) i
    rw [sub_add_cancel] at h1
    exact thickening_mono (by omega) (mem_thickening_add hY h1)
  have hS : ∀ {Z : TorusSite n}, Z ∈ thickening (D - 12) (blocksNear R.params.side R.range K) → Z ∈ S₀ := fun h =>
    hb.zone_sub _ (thickening_mono (by omega) h)
  have h1 := abs_twoPart_sub_le (sitesInBlocks R.params.side {Y})
    (fun y => levelShare R.params.coupling R.params.side R.depth (settingRegion s) y (nearPieceField s _ ζ))
    (fun y => levelShare R.params.coupling R.params.side R.depth (splicedRegion s K S₀) y (splicedField s K D S ζ))
    R.params.coupling e 0
    (fun i => StepCosts.bondFit R.params (nearPieceField s _ ζ) s.coarse s.bases (Y, i))
    (fun i => StepCosts.bondFit R.params (nearPieceField s _ ζ) s.coarse s.bases (Y - unitStep n i, i))
    (fun i => if Y ∈ S₀ ∧ Y + unitStep n i ∈ S₀ then splicedFit s K D S₀ S ζ (Y, i) else 0)
    (fun i => if Y - unitStep n i ∈ S₀ ∧ Y ∈ S₀ then splicedFit s K D S₀ S ζ (Y - unitStep n i, i) else 0) ha
    (fun y hy => hsh y (by simpa using mem_sitesInBlocks.mp hy))
    (fun i => by
      rw [if_pos ⟨hS hY1, hS (hnext i)⟩, bondFit_nearPieceField_eq ζ hH hb hζ (Y, i) hY1]
      simp)
    (fun i => by
      rw [if_pos ⟨hS (hprev i), hS hY1⟩, bondFit_nearPieceField_eq ζ hH hb hζ (Y - unitStep n i, i) (hprev i)]
      simp)
  refine h1.trans ?_
  have hc := card_sitesInBlocks_singleton_le (R := R) hb.sizes.admissible.L_odd hb.two_le Y
  have hc' : ((sitesInBlocks R.params.side {Y} : Finset (TorusSite (n * R.params.side))).card : ℝ) ≤
      (2 * (R.params.side : ℝ) + 1) ^ 4 := by
    exact_mod_cast hc
  simp only [mul_zero, add_zero]
  exact mul_le_mul_of_nonneg_right hc' he
def ShareSplitsOn (s : ChartSetting R n) (S : Finset (TorusSite n)) : Prop :=
  ∀ Y ∈ S, levelShare R.params.coupling R.params.side (R.depth + 1) S Y s.coarse =
    ∑ y ∈ sitesInBlocks R.params.side {Y},
        levelShare R.params.coupling R.params.side R.depth (sitesInBlocks R.params.side S) y (minimizerOn s S) +
      R.params.coupling * halfBlockFits R.params.side S (minimizerOn s S) s.coarse Y
theorem abs_blockCost_zero_sub_share_le (hH : TorusFrames.hotLumpsOfStepStatement) (hb : NearPieceData s c K D S₀ S g s')
    (hsp : ShareSplitsOn s S) (hW0 : torusHotLumps R.params (s.field 0) = torusHotLumps R.params s.fine) {Y : TorusSite n}
    (hoff : ∀ Z : TorusSite n, _root_.YangMills.Construction.TorusFields.supDist Z Y ≤ 14 → Z ∉ s.storedBlockSet c) {e : ℝ} (he : 0 ≤ e)
    (hsh : ∀ y : TorusSite (n * R.params.side), parentBlock R.params.side y = Y →
      |levelShare R.params.coupling R.params.side R.depth (settingRegion s) y (s.field 0) -
        levelShare R.params.coupling R.params.side R.depth (sitesInBlocks R.params.side S) y (minimizerOn s S)| ≤ e) :
    |blockCost R.params R.depth (s.field 0) s.coarse s.bases Y -
      levelShare R.params.coupling R.params.side (R.depth + 1) S Y s.coarse| ≤
      (2 * R.params.side + 1) ^ 4 * e + R.params.coupling * (4 * (10 * R.params.side * (2 * g))) := by
  classical
  have ha : 0 ≤ R.params.coupling := by have := hb.sizes.admissible.a_ge; linarith
  have hg2 : 0 ≤ 2 * g := by have := hb.gap_nonneg; linarith
  have hinS : ∀ Z : TorusSite n, _root_.YangMills.Construction.TorusFields.supDist Z Y ≤ 14 → Z ∈ S := fun Z hZ =>
    hb.mem_cut_of_not_core Z fun h => hoff Z hZ (Finset.mem_union_left _ h)
  have hself : Y ∈ S := hinS Y (by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega)
  rw [blockCost_eq hb _ hW0, hsp Y hself]
  unfold halfBlockFits
  have hn1 : ∀ i : Fin 4, _root_.YangMills.Construction.TorusFields.supDist (Y + unitStep n i) Y ≤ 1 := fun i => by
    have h1 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le Y i
    rwa [_root_.YangMills.Construction.TorusFields.supDist_comm] at h1
  have hp1 : ∀ i : Fin 4, _root_.YangMills.Construction.TorusFields.supDist (Y - unitStep n i) Y ≤ 1 := fun i => by
    have h1 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (Y - unitStep n i) i
    rwa [sub_add_cancel] at h1
  have hfitN : ∀ e₀ : TorusBond n, _root_.YangMills.Construction.TorusFields.supDist e₀.1 Y ≤ 1 →
      |StepCosts.bondFit R.params (s.field 0) s.coarse s.bases e₀ - blockFitAt R.params.side (minimizerOn s S) s.coarse e₀| ≤
        10 * R.params.side * (2 * g) := by
    intro e₀ he₀
    rw [bondFit_eq_blockFitAt hH hb _ hW0 e₀ fun Z hZ => hoff Z (by
      have := _root_.YangMills.Construction.TorusFields.supDist_triangle Z e₀.1 Y
      omega)]
    refine abs_blockFitAt_sub_le hb _ _ _ e₀ (2 * g) hg2 fun x i hx => ?_
    have hxY : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side x) Y ≤ 11 := by
      have := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side x) e₀.1 Y
      omega
    have n1 := hoff _ (by omega : supDist (parentBlock R.params.side x) Y ≤ 14)
    have n2 := hoff (parentBlock R.params.side (x + unitStep (n * R.params.side) i)) (by
      have h3 := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_add_unitStep_le hb x i
      have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side (x + unitStep (n * R.params.side) i))
        (parentBlock R.params.side x) Y
      omega)
    obtain ⟨v, hv, e⟩ := exists_field_zero_eq hb.sizes.admissible.L_odd hb.two_le hb.admissible hb.core hb.marked
      hb.gap_nonneg hb.frames_near x i n1 n2
    exact norm_sub_le_of_eq_mul hv e
  have h1 := abs_twoPart_sub_le (sitesInBlocks R.params.side {Y})
    (fun y => levelShare R.params.coupling R.params.side R.depth (settingRegion s) y (s.field 0))
    (fun y => levelShare R.params.coupling R.params.side R.depth (sitesInBlocks R.params.side S) y (minimizerOn s S))
    R.params.coupling e (10 * R.params.side * (2 * g))
    (fun i => StepCosts.bondFit R.params (s.field 0) s.coarse s.bases (Y, i))
    (fun i => StepCosts.bondFit R.params (s.field 0) s.coarse s.bases (Y - unitStep n i, i))
    (fun i => if Y + unitStep n i ∈ S then blockFitAt R.params.side (minimizerOn s S) s.coarse (Y, i) else 0)
    (fun i => if Y - unitStep n i ∈ S then blockFitAt R.params.side (minimizerOn s S) s.coarse (Y - unitStep n i, i)
      else 0) ha
    (fun y hy => hsh y (by simpa using mem_sitesInBlocks.mp hy))
    (fun i => by
      rw [if_pos (hinS _ (by have := hn1 i; omega))]
      exact hfitN (Y, i) (by change _root_.YangMills.Construction.TorusFields.supDist Y Y ≤ 1; rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega))
    (fun i => by
      rw [if_pos (hinS _ (by have := hp1 i; omega))]
      exact hfitN (Y - unitStep n i, i) (hp1 i))
  refine h1.trans ?_
  have hc := card_sitesInBlocks_singleton_le (R := R) hb.sizes.admissible.L_odd hb.two_le Y
  have hc' : ((sitesInBlocks R.params.side {Y} : Finset (TorusSite (n * R.params.side))).card : ℝ) ≤
      (2 * (R.params.side : ℝ) + 1) ^ 4 := by
    exact_mod_cast hc
  have := mul_le_mul_of_nonneg_right hc' he
  linarith
theorem abs_splicedCost_sub_share_le (hH : TorusFrames.hotLumpsOfStepStatement) (hb : NearPieceData s c K D S₀ S g s')
    (hsp : ShareSplitsOn s S) (hζ : s.InBalls (s.extendByZero _ ζ)) {Y : TorusSite n} (hL : Odd R.params.side)
    (hoff : ∀ Z : TorusSite n, _root_.YangMills.Construction.TorusFields.supDist Z Y ≤ 6 → Z ∉ blocksNear R.params.side R.range K) {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ x i, _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side x) Y ≤ 11 →
      ‖(splicedField s K D S ζ x i : ℍ[ℝ]) - minimizerOn s S x i‖ ≤ ε)
    {e : ℝ} (he : 0 ≤ e)
    (hsh : ∀ y : TorusSite (n * R.params.side), parentBlock R.params.side y = Y →
      |levelShare R.params.coupling R.params.side R.depth (splicedRegion s K S₀) y (splicedField s K D S ζ) -
        levelShare R.params.coupling R.params.side R.depth (sitesInBlocks R.params.side S) y (minimizerOn s S)| ≤ e) :
    |splicedCost s K D S₀ S ζ Y - levelShare R.params.coupling R.params.side (R.depth + 1) S Y s.coarse| ≤
      (2 * R.params.side + 1) ^ 4 * e + R.params.coupling * (4 * (10 * R.params.side * ε)) := by
  classical
  have ha : 0 ≤ R.params.coupling := by have := hb.sizes.admissible.a_ge; linarith
  have hpos : 0 ≤ (2 * (R.params.side : ℝ) + 1) ^ 4 * e + R.params.coupling * (4 * (10 * R.params.side * ε)) := by
    positivity
  have hYN := hoff Y (by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega)
  by_cases hself : Y ∈ S
  · have hn1 : ∀ i : Fin 4, _root_.YangMills.Construction.TorusFields.supDist (Y + unitStep n i) Y ≤ 1 := fun i => by
      have h1 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le Y i
      rwa [_root_.YangMills.Construction.TorusFields.supDist_comm] at h1
    have hp1 : ∀ i : Fin 4, _root_.YangMills.Construction.TorusFields.supDist (Y - unitStep n i) Y ≤ 1 := fun i => by
      have h1 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (Y - unitStep n i) i
      rwa [sub_add_cancel] at h1
    have hiff : ∀ Z : TorusSite n, _root_.YangMills.Construction.TorusFields.supDist Z Y ≤ 1 → (Z ∈ S₀ ↔ Z ∈ S) := fun Z hZ =>
      ⟨fun h => hb.rest_sub Z h (hoff Z (by omega)), fun h => hb.cut_sub h⟩
    have hYS₀ : Y ∈ S₀ := hb.cut_sub hself
    have hfitN : ∀ e₀ : TorusBond n, _root_.YangMills.Construction.TorusFields.supDist e₀.1 Y ≤ 1 →
        |splicedFit s K D S₀ S ζ e₀ - blockFitAt R.params.side (minimizerOn s S) s.coarse e₀| ≤
          10 * R.params.side * ε := by
      intro e₀ he₀
      have e1 : splicedFit s K D S₀ S ζ e₀ = blockFitAt R.params.side (splicedField s K D S ζ) s.coarse e₀ :=
        bondFit_spliced_eq_blockFitAt ζ hH hb hζ e₀ fun Z hZ => hoff Z (by
          have := _root_.YangMills.Construction.TorusFields.supDist_triangle Z e₀.1 Y
          omega)
      rw [e1]
      refine abs_blockFitAt_sub_le hb _ _ _ e₀ ε hε fun x i hx => hclose x i ?_
      have := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side x) e₀.1 Y
      omega
    rw [hsp Y hself]
    unfold splicedCost halfFitsWithin halfBlockFits
    have h1 := abs_twoPart_sub_le (sitesInBlocks R.params.side {Y})
      (fun y => levelShare R.params.coupling R.params.side R.depth (splicedRegion s K S₀) y (splicedField s K D S ζ))
      (fun y => levelShare R.params.coupling R.params.side R.depth (sitesInBlocks R.params.side S) y (minimizerOn s S))
      R.params.coupling e (10 * R.params.side * ε)
      (fun i => if Y ∈ S₀ ∧ Y + unitStep n i ∈ S₀ then splicedFit s K D S₀ S ζ (Y, i) else 0)
      (fun i => if Y - unitStep n i ∈ S₀ ∧ Y ∈ S₀ then splicedFit s K D S₀ S ζ (Y - unitStep n i, i) else 0)
      (fun i => if Y + unitStep n i ∈ S then blockFitAt R.params.side (minimizerOn s S) s.coarse (Y, i) else 0)
      (fun i => if Y - unitStep n i ∈ S then blockFitAt R.params.side (minimizerOn s S) s.coarse (Y - unitStep n i, i)
        else 0) ha
      (fun y hy => hsh y (by simpa using mem_sitesInBlocks.mp hy))
      (fun i => by
        by_cases hc : Y + unitStep n i ∈ S
        · rw [if_pos ⟨hYS₀, (hiff _ (hn1 i)).mpr hc⟩, if_pos hc]
          exact hfitN (Y, i) (by change _root_.YangMills.Construction.TorusFields.supDist Y Y ≤ 1; rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega)
        · rw [if_neg (fun h => hc ((hiff _ (hn1 i)).mp h.2)), if_neg hc]
          simpa using mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) (Nat.cast_nonneg R.params.side)) hε)
      (fun i => by
        by_cases hc : Y - unitStep n i ∈ S
        · rw [if_pos ⟨(hiff _ (hp1 i)).mpr hc, hYS₀⟩, if_pos hc]
          exact hfitN (Y - unitStep n i, i) (hp1 i)
        · rw [if_neg (fun h => hc ((hiff _ (hp1 i)).mp h.1)), if_neg hc]
          simpa using mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) (Nat.cast_nonneg R.params.side)) hε)
    refine h1.trans ?_
    have hc := card_sitesInBlocks_singleton_le (R := R) hb.sizes.admissible.L_odd hb.two_le Y
    have hc' : ((sitesInBlocks R.params.side {Y} : Finset (TorusSite (n * R.params.side))).card : ℝ) ≤
        (2 * (R.params.side : ℝ) + 1) ^ 4 := by
      exact_mod_cast hc
    have := mul_le_mul_of_nonneg_right hc' he
    linarith
  · have hnS₀ : Y ∉ S₀ := fun h => hself (hb.rest_sub Y h hYN)
    have e1 : splicedCost s K D S₀ S ζ Y = 0 := by
      unfold splicedCost halfFitsWithin
      have h1 : ∑ y ∈ sitesInBlocks R.params.side {Y},
          levelShare R.params.coupling R.params.side R.depth (splicedRegion s K S₀) y (splicedField s K D S ζ) = 0 := by
        refine Finset.sum_eq_zero fun y hy => levelShare_of_not_mem _ hL _ _ (fun hX => hnS₀ ?_) _
        have h2 := mem_sitesInBlocks.mp (Finset.mem_sdiff.mp hX).1
        have h3 : parentBlock R.params.side y = Y := by simpa using mem_sitesInBlocks.mp hy
        rwa [h3] at h2
      rw [h1]
      simp [hnS₀]
    rw [e1, levelShare_of_not_mem _ hL _ _ hself]
    simpa using hpos
theorem abs_blockCost_sub_blockCost_zero_le (hH : TorusFrames.hotLumpsOfStepStatement)
    (hb : NearPieceData s c K D S₀ S g s') (hζ : s.InBalls (s.extendByZero _ ζ))
    (hW0 : torusHotLumps R.params (s.field 0) = torusHotLumps R.params s.fine) {Y : TorusSite n}
    (hoff : ∀ Z : TorusSite n, _root_.YangMills.Construction.TorusFields.supDist Z Y ≤ 13 → Z ∉ blocksNear R.params.side R.range K) {e : ℝ} (he : 0 ≤ e)
    (hsh : ∀ y : TorusSite (n * R.params.side), parentBlock R.params.side y = Y →
      |levelShare R.params.coupling R.params.side R.depth (settingRegion s) y (nearPieceField s _ ζ) -
        levelShare R.params.coupling R.params.side R.depth (settingRegion s) y (s.field 0)| ≤ e) :
    |blockCost R.params R.depth (nearPieceField s _ ζ) s.coarse s.bases Y -
      blockCost R.params R.depth (s.field 0) s.coarse s.bases Y| ≤ (2 * R.params.side + 1) ^ 4 * e := by
  classical
  have ha : 0 ≤ R.params.coupling := by have := hb.sizes.admissible.a_ge; linarith
  have hL0 : 0 < (stepBlockFrame R.params.side n).blockSide := Nat.pos_of_ne_zero (NeZero.ne R.params.side)
  have hsame : StepCosts.stepHotLumps R.params (nearPieceField s _ ζ) = StepCosts.stepHotLumps R.params (s.field 0) :=
    stepHotLumps_congr hH ((torusHotLumps_nearPieceField ζ hb hζ).trans hW0.symm)
  have hfit : ∀ e₀ : TorusBond n, _root_.YangMills.Construction.TorusFields.supDist e₀.1 Y ≤ 1 →
      StepCosts.bondFit R.params (nearPieceField s _ ζ) s.coarse s.bases e₀ =
        StepCosts.bondFit R.params (s.field 0) s.coarse s.bases e₀ := by
    intro e₀ he₀
    unfold StepCosts.bondFit
    rw [hsame]
    set F := stepBlockFrame R.params.side n with hF
    set y : F.Cell := torusSiteInFrame F F.top e₀.1 with hy
    have u1 := mem_sitesBelow_of_isBaseChoice hL0 hb.marked.bases y
    have u2 := mem_sitesBelow_of_isBaseChoice hL0 hb.marked.bases (y + BlockAverages.unitStep F.top e₀.2 : F.Cell)
    refine contourFit_congr (F := F) (c := (y, e₀.2)) (period_stepBlockFrame_neZero R.params.side) _ rfl rfl rfl rfl u1 u2
      fun z hz i => ?_
    have hbl := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_le_ten hb u1 hz
    have hgoal : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side (toTorusSite (n * R.params.side) z)) Y ≤ 13 := by
      have := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side (toTorusSite (n * R.params.side) z)) e₀.1 Y
      omega
    exact field_extendByZero_of_not_mem _ _ (toTorusSite (n * R.params.side) z) i (hoff _ hgoal)
  rw [blockCost_eq hb _ (torusHotLumps_nearPieceField ζ hb hζ), blockCost_eq hb _ hW0]
  have h1 := abs_twoPart_sub_le (sitesInBlocks R.params.side {Y})
    (fun y => levelShare R.params.coupling R.params.side R.depth (settingRegion s) y (nearPieceField s _ ζ))
    (fun y => levelShare R.params.coupling R.params.side R.depth (settingRegion s) y (s.field 0)) R.params.coupling e 0
    (fun i => StepCosts.bondFit R.params (nearPieceField s _ ζ) s.coarse s.bases (Y, i))
    (fun i => StepCosts.bondFit R.params (nearPieceField s _ ζ) s.coarse s.bases (Y - unitStep n i, i))
    (fun i => StepCosts.bondFit R.params (s.field 0) s.coarse s.bases (Y, i))
    (fun i => StepCosts.bondFit R.params (s.field 0) s.coarse s.bases (Y - unitStep n i, i)) ha
    (fun y hy => hsh y (by simpa using mem_sitesInBlocks.mp hy))
    (fun i => by
      rw [hfit (Y, i) (by change _root_.YangMills.Construction.TorusFields.supDist Y Y ≤ 1; rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega)]
      simp)
    (fun i => by
      have h3 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (Y - unitStep n i) i
      rw [sub_add_cancel] at h3
      rw [hfit (Y - unitStep n i, i) h3]
      simp)
  refine h1.trans ?_
  have hc := card_sitesInBlocks_singleton_le (R := R) hb.sizes.admissible.L_odd hb.two_le Y
  have hc' : ((sitesInBlocks R.params.side {Y} : Finset (TorusSite (n * R.params.side))).card : ℝ) ≤
      (2 * (R.params.side : ℝ) + 1) ^ 4 := by
    exact_mod_cast hc
  simp only [mul_zero, add_zero]
  exact mul_le_mul_of_nonneg_right hc' he
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
section Frames
variable {F : BlockFrame}
theorem axialGauge_congr (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide) (W W' : F.GaugeField F.depth)
    (x : F.Site F.depth) (h : ∀ b ∈ cutBonds (sitesBelow F.depth (enclosingCell x)), W b.1 b.2 = W' b.1 b.2) :
    axialGauge 1 W x = axialGauge 1 W' x := by
  have ho := (centre_cellOffset hL hs x).1
  unfold axialGauge
  exact GaugeFixing.pathHolonomy_congr h _ _ (GaugeFixing.pathWithin_axisPath _
    (fun o hoc => (mem_sitesBelow_iff _ _).mpr ⟨o, hoc, rfl⟩) _ ho 1)
theorem bondCoordinate_congr (V : F.GaugeField F.top) {W W' : F.GaugeField F.depth} {b : F.Site F.depth × Fin 4}
    (h1 : W b.1 b.2 = W' b.1 b.2) (t1 : axialGauge 1 W b.1 = axialGauge 1 W' b.1)
    (t2 : axialGauge 1 W (b.1 + BlockAverages.unitStep F.depth b.2) =
      axialGauge 1 W' (b.1 + BlockAverages.unitStep F.depth b.2)) :
    LumpContours.bondCoordinate 1 V W b = LumpContours.bondCoordinate 1 V W' b := by
  unfold LumpContours.bondCoordinate BlockAverages.gaugeTransform
  rw [h1, t1, t2]
theorem minimizingCoordinates_of_not_mem {a ρ : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top}
    {b : F.Site F.depth × Fin 4} (hb : b ∉ chordBonds S) : minimizingCoordinates a S V ρ b.1 b.2 = 0 := by
  classical
  unfold minimizingCoordinates
  split_ifs with h
  · exact h.choose_spec.1 b hb
  · rfl
theorem not_mem_chordBonds_of_tree {S : Finset F.Cell} {b : F.Site F.depth × Fin 4} (hb : IsAxialTreeBond b) :
    b ∉ chordBonds S := by
  classical
  intro h
  exact (Finset.mem_filter.mp h).2 hb
end Frames
variable {n : ℕ} [NeZero n] {R : StepSetup} {s : ChartSetting R n} {c : SettingCore R n}
  {K : Finset (TorusSite (n * R.params.side))} {D : ℕ} {S₀ S : Finset (TorusSite n)} {g s' : ℝ}
variable (ζ : s.freeNear (blocksNear R.params.side R.range K) → EuclideanSpace ℝ (Fin 3))
open GroupMoves TorusMinimizer ShareStability ContourStability
theorem torusSiteInFrame_add_unitStep (L : ℕ) [NeZero L] (x : TorusSite (n * L)) (i : Fin 4) :
    torusSiteInFrame (stepBlockFrame L n) 0 x + BlockAverages.unitStep (F := stepBlockFrame L n) 0 i =
      torusSiteInFrame (stepBlockFrame L n) 0 (x + unitStep (n * L) i) := by
  apply toTorusSite_injective (F := stepBlockFrame L n) (j := 0) (N := n * L) period_stepBlockFrame_zero
  rw [toTorusSite_add period_stepBlockFrame_zero, toTorusSite_torusSiteInFrame period_stepBlockFrame_zero,
    toTorusSite_torusSiteInFrame period_stepBlockFrame_zero, toTorusSite_unitStep period_stepBlockFrame_zero]
theorem minimizerCoord_of_tree (hL : Odd R.params.side) (h2 : 2 ≤ n) {b : TorusBond (n * R.params.side)}
    (ht : IsAxialTreeBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1, b.2)) :
    minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse b = 0 :=
  minimizingCoordinates_of_not_mem (not_mem_chordBonds_of_tree ((isAxialTreeBond_frames_iff hL h2 R.depth b.1 b.2).mpr ht))
theorem frame_of_tree (hL : Odd R.params.side) (h2 : 2 ≤ n) (hm4 : 2 ≤ 4 * R.frameReach) {b : TorusBond (n * R.params.side)}
    (ht : IsAxialTreeBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1, b.2)) :
    s.frame b = 0 := by
  classical
  set F := torusFrame R.params.side R.depth n with hF
  have htop : IsAxialTreeBond (F := F) (torusSiteInFrame F F.depth b.1, b.2) :=
    (isAxialTreeBond_frames_iff hL h2 R.depth b.1 b.2).mpr ht
  have hL' : Odd F.blockSide := hL
  have hs : ∀ i, 2 ≤ F.extent i := fun _ => h2
  unfold ChartSetting.frame frameCoord bondFrameCoord
  split_ifs with hbig
  · unfold reflectedBondCoord minimizingBondCoordinate reflectedBond
    set M := reflectedFrame F R.frameReach with hM
    have hLM : Odd M.blockSide := hL
    have hsM : ∀ i, 2 ≤ M.extent i := fun _ => hm4
    obtain ⟨ho, he⟩ := centre_cellOffset hL' hs (torusSiteInFrame F F.depth b.1)
    have hoM : cellOffset (torusSiteInFrame F F.depth b.1) ∈ centredCube M.blockSide := ho
    have t1 : IsTreeOffset F.blockSide (cellOffset (torusSiteInFrame F F.depth b.1), b.2) := by
      have := (isAxialTreeBond_iff hL' hs (enclosingCell (torusSiteInFrame F F.depth b.1)) _ ho b.2).mp
        (by rw [he]; exact htop)
      exact this
    have t2 : IsAxialTreeBond (F := M)
        (cellCentre M.depth (0 : M.Cell) + siteOfCoords M.depth (cellOffset (torusSiteInFrame F F.depth b.1)), b.2) :=
      (isAxialTreeBond_iff hLM hsM 0 _ hoM b.2).mpr t1
    have e0 : (cellCentre M.depth (0 : M.Cell) : M.Site M.depth) = 0 := by
      funext l
      simp [cellCentre, siteCoords, siteOfCoords]
    rw [e0, zero_add] at t2
    exact minimizingCoordinates_of_not_mem (b := (siteOfCoords M.depth (cellOffset (torusSiteInFrame F F.depth b.1)), b.2))
      (not_mem_chordBonds_of_tree t2)
  · exact minimizingCoordinates_of_not_mem (not_mem_chordBonds_of_tree htop)
theorem chartCoord_minimizerOn (hb : NearPieceData s c K D S₀ S g s') (b : TorusBond (n * R.params.side)) :
    chartCoord R.params s.coarse (minimizerOn s S) b =
      minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse b := by
  classical
  have hL := hb.sizes.admissible.L_odd
  have h2 := hb.two_le
  obtain ⟨x, i⟩ := b
  set F := stepBlockFrame R.params.side n with hF
  have htree : ∀ y : TorusSite (n * R.params.side), gaugeAt (R := R) (minimizerOn s S) y = 1 := fun y =>
    gaugeAt_eq_one_of hL h2 _ y fun b _ ht => by
      have hc : ¬ IsCrossingBond (F := stepBlockFrame R.params.side n)
          (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1, b.2) := ht.1
      simp only [minimizerOn]
      rw [minimizingField_apply hL h2, if_neg hc, if_pos ht]
  have g1 : axialGauge 1 (readAtLevel F F.depth (minimizerOn s S)) (torusSiteInFrame F F.depth x) = 1 := htree x
  have g2 : axialGauge 1 (readAtLevel F F.depth (minimizerOn s S))
      (torusSiteInFrame F F.depth x + BlockAverages.unitStep F.depth i) = 1 := by
    have e : (torusSiteInFrame F F.depth x + BlockAverages.unitStep F.depth i : F.Site F.depth) =
        torusSiteInFrame F F.depth (x + unitStep (n * R.params.side) i) :=
      torusSiteInFrame_add_unitStep R.params.side x i
    rw [e]
    exact htree _
  have hread : readAtLevel F F.depth (minimizerOn s S) (torusSiteInFrame F F.depth x) i = minimizerOn s S x i :=
    readAtLevel_torusSiteInFrame period_stepBlockFrame_zero _ x i
  have hg : gaugeTransform (j := F.depth) (axialGauge 1 (readAtLevel F F.depth (minimizerOn s S)))
      (readAtLevel F F.depth (minimizerOn s S)) (torusSiteInFrame F F.depth x) i = minimizerOn s S x i := by
    unfold BlockAverages.gaugeTransform
    rw [g1, hread, g2]
    simp
  have hw := hb.minimizer_small (x, i)
  have hcell : readAtLevel F 1 s.coarse (enclosingCell (torusSiteInFrame F 0 x)) i = s.coarse (parentBlock R.params.side x) i := by
    have e : enclosingCell (torusSiteInFrame F F.depth x) = torusSiteInFrame F F.top (parentBlock R.params.side x) :=
      enclosingCell_torusSiteInFrame (F := F) (n := n) (fun _ => rfl) x
    have : enclosingCell (torusSiteInFrame F 0 x) = torusSiteInFrame F 1 (parentBlock R.params.side x) := e
    rw [this]
    exact readAtLevel_torusSiteInFrame period_stepBlockFrame_one s.coarse _ i
  unfold chartCoord LumpContours.bondCoordinate
  simp only
  have hg' : gaugeTransform (axialGauge 1 (readAtLevel F 0 (minimizerOn s S))) (readAtLevel F 0 (minimizerOn s S))
      (torusSiteInFrame F 0 x) i = minimizerOn s S x i := hg
  by_cases h1 : IsCrossingBond (F := F) (torusSiteInFrame F 0 x, i)
  · rw [if_pos h1]
    have e1 : minimizerOn s S x i =
        expUnit (minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse (x, i)) *
          s.coarse (parentBlock R.params.side x) i := by
      simp only [minimizerOn]
      rw [minimizingField_apply hL h2, if_pos h1]
    have e3 : gaugeTransform (axialGauge 1 (readAtLevel F 0 (minimizerOn s S))) (readAtLevel F 0 (minimizerOn s S))
        (torusSiteInFrame F 0 x) i * (readAtLevel F 1 s.coarse (enclosingCell (torusSiteInFrame F 0 x)) i)⁻¹ =
        expUnit (minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse (x, i)) := by
      rw [hg', hcell, e1]
      group
    have e4 := minimalLog_expUnit_of_norm_lt_pi hw
    rw [← e3] at e4
    exact e4
  · rw [if_neg h1]
    by_cases h3 : IsAxialTreeBond (F := F) (torusSiteInFrame F 0 x, i)
    · have e1 : minimizerOn s S x i = 1 := by
        simp only [minimizerOn]
        rw [minimizingField_apply hL h2, if_neg h1, if_pos h3]
      have e3 : minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse (x, i) = 0 :=
        minimizerCoord_of_tree hL h2 h3
      rw [hg', e1, e3]
      have e4 := minimalLog_expUnit_of_norm_lt_pi (w := 0) (by simpa using Real.pi_pos)
      rw [_root_.YangMills.Construction.ClusterExpansionOfAStep.GroupMoves.expUnit_zero_eq_one] at e4
      exact e4
    · have e1 : minimizerOn s S x i =
          expUnit (minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse (x, i)) := by
        simp only [minimizerOn]
        rw [minimizingField_apply hL h2, if_neg h1, if_neg h3]
      rw [hg', e1]
      exact minimalLog_expUnit_of_norm_lt_pi hw
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
variable {n : ℕ} [NeZero n] {R : StepSetup} {s : ChartSetting R n} {c : SettingCore R n}
  {K : Finset (TorusSite (n * R.params.side))} {D : ℕ} {S₀ S : Finset (TorusSite n)} {g s' : ℝ}
variable (ζ : s.freeNear (blocksNear R.params.side R.range K) → EuclideanSpace ℝ (Fin 3))
open GroupMoves TorusMinimizer ShareStability ContourStability
theorem splicedField_eq_fine (hb : NearPieceData s c K D S₀ S g s') (x : TorusSite (n * R.params.side)) (i : Fin 4)
    (hz : parentBlock R.params.side x ∈ thickening D (blocksNear R.params.side R.range K))
    (h1 : parentBlock R.params.side x ∈ s.storedBlockSet c)
    (h2 : parentBlock R.params.side (x + unitStep (n * R.params.side) i) ∈ s.storedBlockSet c) :
    splicedField s K D S ζ x i = s.fine x i := by
  classical
  rw [splicedField_of_mem ζ x i hz]
  have hnf : (x, i) ∉ s.free := by
    rw [hb.core.free_eq]
    intro h
    exact (Finset.mem_filter.mp h).2.2 ⟨h1, h2⟩
  simp only [nearPieceField, ChartSetting.field, dif_neg hnf]
theorem axialGauge_splicedField (hb : NearPieceData s c K D S₀ S g s') (y : TorusSite (n * R.params.side))
    (hz : parentBlock R.params.side y ∈ thickening D (blocksNear R.params.side R.range K))
    (h1 : parentBlock R.params.side y ∈ s.storedBlockSet c) :
    axialGauge 1 (readAtLevel (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth (splicedField s K D S ζ))
        (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth y) =
      axialGauge 1 (readAtLevel (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth s.fine)
        (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth y) := by
  classical
  set F := stepBlockFrame R.params.side n with hF
  have hL : Odd F.blockSide := hb.sizes.admissible.L_odd
  have hs : ∀ i, 2 ≤ F.extent i := fun _ => hb.two_le
  refine axialGauge_congr hs hL _ _ _ fun b hbb => ?_
  have hb1 : b.1 ∈ sitesBelow F.depth (enclosingCell (torusSiteInFrame F F.depth y)) :=
    (Finset.mem_product.mp (Finset.mem_filter.mp hbb).1).1
  have hb2 : b.1 + BlockAverages.unitStep F.depth b.2 ∈ sitesBelow F.depth (enclosingCell (torusSiteInFrame F F.depth y)) :=
    (Finset.mem_filter.mp hbb).2
  have hcell : ∀ {u : F.Site F.depth}, u ∈ sitesBelow F.depth (enclosingCell (torusSiteInFrame F F.depth y)) →
      parentBlock R.params.side (toTorusSite (n * R.params.side) u) = parentBlock R.params.side y := by
    intro u hu
    have e1 := parentBlock_toTorusSite (F := F) (n := n) (fun _ => rfl) u
    have e2 := enclosingCell_of_mem_sitesBelow hL hs hu
    have e3 := parentBlock_toTorusSite (F := F) (n := n) (fun _ => rfl) (torusSiteInFrame F F.depth y)
    have e4 : toTorusSite (n * F.blockSide) (torusSiteInFrame F F.depth y) = y :=
      toTorusSite_torusSiteInFrame period_stepBlockFrame_zero y
    rw [e2, ← e3, e4] at e1
    exact e1
  have hnext : toTorusSite (n * R.params.side) b.1 + unitStep (n * R.params.side) b.2 =
      toTorusSite (n * R.params.side) (b.1 + BlockAverages.unitStep F.depth b.2) := by
    have e1 := toTorusSite_add (F := F) (j := F.depth) (N := n * R.params.side) period_stepBlockFrame_zero b.1
      (BlockAverages.unitStep F.depth b.2)
    have e2 := toTorusSite_unitStep (F := F) (j := F.depth) (N := n * R.params.side) period_stepBlockFrame_zero b.2
    rw [e1, e2]
  have h3 := hcell hb1
  have h4 := hcell hb2
  rw [← hnext] at h4
  exact splicedField_eq_fine ζ hb _ _ (h3 ▸ hz) (h3 ▸ h1) (h4 ▸ h1)
theorem chartCoord_splicedField (hb : NearPieceData s c K D S₀ S g s') (b : TorusBond (n * R.params.side))
    (hz1 : parentBlock R.params.side b.1 ∈ thickening D (blocksNear R.params.side R.range K))
    (hz2 : parentBlock R.params.side (b.1 + unitStep (n * R.params.side) b.2) ∈
      thickening D (blocksNear R.params.side R.range K))
    (h1 : parentBlock R.params.side b.1 ∈ s.storedBlockSet c)
    (h2 : parentBlock R.params.side (b.1 + unitStep (n * R.params.side) b.2) ∈ s.storedBlockSet c) :
    chartCoord R.params s.coarse (splicedField s K D S ζ) b = chartCoord R.params s.coarse s.fine b := by
  have t1 := axialGauge_splicedField ζ hb b.1 hz1 h1
  have t2 := axialGauge_splicedField ζ hb (b.1 + unitStep (n * R.params.side) b.2) hz2 h2
  have e : (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth b.1 +
      BlockAverages.unitStep (stepBlockFrame R.params.side n).depth b.2 :
      (stepBlockFrame R.params.side n).Site (stepBlockFrame R.params.side n).depth) =
      torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth
        (b.1 + unitStep (n * R.params.side) b.2) :=
    torusSiteInFrame_add_unitStep R.params.side b.1 b.2
  have hv : readAtLevel (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth (splicedField s K D S ζ)
      (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth b.1) b.2 =
      readAtLevel (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth s.fine
        (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth b.1) b.2 := by
    have r1 : ∀ W : TorusField (n * R.params.side),
        readAtLevel (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth W
          (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth b.1) b.2 =
          W b.1 b.2 := fun W =>
      readAtLevel_torusSiteInFrame (F := stepBlockFrame R.params.side n) (j := (stepBlockFrame R.params.side n).depth)
        period_stepBlockFrame_zero W b.1 b.2
    rw [r1, r1]
    exact splicedField_eq_fine ζ hb _ _ hz1 h1 h2
  have t2' : axialGauge 1
      (readAtLevel (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth (splicedField s K D S ζ))
      (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth b.1 +
        BlockAverages.unitStep (stepBlockFrame R.params.side n).depth b.2) =
      axialGauge 1 (readAtLevel (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth s.fine)
      (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).depth b.1 +
        BlockAverages.unitStep (stepBlockFrame R.params.side n).depth b.2) := by
    rw [e]
    exact t2
  unfold chartCoord
  exact bondCoordinate_congr (F := stepBlockFrame R.params.side n) _ hv t1 t2'
theorem card_badBlocksOff_le (hb : NearPieceData s c K D S₀ S g s') (hm4 : 2 ≤ 4 * R.frameReach)
    (hbad : ∀ b ∈ c.badBonds, b.1 ∈ K →
      5 * R.ballRadius / 8 ≤ ‖(frameDeviation R.params R.anchorRadius R.depth R.frameReach s.coarse s.fine b : ℍ[ℝ])‖) :
    (badBlocksOff R.params.side c.badBonds c.core K).card ≤
      (chartDeviationSites R.params (R.params.threshold / 128) S s.coarse (splicedField s K D S ζ) (minimizerOn s S)).card := by
  classical
  refine Finset.card_le_card fun Y hY => ?_
  obtain ⟨hY1, hYC⟩ := Finset.mem_sdiff.mp hY
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hY1
  obtain ⟨hu1, huK⟩ := Finset.mem_inter.mp hu
  obtain ⟨b, hbb, rfl⟩ := Finset.mem_image.mp hu1
  have hfit := hb.sizes.admissible
  have hD := hb.depth_ge
  have hN : parentBlock R.params.side b.1 ∈ blocksNear R.params.side R.range K :=
    mem_blocksNear.mpr ⟨b.1, rfl, b.1, huK, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩
  have hnext := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_add_unitStep_le hb b.1 b.2
  have hz1 : parentBlock R.params.side b.1 ∈ thickening D (blocksNear R.params.side R.range K) := mem_thickening_self _ hN
  have hz2 : parentBlock R.params.side (b.1 + unitStep (n * R.params.side) b.2) ∈
      thickening D (blocksNear R.params.side R.range K) :=
    thickening_mono (by omega) (mem_thickening_add (mem_thickening_self 0 hN) hnext)
  have hpt : b.1 ∈ pieceSites s c := Finset.mem_union_left _ (Finset.mem_union_left _ hu1)
  have st1 : parentBlock R.params.side b.1 ∈ s.storedBlockSet c :=
    (mem_storedBlockSet s c).mpr (Or.inr ⟨b.1, rfl, b.1, hpt, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
  have st2 : parentBlock R.params.side (b.1 + unitStep (n * R.params.side) b.2) ∈ s.storedBlockSet c :=
    (mem_storedBlockSet s c).mpr (Or.inr ⟨_, rfl, b.1, hpt, by
      have := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le b.1 b.2
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at this
      have := hb.sizes.range_large
      omega⟩)
  refine Finset.mem_filter.mpr ⟨hb.mem_cut_of_not_core _ hYC, b, ?_, rfl, ?_⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_sitesInBlocks.mpr (hb.mem_cut_of_not_core _ hYC),
      mem_sitesInBlocks.mpr (hb.mem_cut_of_near_not_core _ hYC _ hnext)⟩
  · rw [chartCoord_splicedField ζ hb b hz1 hz2 st1 st2, chartCoord_minimizerOn hb]
    have hfar := hbad b hbb huK
    have hσ : R.params.threshold / 128 = R.ballRadius / 2 := by
      unfold StepSetup.ballRadius
      ring
    have hgap : ‖(s.frame b : ℍ[ℝ]) -
        (minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse b : ℍ[ℝ])‖ ≤ g := by
      by_cases ht : IsAxialTreeBond (F := stepBlockFrame R.params.side n)
          (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1, b.2)
      · rw [frame_of_tree hfit.L_odd hb.two_le hm4 ht, minimizerCoord_of_tree hfit.L_odd hb.two_le ht]
        simpa using hb.gap_nonneg
      · exact hb.frames_near b (mem_chartBonds_iff.mpr ht) hYC
    have he : (frameDeviation R.params R.anchorRadius R.depth R.frameReach s.coarse s.fine b : ℍ[ℝ]) =
        (chartCoord R.params s.coarse s.fine b : ℍ[ℝ]) - (s.frame b : ℍ[ℝ]) := rfl
    rw [he] at hfar
    have h3 : (chartCoord R.params s.coarse s.fine b : ℍ[ℝ]) - (s.frame b : ℍ[ℝ]) =
        ((chartCoord R.params s.coarse s.fine b : ℍ[ℝ]) -
          (minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse b : ℍ[ℝ])) -
          ((s.frame b : ℍ[ℝ]) -
            (minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse b : ℍ[ℝ])) := by abel
    rw [h3] at hfar
    have h4 := norm_sub_le ((chartCoord R.params s.coarse s.fine b : ℍ[ℝ]) -
        (minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse b : ℍ[ℝ]))
      ((s.frame b : ℍ[ℝ]) - (minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse b : ℍ[ℝ]))
    have h5 := hb.gap_le
    rw [hσ]
    linarith
theorem sum_share_add_le_sum_splicedCost (hSA : SharesSumToAction) (hH : TorusFrames.hotLumpsOfStepStatement)
    (hb : NearPieceData s c K D S₀ S g s') (hζ : s.InBalls (s.extendByZero _ ζ)) (hm4 : 2 ≤ 4 * R.frameReach) {cE : ℝ}
    (hcE : 0 ≤ cE) {m : ℕ}
    (hbadK : ∀ b ∈ c.badBonds, b.1 ∈ K →
      5 * R.ballRadius / 8 ≤ ‖(frameDeviation R.params R.anchorRadius R.depth R.frameReach s.coarse s.fine b : ℍ[ℝ])‖)
    (hsave : HoleSavingOnTorus R.params cE R.depth S₀ S m s.coarse (splicedField s K D S ζ) (minimizerOn s S)
      (splicedBases s (thickening D (blocksNear R.params.side R.range K)))) :
    ∑ Y : TorusSite n, levelShare R.params.coupling R.params.side (R.depth + 1) S Y s.coarse +
        (6 * R.params.κ * R.params.threshold ^ 2 * m +
          R.params.κ / 4 * R.params.threshold ^ 2 * ((s.lumpsInPiece K).card : ℝ) +
          cE * ((badBlocksOff R.params.side c.badBonds c.core K).card : ℝ) -
          R.params.κ * R.params.threshold ^ 2 * ((s.lumpsInPiece K).card : ℝ)) ≤
      ∑ Y : TorusSite n, splicedCost s K D S₀ S ζ Y := by
  classical
  have hfit := hb.sizes.admissible
  have ha : 0 ≤ R.params.coupling := by have := hfit.a_ge; linarith
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have h2 := hb.two_le
  have hnL : 2 ≤ n * R.params.side := by nlinarith
  unfold HoleSavingOnTorus at hsave
  rw [card_splicedLumps ζ hb hζ, stepLumpSites_splicedLumps ζ hb hζ] at hsave
  have e1 := sum_levelShare hSA ha hL0 h2 (R.depth + 1) S s.coarse
  have e2 := sum_levelShare hSA ha hL0 hnL R.depth (splicedRegion s K S₀) (splicedField s K D S ζ)
  have e3 : ∑ Y : TorusSite n, splicedCost s K D S₀ S ζ Y =
      actionAtLevel R.params.coupling R.params.side R.depth (splicedRegion s K S₀) (splicedField s K D S ζ) +
        R.params.coupling * ∑ e ∈ bondsWithin S₀, splicedFit s K D S₀ S ζ e := by
    unfold splicedCost
    rw [Finset.sum_add_distrib, sum_sitesInBlocks, ← Finset.mul_sum, sum_halfFitsWithin, e2]
  have hbad := card_badBlocksOff_le ζ hb hm4 hbadK
  have hbad' : cE * ((badBlocksOff R.params.side c.badBonds c.core K).card : ℝ) ≤
      cE * ((chartDeviationSites R.params (R.params.threshold / 128) S s.coarse (splicedField s K D S ζ)
        (minimizerOn s S)).card : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hbad) hcE
  rw [e3, e1]
  linarith
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
theorem two_mul_supDist_le {m : ℕ} [NeZero m] (x y : TorusSite m) : 2 * _root_.YangMills.Construction.TorusFields.supDist x y ≤ m := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.two_mul_supDist_le <;> assumption
variable {n : ℕ} [NeZero n] {R : StepSetup} {s : ChartSetting R n} {c : SettingCore R n}
  {K : Finset (TorusSite (n * R.params.side))} {D : ℕ} {S₀ S : Finset (TorusSite n)} {g s' : ℝ}
open GroupMoves TorusMinimizer ShareStability ContourStability
def blockError (Nb : Finset (TorusSite n)) (D : ℕ) (ein wgt cc : ℝ) (Y : TorusSite n) : ℝ :=
  open Classical in
  if Y ∈ thickening (4 * D) Nb then ein
  else wgt * ∑ Y₀ ∈ Nb, if 4 * D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y₀ then Real.exp (-(cc * _root_.YangMills.Construction.TorusFields.supDist Y Y₀)) else 0
theorem card_thickening_le (m : ℕ) (Nb : Finset (TorusSite n)) :
    (thickening m Nb).card ≤ Nb.card * (2 * m + 1) ^ 4 := by
  classical
  have hsub : thickening m Nb ⊆ Nb.biUnion fun y => thickening m ({y} : Finset (TorusSite n)) := by
    intro z hz
    obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp hz
    exact Finset.mem_biUnion.mpr ⟨x, hx, (mem_thickening _ _ _).mpr ⟨x, Finset.mem_singleton_self _, hd⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  have := Finset.sum_le_card_nsmul Nb (fun y => (thickening m ({y} : Finset (TorusSite n))).card) ((2 * m + 1) ^ 4)
    (fun y _ => card_thickening_singleton_le m y)
  simpa using this
theorem sum_blockError_le {Nb : Finset (TorusSite n)} {ein wgt cc A' : ℝ} (hein : 0 ≤ ein) (hw : 0 ≤ wgt)
    (hA' : ∀ (y : TorusSite n) (Dd : ℕ), ∑ Y ∈ Finset.univ.filter (fun Y : TorusSite n => Dd ≤ _root_.YangMills.Construction.TorusFields.supDist Y y),
      Real.exp (-(cc * _root_.YangMills.Construction.TorusFields.supDist Y y)) ≤ A' * Real.exp (-(cc * Dd / 2))) :
    ∑ Y : TorusSite n, blockError Nb D ein wgt cc Y ≤
      Nb.card * (((2 * (4 * D : ℕ) + 1 : ℕ) : ℝ) ^ 4 * ein + wgt * (A' * Real.exp (-(cc * (4 * D : ℕ) / 2)))) := by
  classical
  have h1 : ∀ Y : TorusSite n, blockError Nb D ein wgt cc Y ≤ (if Y ∈ thickening (4 * D) Nb then ein else 0) +
      wgt * ∑ Y₀ ∈ Nb, if 4 * D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y₀ then Real.exp (-(cc * _root_.YangMills.Construction.TorusFields.supDist Y Y₀)) else 0 := by
    intro Y
    have hnn : 0 ≤ wgt * ∑ Y₀ ∈ Nb, if 4 * D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y₀ then Real.exp (-(cc * _root_.YangMills.Construction.TorusFields.supDist Y Y₀)) else 0 := by
      refine mul_nonneg hw (Finset.sum_nonneg fun Y₀ _ => ?_)
      split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
    unfold blockError
    split_ifs with h
    · linarith
    · simp
  refine (Finset.sum_le_sum fun Y _ => h1 Y).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
  have h2 : ∑ Y : TorusSite n, (if Y ∈ thickening (4 * D) Nb then ein else 0) ≤
      (Nb.card : ℝ) * ((2 * (4 * D : ℕ) + 1 : ℕ) : ℝ) ^ 4 * ein := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    have h3 := card_thickening_le (4 * D) Nb
    have h4 : ((thickening (4 * D) Nb).card : ℝ) ≤ (Nb.card : ℝ) * ((2 * (4 * D : ℕ) + 1 : ℕ) : ℝ) ^ 4 := by
      exact_mod_cast h3
    exact mul_le_mul_of_nonneg_right h4 hein
  have h3 : ∑ Y₀ ∈ Nb, ∑ Y : TorusSite n, (if 4 * D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y₀ then Real.exp (-(cc * _root_.YangMills.Construction.TorusFields.supDist Y Y₀)) else 0) ≤
      Nb.card * (A' * Real.exp (-(cc * (4 * D : ℕ) / 2))) := by
    have hone : ∀ Y₀ ∈ Nb, ∑ Y : TorusSite n, (if 4 * D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y₀ then Real.exp (-(cc * _root_.YangMills.Construction.TorusFields.supDist Y Y₀)) else 0) ≤
        A' * Real.exp (-(cc * (4 * D : ℕ) / 2)) := by
      intro Y₀ _
      rw [← Finset.sum_filter]
      exact hA' Y₀ (4 * D)
    have := Finset.sum_le_card_nsmul Nb _ _ hone
    simpa using this
  have h4 := mul_le_mul_of_nonneg_left h3 hw
  nlinarith
theorem ten_mul_range_lt (hb : NearPieceData s c K D S₀ S g s') (hNb : (blocksNear R.params.side R.range K).Nonempty)
    {Y₁ : TorusSite n} (hY₁ : Y₁ ∉ blocksNear R.params.side R.range K) : 10 * R.range < n * R.params.side := by
  classical
  obtain ⟨Y₀, hY₀⟩ := hNb
  obtain ⟨z, -, u, hu, -⟩ := mem_blocksNear.mp hY₀
  obtain ⟨y₁, hy₁⟩ := exists_parentBlock_eq (L := R.params.side) hb.sizes.admissible.L_odd hb.two_le Y₁
  have h1 : 5 * R.range < _root_.YangMills.Construction.TorusFields.supDist y₁ u := by
    by_contra hcon
    exact hY₁ (mem_blocksNear.mpr ⟨y₁, hy₁, u, hu, not_lt.mp hcon⟩)
  have := two_mul_supDist_le y₁ u
  omega
variable (ζ : s.freeNear (blocksNear R.params.side R.range K) → EuclideanSpace ℝ (Fin 3))
theorem supDist_parentBlock_box_le_sub_one (hb : NearPieceData s c K D S₀ S g s') {y : TorusSite (n * R.params.side)}
    {Dh : ℕ} (hDh : 3 ≤ Dh) {h : Fin 4 → ℤ} (hh : OffsetInBox (R.params.side * (Dh - 2) + 1) h) :
    _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side (y + siteOfInt h)) (parentBlock R.params.side y) ≤ Dh - 1 := by
  have h1 := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_box_le (s := s) (c := c) hb (y := y) hh
  have hL := hb.sizes.admissible.L_ge
  have h3 : (R.params.side * (Dh - 2) + 1) / R.params.side = Dh - 2 := by
    have hL0 : 0 < R.params.side := by omega
    rw [Nat.mul_add_div hL0]
    have : 1 / R.params.side = 0 := Nat.div_eq_of_lt (by omega)
    omega
  omega
theorem offsetInBox_succ {ρ : ℕ} {h : Fin 4 → ℤ} (hh : OffsetInBox ρ h) : OffsetInBox (ρ + 1) h :=
  fun i => (hh i).trans (by push_cast; omega)
section Bounds
variable {A δ s₀ : ℝ} (hSh : ShareLocality R.params.coupling R.params.side s₀ A δ) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
  (hs₀ : R.params.threshold ≤ s₀) (h64 : 64 ≤ n * R.params.side) (hc : ComplementOfThickenedLumpsRegular)
  (hH : TorusFrames.hotLumpsOfStepStatement) (hb : NearPieceData s c K D S₀ S g s')
  (hζ : s.InBalls (s.extendByZero _ ζ)) (hsp : ShareSplitsOn s S) {Dh : ℕ} (hD1 : 2 * Dh + 14 ≤ D) (hD2 : 16 ≤ Dh)
include hSh hA hδ hs₀ h64 hc hH hb hζ hsp hD1 hD2
theorem abs_blockCost_sub_splicedCost_le_near (hNb : (blocksNear R.params.side R.range K).Nonempty) {Y : TorusSite n}
    (hY : Y ∈ thickening Dh (blocksNear R.params.side R.range K)) :
    |blockCost R.params R.depth (nearPieceField s _ ζ) s.coarse s.bases Y - splicedCost s K D S₀ S ζ Y| ≤
      (2 * R.params.side + 1) ^ 4 * (A * Real.exp (-(δ * (R.params.side * (Dh - 2) : ℕ)))) := by
  classical
  have hY13 : Y ∈ thickening (D - 13) (blocksNear R.params.side R.range K) := thickening_mono (by omega) hY
  have he : 0 ≤ A * Real.exp (-(δ * (R.params.side * (Dh - 2) : ℕ))) := mul_nonneg hA (Real.exp_pos _).le
  by_cases hall : ∀ Z : TorusSite n, Z ∈ blocksNear R.params.side R.range K
  · refine abs_blockCost_sub_splicedCost_le ζ hH hb hζ hY13 he fun y hy => ?_
    have e1 : splicedRegion s K S₀ = settingRegion s := by
      ext z
      exact (mem_settingRegion_iff_of_near hb (mem_thickening_self _ (hall _))).symm
    have e2 : splicedField s K D S ζ = nearPieceField s _ ζ := by
      funext x i
      exact splicedField_of_mem ζ x i (mem_thickening_self _ (hall _))
    rw [e1, e2, sub_self, abs_zero]
    exact he
  · push Not at hall
    obtain ⟨Y₁, hY₁⟩ := hall
    have hemb := ten_mul_range_lt hb hNb hY₁
    have hzone := hb.sizes.zone_le
    have hρ : 2 * (R.params.side * (Dh - 2)) + 2 < n * R.params.side := by
      have hL := hb.sizes.admissible.L_ge
      have h1 : 2 * (R.params.side * (Dh - 2)) ≤ R.params.side * (D + 8) := by
        have : 2 * (Dh - 2) ≤ D + 8 := by omega
        calc 2 * (R.params.side * (Dh - 2)) = R.params.side * (2 * (Dh - 2)) := by ring
          _ ≤ R.params.side * (D + 8) := Nat.mul_le_mul_left _ this
      have := hb.sizes.range_large
      omega
    refine abs_blockCost_sub_splicedCost_le ζ hH hb hζ hY13 he fun y hy => ?_
    refine abs_share_near_sub_spliced_le ζ hSh hs₀ h64 hc hH hb hζ R.depth hρ fun h hh => ?_
    have h1 := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_box_le_sub_one hb (y := y) (by omega : 3 ≤ Dh) (offsetInBox_succ hh)
    rw [hy] at h1
    exact thickening_mono (by omega) (mem_thickening_add hY h1)
end Bounds
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
variable {n : ℕ} [NeZero n] {R : StepSetup} {s : ChartSetting R n} {c : SettingCore R n}
  {K : Finset (TorusSite (n * R.params.side))} {D : ℕ} {S₀ S : Finset (TorusSite n)} {g s' : ℝ}
variable (ζ : s.freeNear (blocksNear R.params.side R.range K) → EuclideanSpace ℝ (Fin 3))
open GroupMoves TorusMinimizer ShareStability ContourStability
def shareDebt (A δ : ℝ) (ρ₀ : ℕ) : ℝ := A * Real.exp (-(δ * ρ₀))
def movedDebt (A δ g : ℝ) (ρ₀ : ℕ) : ℝ := shareDebt A δ ρ₀ + ((4 * (2 * ρ₀ + 1) ^ 4 : ℕ) : ℝ) * (A * (2 * g))
def nearDebt (R : StepSetup) (A δ g : ℝ) (ρ₀ : ℕ) : ℝ :=
  (2 * (R.params.side : ℝ) + 1) ^ 4 * shareDebt A δ ρ₀ +
    ((2 * (R.params.side : ℝ) + 1) ^ 4 * movedDebt A δ g ρ₀ + R.params.coupling * (4 * (10 * R.params.side * (2 * g))))
section Bounds
variable {A δ s₀ : ℝ} (hSh : ShareLocality R.params.coupling R.params.side s₀ A δ) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
  (hs₀ : R.params.threshold ≤ s₀) (h64 : 64 ≤ n * R.params.side) (hc : ComplementOfThickenedLumpsRegular)
  (hH : TorusFrames.hotLumpsOfStepStatement) (hb : NearPieceData s c K D S₀ S g s')
  (hζ : s.InBalls (s.extendByZero _ ζ)) (hsp : ShareSplitsOn s S) {Dh : ℕ} (hD1 : 2 * Dh + 14 ≤ D) (hD2 : 16 ≤ Dh)
include hb hD1 hD2 in
theorem two_mul_radius_add_two_lt (hNb : (blocksNear R.params.side R.range K).Nonempty) {Y₁ : TorusSite n}
    (hY₁ : Y₁ ∉ blocksNear R.params.side R.range K) : 2 * (R.params.side * (Dh - 2)) + 2 < n * R.params.side := by
  have hemb := ten_mul_range_lt hb hNb hY₁
  have hzone := hb.sizes.zone_le
  have h1 : 2 * (R.params.side * (Dh - 2)) ≤ R.params.side * (D + 8) := by
    have : 2 * (Dh - 2) ≤ D + 8 := by omega
    calc 2 * (R.params.side * (Dh - 2)) = R.params.side * (2 * (Dh - 2)) := by ring
      _ ≤ R.params.side * (D + 8) := Nat.mul_le_mul_left _ this
  have := hb.sizes.range_large
  omega
theorem shareDebt_nonneg (hA : 0 ≤ A) (ρ₀ : ℕ) : 0 ≤ shareDebt A δ ρ₀ := mul_nonneg hA (Real.exp_pos _).le
theorem movedDebt_nonneg (hA : 0 ≤ A) (hg : 0 ≤ g) (ρ₀ : ℕ) : 0 ≤ movedDebt A δ g ρ₀ := by
  unfold movedDebt
  have := shareDebt_nonneg (δ := δ) hA ρ₀
  positivity
theorem nearDebt_nonneg (ha : 0 ≤ R.params.coupling) (hA : 0 ≤ A) (hg : 0 ≤ g) (ρ₀ : ℕ) : 0 ≤ nearDebt R A δ g ρ₀ := by
  unfold nearDebt
  have := shareDebt_nonneg (δ := δ) hA ρ₀
  have := movedDebt_nonneg (δ := δ) hA hg ρ₀
  positivity
theorem card_bondsOfBox_cast_le [NeZero (n * R.params.side)] (y : TorusSite (n * R.params.side)) (ρ : ℕ) :
    ((bondsOfBox y ρ).card : ℝ) ≤ ((4 * (2 * ρ + 1) ^ 4 : ℕ) : ℝ) := by
  exact_mod_cast card_bondsOfBox_le y ρ
include hSh hA hδ hs₀ h64 hc hH hb hζ hsp hD1 hD2
theorem abs_block_debt_le_near (hNb : (blocksNear R.params.side R.range K).Nonempty) {Y : TorusSite n}
    (hYN : Y ∉ blocksNear R.params.side R.range K) (hY : Y ∈ thickening Dh (blocksNear R.params.side R.range K)) :
    |(blockCost R.params R.depth (nearPieceField s _ ζ) s.coarse s.bases Y -
        blockCost R.params R.depth (s.field 0) s.coarse s.bases Y) -
      (splicedCost s K D S₀ S ζ Y - levelShare R.params.coupling R.params.side (R.depth + 1) S Y s.coarse)| ≤
      nearDebt R A δ g (R.params.side * (Dh - 2)) := by
  classical
  have hρ : 0 ≤ R.ballRadius := by
    have := hb.sizes.admissible.σ_pos
    unfold StepSetup.ballRadius
    positivity
  have hW0 : torusHotLumps R.params (s.field 0) = torusHotLumps R.params s.fine :=
    hb.admissible.hotLumps_eq 0 (inBalls_zero hρ)
  have hemb := two_mul_radius_add_two_lt hb hD1 hD2 hNb hYN
  have h1 := abs_blockCost_sub_splicedCost_le_near ζ hSh hA hδ hs₀ h64 hc hH hb hζ hsp hD1 hD2 hNb hY
  have hzs : ∀ Z : TorusSite n, _root_.YangMills.Construction.TorusFields.supDist Z Y ≤ Dh → Z ∉ s.storedBlockSet c := by
    intro Z hZ
    exact not_mem_storedBlockSet_of_zone hb.sizes hb.piece hb.two_le (thickening_mono (by omega) (mem_thickening_add hY hZ))
      hYN (by omega)
  have h2 := abs_blockCost_zero_sub_share_le hH hb hsp hW0 (Y := Y) (fun Z hZ => hzs Z (by omega))
    (movedDebt_nonneg (δ := δ) hA hb.gap_nonneg (R.params.side * (Dh - 2))) fun y hy => by
      have h3 := abs_share_zero_sub_minimizer_le hSh hs₀ h64 hc hb R.depth (y := y) hA hδ hW0 hemb fun h hh => by
        have h4 := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_box_le_sub_one hb (y := y) (by omega : 3 ≤ Dh) hh
        rw [hy] at h4
        exact hzs _ (by omega)
      refine h3.trans ?_
      unfold movedDebt shareDebt
      have h5 := card_bondsOfBox_cast_le (R := R) y (R.params.side * (Dh - 2))
      have h6 : 0 ≤ A * (2 * g) := mul_nonneg hA (by have := hb.gap_nonneg; linarith)
      have := mul_le_mul_of_nonneg_right h5 h6
      linarith
  have e : (blockCost R.params R.depth (nearPieceField s _ ζ) s.coarse s.bases Y -
        blockCost R.params R.depth (s.field 0) s.coarse s.bases Y) -
      (splicedCost s K D S₀ S ζ Y - levelShare R.params.coupling R.params.side (R.depth + 1) S Y s.coarse) =
      (blockCost R.params R.depth (nearPieceField s _ ζ) s.coarse s.bases Y - splicedCost s K D S₀ S ζ Y) -
      (blockCost R.params R.depth (s.field 0) s.coarse s.bases Y -
        levelShare R.params.coupling R.params.side (R.depth + 1) S Y s.coarse) := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  unfold nearDebt
  unfold shareDebt at h1 ⊢
  linarith
theorem abs_block_debt_le_mid (hNb : (blocksNear R.params.side R.range K).Nonempty) {Y : TorusSite n}
    (hYN : Y ∉ blocksNear R.params.side R.range K) (hY : Y ∉ thickening Dh (blocksNear R.params.side R.range K)) :
    |(blockCost R.params R.depth (nearPieceField s _ ζ) s.coarse s.bases Y -
        blockCost R.params R.depth (s.field 0) s.coarse s.bases Y) -
      (splicedCost s K D S₀ S ζ Y - levelShare R.params.coupling R.params.side (R.depth + 1) S Y s.coarse)| ≤
      nearDebt R A δ g (R.params.side * (Dh - 2)) := by
  classical
  have hρ : 0 ≤ R.ballRadius := by
    have := hb.sizes.admissible.σ_pos
    unfold StepSetup.ballRadius
    positivity
  have hW0 : torusHotLumps R.params (s.field 0) = torusHotLumps R.params s.fine :=
    hb.admissible.hotLumps_eq 0 (inBalls_zero hρ)
  have hemb := two_mul_radius_add_two_lt hb hD1 hD2 hNb hYN
  have hoff : ∀ Z : TorusSite n, _root_.YangMills.Construction.TorusFields.supDist Z Y ≤ Dh → Z ∉ blocksNear R.params.side R.range K := by
    intro Z hZ hin
    apply hY
    refine (mem_thickening _ _ _).mpr ⟨Z, hin, ?_⟩
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
    exact hZ
  have h1 := abs_blockCost_sub_blockCost_zero_le ζ hH hb hζ hW0 (Y := Y) (fun Z hZ => hoff Z (by omega))
    (shareDebt_nonneg (δ := δ) hA (R.params.side * (Dh - 2)))
    fun y hy => abs_share_near_sub_zero_le ζ hSh hs₀ h64 hc hb hζ R.depth hW0 hemb fun h hh => by
      have h4 := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_box_le_sub_one hb (y := y) (by omega : 3 ≤ Dh) (offsetInBox_succ hh)
      rw [hy] at h4
      exact hoff _ (by omega)
  have hg2 : 0 ≤ 2 * g := by have := hb.gap_nonneg; linarith
  have h2 := abs_splicedCost_sub_share_le ζ hH hb hsp hζ (Y := Y) hb.sizes.admissible.L_odd
    (fun Z hZ => hoff Z (by omega)) hg2
    (fun x i hx => by
      have n1 := hoff (parentBlock R.params.side x) (by omega)
      have n2 := hoff (parentBlock R.params.side (x + unitStep (n * R.params.side) i)) (by
        have h3 := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_add_unitStep_le hb x i
        have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side (x + unitStep (n * R.params.side) i))
          (parentBlock R.params.side x) Y
        omega)
      obtain ⟨v, hv, e⟩ := exists_splicedField_eq (S := S) ζ hb x i n1 n2
      exact norm_sub_le_of_eq_mul hv e)
    (movedDebt_nonneg (δ := δ) hA hb.gap_nonneg (R.params.side * (Dh - 2))) fun y hy => by
      have h3 := abs_share_spliced_sub_minimizer_le ζ hSh hs₀ h64 hc hH hb hζ R.depth (y := y) hA hδ hemb fun h hh => by
        have h4 := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_box_le_sub_one hb (y := y) (by omega : 3 ≤ Dh) hh
        rw [hy] at h4
        exact hoff _ (by omega)
      refine h3.trans ?_
      unfold movedDebt shareDebt
      have h5 := card_bondsOfBox_cast_le (R := R) y (R.params.side * (Dh - 2))
      have h6 : 0 ≤ A * (2 * g) := mul_nonneg hA hg2
      have := mul_le_mul_of_nonneg_right h5 h6
      linarith
  refine (abs_sub _ _).trans ?_
  unfold nearDebt
  linarith
theorem abs_block_debt_le_far (hNb : (blocksNear R.params.side R.range K).Nonempty) {Y : TorusSite n}
    (hY : Y ∉ thickening (4 * D) (blocksNear R.params.side R.range K)) :
    |(blockCost R.params R.depth (nearPieceField s _ ζ) s.coarse s.bases Y -
        blockCost R.params R.depth (s.field 0) s.coarse s.bases Y) -
      (splicedCost s K D S₀ S ζ Y - levelShare R.params.coupling R.params.side (R.depth + 1) S Y s.coarse)| ≤
      2 * (2 * (R.params.side : ℝ) + 1) ^ 4 * A * ∑ Y₀ ∈ blocksNear R.params.side R.range K,
        if 4 * D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y₀ then Real.exp (-(δ * R.params.side / 2 * _root_.YangMills.Construction.TorusFields.supDist Y Y₀)) else 0 := by
  classical
  have hρ : 0 ≤ R.ballRadius := by
    have := hb.sizes.admissible.σ_pos
    unfold StepSetup.ballRadius
    positivity
  have hW0 : torusHotLumps R.params (s.field 0) = torusHotLumps R.params s.fine :=
    hb.admissible.hotLumps_eq 0 (inBalls_zero hρ)
  have hD := hb.depth_ge
  obtain ⟨Y₀, hY₀, hmin⟩ := Finset.exists_min_image _ (fun Z => _root_.YangMills.Construction.TorusFields.supDist Y Z) hNb
  set d := _root_.YangMills.Construction.TorusFields.supDist Y Y₀ with hd
  have hd4 : 4 * D < d := by
    by_contra hcon
    exact hY ((mem_thickening _ _ _).mpr ⟨Y₀, hY₀, not_lt.mp (not_not.mpr (not_lt.mp hcon |> fun h => h) |>
      fun h => by omega)⟩)
  have hnear : ∀ Z ∈ blocksNear R.params.side R.range K, d ≤ _root_.YangMills.Construction.TorusFields.supDist Y Z := hmin
  set ρ := R.params.side * (d - D - 2) with hρdef
  have hL := hb.sizes.admissible.L_ge
  have hhalf := two_mul_supDist_le Y Y₀
  have hemb : 2 * ρ + 2 < n * R.params.side := by
    have h1 : 2 * (d - D - 2) + 2 ≤ n := by omega
    have h2 : 2 * ρ + 2 * R.params.side ≤ n * R.params.side := by
      calc 2 * ρ + 2 * R.params.side = (2 * (d - D - 2) + 2) * R.params.side := by rw [hρdef]; ring
        _ ≤ n * R.params.side := Nat.mul_le_mul_right _ h1
    omega
  have hblock : ∀ {y : TorusSite (n * R.params.side)}, parentBlock R.params.side y = Y → ∀ {h : Fin 4 → ℤ},
      OffsetInBox ρ h → _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side (y + siteOfInt h)) Y ≤ d - D - 1 := by
    intro y hy h hh
    have h1 := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_parentBlock_box_le (s := s) (c := c) hb (y := y) hh
    rw [hy] at h1
    have h3 : ρ / R.params.side = d - D - 2 := by
      rw [hρdef]
      exact Nat.mul_div_cancel_left _ (by omega)
    omega
  have hoffZ : ∀ Z : TorusSite n, _root_.YangMills.Construction.TorusFields.supDist Z Y < d → Z ∉ blocksNear R.params.side R.range K := by
    intro Z hZ hin
    have := hnear Z hin
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at this
    omega
  have hoffD : ∀ Z : TorusSite n, _root_.YangMills.Construction.TorusFields.supDist Z Y + D < d → Z ∉ thickening D (blocksNear R.params.side R.range K) := by
    intro Z hZ hin
    obtain ⟨Z', hZ', hdz⟩ := (mem_thickening _ _ _).mp hin
    have h1 := hnear Z' hZ'
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle Y Z Z'
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm Y Z] at h2
    omega
  have he : 0 ≤ A * Real.exp (-(δ * ρ)) := mul_nonneg hA (Real.exp_pos _).le
  have h1 := abs_blockCost_sub_blockCost_zero_le ζ hH hb hζ hW0 (Y := Y) (fun Z hZ => hoffZ Z (by omega)) he
    fun y hy => abs_share_near_sub_zero_le ζ hSh hs₀ h64 hc hb hζ R.depth hW0 hemb fun h hh => hoffZ _ (by
      have := hblock hy hh
      omega)
  have h2 := abs_splicedCost_sub_share_le ζ hH hb hsp hζ (Y := Y) hb.sizes.admissible.L_odd
    (fun Z hZ => hoffZ Z (by omega)) (le_refl (0 : ℝ))
    (fun x i hx => by
      rw [splicedField_of_not_mem ζ x i (hoffD _ (by omega))]
      simp) he
    fun y hy => abs_share_spliced_sub_minimizer_le_of_far ζ hSh hs₀ h64 hc hH hb hζ R.depth hemb fun h hh => hoffD _ (by
      have := hblock hy hh
      omega)
  have hexp : Real.exp (-(δ * ρ)) ≤ Real.exp (-(δ * R.params.side / 2 * d)) := by
    rw [Real.exp_le_exp]
    have h3 : (ρ : ℝ) = R.params.side * ((d : ℝ) - D - 2) := by
      rw [hρdef]
      push_cast [Nat.sub_sub, Nat.cast_sub (by omega : D + 2 ≤ d)]
      ring
    rw [h3]
    have hh : (d : ℝ) / 2 ≤ (d : ℝ) - D - 2 := by
      have : 2 * (D : ℝ) + 4 ≤ d := by exact_mod_cast (by omega : 2 * D + 4 ≤ d)
      linarith
    have hLδ : 0 ≤ δ * (R.params.side : ℝ) := by positivity
    nlinarith
  have hsum : Real.exp (-(δ * R.params.side / 2 * d)) ≤ ∑ Y₁ ∈ blocksNear R.params.side R.range K,
      if 4 * D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y₁ then Real.exp (-(δ * R.params.side / 2 * _root_.YangMills.Construction.TorusFields.supDist Y Y₁)) else 0 := by
    have hnn : ∀ Y₁ ∈ blocksNear R.params.side R.range K,
        0 ≤ (if 4 * D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y₁ then Real.exp (-(δ * R.params.side / 2 * _root_.YangMills.Construction.TorusFields.supDist Y Y₁)) else 0) := by
      intro Y₁ _
      split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
    have := Finset.single_le_sum hnn hY₀
    rw [if_pos (by omega : 4 * D ≤ supDist Y Y₀)] at this
    exact this
  have h3 : (2 * (R.params.side : ℝ) + 1) ^ 4 * (A * Real.exp (-(δ * ρ))) ≤ (2 * (R.params.side : ℝ) + 1) ^ 4 * A *
      ∑ Y₁ ∈ blocksNear R.params.side R.range K,
        if 4 * D ≤ _root_.YangMills.Construction.TorusFields.supDist Y Y₁ then Real.exp (-(δ * R.params.side / 2 * _root_.YangMills.Construction.TorusFields.supDist Y Y₁)) else 0 := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (hexp.trans hsum) (by positivity)
  refine (abs_sub _ _).trans ?_
  simp only [mul_zero, add_zero] at h2
  linarith
end Bounds
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
variable {n : ℕ} [NeZero n] {R : StepSetup} {s : ChartSetting R n} {c : SettingCore R n}
  {K : Finset (TorusSite (n * R.params.side))} {D : ℕ}
open GroupMoves TorusMinimizer ShareStability ContourStability
theorem period_stepBlockFrame_div {L : ℕ} (hLn : L ∣ n) (i : Fin 4) : (stepBlockFrame L (n / L)).period 0 i = n := by
  have h1 : (stepBlockFrame L (n / L)).period 0 i = (n / L) * L := by
    have := period_depth (F := stepBlockFrame L (n / L)) i
    exact this
  rw [h1]
  exact Nat.div_mul_cancel hLn
theorem exists_eq_torusLumpOf_of_hot {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) {V : TorusField n}
    {l : Finset (TorusSite n)} (hl : l ∈ torusHotLumps ℓ V) : ∃ z, l = torusLumpOf ℓ z := by
  obtain ⟨_, _, _, _, _, z, _, e⟩ := (mem_torusHotLumps_iff ℓ hfit hLn _ _).mp hl
  exact ⟨z, e⟩
theorem mem_topHotLumps_iff {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (X : Finset (TorusSite n))
    (V : TorusField n) (l : Finset (TorusSite n)) :
    l ∈ topHotLumps ℓ X V ↔ ∃ (x : TorusSite n) (μ ν : Fin 4), μ < ν ∧ (∀ z ∈ plaquetteVertices x μ ν, z ∈ X) ∧
      ℓ.threshold ≤ curvature V x μ ν ∧ ∃ z ∈ plaquetteVertices x μ ν, l = torusLumpOf ℓ z := by
  classical
  unfold topHotLumps
  rw [Finset.mem_image]
  constructor
  · rintro ⟨l₀, h0, rfl⟩
    obtain ⟨x, μ, ν, hlt, hX, hs, z, hz, e⟩ :=
      (mem_hotLumps_readAtLevel_iff hfit hLn (period_stepBlockFrame_div hLn) X V l₀).mp h0
    exact ⟨x, μ, ν, hlt, hX, hs, z, hz, e⟩
  · rintro ⟨x, μ, ν, hlt, hX, hs, z, hz, rfl⟩
    refine ⟨(torusLumpOf ℓ z).image (torusSiteInFrame (stepBlockFrame ℓ.side (n / ℓ.side)) 0), ?_, ?_⟩
    · have e : ((torusLumpOf ℓ z).image (torusSiteInFrame (stepBlockFrame ℓ.side (n / ℓ.side)) 0)).image (toTorusSite n) =
          torusLumpOf ℓ z := by
        rw [Finset.image_image]
        have : (toTorusSite n ∘ torusSiteInFrame (stepBlockFrame ℓ.side (n / ℓ.side)) 0 : TorusSite n → _) = id := by
          funext u
          exact toTorusSite_torusSiteInFrame (period_stepBlockFrame_div hLn) u
        rw [this, Finset.image_id]
      exact (mem_hotLumps_readAtLevel_iff hfit hLn (period_stepBlockFrame_div hLn) X V _).mpr
        ⟨x, μ, ν, hlt, hX, hs, z, hz, e⟩
    · rw [Finset.image_image]
      have : (toTorusSite n ∘ torusSiteInFrame (stepBlockFrame ℓ.side (n / ℓ.side)) 0 : TorusSite n → _) = id := by
        funext u
        exact toTorusSite_torusSiteInFrame (period_stepBlockFrame_div hLn) u
      rw [this, Finset.image_id]
theorem isTopLump_of_mem {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) {V : TorusField n}
    {l : Finset (TorusSite n)} (hl : l ∈ torusHotLumps ℓ V) : IsTopLump ℓ l := by
  classical
  obtain ⟨z, rfl⟩ := exists_eq_torusLumpOf_of_hot hfit hLn hl
  refine ⟨torusSiteInFrame (stepBlockFrame ℓ.side (n / ℓ.side)) 0 z, ?_⟩
  have e := image_lumpOf_toTorusSite hfit hLn (period_stepBlockFrame_div hLn)
    (torusSiteInFrame (stepBlockFrame ℓ.side (n / ℓ.side)) 0 z)
  rw [toTorusSite_torusSiteInFrame (period_stepBlockFrame_div hLn)] at e
  exact e.symm
theorem lumpOf_nonempty {L : ℕ} (hL : Odd L) (g : LumpGrid L) {F : BlockFrame} {j : ℕ} (x : F.Site j) :
    (LumpContours.lumpOf g x).Nonempty := by
  classical
  have hL0 : (0 : ℤ) < L := by exact_mod_cast hL.pos
  have hb : ∀ i, |offsetFromCentre L (siteCoords x i)| ≤ ((L : ℤ) - 1) / 2 := by
    intro i
    unfold offsetFromCentre
    have h1 := Int.emod_nonneg (siteCoords x i + ((L : ℤ) - 1) / 2) hL0.ne'
    have h2 := Int.emod_lt_of_pos (siteCoords x i + ((L : ℤ) - 1) / 2) hL0
    obtain ⟨k, hk⟩ := hL
    have hLz : (L : ℤ) = 2 * k + 1 := by exact_mod_cast hk
    have hh : ((L : ℤ) - 1) / 2 = k := by rw [hLz]; omega
    rw [hh] at h1 h2 ⊢
    rw [abs_le]
    constructor <;> omega
  unfold LumpContours.lumpOf boxSites
  refine ⟨siteOfCoords j fun i => siteCoords x i - offsetFromCentre L (siteCoords x i) +
      g.lower (offsetFromCentre L (siteCoords x i)),
    Finset.mem_image.mpr ⟨_, Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ⟨le_rfl, ?_⟩, rfl⟩⟩
  have := g.mem_interval _ (hb i)
  linarith [this.2.1, this.2.2.1]
theorem nonempty_of_mem_torusHotLumps {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} (hfit : ℓ.Admissible) {V : TorusField n}
    {l : Finset (TorusSite n)} (hl : l ∈ torusHotLumps ℓ V) : l.Nonempty := by
  classical
  unfold torusHotLumps at hl
  obtain ⟨l₀, h0, rfl⟩ := Finset.mem_image.mp hl
  unfold hotLumps at h0
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.mp h0
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hp
  exact (lumpOf_nonempty hfit.L_odd ℓ.grid z).image _
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
variable {n : ℕ} [NeZero n] {R : StepSetup} {s : ChartSetting R n} {c : SettingCore R n}
  {K : Finset (TorusSite (n * R.params.side))} {D : ℕ}
open GroupMoves TorusMinimizer ShareStability ContourStability
def otherLumps (s : ChartSetting R n) (c : SettingCore R n) (K : Finset (TorusSite (n * R.params.side))) :
    Finset (Finset (TorusSite n)) :=
  open Classical in torusHotLumps R.params s.coarse \ s.coarseLumpsInPiece c K
structure HotCoarseField (s : ChartSetting R n) (c : SettingCore R n) (K : Finset (TorusSite (n * R.params.side)))
    (D : ℕ) : Prop where
  sizes : Sizes R D
  two_le : 2 ≤ n
  piece : s.IsPiece c K
  side_dvd : R.params.side ∣ n
  core_eq : c.core = thickening (2 * clusterRange R.nextCoupling) (torusHotSites R.params s.coarse)
  small : 5 * R.range / R.params.side + D + 9 ≤ clusterRange R.nextCoupling / 2
  depth_ge : 2 ^ 13 ≤ D
theorem mem_core_of_mem_hotSites (ht : HotCoarseField s c K D) {y : TorusSite n}
    (hy : y ∈ torusHotSites R.params s.coarse) : y ∈ c.core := by
  rw [ht.core_eq]
  exact mem_thickening_self _ hy
theorem mem_coarseHull_of_mem_core {y : TorusSite n} (hy : y ∈ c.core) : y ∈ s.coarseHullOf c := by
  classical
  exact mem_thickening_self _ (Finset.mem_union_left _ hy)
theorem mem_attachedPart_of_core {z : TorusSite (n * R.params.side)} (hz : parentBlock R.params.side z ∈ c.core) :
    z ∈ s.attachedPart c := by
  classical
  have hzL : z ∈ sitesInBlocks R.params.side c.core := mem_sitesInBlocks.mpr hz
  have hp : z ∈ pieceSites s c := Finset.mem_union_right _ hzL
  obtain ⟨X, hX, hzX⟩ := exists_mem_chainComponents (r := 10 * R.range) hp
  exact Finset.mem_biUnion.mpr ⟨X, Finset.mem_filter.mpr ⟨hX, z, Finset.mem_inter.mpr ⟨hzX, hzL⟩⟩, hzX⟩
theorem lt_supDist_of_other (ht : HotCoarseField s c K D) {l : Finset (TorusSite n)} (hl : l ∈ otherLumps s c K)
    {y : TorusSite n} (hy : y ∈ l) {Z : TorusSite n} (hZ : Z ∈ thickening (D + 7) (blocksNear R.params.side R.range K)) :
    clusterRange R.nextCoupling / 2 < _root_.YangMills.Construction.TorusFields.supDist Z y := by
  classical
  obtain ⟨hl1, hl2⟩ := Finset.mem_sdiff.mp hl
  obtain ⟨Y, hY, hZY⟩ := (mem_thickening _ _ _).mp hZ
  obtain ⟨z₁, rfl, u, hu, hd⟩ := mem_blocksNear.mp hY
  have hyh : y ∈ torusHotSites R.params s.coarse := TorusLumps.mem_torusHotSites_iff.mpr ⟨l, hl1, hy⟩
  have hb1 : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side u) (parentBlock R.params.side z₁) ≤ 5 * R.range / R.params.side + 1 := by
    have h1 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one R.params.side u z₁
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm u z₁] at h1
    have := Nat.div_le_div_right (c := R.params.side) hd
    omega
  have hmain : clusterRange R.nextCoupling < _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side u) y := by
    by_contra hcon
    rw [not_lt] at hcon
    rcases ht.piece with ⟨P, hP, rfl⟩ | ⟨Q, hQ, rfl⟩
    · obtain ⟨X, hX, huX⟩ := Finset.mem_biUnion.mp hu
      have hfree := (Finset.mem_filter.mp (hP hX)).2
      have hBC : parentBlock R.params.side u ∈ c.core := by
        rw [ht.core_eq]
        exact (mem_thickening _ _ _).mpr ⟨y, hyh, by omega⟩
      exact hfree ⟨u, Finset.mem_inter.mpr ⟨huX, mem_sitesInBlocks.mpr hBC⟩⟩
    · obtain ⟨hu1, hu2⟩ := Finset.mem_inter.mp hu
      obtain ⟨X', hX', hbu⟩ := Finset.mem_biUnion.mp (mem_sitesInBlocks.mp hu2)
      have hXq : X' ∈ chainComponents (clusterRange R.nextCoupling) (s.coarseHullOf c) := hQ hX'
      have hyX : y ∈ X' := mem_of_chainConnected_of_mem_chainComponents hXq hbu
        (mem_coarseHull_of_mem_core (mem_core_of_mem_hotSites ht hyh))
        (chainConnected_of_supDist_le (subset_of_mem_chainComponents hXq hbu)
          (mem_coarseHull_of_mem_core (mem_core_of_mem_hotSites ht hyh)) hcon)
      have hlX : l ⊆ X' := by
        intro y' hy'
        have hC' := mem_core_of_mem_hotSites ht (TorusLumps.mem_torusHotSites_iff.mpr ⟨l, hl1, hy'⟩)
        have h3 := _root_.YangMills.Construction.TorusLumps.supDist_lt_of_mem_torusHotLumps ht.sizes.admissible ht.side_dvd hl1 hy hy'
        have h4 := ht.sizes.nextRange_large
        exact mem_of_chainConnected_of_mem_chainComponents hXq hyX (mem_coarseHull_of_mem_core hC')
          (chainConnected_of_supDist_le (subset_of_mem_chainComponents hXq hyX) (mem_coarseHull_of_mem_core hC')
            (by omega))
      refine hl2 (Finset.mem_filter.mpr ⟨hl1, fun y' hy' =>
        mem_core_of_mem_hotSites ht (TorusLumps.mem_torusHotSites_iff.mpr ⟨l, hl1, hy'⟩), fun z hz => ?_⟩)
      have hbz : parentBlock R.params.side z ∈ l := mem_sitesInBlocks.mp hz
      refine Finset.mem_inter.mpr
        ⟨mem_attachedPart_of_core (mem_core_of_mem_hotSites ht (TorusLumps.mem_torusHotSites_iff.mpr ⟨l, hl1, hbz⟩)), ?_⟩
      exact mem_sitesInBlocks.mpr (Finset.mem_biUnion.mpr ⟨X', hX', hlX hbz⟩)
  have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side u) (parentBlock R.params.side z₁) y
  have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side z₁) Z y
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm (parentBlock R.params.side z₁) Z] at h2
  have h3 := ht.small
  omega
abbrev otherCut (s : ChartSetting R n) (c : SettingCore R n) (K : Finset (TorusSite (n * R.params.side))) :
    Finset (TorusSite n) :=
  awayFromLumps (otherLumps s c K)
theorem mem_otherCut {Z : TorusSite n} :
    Z ∈ otherCut s c K ↔ ∀ l ∈ otherLumps s c K, ∀ y ∈ l, lumpRange < _root_.YangMills.Construction.TorusFields.supDist Z y := by
  classical
  unfold otherCut awayFromLumps
  rw [Finset.mem_sdiff]
  constructor
  · rintro ⟨-, h⟩ l hl y hy
    by_contra hcon
    exact h ((mem_thickening _ _ _).mpr ⟨y, Finset.mem_biUnion.mpr ⟨l, hl, hy⟩, not_lt.mp hcon⟩)
  · intro h
    refine ⟨Finset.mem_univ _, fun h2 => ?_⟩
    obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp h2
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hx
    exact absurd hd (not_le.mpr (h l hl x hxl))
theorem mem_otherCut_of_zone (ht : HotCoarseField s c K D) {Z : TorusSite n}
    (hZ : Z ∈ thickening (D + 7) (blocksNear R.params.side R.range K)) : Z ∈ otherCut s c K := by
  refine mem_otherCut.mpr fun l hl y hy => ?_
  have h1 := lt_supDist_of_other ht hl hy hZ
  have h2 := ht.sizes.nextRange_large
  have hr : lumpRange = 2 ^ 12 := rfl
  omega
theorem mem_blocksNear_of_piece_lump (ht : HotCoarseField s c K D) {l : Finset (TorusSite n)}
    (hl : l ∈ s.coarseLumpsInPiece c K) {z : TorusSite n} (hz : z ∈ l) : z ∈ blocksNear R.params.side R.range K := by
  classical
  obtain ⟨w, hw⟩ := exists_parentBlock_eq (L := R.params.side) ht.sizes.admissible.L_odd ht.two_le z
  have hwK : w ∈ K := (Finset.mem_filter.mp hl).2.2 (mem_sitesInBlocks.mpr (hw ▸ hz))
  exact mem_blocksNear.mpr ⟨w, hw, w, hwK, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩
theorem mem_piece_or_other (ht : HotCoarseField s c K D) {l : Finset (TorusSite n)}
    (hl : l ∈ torusHotLumps R.params s.coarse) : l ∈ s.coarseLumpsInPiece c K ∨ l ∈ otherLumps s c K := by
  classical
  by_cases h : l ∈ s.coarseLumpsInPiece c K
  · exact Or.inl h
  · exact Or.inr (Finset.mem_sdiff.mpr ⟨hl, h⟩)
theorem topHotLumps_otherCut (ht : HotCoarseField s c K D) :
    topHotLumps R.params (otherCut s c K) s.coarse = s.coarseLumpsInPiece c K := by
  classical
  have hfit := ht.sizes.admissible
  ext l
  rw [mem_topHotLumps_iff hfit ht.side_dvd]
  constructor
  · rintro ⟨x, μ, ν, hlt, hX, hs, z, hz, rfl⟩
    have hl : torusLumpOf R.params z ∈ torusHotLumps R.params s.coarse :=
      (mem_torusHotLumps_iff R.params hfit ht.side_dvd _ _).mpr ⟨x, μ, ν, hlt, hs, z, hz, rfl⟩
    rcases mem_piece_or_other ht hl with h | h
    · exact h
    · have := mem_otherCut.mp (hX z hz) _ h z (mem_torusLumpOf_self z)
      rw [_root_.YangMills.Construction.TorusFields.supDist_self] at this
      omega
  · intro hl
    have hl1 := (Finset.mem_filter.mp hl).1
    obtain ⟨x, μ, ν, hlt, hs, z, hz, e⟩ := (mem_torusHotLumps_iff R.params hfit ht.side_dvd _ _).mp hl1
    refine ⟨x, μ, ν, hlt, fun z' hz' => mem_otherCut_of_zone ht ?_, hs, z, hz, e⟩
    have hzN := mem_blocksNear_of_piece_lump ht hl (e ▸ mem_torusLumpOf_self z)
    refine (mem_thickening _ _ _).mpr ⟨z, hzN, ?_⟩
    have := _root_.YangMills.Construction.TorusLumps.supDist_le_four_of_mem_plaquetteVertices (x, μ, ν) hz' hz
    have hD := ht.depth_ge
    omega
theorem otherCut_sdiff_eq_restSet (ht : HotCoarseField s c K D) :
    otherCut s c K \ thickening lumpRange ((topHotLumps R.params (otherCut s c K) s.coarse).biUnion id) = s.restSet c := by
  classical
  rw [topHotLumps_otherCut ht]
  ext Z
  unfold ChartSetting.restSet
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩ h3
    obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp h3
    obtain ⟨l, hl, hxl⟩ := TorusLumps.mem_torusHotSites_iff.mp (Finset.mem_inter.mp hx).2
    rcases mem_piece_or_other ht hl with h | h
    · exact h2 ((mem_thickening _ _ _).mpr ⟨x, Finset.mem_biUnion.mpr ⟨l, h, hxl⟩, hd⟩)
    · exact absurd hd (not_le.mpr (mem_otherCut.mp h1 l h x hxl))
  · intro h
    refine ⟨mem_otherCut.mpr fun l hl y hy => ?_, fun h2 => h ?_⟩
    · by_contra hcon
      have hyh : y ∈ torusHotSites R.params s.coarse :=
        TorusLumps.mem_torusHotSites_iff.mpr ⟨l, (Finset.mem_sdiff.mp hl).1, hy⟩
      exact h ((mem_thickening _ _ _).mpr ⟨y, Finset.mem_inter.mpr ⟨mem_core_of_mem_hotSites ht hyh, hyh⟩,
        not_lt.mp hcon⟩)
    · obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp h2
      obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hx
      have hyh : x ∈ torusHotSites R.params s.coarse :=
        TorusLumps.mem_torusHotSites_iff.mpr ⟨l, (Finset.mem_filter.mp hl).1, hxl⟩
      exact (mem_thickening _ _ _).mpr ⟨x, Finset.mem_inter.mpr ⟨mem_core_of_mem_hotSites ht hyh, hyh⟩, hd⟩
theorem mem_restSet_of_otherCut (ht : HotCoarseField s c K D) {Z : TorusSite n} (hZ : Z ∈ otherCut s c K)
    (hN : Z ∉ blocksNear R.params.side R.range K) : Z ∈ s.restSet c := by
  classical
  unfold ChartSetting.restSet
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => ?_⟩
  obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp h
  obtain ⟨hxC, hxh⟩ := Finset.mem_inter.mp hx
  obtain ⟨l, hl, hxl⟩ := TorusLumps.mem_torusHotSites_iff.mp hxh
  rcases mem_piece_or_other ht hl with h1 | h1
  · have hfit := ht.sizes.admissible
    obtain ⟨w, hw⟩ := exists_parentBlock_eq (L := R.params.side) hfit.L_odd ht.two_le Z
    obtain ⟨v, hv⟩ := exists_parentBlock_eq (L := R.params.side) hfit.L_odd ht.two_le x
    have hvK : v ∈ K := (Finset.mem_filter.mp h1).2.2 (mem_sitesInBlocks.mpr (hv ▸ hxl))
    have hZC : Z ∈ c.core := by
      rw [ht.core_eq]
      have hr : lumpRange = 2 ^ 12 := rfl
      have := ht.sizes.nextRange_large
      exact (mem_thickening _ _ _).mpr ⟨x, hxh, by omega⟩
    have hwp : w ∈ pieceSites s c := Finset.mem_union_right _ (mem_sitesInBlocks.mpr (hw ▸ hZC))
    have hd2 : _root_.YangMills.Construction.TorusFields.supDist v w ≤ 10 * R.range := by
      have h3 := _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.supDist_le_side_mul_parentBlock_add hfit.L_odd v w
      rw [hv, hw, _root_.YangMills.Construction.TorusFields.supDist_comm x Z] at h3
      have h4 : R.params.side * _root_.YangMills.Construction.TorusFields.supDist Z x ≤ R.params.side * (D + 7) := Nat.mul_le_mul_left _ (by
        have hr : lumpRange = 2 ^ 12 := rfl
        have := ht.depth_ge
        omega)
      have h5 := ht.sizes.zone_le
      have h6 : R.params.side * (D + 8) = R.params.side * (D + 7) + R.params.side := by ring
      omega
    have hwK := mem_piece_of_supDist_le ht.piece ht.sizes.range_le hvK hwp hd2
    exact hN (mem_blocksNear.mpr ⟨w, hw, w, hwK, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
  · exact absurd hd (not_le.mpr (mem_otherCut.mp hZ l h1 x hxl))
theorem wall_le_supDist (ht : HotCoarseField s c K D) {y z : TorusSite n}
    (hy : y ∈ thickening lumpRange ((topHotLumps R.params (otherCut s c K) s.coarse).biUnion id))
    (hz : z ∈ thickening lumpRange ((otherLumps s c K).biUnion id)) : 2 * HoleBounds.wallMargin ≤ _root_.YangMills.Construction.TorusFields.supDist y z := by
  classical
  rw [topHotLumps_otherCut ht] at hy
  obtain ⟨y', hy', hd⟩ := (mem_thickening _ _ _).mp hy
  obtain ⟨z', hz', hd'⟩ := (mem_thickening _ _ _).mp hz
  obtain ⟨l, hl, hyl⟩ := Finset.mem_biUnion.mp hy'
  obtain ⟨l', hl', hzl⟩ := Finset.mem_biUnion.mp hz'
  have hN := mem_blocksNear_of_piece_lump ht hl hyl
  have h1 := lt_supDist_of_other ht hl' hzl (mem_thickening_self (D + 7) hN)
  have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle y' y z'
  have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle y z z'
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm y' y] at h2
  have hr : lumpRange = 2 ^ 12 := rfl
  have hw : HoleBounds.wallMargin = 5 := rfl
  have := ht.sizes.nextRange_large
  omega
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
variable {n : ℕ} [NeZero n] {R : StepSetup} {s : ChartSetting R n} {c : SettingCore R n}
  {K : Finset (TorusSite (n * R.params.side))} {D : ℕ}
open GroupMoves TorusMinimizer ShareStability ContourStability
structure ChainData (R : StepSetup) (δ lam σA cg : ℝ) (N : ℕ → ℝ) : Prop where
  admissible : R.params.Admissible
  constants : ColdChain.ColdChainConstants R.params.coupling δ R.params.side lam R.anchorRadius σA cg N
  threshold_le : 2 * R.params.threshold ≤ σA
variable {δ lam σA cg : ℝ} {N : ℕ → ℝ}
section Least
variable {S C : Finset (TorusSite n)} {sT : ℝ}
theorem exists_minimizing_chart (hch : ChainData R δ lam σA cg N) (hc : ComplementOfThickenedLumpsRegular)
    (hsit : IsStepSituation R.params (clusterRange R.nextCoupling) s.coarse S C sT) :
    ∃ w, IsMinimizingChart R.params.coupling (cellsOfSites (torusFrame R.params.side R.depth n) S)
        (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top s.coarse)
        (min R.anchorRadius (N 0 * sT)) w ∧
      IsCold (cellsOfSites (torusFrame R.params.side R.depth n) S) (torusFrame R.params.side R.depth n).depth (sT / 8)
        (chartedField w (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top s.coarse)) ∧
      minimizingCoordinates R.params.coupling (cellsOfSites (torusFrame R.params.side R.depth n) S)
        (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top s.coarse)
        R.anchorRadius = w := by
  obtain ⟨hs0, hs2, h4096, hall⟩ := stepSituation_regular_and_cold hc hch.admissible hsit
  set F := torusFrame R.params.side R.depth n with hF
  obtain ⟨hreg, hcold⟩ := hall F (fun _ => rfl)
  obtain ⟨_, _, _, hρ0, hρ1, _, _, _, hmain⟩ := hch.constants
  have hamb : IsAdmissibleAmbient F := isAdmissibleAmbient_torusFrame (by omega)
  have hone := (hmain F 2047 _ rfl hamb (by norm_num) hreg sT _ hs0 (hs2.trans hch.threshold_le) hcold).1
  have hL : Odd F.blockSide := hch.admissible.L_odd
  have hs : ∀ i, 2 ≤ F.extent i := fun _ => by
    change 2 ≤ n
    omega
  have hπ : R.anchorRadius < Real.pi := by linarith [Real.pi_gt_three]
  exact minimizingCoordinates_eq hL hs hπ le_rfl hone
theorem isColdOn_minimizingField (hch : ChainData R δ lam σA cg N) (hc : ComplementOfThickenedLumpsRegular)
    (hsit : IsStepSituation R.params (clusterRange R.nextCoupling) s.coarse S C sT) :
    IsColdOn (sitesInBlocks R.params.side S) (sT / 8)
      (minimizingField R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse) := by
  classical
  obtain ⟨w, -, hcold, hw⟩ := exists_minimizing_chart hch hc hsit
  obtain ⟨hs0, hs2, h4096, -⟩ := stepSituation_regular_and_cold hc hch.admissible hsit
  set F := torusFrame R.params.side R.depth n with hF
  have hL : Odd F.blockSide := hch.admissible.L_odd
  have h2 : 2 ≤ n := by omega
  have hread := readAtLevel_minimizingField (n := n) (L := R.params.side) R.params.coupling R.anchorRadius R.depth S s.coarse
  rw [hw] at hread
  rw [← hread] at hcold
  intro x μ ν hlt hcn
  have hp : ∀ i, F.period F.depth i = n * R.params.side := period_torusFrame_depth R.depth
  haveI hLF : NeZero F.blockSide := ⟨NeZero.ne R.params.side⟩
  have hsite : ∀ u : TorusSite (n * R.params.side), u ∈ sitesInBlocks R.params.side S →
      torusSiteInFrame F F.depth u ∈ sitesOfCells (cellsOfSites F S) F.depth :=
    fun u hu => torusSiteInFrame_mem_sitesOfCells (F := F) (n := n) (fun _ => rfl) hL h2 u (mem_sitesInBlocks.mp hu)
  have hxs : torusSiteInFrame F F.depth x ∈ sitesOfCells (cellsOfSites F S) F.depth :=
    hsite x (hcn x (by simp [plaquetteVertices]))
  have hmem : (torusSiteInFrame F F.depth x, μ, ν) ∈ innerPlaquettes (cellsOfSites F S) F.depth := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxs, by simp⟩, hlt, fun q hq => ?_⟩
    have h3 := (mem_plaquetteCorners_iff_toTorusSite hp _ μ ν q).mp hq
    rw [toTorusSite_torusSiteInFrame hp] at h3
    have h4 := hsite _ (hcn _ h3)
    rwa [torusSiteInFrame_toTorusSite hp] at h4
  have h5 := hcold _ hmem
  rw [plaquetteDefect_readAtLevel_eq hp, toTorusSite_torusSiteInFrame hp] at h5
  exact h5
theorem norm_minimizerCoord_lt_pi (hch : ChainData R δ lam σA cg N) (hc : ComplementOfThickenedLumpsRegular)
    (hsit : IsStepSituation R.params (clusterRange R.nextCoupling) s.coarse S C sT) (b : TorusBond (n * R.params.side)) :
    ‖(minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse b : ℍ[ℝ])‖ < Real.pi := by
  classical
  obtain ⟨w, hl, -, hw⟩ := exists_minimizing_chart hch hc hsit
  obtain ⟨_, _, _, hρ0, hρ1, _, _, _, -⟩ := hch.constants
  have hpi := Real.pi_gt_three
  have e : minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse b =
      w (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).depth b.1) b.2 := by
    unfold minimizerCoord minimizingBondCoordinate
    rw [hw]
  rw [e]
  by_cases hb : (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).depth b.1, b.2) ∈
      chordBonds (cellsOfSites (torusFrame R.params.side R.depth n) S)
  · have h1 := hl.2.1 _ hb
    have h2 : ‖w (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).depth b.1) b.2‖
        ≤ 1 :=
      h1.trans ((min_le_left _ _).trans hρ1)
    have h3 : ‖(w (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).depth b.1)
        b.2 : ℍ[ℝ])‖ ≤ 1 := h2
    linarith
  · have h1 := hl.1 _ hb
    have h2 : w (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).depth b.1) b.2
        = 0 := h1
    rw [h2]
    simpa using Real.pi_pos
theorem isMinimizingField_readAtLevel (hch : ChainData R δ lam σA cg N) (hc : ComplementOfThickenedLumpsRegular)
    (hC : WholeCellCostEqualsMinimalAction)
    (hsit : IsStepSituation R.params (clusterRange R.nextCoupling) s.coarse S C sT) :
    IsMinimizingField R.params.coupling (cellsOfSites (torusFrame R.params.side R.depth n) S)
      (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top s.coarse)
      (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).depth
        (minimizingField R.params.coupling R.anchorRadius R.params.side R.depth S s.coarse)) := by
  obtain ⟨w, hl, -, hw⟩ := exists_minimizing_chart hch hc hsit
  have ha : 0 ≤ R.params.coupling := by have := hch.admissible.a_ge; linarith
  intro W'
  have hE := (hC (torusFrame R.params.side R.depth n) R.params.coupling
    (cellsOfSites (torusFrame R.params.side R.depth n) S) hch.admissible.L_odd ha).2.2
  rw [hE, hE, readAtLevel_minimizingField, hw]
  exact hl.2.2 W'
theorem regular_of_stepSituation (hch : ChainData R δ lam σA cg N) (hc : ComplementOfThickenedLumpsRegular)
    (hsit : IsStepSituation R.params (clusterRange R.nextCoupling) s.coarse S C sT) : IsLocallyOrthantClosed S 2047 := by
  obtain ⟨-, -, -, hall⟩ := stepSituation_regular_and_cold hc hch.admissible hsit
  exact isLocallyOrthantClosed_of_cells (L := R.params.side) (t := R.depth) le_rfl
    (hall (torusFrame R.params.side R.depth n) (fun _ => rfl)).1
theorem isColdOn_of_stepSituation (hch : ChainData R δ lam σA cg N) (hc : ComplementOfThickenedLumpsRegular)
    (hsit : IsStepSituation R.params (clusterRange R.nextCoupling) s.coarse S C sT) : IsColdOn S sT s.coarse := by
  classical
  obtain ⟨-, -, -, hall⟩ := stepSituation_regular_and_cold hc hch.admissible hsit
  set F := torusFrame R.params.side R.depth n with hF
  have hcold := (hall F (fun _ => rfl)).2
  have hp : ∀ i, F.period F.top i = n := period_torusFrame_top R.depth
  have hn : ∀ i, F.extent i = n := fun _ => rfl
  intro x μ ν hlt hcn
  have hmem : (torusSiteInFrame F F.top x, μ, ν) ∈ innerPlaquettes (cellsOfSites F S) F.top := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, by simp⟩, hlt, fun q hq => ?_⟩
    · rw [BlockAverages.mem_sitesOfCells_top]
      exact (torusSiteInFrame_mem_cellsOfSites_iff hn).mpr (hcn x (by simp [plaquetteVertices]))
    · have h3 := (mem_plaquetteCorners_iff_toTorusSite hp _ μ ν q).mp hq
      rw [toTorusSite_torusSiteInFrame hp] at h3
      rw [BlockAverages.mem_sitesOfCells_top, mem_cellsOfSites_iff hn]
      exact hcn _ h3
  have h5 := hcold _ hmem
  rw [plaquetteDefect_readAtLevel_eq hp, toTorusSite_torusSiteInFrame hp] at h5
  exact h5
theorem shareSplitsOn_of_stepSituation (hch : ChainData R δ lam σA cg N) (hc : ComplementOfThickenedLumpsRegular)
    (hS : LevelShareSplits) (hsit : IsStepSituation R.params (clusterRange R.nextCoupling) s.coarse S C sT) :
    ShareSplitsOn s S := by
  obtain ⟨hs0, hs2, h4096, -⟩ := stepSituation_regular_and_cold hc hch.admissible hsit
  have ha : 0 < R.params.coupling := by have := hch.admissible.a_ge; linarith
  intro Y hY
  have hreg := regular_of_stepSituation hch hc hsit
  have hreg' : IsLocallyOrthantClosed S 1024 := by
    intro z
    obtain ⟨eps, he, hX⟩ := hreg z
    exact ⟨eps, he, fun q hq hd v hv hbd => hX q hq (by omega) v hv fun i => (hbd i).trans (by norm_num)⟩
  exact hS R.params.coupling δ R.params.side lam R.anchorRadius σA cg N ha hch.admissible.L_odd hch.constants R.depth n S
    s.coarse sT Y (by omega) hs0 (hs2.trans hch.threshold_le) hreg' (isColdOn_of_stepSituation hch hc hsit) hY
theorem framesNear_of_stepSituation (hch : ChainData R δ lam σA cg N) (hF : StepFrames.FrameNearMinimizer)
    (hrf : RangesAdmissible R.range (clusterRange R.nextCoupling))
    (hsit : IsStepSituation R.params (clusterRange R.nextCoupling) s.coarse S C sT) :
    FramesNearMinimizer s C S (N 0 * sT * Real.exp (-(δ * ((R.range / 2 ^ 11 : ℕ) : ℝ)))) := by
  intro b hb hbC
  exact ((hF R.params δ lam R.anchorRadius σA cg N hch.admissible hch.constants hch.threshold_le).2 R.depth R.range
    (clusterRange R.nextCoupling) n s.coarse S C sT hrf hsit b hb hbC).2
end Least
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
variable {n : ℕ} [NeZero n] {R : StepSetup} {s : ChartSetting R n} {c : SettingCore R n}
  {K : Finset (TorusSite (n * R.params.side))} {D : ℕ}
variable {δ lam σA cg : ℝ} {N : ℕ → ℝ}
open GroupMoves TorusMinimizer ShareStability ContourStability
structure StepSizes (R : StepSetup) (D : ℕ) (g : ℝ) : Prop where
  sizes : Sizes R D
  depth_ge : 2 ^ 13 ≤ D
  small : 5 * R.range / R.params.side + D + 9 ≤ clusterRange R.nextCoupling / 2
  ranges : RangesAdmissible R.range (clusterRange R.nextCoupling)
  gap_nonneg : 0 ≤ g
  gap_small : R.params.threshold / 4 + 8 * g < R.params.threshold
  gap_le : g ≤ R.ballRadius / 8
structure CutPlace (s : ChartSetting R n) (c : SettingCore R n) (K : Finset (TorusSite (n * R.params.side))) (D : ℕ)
    (g cE : ℝ) (S₀ : Finset (TorusSite n)) (m : ℕ) : Prop where
  near : NearPieceData s c K D S₀ (s.restSet c) g (R.params.threshold / 4)
  count_eq : m = (s.coarseLumpsInPiece c K).card
  splits : ShareSplitsOn s (s.restSet c)
  saves : ∀ (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n),
    (∀ e ∈ bondsWithin (sitesInBlocks R.params.side (s.restSet c)), ∀ z, z ∉ S₀ →
      _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side e.1) z ≤ HoleBounds.wallMargin →
      W e.1 e.2 = minimizerOn s (s.restSet c) e.1 e.2) →
    IsBaseChoice R.params.baseDepth (HoleOnTori.stepHotLumps R.params (sitesInBlocks R.params.side S₀) W) b →
    HoleSavingOnTorus R.params cE R.depth S₀ (s.restSet c) m s.coarse W (minimizerOn s (s.restSet c)) b
theorem framesNearMinimizer_mono {C S : Finset (TorusSite n)} {g g' : ℝ} (h : g ≤ g')
    (hf : FramesNearMinimizer s C S g) : FramesNearMinimizer s C S g' :=
  fun b hb hC => (hf b hb hC).trans h
theorem exists_cutPlace (hch : ChainData R δ lam σA cg N) (hc : ComplementOfThickenedLumpsRegular)
    (hC : WholeCellCostEqualsMinimalAction) (hS : LevelShareSplits) (hF : StepFrames.FrameNearMinimizer) {cE : ℝ}
    (hsv : HoleSavingBounds R.params cE) {g : ℝ} (hnum : StepSizes R D g)
    (hg : N 0 * (2 * R.params.threshold) * Real.exp (-(δ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤ g)
    (hn₀ : R.params.n₀ ≤ n) (hD : 16 ≤ D) (hs : s.IsAdmissible) (hst : s.IsCoreOf c) (hm : s.IsMarked c)
    (hK : s.IsPiece c K) :
    ∃ (S₀ : Finset (TorusSite n)) (m : ℕ), CutPlace s c K D g cE S₀ m := by
  classical
  have hfit := hch.admissible
  have hσ := hfit.σ_pos
  have hN0 : 0 < N 0 := hch.constants.2.2.2.2.2.2.2.1 0
  have h4096 : 4096 ≤ n := hfit.n₀_ge.trans hn₀
  have h2 : 2 ≤ n := by omega
  have hr' := hnum.sizes.nextRange_large
  rcases hst.hot_or_cold with ⟨hB, hCh⟩ | ⟨hCe, hcold⟩
  · have ht : HotCoarseField s c K D := ⟨hnum.sizes, h2, hK, hB.1, hCh, hnum.small, hnum.depth_ge⟩
    have hrest : s.restSet c = Finset.univ \ thickening lumpRange (torusHotSites R.params s.coarse) := by
      unfold ChartSetting.restSet
      congr 2
      exact Finset.inter_eq_right.mpr fun y hy => mem_core_of_mem_hotSites ht hy
    have hsit : IsStepSituation R.params (clusterRange R.nextCoupling) s.coarse (s.restSet c) c.core R.params.threshold :=
      Or.inl ⟨hB, hrest, hCh, rfl⟩
    have hnext : ∀ Z, Z ∉ c.core → ∀ Z', _root_.YangMills.Construction.TorusFields.supDist Z' Z ≤ 1 → Z' ∈ s.restSet c := by
      intro Z hZ Z' hd
      rw [hrest]
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => hZ ?_⟩
      obtain ⟨x, hx, hdx⟩ := (mem_thickening _ _ _).mp h
      rw [hCh]
      have hr : lumpRange = 2 ^ 12 := rfl
      refine (mem_thickening _ _ _).mpr ⟨x, hx, ?_⟩
      have := _root_.YangMills.Construction.TorusFields.supDist_triangle Z Z' x
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm Z Z'] at this
      omega
    refine ⟨otherCut s c K, (s.coarseLumpsInPiece c K).card, ?_, rfl, shareSplitsOn_of_stepSituation hch hc hS hsit, ?_⟩
    · refine ⟨hnum.sizes, h2, hD, hs, hst, hm, hK, hnum.gap_nonneg,
        framesNearMinimizer_mono ?_ (framesNear_of_stepSituation hch hF hnum.ranges hsit), ?_, hnum.gap_small,
        fun Z hZ => mem_otherCut_of_zone ht (thickening_mono (by omega) hZ),
        fun Z h1 h3 => mem_restSet_of_otherCut ht h1 h3, ?_,
        fun Z hZ => hnext Z hZ Z (by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega), hnext, hnum.gap_le,
        norm_minimizerCoord_lt_pi hch hc hsit, ?_, ?_⟩
      · refine le_trans ?_ hg
        have h3 : N 0 * R.params.threshold ≤ N 0 * (2 * R.params.threshold) :=
          mul_le_mul_of_nonneg_left (by linarith) hN0.le
        exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      · intro x μ ν hlt hcn
        have := isColdOn_minimizingField hch hc hsit x μ ν hlt hcn
        have e : R.params.threshold / 8 ≤ R.params.threshold / 4 := by linarith
        linarith
      · intro Z hZ
        rw [← otherCut_sdiff_eq_restSet ht] at hZ
        exact (Finset.mem_sdiff.mp hZ).1
      · exact isLocallyOrthantClosed_compl_lumps hc hfit ht.side_dvd _ fun l hl =>
          exists_eq_torusLumpOf_of_hot hfit ht.side_dvd (Finset.mem_sdiff.mp hl).1
      · exact regular_of_stepSituation hch hc hsit
    · intro W b hwall hbases
      have hleast := isMinimizingField_readAtLevel (s := s) hch hc hC hsit
      have hres := hsv.holed R.depth n ht.side_dvd h4096 (otherLumps s c K)
        (fun l hl => isTopLump_of_mem hfit ht.side_dvd (Finset.mem_sdiff.mp hl).1) s.coarse W (minimizerOn s (s.restSet c)) b
        (fun y hy z hz => wall_le_supDist ht hy hz) (by rw [otherCut_sdiff_eq_restSet ht]; exact hleast)
        (fun e he z hz hd => by
          rw [otherCut_sdiff_eq_restSet ht] at he
          refine hwall e he z (fun h => ?_) hd
          obtain ⟨x, hx, hdx⟩ := (mem_thickening _ _ _).mp hz
          obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hx
          exact absurd hdx (not_le.mpr (mem_otherCut.mp h l hl x hxl))) hbases
      rw [otherCut_sdiff_eq_restSet ht, topHotLumps_otherCut ht] at hres
      exact hres
  · have hrest : s.restSet c = Finset.univ := by
      unfold ChartSetting.restSet
      rw [hCe]
      simp [thickening]
    have hsit : IsStepSituation R.params (clusterRange R.nextCoupling) s.coarse (s.restSet c) c.core
        (9 / 8 * R.params.threshold) :=
      Or.inr ⟨hn₀, hcold, hrest, hCe, rfl⟩
    refine ⟨Finset.univ, 0, ?_, ?_, shareSplitsOn_of_stepSituation hch hc hS hsit, ?_⟩
    · refine ⟨hnum.sizes, h2, hD, hs, hst, hm, hK, hnum.gap_nonneg,
        framesNearMinimizer_mono ?_ (framesNear_of_stepSituation hch hF hnum.ranges hsit), ?_, hnum.gap_small,
        fun _ _ => Finset.mem_univ _, fun Z _ _ => by rw [hrest]; exact Finset.mem_univ _, fun _ _ => Finset.mem_univ _,
        fun _ _ => by rw [hrest]; exact Finset.mem_univ _, fun _ _ _ _ => by rw [hrest]; exact Finset.mem_univ _,
        hnum.gap_le, norm_minimizerCoord_lt_pi hch hc hsit, ?_, ?_⟩
      · refine le_trans ?_ hg
        have h3 : N 0 * (9 / 8 * R.params.threshold) ≤ N 0 * (2 * R.params.threshold) :=
          mul_le_mul_of_nonneg_left (by linarith) hN0.le
        exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      · intro x μ ν hlt hcn
        have := isColdOn_minimizingField hch hc hsit x μ ν hlt hcn
        have e : 9 / 8 * R.params.threshold / 8 ≤ R.params.threshold / 4 := by linarith
        linarith
      · exact fun _ => ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ _ _ _ _ _ => Finset.mem_univ _⟩
      · exact regular_of_stepSituation hch hc hsit
    · symm
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro l hl
      obtain ⟨h1, h3, -⟩ := Finset.mem_filter.mp hl
      obtain ⟨z, hz⟩ := nonempty_of_mem_torusHotLumps hfit h1
      have := h3 hz
      rw [hCe] at this
      simp at this
    · intro W b hwall hbases
      have hleast := isMinimizingField_readAtLevel (s := s) hch hc hC hsit
      rw [hrest] at hleast ⊢
      have hres := hsv.cold R.depth n h4096 s.coarse W (minimizerOn s Finset.univ) b hcold hleast hbases
      exact hres
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
variable {n : ℕ} [NeZero n] {R : StepSetup} {s : ChartSetting R n} {c : SettingCore R n}
  {K : Finset (TorusSite (n * R.params.side))} {D : ℕ} {S₀ : Finset (TorusSite n)} {m : ℕ} {g cE : ℝ}
open GroupMoves TorusMinimizer ShareStability ContourStability
def totalDebt (R : StepSetup) (A δ g A' : ℝ) (D Dh : ℕ) : ℝ :=
  ((2 * (4 * D : ℕ) + 1 : ℕ) : ℝ) ^ 4 * nearDebt R A δ g (R.params.side * (Dh - 2)) +
    (2 * (2 * (R.params.side : ℝ) + 1) ^ 4 * A) * (A' * Real.exp (-(δ * R.params.side / 2 * (4 * D : ℕ) / 2)))
theorem inBalls_extendByZero (hρ : 0 ≤ R.ballRadius) {η : FreeCoords s.free} (hη : s.InBalls η)
    (Nb : Finset (TorusSite n)) : s.InBalls (s.extendByZero Nb fun b => η b.1) := by
  classical
  intro b
  unfold ChartSetting.extendByZero
  split_ifs with h
  · exact hη b
  · change ‖((toImaginary (0 : EuclideanSpace ℝ (Fin 3)) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ R.ballRadius
    rw [toImaginary_zero]
    simpa using hρ
theorem extendByZero_of_eq_empty {Nb : Finset (TorusSite n)} (hN : Nb = ∅)
    (ζ : s.freeNear Nb → EuclideanSpace ℝ (Fin 3)) : s.extendByZero Nb ζ = 0 := by
  classical
  funext b
  unfold ChartSetting.extendByZero
  rw [dif_neg]
  · rfl
  · intro h
    have := (Finset.mem_filter.mp h).2
    rw [hN] at this
    simp at this
theorem energy_bound_of_cutPlace (hcE : 0 ≤ cE) {A δ s₀ A' Xq : ℝ}
    (hSh : ShareLocality R.params.coupling R.params.side s₀ A δ) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hs₀ : R.params.threshold ≤ s₀) (hc : ComplementOfThickenedLumpsRegular) (hH : TorusFrames.hotLumpsOfStepStatement)
    (hSA : SharesSumToAction) (hp : CutPlace s c K D g cE S₀ m) (h64 : 64 ≤ n * R.params.side)
    {η : FreeCoords s.free} (hη : s.InBalls η)
    (hbad : ∀ b ∈ c.badBonds, b.1 ∈ K →
      5 * R.ballRadius / 8 ≤ ‖(frameDeviation R.params R.anchorRadius R.depth R.frameReach s.coarse s.fine b : ℍ[ℝ])‖)
    {Dh : ℕ} (hD1 : 2 * Dh + 14 ≤ D) (hD2 : 16 ≤ Dh) (hm4 : 2 ≤ 4 * R.frameReach)
    (hA' : ∀ (y : TorusSite n) (Dd : ℕ), ∑ Y ∈ Finset.univ.filter (fun Y : TorusSite n => Dd ≤ _root_.YangMills.Construction.TorusFields.supDist Y y),
      Real.exp (-(δ * R.params.side / 2 * _root_.YangMills.Construction.TorusFields.supDist Y y)) ≤ A' * Real.exp (-(δ * R.params.side / 2 * Dd / 2)))
    (hx : 0 < R.coupling) (hq : R.coupling * totalDebt R A δ g A' D Dh ≤ Xq) :
    R.coupling * (∑ Y ∈ blocksNear R.params.side R.range K,
          levelShare R.params.coupling R.params.side (R.depth + 1) (s.restSet c) Y s.coarse +
        6 * R.params.κ * R.params.threshold ^ 2 * ((s.coarseLumpsInPiece c K).card : ℝ) +
        R.params.κ / 4 * R.params.threshold ^ 2 * ((s.lumpsInPiece K).card : ℝ) +
        cE * ((badBlocksOff R.params.side c.badBonds c.core K).card : ℝ)) -
      Xq * ((blocksNear R.params.side R.range K).card : ℝ) ≤
    R.coupling * (s.energyNear (blocksNear R.params.side R.range K) η +
      R.params.κ * R.params.threshold ^ 2 * ((s.lumpsInPiece K).card : ℝ)) := by
  classical
  have hb := hp.near
  have hfit := hb.sizes.admissible
  have hρ : 0 ≤ R.ballRadius := by
    have := hfit.σ_pos
    unfold StepSetup.ballRadius
    positivity
  have hg := hb.gap_nonneg
  have ha : 0 ≤ R.params.coupling := by have := hfit.a_ge; linarith
  have hζ := inBalls_extendByZero hρ hη (blocksNear R.params.side R.range K)
  by_cases hNb : (blocksNear R.params.side R.range K).Nonempty
  · set ζ : s.freeNear (blocksNear R.params.side R.range K) → EuclideanSpace ℝ (Fin 3) := fun b => η b.1 with hζdef
    have hwall : ∀ e ∈ bondsWithin (sitesInBlocks R.params.side (s.restSet c)), ∀ z, z ∉ S₀ →
        _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side e.1) z ≤ HoleBounds.wallMargin →
        splicedField s K D (s.restSet c) ζ e.1 e.2 = minimizerOn s (s.restSet c) e.1 e.2 := by
      intro e _ z hz hd
      refine splicedField_of_not_mem ζ _ _ fun h => hz (hb.zone_sub _ ?_)
      have hw : HoleBounds.wallMargin = 5 := rfl
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm, hw] at hd
      exact thickening_mono (by omega) (mem_thickening_add h hd)
    have hsave := hp.saves _ _ hwall (splicedBases_isBaseChoice ζ hH hb hζ)
    have hsum := sum_share_add_le_sum_splicedCost ζ hSA hH hb hζ hm4 hcE hbad hsave
    set ρ₀ := R.params.side * (Dh - 2) with hρ₀
    have hein := nearDebt_nonneg (R := R) (δ := δ) ha hA hg ρ₀
    have hw : 0 ≤ 2 * (2 * (R.params.side : ℝ) + 1) ^ 4 * A := by positivity
    have hN : ∀ Y ∈ blocksNear R.params.side R.range K,
        |blockCost R.params R.depth (nearPieceField s _ ζ) s.coarse s.bases Y - splicedCost s K D S₀ (s.restSet c) ζ Y| ≤
          blockError (blocksNear R.params.side R.range K) D (nearDebt R A δ g ρ₀)
            (2 * (2 * (R.params.side : ℝ) + 1) ^ 4 * A) (δ * R.params.side / 2) Y := by
      intro Y hY
      unfold blockError
      rw [if_pos (mem_thickening_self _ hY)]
      refine (abs_blockCost_sub_splicedCost_le_near ζ hSh hA hδ hs₀ h64 hc hH hb hζ hp.splits hD1 hD2 hNb
        (mem_thickening_self _ hY)).trans ?_
      unfold nearDebt
      have h1 := movedDebt_nonneg (δ := δ) hA hg ρ₀
      have h2 : (0 : ℝ) ≤ (2 * (R.params.side : ℝ) + 1) ^ 4 := by positivity
      have h3 := mul_nonneg h2 h1
      have h4 : 0 ≤ R.params.coupling * (4 * (10 * R.params.side * (2 * g))) := by positivity
      change _ ≤ _ * shareDebt A δ ρ₀ + _
      unfold shareDebt
      linarith
    have hO : ∀ Y, Y ∉ blocksNear R.params.side R.range K →
        |(blockCost R.params R.depth (nearPieceField s _ ζ) s.coarse s.bases Y -
            blockCost R.params R.depth (s.field 0) s.coarse s.bases Y) -
          (splicedCost s K D S₀ (s.restSet c) ζ Y -
            levelShare R.params.coupling R.params.side (R.depth + 1) (s.restSet c) Y s.coarse)| ≤
          blockError (blocksNear R.params.side R.range K) D (nearDebt R A δ g ρ₀)
            (2 * (2 * (R.params.side : ℝ) + 1) ^ 4 * A) (δ * R.params.side / 2) Y := by
      intro Y hY
      unfold blockError
      by_cases h4 : Y ∈ thickening (4 * D) (blocksNear R.params.side R.range K)
      · rw [if_pos h4]
        by_cases hh : Y ∈ thickening Dh (blocksNear R.params.side R.range K)
        · exact abs_block_debt_le_near ζ hSh hA hδ hs₀ h64 hc hH hb hζ hp.splits hD1 hD2 hNb hY hh
        · exact abs_block_debt_le_mid ζ hSh hA hδ hs₀ h64 hc hH hb hζ hp.splits hD1 hD2 hNb hY hh
      · rw [if_neg h4]
        exact abs_block_debt_le_far ζ hSh hA hδ hs₀ h64 hc hH hb hζ hp.splits hD1 hD2 hNb h4
    have hall := sum_le_of_block_bounds
      (fun Y => blockCost R.params R.depth (nearPieceField s _ ζ) s.coarse s.bases Y)
      (fun Y => blockCost R.params R.depth (s.field 0) s.coarse s.bases Y) (splicedCost s K D S₀ (s.restSet c) ζ)
      (fun Y => levelShare R.params.coupling R.params.side (R.depth + 1) (s.restSet c) Y s.coarse)
      (blockError (blocksNear R.params.side R.range K) D (nearDebt R A δ g ρ₀)
        (2 * (2 * (R.params.side : ℝ) + 1) ^ 4 * A) (δ * R.params.side / 2))
      (blocksNear R.params.side R.range K) _ hN hO hsum
    have herr := sum_blockError_le (D := D) (Nb := blocksNear R.params.side R.range K) hein hw hA'
    have hcount : ((m : ℕ) : ℝ) = ((s.coarseLumpsInPiece c K).card : ℝ) := by rw [hp.count_eq]
    rw [hcount] at hall
    have hcn : s.energyNear (blocksNear R.params.side R.range K) η =
        ∑ Y ∈ blocksNear R.params.side R.range K, blockCost R.params R.depth (nearPieceField s _ ζ) s.coarse s.bases Y +
        ∑ Y ∈ Finset.univ \ blocksNear R.params.side R.range K,
          (blockCost R.params R.depth (nearPieceField s _ ζ) s.coarse s.bases Y -
            blockCost R.params R.depth (s.field 0) s.coarse s.bases Y) := rfl
    rw [hcn]
    have hNc : (0 : ℝ) ≤ ((blocksNear R.params.side R.range K).card : ℝ) := Nat.cast_nonneg _
    have hq' : R.coupling * (((blocksNear R.params.side R.range K).card : ℝ) * totalDebt R A δ g A' D Dh) ≤
        Xq * ((blocksNear R.params.side R.range K).card : ℝ) := by
      have := mul_le_mul_of_nonneg_right hq hNc
      linarith
    have herr' : ∑ Y : TorusSite n, blockError (blocksNear R.params.side R.range K) D (nearDebt R A δ g ρ₀)
        (2 * (2 * (R.params.side : ℝ) + 1) ^ 4 * A) (δ * R.params.side / 2) Y ≤
        ((blocksNear R.params.side R.range K).card : ℝ) * totalDebt R A δ g A' D Dh := herr
    have hmul := mul_le_mul_of_nonneg_left (hall.trans' (by linarith [herr'] :
      ∑ Y ∈ blocksNear R.params.side R.range K,
          levelShare R.params.coupling R.params.side (R.depth + 1) (s.restSet c) Y s.coarse +
        (6 * R.params.κ * R.params.threshold ^ 2 * ((s.coarseLumpsInPiece c K).card : ℝ) +
          R.params.κ / 4 * R.params.threshold ^ 2 * ((s.lumpsInPiece K).card : ℝ) +
          cE * ((badBlocksOff R.params.side c.badBonds c.core K).card : ℝ) -
          R.params.κ * R.params.threshold ^ 2 * ((s.lumpsInPiece K).card : ℝ)) -
        ((blocksNear R.params.side R.range K).card : ℝ) * totalDebt R A δ g A' D Dh ≤ _)) hx.le
    nlinarith
  · have hNe : blocksNear R.params.side R.range K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hNb
    have hKe : ∀ u, u ∉ K := fun u hu => by
      have : parentBlock R.params.side u ∈ blocksNear R.params.side R.range K :=
        mem_blocksNear.mpr ⟨u, rfl, u, hu, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩
      rw [hNe] at this
      simp at this
    have e1 : (s.lumpsInPiece K).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro l hl
      obtain ⟨h1, h3⟩ := Finset.mem_filter.mp hl
      obtain ⟨z, hz⟩ := lump_nonempty hb h1
      exact hKe z (h3 hz)
    have e2 : (s.coarseLumpsInPiece c K).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro l hl
      obtain ⟨h1, -, h3⟩ := Finset.mem_filter.mp hl
      obtain ⟨z, hz⟩ := nonempty_of_mem_torusHotLumps hfit h1
      obtain ⟨w, hw⟩ := exists_parentBlock_eq (L := R.params.side) hfit.L_odd hb.two_le z
      exact hKe w (h3 (mem_sitesInBlocks.mpr (hw ▸ hz)))
    have e3 : (badBlocksOff R.params.side c.badBonds c.core K).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro Y hY
      obtain ⟨hY1, -⟩ := Finset.mem_sdiff.mp hY
      obtain ⟨u, hu, -⟩ := Finset.mem_image.mp hY1
      exact hKe u (Finset.mem_inter.mp hu).2
    have e4 : s.energyNear (blocksNear R.params.side R.range K) η = 0 := by
      unfold ChartSetting.energyNear
      rw [extendByZero_of_eq_empty hNe]
      rw [hNe]
      simp
    rw [e1, e2, e3, e4, hNe]
    simp
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
open GroupMoves TorusMinimizer ShareStability ContourStability
def debtConstant (a : ℝ) (L : ℕ) (A G A' : ℝ) : ℝ :=
  6561 * ((2 * (L : ℝ) + 1) ^ 4 * A + ((2 * (L : ℝ) + 1) ^ 4 * (A + 648 * (A * G)) + 80 * a * L * G)) +
    2 * (2 * (L : ℝ) + 1) ^ 4 * A * A'
theorem totalDebt_le {R : StepSetup} {A δ g G A' : ℝ} {r D Dh : ℕ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hG : 0 ≤ G)
    (hA' : 0 ≤ A') (ha : 0 ≤ R.params.coupling) (hg0 : 0 ≤ g) (hr1 : 1 ≤ r) (h5 : r ≤ 5 * (R.params.side * (Dh - 2)))
    (hρ : R.params.side * (Dh - 2) ≤ r) (hD : D ≤ r) (hLD : r ≤ 3 * (R.params.side * D))
    (hg : g ≤ G * Real.exp (-(δ * r / 2 ^ 12))) :
    totalDebt R A δ g A' D Dh ≤
      (r : ℝ) ^ 8 * Real.exp (-(δ * r / 2 ^ 12)) * debtConstant R.params.coupling R.params.side A G A' := by
  set E := Real.exp (-(δ * r / 2 ^ 12)) with hE
  set ρ₀ := R.params.side * (Dh - 2) with hρ₀
  set Cb : ℝ := (2 * (R.params.side : ℝ) + 1) ^ 4 with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hr4 : (1 : ℝ) ≤ (r : ℝ) ^ 4 := one_le_pow₀ hrR
  have hs1 : shareDebt A δ ρ₀ ≤ A * E := by
    unfold shareDebt
    refine mul_le_mul_of_nonneg_left ?_ hA
    rw [hE, Real.exp_le_exp]
    have h1 : (r : ℝ) ≤ 5 * ρ₀ := by exact_mod_cast h5
    have h2 : 0 ≤ (ρ₀ : ℝ) := Nat.cast_nonneg _
    have h3 : δ * r ≤ δ * (5 * ρ₀) := mul_le_mul_of_nonneg_left h1 hδ
    have h4 : 0 ≤ δ * ρ₀ := mul_nonneg hδ h2
    have e : (2 : ℝ) ^ 12 = 4096 := by norm_num
    rw [e]
    linarith
  have hb : (((4 * (2 * ρ₀ + 1) ^ 4 : ℕ)) : ℝ) ≤ 324 * (r : ℝ) ^ 4 := by
    have h1 : ((2 * ρ₀ + 1 : ℕ) : ℝ) ≤ 3 * r := by
      have : 2 * ρ₀ + 1 ≤ 3 * r := by omega
      exact_mod_cast this
    have h2 : ((2 * ρ₀ + 1 : ℕ) : ℝ) ^ 4 ≤ (3 * (r : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 4
    push_cast at h2 ⊢
    nlinarith
  have hAg : A * (2 * g) ≤ A * (2 * (G * E)) := mul_le_mul_of_nonneg_left (by linarith) hA
  have hm1 : movedDebt A δ g ρ₀ ≤ (r : ℝ) ^ 4 * E * (A + 648 * (A * G)) := by
    unfold movedDebt
    have h1 : (((4 * (2 * ρ₀ + 1) ^ 4 : ℕ)) : ℝ) * (A * (2 * g)) ≤ 324 * (r : ℝ) ^ 4 * (A * (2 * (G * E))) := by
      refine mul_le_mul hb hAg (by positivity) (by positivity)
    have h2 : A * E ≤ (r : ℝ) ^ 4 * E * A := by
      have : 0 ≤ A * E := by positivity
      nlinarith
    have e : 324 * (r : ℝ) ^ 4 * (A * (2 * (G * E))) = (r : ℝ) ^ 4 * E * (648 * (A * G)) := by ring
    rw [e] at h1
    have e2 : (r : ℝ) ^ 4 * E * (A + 648 * (A * G)) = (r : ℝ) ^ 4 * E * A + (r : ℝ) ^ 4 * E * (648 * (A * G)) := by ring
    rw [e2]
    linarith
  set Q₁ : ℝ := Cb * A + (Cb * (A + 648 * (A * G)) + 80 * R.params.coupling * R.params.side * G) with hQ₁
  have hn1 : nearDebt R A δ g ρ₀ ≤ (r : ℝ) ^ 4 * E * Q₁ := by
    unfold nearDebt
    have t1 : Cb * shareDebt A δ ρ₀ ≤ (r : ℝ) ^ 4 * E * (Cb * A) := by
      have h1 := mul_le_mul_of_nonneg_left hs1 hCb0
      have h2 : 0 ≤ Cb * A * E := by positivity
      nlinarith
    have t2 : Cb * movedDebt A δ g ρ₀ ≤ (r : ℝ) ^ 4 * E * (Cb * (A + 648 * (A * G))) := by
      have h1 := mul_le_mul_of_nonneg_left hm1 hCb0
      calc Cb * movedDebt A δ g ρ₀ ≤ Cb * ((r : ℝ) ^ 4 * E * (A + 648 * (A * G))) := h1
        _ = _ := by ring
    have t3 : R.params.coupling * (4 * (10 * R.params.side * (2 * g))) ≤
        (r : ℝ) ^ 4 * E * (80 * R.params.coupling * R.params.side * G) := by
      have h1 : R.params.coupling * (4 * (10 * R.params.side * (2 * g))) = 80 * R.params.coupling * R.params.side * g := by
        ring
      rw [h1]
      have h2 : 80 * R.params.coupling * R.params.side * g ≤ 80 * R.params.coupling * R.params.side * (G * E) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      have h3 : 0 ≤ 80 * R.params.coupling * R.params.side * (G * E) := by positivity
      nlinarith
    have e : (r : ℝ) ^ 4 * E * Q₁ = (r : ℝ) ^ 4 * E * (Cb * A) +
        ((r : ℝ) ^ 4 * E * (Cb * (A + 648 * (A * G))) + (r : ℝ) ^ 4 * E * (80 * R.params.coupling * R.params.side * G)) := by
      rw [hQ₁]
      ring
    rw [e]
    linarith
  have hc1 : (((2 * (4 * D : ℕ) + 1 : ℕ) : ℝ)) ^ 4 ≤ 6561 * (r : ℝ) ^ 4 := by
    have h1 : ((2 * (4 * D : ℕ) + 1 : ℕ) : ℝ) ≤ 9 * r := by
      have : 2 * (4 * D) + 1 ≤ 9 * r := by omega
      exact_mod_cast this
    have h2 : ((2 * (4 * D : ℕ) + 1 : ℕ) : ℝ) ^ 4 ≤ (9 * (r : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 4
    nlinarith
  have hexp : Real.exp (-(δ * R.params.side / 2 * (4 * D : ℕ) / 2)) ≤ E := by
    rw [hE, Real.exp_le_exp]
    have h1 : (r : ℝ) ≤ 3 * ((R.params.side : ℝ) * D) := by exact_mod_cast hLD
    have h2 : δ * r ≤ δ * (3 * ((R.params.side : ℝ) * D)) := mul_le_mul_of_nonneg_left h1 hδ
    have h3 : 0 ≤ δ * ((R.params.side : ℝ) * D) := by positivity
    have e : δ * R.params.side / 2 * ((4 * D : ℕ) : ℝ) / 2 = δ * ((R.params.side : ℝ) * D) := by
      push_cast
      ring
    rw [e]
    have e2 : (2 : ℝ) ^ 12 = 4096 := by norm_num
    rw [e2]
    linarith
  unfold totalDebt debtConstant
  have t1 : (((2 * (4 * D : ℕ) + 1 : ℕ) : ℝ)) ^ 4 * nearDebt R A δ g ρ₀ ≤ 6561 * (r : ℝ) ^ 4 * ((r : ℝ) ^ 4 * E * Q₁) := by
    refine mul_le_mul hc1 hn1 (nearDebt_nonneg ha hA hg0 ρ₀) (by positivity)
  have t2 : (2 * Cb * A) * (A' * Real.exp (-(δ * R.params.side / 2 * (4 * D : ℕ) / 2))) ≤
      (r : ℝ) ^ 8 * E * (2 * Cb * A * A') := by
    have h1 : 0 ≤ 2 * Cb * A * A' := by positivity
    have h2 : (2 * Cb * A) * (A' * Real.exp (-(δ * R.params.side / 2 * (4 * D : ℕ) / 2))) ≤ (2 * Cb * A * A') * E := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hexp h1
    have h3 : (1 : ℝ) ≤ (r : ℝ) ^ 8 := one_le_pow₀ hrR
    have h4 : 0 ≤ (2 * Cb * A * A') * E := by positivity
    nlinarith
  have e3 : 6561 * (r : ℝ) ^ 4 * ((r : ℝ) ^ 4 * E * Q₁) = (r : ℝ) ^ 8 * E * (6561 * Q₁) := by ring
  rw [e3] at t1
  have e4 : (r : ℝ) ^ 8 * E * (6561 * (Cb * A + (Cb * (A + 648 * (A * G)) + 80 * R.params.coupling * R.params.side * G)) +
      2 * Cb * A * A') = (r : ℝ) ^ 8 * E * (6561 * Q₁) + (r : ℝ) ^ 8 * E * (2 * Cb * A * A') := by
    rw [hQ₁]
    ring
  rw [e4]
  linarith
theorem le_clusterRange {m : ℕ} {x : ℝ} (hx : (m : ℝ) ^ 100 ≤ x) : m ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
theorem clusterRange_le_two_mul {x : ℝ} (hx : 1 ≤ x) : (clusterRange x : ℝ) ≤ 2 * x := by apply _root_.YangMills.SharedProofs.p24708 <;> assumption
end YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood
end
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
namespace ClassNeighbourhood
open GroupMoves TorusMinimizer ShareStability ContourStability
theorem sizes_of_range_large {L r r' m₁ : ℕ} (hL : 2 ^ 16 ≤ L) (hr : L * 2 ^ 14 + 2 ^ 11 * (m₁ + 2 ^ 5) + 2 ^ 20 ≤ r)
    (h1 : r ≤ r' + 1) :
    10 * r / L + 1 ≤ r' ∧ L * ((r / L - 8) + 8) ≤ r ∧ 2 ^ 16 ≤ r ∧ 2 ^ 16 ≤ r' ∧ 2 ^ 13 ≤ r / L - 8 ∧
      5 * r / L + (r / L - 8) + 9 ≤ r' / 2 ∧ 16 ≤ r / 2 ^ 11 ∧ m₁ ≤ r / 2 ^ 11 ∧ r ≤ 2 ^ 12 * (r / 2 ^ 11) ∧
      2 * (((r / L - 8) - 14) / 2) + 14 ≤ r / L - 8 ∧ 16 ≤ ((r / L - 8) - 14) / 2 ∧
      r ≤ 5 * (L * (((r / L - 8) - 14) / 2 - 2)) ∧ L * (((r / L - 8) - 14) / 2 - 2) ≤ r ∧ r / L - 8 ≤ r ∧
      r ≤ 3 * (L * (r / L - 8)) := by
  have hL0 : 0 < L := by omega
  set q := r / L with hq
  have hqL : L * q ≤ r := Nat.mul_div_le r L
  have hqr : r < L * q + L := by
    have := Nat.lt_mul_div_succ r hL0
    rw [← hq] at this
    linarith [Nat.mul_succ L q]
  have hq14 : 2 ^ 14 ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le hL0]
    nlinarith
  have hq16 : 2 ^ 16 * q ≤ r := (Nat.mul_le_mul_right q hL).trans hqL
  have e10 : (10 * r / L) * 2 ^ 16 ≤ 10 * r :=
    (Nat.mul_le_mul_left _ hL).trans (Nat.div_mul_le_self (10 * r) L)
  have e5 : (5 * r / L) * 2 ^ 16 ≤ 5 * r :=
    (Nat.mul_le_mul_left _ hL).trans (Nat.div_mul_le_self (5 * r) L)
  have hm : (r / 2 ^ 11) * 2 ^ 11 ≤ r := Nat.div_mul_le_self r _
  have hq8 : L * ((q - 8) + 8) = L * q := by
    congr 1
    omega
  set u := (q - 8 - 14) / 2 - 2 with hu
  have hu1 : q ≤ 4 * u := by omega
  have hu2 : u ≤ q := by omega
  have hu3 : 1 ≤ u := by omega
  have h4 : L * q ≤ 4 * (L * u) := by
    calc L * q ≤ L * (4 * u) := Nat.mul_le_mul_left _ hu1
      _ = 4 * (L * u) := by ring
  have h6 : L * u ≤ L * q := Nat.mul_le_mul_left _ hu2
  have h7 : L * (q - 8) + 8 * L = L * q := by
    rw [← hq8]
    ring
  have h8 : L * 13 ≤ L * q := Nat.mul_le_mul_left _ (by omega)
  refine ⟨?_, by rw [hq8]; exact hqL, by omega, by omega, by omega, ?_, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega⟩
  · omega
  · omega
end ClassNeighbourhood
open BlockAverages hiding unitStep
open LumpContours hiding supDist
open TorusFields TorusLumps StepSettings StepCosts StepMarks HoleOnTori TorusShares TorusBalls TorusFrame TopLevelSites
open ColdStepAtMirrorFrames
open ClassNeighbourhood in
theorem energyNearPieceBound_holds (hSR : ShareLocalityExists) (hSC : LevelShareSplits)
    (hFA : StepFrames.FrameNearMinimizer) (hTab : RenormalizationStepParameters.HoleSavingAtFixedParameters) (hSA : SharesSumToAction)
    (hc : ComplementOfThickenedLumpsRegular) (hH : TorusFrames.hotLumpsOfStepStatement)
    (hCost : WholeCellCostEqualsMinimalAction) :
    StepEnergy.EnergyNearPieceBound := by
  intro T hT
  have ha0 : 0 < T.coupling := by have := hT.a_ge; linarith
  obtain ⟨A, hA0, hSh⟩ := hSR T.coupling T.δ₁ T.side T.lam T.ρA T.σA T.cg T.N ha0 hT.L_odd hT.chain
  have hδ : 0 < T.δ₁ := hT.δ₁_pos
  have hN0 : 0 < T.N 0 := hT.chain.2.2.2.2.2.2.2.1 0
  have hLpos : (0 : ℝ) < T.side := by exact_mod_cast hT.L_odd.pos
  have hcc : 0 < T.δ₁ * T.side / 2 := by positivity
  obtain ⟨A', hA'0, hA'⟩ := exists_sum_exp_supDist_le (T.δ₁ * T.side / 2) hcc
  refine ⟨((10 : ℕ) : ℝ), T.δ₁ / 2 ^ 13, by positivity, ?_⟩
  set G : ℝ := T.N 0 * (2 * T.threshold) with hG
  have hσ : 0 < T.threshold := hT.σ_pos
  have hG0 : 0 ≤ G := by positivity
  set Q : ℝ := debtConstant T.coupling T.side A G A' with hQ
  have hQ0 : 0 ≤ Q := by
    rw [hQ]
    unfold debtConstant
    have := hA0.le
    positivity
  set m₁ : ℕ := ⌈Real.log (1024 * T.N 0) / T.δ₁⌉₊ with hm₁
  set r₀ : ℕ := T.side * 2 ^ 14 + 2 ^ 11 * (m₁ + 2 ^ 5) + 2 ^ 20 with hr₀
  refine ⟨max T.floorMin (max ((r₀ : ℝ) ^ 100) (max (2 ^ 8 * Q) 1)), fun y hy R hR => ?_⟩
  have hℓ := hR.params_eq
  have hρA := hR.anchorRadius_eq
  have hyx := hR.le_coupling
  have hy1 : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hy3 : (r₀ : ℝ) ^ 100 ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hy4 : 2 ^ 8 * Q ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))
  have hy5 : 1 ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))
  have hfit : R.params.Admissible := by
    rw [hℓ]
    exact hT.fits y hy1
  have eL : R.params.side = T.side := by rw [hℓ]; rfl
  have ea : R.params.coupling = T.coupling := by rw [hℓ]; rfl
  have eσ : R.params.threshold = T.threshold := by rw [hℓ]; rfl
  have hchain : ColdChain.ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [hℓ, hρA]
    exact hT.chain
  have hch : ChainData R T.δ₁ T.lam T.σA T.cg T.N := ⟨hfit, hchain, by rw [eσ]; exact hT.σ_le⟩
  have hSh' : ShareLocality R.params.coupling R.params.side T.σA A T.δ₁ := by
    rw [ea, eL]
    exact hSh
  have hsv : HoleSavingBounds R.params T.cE := by
    rw [hℓ]
    exact (hTab T hT).2 y
  have hcE : 0 ≤ T.cE := hT.cE_pos.le
  have hx1 : 1 ≤ R.coupling := hy5.trans hyx
  have hx0 : 0 < R.coupling := by linarith
  have hr1 : R.range ≤ clusterRange R.nextCoupling + 1 := hR.isStep.2.2
  set r := R.range with hr
  have hrx : r = clusterRange R.coupling := rfl
  have hr0 : r₀ ≤ r := le_clusterRange (hy3.trans hyx)
  have hLge : 2 ^ 16 ≤ R.params.side := hfit.L_ge
  have hr0' : R.params.side * 2 ^ 14 + 2 ^ 11 * (m₁ + 2 ^ 5) + 2 ^ 20 ≤ r := by
    rw [eL]
    exact hr0
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15⟩ :=
    sizes_of_range_large hLge hr0' hr1
  set D := r / R.params.side - 8 with hD
  set Dh := (D - 14) / 2 with hDh
  set m₀ := r / 2 ^ 11 with hm₀
  set g : ℝ := T.N 0 * (2 * T.threshold) * Real.exp (-(T.δ₁ * (m₀ : ℝ))) with hg
  have hg0 : 0 ≤ g := by positivity
  have hlog : Real.log (1024 * T.N 0) ≤ T.δ₁ * m₀ := by
    have h1 : Real.log (1024 * T.N 0) / T.δ₁ ≤ m₁ := Nat.le_ceil _
    have h2 : (m₁ : ℝ) ≤ m₀ := by exact_mod_cast s8
    have h3 := (div_le_iff₀ hδ).mp (h1.trans h2)
    linarith
  have hexp1 : Real.exp (-(T.δ₁ * (m₀ : ℝ))) ≤ (1024 * T.N 0)⁻¹ := by
    rw [← Real.exp_log (by positivity : 0 < 1024 * T.N 0), ← Real.exp_neg, Real.exp_le_exp]
    linarith
  have hg512 : g ≤ T.threshold / 512 := by
    have h1 : g ≤ T.N 0 * (2 * T.threshold) * (1024 * T.N 0)⁻¹ :=
      mul_le_mul_of_nonneg_left hexp1 (by positivity)
    have h2 : T.N 0 * (2 * T.threshold) * (1024 * T.N 0)⁻¹ = T.threshold / 512 := by
      field_simp
      norm_num
    linarith
  have hnum : StepSizes R D g := by
    refine ⟨⟨hfit, s1, s2, s3, s4⟩, s5, s6, ⟨hr1, s4, s7⟩, hg0, ?_, ?_⟩
    · rw [eσ]
      linarith
    · unfold StepSetup.ballRadius
      rw [eσ]
      linarith
  have hgN : T.N 0 * (2 * R.params.threshold) * Real.exp (-(T.δ₁ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤ g := by
    rw [eσ]
  have hgE : g ≤ G * Real.exp (-(T.δ₁ * r / 2 ^ 12)) := by
    refine mul_le_mul_of_nonneg_left ?_ hG0
    rw [Real.exp_le_exp]
    have h1 : (r : ℝ) ≤ 2 ^ 12 * m₀ := by exact_mod_cast s9
    have h2 : T.δ₁ * r ≤ T.δ₁ * (2 ^ 12 * m₀) := mul_le_mul_of_nonneg_left h1 hδ.le
    have e : T.δ₁ * (2 ^ 12 * (m₀ : ℝ)) = 2 ^ 12 * (T.δ₁ * m₀) := by ring
    rw [e] at h2
    have h3 : T.δ₁ * r / 2 ^ 12 ≤ T.δ₁ * m₀ := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 12)]
      linarith
    linarith
  have hrR : (r : ℝ) ≤ 2 * R.coupling := clusterRange_le_two_mul hx1
  have hr1' : 1 ≤ r := by omega
  have hower := totalDebt_le (R := R) (A := A) (δ := T.δ₁) (g := g) (G := G) (A' := A') (r := r) (D := D) (Dh := Dh)
    hA0.le hδ.le hG0 hA'0 (by rw [ea]; exact ha0.le) hg0 hr1' s12 s13 s14 s15 hgE
  have hQe : debtConstant R.params.coupling R.params.side A G A' = Q := by rw [ea, eL]
  rw [hQe] at hower
  have hq : R.coupling * totalDebt R A T.δ₁ g A' D Dh ≤
      R.coupling ^ ((10 : ℕ) : ℝ) * Real.exp (-(T.δ₁ / 2 ^ 13 * r)) := by
    rw [Real.rpow_natCast]
    set E := Real.exp (-(T.δ₁ * r / 2 ^ 12)) with hE
    have hEpos : 0 < E := Real.exp_pos _
    have hE2 : E ≤ Real.exp (-(T.δ₁ / 2 ^ 13 * r)) := by
      rw [hE, Real.exp_le_exp]
      have h1 : 0 ≤ T.δ₁ * r := by positivity
      have e : T.δ₁ / 2 ^ 13 * r = T.δ₁ * r / 2 ^ 13 := by ring
      rw [e]
      have e2 : (2 : ℝ) ^ 12 = 4096 := by norm_num
      have e3 : (2 : ℝ) ^ 13 = 8192 := by norm_num
      rw [e2, e3]
      linarith
    have h8 : (r : ℝ) ^ 8 ≤ (2 * R.coupling) ^ 8 := pow_le_pow_left₀ (Nat.cast_nonneg _) hrR 8
    have hQx : 2 ^ 8 * Q ≤ R.coupling := hy4.trans hyx
    calc R.coupling * totalDebt R A T.δ₁ g A' D Dh ≤ R.coupling * ((r : ℝ) ^ 8 * E * Q) :=
          mul_le_mul_of_nonneg_left hower hx0.le
      _ ≤ R.coupling * ((2 * R.coupling) ^ 8 * E * Q) := by
          refine mul_le_mul_of_nonneg_left ?_ hx0.le
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h8 hEpos.le) hQ0
      _ = R.coupling ^ 9 * (2 ^ 8 * Q) * E := by ring
      _ ≤ R.coupling ^ 9 * R.coupling * E := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQx (by positivity)) hEpos.le
      _ = R.coupling ^ 10 * E := by ring
      _ ≤ R.coupling ^ 10 * Real.exp (-(T.δ₁ / 2 ^ 13 * r)) := mul_le_mul_of_nonneg_left hE2 (by positivity)
  intro n _ s st K η hn hs hst hm hK hball hbad
  obtain ⟨S₀, m, hp⟩ := exists_cutPlace hch hc hCost hSC hFA hsv hnum hgN hn (by omega) hs hst hm hK
  have h64 : 64 ≤ n * R.params.side := by
    have h1 := hfit.n₀_ge
    have h2 : 0 < R.params.side := by omega
    have h3 : 64 ≤ n := by omega
    exact h3.trans (Nat.le_mul_of_pos_right n h2)
  have hs₀ : R.params.threshold ≤ T.σA := by
    have := hch.threshold_le
    have := hfit.σ_pos
    linarith
  refine energy_bound_of_cutPlace hcE hSh' hA0.le hδ.le hs₀ hc hH hSA hp h64 hball (fun b hb hbK => (hbad b hb hbK).2)
    s10 s11 ?_ ?_ hx0 hq
  · change 2 ≤ 4 * (R.range / 2 ^ 11)
    omega
  · intro y₀ Dd
    have := hA' n y₀ Dd
    rw [eL]
    exact this
end YangMills.Construction.ClusterExpansionOfAStep
