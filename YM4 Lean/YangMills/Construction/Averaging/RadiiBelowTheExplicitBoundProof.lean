import YangMills.Construction.Averaging.AveragingMapRealAnalyticAtSmallRadii
import YangMills.Construction.Averaging.EverySmallRadiusServes
import YangMills.Construction.Averaging.RadiiBelowTheExplicitBound
import YangMills.Construction.Lattice.DoubleBlockContours
import YangMills.Construction.Lattice.HolonomyCommutingEqualSteps
import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocks
import YangMills.Construction.Lattice.SpreadOfAContourFamily
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices PeriodicLattice
namespace Averaging.ExplicitRadiiProof
theorem radius_mul_sq_le {L : ℕ} (hL : 13 ≤ L) {ω : ℝ}
    (hω : ω ∈ Ioc (0 : ℝ) (averagingRadiusCap L)) : ω * (L : ℝ) ^ 2 ≤ 1 / 200 := by
  have h := hω.2
  rw [averagingRadiusCap, le_div_iff₀ (by positivity)] at h
  linarith
theorem swapDiameter_lt {L : ℕ} (hL : 13 ≤ L) {ω : ℝ}
    (hω : ω ∈ Ioc (0 : ℝ) (averagingRadiusCap L)) : 3 / 2 * ((L : ℝ) - 1) ^ 2 * ω < 3 / 400 := by
  have h := radius_mul_sq_le hL hω
  have hL' : (13 : ℝ) ≤ L := by exact_mod_cast hL
  have hsq : ((L : ℝ) - 1) ^ 2 < (L : ℝ) ^ 2 := by nlinarith
  have := mul_lt_mul_of_pos_right hsq hω.1
  nlinarith
theorem averagingRadiusCap_mem {L : ℕ} (hL : 13 ≤ L) : averagingRadiusCap L ∈ Ioc (0 : ℝ) 1 := by
  have hL' : (13 : ℝ) ≤ L := by exact_mod_cast hL
  have hden : (0 : ℝ) < 200 * (L : ℝ) ^ 2 := by positivity
  unfold averagingRadiusCap
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hden]
  nlinarith
section Reindex
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
theorem isLogMean_comp_equiv (e : ι ≃ κ) (𝒢 : Set ComplexMatrix2) (f : κ → ComplexMatrix2)
    (W : ComplexMatrix2) :
    ComplexMatrix2.IsLogMean 𝒢 (f ∘ e) W ↔ ComplexMatrix2.IsLogMean 𝒢 f W := by
  unfold ComplexMatrix2.IsLogMean
  refine and_congr_right fun _ => and_congr ?_ ?_
  · exact ⟨fun h i => by simpa using h (e.symm i), fun h i => h (e i)⟩
  · rw [show ∑ i, ComplexMatrix2.logSeries ((f ∘ e) i * W⁻¹) =
        ∑ i, ComplexMatrix2.logSeries (f i * W⁻¹) from
      Equiv.sum_comp e fun i => ComplexMatrix2.logSeries (f i * W⁻¹)]
theorem complexLogMean_comp_equiv (e : ι ≃ κ) (f : κ → ComplexMatrix2) :
    complexLogMean (f ∘ e) = complexLogMean f := by
  have hp : (fun W => ComplexMatrix2.IsLogMean complexGaugeGroup (f ∘ e) W ∧
        ∃ i, ComplexMatrix2.operatorNorm ((f ∘ e) i * W⁻¹ - 1) ≤ complexMeanTolerance) =
      fun W => ComplexMatrix2.IsLogMean complexGaugeGroup f W ∧
        ∃ i, ComplexMatrix2.operatorNorm (f i * W⁻¹ - 1) ≤ complexMeanTolerance := by
    funext W
    refine propext (and_congr (isLogMean_comp_equiv e _ f W) ⟨?_, ?_⟩)
    · rintro ⟨i, h⟩
      exact ⟨e i, h⟩
    · rintro ⟨i, h⟩
      exact ⟨e.symm i, by simpa using h⟩
  simp only [complexLogMean, hp]
end Reindex
theorem isRealAnalyticBetween_pair {ι : Type} [Fintype ι] {s : ι → ComplexMatrix2.FactorKind}
    {D : Set (ι → ComplexMatrix2)} {a b : (ι → ComplexMatrix2) → ComplexMatrix2}
    (ha : ComplexMatrix2.IsRealAnalyticBetween s
      (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group) D fun v _ => a v)
    (hb : ComplexMatrix2.IsRealAnalyticBetween s
      (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group) D fun v _ => b v) :
    ComplexMatrix2.IsRealAnalyticBetween s
      (fun _ : Fin 2 => ComplexMatrix2.FactorKind.group) D fun v => ![a v, b v] := by
  refine ⟨ha.1, fun x hx => ?_⟩
  obtain ⟨W₁, g₁, hxW₁, ⟨⟨O₁, hO₁, rfl⟩, hmap₁, hF₁⟩, he₁⟩ := ha.2 x hx
  obtain ⟨W₂, g₂, hxW₂, ⟨⟨O₂, hO₂, rfl⟩, hmap₂, hF₂⟩, he₂⟩ := hb.2 x hx
  refine ⟨(O₁ ∩ O₂) ∩ ComplexMatrix2.complexifiedProduct s, fun y => ![g₁ y 0, g₂ y 0],
    ⟨⟨hxW₁.1, hxW₂.1⟩, hxW₁.2⟩, ⟨⟨O₁ ∩ O₂, hO₁.inter hO₂, rfl⟩, ?_, ?_⟩, ?_⟩
  · intro y hy i
    have h₁ := hmap₁ (show y ∈ O₁ ∩ ComplexMatrix2.complexifiedProduct s from ⟨hy.1.1, hy.2⟩) 0
    have h₂ := hmap₂ (show y ∈ O₂ ∩ ComplexMatrix2.complexifiedProduct s from ⟨hy.1.2, hy.2⟩) 0
    fin_cases i
    · exact h₁
    · exact h₂
  · intro z hz
    obtain ⟨F₁, hA₁, hE₁⟩ := hF₁ z ⟨hz.1.1, hz.2⟩
    obtain ⟨F₂, hA₂, hE₂⟩ := hF₂ z ⟨hz.1.2, hz.2⟩
    refine ⟨fun y => ![F₁ y 0, F₂ y 0], ?_, ?_⟩
    · rw [analyticAt_pi_iff]
      intro i
      fin_cases i
      · exact analyticAt_pi_iff.1 hA₁ 0
      · exact analyticAt_pi_iff.1 hA₂ 0
    · have s₁ : (O₁ ∩ O₂) ∩ ComplexMatrix2.complexifiedProduct s ⊆
          O₁ ∩ ComplexMatrix2.complexifiedProduct s :=
        fun y hy => ⟨hy.1.1, hy.2⟩
      have s₂ : (O₁ ∩ O₂) ∩ ComplexMatrix2.complexifiedProduct s ⊆
          O₂ ∩ ComplexMatrix2.complexifiedProduct s :=
        fun y hy => ⟨hy.1.2, hy.2⟩
      filter_upwards [nhdsWithin_mono z s₁ hE₁, nhdsWithin_mono z s₂ hE₂] with y h₁ h₂
      rw [h₁, h₂]
  · filter_upwards [he₁, he₂] with y h₁ h₂
    have e₁ : a y = g₁ y 0 := congrFun h₁ 0
    have e₂ : b y = g₂ y 0 := congrFun h₂ 0
    rw [e₁, e₂]
section GroupNorms
theorem norm_mul_specialUnitary {u : ComplexMatrix2} (h : u ∈ ComplexMatrix2.specialUnitary)
    (Y : ComplexMatrix2) : ‖Y * u‖ = ‖Y‖ :=
  CStarRing.norm_mul_coe_unitary Y ⟨u, Matrix.specialUnitaryGroup_le_unitaryGroup h⟩
theorem norm_specialUnitary_mul {u : ComplexMatrix2} (h : u ∈ ComplexMatrix2.specialUnitary)
    (Y : ComplexMatrix2) : ‖u * Y‖ = ‖Y‖ :=
  CStarRing.norm_mem_unitary_mul Y (Matrix.specialUnitaryGroup_le_unitaryGroup h)
theorem specialUnitary_inv_mem {U : ComplexMatrix2} (h : U ∈ ComplexMatrix2.specialUnitary) :
    U⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
theorem specialUnitary_mul_inv {U : ComplexMatrix2} (h : U ∈ ComplexMatrix2.specialUnitary) :
    U * U⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p21267 <;> assumption
theorem specialUnitary_mem_complexGaugeGroup {U : ComplexMatrix2}
    (h : U ∈ ComplexMatrix2.specialUnitary) : U ∈ complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.mp h).2
theorem norm_sub_eq_norm_mul_inv_sub_one {a G : ComplexMatrix2}
    (ha : a ∈ ComplexMatrix2.specialUnitary) : ‖a - G‖ = ‖G * a⁻¹ - 1‖ := by
  have e : (G * a⁻¹ - 1) = -((a - G) * a⁻¹) := by
    rw [sub_mul, specialUnitary_mul_inv ha]
    abel
  rw [e, norm_neg, norm_mul_specialUnitary (specialUnitary_inv_mem ha)]
theorem norm_crossing_sub_one_le {a b G G' X T : ComplexMatrix2} {A B : ℝ}
    (ha : a ∈ ComplexMatrix2.specialUnitary) (hb : b ∈ ComplexMatrix2.specialUnitary)
    (hX : X ∈ ComplexMatrix2.specialUnitary) (hT : T ∈ ComplexMatrix2.specialUnitary)
    (h₁ : ‖G * a⁻¹ - 1‖ ≤ A) (h₂ : ‖G' * b⁻¹ - 1‖ ≤ A) (h₃ : ‖G * X - T * G'‖ ≤ B) :
    ‖a * X * b⁻¹ * T⁻¹ - 1‖ ≤ 2 * A + B := by
  have e₁ : a * X * b⁻¹ * T⁻¹ - 1 = (a * X - T * b) * (b⁻¹ * T⁻¹) := by
    rw [sub_mul, mul_assoc T, ← mul_assoc b, specialUnitary_mul_inv hb, one_mul,
      specialUnitary_mul_inv hT]
    simp only [mul_assoc]
  have e₂ : a * X - T * b = (a - G) * X + (G * X - T * G') + T * (G' - b) := by noncomm_ring
  rw [e₁, norm_mul_specialUnitary
    (mul_mem (specialUnitary_inv_mem hb) (specialUnitary_inv_mem hT)), e₂]
  calc ‖(a - G) * X + (G * X - T * G') + T * (G' - b)‖
      ≤ ‖(a - G) * X‖ + ‖G * X - T * G'‖ + ‖T * (G' - b)‖ := norm_add₃_le
    _ = ‖a - G‖ + ‖G * X - T * G'‖ + ‖G' - b‖ := by
        rw [norm_mul_specialUnitary hX, norm_specialUnitary_mul hT]
    _ ≤ 2 * A + B := by
        have : ‖G' - b‖ = ‖G' * b⁻¹ - 1‖ := by
          rw [norm_sub_rev, norm_sub_eq_norm_mul_inv_sub_one hb]
        rw [this, norm_sub_eq_norm_mul_inv_sub_one ha]
        linarith
end GroupNorms
section Counting
theorem countP_le_sum_countP {α ι : Type*} (l : List α) (P : α → Bool) (S : Finset ι)
    (Q : ι → α → Bool) (h : ∀ a ∈ l, P a = true → ∃ i ∈ S, Q i a = true) :
    l.countP P ≤ ∑ i ∈ S, l.countP (Q i) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.countP_cons, Finset.sum_add_distrib]
    by_cases hP : P a = true
    · obtain ⟨i, hi, hQ⟩ := h a List.mem_cons_self hP
      have : 1 ≤ ∑ i ∈ S, (if Q i a = true then 1 else 0) :=
        (by simp [hQ] : 1 ≤ (if Q i a = true then 1 else 0)).trans
          (Finset.single_le_sum (f := fun i => if Q i a = true then 1 else 0)
            (fun _ _ => Nat.zero_le _) hi)
      simp only [hP, if_true]
      omega
    · simp only [hP]
      simp
      omega
variable {L m : ℕ} {j : ℤ}
theorem countP_pathOfWord (P : Site L m j → Bool) (z : Site L m j) (𝔞 : StepWord L m j) :
    (pathOfWord z 𝔞).countP (fun b => P (b.target - b.source)) =
      𝔞.countP (fun s : UnitStepVec L m j => P s.1) := by
  induction 𝔞 generalizing z with
  | nil => rfl
  | cons s 𝔞 ih =>
    simp only [pathOfWord, List.countP_cons, ih, bondOfStep, add_sub_cancel_left]
theorem countP_coe_stepList (P : Site L m j → Bool) (𝔞 : StepWord L m j) :
    List.countP P (𝔞 : List (Site L m j)) = 𝔞.countP (fun s : UnitStepVec L m j => P s.1) := by
  induction 𝔞 with
  | nil => rfl
  | cons s 𝔞 ih =>
    have e : ((s :: 𝔞 : StepWord L m j) : List (Site L m j)) =
        (s : Site L m j) :: (𝔞 : List (Site L m j)) := rfl
    rw [e, List.countP_cons, List.countP_cons, ih]
end Counting
section Bond
variable {L m K k : ℕ}
theorem blockPlaquetteDefect_le {ω : ℝ} (hω : 0 ≤ ω) (c : BondAtLevel L m K (k + 1))
    {U : BondAtLevel L m K k → ComplexMatrix2}
    (hU : U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)))
    {y : SiteAtLevel L m K (k + 1)}
    (hy : y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1)))) :
    blockPlaquetteDefect y U ≤ ω := by
  refine Real.iSup_le (fun p => (hU.2 p.1 ?_).le) hω
  intro z hz
  have hp := p.2 z hz
  rcases hy with rfl | hy
  · exact Or.inl hp
  · rw [mem_singleton_iff] at hy
    subst hy
    exact Or.inr hp
theorem contourDiameterBounds_of (hS : ContourFamilySpread)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hk : k < K) {ω : ℝ} (hω : ω ∈ Ioc (0 : ℝ) (averagingRadiusCap L))
    (c : BondAtLevel L m K (k + 1)) : ExplicitRadii.ContourDiameterBounds ω k c := by
  intro U hU y hy x hx
  have hconf : IsGaugeField compactGaugeGroup
      (bondsInside (unitBlock y) : Set (BondAtLevel L m K k)) U :=
    ⟨fun b _ => hU.1.1 b (mem_univ _), fun b _ => hU.1.2 b (mem_univ _)⟩
  obtain ⟨-, hd, -⟩ := hS L m K hL hm k hk y U hconf x hx
  have h1 : contourSwapConstant L * blockPlaquetteDefect y U ≤
      3 / 2 * ((L : ℝ) - 1) ^ 2 * ω :=
    mul_le_mul_of_nonneg_left (blockPlaquetteDefect_le hω.1.le c hU hy)
      (by unfold contourSwapConstant; positivity)
  have h2 := swapDiameter_lt hL.2 hω
  exact ⟨hd.trans h1, h2, by linarith [hd.trans h1]⟩
theorem pathHolonomy_mem_specialUnitary {U : BondAtLevel L m K k → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m (levelDepth K k)) (Γ : List (BondAtLevel L m K k)) :
    pathHolonomy U Γ ∈ ComplexMatrix2.specialUnitary := by
  apply Submonoid.list_prod_mem
  intro X hX
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hX
  exact hU.1 b (mem_univ _)
theorem contourMean_facts (hM : ComplexLogMeanOfSmallFamilies)
    (hS : ContourFamilySpread) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hk : k < K) {ω : ℝ} (hω : ω ∈ Ioc (0 : ℝ) (averagingRadiusCap L))
    (c : BondAtLevel L m K (k + 1)) {U : BondAtLevel L m K k → ComplexMatrix2}
    (hU : U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)))
    {y : SiteAtLevel L m K (k + 1)}
    (hy : y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))))
    {x : SiteAtLevel L m K k} (hx : x ∈ sitesInBlock (levelDepth K k) y) :
    HasContourMean U y x ∧ meanContourHolonomy U y x ∈ compactGaugeGroup ∧
      complexMeanContourHolonomy U y x = meanContourHolonomy U y x ∧
      ∀ σ : AxisOrdering y x,
        ComplexMatrix2.operatorNorm
            (pathHolonomy U (orderedContour y x σ) * (meanContourHolonomy U y x)⁻¹ - 1) ≤
          6 * ((L : ℝ) - 1) ^ 2 * ω := by
  classical
  obtain ⟨hd, hlt, hlt'⟩ := contourDiameterBounds_of hS hL hm hk hω c U hU y hy x hx
  have hconf : IsGaugeField compactGaugeGroup
      (bondsInside (unitBlock y) : Set (BondAtLevel L m K k)) U :=
    ⟨fun b _ => hU.1.1 b (mem_univ _), fun b _ => hU.1.2 b (mem_univ _)⟩
  have hD0 : 0 ≤ 3 / 2 * ((L : ℝ) - 1) ^ 2 * ω := by have := hω.1; positivity
  let e : Fin (Fintype.card (AxisOrdering y x)) ≃ AxisOrdering y x :=
    (Fintype.equivFin (AxisOrdering y x)).symm
  have hne : Nonempty (AxisOrdering y x) := ⟨(offsetAxes y x).equivFin.symm⟩
  have hn : 1 ≤ Fintype.card (AxisOrdering y x) := Fintype.card_pos
  set V' : Fin (Fintype.card (AxisOrdering y x)) → ComplexMatrix2 :=
    contourHolonomies U y x ∘ e with hV'
  have hreal : ∀ i, V' i ∈ compactGaugeGroup := fun i => pathHolonomy_mem_specialUnitary hU.1 _
  have hd' : ComplexMatrix2.familyDiameter V' ≤ 3 / 2 * ((L : ℝ) - 1) ^ 2 * ω := by
    refine Real.iSup_le (fun p => le_trans ?_ hd) hD0
    exact le_ciSup (f := fun p : AxisOrdering y x × AxisOrdering y x =>
      ComplexMatrix2.operatorNorm
        (contourHolonomies U y x p.1 * (contourHolonomies U y x p.2)⁻¹ - 1))
      (Set.finite_range _).bddAbove (e p.1, e p.2)
  have hsmall : ComplexMatrix2.familyDiameter V' < centreOfMassDiameter := by
    unfold centreOfMassDiameter
    linarith
  have hmf := hM.2.2.2.1 _ hn
  have hone := hmf.exactlyOneMean V' hreal hsmall
  have hhas : HasContourMean U y x := by
    obtain ⟨W, hW, huniq⟩ := hone
    exact ⟨W, (isLogMean_comp_equiv e _ _ W).1 hW,
      fun W' h => huniq W' ((isLogMean_comp_equiv e _ _ W').2 h)⟩
  have hmean := ((hS L m K hL hm k hk y U hconf x hx).2.2 hhas).1
  have hmean' := (isLogMean_comp_equiv e _ _ _).2 hmean
  have heq : meanContourHolonomy U y x = complexLogMean V' :=
    (hmf.onlyMean V' hreal hsmall _).1 hmean'
  refine ⟨hhas, hmean.1, ?_, fun σ => ?_⟩
  · rw [heq, hV', complexLogMean_comp_equiv]
    rfl
  · have hmem : V' ∈ smallComplexFamilies _ :=
      ⟨fun i => specialUnitary_mem_complexGaugeGroup (hreal i), hsmall⟩
    have hsp := hmf.spread V' hmem (e.symm σ)
    rw [← heq] at hsp
    have hval : V' (e.symm σ) = pathHolonomy U (orderedContour y x σ) := by
      simp [hV', contourHolonomies]
    rw [hval] at hsp
    refine hsp.trans ?_
    nlinarith
theorem nonParallelStepCount_le (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : k < K)
    (c : BondAtLevel L m K (k + 1))
    (ν : Fin 4) {x : SiteAtLevel L m K k} (hx : x ∈ sitesInBlock (levelDepth K k) c.source)
    (σ : AxisOrdering c.source x) (𝔞 : StepWord L m (levelDepth K k))
    (hpath : pathOfWord (c.source.toSublattice (levelDepth K k)) 𝔞 = orderedContour c.source x σ) :
    (nonParallelStepCount 𝔞 (DoubleBlock.positiveUnitStep L m (levelDepth K k) ν) : ℤ) ≤
      3 * centreToFaceSteps L := by
  classical
  obtain ⟨hco, -, hall⟩ := (hP L m K hL.1 hL.2 hm k hk).1 c.source
  have hxi : (x : FourTorus L m) ∈ (fun p => (offsetSite (c.source.toSublattice (levelDepth K k)) p :
      FourTorus L m)) '' blockIndexBox L := by
    rw [hco.1.2]
    exact hx
  obtain ⟨p, hp, hpx⟩ := hxi
  have hxeq : offsetSite (c.source.toSublattice (levelDepth K k)) p = x := Subtype.ext hpx
  have hcc := (hall p hp).1
  rw [hxeq] at hcc
  obtain ⟨-, hcount, hstep, -, -⟩ := hcc _ ⟨σ, rfl⟩
  set Γ := orderedContour c.source x σ with hΓ
  set e : Site L m (levelDepth K k) := unitStep L m (levelDepth K k) ν with he
  set S : Finset (Fin 4) := (Finset.univ.erase ν).filter fun ν' => p ν' ≠ 0 with hSdef
  let Q : Fin 4 → BondAtLevel L m K k → Bool := fun ν' b =>
    decide (b.target - b.source = (p ν').sign • unitStep L m (levelDepth K k) ν')
  let P : Site L m (levelDepth K k) → Bool := fun s => decide (s ≠ e ∧ s ≠ -e)
  have h1 : nonParallelStepCount 𝔞 (DoubleBlock.positiveUnitStep L m (levelDepth K k) ν) =
      Γ.countP (fun b => P (b.target - b.source)) := by
    rw [← hpath, countP_pathOfWord]
    exact countP_coe_stepList _ 𝔞
  have h2 : Γ.countP (fun b => P (b.target - b.source)) ≤ ∑ ν' ∈ S, Γ.countP (Q ν') := by
    refine countP_le_sum_countP Γ _ S Q fun b hb hPb => ?_
    obtain ⟨ν', hν', hd⟩ := hstep b hb
    have hne : ν' ≠ ν := by
      rintro rfl
      have hPb' : b.target - b.source ≠ e ∧ b.target - b.source ≠ -e := by simpa [P] using hPb
      rcases lt_or_gt_of_ne hν' with h | h
      · rw [Int.sign_eq_neg_one_of_neg h] at hd
        exact hPb'.2 (by simpa [he] using hd)
      · rw [Int.sign_eq_one_of_pos h] at hd
        exact hPb'.1 (by simpa [he] using hd)
    exact ⟨ν', by simp [hSdef, hne, hν'], by simpa [Q] using hd⟩
  have h3 : ∀ ν' ∈ S, ((Γ.countP (Q ν') : ℕ) : ℤ) ≤ centreToFaceSteps L := by
    intro ν' hν'
    have hν0 : p ν' ≠ 0 := (Finset.mem_filter.mp hν').2
    obtain ⟨h4, h5⟩ := hcount ν' hν0
    have h6 : Γ.countP (Q ν') = (p ν').natAbs := h4
    rw [h6, Int.natCast_natAbs]
    exact h5
  have hcard : S.card ≤ 3 := by
    refine (Finset.card_filter_le _ _).trans ?_
    simp
  have hh : 0 ≤ centreToFaceSteps L := by
    have := hL.2
    unfold centreToFaceSteps
    omega
  rw [h1]
  calc ((Γ.countP (fun b => P (b.target - b.source)) : ℕ) : ℤ)
      ≤ ((∑ ν' ∈ S, Γ.countP (Q ν') : ℕ) : ℤ) := by exact_mod_cast h2
    _ = ∑ ν' ∈ S, ((Γ.countP (Q ν') : ℕ) : ℤ) := by push_cast; rfl
    _ ≤ S.card • centreToFaceSteps L := Finset.sum_le_card_nsmul _ _ _ h3
    _ ≤ 3 * centreToFaceSteps L := by
        rw [nsmul_eq_mul]
        have : (S.card : ℤ) ≤ 3 := by exact_mod_cast hcard
        nlinarith
theorem pathHolonomy_concat_eq_mul {j : ℤ} (U : Bond L m j → ComplexMatrix2)
    (Γ Γ' : List (Bond L m j)) :
    pathHolonomy U (Γ ++ Γ') = pathHolonomy U Γ * pathHolonomy U Γ' := by
  simp [pathHolonomy]
theorem shiftAcross_facts (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : k < K)
    (c : BondAtLevel L m K (k + 1))
    {ν : Fin 4} (hν : c.target - c.source = unitStep L m (levelDepth K (k + 1)) ν)
    {x : SiteAtLevel L m K k} (hx : x ∈ sitesInBlock (levelDepth K k) c.source) :
    shiftAcross c x = x + L • unitStep L m (levelDepth K k) ν ∧
      shiftAcross c x ∈ sitesInBlock (levelDepth K k) c.target := by
  obtain ⟨⟨-, -, -, himg, htr, -⟩, -⟩ := (hP L m K hL.1 hL.2 hm k hk).2 c ν hν
  have h1 := htr x hx
  refine ⟨?_, ?_⟩
  · rw [h1, blockTranslation, natCast_zsmul]
  · rw [h1, ← himg]
    exact ⟨x, hx, rfl⟩
theorem defectsNearOne_of (hC : DoubleBlock.DoubleBlockContoursStatement)
    (hP : BlockPaths.Statement)
    (hR : HolonomyCommutesWithEqualSteps)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : k < K) {ω : ℝ}
    (hω : ω ∈ Ioc (0 : ℝ) (averagingRadiusCap L)) (c : BondAtLevel L m K (k + 1))
    (hmeans : ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
      ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
        ∀ x ∈ sitesInBlock (levelDepth K k) y, meanContourHolonomy U y x ∈ compactGaugeGroup ∧
          ∀ σ : AxisOrdering y x,
            ComplexMatrix2.operatorNorm
                (pathHolonomy U (orderedContour y x σ) * (meanContourHolonomy U y x)⁻¹ - 1) ≤
              6 * ((L : ℝ) - 1) ^ 2 * ω) :
    ExplicitRadii.DefectsNearOne ω k c := by
  rintro ⟨ν, hν⟩ U hU x hx
  have hreal : U ∈ compactGaugeFields L m (levelDepth K k) := hU.1
  have hhead : c.target = c.source + unitStep L m (levelDepth K (k + 1)) ν := by rw [← hν]; abel
  obtain ⟨-, hsite⟩ := (hC L m K hL.1 hL.2 hm k hk c).1 c.source (Or.inl rfl)
  obtain ⟨⟨n, hn⟩, hall⟩ := hsite x hx
  obtain ⟨-, h2, -⟩ := hall n hn
  let σ : AxisOrdering c.source x := (offsetAxes c.source x).equivFin.symm
  obtain ⟨𝔞, -, hpath⟩ := h2 _ ⟨σ, rfl⟩
  have hA := (hC L m K hL.1 hL.2 hm k hk c).2 ν hhead x hx σ 𝔞 hpath
  obtain ⟨hx', ⟨σ', -, hpath'⟩, -, -, -, -, -, hp1, hp2, hs1, -, -, -⟩ := hA
  obtain ⟨hxeq, -⟩ := shiftAcross_facts hP hL hm hk c hν hx
  have hrun := hR L m hL.1 hL.2 hm (levelDepth K k) (by simp only [levelDepth]; omega) U hreal
    (c.source.toSublattice (levelDepth K k)) 𝔞
    (DoubleBlock.positiveUnitStep L m (levelDepth K k) ν) L ω hω.1.le
    (fun p hp => (hU.2 p (fun z hz => hs1 z (hp hz))).le)
  rw [wordHolonomy, wordHolonomy, hp1, hp2, hpath', pathHolonomy_concat_eq_mul,
    pathHolonomy_concat_eq_mul] at hrun
  have hxb : x + L • unitStep L m (levelDepth K k) ν ∈
      sitesInBlock (levelDepth K k) c.target := hx'
  obtain ⟨ha, hGa⟩ := hmeans U hU c.source (by simp) x hx
  obtain ⟨hb, hGb⟩ := hmeans U hU c.target (by simp) _ hxb
  have hW : crossingDefect U c x = meanContourHolonomy U c.source x *
      pathHolonomy U (axialPath x (x + L • unitStep L m (levelDepth K k) ν)) *
      (meanContourHolonomy U c.target (x + L • unitStep L m (levelDepth K k) ν))⁻¹ *
      (parallelTransport U c)⁻¹ := by
    rw [crossingDefect, crossingPath, hxeq]
  rw [hW]
  have hbound := norm_crossing_sub_one_le ha hb (pathHolonomy_mem_specialUnitary hreal _)
    (pathHolonomy_mem_specialUnitary hreal _) (hGa σ) (hGb σ') hrun
  have hcount := nonParallelStepCount_le hP hL hm hk c ν hx σ 𝔞 hpath
  have hhalf : 2 * centreToFaceSteps L = (L : ℤ) - 1 := by
    obtain ⟨t, ht⟩ := hL.1
    unfold centreToFaceSteps
    omega
  have hcnt : 2 * (nonParallelStepCount 𝔞
      (DoubleBlock.positiveUnitStep L m (levelDepth K k) ν) : ℝ) ≤ 3 * ((L : ℝ) - 1) := by
    have hz : 2 * (nonParallelStepCount 𝔞
        (DoubleBlock.positiveUnitStep L m (levelDepth K k) ν) : ℤ) ≤ 3 * ((L : ℤ) - 1) := by
      omega
    exact_mod_cast hz
  refine lt_of_le_of_lt hbound ?_
  have hL' : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  have hω₂ := radius_mul_sq_le hL.2 hω
  have hω0 := hω.1
  have hrunle : (L : ℝ) * (nonParallelStepCount 𝔞
      (DoubleBlock.positiveUnitStep L m (levelDepth K k) ν) : ℝ) * ω ≤
      (L : ℝ) * (3 / 2 * ((L : ℝ) - 1)) * ω := by
    have : (nonParallelStepCount 𝔞
        (DoubleBlock.positiveUnitStep L m (levelDepth K k) ν) : ℝ) ≤
        3 / 2 * ((L : ℝ) - 1) := by linarith
    gcongr
  have hE : 12 * ((L : ℝ) - 1) ^ 2 + (L : ℝ) * (3 / 2 * ((L : ℝ) - 1)) <
      27 / 2 * (L : ℝ) ^ 2 := by
    nlinarith
  have := mul_lt_mul_of_pos_right hE hω0
  nlinarith
theorem smallSetInComplexDomain_of (hM : ComplexLogMeanOfSmallFamilies)
    (hS : ContourFamilySpread) (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : k < K) {ω : ℝ}
    (hω : ω ∈ Ioc (0 : ℝ) (averagingRadiusCap L)) (c : BondAtLevel L m K (k + 1))
    (hpos : c.IsPositivelyOriented) (hnear : ExplicitRadii.DefectsNearOne ω k c) :
    ExplicitRadii.SmallSetInComplexDomain ω k c := by
  intro U hU
  obtain ⟨ν, hν⟩ := hpos
  have hdiam : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y,
        ComplexMatrix2.familyDiameter (contourHolonomies U y x) < centreOfMassDiameter := by
    intro y hy x hx
    have := (contourDiameterBounds_of hS hL hm hk hω c U hU y hy x hx).2.2
    unfold centreOfMassDiameter
    exact this
  have hel : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      complexCrossingDefect U c x = crossingDefect U c x := by
    intro x hx
    obtain ⟨-, hx'⟩ := shiftAcross_facts hP hL hm hk c hν hx
    have h₁ := (contourMean_facts hM hS hL hm hk hω c hU (y := c.source) (by simp) hx).2.2.1
    have h₂ := (contourMean_facts hM hS hL hm hk hω c hU (y := c.target) (by simp) hx').2.2.1
    rw [complexCrossingDefect, crossingDefect, h₁, h₂]
  refine ⟨⟨⟨⟨fun b _ => specialUnitary_mem_complexGaugeGroup (hU.1.1 b (mem_univ _)),
    fun b _ => hU.1.2 b (mem_univ _)⟩, fun x hx => hdiam _ (by simp) x hx,
    fun x hx => hdiam _ (by simp) x hx⟩, fun x hx => ?_⟩, ?_⟩
  · rw [hel x hx]
    exact lt_trans (hnear ⟨ν, hν⟩ U hU x hx) (by norm_num)
  · have hsum : ∑ᶠ x ∈ sitesInBlock (levelDepth K k) c.source,
          ComplexMatrix2.logSeries (complexCrossingDefect U c x) =
        ∑ᶠ x ∈ sitesInBlock (levelDepth K k) c.source,
          ComplexMatrix2.logSeries (crossingDefect U c x) :=
      finsum_mem_congr rfl fun x hx => by rw [hel x hx]
    rw [complexBlockAverageOnPositive, regularAverageValue, hsum]
theorem isOpen_smallPlaquetteFields_of {ω : ℝ} (c : BondAtLevel L m K (k + 1))
    (hopen : IsOpen[gaugeFieldsAtLevelTopology L m K k]
      (Subtype.val ⁻¹' (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)))) :
    ExplicitRadii.isOpen_smallPlaquetteFields ω k c := by
  have hcont : Continuous (gaugeFieldAtLevelValues (L := L) (m := m) (K := K) (k := k)) :=
    continuous_pi fun b => Continuous.subtype_mk
      ((continuous_apply b.1).comp continuous_subtype_val) _
  have hle : (inferInstance : TopologicalSpace (gaugeFieldsAtLevel L m K k)) ≤
      gaugeFieldsAtLevelTopology L m K k := continuous_iff_le_induced.mp hcont
  exact hle _ hopen
end Bond
theorem holds (hM : ComplexLogMeanOfSmallFamilies)
    (hE : SmallRadius.EverySmallRadiusSuffices)
    (hS : ContourFamilySpread) (hC : DoubleBlock.DoubleBlockContoursStatement)
    (hP : BlockPaths.Statement)
    (hR : HolonomyCommutesWithEqualSteps)
    (hA : BlockAverageRealAnalyticOnSmallFields) : ExplicitRadii.Holds := by
  have hconcl : ∀ s : Conventions.StandingParameters,
      ∀ ω ∈ Ioc (0 : ℝ) (averagingRadiusCap s.L), ∀ k,
      k < (s.K : ℕ) → ∀ c : BondAtLevel s.L s.m s.K (k + 1),
      SymmetrisedDomainPropertiesAtBond ω k c := by
    intro s ω hω k hk c
    have hc := hE s ω hω k hk c
    refine ⟨fun U hU y hy x hx => (hc.contourMean_spec U hU y hy x hx).1, fun inst =>
      ⟨fun U hU => hU.1, fun y hy x hx =>
        ⟨fun U hU => (hc.contourMean_spec U hU y hy x hx).1, ?_⟩⟩, fun hp U hU x hx => ?_⟩
    · exact isRealAnalyticBetween_pair (hc.realAnalytic_contourMean inst y hy x hx).1
        (hc.realAnalytic_contourMean inst y hy x hx).2
    · exact lt_trans (hc.crossingDefect_near hp U hU x hx).2 (by norm_num)
  have hnear : ∀ s : Conventions.StandingParameters,
      ∀ ω ∈ Ioc (0 : ℝ) (averagingRadiusCap s.L), ∀ k,
      k < (s.K : ℕ) → ∀ c : BondAtLevel s.L s.m s.K (k + 1),
      ExplicitRadii.DefectsNearOne ω k c := by
    intro s ω hω k hk c
    exact defectsNearOne_of hC hP hR s.isAdmissible s.m.pos hk hω c
      fun U hU y hy x hx =>
        let h := contourMean_facts hM hS s.isAdmissible s.m.pos hk hω c hU hy hx
        ⟨h.2.1, h.2.2.2⟩
  refine ⟨?_, fun s s' h => by rw [h], fun s => ?_, fun ω s hω => ?_⟩
  · refine ⟨by norm_num, by norm_num, by norm_num, rfl, rfl, hM.2.2.2.1⟩
  · refine ⟨averagingRadiusCap_mem s.isAdmissible.2,
      fun ω hω k hk c => contourDiameterBounds_of hS s.isAdmissible s.m.pos hk hω c,
      (hM.2.2.2.2 s).2, fun ω hω k hk c => ?_, fun ω hω k hk c hp U hU => ?_,
      fun ω hω k hk c hp =>
        smallSetInComplexDomain_of hM hS hP s.isAdmissible s.m.pos hk hω c hp
          (hnear s ω hω k hk c),
      fun ω hω k hk c hp inst => hA s ω hω k hk c hp inst⟩
    · have hc := hE s ω hω k hk c
      have hb := hconcl s ω hω k hk c
      exact ⟨hb, isOpen_smallPlaquetteFields_of c (hc.isOpen_smallPlaquetteFields ω
          ⟨hω.1, hω.2.trans (averagingRadiusCap_mem s.isAdmissible.2).2⟩),
        hb.dependAnalytically,
        fun U hU y hy x hx σ => (contourMean_facts hM hS s.isAdmissible s.m.pos hk hω c
          hU hy hx).2.2.2 σ, hnear s ω hω k hk c⟩
    · refine ⟨hU.2, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
      · exact (contourMean_facts hM hS s.isAdmissible s.m.pos hk hω c hU
          (y := c.source) (by simp) hx).1
      · exact (contourMean_facts hM hS s.isAdmissible s.m.pos hk hω c hU
          (y := c.target) (by simp) hx).1
      · exact lt_trans (hnear s ω hω k hk c hp U hU x hx) (by norm_num)
  · have hb := averagingRadiusCap_mem s.isAdmissible.2
    exact ⟨⟨hω.1, hω.2.trans hb.2⟩, hω.2, fun k hk c => hconcl s _ hω k hk c⟩
end Averaging.ExplicitRadiiProof
end YangMills.Construction
end
