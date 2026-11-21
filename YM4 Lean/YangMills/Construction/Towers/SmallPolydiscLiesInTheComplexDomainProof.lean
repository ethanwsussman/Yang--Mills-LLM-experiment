import YangMills.Construction.Lattice.LengthsOfThePathsOfADoubleBlock
import YangMills.Construction.Towers.BlocksOfATower
import YangMills.Construction.Towers.ComplexAverageLiesInTheComplexGroupProof
import YangMills.Construction.Towers.SmallPolydiscLiesInTheComplexDomain
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
open Matrices
open PeriodicLattice (complexGaugeGroup)
private theorem mul_sub_one_le {X Y : ComplexMatrix2} {a b : ℝ}
    (hX : ComplexMatrix2.operatorNorm (X - 1) ≤ a)
    (hY : ComplexMatrix2.operatorNorm (Y - 1) ≤ b) :
    ComplexMatrix2.operatorNorm (X * Y - 1) ≤ a + b + a * b := by
  have hdecomp : X * Y - 1 = (X - 1) * (Y - 1) + (X - 1) + (Y - 1) := by noncomm_ring
  have ha : 0 ≤ a := (norm_nonneg _).trans hX
  have hprod : ‖(X - 1) * (Y - 1)‖ ≤ a * b :=
    (norm_mul_le _ _).trans (mul_le_mul hX hY (norm_nonneg _) ha)
  have hsum : ‖(X - 1) * (Y - 1) + (X - 1) + (Y - 1)‖ ≤
      ‖(X - 1) * (Y - 1)‖ + ‖X - 1‖ + ‖Y - 1‖ := norm_add₃_le
  show ‖X * Y - 1‖ ≤ a + b + a * b
  rw [hdecomp]
  linarith
private theorem list_prod_sub_one_le {r : ℝ} (l : List ComplexMatrix2)
    (h : ∀ X ∈ l, ComplexMatrix2.operatorNorm (X - 1) ≤ r) :
    ComplexMatrix2.operatorNorm (l.prod - 1) ≤ (1 + r) ^ l.length - 1 := by
  induction l with
  | nil => simp
  | cons X l ih =>
    rw [List.prod_cons, List.length_cons, pow_succ]
    have htail := ih fun Y hY => h Y (List.mem_cons_of_mem _ hY)
    refine (mul_sub_one_le (h X List.mem_cons_self) htail).trans (le_of_eq ?_)
    ring
private theorem inv_sub_one_le (hE : ComplexMatrix2.ExpLogEstimates) {X : ComplexMatrix2} {a : ℝ}
    (hX : ComplexMatrix2.operatorNorm (X - 1) ≤ a) (ha : a ≤ 1 / 2) :
    ComplexMatrix2.operatorNorm (X⁻¹ - 1) ≤ 2 * a := by
  have hlt : ComplexMatrix2.operatorNorm (X - 1) < 1 := by linarith
  have hinv := (hE.2.2.2.1 (X - 1) hlt).2.2.2.1
  rw [add_sub_cancel] at hinv
  refine hinv.trans ?_
  have hnn : 0 ≤ ComplexMatrix2.operatorNorm (X - 1) := norm_nonneg _
  rw [div_le_iff₀ (by linarith)]
  nlinarith
private theorem logSeries_le_of_near (hE : ComplexMatrix2.ExpLogEstimates) {X : ComplexMatrix2}
    (hX : ComplexMatrix2.operatorNorm (X - 1) ≤ 1 / 16) :
    ComplexMatrix2.operatorNorm (ComplexMatrix2.logSeries X) ≤ 1 / 10 := by
  have hlt : ComplexMatrix2.operatorNorm (X - 1) < 1 := by linarith
  have hlog := hE.2.2.2.1 (X - 1) hlt
  have hchain := hlog.1.trans hlog.2.1
  rw [add_sub_cancel] at hchain
  refine hchain.trans ?_
  rw [div_le_iff₀ (by linarith)]
  linarith
private theorem exp_one_tenth_sub_one_le : Real.exp (1 / 10) - 1 ≤ 1 / 9 := by
  have hlow := Real.add_one_le_exp (-(1 / 10 : ℝ))
  have hprod : Real.exp (1 / 10) * Real.exp (-(1 / 10 : ℝ)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (1 / 10 : ℝ)
  nlinarith
private theorem exists_small_radius (N : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ (1 + ρ) ^ N - 1 ≤ 1 / 2000 := by
  have hcont : ContinuousAt (fun r : ℝ => (1 + r) ^ N - 1) 0 := by fun_prop
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hcont (1 / 2000) (by norm_num)
  have hpos : 0 < min (δ / 2) 1 := lt_min (by linarith) one_pos
  refine ⟨min (δ / 2) 1, hpos, min_le_right _ _, ?_⟩
  have hdist : dist (min (δ / 2) 1) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    exact (min_le_left _ _).trans_lt (by linarith)
  have hval := hball hdist
  simp only [add_zero, one_pow, sub_self, Real.dist_eq, sub_zero] at hval
  exact (le_abs_self _).trans hval.le
private theorem complexLogMean_equiv_reindex {ι : Type} [Fintype ι] {n : ℕ} (e : ι ≃ Fin n)
    (V : ι → ComplexMatrix2) :
    PeriodicLattice.complexLogMean V =
      PeriodicLattice.complexLogMean fun i : Fin n => V (e.symm i) := by
  unfold PeriodicLattice.complexLogMean
  congr 1
  funext W
  apply propext
  constructor
  · rintro ⟨⟨h₁, h₂, h₃⟩, i, hi⟩
    refine ⟨⟨h₁, fun i => h₂ _, ?_⟩, e i, by simpa using hi⟩
    rw [← h₃]
    exact Equiv.sum_comp e.symm fun i => ComplexMatrix2.logSeries (V i * W⁻¹)
  · rintro ⟨⟨h₁, h₂, h₃⟩, i, hi⟩
    refine ⟨⟨h₁, fun i => by simpa using h₂ (e i), ?_⟩, e.symm i, hi⟩
    rw [← h₃]
    exact (Equiv.sum_comp e.symm fun i => ComplexMatrix2.logSeries (V i * W⁻¹)).symm
private theorem diameter_and_mean_near_one (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hE : ComplexMatrix2.ExpLogEstimates) {ι : Type} [Fintype ι] [Nonempty ι]
    (V : ι → ComplexMatrix2) (hV : ∀ i, V i ∈ complexGaugeGroup)
    (hn : ∀ i, ComplexMatrix2.operatorNorm (V i - 1) ≤ 1 / 2000) :
    ComplexMatrix2.familyDiameter V < Averaging.centreOfMassDiameter ∧
      ComplexMatrix2.operatorNorm (PeriodicLattice.complexLogMean V - 1) ≤ 34 / 2000 := by
  have hdle : ComplexMatrix2.familyDiameter V ≤ 4 / 2000 := by
    refine Real.iSup_le (fun p => ?_) (by norm_num)
    refine (mul_sub_one_le (hn p.1) (inv_sub_one_le hE (hn p.2) (by norm_num))).trans ?_
    norm_num
  have hd : ComplexMatrix2.familyDiameter V < Averaging.centreOfMassDiameter := by
    unfold Averaging.centreOfMassDiameter
    linarith
  refine ⟨hd, ?_⟩
  let e := Fintype.equivFin ι
  have hc : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hF := hM.2.2.2.1 (Fintype.card ι) hc
  let U : Fin (Fintype.card ι) → ComplexMatrix2 := fun i => V (e.symm i)
  have hdiam : ComplexMatrix2.familyDiameter U = ComplexMatrix2.familyDiameter V :=
    (Equiv.prodCongr e.symm e.symm).iSup_comp
      (g := fun p : ι × ι => ComplexMatrix2.operatorNorm (V p.1 * (V p.2)⁻¹ - 1))
  have hs : U ∈ Averaging.smallComplexFamilies (Fintype.card ι) :=
    ⟨fun i => hV _, by rw [hdiam]; exact hd⟩
  have hmean : PeriodicLattice.complexLogMean V = PeriodicLattice.complexLogMean U :=
    complexLogMean_equiv_reindex e V
  obtain ⟨W₀, hW₀, -⟩ := hF.existsUnique U hs
  have hspec : Averaging.IsNearComplexLogMean U (PeriodicLattice.complexLogMean U) :=
    Classical.epsilon_spec (p := fun W => ComplexMatrix2.IsLogMean complexGaugeGroup U W ∧
      ∃ i, ComplexMatrix2.operatorNorm (U i * W⁻¹ - 1) ≤ PeriodicLattice.complexMeanTolerance)
      ⟨W₀, hW₀⟩
  rw [hmean]
  set W := PeriodicLattice.complexLogMean U with hWdef
  have hdet : W.det = 1 := hspec.1.1
  obtain ⟨i⟩ : Nonempty (Fin (Fintype.card ι)) := ⟨⟨0, hc⟩⟩
  have hsp : ComplexMatrix2.operatorNorm (U i * W⁻¹ - 1) ≤ 16 / 2000 := by
    refine (hF.spread U hs i).trans ?_
    rw [hdiam]
    linarith
  have hUdet : (U i).det = 1 := hV _
  have hW : W = (U i * W⁻¹)⁻¹ * U i := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv W (by rw [hdet]; exact isUnit_one),
      mul_assoc, Matrix.nonsing_inv_mul _ (by rw [hUdet]; exact isUnit_one), mul_one]
  rw [hW]
  refine (mul_sub_one_le (inv_sub_one_le hE hsp (by norm_num)) (hn _)).trans ?_
  norm_num
private theorem weight_smul_finsum_le {L : ℕ} (hL : 0 < L) {X : Type} {s : Set X}
    (f : X → ComplexMatrix2) {B : ℝ}
    (hB : 0 ≤ B) (hs : s.Finite) (hcard : s.ncard ≤ L ^ 4) (hf : ∀ x ∈ s, ‖f x‖ ≤ B) :
    ‖PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ s, f x‖ ≤ B := by
  have hw : ‖PeriodicLattice.inverseFourthPowerWeight L‖ = ((L : ℝ) ^ 4)⁻¹ := by
    unfold PeriodicLattice.inverseFourthPowerWeight
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), zpow_neg]
    norm_cast
  have hsum : ‖∑ᶠ x ∈ s, f x‖ ≤ (L : ℝ) ^ 4 * B := by
    rw [finsum_mem_eq_finite_toFinset_sum f hs]
    have hterm : ‖∑ x ∈ hs.toFinset, f x‖ ≤ ∑ _x ∈ hs.toFinset, B :=
      norm_sum_le_of_le _ fun x hx => hf x (hs.mem_toFinset.1 hx)
    rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card s hs] at hterm
    have hcardr : (s.ncard : ℝ) ≤ (L : ℝ) ^ 4 := by exact_mod_cast hcard
    exact hterm.trans (mul_le_mul_of_nonneg_right hcardr hB)
  rw [norm_smul, hw]
  calc ((L : ℝ) ^ 4)⁻¹ * ‖∑ᶠ x ∈ s, f x‖ ≤ ((L : ℝ) ^ 4)⁻¹ * ((L : ℝ) ^ 4 * B) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = B := by field_simp
section FiniteSide
open PeriodicLattice
variable {L m K n : ℕ}
private theorem prod_map_mem_complexGaugeGroup {β : Type} (U : β → ComplexMatrix2) (Γ : List β)
    (h : ∀ b ∈ Γ, U b ∈ complexGaugeGroup) : (Γ.map U).prod ∈ complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.ComplexMeanMembership.map_prod_mem_gaugeGroup <;> assumption
private theorem coarse_site_self_mem (hL : 0 < L) (y : SiteAtLevel L m K (n + 1)) :
    ((y.toSublattice (levelDepth K n) : SiteAtLevel L m K n) : FourTorus L m) = y ∧
      y.toSublattice (levelDepth K n) ∈ sitesInBlock (levelDepth K n) y := by apply _root_.YangMills.SharedProofs.p56939 <;> assumption
private theorem axialPath_eq_crossingPath (hL : 0 < L) (c : BondAtLevel L m K (n + 1)) :
    axialPath (c.source.toSublattice (levelDepth K n)) (c.target.toSublattice (levelDepth K n)) =
      crossingPath c (c.source.toSublattice (levelDepth K n)) := by apply _root_.YangMills.SharedProofs.p11419 <;> assumption
private theorem sitesInBlock_finite_card {y : SiteAtLevel L m K (n + 1)} (hL : 0 < L)
    (hcard : (unitBlock y).ncard = L ^ 4) :
    (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)).Finite ∧
      (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)).ncard ≤ L ^ 4 := by
  have hfin : (unitBlock y).Finite := Set.finite_of_ncard_pos (by rw [hcard]; positivity)
  have hsub : (Subtype.val '' (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n))) ⊆
      unitBlock y := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  refine ⟨Set.Finite.of_finite_image (hfin.subset hsub) Subtype.val_injective.injOn, ?_⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, ← hcard]
  exact Set.ncard_le_ncard hsub hfin
private theorem bounds_on_polydisc (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hD : DoubleBlockStructure.Statement)
    (hP : DoubleBlockPathLengths)
    (hB : Tower.BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K) {ρ : ℝ}
    (hρ₀ : 0 < ρ) (hρ : (1 + ρ) ^ (2 * L) - 1 ≤ 1 / 2000) (c : BondAtLevel L m K (n + 1))
    (hc : c.IsPositivelyOriented)
    (V : BondAtLevel L m K n → ComplexMatrix2) (hV : V ∈ Tower.nearIdentityPolydisc ρ c) :
    V ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K n → ComplexMatrix2)) ∧
      ComplexMatrix2.operatorNorm (complexBlockAverage V c - 1) < 1 / 2 ∧
      ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
        ∀ x ∈ sitesInBlock (levelDepth K n) y,
          ComplexMatrix2.operatorNorm (complexMeanContourHolonomy V y x - 1) < 1 / 2 := by
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨-, hContours, hStraight, -, -⟩ := hD L m K n hL hm hn c
  have hLengths := hP L m K n hL hm hn
  obtain ⟨hconf, hsmall⟩ := hV
  have hhol : ∀ Γ : List (BondAtLevel L m K n), Γ.length ≤ 2 * L →
      (∀ b ∈ Γ, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))) →
      ComplexMatrix2.operatorNorm (pathHolonomy V Γ - 1) ≤ 1 / 2000 := by
    intro Γ hl hb
    have hprod := list_prod_sub_one_le (Γ.map V) fun X hX => by
      obtain ⟨b, hb', rfl⟩ := List.mem_map.1 hX
      exact (hsmall b (hb b hb')).le
    rw [List.length_map] at hprod
    have hpow : (1 + ρ) ^ Γ.length ≤ (1 + ρ) ^ (2 * L) :=
      pow_le_pow_right₀ (by linarith) hl
    exact hprod.trans (by linarith)
  have hvalues : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
      ∀ x ∈ sitesInBlock (levelDepth K n) y, ∀ σ, contourHolonomies V y x σ ∈ complexGaugeGroup :=
    fun y hy x hx σ => prod_map_mem_complexGaugeGroup V _ fun b hb =>
      hconf.1 b ((hContours y hy x hx _ ⟨σ, rfl⟩).2 b hb)
  have hnear : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
      ∀ x ∈ sitesInBlock (levelDepth K n) y, ∀ σ,
        ComplexMatrix2.operatorNorm (contourHolonomies V y x σ - 1) ≤ 1 / 2000 :=
    fun y hy x hx σ => hhol _ ((hLengths.contour y x hx σ).trans (by omega))
      (hContours y hy x hx _ ⟨σ, rfl⟩).2
  have hmean : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
        ComplexMatrix2.familyDiameter (contourHolonomies V y x) < Averaging.centreOfMassDiameter ∧
          ComplexMatrix2.operatorNorm (complexMeanContourHolonomy V y x - 1) ≤ 34 / 2000 := by
    intro y hy x hx
    have : Nonempty (AxisOrdering y x) := ⟨(offsetAxes y x).equivFin.symm⟩
    exact diameter_and_mean_near_one hM hE _ (hvalues y hy x hx) (hnear y hy x hx)
  have hcross : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      ComplexMatrix2.operatorNorm (pathHolonomy V (crossingPath c x) - 1) ≤ 1 / 2000 :=
    fun x hx => hhol _ (by rw [(hStraight.1 x hx).2.2.1]; omega) (hStraight.1 x hx).2.2.2.2
  have htr : ComplexMatrix2.operatorNorm (parallelTransport V c - 1) ≤ 1 / 2000 := by
    unfold parallelTransport
    rw [axialPath_eq_crossingPath hL0 c]
    exact hcross _ (coarse_site_self_mem hL0 c.source).2
  have hW : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      ComplexMatrix2.operatorNorm (complexCrossingDefect V c x - 1) ≤ 1 / 16 := by
    intro x hx
    have a₁ := mul_sub_one_le (hmean _ (Or.inl rfl) x hx).2 (hcross x hx)
    have a₂ := mul_sub_one_le a₁
      (inv_sub_one_le hE (hmean _ (Or.inr rfl) _ (hStraight.1 x hx).1).2 (by norm_num))
    have a₃ := mul_sub_one_le a₂ (inv_sub_one_le hE htr (by norm_num))
    exact a₃.trans (by norm_num)
  refine ⟨⟨⟨hconf, fun x hx => (hmean _ (Or.inl rfl) x hx).1,
    fun x hx => (hmean _ (Or.inr rfl) x hx).1⟩, fun x hx => (hW x hx).trans_lt (by norm_num)⟩,
    ?_, ?_⟩
  · have hval : complexBlockAverage V c = complexBlockAverageOnPositive V c := if_pos hc
    have hblock := (hB L K (n + 1) hL (by omega) (by omega) (by omega)).1 m hm
    obtain ⟨hfin, hcard⟩ := sitesInBlock_finite_card (n := n) hL0 (hblock.1 c.source).2.2.1
    have hZ := weight_smul_finsum_le hL0
      (fun x => ComplexMatrix2.logSeries (complexCrossingDefect V c x))
      (by norm_num : (0 : ℝ) ≤ 1 / 10) hfin hcard fun x hx => logSeries_le_of_near hE (hW x hx)
    rw [hval]
    unfold complexBlockAverageOnPositive
    have hexp : ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp (inverseFourthPowerWeight L •
        ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
          ComplexMatrix2.logSeries (complexCrossingDefect V c x)) - 1) ≤ 1 / 9 :=
      (hE.1 _).2.trans (by
        have := Real.exp_le_exp.2 hZ
        have := exp_one_tenth_sub_one_le
        linarith)
    exact (mul_sub_one_le hexp htr).trans_lt (by norm_num)
  · intro y hy x hx
    have hy' : y = c.source ∨ y = c.target := by simpa using hy
    exact (hmean y hy' x hx).2.trans_lt (by norm_num)
end FiniteSide
theorem polydiscInComplexDomain_holds (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hD : PeriodicLattice.DoubleBlockStructure.Statement)
    (hP : PeriodicLattice.DoubleBlockPathLengths)
    (hB : Tower.BlockStructure) :
    Tower.PolydiscInComplexDomain := fun L hL => by
  obtain ⟨ρ, h₀, h₁, hρ⟩ := exists_small_radius (2 * L)
  refine ⟨ρ, h₀, h₁, fun n k j hn hj c hc => ⟨fun V hV => ?_, fun V hV => ?_, fun V hV => ?_⟩⟩
  · exact (bounds_on_polydisc hM hE hD hP hB hL hn hj h₀ hρ c hc V hV).1
  · exact (bounds_on_polydisc hM hE hD hP hB hL hn hj h₀ hρ c hc V hV).2.1
  · exact (bounds_on_polydisc hM hE hD hP hB hL hn hj h₀ hρ c hc V hV).2.2
end YangMills.Construction.Tower
end
