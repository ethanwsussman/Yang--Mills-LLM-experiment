import YangMills.Construction.Lattice.BlockPartitionProof
import YangMills.Construction.Lattice.IsometryCarriesTheObjectsOfTheAverageProof
import YangMills.Construction.Lattice.TreeOfALocalisationDomainProof
import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATowerProof
import YangMills.Construction.Towers.ClosedFormsOnATorus
import YangMills.Construction.Towers.ClosedFormsUnderTheLinearAverage
import YangMills.Construction.Towers.RelationsOfTheLinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice.ClosedFormsSmoothing
section Coordinates
variable {L m : ℕ} {j j' : ℤ}
theorem pointOnAxis_zero (μ : Fin 4) : pointOnAxis L m μ 0 = 0 := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCells.pointOnAxis_zero <;> assumption
theorem pointOnAxis_add (μ : Fin 4) (s t : ℝ) :
    pointOnAxis L m μ (s + t) = pointOnAxis L m μ s + pointOnAxis L m μ t := by apply _root_.YangMills.Construction.TorusBound.LocalisationDomainTree.pointOnAxis_add <;> assumption
theorem coe_sum_zsmul_unitStep (p : Fin 4 → ℤ) :
    ((∑ μ, p μ • unitStep L m j μ : Site L m j) : FourTorus L m) =
      ∑ μ, pointOnAxis L m μ ((p μ : ℝ) * meshSize L j) := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.coe_sum_zsmul_unitStep <;> assumption
theorem meshSize_eq_mul_succ (hL : 0 < L) (j : ℤ) :
    meshSize L j = (L : ℝ) * meshSize L (j + 1) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryImages.meshSize_eq_mul_succ <;> assumption
theorem exists_eq_mul_add_balanced {l : ℤ} (hodd : Odd l) (hpos : 0 < l) (z : ℤ) :
    ∃ q r : ℤ, z = l * q + r ∧ 2 * |r| ≤ l - 1 := by apply _root_.YangMills.Construction.PeriodicLattice.BlockPartition.exists_eq_mul_add_centered <;> assumption
theorem exists_blockOffset (hodd : Odd L) (hL : 0 < L) (hc : SublatticeCoordinates L m j')
    (hj : j' = j + 1) (x : Site L m j') :
    ∃ (y : Site L m j) (ν : Fin 4 → ℤ), IsBlockOffset y x ν := by
  subst hj
  obtain ⟨-, -, -, hgen, -⟩ := hc
  obtain ⟨n, hn⟩ := hgen 0 x
  have hoddZ : Odd (L : ℤ) := by exact_mod_cast hodd
  choose q r hqr hr using fun μ => exists_eq_mul_add_balanced hoddZ (by exact_mod_cast hL) (n μ)
  refine ⟨∑ μ, q μ • unitStep L m j μ, r, ?_, hr⟩
  have hx : (x : FourTorus L m) = ∑ μ, pointOnAxis L m μ ((n μ : ℝ) * meshSize L (j + 1)) := by
    rw [hn]
    simp only [offsetSite, zero_add]
    exact coe_sum_zsmul_unitStep n
  rw [hx, coe_sum_zsmul_unitStep, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [sub_eq_iff_eq_add, ← pointOnAxis_add]
  congr 1
  rw [hqr μ, meshSize_eq_mul_succ hL j]
  push_cast
  ring
theorem blockOffset_unique (hc : SublatticeCoordinates L m j) (hc' : SublatticeCoordinates L m j')
    (hL : 0 < L) (hdvd : (L : ℤ) ∣ ((2 * halfPeriod L m j' : ℕ) : ℤ)) (hj : j' = j + 1)
    {y y' : Site L m j} {x : Site L m j'} {ν ν' : Fin 4 → ℤ}
    (h : IsBlockOffset y x ν) (h' : IsBlockOffset y' x ν') : y = y' ∧ ν = ν' := by
  subst hj
  obtain ⟨-, -, -, hgen, -⟩ := hc
  obtain ⟨-, -, -, -, hmod, -⟩ := hc'
  obtain ⟨p, hp⟩ := hgen y y'
  have hy' : (y' : FourTorus L m) = y + ∑ μ, pointOnAxis L m μ ((p μ : ℝ) * meshSize L j) := by
    rw [hp]
    simp only [offsetSite]
    rw [AddSubgroup.coe_add, coe_sum_zsmul_unitStep]
  have hsum : ∑ μ, pointOnAxis L m μ ((ν μ : ℝ) * meshSize L (j + 1)) =
      ∑ μ, pointOnAxis L m μ (((ν' μ + (L : ℤ) * p μ : ℤ) : ℝ) * meshSize L (j + 1)) := by
    have e : ∀ μ, pointOnAxis L m μ (((ν' μ + (L : ℤ) * p μ : ℤ) : ℝ) * meshSize L (j + 1)) =
        pointOnAxis L m μ ((ν' μ : ℝ) * meshSize L (j + 1)) +
          pointOnAxis L m μ ((p μ : ℝ) * meshSize L j) := by
      intro μ
      rw [← pointOnAxis_add, meshSize_eq_mul_succ hL j]
      congr 1
      push_cast
      ring
    simp only [e, Finset.sum_add_distrib]
    have h1 := h.1
    have h2 := h'.1
    rw [hy'] at h2
    rw [← h1, ← h2]
    abel
  have heq : offsetSite (0 : Site L m (j + 1)) ν =
      offsetSite 0 fun μ => ν' μ + (L : ℤ) * p μ := by
    refine Subtype.ext ?_
    simp only [offsetSite, zero_add]
    rw [coe_sum_zsmul_unitStep, coe_sum_zsmul_unitStep]
    exact hsum
  have hm := (hmod 0 _ _).1 heq
  have hν : ν = ν' := by
    funext μ
    have hd : (L : ℤ) ∣ ν μ - ν' μ := by
      have e := hdvd.trans (hm μ).dvd
      have e' : ν μ - ν' μ = (L : ℤ) * p μ - (ν' μ + (L : ℤ) * p μ - ν μ) := by ring
      rw [e']
      exact dvd_sub (dvd_mul_right _ _) e
    have hlt : |ν μ - ν' μ| < (L : ℤ) := by
      have a1 := h.2 μ
      have a2 := h'.2 μ
      have a3 := abs_sub (ν μ) (ν' μ)
      have hLpos : (0 : ℤ) < L := by exact_mod_cast hL
      have a4 := abs_nonneg (ν μ)
      have a5 := abs_nonneg (ν' μ)
      linarith
    have := Int.eq_zero_of_abs_lt_dvd hd hlt
    linarith
  subst hν
  refine ⟨Subtype.ext ?_, rfl⟩
  exact (sub_right_inj.mp (h.1.trans h'.1.symm))
theorem mem_sitesInBlock_iff (hB : RefinedBlockCoordinates L m j 1) (hj : j' = j + 1)
    (y : Site L m j) (x : Site L m j') :
    x ∈ sitesInBlock j' y ↔ ∃ ν, IsBlockOffset y x ν := by
  subst hj
  obtain ⟨hy, hset, -⟩ := hB y
  have hcoe : ((y.toSublattice (j + ((1 : ℕ) : ℤ)) : Site L m (j + ((1 : ℕ) : ℤ))) :
      FourTorus L m) = y :=
    Classical.epsilon_spec (p := fun x : Site L m (j + ((1 : ℕ) : ℤ)) => (x : FourTorus L m) = y)
      ⟨⟨y, hy⟩, rfl⟩
  have hsite : ∀ p : Fin 4 → ℤ,
      ((refinedOffsetSite 1 y p : Site L m (j + ((1 : ℕ) : ℤ))) : FourTorus L m) =
        y + ∑ μ, pointOnAxis L m μ ((p μ : ℝ) * meshSize L (j + 1)) := by
    intro p
    simp only [refinedOffsetSite, offsetSite]
    rw [AddSubgroup.coe_add, hcoe, coe_sum_zsmul_unitStep, Nat.cast_one]
  show (x : FourTorus L m) ∈ refinedBlock 1 y ↔ _
  rw [hset]
  constructor
  · rintro ⟨p, hp, hx⟩
    refine ⟨p, ?_, fun μ => by simpa [blockOffsets] using hp μ⟩
    simp only at hx
    rw [← hx, hsite]
    abel
  · rintro ⟨ν, hd, hb⟩
    refine ⟨ν, fun μ => by simpa [blockOffsets] using hb μ, ?_⟩
    simp only
    rw [hsite, ← hd]
    abel
theorem sitesInBlock_finite (hL : 0 < L) (hB : RefinedBlockCoordinates L m j 1) (y : Site L m j) :
    (sitesInBlock j' y).Finite := by
  obtain ⟨-, -, -, hcard, -⟩ := hB y
  have hfin : (refinedBlock 1 y).Finite :=
    Set.finite_of_ncard_pos (by rw [hcard]; exact pow_pos hL _)
  exact Set.Finite.preimage (f := Subtype.val) Subtype.val_injective.injOn hfin
theorem dvd_halfPeriod_and_one_lt (hL : 13 ≤ L) (h : 0 < (m : ℤ) + j) :
    L ∣ halfPeriod L m j ∧ 1 < halfPeriod L m j := by
  have he : ((m : ℤ) + j).toNat ≠ 0 := by omega
  exact ⟨dvd_pow_self L he, Nat.one_lt_pow he (by omega)⟩
theorem unitStep_injective_and_ne_neg (hc : SublatticeCoordinates L m j)
    (h2 : 1 < halfPeriod L m j) :
    (∀ μ ν, unitStep L m j μ = unitStep L m j ν → μ = ν) ∧
      ∀ μ ν, unitStep L m j μ ≠ -unitStep L m j ν := by
  obtain ⟨-, -, -, -, hmod, -⟩ := hc
  have hs : ∀ (μ : Fin 4) (t : ℤ), t • unitStep L m j μ = offsetSite 0 (Pi.single μ t) := by
    intro μ t
    simp [offsetSite, Pi.single_apply, ite_smul]
  have hN : (2 : ℤ) < ((2 * halfPeriod L m j : ℕ) : ℤ) := by
    push_cast
    omega
  have n10 : ¬(1 : ℤ) ≡ 0 [ZMOD ((2 * halfPeriod L m j : ℕ) : ℤ)] := fun e => by
    have d := e.dvd
    rw [show (0 : ℤ) - 1 = -1 by norm_num, dvd_neg] at d
    have := Int.le_of_dvd one_pos d
    omega
  have n11 : ¬(1 : ℤ) ≡ -1 [ZMOD ((2 * halfPeriod L m j : ℕ) : ℤ)] := fun e => by
    have d := e.dvd
    rw [show (-1 : ℤ) - 1 = -2 by norm_num, dvd_neg] at d
    have := Int.le_of_dvd two_pos d
    omega
  have key : ∀ (μ ν : Fin 4) (t : ℤ), unitStep L m j μ = t • unitStep L m j ν →
      ∀ κ, (Pi.single μ (1 : ℤ) : Fin 4 → ℤ) κ ≡ (Pi.single ν t : Fin 4 → ℤ) κ
        [ZMOD ((2 * halfPeriod L m j : ℕ) : ℤ)] := by
    intro μ ν t e
    refine (hmod 0 _ _).1 ?_
    rw [← hs, ← hs, one_smul, e]
  refine ⟨fun μ ν e => ?_, fun μ ν e => ?_⟩
  · by_contra hne
    have := key μ ν 1 (by rw [one_smul]; exact e) μ
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
    exact n10 this
  · have := key μ ν (-1) (by rw [neg_one_zsmul]; exact e) μ
    by_cases hne : μ = ν
    · subst hne
      rw [Pi.single_eq_same, Pi.single_eq_same] at this
      exact n11 this
    · rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
      exact n10 this
end Coordinates
section Forms
variable {L m : ℕ} {j j' : ℤ}
theorem eq_forwardFrom_source {b : Bond L m j} {μ : Fin 4}
    (h : b.target - b.source = unitStep L m j μ) :
    b = Bond.forwardFrom b.source μ := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.eq_forwardFrom <;> assumption
theorem antisymmetric_bondFunction_ext {B B' : Bond L m j → ComplexMatrix2}
    (h : ∀ b : Bond L m j, B b.opposite = -B b)
    (h' : ∀ b : Bond L m j, B' b.opposite = -B' b)
    (e : ∀ (x : Site L m j) (μ : Fin 4), B (Bond.forwardFrom x μ) = B' (Bond.forwardFrom x μ)) :
    B = B' := by
  funext b
  obtain ⟨μ, h1 | h1⟩ := b.isNeighbour
  · rw [eq_forwardFrom_source h1, e]
  · have hr : b.opposite = Bond.forwardFrom b.target μ := by
      refine Bond.ext rfl ?_
      simp only [Bond.opposite, Bond.forwardFrom]
      rw [← neg_eq_iff_eq_neg.mpr h1]
      abel
    have e1 := h b
    have e2 := h' b
    rw [hr, e] at e1
    rw [hr] at e2
    exact neg_injective (e1.symm.trans e2)
open Classical in
def translationInvariantForm (a : Fin 4 → ComplexMatrix2) : Bond L m j → ComplexMatrix2 := fun b =>
  ∑ μ, ((if b.target - b.source = unitStep L m j μ then a μ else 0) -
    (if b.target - b.source = -unitStep L m j μ then a μ else 0))
theorem translationInvariantForm_opposite (a : Fin 4 → ComplexMatrix2) (b : Bond L m j) :
    translationInvariantForm a b.opposite = -translationInvariantForm a b := by
  have e : b.opposite.target - b.opposite.source = -(b.target - b.source) := by
    simp [Bond.opposite]
  simp only [translationInvariantForm, e, neg_eq_iff_eq_neg, neg_neg]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun μ _ => (neg_sub _ _).symm
theorem translationInvariantForm_forwardFrom
    (hs : (∀ μ ν, unitStep L m j μ = unitStep L m j ν → μ = ν) ∧
      ∀ μ ν, unitStep L m j μ ≠ -unitStep L m j ν)
    (a : Fin 4 → ComplexMatrix2) (x : Site L m j) (μ : Fin 4) :
    translationInvariantForm a (Bond.forwardFrom x μ) = a μ := by
  have e : (Bond.forwardFrom x μ).target - (Bond.forwardFrom x μ).source = unitStep L m j μ := by
    simp [Bond.forwardFrom]
  simp only [translationInvariantForm, e]
  rw [Finset.sum_eq_single μ]
  · rw [if_pos rfl, if_neg (hs.2 μ μ), sub_zero]
  · intro ν _ hν
    rw [if_neg (fun h => hν (hs.1 _ _ h).symm), if_neg (hs.2 μ ν), sub_zero]
  · simp
theorem bondFormSumAlong_add (A A' : Bond L m j → ComplexMatrix2) (Γ : List (Bond L m j)) :
    bondFormSumAlong (A + A') Γ = bondFormSumAlong A Γ + bondFormSumAlong A' Γ := by
  simp only [bondFormSumAlong]
  induction Γ with
  | nil => simp
  | cons b Γ ih =>
    simp only [List.map_cons, List.sum_cons, Pi.add_apply, ih]
    abel
theorem bondFormSumAlong_sub (A A' : Bond L m j → ComplexMatrix2) (Γ : List (Bond L m j)) :
    bondFormSumAlong (A - A') Γ = bondFormSumAlong A Γ - bondFormSumAlong A' Γ := by
  simp only [bondFormSumAlong]
  induction Γ with
  | nil => simp
  | cons b Γ ih =>
    simp only [List.map_cons, List.sum_cons, Pi.sub_apply, ih]
    abel
theorem contourFormAverage_add (A A' : Bond L m j' → ComplexMatrix2) (y : Site L m j)
    (x : Site L m j') :
    contourFormAverage (A + A') y x = contourFormAverage A y x + contourFormAverage A' y x := by
  simp only [contourFormAverage, bondFormSumAlong_add, Finset.sum_add_distrib, smul_add]
theorem contourFormAverage_sub (A A' : Bond L m j' → ComplexMatrix2) (y : Site L m j)
    (x : Site L m j') :
    contourFormAverage (A - A') y x = contourFormAverage A y x - contourFormAverage A' y x := by
  simp only [contourFormAverage, bondFormSumAlong_sub, Finset.sum_sub_distrib, smul_sub]
theorem scaledLinearBlockAverage_sub (hfin : ∀ y : Site L m j, (sitesInBlock j' y).Finite)
    (A A' : Bond L m j' → ComplexMatrix2) :
    (scaledLinearBlockAverage (A - A') : Bond L m j → ComplexMatrix2) =
      scaledLinearBlockAverage A - scaledLinearBlockAverage A' := by
  funext c
  simp only [scaledLinearBlockAverage, Pi.sub_apply, linearBlockSum]
  have hfs := hfin c.source
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfs]
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [contourFormAverage_sub, bondFormSumAlong_sub, contourFormAverage_sub]
  abel
end Forms
end PeriodicLattice.ClosedFormsSmoothing
namespace Tower.ClosedFormsSmoothing
open PeriodicLattice PeriodicLattice.ClosedFormsSmoothing
theorem vertexCoboundary_mem {L n k j : ℕ} {l : Vertex L n k j → ComplexMatrix2}
    (hl : l ∈ vertexFunctionSpace L n k j) : vertexCoboundary l ∈ edgeFormSpace L n k j :=
  ⟨fun _ _ => ComplexMatrix2.hermitianTraceless.sub_mem (hl _ (Set.mem_univ _))
      (hl _ (Set.mem_univ _)),
    fun b => by simp [vertexCoboundary, Bond.opposite]⟩
theorem linearSmoothing_closedForms (hT : ClosedEdgeFormsOnPeriodicLattice)
    (hR : TrivialLinearization.AllRelationsStatement)
    (hC : PeriodicLattice.CoordinateDescription) :
    LinearSmoothingOnClosedForms := by
  intro L n k i hL hn hik
  obtain ⟨hodd, h13⟩ := id hL
  have hL0 : 0 < L := by omega
  have hj : levelDepth k i = levelDepth k (i + 1) + 1 := by
    simp only [levelDepth]
    push_cast
    ring
  have hjm : -(n : ℤ) ≤ levelDepth k (i + 1) := by
    simp only [levelDepth]
    omega
  have hjm' : -(n : ℤ) ≤ levelDepth k i := by
    simp only [levelDepth]
    omega
  have hpos : 0 < (n : ℤ) + levelDepth k i := by
    simp only [levelDepth]
    omega
  have hC' := hC L n hodd h13 hn
  have hcoarse := hC'.1 _ hjm
  have hfine := hC'.1 _ hjm'
  have hblock := hC'.2.2.1 _ 1 hjm
  obtain ⟨hdv, h1⟩ := dvd_halfPeriod_and_one_lt (m := n) (j := levelDepth k i) h13 hpos
  have hdvd : (L : ℤ) ∣ ((2 * halfPeriod L n (levelDepth k i) : ℕ) : ℤ) := by
    exact_mod_cast Dvd.dvd.mul_left hdv 2
  obtain ⟨hSR, hCF, -⟩ := (hR L hL).1 n k i 0 hn hik (Nat.zero_le _)
  have hsub : ∀ ξ ξ' : Edge L n k i → ComplexMatrix2, linearSmoothing L n k i (ξ - ξ') =
      linearSmoothing L n k i ξ - linearSmoothing L n k i ξ' := fun ξ ξ' =>
    scaledLinearBlockAverage_sub (fun y => sitesInBlock_finite hL0 hblock y) ξ ξ'
  have hstep : ∀ l ∈ vertexFunctionSpace L n k i, ∀ a ∈ edgeFormSpace L n k i,
      ∀ c : Fin 4 → ComplexMatrix2,
      (∀ (x : Vertex L n k i) (μ : Fin 4), a (Bond.forwardFrom x μ) = c μ) →
      linearSmoothing L n k i (vertexCoboundary l + a) =
        vertexCoboundary (restrictVertexFunction (i + 1) l) + crossingSmoothing L n k i a := by
    intro l hl a ha c hc
    have e := hsub (vertexCoboundary l + a) a
    rw [add_sub_cancel_right, (hSR.2 l hl).1, (hCF a ha c hc).2.2.1] at e
    exact sub_eq_iff_eq_add.mp e.symm
  refine ⟨fun ξ _ ξ' _ => hsub ξ ξ', ?_, ?_⟩
  · intro ξ hξ hcl
    obtain ⟨l, hl, a, ha, hac, rfl⟩ := (hT L n k i hL hn hik.le ξ hξ).1 hcl
    have hc : ∀ (x : Vertex L n k i) (μ : Fin 4),
        a (Bond.forwardFrom x μ) = a (Bond.forwardFrom 0 μ) :=
      fun x μ => hac μ x 0
    rw [hstep l hl a ha _ hc]
    obtain ⟨-, -, -, hmem, hval⟩ := hCF a ha _ hc
    have hrl : restrictVertexFunction (i + 1) l ∈ vertexFunctionSpace L n k (i + 1) :=
      fun y _ => hl _ (Set.mem_univ _)
    exact (hT L n k (i + 1) hL hn hik _ (add_mem (vertexCoboundary_mem hrl) hmem)).2
      ⟨_, hrl, _, hmem, fun μ x x' => by rw [hval, hval], rfl⟩
  · intro B hB hcl
    obtain ⟨l', hl', b, hb, hbc, rfl⟩ := (hT L n k (i + 1) hL hn hik B hB).1 hcl
    obtain ⟨c, hcsu, hcb⟩ : ∃ c : Fin 4 → ComplexMatrix2,
        (∀ μ, c μ ∈ ComplexMatrix2.hermitianTraceless) ∧
        ∀ (x : Vertex L n k (i + 1)) (μ : Fin 4), (L : ℂ) • c μ = b (Bond.forwardFrom x μ) := by
      refine ⟨fun μ => ((L : ℝ)⁻¹) • b (Bond.forwardFrom 0 μ),
        fun μ => ComplexMatrix2.hermitianTraceless.smul_mem _
          (hb.1 _ ⟨μ, by simp [Bond.forwardFrom]⟩), fun x μ => ?_⟩
      have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL0.ne'
      rw [hbc μ x 0, show (L : ℂ) = ((L : ℝ) : ℂ) by simp, Complex.coe_smul, smul_smul,
        mul_inv_cancel₀ hLr, one_smul]
    have hs := unitStep_injective_and_ne_neg hfine h1
    obtain ⟨a, ha, hac⟩ : ∃ a ∈ edgeFormSpace L n k i,
        ∀ (x : Vertex L n k i) (μ : Fin 4), a (Bond.forwardFrom x μ) = c μ := by
      refine ⟨translationInvariantForm c,
        ⟨fun b' ⟨μ, h⟩ => ?_, translationInvariantForm_opposite c⟩,
        translationInvariantForm_forwardFrom hs c⟩
      rw [eq_forwardFrom_source h, translationInvariantForm_forwardFrom hs]
      exact hcsu μ
    have hacc : IsTranslationInvariantEdgeForm a := fun μ x x' => by rw [hac, hac]
    choose Y V hYV using exists_blockOffset hodd hL0 hfine hj
    have huniq : ∀ {y : Vertex L n k (i + 1)} {x : Vertex L n k i} {ν : Fin 4 → ℤ},
        IsBlockOffset y x ν → y = Y x ∧ ν = V x := fun h =>
      blockOffset_unique hcoarse hfine hL0 hdvd hj h (hYV _)
    obtain ⟨l, hldef⟩ : ∃ l : Vertex L n k i → ComplexMatrix2,
        ∀ x, l x = l' (Y x) - ∑ μ, V x μ • c μ := ⟨_, fun _ => rfl⟩
    have hl : l ∈ vertexFunctionSpace L n k i := fun x _ => by
      rw [hldef]
      exact ComplexMatrix2.hermitianTraceless.sub_mem (hl' _ (Set.mem_univ _))
        (ComplexMatrix2.hermitianTraceless.sum_mem fun μ _ => zsmul_mem (hcsu μ) _)
    have hrestrict : restrictVertexFunction (i + 1) l = l' := by
      funext y
      have hyl : (y : PeriodicLattice.FourTorus L n) ∈
          PeriodicLattice.sublattice L n (levelDepth k i) :=
        sublattice_mono hL0 n (by simp only [levelDepth]; omega) y.2
      have hx : ((PeriodicLattice.Site.toSublattice y (levelDepth k i) :
          PeriodicLattice.Site L n (levelDepth k i)) : PeriodicLattice.FourTorus L n) = y :=
        Classical.epsilon_spec
          (p := fun x : PeriodicLattice.Site L n (levelDepth k i) =>
            (x : PeriodicLattice.FourTorus L n) = y)
          ⟨⟨y, hyl⟩, rfl⟩
      have hd : IsBlockOffset y (PeriodicLattice.Site.toSublattice y (levelDepth k i)) 0 := by
        refine ⟨?_, fun μ => ?_⟩
        · rw [hx, sub_self]
          simp [pointOnAxis_zero]
        · simp only [Pi.zero_apply, abs_zero, mul_zero]
          omega
      obtain ⟨e1, e2⟩ := huniq hd
      show l (PeriodicLattice.Site.toSublattice y (levelDepth k i)) = l' y
      rw [hldef, ← e1, ← e2]
      simp
    have hdl := vertexCoboundary_mem hl
    refine ⟨vertexCoboundary l + a, add_mem hdl ha,
      (hT L n k i hL hn hik.le _ (add_mem hdl ha)).2 ⟨l, hl, a, ha, hacc, rfl⟩, ?_, ?_⟩
    · rw [hstep l hl a ha c hac, hrestrict]
      obtain ⟨-, -, -, hmem, hval⟩ := hCF a ha c hac
      have e : crossingSmoothing L n k i a = b :=
        antisymmetric_bondFunction_ext hmem.2 hb.2 fun x μ => by rw [hval, hcb x μ]
      rw [e]
    · funext x
      have hnot : (x.1 : PeriodicLattice.FourTorus L n) ≠
          (Y x.1 : PeriodicLattice.FourTorus L n) := fun e =>
        x.2 (by rw [e]; exact (Y x.1).2)
      have hmem : x.1 ∈ sitesInBlock (levelDepth k i) (Y x.1) :=
        (mem_sitesInBlock_iff hblock hj _ _).2 ⟨V x.1, hYV x.1⟩
      have hspec : x.1 ∈ sitesInBlock (levelDepth k i) (cubeCentre x) ∧
          (x.1 : PeriodicLattice.FourTorus L n) ≠ (cubeCentre x : PeriodicLattice.FourTorus L n) :=
        Classical.epsilon_spec (p := fun y : Vertex L n k (i + 1) =>
          x.1 ∈ sitesInBlock (levelDepth k i) y ∧ (x.1 : PeriodicLattice.FourTorus L n) ≠ y)
          ⟨Y x.1, hmem, hnot⟩
      obtain ⟨ν, hν⟩ := (mem_sitesInBlock_iff hblock hj _ _).1 hspec.1
      obtain ⟨e1, e2⟩ := huniq hν
      have hmean : fineOnlyContourAverage L n k i (vertexCoboundary l + a) x =
          fineOnlyContourAverage L n k i (vertexCoboundary l) x +
            contourFormAverage a (cubeCentre x) x.1 := contourFormAverage_add _ _ _ _
      rw [hmean, (hSR.2 l hl).2.2.2 _ x hspec.1 hspec.2, hrestrict,
        (hCF a ha c hac).1 _ _ ν hspec.1 hν, hldef, e1, e2]
      simp only [Pi.zero_apply]
      abel
end Tower.ClosedFormsSmoothing
end YangMills.Construction
end
