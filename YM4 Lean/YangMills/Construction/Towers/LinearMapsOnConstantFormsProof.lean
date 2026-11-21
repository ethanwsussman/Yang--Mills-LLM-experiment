import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATower
import YangMills.Construction.Towers.LinearMapsOnConstantForms
import YangMills.Construction.Towers.QuotientOfATowerCarriesConfigurationsProof
import YangMills.Construction.Towers.RelationsOfTheLinearMapsOfAStep
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open PeriodicLattice (FourTorus blockOffset orderedContour offsetAxes bondFormSumAlong flowAlong
  backwardAxisPath forwardAxisPath stepsThroughAxes AxisOrdering IsBlockOffset)
namespace Tower.ConstantForms
section SingleLattice
variable {L m : ℕ} {i : ℤ} (B : PeriodicLattice.Bond L m i → Matrices.ComplexMatrix2)
theorem bondFormSumAlong_forwardFlow {μ : Fin 4} {v : Matrices.ComplexMatrix2}
    (h : ∀ x, B (PeriodicLattice.Bond.forwardFrom x μ) = v) (t : ℕ)
    (x : PeriodicLattice.Site L m i) :
    bondFormSumAlong B (forwardAxisPath x μ t) = t • v := by
  induction t generalizing x with
  | zero => simp [bondFormSumAlong, forwardAxisPath]
  | succ t ih =>
    have hs := ih (x + PeriodicLattice.unitStep L m i μ)
    simp only [bondFormSumAlong] at hs ⊢
    simp only [forwardAxisPath, List.map_cons, List.sum_cons, hs, h, succ_nsmul']
theorem bondFormSumAlong_backwardFlow {μ : Fin 4} {v : Matrices.ComplexMatrix2}
    (h : ∀ x, B (PeriodicLattice.Bond.backwardFrom x μ) = -v) (t : ℕ)
    (x : PeriodicLattice.Site L m i) :
    bondFormSumAlong B (backwardAxisPath x μ t) = -(t • v) := by
  induction t generalizing x with
  | zero => simp [bondFormSumAlong, backwardAxisPath]
  | succ t ih =>
    have hs := ih (x - PeriodicLattice.unitStep L m i μ)
    simp only [bondFormSumAlong] at hs ⊢
    simp only [backwardAxisPath, List.map_cons, List.sum_cons, hs, h, succ_nsmul', neg_add]
theorem bondFormSumAlong_flowAlong {μ : Fin 4} {v : Matrices.ComplexMatrix2}
    (h : ∀ x, B (PeriodicLattice.Bond.forwardFrom x μ) = v)
    (hr : ∀ b : PeriodicLattice.Bond L m i, B b.opposite = -B b) (t : ℤ)
    (x : PeriodicLattice.Site L m i) :
    bondFormSumAlong B (flowAlong x μ t) = t • v := by
  have hb : ∀ x, B (PeriodicLattice.Bond.backwardFrom x μ) = -v := by
    intro x
    have he : PeriodicLattice.Bond.backwardFrom x μ =
        (PeriodicLattice.Bond.forwardFrom (x - PeriodicLattice.unitStep L m i μ) μ).opposite :=
      PeriodicLattice.Bond.ext (by simp [PeriodicLattice.Bond.backwardFrom,
        PeriodicLattice.Bond.forwardFrom, PeriodicLattice.Bond.opposite])
        (by simp [PeriodicLattice.Bond.backwardFrom, PeriodicLattice.Bond.forwardFrom,
          PeriodicLattice.Bond.opposite])
    rw [he, hr, h]
  unfold flowAlong
  split_ifs with ht
  · rw [bondFormSumAlong_forwardFlow B h, ← natCast_zsmul, Int.toNat_of_nonneg ht]
  · rw [bondFormSumAlong_backwardFlow B hb, ← natCast_zsmul, Int.toNat_of_nonneg (by omega),
      neg_smul, neg_neg]
theorem bondFormSumAlong_stepsThroughAxes (a : Fin 4 → Matrices.ComplexMatrix2)
    (h : ∀ x μ, B (PeriodicLattice.Bond.forwardFrom x μ) = a μ)
    (hr : ∀ b : PeriodicLattice.Bond L m i, B b.opposite = -B b) (n : Fin 4 → ℤ)
    (l : List (Fin 4)) (x : PeriodicLattice.Site L m i) :
    bondFormSumAlong B (stepsThroughAxes n x l) = (l.map fun μ => n μ • a μ).sum := by
  induction l generalizing x with
  | nil => simp [bondFormSumAlong, stepsThroughAxes]
  | cons μ l ih =>
    have h₁ := bondFormSumAlong_flowAlong B (fun x => h x μ) hr (n μ) x
    have h₂ := ih (x + n μ • PeriodicLattice.unitStep L m i μ)
    simp only [bondFormSumAlong] at h₁ h₂ ⊢
    simp only [stepsThroughAxes, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      h₁, h₂]
theorem bondFormSumAlong_orderedContour {j : ℤ} (a : Fin 4 → Matrices.ComplexMatrix2)
    (h : ∀ x μ, B (PeriodicLattice.Bond.forwardFrom x μ) = a μ)
    (hr : ∀ b : PeriodicLattice.Bond L m i, B b.opposite = -B b)
    (y : PeriodicLattice.Site L m j) (x : PeriodicLattice.Site L m i) (σ : AxisOrdering y x) :
    bondFormSumAlong B (orderedContour y x σ) = ∑ μ, blockOffset y x μ • a μ := by
  unfold orderedContour
  rw [bondFormSumAlong_stepsThroughAxes B a h hr, List.map_map, ← Fin.sum_univ_def]
  have he := Equiv.sum_comp σ fun s : offsetAxes y x =>
    blockOffset y x (s : Fin 4) • a (s : Fin 4)
  simp only [Function.comp_apply]
  rw [he, Finset.sum_coe_sort (offsetAxes y x) fun μ => blockOffset y x μ • a μ]
  refine Finset.sum_subset (Finset.subset_univ _) fun μ _ hμ => ?_
  have h0 : blockOffset y x μ = 0 := by
    simpa [offsetAxes] using hμ
  rw [h0, zero_smul]
theorem contourFormAverage_eq_sum {j : ℤ} (a : Fin 4 → Matrices.ComplexMatrix2)
    (h : ∀ x μ, B (PeriodicLattice.Bond.forwardFrom x μ) = a μ)
    (hr : ∀ b : PeriodicLattice.Bond L m i, B b.opposite = -B b)
    (y : PeriodicLattice.Site L m j) (x : PeriodicLattice.Site L m i) :
    PeriodicLattice.contourFormAverage B y x = ∑ μ, blockOffset y x μ • a μ := by
  unfold PeriodicLattice.contourFormAverage
  simp only [bondFormSumAlong_orderedContour B a h hr y x, Finset.sum_const, Finset.card_univ]
  have : Nonempty (AxisOrdering y x) := ⟨(Finset.equivFin _).symm⟩
  have hc : (Fintype.card (AxisOrdering y x) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hone : (((Fintype.card (AxisOrdering y x) : ℝ)⁻¹ : ℝ) : ℂ) *
      (Fintype.card (AxisOrdering y x) : ℂ) = 1 := by
    have hc' : (Fintype.card (AxisOrdering y x) : ℂ) ≠ 0 := by exact_mod_cast hc
    push_cast
    exact inv_mul_cancel₀ hc'
  rw [hone, one_smul]
end SingleLattice
section Levels
variable {L n k j : ℕ}
theorem offsetPoint_of_isBlockOffset {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
    {ν : Fin 4 → ℤ} (h : IsBlockOffset y x ν) :
    (x : FourTorus L n) = offsetPoint (meshAt L k j) (y : FourTorus L n) ν ∧
      ν ∈ offsetBox L 1 := by
  refine ⟨?_, mem_offsetBox_iff.2 fun μ => by simpa using h.2 μ⟩
  have hx := h.1
  rw [meshSize_levelDepth] at hx
  unfold offsetPoint
  rw [← hx]
  abel
theorem isBlockOffset_of_offsetPoint {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
    {ν : Fin 4 → ℤ}
    (hx : (x : FourTorus L n) = offsetPoint (meshAt L k j) (y : FourTorus L n) ν)
    (hν : ν ∈ offsetBox L 1) : IsBlockOffset y x ν := by
  refine ⟨?_, fun μ => by simpa using mem_offsetBox_iff.1 hν μ⟩
  rw [meshSize_levelDepth, hx]
  unfold offsetPoint
  abel
theorem offsetPoint_neg (a : ℝ) (y : FourTorus L n) (ν : Fin 4 → ℤ) :
    offsetPoint a y (-ν) = y + y - offsetPoint a y ν := by
  have hμ : ∀ μ, PeriodicLattice.pointOnAxis L n μ ((((-ν) μ : ℤ) : ℝ) * a) =
      -PeriodicLattice.pointOnAxis L n μ (((ν μ : ℤ) : ℝ) * a) := by
    intro μ
    simp [PeriodicLattice.pointOnAxis, Pi.single_neg]
  unfold offsetPoint
  simp only [hμ, Finset.sum_neg_distrib]
  abel
theorem coe_toSublattice_succ (hL : 0 < L) (y : Vertex L n k (j + 1)) :
    ((y.toSublattice (PeriodicLattice.levelDepth k j) : Vertex L n k j) : FourTorus L n) = y := by apply _root_.YangMills.Construction.Tower.FieldProjection.coe_toSublattice <;> assumption
end Levels
theorem constantFormsStatement_holds (hRel : TrivialLinearization.OneStepIdentitiesHold)
    (hRev : AxisPathReversal.MainStatement)
    (hBlocks : BlockPathContourPivotStatement) : LinearizationFacts.constantFormsStatement := by
  intro L hL n k j hn hj B hB a ha
  have hL0 : 0 < L := by
    have := hL.2
    omega
  obtain ⟨hP, -, hT, -⟩ := (hBlocks L hL k 1 (j + 1) (by omega) (by omega) (by omega)).1 n hn
  have hB' : PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra B := hB
  have hr : ∀ b : Edge L n k j, B b.opposite = -B b := hB'.2
  have hinj : ∀ y : Vertex L n k (j + 1),
      InjOn (offsetPoint (meshAt L k j) (y : FourTorus L n)) (offsetBox L 1) := hP.injOn_offset
  have hblock : ∀ y : Vertex L n k (j + 1), PeriodicLattice.refinedBlock 1 y =
      offsetPoint (meshAt L k j) (y : FourTorus L n) '' offsetBox L 1 := hP.eq_image
  have hcross : ∀ (c : Edge L n k (j + 1)) (μ : Fin 4),
      c.target - c.source = PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k (j + 1)) μ →
      ∀ x : Vertex L n k j, (x : FourTorus L n) ∈ PeriodicLattice.refinedBlock 1 c.source →
        PeriodicLattice.crossingPath c x = (List.range (L ^ 1)).map fun t =>
          PeriodicLattice.Bond.forwardFrom
            (x + t • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ) μ :=
    hT.crossingPath_eq
  have hcm : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j) (ν : Fin 4 → ℤ),
      IsBlockOffset y x ν → PeriodicLattice.contourFormAverage B y x = ∑ μ, ν μ • a μ := by
    intro y x ν h
    rw [contourFormAverage_eq_sum B a ha hr y x]
    have hspec : IsBlockOffset y x (blockOffset y x) :=
      Classical.epsilon_spec (p := IsBlockOffset y x) ⟨ν, h⟩
    obtain ⟨e₁, m₁⟩ := offsetPoint_of_isBlockOffset h
    obtain ⟨e₂, m₂⟩ := offsetPoint_of_isBlockOffset hspec
    rw [hinj y m₂ m₁ (e₂.symm.trans e₁)]
  have hzero : cubeContourAverage L n k j B = 0 := by
    funext y
    let y' : Vertex L n k j := y.toSublattice (PeriodicLattice.levelDepth k j)
    have hy' : (y' : FourTorus L n) = y := coe_toSublattice_succ hL0 y
    let e : Vertex L n k j → Vertex L n k j := fun x => y' + y' - x
    have hrefl : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        ∃ ν : Fin 4 → ℤ, IsBlockOffset y x ν ∧ IsBlockOffset y (e x) (-ν) ∧
          e x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y := by
      intro x hx
      have hx' : (x : FourTorus L n) ∈ PeriodicLattice.refinedBlock 1 y := hx
      rw [hblock y] at hx'
      obtain ⟨ν, hν, hνx⟩ := hx'
      have hneg : -ν ∈ offsetBox L 1 :=
        mem_offsetBox_iff.2 fun μ => by simpa using mem_offsetBox_iff.1 hν μ
      have hex : ((e x : Vertex L n k j) : FourTorus L n) =
          offsetPoint (meshAt L k j) (y : FourTorus L n) (-ν) := by
        rw [offsetPoint_neg, hνx]
        simp [e, hy']
      refine ⟨ν, isBlockOffset_of_offsetPoint hνx.symm hν,
        isBlockOffset_of_offsetPoint hex hneg, ?_⟩
      show ((e x : Vertex L n k j) : FourTorus L n) ∈ PeriodicLattice.refinedBlock 1 y
      rw [hblock y, hex]
      exact ⟨-ν, hneg, rfl⟩
    have hee : ∀ x, e (e x) = x := fun x => by simp [e]
    have hb : BijOn e (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
        (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) := by
      refine ⟨fun x hx => ?_, fun p _ q _ hpq => ?_, fun z hz => ?_⟩
      · obtain ⟨_, _, _, h⟩ := hrefl x hx
        exact h
      · rw [← hee p, ← hee q, hpq]
      · obtain ⟨_, _, _, h⟩ := hrefl z hz
        exact ⟨e z, h, hee z⟩
    have hsum : (∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
          -PeriodicLattice.contourFormAverage B y x) =
        ∑ᶠ z ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
          PeriodicLattice.contourFormAverage B y z := by
      refine finsum_mem_eq_of_bijOn e hb fun x hx => ?_
      obtain ⟨ν, h₁, h₂, _⟩ := hrefl x hx
      rw [hcm y x ν h₁, hcm y (e x) (-ν) h₂]
      simp [neg_smul, Finset.sum_neg_distrib]
    simp only [finsum_neg_distrib] at hsum
    have h2 : (2 : ℂ) • (∑ᶠ z ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        PeriodicLattice.contourFormAverage B y z) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hsum]
      exact neg_add_cancel _
    have hS := (smul_eq_zero.1 h2).resolve_left two_ne_zero
    show PeriodicLattice.inverseFourthPowerWeight L • _ = 0
    rw [hS, smul_zero]
  have hcard : ∀ y : Vertex L n k (j + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).ncard = L ^ 4 := by
    intro y
    have himg : Subtype.val '' PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y =
        PeriodicLattice.refinedBlock 1 y := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hp
        exact ⟨⟨p, hP.subset_sublattice y hp⟩, hp, rfl⟩
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg]
    simpa using hP.ncard_eq y
  have hfwd : ∀ (x : Vertex L n k (j + 1)) (μ : Fin 4),
      crossingSmoothing L n k j B (PeriodicLattice.Bond.forwardFrom x μ) = (L : ℂ) • a μ := by
    intro x μ
    have hc : (PeriodicLattice.Bond.forwardFrom x μ).target -
        (PeriodicLattice.Bond.forwardFrom x μ).source =
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k (j + 1)) μ := by
      simp [PeriodicLattice.Bond.forwardFrom]
    have hterm : ∀ z ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (PeriodicLattice.Bond.forwardFrom x μ).source,
        edgeFormPathSum B (PeriodicLattice.crossingPath (PeriodicLattice.Bond.forwardFrom x μ) z) =
          L • a μ := by
      intro z hz
      rw [hcross _ μ hc z hz]
      simp [edgeFormPathSum, bondFormSumAlong, List.map_map, Function.comp_def, ha]
    have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (PeriodicLattice.Bond.forwardFrom x μ).source).Finite :=
      Set.finite_of_ncard_pos (by rw [hcard]; positivity)
    unfold crossingSmoothing
    rw [finsum_mem_congr rfl hterm, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const,
      ← Set.ncard_eq_toFinset_card _ hfin, hcard, ← Nat.cast_smul_eq_nsmul ℂ,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
    have hw : PeriodicLattice.inverseFourthPowerWeight L * ((L ^ 4 : ℕ) : ℂ) = 1 := by
      unfold PeriodicLattice.inverseFourthPowerWeight
      push_cast
      rw [zpow_neg]
      field_simp
    rw [hw, one_mul]
  have hform : crossingSmoothing L n k j B ∈ edgeFormSpace L n k (j + 1) := by
    exact show PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra
        (crossingSmoothing L n k j B) from by
      refine ⟨fun b hb => ?_, fun b => ?_⟩
      · obtain ⟨μ, hμ⟩ := hb
        have hbe : b = PeriodicLattice.Bond.forwardFrom b.source μ :=
          PeriodicLattice.Bond.ext rfl (by
            show b.target = b.source + _
            rw [← hμ]
            abel)
        rw [hbe, hfwd]
        have hpos : (PeriodicLattice.Bond.forwardFrom (0 : Vertex L n k j) μ).IsPositivelyOriented :=
          ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
        have haμ : a μ ∈ Matrices.ComplexMatrix2.hermitianTraceless := by
          have := hB'.1 _ hpos
          rwa [ha] at this
        have hs := Matrices.ComplexMatrix2.hermitianTraceless.smul_mem (L : ℝ) haμ
        have he : (L : ℂ) • a μ = (L : ℝ) • a μ := by
          rw [← Complex.coe_smul]
          norm_num
        rw [he]
        exact hs
      · have hOneC : PeriodicLattice.IsBondForm PeriodicLattice.complexLieAlgebra B :=
          (((hRev L hL k).1 n hn).1 j hj.le).1 B hB
        have hs := (((hRev L hL k).1 n hn).2 j hj b B hOneC).1
        unfold crossingSmoothing
        rw [hs, smul_neg]
  refine ⟨fun y x ν _ hν => hcm y x ν hν, hzero, ?_, hform, hfwd⟩
  have hq := ((hRel L hL n k j hn hj).1) B hB
  rw [hq, hzero]
  funext c
  simp [vertexCoboundary]
end Tower.ConstantForms
end YangMills.Construction
end
