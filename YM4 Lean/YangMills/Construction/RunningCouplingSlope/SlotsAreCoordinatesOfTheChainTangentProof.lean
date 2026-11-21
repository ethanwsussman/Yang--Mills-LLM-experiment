import YangMills.Construction.Lattice.BondOrientation
import YangMills.Construction.Lattice.BondsWithTheirReverses
import YangMills.Construction.RunningCouplingSlope.MovementsOfAChainAreTriangularProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower BlockAverages ColdStepAtMirrorFrames TorusFields Matrices Conventions
namespace SlotCoordinates
private def ofComponents (v : Fin 3 → ℝ) : ComplexMatrix2 :=
  !![(v 0 : ℂ), (v 2 : ℂ) - Complex.I * (v 1 : ℂ); (v 2 : ℂ) + Complex.I * (v 1 : ℂ), -(v 0 : ℂ)]
private theorem suTwoComponents_ofComponents (v : Fin 3 → ℝ) : suTwoComponents (ofComponents v) = v := by
  funext c
  fin_cases c <;> simp [suTwoComponents, ofComponents]
private theorem ofComponents_mem (v : Fin 3 → ℝ) : ofComponents v ∈ ComplexMatrix2.hermitianTraceless := by
  refine ⟨?_, ?_⟩
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [ofComponents, Matrix.conjTranspose_apply] <;> ring
  · simp [ComplexMatrix2.fullTrace, ofComponents, Matrix.trace_fin_two]
private theorem ofComponents_add (v w : Fin 3 → ℝ) : ofComponents (v + w) = ofComponents v + ofComponents w := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [ofComponents] <;> ring
private theorem ofComponents_smul (r : ℝ) (v : Fin 3 → ℝ) : ofComponents (r • v) = r • ofComponents v := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [ofComponents] <;> ring
private theorem suTwoComponents_add (A B : ComplexMatrix2) :
    suTwoComponents (A + B) = suTwoComponents A + suTwoComponents B := by apply _root_.YangMills.SharedProofs.p37688 <;> assumption
private theorem suTwoComponents_smul (r : ℝ) (A : ComplexMatrix2) :
    suTwoComponents (r • A) = r • suTwoComponents A := by apply _root_.YangMills.SharedProofs.p5119 <;> assumption
private theorem halfTrace_mul_re {A B : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.hermitianTraceless)
    (hB : B ∈ ComplexMatrix2.hermitianTraceless) :
    (ComplexMatrix2.halfTrace (A * B)).re = ∑ c : Fin 3, suTwoComponents A c * suTwoComponents B c := by
  obtain ⟨hA, tA⟩ := hA
  obtain ⟨hB, tB⟩ := hB
  have a10 : A 1 0 = star (A 0 1) := by
    have := congrFun (congrFun hA 1) 0
    simpa [Matrix.conjTranspose_apply] using this
  have b10 : B 1 0 = star (B 0 1) := by
    have := congrFun (congrFun hB 1) 0
    simpa [Matrix.conjTranspose_apply] using this
  have a00 : (A 0 0).im = 0 := by
    have := congrArg Complex.im (congrFun (congrFun hA 0) 0)
    simp [Matrix.conjTranspose_apply] at this
    linarith
  have b00 : (B 0 0).im = 0 := by
    have := congrArg Complex.im (congrFun (congrFun hB 0) 0)
    simp [Matrix.conjTranspose_apply] at this
    linarith
  have a11 : A 1 1 = -A 0 0 := by
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] at tA
    linear_combination tA
  have b11 : B 1 1 = -B 0 0 := by
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] at tB
    linear_combination tB
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_three, a10, b10, a11, b11, suTwoComponents]
  simp [Complex.mul_re, Complex.add_re, a00, b00]
  ring
private theorem torusSideBelow_eq (L : ℕ) : ∀ s N : ℕ, torusSideBelow L s N = N * L ^ s
  | 0, N => by simp [torusSideBelow]
  | s + 1, N => by
    rw [torusSideBelow, torusSideBelow_eq L s, pow_succ]
    ring
variable {L n K : ℕ}
private theorem period_frameAtStep (j : Fin K) (i : Fin 4) :
    (frameAtStep L n K j).period (frameAtStep L n K j).depth i = 2 * L ^ (n + (K - j)) := by apply _root_.YangMills.SharedProofs.p118180 <;> assumption
private def coordPair (F : BlockFrame) : LevelCoord F → (F.Site F.depth × Fin 4) × Fin 3
  | .inl i => (i.1.1, i.2)
  | .inr i => (i.1.1, i.2)
private theorem mem_innerBonds_all {F : BlockFrame} (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (b : F.Site F.depth × Fin 4) : b ∈ innerBonds (finiteCells F) F.depth := by
  have cov : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth := fun x =>
    FrameTorusAction.mem_sitesOfCells_of_forall_mem hodd hs
      (FrameTorusAction.mem_finiteCells F hs) x
  unfold innerBonds
  simp [cov]
private theorem coordPair_bijective {F : BlockFrame} (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) :
    Function.Bijective (coordPair F) := by
  classical
  constructor
  · rintro (a | a) (b | b) h
    · simp only [coordPair, Prod.mk.injEq] at h
      exact congrArg Sum.inl (Prod.ext (Subtype.ext h.1) h.2)
    · simp only [coordPair, Prod.mk.injEq] at h
      have h1 := (Finset.mem_filter.mp a.1.2).2
      have h2 := (Finset.mem_filter.mp b.1.2).2
      exact absurd (h.1 ▸ h2) h1
    · simp only [coordPair, Prod.mk.injEq] at h
      have h1 := (Finset.mem_filter.mp a.1.2).2
      have h2 := (Finset.mem_filter.mp b.1.2).2
      exact absurd (h.1 ▸ h1) h2
    · simp only [coordPair, Prod.mk.injEq] at h
      exact congrArg Sum.inr (Prod.ext (Subtype.ext h.1) h.2)
  · rintro ⟨b, c⟩
    by_cases hb : IsAxialTreeBond b
    · exact ⟨.inr (⟨b, Finset.mem_filter.mpr ⟨mem_innerBonds_all hodd hs b, hb⟩⟩, c), rfl⟩
    · exact ⟨.inl (⟨b, Finset.mem_filter.mpr ⟨mem_innerBonds_all hodd hs b, hb⟩⟩, c), rfl⟩
private theorem levelCoords_eq (j : Fin K) (B : Edge L n K j → ComplexMatrix2)
    (e : LevelCoord (frameAtStep L n K j)) :
    levelCoords j B e = suTwoComponents (B (edgeOfCoords j (coordPair _ e).1)) (coordPair _ e).2 := by
  rcases e with i | i <;> rfl
private theorem levelCoords_add (j : Fin K) (B B' : Edge L n K j → ComplexMatrix2) :
    levelCoords j (B + B') = levelCoords j B + levelCoords j B' := by
  funext e
  simp [levelCoords_eq, suTwoComponents_add]
private theorem levelCoords_smul (j : Fin K) (r : ℝ) (B : Edge L n K j → ComplexMatrix2) :
    levelCoords j (r • B) = r • levelCoords j B := by
  funext e
  simp [levelCoords_eq, suTwoComponents_smul]
private theorem levelCoords_zero (j : Fin K) :
    levelCoords j (0 : Edge L n K j → ComplexMatrix2) = 0 := by
  have := levelCoords_smul (L := L) (n := n) j 0 0
  simpa using this
private theorem blockFactor_pos (hL : IsAdmissibleBlockingFactor L) : 0 < L := by apply _root_.YangMills.Construction.Tower.AxisPathReversal.blockingFactor_pos <;> assumption
private theorem extent_pos (hL : IsAdmissibleBlockingFactor L) (j : Fin K) (i : Fin 4) :
    0 < (frameAtStep L n K j).extent i := by
  have h : (frameAtStep L n K j).extent i = sideAtStep L n K j := rfl
  rw [h, sideAtStep, torusSideBelow_eq]
  have := blockFactor_pos hL
  positivity
private theorem period_neZero (hL : IsAdmissibleBlockingFactor L) (j : Fin K) (i : Fin 4) :
    NeZero ((frameAtStep L n K j).period (frameAtStep L n K j).depth i) :=
  ⟨by
    rw [period_frameAtStep]
    have := blockFactor_pos hL
    positivity⟩
private theorem edgeFormPairing_re_eq (hpos : FramePositiveEdgesBijective)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (j : Fin K) {B B' : Edge L n K j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n K j) (hB' : B' ∈ edgeFormSpace L n K j) :
    (edgeFormPairing B B').re = dotProduct (levelCoords j B) (levelCoords j B') := by
  classical
  obtain ⟨hp, hinj, hsurj⟩ := hpos L hL n K j hn j.2.le (frameAtStep L n K j)
    (frameAtStep L n K j).depth (period_frameAtStep j)
  have := period_neZero (n := n) hL j
  let φ : (frameAtStep L n K j).Site (frameAtStep L n K j).depth × Fin 4 → PositiveEdge L n K j :=
    fun b => ⟨edgeOfCoords j b, hp b⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => hinj (congrArg Subtype.val h), fun c => ?_⟩
    obtain ⟨b, hb⟩ := hsurj c.1 c.2
    exact ⟨b, Subtype.ext hb⟩
  letI : Fintype (PositiveEdge L n K j) := Fintype.ofBijective φ hφ
  have hT := coordPair_bijective (F := frameAtStep L n K j) hL.1 (extent_pos hL j)
  unfold edgeFormPairing traceFinsumPairing restrictToPositiveEdges
  rw [finsum_eq_sum_of_fintype, Complex.re_sum, ← hφ.sum_comp]
  simp only [dotProduct, levelCoords_eq]
  rw [hT.sum_comp (fun p => suTwoComponents (B (edgeOfCoords j p.1)) p.2 *
    suTwoComponents (B' (edgeOfCoords j p.1)) p.2),
    Fintype.sum_prod_type (fun p : ((frameAtStep L n K j).Site (frameAtStep L n K j).depth × Fin 4) × Fin 3 =>
      suTwoComponents (B (edgeOfCoords j p.1)) p.2 * suTwoComponents (B' (edgeOfCoords j p.1)) p.2)]
  exact Finset.sum_congr rfl fun b _ => halfTrace_mul_re (hB.1 _ (hp b)) (hB'.1 _ (hp b))
private theorem exists_linear_form (hpos : FramePositiveEdgesBijective)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (j : Fin K) :
    ∃ d : (LevelCoord (frameAtStep L n K j) → ℝ) →ₗ[ℝ] edgeFormSpace L n K j,
      ∀ v, levelCoords j (d v : Edge L n K j → ComplexMatrix2) = v := by
  classical
  obtain ⟨hp, hinj, -⟩ := hpos L hL n K j hn j.2.le (frameAtStep L n K j)
    (frameAtStep L n K j).depth (period_frameAtStep j)
  have := period_neZero (n := n) hL j
  have hT := coordPair_bijective (F := frameAtStep L n K j) hL.1 (extent_pos hL j)
  let ε := Equiv.ofBijective _ hT
  let r : Edge L n K j → (frameAtStep L n K j).Site (frameAtStep L n K j).depth × Fin 4 :=
    Function.invFun (fun b => edgeOfCoords j b)
  have hr : ∀ b, r (edgeOfCoords j b) = b := Function.leftInverse_invFun hinj
  have hX : ∀ b : Edge L n K j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun b =>
    PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite (by have := hL.2; omega)
      (by
        have : PeriodicLattice.levelDepth K j = ((K : ℤ) - (j : ℕ)) := rfl
        rw [this]
        omega) b
  let f : (LevelCoord (frameAtStep L n K j) → ℝ) → Edge L n K j → ComplexMatrix2 :=
    fun v c => ofComponents fun t => v (ε.symm (r c, t))
  have hmem : ∀ v, extendOddly (f v) ∈ edgeFormSpace L n K j := fun v => by
    refine ⟨fun b hb => ?_, fun b => ?_⟩
    · simp only [extendOddly, if_pos hb]
      exact ofComponents_mem _
    · by_cases hb : b.IsPositivelyOriented
      · have h' := PeriodicLattice.not_isPositivelyOriented_opposite hX hb
        simp only [extendOddly, if_pos hb, if_neg h']
        rw [PeriodicLattice.Bond.opposite_involutive b]
      · have h' := PeriodicLattice.isPositivelyOriented_opposite hX hb
        simp only [extendOddly, if_neg hb, if_pos h', neg_neg]
  refine ⟨{ toFun := fun v => ⟨extendOddly (f v), hmem v⟩, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro v w
    refine Subtype.ext (funext fun c => ?_)
    have e : ∀ c, f (v + w) c = f v c + f w c := fun c => ofComponents_add _ _
    by_cases hc : c.IsPositivelyOriented
    · simp [extendOddly, hc, e]
    · simp [extendOddly, hc, e]
      abel
  · intro a v
    refine Subtype.ext (funext fun c => ?_)
    have e : ∀ c, f (a • v) c = a • f v c := fun c => ofComponents_smul _ _
    by_cases hc : c.IsPositivelyOriented
    · simp [extendOddly, hc, e]
    · simp [extendOddly, hc, e]
  · intro v
    funext e
    rw [levelCoords_eq]
    show suTwoComponents (extendOddly (f v) _) _ = _
    simp only [extendOddly, if_pos (hp _), f, hr, suTwoComponents_ofComponents]
    exact congrArg v (ε.symm_apply_apply e)
variable {k : ℕ}
private theorem slotOfLevel_mem (ξ : LevelForms L n (k + 1)) (j : Fin (k + 1)) :
    slotOfLevel ξ j ∈ edgeFormSpace L n (k + 1) j := by
  obtain ⟨_ | j, h⟩ := j
  · exact ξ.1.2
  · exact (ξ.2 ⟨j, Nat.lt_of_succ_lt h⟩).2
private theorem slotOfLevel_add (ξ ξ' : LevelForms L n (k + 1)) (j : Fin (k + 1)) :
    slotOfLevel (ξ + ξ') j = slotOfLevel ξ j + slotOfLevel ξ' j := by
  obtain ⟨_ | j, h⟩ := j <;> rfl
private theorem slotOfLevel_smul (r : ℝ) (ξ : LevelForms L n (k + 1)) (j : Fin (k + 1)) :
    slotOfLevel (r • ξ) j = r • slotOfLevel ξ j := by
  obtain ⟨_ | j, h⟩ := j <;> rfl
private def slotLinearMap (L n k : ℕ) :
    LevelForms L n (k + 1) →ₗ[ℝ] EuclideanSpace ℝ (ChainCoord L n (k + 1)) where
  toFun ξ := WithLp.toLp 2 (slotCoords ξ)
  map_add' ξ ξ' := by
    ext e
    simp [slotCoords, slotOfLevel_add, levelCoords_add]
  map_smul' r ξ := by
    ext e
    simp [slotCoords, slotOfLevel_smul, levelCoords_smul]
private theorem levelPairing_eq (hpos : FramePositiveEdgesBijective)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (ξ ξ' : LevelForms L n (k + 1)) :
    levelPairing (formValues ξ) (formValues ξ') =
      dotProduct (slotCoords ξ) (slotCoords ξ') +
        (edgeFormPairing ((finalNoise ξ : edgeFormSpace L n (k + 1) (k + 1)) : Edge L n (k + 1) (k + 1) → ComplexMatrix2)
          ((finalNoise ξ' : edgeFormSpace L n (k + 1) (k + 1)) : Edge L n (k + 1) (k + 1) → ComplexMatrix2)).re := by
  have hd : dotProduct (slotCoords ξ) (slotCoords ξ') =
      ∑ j : Fin (k + 1), (edgeFormPairing (slotOfLevel ξ j) (slotOfLevel ξ' j)).re := by
    simp only [dotProduct, Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun j _ =>
      (edgeFormPairing_re_eq hpos hL hn j (slotOfLevel_mem ξ j) (slotOfLevel_mem ξ' j)).symm
  rw [hd, Fin.sum_univ_succ]
  simp only [levelPairing, formValues]
  rw [Fin.sum_univ_castSucc, add_assoc]
  rfl
private theorem exists_slot_section (hpos : FramePositiveEdgesBijective)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∃ s : EuclideanSpace ℝ (ChainCoord L n (k + 1)) →ₗ[ℝ] LevelForms L n (k + 1),
      slotLinearMap L n k ∘ₗ s = LinearMap.id ∧ finalNoise ∘ₗ s = 0 := by
  classical
  choose d hd using fun j : Fin (k + 1) => exists_linear_form (L := L) (n := n) hpos hL hn j
  let res : (j : Fin (k + 1)) → EuclideanSpace ℝ (ChainCoord L n (k + 1)) →ₗ[ℝ]
      (LevelCoord (frameAtStep L n (k + 1) j) → ℝ) := fun j =>
    { toFun := fun v e => v ⟨j, e⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let q : (i : Fin (k + 1)) → EuclideanSpace ℝ (ChainCoord L n (k + 1)) →ₗ[ℝ]
      edgeFormSpace L n (k + 1) (i + 1) := fun i =>
    if h : (i : ℕ) < k then d ⟨i + 1, by omega⟩ ∘ₗ res ⟨i + 1, by omega⟩ else 0
  have hq : ∀ (i : Fin (k + 1)) (h : (i : ℕ) < k) v,
      q i v = d ⟨i + 1, by omega⟩ (res ⟨i + 1, by omega⟩ v) := fun i h v => by
    simp only [q, dif_pos h]
    rfl
  have hq0 : q (Fin.last k) = 0 := by
    simp [q]
  refine ⟨LinearMap.prod (d ⟨0, Nat.succ_pos k⟩ ∘ₗ res ⟨0, Nat.succ_pos k⟩) (LinearMap.pi q), ?_, ?_⟩
  · refine LinearMap.ext fun v => ?_
    ext ⟨j, e⟩
    obtain ⟨_ | j, h⟩ := j
    · exact congrFun (hd ⟨0, h⟩ (res ⟨0, h⟩ v)) e
    · have hj : j < k := by omega
      have := congrFun (hd ⟨j + 1, h⟩ (res ⟨j + 1, h⟩ v)) e
      show levelCoords ⟨j + 1, h⟩ ((q ⟨j, Nat.lt_of_succ_lt h⟩ v : edgeFormSpace L n (k + 1) (j + 1)) :
        Edge L n (k + 1) (j + 1) → ComplexMatrix2) e = _
      rw [hq ⟨j, Nat.lt_of_succ_lt h⟩ hj]
      exact this
  · refine LinearMap.ext fun v => ?_
    show q (Fin.last k) v = 0
    rw [hq0]
    rfl
end SlotCoordinates
open SlotCoordinates in
theorem slotCoordsIsometry_holds
    (hS : FiniteSideFormSpaces)
    (hpos : FramePositiveEdgesBijective) :
    SlotCoordsIsometry := by
  intro L hL k n hn
  have hE : ∀ j, j ≤ k + 1 → EdgeFormsEuclidean L n (k + 1) j := fun j hj => by
    obtain ⟨-, f, -, c, h⟩ := hS L n (k + 1) j hL hn hj
    exact ⟨f, c, fun B B' => by rw [h B B', Complex.ofReal_re]⟩
  have hC : LevelFormsEuclidean L n (k + 1) := by
    obtain ⟨f₀, c₀, h₀⟩ := hE 0 (Nat.zero_le _)
    have hi := fun i : Fin (k + 1) => hE (i + 1) (by omega)
    choose fi ci hci using hi
    have hcp : ∀ ξ ξ' : LevelForms L n (k + 1), levelPairing (formValues ξ) (formValues ξ') =
        c₀.inner ξ.1 ξ'.1 + ∑ i, (ci i).inner (ξ.2 i) (ξ'.2 i) := fun ξ ξ' => by
      simp only [levelPairing, formValues, h₀ _ _, hci _ _ _]
    have h0s : ∀ x y : edgeFormSpace L n (k + 1) 0, c₀.inner x y = c₀.inner y x := fun x y => by
      simpa using (c₀.conj_inner_symm x y).symm
    have his : ∀ (i : Fin (k + 1)) (x y : edgeFormSpace L n (k + 1) (i + 1)),
        (ci i).inner x y = (ci i).inner y x := fun i x y => by
      simpa using ((ci i).conj_inner_symm x y).symm
    have h0n : ∀ x : edgeFormSpace L n (k + 1) 0, 0 ≤ c₀.inner x x := fun x => by
      simpa using c₀.re_inner_nonneg x
    have hin : ∀ (i : Fin (k + 1)) (x : edgeFormSpace L n (k + 1) (i + 1)), 0 ≤ (ci i).inner x x := fun i x => by
      simpa using (ci i).re_inner_nonneg x
    refine ⟨inferInstance,
      { inner := fun ξ ξ' => levelPairing (formValues ξ) (formValues ξ')
        conj_inner_symm := ?_
        re_inner_nonneg := ?_
        add_left := ?_
        smul_left := ?_
        definite := ?_ }, fun _ _ => rfl⟩
    · intro ξ ξ'
      show starRingEnd ℝ (levelPairing (formValues ξ') (formValues ξ)) = levelPairing (formValues ξ) (formValues ξ')
      rw [conj_trivial, hcp, hcp, h0s ξ'.1 ξ.1]
      congr 1
      exact Finset.sum_congr rfl fun i _ => his i _ _
    · intro ξ
      show 0 ≤ RCLike.re (levelPairing (formValues ξ) (formValues ξ))
      rw [RCLike.re_to_real, hcp]
      exact add_nonneg (h0n _) (Finset.sum_nonneg fun i _ => hin i _)
    · intro ξ ξ' ζ
      show levelPairing (formValues (ξ + ξ')) (formValues ζ) =
        levelPairing (formValues ξ) (formValues ζ) + levelPairing (formValues ξ') (formValues ζ)
      rw [hcp, hcp, hcp]
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, c₀.add_left, (ci _).add_left,
        Finset.sum_add_distrib]
      ring
    · intro ξ ζ r
      show levelPairing (formValues (r • ξ)) (formValues ζ) =
        starRingEnd ℝ r * levelPairing (formValues ξ) (formValues ζ)
      rw [hcp, hcp, conj_trivial]
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, c₀.smul_left, (ci _).smul_left,
        conj_trivial, mul_add, Finset.mul_sum]
    · intro ξ h
      have h' : levelPairing (formValues ξ) (formValues ξ) = 0 := h
      rw [hcp] at h'
      obtain ⟨ha, hb⟩ := (add_eq_zero_iff_of_nonneg (h0n _)
        (Finset.sum_nonneg fun i _ => hin i _)).mp h'
      have hb' := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hin i _).mp hb
      exact Prod.ext (c₀.definite _ ha) (funext fun i => (ci i).definite _ (hb' i (Finset.mem_univ i)))
  obtain ⟨s, hps, hqs⟩ := exists_slot_section (L := L) (n := n) (k := k) hpos hL hn
  refine ⟨hC, hE _ le_rfl, slotLinearMap L n k, s,
    LinearMap.inr ℝ _ _ ∘ₗ LinearMap.single ℝ (fun i : Fin (k + 1) => edgeFormSpace L n (k + 1) (i + 1)) (Fin.last k),
    fun ξ => rfl, fun ξ ξ' => levelPairing_eq hpos hL hn ξ ξ', hps, hqs, ?_, ?_⟩
  · refine LinearMap.ext fun B => ?_
    ext ⟨j, e⟩
    obtain ⟨_ | j, h⟩ := j
    · show levelCoords (⟨0, h⟩ : Fin (k + 1)) (0 : Edge L n (k + 1) 0 → ComplexMatrix2) e = 0
      rw [levelCoords_zero]
      rfl
    · have hj : j < k := by omega
      have hne : (⟨j, Nat.lt_of_succ_lt h⟩ : Fin (k + 1)) ≠ Fin.last k := fun he =>
        absurd (congrArg Fin.val he) (by simp; omega)
      have h0 : (Pi.single (Fin.last k) B : (i : Fin (k + 1)) → edgeFormSpace L n (k + 1) (i + 1))
          ⟨j, Nat.lt_of_succ_lt h⟩ = 0 :=
        Pi.single_eq_of_ne (M := fun i : Fin (k + 1) => edgeFormSpace L n (k + 1) (i + 1)) hne B
      show levelCoords ⟨j + 1, h⟩
        (((Pi.single (Fin.last k) B : (i : Fin (k + 1)) → edgeFormSpace L n (k + 1) (i + 1))
          ⟨j, Nat.lt_of_succ_lt h⟩ : edgeFormSpace L n (k + 1) (j + 1)) : Edge L n (k + 1) (j + 1) → ComplexMatrix2) e = 0
      rw [h0]
      show levelCoords ⟨j + 1, h⟩ (0 : Edge L n (k + 1) (j + 1) → ComplexMatrix2) e = 0
      rw [levelCoords_zero]
      rfl
  · refine LinearMap.ext fun B => ?_
    exact Pi.single_eq_same (M := fun i : Fin (k + 1) => edgeFormSpace L n (k + 1) (i + 1)) (Fin.last k) B
end YangMills.Construction.RunningCouplingSlope
end
