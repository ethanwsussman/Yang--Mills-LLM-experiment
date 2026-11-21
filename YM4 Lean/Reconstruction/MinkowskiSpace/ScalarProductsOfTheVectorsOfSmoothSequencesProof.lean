import YangMills.Construction.Continuum.CompactSupportAndTensorsOfSeparatedTuples
import YangMills.Construction.HilbertSpaces.CompletionsAdjointsAndWeakIntegralsAreWellDefined
import Reconstruction.MinkowskiSpace.ProductsOfABoundedFieldForm
import Reconstruction.MinkowskiSpace.ScalarProductsOfTheVectorsOfSmoothSequences
import Reconstruction.MinkowskiSpace.VectorsOfSmoothSequencesLieInTheClosedSubspace
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Set
open scoped ComplexConjugate InnerProductSpace Topology ContDiff
noncomputable section
namespace YangMills.Construction.SmoothSeqInner
open MinkowskiSpace FieldForms ConfigSpace RealPointVectors WightmanTheory FieldFormHilbert
  ProjectionMeasures FormsOperators OneLoopNotation ComplexHilbert FormReconstruction
def revFlip {n : ℕ} (x : Fin n → Fin 4 → ℝ) : Fin n → Fin 4 → ℝ :=
  fun i => timeFlip (x (Fin.rev i))
theorem revFlip_involutive {n : ℕ} :
    Function.Involutive (revFlip (n := n)) := by
  intro x
  funext i
  simp [revFlip, timeFlip_timeFlip]
theorem continuous_timeFlip : Continuous timeFlip := by
  refine continuous_pi fun k => ?_
  fin_cases k <;> simp [timeFlip] <;> fun_prop
theorem continuous_revFlip {n : ℕ} :
    Continuous (revFlip (n := n)) :=
  continuous_pi fun _ => continuous_timeFlip.comp (continuous_apply _)
theorem measurePreserving_timeFlip :
    MeasurePreserving timeFlip (volume : Measure (Fin 4 → ℝ)) volume := by
  have h := MeasureTheory.volume_preserving_pi
    (f := fun i : Fin 4 => if i = 3 then (fun t : ℝ => -t) else id)
    (fun i => by
      by_cases hi : i = 3
      · simpa [hi] using Measure.measurePreserving_neg (volume : Measure ℝ)
      · simpa [hi] using MeasurePreserving.id (volume : Measure ℝ))
  have e : timeFlip = fun (a : Fin 4 → ℝ) i =>
      (if i = 3 then (fun t : ℝ => -t) else id) (a i) := by
    funext u k
    fin_cases k <;> simp [timeFlip]
  rw [e]
  exact h
theorem measurePreserving_revFlip {n : ℕ} :
    MeasurePreserving (revFlip (n := n)) volume volume := by
  have h₁ : MeasurePreserving (fun (x : Fin n → Fin 4 → ℝ) i => timeFlip (x i))
      volume volume :=
    MeasureTheory.volume_preserving_pi (fun _ => measurePreserving_timeFlip)
  have h₂ := volume_measurePreserving_piCongrLeft (fun _ : Fin n => Fin 4 → ℝ) Fin.revPerm
  convert h₁.comp h₂ using 1
  funext x i
  simp only [Function.comp, revFlip]
  congr 1
  obtain ⟨j, rfl⟩ := Fin.revPerm.surjective i
  simp only [Fin.revPerm_apply, Fin.rev_rev, MeasurableEquiv.coe_piCongrLeft]
  exact (Equiv.piCongrLeft_apply_apply (fun _ : Fin n => Fin 4 → ℝ) Fin.revPerm x j).symm
theorem measurePreserving_concatConfig {n n' : ℕ} :
    MeasurePreserving
      (fun p : (Fin n → Fin 4 → ℝ) × (Fin n' → Fin 4 → ℝ) => concatConfig p.1 p.2)
      volume volume := by
  have h₁ := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin n ⊕ Fin n' => Fin 4 → ℝ)
  have h₂ := volume_measurePreserving_piCongrLeft (fun _ : Fin (n + n') => Fin 4 → ℝ)
    (finSumFinEquiv (m := n) (n := n'))
  convert h₂.comp h₁ using 1
  funext p i
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  rcases s with i | j
  · simp only [finSumFinEquiv_apply_left, concatConfig, Fin.append_left, Function.comp,
      MeasurableEquiv.coe_piCongrLeft]
    exact (Equiv.piCongrLeft_apply_apply (fun _ : Fin (n + n') => Fin 4 → ℝ) finSumFinEquiv
      ((MeasurableEquiv.sumPiEquivProdPi fun _ => Fin 4 → ℝ).symm p) (Sum.inl i)).symm
  · simp only [finSumFinEquiv_apply_right, concatConfig, Fin.append_right, Function.comp,
      MeasurableEquiv.coe_piCongrLeft]
    exact (Equiv.piCongrLeft_apply_apply (fun _ : Fin (n + n') => Fin 4 → ℝ) finSumFinEquiv
      ((MeasurableEquiv.sumPiEquivProdPi fun _ => Fin 4 → ℝ).symm p) (Sum.inr j)).symm
def flipConcat {n n' : ℕ} (p : (Fin n → Fin 4 → ℝ) × (Fin n' → Fin 4 → ℝ)) :
    Fin (n + n') → Fin 4 → ℝ :=
  concatConfig (revFlip p.1) p.2
theorem measurePreserving_flipConcat {n n' : ℕ} :
    MeasurePreserving (flipConcat (n := n) (n' := n')) volume volume := by
  have h : MeasurePreserving
      (Prod.map (revFlip (n := n)) (id : (Fin n' → Fin 4 → ℝ) → _)) volume volume :=
    measurePreserving_revFlip.prod (MeasurePreserving.id _)
  exact measurePreserving_concatConfig.comp h
theorem revFlip_headArgs_flipConcat {n n' : ℕ} (x : Fin n → Fin 4 → ℝ) (y : Fin n' → Fin 4 → ℝ) :
    revFlip (headArgs (flipConcat (x, y))) = x := by
  simp [flipConcat, headArgs_concatConfig, revFlip_involutive x]
theorem tailArgs_flipConcat {n n' : ℕ} (x : Fin n → Fin 4 → ℝ) (y : Fin n' → Fin 4 → ℝ) :
    tailArgs (flipConcat (x, y)) = y := by
  simp [flipConcat, tailArgs_concatConfig]
theorem flipConcat_revFlip_headArgs_tailArgs {n n' : ℕ} (w : Fin (n + n') → Fin 4 → ℝ) :
    flipConcat (revFlip (headArgs w), tailArgs w) = w := by
  simp [flipConcat, revFlip_involutive _, concatConfig_headArgs_tailArgs]
theorem continuous_concatConfig {n n' : ℕ} :
    Continuous
      (fun p : (Fin n → Fin 4 → ℝ) × (Fin n' → Fin 4 → ℝ) => concatConfig p.1 p.2) := by
  refine continuous_pi fun i => ?_
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [concatConfig, Fin.append_left]
    fun_prop
  · simp only [concatConfig, Fin.append_right]
    fun_prop
theorem continuous_flipConcat {n n' : ℕ} :
    Continuous (flipConcat (n := n) (n' := n')) :=
  continuous_concatConfig.comp
    ((continuous_revFlip.comp continuous_fst).prodMk continuous_snd)
theorem time_pos_of_mem {n : ℕ} {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ TestSpaces.increasingPositiveTimes n) (i : Fin n) : 0 < x i 3 := by
  have h0 : 0 < n := i.pos
  have h1 : 0 < x ⟨0, h0⟩ 3 := hx.2 h0
  have h2 : x ⟨0, h0⟩ 3 ≤ x i 3 := hx.1.monotone (Fin.mk_le_of_le_val (Nat.zero_le _))
  exact lt_of_lt_of_le h1 h2
theorem flipConcat_castAdd {n n' : ℕ} (x : Fin n → Fin 4 → ℝ) (y : Fin n' → Fin 4 → ℝ)
    (a : Fin n) : flipConcat (x, y) (Fin.castAdd n' a) 3 = -x (Fin.rev a) 3 := by
  simp [flipConcat, concatConfig, revFlip, timeFlip]
theorem flipConcat_natAdd {n n' : ℕ} (x : Fin n → Fin 4 → ℝ) (y : Fin n' → Fin 4 → ℝ)
    (b : Fin n') : flipConcat (x, y) (Fin.natAdd n b) = y b := by
  simp [flipConcat, concatConfig]
theorem flipConcat_mem_increasingTimes {n n' : ℕ} {x : Fin n → Fin 4 → ℝ}
    {y : Fin n' → Fin 4 → ℝ} (hx : x ∈ TestSpaces.increasingPositiveTimes n)
    (hy : y ∈ TestSpaces.increasingPositiveTimes n') :
    flipConcat (x, y) ∈ TestSpaces.increasingTimes (n + n') := by
  intro i j hij
  change flipConcat (x, y) i 3 < flipConcat (x, y) j 3
  induction i using Fin.addCases with
  | left a =>
    induction j using Fin.addCases with
    | left a' =>
      rw [flipConcat_castAdd, flipConcat_castAdd]
      have h : a < a' := hij
      have h' : x (Fin.rev a') 3 < x (Fin.rev a) 3 := hx.1 (Fin.rev_lt_rev.2 h)
      linarith
    | right b =>
      rw [flipConcat_castAdd, flipConcat_natAdd]
      have h₁ := time_pos_of_mem hx (Fin.rev a)
      have h₂ := time_pos_of_mem hy b
      linarith
  | right b =>
    induction j using Fin.addCases with
    | left a =>
      exfalso
      simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at hij
      omega
    | right b' =>
      rw [flipConcat_natAdd, flipConcat_natAdd]
      have h0 : n + b.val < n + b'.val := hij
      have h : b < b' := Nat.lt_of_add_lt_add_left h0
      exact hy.1 h
def wickOfReal {n : ℕ} (x : Fin n → Fin 4 → ℝ) : Fin n → ComplexVec4 :=
  wickMapTuple (tupleToComplex x)
theorem conjPoint_wickMap (u : Fin 4 → ℝ) :
    MinkowskiSpace.conjPoint (wickMap (toComplex u)) =
      wickMap (toComplex (timeFlip u)) := by
  funext μ
  fin_cases μ <;>
    simp [MinkowskiSpace.conjPoint, MinkowskiSpace.rePart, MinkowskiSpace.imPart, toComplex,
      wickMap, timeFlip]
theorem wickOfReal_mem_diffCoordsInTube {n : ℕ} {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ TestSpaces.increasingPositiveTimes n) : wickOfReal x ∈ diffCoordsInTube n := by
  cases n with
  | zero => intro i; exact i.elim0
  | succ n =>
    intro i _
    change diffCoords (wickOfReal x) i ∈ futureTube
    refine Fin.cases ?_ (fun i => ?_) i
    · have him : MinkowskiSpace.imPart (diffCoords (wickOfReal x) 0) = mkTimeSpace (x 0 3) 0 := by
        funext μ
        fin_cases μ <;>
          simp [MinkowskiSpace.imPart, MinkowskiSpace.diffCoords, wickOfReal, wickMapTuple, tupleToComplex,
            wickMap, toComplex, mkTimeSpace, Fin.cons]
        all_goals rfl
      change coneGap (MinkowskiSpace.imPart (diffCoords (wickOfReal x) 0)) > 0
      rw [him]
      simpa [coneGap, spacePart, mkTimeSpace, spaceNorm] using time_pos_of_mem hx 0
    · exact wickDiffs_mem_futureTube hx.1 i
theorem continuous_wickOfReal {n : ℕ} : Continuous (wickOfReal (n := n)) := by
  refine continuous_pi fun i => ?_
  have h₁ : Continuous (wickMap : ComplexVec4 → ComplexVec4) :=
    wickMap.toLinearMap.continuous_of_finiteDimensional
  have h₂ : Continuous (toComplex : RealVec4 → ComplexVec4) :=
    continuous_pi fun μ => Complex.continuous_ofReal.comp (continuous_apply μ)
  exact h₁.comp (h₂.comp (continuous_apply i))
section States
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : FourBorelSet → BddOp K} {Ω : K} {A : ℝ → BddOp K}
variable (E Ω A) in
def stateAt (n : ℕ) (x : Fin n → Fin 4 → ℝ) : K := stateVector E Ω A n (wickOfReal x)
variable (E Ω A) in
def expectationAt (n : ℕ) (x : Fin n → Fin 4 → ℝ) : ℂ :=
  vacuumExpectation E Ω A n (successiveDiffsOfLength n (wickOfReal x))
theorem inner_stateAt (hsp : StatesTranslateInner E Ω A) {n n' : ℕ}
    {x : Fin n → Fin 4 → ℝ} {y : Fin n' → Fin 4 → ℝ}
    (hx : x ∈ TestSpaces.increasingPositiveTimes n)
    (hy : y ∈ TestSpaces.increasingPositiveTimes n') :
    inner ℂ (stateAt E Ω A n x) (stateAt E Ω A n' y) =
      expectationAt E Ω A (n + n') (flipConcat (x, y)) := by
  have h0 : MinkowskiSpace.imPart (0 : ComplexVec4) ∈ closedFutureCone := by
    change coneGap _ ≥ 0
    have : MinkowskiSpace.imPart (0 : ComplexVec4) = 0 := by
      funext μ
      simp [MinkowskiSpace.imPart]
    rw [this]
    simp [coneGap, spacePart, spaceNorm]
  have h := (hsp n' n (wickOfReal y) (wickOfReal x) 0 (wickOfReal_mem_diffCoordsInTube hy)
    (wickOfReal_mem_diffCoordsInTube hx) h0).2.2
  have happ : (Fin.append (fun k => MinkowskiSpace.conjPoint (wickOfReal x (Fin.rev k)))
      (wickOfReal y) : Fin (n + n') → ComplexVec4) = wickOfReal (flipConcat (x, y)) := by
    funext i
    induction i using Fin.addCases with
    | left a =>
      simp [wickOfReal, wickMapTuple, tupleToComplex, flipConcat, concatConfig,
        revFlip, conjPoint_wickMap]
    | right b =>
      simp [wickOfReal, wickMapTuple, tupleToComplex, flipConcat, concatConfig]
  rw [happ] at h
  exact h
theorem continuousOn_stateAt
    (hc : ∀ n : ℕ, ContinuousOn (stateVector E Ω A (n + 1)) (diffCoordsInTube (n + 1)))
    (n : ℕ) : ContinuousOn (stateAt E Ω A n) (TestSpaces.increasingPositiveTimes n) := by
  cases n with
  | zero => exact continuousOn_const
  | succ n =>
    exact (hc n).comp continuous_wickOfReal.continuousOn fun x hx =>
      wickOfReal_mem_diffCoordsInTube hx
end States
section Paired
variable {n n' : ℕ} {f : (Fin n → Fin 4 → ℝ) → ℂ} {g : (Fin n' → Fin 4 → ℝ) → ℂ}
def pairedFn (f : (Fin n → Fin 4 → ℝ) → ℂ) (g : (Fin n' → Fin 4 → ℝ) → ℂ)
    (w : Fin (n + n') → Fin 4 → ℝ) : ℂ :=
  conj (f (revFlip (headArgs w))) * g (tailArgs w)
theorem pairedFn_flipConcat (f : (Fin n → Fin 4 → ℝ) → ℂ)
    (g : (Fin n' → Fin 4 → ℝ) → ℂ) (x : Fin n → Fin 4 → ℝ) (y : Fin n' → Fin 4 → ℝ) :
    pairedFn f g (flipConcat (x, y)) = conj (f x) * g y := by
  simp [pairedFn, revFlip_headArgs_flipConcat, tailArgs_flipConcat]
theorem contDiff_coord {N : ℕ} (a : Fin N) (b : Fin 4) :
    ContDiff ℝ ∞ fun w : Fin N → Fin 4 → ℝ => w a b :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) b).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Fin 4 → ℝ) a)).contDiff
theorem contDiff_revFlip_headArgs :
    ContDiff ℝ ∞ fun w : Fin (n + n') → Fin 4 → ℝ => revFlip (headArgs w) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun k => ?_
  fin_cases k
  · exact contDiff_coord _ _
  · exact contDiff_coord _ _
  · exact contDiff_coord _ _
  · exact (contDiff_coord _ _).neg
theorem contDiff_tailArgs :
    ContDiff ℝ ∞ fun w : Fin (n + n') → Fin 4 → ℝ => (tailArgs w : Fin n' → Fin 4 → ℝ) :=
  contDiff_pi.2 fun _ => contDiff_pi.2 fun _ => contDiff_coord _ _
theorem contDiff_pairedFn (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (pairedFn f g) :=
  (Complex.conjCLE.contDiff.comp (hf.comp contDiff_revFlip_headArgs)).mul
    (hg.comp contDiff_tailArgs)
theorem tsupport_pairedFn_subset (hf : IsCompact (tsupport f)) (hg : IsCompact (tsupport g)) :
    tsupport (pairedFn f g) ⊆ flipConcat '' (tsupport f ×ˢ tsupport g) := by
  refine closure_minimal ?_ ((hf.prod hg).image continuous_flipConcat).isClosed
  intro w hw
  have hw' : pairedFn f g w ≠ 0 := hw
  refine ⟨(revFlip (headArgs w), tailArgs w), ⟨?_, ?_⟩,
    flipConcat_revFlip_headArgs_tailArgs w⟩
  · refine subset_tsupport _ ?_
    intro h0
    exact hw' (by simp [pairedFn, show f (revFlip (headArgs w)) = 0 from h0])
  · refine subset_tsupport _ ?_
    intro h0
    exact hw' (by simp [pairedFn, show g (tailArgs w) = 0 from h0])
theorem pairedFn_mem
    (hf : f ∈ (TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes n) :
      Set ((Fin n → Fin 4 → ℝ) → ℂ)))
    (hg : g ∈ (TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes n') :
      Set ((Fin n' → Fin 4 → ℝ) → ℂ))) :
    pairedFn f g ∈ (TestSpaces.smoothCompactSupp (TestSpaces.increasingTimes (n + n')) :
      Set ((Fin (n + n') → Fin 4 → ℝ) → ℂ)) := by
  have hsub := tsupport_pairedFn_subset hf.2.1 hg.2.1
  refine ⟨contDiff_pairedFn hf.1 hg.1, ?_, ?_⟩
  · exact IsCompact.of_isClosed_subset
      ((IsCompact.prod hf.2.1 hg.2.1).image continuous_flipConcat) (isClosed_tsupport _) hsub
  · refine hsub.trans ?_
    rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact flipConcat_mem_increasingTimes (hf.2.2 hx) (hg.2.2 hy)
variable (n n') in
def revHeadPerm : Equiv.Perm (Fin (n + n')) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr Fin.revPerm (Equiv.refl _)).trans finSumFinEquiv)
theorem revHeadPerm_castAdd (a : Fin n) :
    revHeadPerm n n' (Fin.castAdd n' a) = Fin.castAdd n' (Fin.rev a) := by
  simp [revHeadPerm]
theorem revHeadPerm_natAdd (b : Fin n') :
    revHeadPerm n n' (Fin.natAdd n b) = Fin.natAdd n b := by
  simp [revHeadPerm]
theorem permAct_pairedFn (f : (Fin n → Fin 4 → ℝ) → ℂ)
    (g : (Fin n' → Fin 4 → ℝ) → ℂ) :
    permAct (revHeadPerm n n') (pairedFn f g) = tensorFn (flipConj f) g := by
  funext w
  have h₁ : revFlip (headArgs fun i => w (revHeadPerm n n' i)) =
      fun i => timeFlip (headArgs w i) := by
    funext i
    simp [revFlip, headArgs, revHeadPerm_castAdd]
  have h₂ : (tailArgs fun i => w (revHeadPerm n n' i)) = tailArgs w := by
    funext j
    simp [tailArgs, revHeadPerm_natAdd]
  simp only [permAct, pairedFn, tensorFn, flipConj, h₁, h₂]
end Paired
section Integrals
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : FourBorelSet → BddOp K} {Ω : K} {A : ℝ → BddOp K}
  {n n' : ℕ} {f : (Fin n → Fin 4 → ℝ) → ℂ} {g : (Fin n' → Fin 4 → ℝ) → ℂ}
theorem integrable_pairIntegrand
    (hc : ∀ n : ℕ, ContinuousOn (stateVector E Ω A (n + 1)) (diffCoordsInTube (n + 1)))
    (hf : f ∈ (TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes n) :
      Set ((Fin n → Fin 4 → ℝ) → ℂ)))
    (hg : g ∈ (TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes n') :
      Set ((Fin n' → Fin 4 → ℝ) → ℂ))) :
    Integrable (fun p : (Fin n → Fin 4 → ℝ) × (Fin n' → Fin 4 → ℝ) =>
      conj (f p.1) * g p.2 * inner ℂ (stateAt E Ω A n p.1) (stateAt E Ω A n' p.2)) := by
  set F : (Fin n → Fin 4 → ℝ) × (Fin n' → Fin 4 → ℝ) → ℂ := fun p =>
    conj (f p.1) * g p.2 * inner ℂ (stateAt E Ω A n p.1) (stateAt E Ω A n' p.2) with hF
  have hsupp : tsupport F ⊆ tsupport f ×ˢ tsupport g := by
    refine closure_minimal ?_ ((isClosed_tsupport _).prod (isClosed_tsupport _))
    rintro ⟨x, y⟩ hp
    have hp' : F (x, y) ≠ 0 := hp
    refine ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩
    · intro h0
      exact hp' (by simp [hF, show f x = 0 from h0])
    · intro h0
      exact hp' (by simp [hF, show g y = 0 from h0])
  have hopen : IsOpen (TestSpaces.increasingPositiveTimes n ×ˢ
      TestSpaces.increasingPositiveTimes n') :=
    (TestSpaces.isOpen_increasingPositiveTimes n).prod
      (TestSpaces.isOpen_increasingPositiveTimes n')
  have hcont : ContinuousOn F
      (TestSpaces.increasingPositiveTimes n ×ˢ TestSpaces.increasingPositiveTimes n') := by
    have h₁ : ContinuousOn (fun p : (Fin n → Fin 4 → ℝ) × (Fin n' → Fin 4 → ℝ) =>
        stateAt E Ω A n p.1)
        (TestSpaces.increasingPositiveTimes n ×ˢ TestSpaces.increasingPositiveTimes n') :=
      (continuousOn_stateAt hc n).comp continuous_fst.continuousOn fun p hp => hp.1
    have h₂ : ContinuousOn (fun p : (Fin n → Fin 4 → ℝ) × (Fin n' → Fin 4 → ℝ) =>
        stateAt E Ω A n' p.2)
        (TestSpaces.increasingPositiveTimes n ×ˢ TestSpaces.increasingPositiveTimes n') :=
      (continuousOn_stateAt hc n').comp continuous_snd.continuousOn fun p hp => hp.2
    have hfc : Continuous f := hf.1.continuous
    have hgc : Continuous g := hg.1.continuous
    have h₃ : Continuous (fun p : (Fin n → Fin 4 → ℝ) × (Fin n' → Fin 4 → ℝ) =>
        conj (f p.1) * g p.2) :=
      (Complex.continuous_conj.comp (hfc.comp continuous_fst)).mul (hgc.comp continuous_snd)
    exact h₃.continuousOn.mul (h₁.inner h₂)
  have hFc : Continuous F := by
    refine continuous_of_tsupport fun p hp => ?_
    have hp' := hsupp hp
    exact hcont.continuousAt (hopen.mem_nhds ⟨hf.2.2 hp'.1, hg.2.2 hp'.2⟩)
  have hFs : HasCompactSupport F :=
    IsCompact.of_isClosed_subset (IsCompact.prod hf.2.1 hg.2.1) (isClosed_tsupport _) hsupp
  exact hFc.integrable_of_hasCompactSupport hFs
theorem inner_eq_integral_prod
    (hc : ∀ n : ℕ, ContinuousOn (stateVector E Ω A (n + 1)) (diffCoordsInTube (n + 1)))
    (hf : f ∈ (TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes n) :
      Set ((Fin n → Fin 4 → ℝ) → ℂ)))
    (hg : g ∈ (TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes n') :
      Set ((Fin n' → Fin 4 → ℝ) → ℂ)))
    {v v' : K} (hv : HasWeakIntegral (tsupport f) (stateAt E Ω A n) f v)
    (hv' : HasWeakIntegral (tsupport g) (stateAt E Ω A n') g v') :
    inner ℂ v v' = ∫ p : (Fin n → Fin 4 → ℝ) × (Fin n' → Fin 4 → ℝ),
      conj (f p.1) * g p.2 * inner ℂ (stateAt E Ω A n p.1) (stateAt E Ω A n' p.2) := by
  have hin : ∀ y, inner ℂ v (stateAt E Ω A n' y) =
      ∫ x, conj (f x) * inner ℂ (stateAt E Ω A n x) (stateAt E Ω A n' y) := by
    intro y
    have h := hv (stateAt E Ω A n' y)
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])] at h
    rw [← inner_conj_symm, h, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [inner_conj_symm]
  rw [hv' v, setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun y hy => by rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]),
    Measure.volume_eq_prod, integral_prod_symm _ (integrable_pairIntegrand hc hf hg)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [hin y, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring
def flipConcatHomeomorph (n n' : ℕ) :
    ((Fin n → Fin 4 → ℝ) × (Fin n' → Fin 4 → ℝ)) ≃ₜ (Fin (n + n') → Fin 4 → ℝ) where
  toFun := flipConcat
  invFun w := (revFlip (headArgs w), tailArgs w)
  left_inv p := Prod.ext (revFlip_headArgs_flipConcat p.1 p.2) (tailArgs_flipConcat p.1 p.2)
  right_inv := flipConcat_revFlip_headArgs_tailArgs
  continuous_toFun := continuous_flipConcat
  continuous_invFun :=
    (continuous_revFlip.comp
      (continuous_pi fun _ => continuous_apply _)).prodMk (continuous_pi fun _ => continuous_apply _)
theorem integral_pairedFn (hsp : StatesTranslateInner E Ω A)
    (hf : f ∈ (TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes n) :
      Set ((Fin n → Fin 4 → ℝ) → ℂ)))
    (hg : g ∈ (TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes n') :
      Set ((Fin n' → Fin 4 → ℝ) → ℂ))) :
    ∫ w, (TestSpaces.increasingTimes (n + n')).indicator
        (fun w => pairedFn f g w * expectationAt E Ω A (n + n') w) w =
      ∫ p : (Fin n → Fin 4 → ℝ) × (Fin n' → Fin 4 → ℝ),
        conj (f p.1) * g p.2 * inner ℂ (stateAt E Ω A n p.1) (stateAt E Ω A n' p.2) := by
  rw [← measurePreserving_flipConcat.integral_comp
    (flipConcatHomeomorph n n').measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
  rintro ⟨x, y⟩
  by_cases hx : x ∈ tsupport f
  · by_cases hy : y ∈ tsupport g
    · have hx' := hf.2.2 hx
      have hy' := hg.2.2 hy
      simp only
      rw [indicator_of_mem (flipConcat_mem_increasingTimes hx' hy'), pairedFn_flipConcat,
        inner_stateAt hsp hx' hy']
    · simp [pairedFn_flipConcat, image_eq_zero_of_notMem_tsupport hy]
  · simp [pairedFn_flipConcat, image_eq_zero_of_notMem_tsupport hx]
end Integrals
section Terms
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : FourBorelSet → BddOp K} {Ω : K} {A : ℝ → BddOp K}
theorem integral_fin_zero (h : (Fin 0 → Fin 4 → ℝ) → ℂ) :
    ∫ x, h x = h (fun i => i.elim0) := by
  have hv : (volume : Measure (Fin 0 → Fin 4 → ℝ)) = Measure.dirac (fun i => i.elim0) := by
    rw [volume_pi]
    exact Measure.pi_of_empty _ _
  rw [hv, integral_dirac]
theorem hasWeakIntegral_zero_degree (c : ℂ) :
    HasWeakIntegral (tsupport fun _ : Fin 0 → Fin 4 → ℝ => c) (stateAt E Ω A 0) (fun _ => c)
      (c • Ω) := by
  intro χ
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have h0 : c = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [h0]), integral_fin_zero]
  simp [stateAt, stateVector]
theorem toConfigFn_cast {N M : ℕ} (h : N = M) (ψ : FnOrScalar N)
    (z : Fin M → Fin 4 → ℝ) :
    toConfigFn (h ▸ ψ) z = toConfigFn ψ (fun i => z (Fin.cast h i)) := by
  subst h
  rfl
theorem tensorAt_flipConjAt_succ {n b : ℕ} (a : FnOrScalar n)
    (c : FnOrScalar (b + 1)) :
    tensorAt (flipConjAt a) c =
      tensorFn (p := n) (p' := b + 1) (flipConj (toConfigFn a)) c := by
  cases n with
  | zero =>
    refine funext fun z => ?_
    refine (toConfigFn_cast (Nat.zero_add (b + 1)).symm
      (smulAt (flipConjAt (n := 0) a) c) z).trans ?_
    have hl : (fun i => z (Fin.cast (Nat.zero_add (b + 1)).symm i)) =
        (tailArgs (p := 0) (p' := b + 1) z : Fin (b + 1) → Fin 4 → ℝ) := by
      funext i
      simp only [tailArgs]
      congr 1
      ext
      simp
    rw [hl]
    rfl
  | succ n => rfl
theorem tensorAt_flipConjAt_zero {n : ℕ} (a : FnOrScalar (n + 1)) (c : FnOrScalar 0) :
    tensorAt (flipConjAt a) c =
      tensorFn (p := n + 1) (p' := 0) (flipConj a) (toConfigFn c) := by
  refine funext fun z => ?_
  have hf : (headArgs (p := n + 1) (p' := 0) z : Fin (n + 1) → Fin 4 → ℝ) = z := by
    funext i
    simp [headArgs]
  change (show ℂ from c) * flipConj a z =
    flipConj a (headArgs (p := n + 1) (p' := 0) z) * (show ℂ from c)
  rw [hf, mul_comm]
theorem evalAt_permAct (hcs : CompactSupportTensorFacts)
    (hop : OperationsPreserveSchwartzSpaces) {S : FlatSequence}
    (hsym : IsPermSymmetric S) (hrep : RepresentsSequence E Ω A S) (m : ℕ)
    {P : (Fin (m + 1) → Fin 4 → ℝ) → ℂ}
    (hP : P ∈ (TestSpaces.smoothCompactSupp (TestSpaces.increasingTimes (m + 1)) :
      Set ((Fin (m + 1) → Fin 4 → ℝ) → ℂ)))
    (σ : Equiv.Perm (Fin (m + 1))) :
    S.evalAt (n := m + 1) (permAct σ P) = orderedIntegral E Ω A m P := by
  have hone : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  have hnd : P ∈ schwartzFlatOffDiagonal (m + 1) :=
    (hcs (m + 1) hone).2.1
      ⟨isOpen_distinctArgs, hP.1, hP.2.1, hP.2.2.trans fun x hx i j e =>
        StrictMono.injective hx (congrArg (fun u : Fin 4 → ℝ => u 3) e)⟩
  have hperm : permAct σ P ∈ schwartzFlatOffDiagonal (m + 1) :=
    ((hop (m + 1) hone).1 P hnd timeFlipMotion σ).2
  have hval : S.evalAt (n := m + 1) (permAct σ P) =
      S.atSucc m ⟨_, hperm⟩ := S.evalAt_of_mem (n := m + 1) (f := permAct σ P) hperm
  rw [hval, hsym m ⟨P, hnd⟩ σ hperm]
  exact hrep.2 m P hP hnd
theorem evalAt_tensorAt_eq_inner (hcs : CompactSupportTensorFacts)
    (hop : OperationsPreserveSchwartzSpaces)
    (hsp : StatesTranslateInner E Ω A)
    (hcont : ∀ n : ℕ, ContinuousOn (stateVector E Ω A (n + 1)) (diffCoordsInTube (n + 1)))
    (hΩ : ‖Ω‖ = 1) {S : FlatSequence}
    (hsym : IsPermSymmetric S) (hrep : RepresentsSequence E Ω A S)
    {n n' : ℕ} (a : FnOrScalar n) (c : FnOrScalar n')
    (ha : toConfigFn a ∈
      (TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes n) :
        Set ((Fin n → Fin 4 → ℝ) → ℂ)))
    (hc : toConfigFn c ∈
      (TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes n') :
        Set ((Fin n' → Fin 4 → ℝ) → ℂ)))
    {v v' : K}
    (hv : HasWeakIntegral (tsupport (toConfigFn a)) (stateAt E Ω A n) (toConfigFn a) v)
    (hv' : HasWeakIntegral (tsupport (toConfigFn c)) (stateAt E Ω A n') (toConfigFn c) v') :
    S.evalAt (tensorAt (flipConjAt a) c) = inner ℂ v v' := by
  have hint := (inner_eq_integral_prod hcont ha hc hv hv').trans
    (integral_pairedFn hsp ha hc).symm
  cases n' with
  | succ b =>
    rw [hint, tensorAt_flipConjAt_succ a c]
    have hp := permAct_pairedFn (toConfigFn a) (toConfigFn (n := b + 1) c)
    refine (congrArg (S.evalAt (n := n + b + 1)) hp.symm).trans ?_
    exact evalAt_permAct hcs hop hsym hrep (n + b)
      (pairedFn_mem (n := n) (n' := b + 1) ha hc) _
  | zero =>
    cases n with
    | succ n =>
      rw [hint, tensorAt_flipConjAt_zero a c]
      have hp := permAct_pairedFn (toConfigFn (n := n + 1) a) (toConfigFn c)
      refine (congrArg (S.evalAt (n := n + 1)) hp.symm).trans ?_
      exact evalAt_permAct hcs hop hsym hrep n
        (pairedFn_mem (n := n + 1) (n' := 0) ha hc) _
    | zero =>
      have ev : v = (show ℂ from a) • Ω := ext_inner_left ℂ fun χ => by
        rw [hv χ]
        exact (hasWeakIntegral_zero_degree (E := E) (A := A) (Ω := Ω) (show ℂ from a) χ).symm
      have ev' : v' = (show ℂ from c) • Ω := ext_inner_left ℂ fun χ => by
        rw [hv' χ]
        exact (hasWeakIntegral_zero_degree (E := E) (A := A) (Ω := Ω) (show ℂ from c) χ).symm
      have hval := S.evalAt_of_mem (n := 0)
        (f := (conj (show ℂ from a) * (show ℂ from c) : ℂ)) (Set.mem_univ _)
      have hS := hrep.1.1 ⟨(conj (show ℂ from a) * (show ℂ from c) : ℂ), Set.mem_univ _⟩
      refine (hval.trans hS).trans ?_
      rw [ev, ev', inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, hΩ]
      simp
      exact congrArg (fun t : ℂ => conj (show ℂ from a) * t) (mul_one (show ℂ from c)).symm
end Terms
section Sum
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K)
def stateTerm (Ψ : AdmissibleSeq) : ℕ → K
  | 0 => zerothScalar Ψ • Ω
  | q + 1 => weakInt (tsupport (succMember Ψ q)) (wickStateAt E Ω A q) (succMember Ψ q)
theorem seqValues_mem {Ψ : AdmissibleSeq} (hΨ : IsSmoothPositiveTimeSeq Ψ)
    (n : ℕ) : toConfigFn (seqValues Ψ n) ∈
      (TestSpaces.smoothCompactSupp (TestSpaces.increasingPositiveTimes n) :
        Set ((Fin n → Fin 4 → ℝ) → ℂ)) := by
  cases n with
  | zero =>
    refine ⟨contDiff_const, (Set.toFinite _).isCompact, fun x _ => ⟨fun i => i.elim0, ?_⟩⟩
    intro h
    exact absurd h (lt_irrefl 0)
  | succ q => exact hΨ q
variable {E Ω A}
theorem hasWeakIntegral_stateTerm
    (hw : HilbertWellDefined.WeakIntegralUnique)
    {Ψ : AdmissibleSeq}
    (hd : ∀ q : ℕ, HasWeakIntegrandData (tsupport (succMember Ψ q))
      (wickStateAt E Ω A q) (succMember Ψ q)) (n : ℕ) :
    HasWeakIntegral (tsupport (toConfigFn (seqValues Ψ n))) (stateAt E Ω A n)
      (toConfigFn (seqValues Ψ n)) (stateTerm E Ω A Ψ n) := by
  cases n with
  | zero => exact hasWeakIntegral_zero_degree _
  | succ q => exact (hw K _ _ _ _ (hd q)).1
theorem eq_zero_of_hasWeakIntegral_zero {n : ℕ} {f : (Fin n → Fin 4 → ℝ) → ℂ} {u : K}
    {C : Set (Fin n → Fin 4 → ℝ)}
    (hf : f = 0) (hu : HasWeakIntegral C (stateAt E Ω A n) f u) : u = 0 := by
  refine inner_self_eq_zero (𝕜 := ℂ).1 ?_
  rw [hu u, hf]
  simp
theorem toConfigFn_zeroOfDegree (n : ℕ) :
    toConfigFn (zeroOfDegree n) = (0 : (Fin n → Fin 4 → ℝ) → ℂ) := by
  cases n <;> rfl
theorem exists_seqValues_eq_zero (Ψ : AdmissibleSeq) :
    ∃ M : ℕ, ∀ n, M ≤ n → seqValues Ψ n = zeroOfDegree n := by
  obtain ⟨B, hB⟩ := Ψ.2.bddAbove
  refine ⟨B + 1, fun n hn => ?_⟩
  by_contra h
  have := hB h
  omega
theorem smoothSeqState_eq_sum {Ψ : AdmissibleSeq} {M : ℕ}
    (hz : ∀ n, M ≤ n → stateTerm E Ω A Ψ n = 0) :
    smoothSeqState E Ω A Ψ = ∑ n ∈ Finset.range (M + 1), stateTerm E Ω A Ψ n := by
  rw [Finset.sum_range_succ', smoothSeqState, add_comm]
  congr 1
  refine finsum_eq_sum_of_support_subset _ ?_
  intro q hq
  by_contra hqM
  have hqM' : M ≤ q + 1 := by
    have : ¬ q < M := by simpa using hqM
    omega
  exact hq (hz (q + 1) hqM')
end Sum
theorem smoothSeqState_inner_holds (hcs : CompactSupportTensorFacts)
    (hop : OperationsPreserveSchwartzSpaces)
    (hwell : HilbertWellDefined.WellDefinedStatement)
    (hprod : FieldProductProperties)
    (hvec : MinkowskiSpace.SmoothSeqStateMemTensorHilbert) :
    MinkowskiSpace.SmoothSeqState_inner := by
  intro S hsym K _ _ _ E Ω A ℘ C hform hrep Φ Φ' hΦ hΦ'
  obtain ⟨-, -, -, -, -, -, -, hhol, -, hsp, -⟩ := hprod K E Ω A ℘ C hform
  have hcont : ∀ n : ℕ, ContinuousOn (stateVector E Ω A (n + 1)) (diffCoordsInTube (n + 1)) :=
    fun n => (hhol n).2.2.2.2
  have hw := hwell.2.2.2
  have hd := (hvec E Ω A ℘ C hform Φ hΦ).1
  have hd' := (hvec E Ω A ℘ C hform Φ' hΦ').1
  have hu := hasWeakIntegral_stateTerm hw hd
  have hu' := hasWeakIntegral_stateTerm hw hd'
  obtain ⟨M₁, hM₁⟩ := exists_seqValues_eq_zero Φ
  obtain ⟨M₂, hM₂⟩ := exists_seqValues_eq_zero Φ'
  set M := max M₁ M₂ with hM
  have hz : ∀ n, M ≤ n → stateTerm E Ω A Φ n = 0 := fun n hn =>
    eq_zero_of_hasWeakIntegral_zero
      (by rw [hM₁ n (le_trans (le_max_left _ _) hn), toConfigFn_zeroOfDegree]) (hu n)
  have hz' : ∀ n, M ≤ n → stateTerm E Ω A Φ' n = 0 := fun n hn =>
    eq_zero_of_hasWeakIntegral_zero
      (by rw [hM₂ n (le_trans (le_max_right _ _) hn), toConfigFn_zeroOfDegree]) (hu' n)
  have hterm : (fun p : ℕ × ℕ => S.evalAt (tensorAt
      (flipConjAt ((Φ.1 p.1).1)) ((Φ'.1 p.2).1))) =
      fun p => inner ℂ (stateTerm E Ω A Φ p.1) (stateTerm E Ω A Φ' p.2) :=
    funext fun p => evalAt_tensorAt_eq_inner hcs hop hsp hcont hform.norm_vacuum hsym hrep _ _
      (seqValues_mem hΦ p.1) (seqValues_mem hΦ' p.2) (hu p.1) (hu' p.2)
  rw [smoothSeqState_eq_sum hz, smoothSeqState_eq_sum hz', sum_inner]
  simp only [inner_sum]
  change _ = ∑ᶠ p : ℕ × ℕ, S.evalAt (tensorAt
    (flipConjAt ((Φ.1 p.1).1)) ((Φ'.1 p.2).1))
  rw [hterm, finsum_eq_sum_of_support_subset (s := Finset.range (M + 1) ×ˢ Finset.range (M + 1)),
    Finset.sum_product]
  intro p hp
  simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio]
  by_contra hnot
  refine hp ?_
  by_cases h₁ : p.1 < M + 1
  · have h₂ : M ≤ p.2 := by
      by_contra h
      exact hnot ⟨h₁, by omega⟩
    simp [hz' p.2 h₂]
  · simp [hz p.1 (by omega)]
end YangMills.Construction.SmoothSeqInner
end
