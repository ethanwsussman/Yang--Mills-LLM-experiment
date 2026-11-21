import YangMills.Construction.ComplexAnalysis.BoxIntegralHolomorphic
import YangMills.Construction.Cumulants.JointCumulantsOfBoundedVariablesProof
import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.Towers.TheMassiveFamilyIsTempered
import YangMills.Construction.Towers.TheMassiveSymbolsAreHolomorphicInTheNumberAndTheMomentum
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctionalAreLocal
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.MassiveLogDet.Holomorphy
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Coordinates
open YangMills.Construction.Coordinates.ComplexCoordinates
section Entries
variable {I : PeriodicData} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
def EntriesDifferentiableOn (U : Set Y) (M : Y → QuotHom I I) : Prop :=
  ∀ c' c, DifferentiableOn ℂ (fun y => linearMapEntry (M y) c' c) U
theorem linearMapEntry_eq_toMatrix [Fintype I.UnitQuot] [DecidableEq I.UnitQuot] (M : QuotHom I I)
    (c' c : I.UnitQuot) : linearMapEntry M c' c = LinearMap.toMatrixAlgEquiv' M c' c := by
  rw [LinearMap.toMatrixAlgEquiv'_apply, linearMapEntry]
  refine congrFun (congrArg M ?_) c'
  ext j
  simp [Pi.single_apply]
theorem EntriesDifferentiableOn.add {U : Set Y} {M M' : Y → QuotHom I I}
    (h : EntriesDifferentiableOn U M) (h' : EntriesDifferentiableOn U M') :
    EntriesDifferentiableOn U fun y => M y + M' y := by
  intro c' c
  have e : (fun y => linearMapEntry (M y + M' y) c' c) =
      fun y => linearMapEntry (M y) c' c + linearMapEntry (M' y) c' c := by
    funext y; simp [linearMapEntry]
  rw [e]
  exact (h c' c).add (h' c' c)
theorem EntriesDifferentiableOn.smul {U : Set Y} {M : Y → QuotHom I I} {a : Y → ℂ}
    (ha : DifferentiableOn ℂ a U) (h : EntriesDifferentiableOn U M) :
    EntriesDifferentiableOn U fun y => a y • M y := by
  intro c' c
  have e : (fun y => linearMapEntry (a y • M y) c' c) =
      fun y => a y * linearMapEntry (M y) c' c := by
    funext y; simp [linearMapEntry]
  rw [e]
  exact ha.mul (h c' c)
theorem EntriesDifferentiableOn.const {U : Set Y} (M : QuotHom I I) :
    EntriesDifferentiableOn U fun _ => M :=
  fun _ _ => differentiableOn_const _
theorem EntriesDifferentiableOn.comp [Finite I.UnitQuot] {U : Set Y} {M M' : Y → QuotHom I I}
    (h : EntriesDifferentiableOn U M) (h' : EntriesDifferentiableOn U M') :
    EntriesDifferentiableOn U fun y => (M y).comp (M' y) := by
  classical
  let := Fintype.ofFinite I.UnitQuot
  intro c' c
  have e : (fun y => linearMapEntry ((M y).comp (M' y)) c' c) =
      fun y => ∑ k, linearMapEntry (M y) c' k * linearMapEntry (M' y) k c := by
    funext y
    simp only [linearMapEntry_eq_toMatrix]
    rw [← Matrix.mul_apply, ← map_mul]
    rfl
  rw [e]
  exact DifferentiableOn.fun_sum fun k _ => (h c' k).mul (h' k c)
theorem EntriesDifferentiableOn.precomp {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {U : Set Y} {V : Set Z} {M : Z → QuotHom I I} {g : Y → Z} (h : EntriesDifferentiableOn V M)
    (hg : DifferentiableOn ℂ g U) (hm : MapsTo g U V) :
    EntriesDifferentiableOn U fun y => M (g y) :=
  fun c' c => (h c' c).comp hg hm
theorem differentiableOn_matrix_det {n : Type} [Fintype n] [DecidableEq n] {U : Set Y}
    {X : Y → Matrix n n ℂ} (h : ∀ i j, DifferentiableOn ℂ (fun y => X y i j) U) :
    DifferentiableOn ℂ (fun y => (X y).det) U := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  have hp : ∀ i ∈ (Finset.univ : Finset n), DifferentiableOn ℂ (fun y => X y (σ i) i) U :=
    fun i _ => h _ _
  have hs : ∀ s : Finset n, DifferentiableOn ℂ (fun y => ∏ i ∈ s, X y (σ i) i) U := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [differentiableOn_const]
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hp a (Finset.mem_univ a)).mul ih
  exact (differentiableOn_const _).mul (hs Finset.univ)
theorem differentiableOn_matrix_adjugate {n : Type} [Fintype n] [DecidableEq n] {U : Set Y}
    {X : Y → Matrix n n ℂ} (h : ∀ i j, DifferentiableOn ℂ (fun y => X y i j) U) (i j : n) :
    DifferentiableOn ℂ (fun y => (X y).adjugate i j) U := by
  simp only [Matrix.adjugate_apply]
  refine differentiableOn_matrix_det fun a b => ?_
  by_cases e : a = j
  · subst e
    simp [Matrix.updateRow_self, differentiableOn_const]
  · simpa [Matrix.updateRow_ne e] using h a b
theorem isUnit_iff_det_toMatrix_ne_zero [Fintype I.UnitQuot] [DecidableEq I.UnitQuot]
    (M : QuotHom I I) :
    IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ)) ↔ (LinearMap.toMatrixAlgEquiv' M).det ≠ 0 := by
  rw [← MulEquiv.isUnit_map (LinearMap.toMatrixAlgEquiv' (R := ℂ) (n := I.UnitQuot)).toMulEquiv
    (x := (M : Module.End ℂ (I.UnitQuot → ℂ)))]
  rw [show ((LinearMap.toMatrixAlgEquiv' (R := ℂ) (n := I.UnitQuot)).toMulEquiv
    (M : Module.End ℂ (I.UnitQuot → ℂ))) = LinearMap.toMatrixAlgEquiv' M from rfl]
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
theorem linearMapEntry_quotHomInverse [Fintype I.UnitQuot] [DecidableEq I.UnitQuot]
    {M : QuotHom I I} (hM : IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ))) (c' c : I.UnitQuot) :
    linearMapEntry (quotHomInverse M) c' c =
      ((LinearMap.toMatrixAlgEquiv' M).det)⁻¹ * (LinearMap.toMatrixAlgEquiv' M).adjugate c' c := by
  obtain ⟨u, hu⟩ := hM
  have hinv : quotHomInverse M = ((u⁻¹ : (Module.End ℂ (I.UnitQuot → ℂ))ˣ) :
      Module.End ℂ (I.UnitQuot → ℂ)) := by
    rw [quotHomInverse, ← hu, Ring.inverse_unit]
  have h1 : LinearMap.toMatrixAlgEquiv' (quotHomInverse M) * LinearMap.toMatrixAlgEquiv' M = 1 := by
    rw [← map_mul, hinv]
    have : ((u⁻¹ : (Module.End ℂ (I.UnitQuot → ℂ))ˣ) : Module.End ℂ (I.UnitQuot → ℂ)) * M = 1 := by
      rw [← hu]; simp
    rw [this, map_one]
  rw [linearMapEntry_eq_toMatrix, Matrix.inv_eq_left_inv h1 |>.symm, Matrix.inv_def,
    Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
theorem EntriesDifferentiableOn.inverse [Finite I.UnitQuot] {U : Set Y} {M : Y → QuotHom I I}
    (h : EntriesDifferentiableOn U M)
    (hu : ∀ y ∈ U, IsUnit (M y : Module.End ℂ (I.UnitQuot → ℂ))) :
    EntriesDifferentiableOn U fun y => quotHomInverse (M y) := by
  classical
  let := Fintype.ofFinite I.UnitQuot
  intro c' c
  have hX : ∀ i j, DifferentiableOn ℂ (fun y => LinearMap.toMatrixAlgEquiv' (M y) i j) U := by
    intro i j
    simpa only [linearMapEntry_eq_toMatrix] using h i j
  have hd := differentiableOn_matrix_det hX
  refine (DifferentiableOn.mul (hd.inv fun y hy => ?_)
    (differentiableOn_matrix_adjugate hX c' c)).congr
    fun y hy => linearMapEntry_quotHomInverse (hu y hy) c' c
  exact (isUnit_iff_det_toMatrix_ne_zero (M y)).1 (hu y hy)
theorem isOpen_setOf_isUnit [Finite I.UnitQuot] {D : Set Y} (hD : IsOpen D) {M : Y → QuotHom I I}
    (h : EntriesDifferentiableOn D M) :
    IsOpen {y | y ∈ D ∧ IsUnit (M y : Module.End ℂ (I.UnitQuot → ℂ))} := by
  classical
  let := Fintype.ofFinite I.UnitQuot
  have hX : ∀ i j, DifferentiableOn ℂ (fun y => LinearMap.toMatrixAlgEquiv' (M y) i j) D := by
    intro i j
    simpa only [linearMapEntry_eq_toMatrix] using h i j
  have hc := (differentiableOn_matrix_det hX).continuousOn
  have e := hc.isOpen_inter_preimage hD (isOpen_compl_singleton (x := (0 : ℂ)))
  convert e using 1
  ext y
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff]
  rw [isUnit_iff_det_toMatrix_ne_zero]
theorem differentiableOn_trace_of_entries [Finite I.UnitQuot] {U : Set Y} {M : Y → QuotHom I I}
    (h : EntriesDifferentiableOn U M) :
    DifferentiableOn ℂ (fun y => LinearMap.trace ℂ (I.UnitQuot → ℂ) (M y)) U := by
  classical
  let := Fintype.ofFinite I.UnitQuot
  have e : (fun y => LinearMap.trace ℂ (I.UnitQuot → ℂ) (M y)) =
      fun y => ∑ c, linearMapEntry (M y) c c := by
    funext y
    rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ I.UnitQuot), Matrix.trace]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [linearMapEntry_eq_toMatrix]
    simp [LinearMap.toMatrixAlgEquiv'_apply]
  rw [e]
  exact DifferentiableOn.fun_sum fun c _ => h c c
end Entries
section Coordinates
variable {N : ℕ}
theorem differentiableOn_of_isHolomorphicIn
    (hM : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {O : Set (ComplexCoordinates N)} {g : ComplexCoordinates N → ℂ}
    (h : IsHolomorphicIn (N' := 1) O fun z _ => g z) : DifferentiableOn ℂ g O := by
  intro b hb
  obtain ⟨L, hL⟩ := ((hM.1 N O h.1).1 1 _ h).2.2.1 b hb
  have hd : HasFDerivAt (fun z (_ : Fin 1) => g z) L b := hasFDerivAt_of_restrictScalars ℝ hL rfl
  exact (differentiableAt_pi.1 hd.differentiableAt 0).differentiableWithinAt
theorem isHolomorphicIn_of_differentiableOn {O : Set (ComplexCoordinates N)} (hO : IsOpen O)
    {g : ComplexCoordinates N → ℂ} (h : DifferentiableOn ℂ g O) :
    IsHolomorphicIn (N' := 1) O fun z _ => g z := by apply _root_.YangMills.SharedProofs.p41626 <;> assumption
end Coordinates
section Numbers
variable {I : PeriodicData}
theorem normalize_f00 (p : Fin 4 → ℂ) (T : JetQuad I I) (q : Fin 4 → ℂ) :
    (JetQuad.normalize p T).f00 q =
      (quotHomInverse (T.f00 q)).comp (T.f00 q) + (-1 : ℂ) • LinearMap.id := rfl
theorem normalize_f10 (p : Fin 4 → ℂ) (T : JetQuad I I) (q : Fin 4 → ℂ) :
    (JetQuad.normalize p T).f10 q = (quotHomInverse (T.f00 (q + p))).comp (T.f10 q) := by
  simp [JetQuad.normalize, JetQuad.add, JetQuad.smul, JetQuad.mul,
    JetQuad.zeroPartInv, JetQuad.one]
theorem normalize_f01 (p : Fin 4 → ℂ) (T : JetQuad I I) (q : Fin 4 → ℂ) :
    (JetQuad.normalize p T).f01 q = (quotHomInverse (T.f00 (q - p))).comp (T.f01 q) := by
  simp [JetQuad.normalize, JetQuad.add, JetQuad.smul, JetQuad.mul,
    JetQuad.zeroPartInv, JetQuad.one]
theorem normalize_f11 (p : Fin 4 → ℂ) (T : JetQuad I I) (q : Fin 4 → ℂ) :
    (JetQuad.normalize p T).f11 q = (quotHomInverse (T.f00 q)).comp (T.f11 q) := by
  simp [JetQuad.normalize, JetQuad.add, JetQuad.smul, JetQuad.mul,
    JetQuad.zeroPartInv, JetQuad.one]
theorem logSeries_f11 (p : Fin 4 → ℂ) (T : JetQuad I I) (κ : Fin 4 → ℂ) :
    (JetQuad.logSeries p T).f11 κ =
      (JetQuad.normalize p T).f11 κ + (-(1 / 2) : ℂ) •
        (((JetQuad.normalize p T).f11 κ).comp ((JetQuad.normalize p T).f00 κ) +
          ((JetQuad.normalize p T).f00 κ).comp ((JetQuad.normalize p T).f11 κ) +
          ((JetQuad.normalize p T).f10 (κ - p)).comp ((JetQuad.normalize p T).f01 κ) +
          ((JetQuad.normalize p T).f01 (κ + p)).comp ((JetQuad.normalize p T).f10 κ)) := rfl
theorem toComplexVec_mem_realDualPoints (κ : InfiniteLattice.AmbientSpace) :
    toComplexVec κ ∈ realDualPoints := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.toComplexVec_mem_realDualPoints <;> assumption
theorem add_mem_realDualPoints {a b : Fin 4 → ℂ} (ha : a ∈ realDualPoints)
    (hb : b ∈ realDualPoints) : a + b ∈ realDualPoints :=
  fun j => by simp [ha j, hb j]
theorem sub_mem_realDualPoints {a b : Fin 4 → ℂ} (ha : a ∈ realDualPoints)
    (hb : b ∈ realDualPoints) : a - b ∈ realDualPoints :=
  fun j => by simp [ha j, hb j]
theorem logNumber_congr_of_real {T S : JetQuad I I} {p : Fin 4 → ℂ} (hp : p ∈ realDualPoints)
    (h00 : ∀ κ ∈ realDualPoints, T.f00 κ = S.f00 κ) (h10 : ∀ κ ∈ realDualPoints, T.f10 κ = S.f10 κ)
    (h01 : ∀ κ ∈ realDualPoints, T.f01 κ = S.f01 κ)
    (h11 : ∀ κ ∈ realDualPoints, T.f11 κ = S.f11 κ) :
    JetQuad.logNumber p T = JetQuad.logNumber p S := by
  have key : ∀ κ : InfiniteLattice.AmbientSpace,
      (JetQuad.logSeries p T).f11 (toComplexVec κ) =
        (JetQuad.logSeries p S).f11 (toComplexVec κ) := by
    intro κ
    have r := toComplexVec_mem_realDualPoints κ
    have rp := add_mem_realDualPoints r hp
    have rm := sub_mem_realDualPoints r hp
    simp only [logSeries_f11, normalize_f00, normalize_f10, normalize_f01, normalize_f11,
      sub_add_cancel, add_sub_cancel_right, h00 _ r, h00 _ rp, h00 _ rm, h10 _ r, h10 _ rm,
      h01 _ r, h01 _ rp, h11 _ r]
  simp only [JetQuad.logNumber, JetQuad.traceNumber, key]
end Numbers
section General
variable {F I : PeriodicData}
def dualPart (w : ComplexCoordinates 5) : Fin 4 → ℂ := fun i => w i.succ
def numberDualPoint (z : ℂ) (p : Fin 4 → ℂ) : ComplexCoordinates 5 := Fin.cons z p
def shiftedJetQuad (S : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (z₀ : ℂ)
    (εPlus εMinus : F.UnitQuot → ℂ) (w : ComplexCoordinates 5) : JetQuad I I :=
  JetQuad.add (jetAlong F I I S (dualPart w) εPlus εMinus)
    (JetQuad.smul (w 0 - z₀) (JetQuad.ofKernel I I (idKernel I)))
theorem differentiable_dualPart : Differentiable ℂ dualPart :=
  differentiable_pi.2 fun i => differentiable_apply i.succ
theorem entriesDifferentiableOn_of_expSum {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {U : Set Y} {G : Y → QuotHom I I} {q m : Y → Fin 4 → ℂ} (hq : Differentiable ℂ q)
    (hm : Differentiable ℂ m)
    (h : ∀ c' c, ∃ (n : ℕ) (f : Fin n → JetDomains.MomentumLinearForm) (a : Fin n → ℂ), ∀ y,
      linearMapEntry (G y) c' c = JetDomains.expSum a f (q y) (m y)) :
    EntriesDifferentiableOn U G := by
  intro c' c
  obtain ⟨n, f, a, e⟩ := h c' c
  have e' : (fun y => linearMapEntry (G y) c' c) =
      fun y => ∑ j, a j * Complex.exp (f j (q y, m y)) := by
    funext y
    rw [e]
    rfl
  rw [e']
  refine Differentiable.differentiableOn ?_
  refine Differentiable.fun_sum fun j _ => (differentiable_const _).mul (Differentiable.cexp ?_)
  exact (LinearMap.toContinuousLinearMap (f j)).differentiable.comp (hq.prodMk hm)
theorem toComplexVec_add (a b : InfiniteLattice.AmbientSpace) :
    toComplexVec a + toComplexVec b = toComplexVec (a + b) := by
  ext μ
  simp [toComplexVec]
theorem toComplexVec_sub (a b : InfiniteLattice.AmbientSpace) :
    toComplexVec a - toComplexVec b = toComplexVec (a - b) := by
  ext μ
  simp [toComplexVec]
theorem continuous_toComplexVec : Continuous toComplexVec := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.continuous_toComplexVec <;> assumption
theorem logNumber_differentiableOn_ball_of_facts
    (hW3 : ComplexAnalysis.BoxIntegralHolomorphicInParameter)
    (hM : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) [Finite I.UnitQuot]
    {S : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
    (hS : JetDomains.OpFunJetProperties F I I S)
    {O₁ : Set (Fin 4 → ℂ)} (hO₁ : IsOpen O₁) (hreal : realDualPoints ⊆ O₁)
    (hA : EntriesDifferentiableOn O₁ (symbolHom I I (coeffZero F I I S)))
    (hB : EntriesDifferentiableOn O₁ (symbolHom I I (idKernel I)))
    (hu : ∀ κ : InfiniteLattice.AmbientSpace, IsUnit (symbolHom I I (coeffZero F I I S)
      (toComplexVec κ) : Module.End ℂ (I.UnitQuot → ℂ)))
    (z₀ : ℂ) (p₀ : InfiniteLattice.AmbientSpace) (εPlus εMinus : F.UnitQuot → ℂ) :
    ∃ r > 0, DifferentiableOn ℂ
      (fun w => JetQuad.logNumber (dualPart w) (shiftedJetQuad S z₀ εPlus εMinus w))
      (Metric.ball (numberDualPoint z₀ (toComplexVec p₀)) r) := by
  let T₀ : ℂ × (Fin 4 → ℂ) → QuotHom I I := fun y =>
    symbolHom I I (coeffZero F I I S) y.2 + y.1 • symbolHom I I (idKernel I) y.2
  let D : Set (ℂ × (Fin 4 → ℂ)) := Prod.snd ⁻¹' O₁
  have hD : IsOpen D := hO₁.preimage continuous_snd
  have hA' : EntriesDifferentiableOn D fun y : ℂ × (Fin 4 → ℂ) =>
      symbolHom I I (coeffZero F I I S) y.2 :=
    hA.precomp (g := Prod.snd) differentiableOn_snd fun y hy => hy
  have hB' : EntriesDifferentiableOn D fun y : ℂ × (Fin 4 → ℂ) => symbolHom I I (idKernel I) y.2 :=
    hB.precomp (g := Prod.snd) differentiableOn_snd fun y hy => hy
  have hT : EntriesDifferentiableOn D T₀ :=
    hA'.add (EntriesDifferentiableOn.smul (a := Prod.fst) differentiableOn_fst hB')
  let W : Set (ℂ × (Fin 4 → ℂ)) :=
    {y | y ∈ D ∧ IsUnit (T₀ y : Module.End ℂ (I.UnitQuot → ℂ))}
  have hW : IsOpen W := isOpen_setOf_isUnit hD hT
  have hTW : EntriesDifferentiableOn W T₀ := fun c' c => (hT c' c).mono fun y hy => hy.1
  have hInv : EntriesDifferentiableOn W fun y => quotHomInverse (T₀ y) :=
    hTW.inverse fun y hy => hy.2
  let cc : (Fin 4 → ℂ) × ComplexCoordinates 5 → ℂ := fun x => x.2 0 - z₀
  let mm : (Fin 4 → ℂ) × ComplexCoordinates 5 → Fin 4 → ℂ := fun x => dualPart x.2
  have hc0' : Differentiable ℂ fun x : (Fin 4 → ℂ) × ComplexCoordinates 5 => x.2 0 := by
    fun_prop
  have hcc : Differentiable ℂ cc := hc0'.fun_sub (differentiable_const _)
  have hmm : Differentiable ℂ mm := differentiable_dualPart.comp differentiable_snd
  have hκ : Differentiable ℂ fun x : (Fin 4 → ℂ) × ComplexCoordinates 5 => x.1 := differentiable_fst
  let g₀ : (Fin 4 → ℂ) × ComplexCoordinates 5 → ℂ × (Fin 4 → ℂ) := fun x => (cc x, x.1)
  let gp : (Fin 4 → ℂ) × ComplexCoordinates 5 → ℂ × (Fin 4 → ℂ) := fun x => (cc x, x.1 + mm x)
  let gm : (Fin 4 → ℂ) × ComplexCoordinates 5 → ℂ × (Fin 4 → ℂ) := fun x => (cc x, x.1 - mm x)
  have hg₀ : Differentiable ℂ g₀ := hcc.prodMk hκ
  have hgp : Differentiable ℂ gp := hcc.prodMk (hκ.add hmm)
  have hgm : Differentiable ℂ gm := hcc.prodMk (hκ.sub hmm)
  let U : Set ((Fin 4 → ℂ) × ComplexCoordinates 5) := g₀ ⁻¹' W ∩ gp ⁻¹' W ∩ gm ⁻¹' W
  have hU : IsOpen U :=
    ((hW.preimage hg₀.continuous).inter (hW.preimage hgp.continuous)).inter
      (hW.preimage hgm.continuous)
  let J : (Fin 4 → ℂ) × ComplexCoordinates 5 → JetQuad I I :=
    fun x => shiftedJetQuad S z₀ εPlus εMinus x.2
  have e10 : ∀ x q, (J x).f10 q = (jetAlong F I I S (mm x) εPlus εMinus).f10 q := by
    intro x q
    simp [J, mm, shiftedJetQuad, JetQuad.add, JetQuad.smul, JetQuad.ofKernel]
  have e01 : ∀ x q, (J x).f01 q = (jetAlong F I I S (mm x) εPlus εMinus).f01 q := by
    intro x q
    simp [J, mm, shiftedJetQuad, JetQuad.add, JetQuad.smul, JetQuad.ofKernel]
  have e11 : ∀ x q, (J x).f11 q = (jetAlong F I I S (mm x) εPlus εMinus).f11 q := by
    intro x q
    simp [J, mm, shiftedJetQuad, JetQuad.add, JetQuad.smul, JetQuad.ofKernel]
  have t0 : EntriesDifferentiableOn U fun x => (J x).f00 x.1 :=
    hTW.precomp (g := g₀) hg₀.differentiableOn fun x hx => hx.1.1
  have i0 : EntriesDifferentiableOn U fun x => quotHomInverse ((J x).f00 x.1) :=
    hInv.precomp (g := g₀) hg₀.differentiableOn fun x hx => hx.1.1
  have ip : EntriesDifferentiableOn U fun x => quotHomInverse ((J x).f00 (x.1 + mm x)) :=
    hInv.precomp (g := gp) hgp.differentiableOn fun x hx => hx.1.2
  have im : EntriesDifferentiableOn U fun x => quotHomInverse ((J x).f00 (x.1 - mm x)) :=
    hInv.precomp (g := gm) hgm.differentiableOn fun x hx => hx.2
  have j10 : ∀ q : (Fin 4 → ℂ) × ComplexCoordinates 5 → Fin 4 → ℂ, Differentiable ℂ q →
      EntriesDifferentiableOn U fun x => (J x).f10 (q x) := by
    intro q hq
    refine entriesDifferentiableOn_of_expSum hq hmm fun c' c => ?_
    obtain ⟨n, f, a, e⟩ := hS.entries_f10 c' c
    exact ⟨n, f, fun j => a j εPlus, fun x => by rw [e10]; exact e _ _ _ _⟩
  have j01 : ∀ q : (Fin 4 → ℂ) × ComplexCoordinates 5 → Fin 4 → ℂ, Differentiable ℂ q →
      EntriesDifferentiableOn U fun x => (J x).f01 (q x) := by
    intro q hq
    refine entriesDifferentiableOn_of_expSum hq hmm fun c' c => ?_
    obtain ⟨n, f, a, e⟩ := hS.entries_f01 c' c
    exact ⟨n, f, fun j => a j εMinus, fun x => by rw [e01]; exact e _ _ _ _⟩
  have j11 : ∀ q : (Fin 4 → ℂ) × ComplexCoordinates 5 → Fin 4 → ℂ, Differentiable ℂ q →
      EntriesDifferentiableOn U fun x => (J x).f11 (q x) := by
    intro q hq
    refine entriesDifferentiableOn_of_expSum hq hmm fun c' c => ?_
    obtain ⟨n, f, a, e⟩ := hS.entries_f11 c' c
    exact ⟨n, f, fun j => a j εPlus εMinus, fun x => by rw [e11]; exact e _ _ _ _⟩
  have n00 : EntriesDifferentiableOn U fun x => (JetQuad.normalize (mm x) (J x)).f00 x.1 := by
    simp only [normalize_f00]
    exact (i0.comp t0).add (EntriesDifferentiableOn.const _)
  have n10 : EntriesDifferentiableOn U fun x => (JetQuad.normalize (mm x) (J x)).f10 x.1 := by
    simp only [normalize_f10]
    exact ip.comp (j10 _ hκ)
  have n10' : EntriesDifferentiableOn U fun x =>
      (JetQuad.normalize (mm x) (J x)).f10 (x.1 - mm x) := by
    simp only [normalize_f10, sub_add_cancel]
    exact i0.comp (j10 _ (hκ.sub hmm))
  have n01 : EntriesDifferentiableOn U fun x => (JetQuad.normalize (mm x) (J x)).f01 x.1 := by
    simp only [normalize_f01]
    exact im.comp (j01 _ hκ)
  have n01' : EntriesDifferentiableOn U fun x =>
      (JetQuad.normalize (mm x) (J x)).f01 (x.1 + mm x) := by
    simp only [normalize_f01, add_sub_cancel_right]
    exact i0.comp (j01 _ (hκ.add hmm))
  have n11 : EntriesDifferentiableOn U fun x => (JetQuad.normalize (mm x) (J x)).f11 x.1 := by
    simp only [normalize_f11]
    exact i0.comp (j11 _ hκ)
  have hP : EntriesDifferentiableOn U fun x => (JetQuad.logSeries (mm x) (J x)).f11 x.1 := by
    simp only [logSeries_f11]
    exact n11.add (EntriesDifferentiableOn.smul (differentiableOn_const _)
      ((((n11.comp n00).add (n00.comp n11)).add (n10'.comp n01)).add (n01'.comp n10)))
  let Φ : (Fin 4 → ℂ) × ComplexCoordinates 5 → ℂ := fun x =>
    LinearMap.trace ℂ (I.UnitQuot → ℂ) ((JetQuad.logSeries (mm x) (J x)).f11 x.1)
  have hΦ : DifferentiableOn ℂ Φ U := differentiableOn_trace_of_entries hP
  have hmom : dualPart (numberDualPoint z₀ (toComplexVec p₀)) = toComplexVec p₀ := by
    ext i
    simp [dualPart, numberDualPoint]
  have hc0 : numberDualPoint z₀ (toComplexVec p₀) 0 - z₀ = 0 := by
    simp [numberDualPoint]
  have memW : ∀ v : InfiniteLattice.AmbientSpace, ((0 : ℂ), toComplexVec v) ∈ W := by
    intro v
    refine ⟨hreal (toComplexVec_mem_realDualPoints v), ?_⟩
    simpa [T₀] using hu v
  let cube : Set (Fin 4 → ℝ) := Icc (fun _ => -Real.pi) fun _ => Real.pi
  have hK : IsCompact (toComplexVec '' cube) := isCompact_Icc.image continuous_toComplexVec
  have hsub : (toComplexVec '' cube) ×ˢ {numberDualPoint z₀ (toComplexVec p₀)} ⊆ U := by
    rintro ⟨q, w⟩ ⟨⟨κ, -, rfl⟩, hw⟩
    obtain rfl : w = numberDualPoint z₀ (toComplexVec p₀) := hw
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show (cc _, toComplexVec κ) ∈ W
      simp only [cc, hc0]
      exact memW κ
    · show (cc _, toComplexVec κ + mm _) ∈ W
      simp only [cc, mm, hc0, hmom, toComplexVec_add]
      exact memW _
    · show (cc _, toComplexVec κ - mm _) ∈ W
      simp only [cc, mm, hc0, hmom, toComplexVec_sub]
      exact memW _
  obtain ⟨u, v, -, hv, hKu, hwv, huv⟩ := generalized_tube_lemma hK isCompact_singleton hU hsub
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hv _ (hwv rfl)
  have hr : 0 < ρ / 2 := half_pos hρ
  have hcb : Metric.closedBall (numberDualPoint z₀ (toComplexVec p₀)) (ρ / 2) ⊆ v :=
    (Metric.closedBall_subset_ball (half_lt_self hρ)).trans hball
  have hsub2 : (toComplexVec '' cube) ×ˢ
      Metric.closedBall (numberDualPoint z₀ (toComplexVec p₀)) (ρ / 2) ⊆ U :=
    (prod_mono hKu hcb).trans huv
  have hcomp : IsCompact ((toComplexVec '' cube) ×ˢ
      Metric.closedBall (numberDualPoint z₀ (toComplexVec p₀)) (ρ / 2)) :=
    hK.prod (isCompact_closedBall _ _)
  obtain ⟨m, hm⟩ := hcomp.exists_bound_of_continuousOn (hΦ.continuousOn.mono hsub2)
  have hmem : ∀ t ∈ cube, ∀ w ∈ Metric.ball (numberDualPoint z₀ (toComplexVec p₀)) (ρ / 2),
      (toComplexVec t, w) ∈ U :=
    fun t ht w hw => hsub2 ⟨⟨t, ht, rfl⟩, Metric.ball_subset_closedBall hw⟩
  have hint := (hW3 4 5 (by norm_num) (by norm_num) (fun _ => -Real.pi) (fun _ => Real.pi)
    (fun _ => by linarith [Real.pi_pos]) (Metric.ball (numberDualPoint z₀ (toComplexVec p₀)) (ρ / 2))
    Metric.isOpen_ball (fun t w => Φ (toComplexVec t, w))
    ⟨m, fun t ht w hw => hm _ ⟨⟨t, ht, rfl⟩, Metric.ball_subset_closedBall hw⟩⟩
    (fun w hw => hΦ.continuousOn.comp
      (continuous_toComplexVec.prodMk continuous_const).continuousOn fun t ht => hmem t ht w hw)
    (fun t ht => isHolomorphicIn_of_differentiableOn Metric.isOpen_ball
      (hΦ.comp (differentiable_const _ |>.prodMk differentiable_id).differentiableOn
        fun w hw => hmem t ht w hw))).2
  refine ⟨ρ / 2, hr, ?_⟩
  have hd := differentiableOn_of_isHolomorphicIn hM hint
  exact (differentiableOn_const (((((2 * Real.pi) ^ 4)⁻¹ : ℝ)) : ℂ)).mul hd
theorem logNumber_addSmulKernel_eq (hW2 : ConstantOpFun.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    (hper : IsPeriodicKernel I I (idKernel I))
    (hfin : IsFiniteRange I I (idKernel I))
    {S : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} (hS : IsLocalOpFun F I I S)
    (z₀ : ℂ) (εPlus εMinus : F.UnitQuot → ℂ) {w : ComplexCoordinates 5}
    (hw : dualPart w ∈ realDualPoints) :
    JetQuad.logNumber (dualPart w)
        (jetAlong F I I (ConstantOpFun.addSmulKernel S (w 0 - z₀) (idKernel I))
          (dualPart w) εPlus εMinus) =
      JetQuad.logNumber (dualPart w) (shiftedJetQuad S z₀ εPlus εMinus w) := by
  have hstrip : ∀ {a : Fin 4 → ℂ}, a ∈ realDualPoints → ∀ {s : ℝ}, 0 ≤ s → a ∈ imStrip s := by
    intro a ha s hs μ
    rw [ha μ]
    simpa using hs
  have hs1 : (0 : ℝ) ≤ 1 := zero_le_one
  have hs2 : (0 : ℝ) ≤ 2 * 1 := by norm_num
  obtain ⟨a00, a10, a01, a11⟩ := ((hW2 F I I hF hI hI (idKernel I) hper hfin 1 (dualPart w)
    one_pos (hstrip hw hs1) εPlus εMinus).2 S (w 0 - z₀) hS).2
  refine logNumber_congr_of_real hw (fun κ hκ => a00 (hstrip hκ hs2)) (fun κ hκ => a10 ?_)
    (fun κ hκ => a01 ?_) (fun κ hκ => a11 hκ)
  · exact ⟨hstrip hκ hs2, hstrip (add_mem_realDualPoints hκ hw) hs2⟩
  · exact ⟨hstrip hκ hs2, hstrip (sub_mem_realDualPoints hκ hw) hs2⟩
theorem idKernel_isFiniteRange : IsFiniteRange I I (idKernel I) := by
  refine ⟨0, fun ι' ι h => ?_⟩
  have hne : ι' ≠ ι := by
    rintro rfl
    apply h
    simp [TorusMetric.euclidNormVec]
  simp [idKernel, hne]
theorem logNumber_differentiableOn_ball (hJ : JetDomains.OpFunJetTheory)
    (hW2 : ConstantOpFun.Claim)
    (hW3 : ComplexAnalysis.BoxIntegralHolomorphicInParameter)
    (hM : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    (hper : IsPeriodicKernel I I (idKernel I))
    {S : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} (hS : IsLocalOpFun F I I S)
    (hu : ∀ κ : InfiniteLattice.AmbientSpace, IsUnit (symbolHom I I (coeffZero F I I S)
      (toComplexVec κ) : Module.End ℂ (I.UnitQuot → ℂ)))
    (z₀ : ℂ) (p₀ : InfiniteLattice.AmbientSpace) (εPlus εMinus : F.UnitQuot → ℂ) :
    ∃ r > 0, DifferentiableOn ℂ
      (fun w => JetQuad.logNumber (dualPart w) (shiftedJetQuad S z₀ εPlus εMinus w))
      (Metric.ball (numberDualPoint z₀ (toComplexVec p₀)) r) := by
  have := hI.finite_quot
  have facts := hJ.2.1 F I I hF hI hI S hS
  have h0 : (0 : Fin 4 → ℂ) ∈ imStrip 1 := by
    intro μ
    simp
  obtain ⟨Oa, hOa, hsa, ea⟩ := (facts.isJet 1 one_pos 0 h0 εPlus εMinus).holo_f00
  obtain ⟨Ob, hOb, hsb, -, eb⟩ := ((hW2 F I I hF hI hI (idKernel I) hper
    idKernel_isFiniteRange 1 0 one_pos h0 εPlus εMinus).1).2.2.2.2.1
  have hr2 : ∀ {a : Fin 4 → ℂ}, a ∈ realDualPoints → a ∈ imStrip (2 * 1) := by
    intro a ha μ
    rw [ha μ]
    norm_num
  refine logNumber_differentiableOn_ball_of_facts hW3 hM facts (hOa.inter hOb)
    (fun a ha => ⟨hsa (hr2 ha), hsb (hr2 ha)⟩) ?_ ?_ hu z₀ p₀ εPlus εMinus
  · exact fun c' c => (differentiableOn_of_isHolomorphicIn hM (ea c' c)).mono inter_subset_left
  · exact fun c' c => (differentiableOn_of_isHolomorphicIn hM (eb c' c)).mono inter_subset_right
end General
open YangMills.Construction.PeriodicOperators.ConstantOpFun (addSmulKernel)
theorem addSmulKernel_addSmulKernel {F I : PeriodicData}
    (S : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (a b : ℂ) (T : I.Carrier → I.Carrier → ℂ) :
    addSmulKernel (addSmulKernel S a T) b T = addSmulKernel S (a + b) T := by
  funext ζ ι' ι
  simp [addSmulKernel, add_smul, add_assoc]
theorem vertexOpFun_eq_addSmulKernel (L : ℕ) (z z₀ : ℝ) :
    MassiveOpFunctions.vertexOpFun L z = addSmulKernel (MassiveOpFunctions.vertexOpFun L z₀)
      ((z : ℂ) - z₀) (idKernel (colourVertices L 0 0)) := by
  have h := addSmulKernel_addSmulKernel (F := colourEdges L 0 0) (I := colourVertices L 0 0)
    FullSpace.gaugeLaplacianAt (z₀ : ℂ) ((z : ℂ) - z₀) (idKernel _)
  rw [add_sub_cancel] at h
  exact h.symm
theorem edgeOpFun_eq_addSmulKernel (L : ℕ) (z z₀ : ℝ) :
    MassiveOpFunctions.edgeOpFun L z = addSmulKernel (MassiveOpFunctions.edgeOpFun L z₀)
      ((z : ℂ) - z₀) (idKernel (colourEdges L 0 0)) := by
  have h := addSmulKernel_addSmulKernel (F := colourEdges L 0 0) (I := colourEdges L 0 0)
    FullSpace.massiveHessianAt (z₀ : ℂ) ((z : ℂ) - z₀) (idKernel _)
  rw [add_sub_cancel] at h
  exact h.symm
theorem symbolHolomorphy_holds (hTemp : MassiveOpFunctions.Tempered.MassiveFamilyTempered)
    (hLoc : MassiveOpFunctions.Locality.OpFunsLocal)
    (hJ : JetDomains.OpFunJetTheory)
    (hW2 : ConstantOpFun.Claim)
    (hW3 : ComplexAnalysis.BoxIntegralHolomorphicInParameter)
    (hM : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hId : IdKernelFacts.Claim) (hT3 : TowerIndexSets.Claim) :
    SymbolHolomorphy := by
  intro L hL μ ν z₀ hz₀ p₀
  obtain ⟨hsites, hbonds, -⟩ := hT3 L hL 0 0 le_rfl
  obtain ⟨l₁, l₂, -, -, u₁, u₂⟩ := (hLoc L hL z₀ hz₀).1
  have per₁ := (hId _ hsites).1
  have per₂ := (hId _ hbonds).1
  obtain ⟨r₁, hr₁, d₁⟩ := logNumber_differentiableOn_ball hJ hW2 hW3 hM hbonds hsites per₁ l₁ u₁
    (z₀ : ℂ) p₀ (MassiveOpFunctions.colourDirectionIndicator L 0 μ)
    (MassiveOpFunctions.colourDirectionIndicator L 0 ν)
  obtain ⟨r₂, hr₂, d₂⟩ := logNumber_differentiableOn_ball hJ hW2 hW3 hM hbonds hbonds per₂ l₂ u₂
    (z₀ : ℂ) p₀ (MassiveOpFunctions.colourDirectionIndicator L 0 μ)
    (MassiveOpFunctions.colourDirectionIndicator L 0 ν)
  let w₀ := numberDualPoint (z₀ : ℂ) (toComplexVec p₀)
  have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  refine ⟨Metric.ball w₀ (min r₁ r₂), ⟨w₀, Metric.mem_ball_self hr, by simp [w₀, numberDualPoint],
    fun i => by simp [w₀, numberDualPoint]⟩,
    fun w => JetQuad.logNumber (dualPart w) (shiftedJetQuad (MassiveOpFunctions.vertexOpFun L z₀)
        (z₀ : ℂ) (MassiveOpFunctions.colourDirectionIndicator L 0 μ)
        (MassiveOpFunctions.colourDirectionIndicator L 0 ν) w) -
      1 / 2 * JetQuad.logNumber (dualPart w) (shiftedJetQuad (MassiveOpFunctions.edgeOpFun L z₀)
        (z₀ : ℂ) (MassiveOpFunctions.colourDirectionIndicator L 0 μ)
        (MassiveOpFunctions.colourDirectionIndicator L 0 ν) w), ?_, ?_⟩
  · refine isHolomorphicIn_of_differentiableOn Metric.isOpen_ball ?_
    exact (d₁.mono (Metric.ball_subset_ball (min_le_left _ _))).sub
      ((differentiableOn_const _).mul (d₂.mono (Metric.ball_subset_ball (min_le_right _ _))))
  · intro w _ hreal hpos
    have hw0 : w 0 = (((w 0).re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using hreal 0)
    let p : InfiniteLattice.AmbientSpace := fun i => (w i.succ).re
    have hp : dualPart w = toComplexVec p := by
      ext i
      exact Complex.ext (by simp [dualPart, toComplexVec, p])
        (by simpa [dualPart, toComplexVec, p] using hreal i.succ)
    have hpr : dualPart w ∈ realDualPoints := hp ▸ toComplexVec_mem_realDualPoints p
    have hs := logNumber_addSmulKernel_eq hW2 hbonds hsites per₁
      idKernel_isFiniteRange l₁ (z₀ : ℂ) (MassiveOpFunctions.colourDirectionIndicator L 0 μ)
      (MassiveOpFunctions.colourDirectionIndicator L 0 ν) hpr
    have hb := logNumber_addSmulKernel_eq hW2 hbonds hbonds per₂
      idKernel_isFiniteRange l₂ (z₀ : ℂ) (MassiveOpFunctions.colourDirectionIndicator L 0 μ)
      (MassiveOpFunctions.colourDirectionIndicator L 0 ν) hpr
    have hpol := (hTemp L hL (w 0).re hpos).2 p 0 μ ν
    have hfun : (fun i : Fin 4 => w i.succ) = toComplexVec p := hp
    beta_reduce
    rw [hfun, hpol, ← hs, ← hb, hp, MassiveOpFunctions.logSymbol]
    conv_rhs => rw [vertexOpFun_eq_addSmulKernel L (w 0).re z₀,
      edgeOpFun_eq_addSmulKernel L (w 0).re z₀, ← hw0]
end YangMills.Construction.Tower.MassiveLogDet.Holomorphy
end
