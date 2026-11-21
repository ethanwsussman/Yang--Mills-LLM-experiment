import YangMills.Construction.Continuum.AtMostOneSchwingerFunctionOfEachOrder
import YangMills.Construction.Continuum.ClusteringFromTuplesToSchwartzFunctions
import YangMills.Construction.Continuum.FunctionsNormsBallsAndNeighbourhoods
import YangMills.Construction.Continuum.PassageFromTuplesToSchwartzFunctions
import YangMills.Construction.Continuum.ReflectionPositivityOfASequenceWithTheValuesOfAFunctional
import YangMills.Construction.Continuum.TranslationsAsMotionsAndSmoothSeparatedTuples
import YangMills.Construction.LimitTheorem.ConditionsAtGivenConstants
import YangMills.Construction.LimitTheorem.RepresentativeAndTheIdentificationsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ConfigSpace (FlatSequence schwartzFlatOffDiagonal)
open Filter Topology
namespace LimitTheorem
namespace ComponentConditions
open TestSpaces (SepTupleOfCard sepTuple_ext)
open Motions (RigidMotion actOnTuple actOnPointFun)
open TupleLists (toList ofList ofList_toList toList_ofList)
open UpperHalfTensors (actOnTuple_mem_disjointSupportTuples)
open WightmanReconstruction (flatSequenceAsMaps)
open HilbertSpaceBasics (IsPosSemidef)
open SeparatedTuples ReflectionPositivity.TupleForm
theorem mem_flatSchwartzSet_of_offDiagonal {m : ℕ} {f : TestSpaces.PointTuple (m + 1) → ℂ}
    (h : f ∈ schwartzFlatOffDiagonal (m + 1)) : f ∈ TestSpaces.flatSchwartzSet (m + 1) :=
  (SchwartzAxioms.flatSchwartzSet_eq (n := m + 1)).superset h
theorem flatSequenceAsMaps_succ (T : FlatSequence) (m : ℕ) (φ : TestSpaces.flatSchwartzSet (m + 1))
    (ψ : schwartzFlatOffDiagonal (m + 1)) (h : φ.1 = ψ.1) :
    flatSequenceAsMaps T (m + 1) φ = T.atSucc m ψ := by
  obtain ⟨f, hf⟩ := φ
  obtain ⟨g, hg⟩ := ψ
  obtain rfl : f = g := h
  rfl
variable {σ : TupleFunctional} {T : FlatSequence}
theorem agreesOnTensors_of (hT : HasSchwingerSequence σ T) :
    ReflectionPositivityFromValues.AgreesOnTensors (evalOnMap σ) T := by
  intro m X hX h
  have hY : X.1 ∈ ConfigSpace.separatedFamilies Set.univ (m + 1) := by
    refine ⟨fun i => ?_, fun i j hij => X.2.2 hij⟩
    obtain ⟨h₁, h₂, -⟩ := X.2.1 i
    exact ConfigSpace.mem_realC1CompactIn_iff.2
      ⟨isOpen_univ, h₁, h₂, Set.subset_univ _⟩
  have hs : ConfigSpace.AllSmoothCompact X.1 := fun i => by
    obtain ⟨h₁, h₂, -⟩ := hX i
    exact ConfigSpace.mem_realSmoothCompactIn_iff.2
      ⟨isOpen_univ, h₁, h₂, Set.subset_univ _⟩
  have et : ConfigSpace.tensorRealFamily X.1 = TestSpaces.tensorProdComplex X.1 := by
    funext x
    simp [ConfigSpace.tensorRealFamily, ConfigSpace.tensorFamily,
      TestSpaces.tensorProdComplex, TestSpaces.tensorProd]
  have hv := (hT.2.2 m).2 ⟨X.1, hY⟩ hs (et ▸ h)
  exact (congrArg (T.atSucc m) (Subtype.ext et.symm)).trans hv
theorem isSchwingerFamily_flatSequenceAsMaps (hT : HasSchwingerSequence σ T) :
    TestSpaces.IsSchwingerFamily (evalOnMap σ) (flatSequenceAsMaps T) := by
  refine ⟨fun n hn => ?_, fun φ => hT.2.1 _⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨h₁, h₂⟩ := (SchwartzAxioms.isContinuousOnFlat_iff
    (flatSequenceAsMaps T (m + 1))).2 (hT.2.2 m).1
  refine ⟨h₁, h₂, fun X hX h => ?_⟩
  have hf : TestSpaces.tensorProdComplex X.1 ∈ schwartzFlatOffDiagonal (m + 1) :=
    (SchwartzAxioms.flatSchwartzSet_eq (n := m + 1)).subset h
  rw [flatSequenceAsMaps_succ T m _ ⟨_, hf⟩ rfl]
  exact agreesOnTensors_of hT m X hX hf
theorem exists_boundedExtensionFamily (hT : HasSchwingerSequence σ T) :
    ∃ (k : ℕ → ℕ) (c : ℕ → ℝ), TestSpaces.IsBoundedExtensionFamily (evalOnMap σ)
      (flatSequenceAsMaps T) k c := by
  have hS := isSchwingerFamily_flatSequenceAsMaps hT
  have hex : ∀ n : ℕ, ∃ (k : ℕ) (c : ℝ), 1 ≤ n → 0 < k ∧ 0 ≤ c ∧
      ∀ φ : TestSpaces.flatSchwartzSet n,
        ENNReal.ofReal ‖flatSequenceAsMaps T n φ‖ ≤
          ENNReal.ofReal c * TestSpaces.weightedSeminorm k φ.1 := by
    intro n
    by_cases hn : 1 ≤ n
    · obtain ⟨k, c, h₁, h₂, h₃⟩ := (hS.1 n hn).2.1
      exact ⟨k, c, fun _ => ⟨h₁, h₂, h₃⟩⟩
    · exact ⟨0, 0, fun h => absurd h hn⟩
  choose k c h using hex
  exact ⟨k, c, hS.2, fun n hn =>
    ⟨(hS.1 n hn).1, (h n hn).1, (h n hn).2.1, (h n hn).2.2, (hS.1 n hn).2.2⟩⟩
theorem invMap_toFun (r : RigidMotion) : SeparatedTuples.invMap r.toFun = r.invFun := by apply _root_.YangMills.SharedProofs.p78111 <;> assumption
theorem push_toList (r : RigidMotion) {n : ℕ} (X Y : SepTupleOfCard n)
    (hY : Y.1 = actOnTuple r X.1) :
    SeparatedTuples.push r.toFun (toList ⟨n, X⟩) = toList ⟨n, Y⟩ := by
  have hlist : SeparatedTuples.pushList r.toFun (toList ⟨n, X⟩).1 = List.ofFn Y.1 := by
    rw [hY]
    simp only [SeparatedTuples.pushList, toList, invMap_toFun, List.map_ofFn, Function.comp_def]
    rfl
  have hsep : SeparatedTuples.IsDisjointlySupported
      (SeparatedTuples.pushList r.toFun (toList ⟨n, X⟩).1) :=
    hlist ▸ TupleLists.isDisjointlySupported_ofFn _
  unfold SeparatedTuples.push
  rw [dif_pos hsep]
  exact Subtype.ext hlist
theorem evalOnMap_eq_of_invariant {r : RigidMotion} (h : σ.IsInvariant r.toFun) {n : ℕ}
    (X Y : SepTupleOfCard n) (hY : Y.1 = actOnTuple r X.1) :
    evalOnMap σ ⟨n, Y⟩ = evalOnMap σ ⟨n, X⟩ := by
  have h₁ := h (toList ⟨n, X⟩)
  rwa [push_toList r X Y hY] at h₁
theorem shiftMotion_toFun (v : Fin 4 → ℝ) : (shiftMotion v).toFun = SeparatedTuples.translate v := by apply _root_.YangMills.Construction.SmoothSeparatedTuples.pureTranslation_toFun <;> assumption
theorem evalOnMap_eq_of_motion (ht : ∀ v, σ.IsInvariant (SeparatedTuples.translate v))
    (hr : IsO4InvariantFunctional σ) (r : RigidMotion) {n : ℕ} (X Y : SepTupleOfCard n)
    (hY : Y.1 = actOnTuple r X.1) : evalOnMap σ ⟨n, Y⟩ = evalOnMap σ ⟨n, X⟩ := by
  let R₀ : Orthogonal.orthogonalGroupFour := ⟨r.mat, r.mat_mem⟩
  let Z : SepTupleOfCard n :=
    ⟨actOnTuple (ofOrthogonal R₀) X.1, actOnTuple_mem_disjointSupportTuples _ X.2⟩
  have e₁ : evalOnMap σ ⟨n, Z⟩ = evalOnMap σ ⟨n, X⟩ :=
    evalOnMap_eq_of_invariant (r := ofOrthogonal R₀) (hr R₀) X Z rfl
  have hZ : Y.1 = actOnTuple (shiftMotion r.shift) Z.1 := by
    rw [hY]
    funext i u
    simp [Z, R₀, actOnTuple, actOnPointFun, RigidMotion.invFun,
      shiftMotion, ofOrthogonal]
  have e₂ : evalOnMap σ ⟨n, Y⟩ = evalOnMap σ ⟨n, Z⟩ :=
    evalOnMap_eq_of_invariant (r := shiftMotion r.shift)
      (by rw [shiftMotion_toFun]; exact ht _) Z Y hZ
  exact e₂.trans e₁
theorem sepTupleInvariant_of (ht : ∀ v, σ.IsInvariant (SeparatedTuples.translate v))
    (hr : IsO4InvariantFunctional σ) (r : RigidMotion) (n : ℕ) :
    TestSpaces.SepTupleInvariant (evalOnMap σ) n r :=
  fun X Y _ hY => evalOnMap_eq_of_motion ht hr r X Y hY
theorem ofList_reorder (T' : SeparatedTuples.SepTuple) (τ : Equiv.Perm (Fin T'.1.length))
    (Y : SepTupleOfCard T'.1.length) (hY : Y.1 = T'.1.get ∘ τ) :
    ofList (T'.reorder τ) = ⟨_, Y⟩ := by
  refine sepTuple_ext _ _ (by simp [SeparatedTuples.SepTuple.reorder]) fun k => ?_
  rw [hY]
  exact List.get_ofFn _ _
theorem sepTupleSymmetric_of (h : σ.IsPermInvariant) (n : ℕ) :
    TestSpaces.SepTupleSymmetric (evalOnMap σ) n := by
  have hv : ∀ T', evalOnMap σ (ofList T') = σ T' := fun T' => by
    rw [evalOnMap, toList_ofList]
  have key : ∀ (Z : TestSpaces.SepTuple) (Y : SepTupleOfCard Z.1) (τ : Equiv.Perm (Fin Z.1)),
      Y.1 = Z.2.1 ∘ τ → evalOnMap σ ⟨Z.1, Y⟩ = evalOnMap σ Z := by
    intro Z
    obtain ⟨T', rfl⟩ : ∃ T', Z = ofList T' := ⟨toList Z, (ofList_toList Z).symm⟩
    intro Y τ hY
    change evalOnMap σ ⟨T'.1.length, Y⟩ = _
    rw [← ofList_reorder T' τ Y hY, hv, hv]
    exact h T' τ
  exact fun ς X Y _ hY => key ⟨n, X⟩ Y ς hY
theorem linearExtension_evalOnMap :
    WightmanReconstruction.linearExtension (evalOnMap σ) = σ.spanExtension := by
  have e : (fun X => ((evalOnMap σ (ofList X) : ℝ) : ℂ)) = fun X => (σ X : ℂ) :=
    funext fun X => by rw [evalOnMap, toList_ofList]
  unfold WightmanReconstruction.linearExtension TupleFunctional.spanExtension
  rw [e]
theorem isFormPositive_of (h : IsPosSemidef (reflectionForm σ)) :
    ReflectionPositivityFromValues.IsFormPositive (evalOnMap σ) := by
  intro F
  have hF := Complex.le_def.1 (h.nonneg F)
  rw [linearExtension_evalOnMap]
  exact ⟨hF.2.symm, hF.1⟩
theorem growth_bound_of_satisfiesGrowth {C : ConditionConstants} (hc : 0 ≤ C.cE) (hC : 0 ≤ C.CE)
    (hb : SatisfiesGrowth T C.kE C.cE C.CE C.κ) (m : ℕ)
    (φ : schwartzFlatOffDiagonal (m + 1)) :
    ‖T.atSucc m φ‖ ≤
      C.cE * Real.exp C.CE * ((m + 1).factorial : ℝ) ^ (C.κ + 1) *
        ConfigSpace.bracketNorm (C.kE * (m + 1))
          (ConfigSpace.toSchwartzFn φ) := by
  refine (hb m φ).trans ?_
  have hn : 0 ≤ ConfigSpace.bracketNorm (C.kE * (m + 1))
      (ConfigSpace.toSchwartzFn φ) := ENNReal.toReal_nonneg
  have hf : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hexp : C.CE ^ (m + 1) ≤ Real.exp C.CE * ((m + 1).factorial : ℝ) :=
    (div_le_iff₀ hf).1 (Real.pow_div_factorial_le_exp C.CE hC (m + 1))
  have hp : ((m + 1).factorial : ℝ) ^ (C.κ + 1) =
      ((m + 1).factorial : ℝ) ^ C.κ * ((m + 1).factorial : ℝ) := by
    rw [Real.rpow_add hf, Real.rpow_one]
  have hq : 0 ≤ ((m + 1).factorial : ℝ) ^ C.κ := Real.rpow_nonneg hf.le _
  rw [hp]
  refine mul_le_mul_of_nonneg_right ?_ hn
  calc C.cE * C.CE ^ (m + 1) * ((m + 1).factorial : ℝ) ^ C.κ
      ≤ C.cE * (Real.exp C.CE * ((m + 1).factorial : ℝ)) * ((m + 1).factorial : ℝ) ^ C.κ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hc) hq
    _ = C.cE * Real.exp C.CE * (((m + 1).factorial : ℝ) ^ C.κ * ((m + 1).factorial : ℝ)) := by ring
theorem os_of_tuple_symmetries
    (hcarry : TestSpaces.SchwingerPropertiesTransfer)
    (hrp : ReflectionPositivityFromValues.Statement)
    {σ : TupleFunctional} (hσ : TestSpaces.IsSepFunctional (evalOnMap σ))
    (ht : ∀ v, σ.IsInvariant (SeparatedTuples.translate v))
    (hr : IsO4InvariantFunctional σ) (hsym : σ.IsPermInvariant)
    (hpos : IsPosSemidef (reflectionForm σ)) {T : FlatSequence} (hT : HasSchwingerSequence σ T) :
    ConfigSpace.IsEuclidInvariant T ∧ ConfigSpace.IsOSPositive T ∧
    ConfigSpace.IsPermSymmetric T ∧ ConfigSpace.IsReflectionReal T := by
  have hSeq : ConfigSpace.IsLinearFunctionalSeq T :=
    ⟨hT.2.1, fun m => (hT.2.2 m).1.1⟩
  have hCont : ConfigSpace.IsContinuousSeq T := fun m => (hT.2.2 m).1
  obtain ⟨k, c, hbd⟩ := exists_boundedExtensionFamily hT
  obtain ⟨-, hpt, -⟩ := hcarry (evalOnMap σ) _ k c hσ hbd
  have hMotion : ∀ (m : ℕ) (φ : schwartzFlatOffDiagonal (m + 1))
      (r : Motions.RigidMotion)
      (h : Motions.actOnFun r φ.1 ∈ schwartzFlatOffDiagonal (m + 1)),
      T.atSucc m ⟨_, h⟩ = T.atSucc m φ := by
    intro m φ r h
    obtain ⟨h', e⟩ := (hpt (m + 1) (Nat.succ_pos m) ⟨φ.1, mem_flatSchwartzSet_of_offDiagonal φ.2⟩).1 r
      (sepTupleInvariant_of ht hr r (m + 1))
    rwa [flatSequenceAsMaps_succ T m _ ⟨_, h⟩ rfl, flatSequenceAsMaps_succ T m _ φ rfl] at e
  have hE1 : ConfigSpace.IsEuclidInvariant T := by
    intro m φ r h
    obtain ⟨R, hR, v, hv⟩ := r.2
    have hfun : ConfigSpace.motionAct r φ.1 =
        Motions.actOnFun ⟨R, hR, v⟩ φ.1 := by
      funext x
      simp only [Motions.actOnFun, ConfigSpace.motionAct]
      exact congrArg φ.1 (funext fun i =>
        ConfigSpace.EuclidMotion.invMap_eq r hR hv _)
    have h' : Motions.actOnFun ⟨R, hR, v⟩ φ.1 ∈ schwartzFlatOffDiagonal (m + 1) :=
      hfun ▸ h
    rw [← hMotion m φ ⟨R, hR, v⟩ h']
    exact congrArg _ (Subtype.ext hfun)
  have hE3 : ConfigSpace.IsPermSymmetric T := by
    intro m φ ς h
    obtain ⟨h', e⟩ := (hpt (m + 1) (Nat.succ_pos m) ⟨φ.1, mem_flatSchwartzSet_of_offDiagonal φ.2⟩).2.1
      (sepTupleSymmetric_of hsym (m + 1)) ς
    rwa [flatSequenceAsMaps_succ T m _ ⟨_, h⟩ rfl, flatSequenceAsMaps_succ T m _ φ rfl] at e
  have hReal : ConfigSpace.IsReflectionReal T := by
    intro m φ h
    obtain ⟨h', e⟩ := (hpt (m + 1) (Nat.succ_pos m) ⟨φ.1, mem_flatSchwartzSet_of_offDiagonal φ.2⟩).2.2.2.2
      (sepTupleInvariant_of ht hr _ (m + 1))
    rwa [flatSequenceAsMaps_succ T m _ ⟨_, h⟩ rfl, flatSequenceAsMaps_succ T m _ φ rfl] at e
  have hE2 : ConfigSpace.IsOSPositive T :=
    hrp (evalOnMap σ) T hσ hSeq hCont (agreesOnTensors_of hT) (isFormPositive_of hpos)
  exact ⟨hE1, hE2, hE3, hReal⟩
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
theorem flatSequence_eq_of_isSchwingerFamily (hOne : TestSpaces.SchwingerUniqueAtEachOrder)
    {σ : TestSpaces.SepTuple → ℝ} (hσ : TestSpaces.IsSepFunctional σ)
    {T T' : FlatSequence} (h₀ : ∀ c, T 0 c = c.1) (h₀' : ∀ c, T' 0 c = c.1)
    (hT : TestSpaces.IsSchwingerFamily σ (flatSequenceAsMaps T))
    (hT' : TestSpaces.IsSchwingerFamily σ (flatSequenceAsMaps T')) : T = T' := by
  funext n
  cases n with
  | zero =>
    funext c
    rw [h₀, h₀']
  | succ m =>
    funext φ
    have e := hOne σ hσ (m + 1) _ _
      ((TestSpaces.isSchwingerFamily_iff_forall_order _ _).1 hT (m + 1))
      ((TestSpaces.isSchwingerFamily_iff_forall_order _ _).1 hT' (m + 1))
    have a := ComponentConditions.flatSequenceAsMaps_succ T m
      ⟨φ.1, ComponentConditions.mem_flatSchwartzSet_of_offDiagonal φ.2⟩ φ rfl
    have b := ComponentConditions.flatSequenceAsMaps_succ T' m
      ⟨φ.1, ComponentConditions.mem_flatSchwartzSet_of_offDiagonal φ.2⟩ φ rfl
    exact a.symm.trans ((congrFun e _).trans b)
theorem euclidNormVec_smul {t : ℝ} (ht : 0 ≤ t) (v : AmbientSpace) :
    euclidNormVec (t • v) = t * euclidNormVec v := by
  unfold euclidNormVec
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
theorem euclidNormVec_pos_of_ne_zero {v : AmbientSpace} (hv : v ≠ 0) : 0 < euclidNormVec v := by
  refine Real.sqrt_pos.2 (Finset.sum_pos' (fun i _ => sq_nonneg (v i)) ?_)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
theorem tendsto_juxt_translate {σ : TupleFunctional} (hfar : ClustersAtInfinity σ)
    (X Y : SepTuple) {v : AmbientSpace} (hv : v ≠ 0) :
    Tendsto (fun t : ℝ => σ (SepTuple.juxt X (push (SeparatedTuples.translate (t • v)) Y))) atTop
      (𝓝 (σ X * σ Y)) := by
  obtain ⟨C, r, hC⟩ := hfar X Y
  have ha := euclidNormVec_pos_of_ne_zero hv
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun t : ℝ => |C| * ((t * euclidNormVec v) ^ 2)⁻¹) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun t : ℝ => t * euclidNormVec v) atTop atTop :=
      tendsto_id.atTop_mul_const ha
    have h₂ : Tendsto (fun t : ℝ => (t * euclidNormVec v) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num)).comp h₁
    simpa using (tendsto_inv_atTop_zero.comp h₂).const_mul |C|
  have hev : ∀ᶠ t : ℝ in atTop, r ≤ t * euclidNormVec v ∧ 0 ≤ t :=
    ((tendsto_id.atTop_mul_const ha).eventually_ge_atTop r).and (eventually_ge_atTop 0)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (hev.mono fun t ht => ?_) hlim
  have hd := euclidNormVec_smul ht.2 v
  have hb := (hC (t • v) (hd ▸ ht.1)).2
  rw [hd] at hb
  rw [Real.norm_eq_abs]
  exact hb.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
theorem evalOnMap_ofList (σ : TupleFunctional) (Z : SepTuple) : evalOnMap σ (ofList Z) = σ Z := by rw [evalOnMap, toList_ofList]
theorem cluster_of_tuple_bounds {σ : TupleFunctional} {T : FlatSequence}
    (hfun : TestSpaces.IsSepFunctional (evalOnMap σ))
    (ht : ∀ v, σ.IsInvariant (SeparatedTuples.translate v))
    (h : IsPosSemidef (reflectionForm σ)) (hT : HasSchwingerSequence σ T)
    (hfar : ClustersAtInfinity σ) (hTr : WightmanReconstruction.ClusteringTransfer.Statement) :
    ConfigSpace.HasClusterProperty T := by
  have hmaps := isSchwingerFamily_flatSequenceAsMaps hT
  have hv : ∀ Z, evalOnMap σ (ofList Z) = σ Z := evalOnMap_ofList σ
  have hinv : WightmanReconstruction.IsTranslationInvariant (evalOnMap σ) := fun y X => by
    refine evalOnMap_eq_of_invariant (r := UpperHalfTensors.translateMotion y) ?_ X.2 _ rfl
    have e : (UpperHalfTensors.translateMotion y).toFun = SeparatedTuples.translate y := by
      funext u
      simp [Motions.RigidMotion.toFun, UpperHalfTensors.translateMotion, SeparatedTuples.translate]
    rw [e]
    exact ht y
  have hpr : WightmanReconstruction.IsReflectionPositiveOnSpan (evalOnMap σ) := fun F hF =>
    isFormPositive_of h ⟨F, hF⟩
  exact (WightmanReconstruction.hasClusterProperty_iff T).2 fun v hvz hv₀ =>
      hTr _ T v hfun hinv hpr hT.2.1 hmaps hvz fun X _ Y _ => by
        simp only [hv]
        exact tendsto_juxt_translate hfar _ _ hv₀
/-- Spatial clustering and the other OS properties follow before constructing any scalar field. -/
theorem osFromConditions (hcarry : TestSpaces.SchwingerPropertiesTransfer)
    (hrp : ReflectionPositivityFromValues.Statement)
    (hTr : WightmanReconstruction.ClusteringTransfer.Statement)
    (hOne : TestSpaces.SchwingerUniqueAtEachOrder) : OSFromConditionsStatement := by
  intro C σ hc hC h hfun ht hr hsym hG hfar T hT
  obtain ⟨T₂, hT₂, hb⟩ := hG
  obtain rfl : T₂ = T := flatSequence_eq_of_isSchwingerFamily hOne hfun hT₂.2.1 hT.2.1
    (isSchwingerFamily_flatSequenceAsMaps hT₂) (isSchwingerFamily_flatSequenceAsMaps hT)
  obtain ⟨hE1,hE2,hE3,hReal⟩ := os_of_tuple_symmetries hcarry hrp hfun ht hr hsym h hT₂
  exact ⟨⟨hb,hE1,hE2,hE3,cluster_of_tuple_bounds hfun ht h hT₂ hfar hTr,hReal⟩,
    growth_bound_of_satisfiesGrowth hc hC hb⟩
end ComponentConditions
end LimitTheorem
end YangMills.Construction
end
