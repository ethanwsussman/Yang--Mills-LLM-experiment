import YangMills.Construction.Continuum.ClusteringFromTuplesToSchwartzFunctionsProof
import YangMills.Construction.Continuum.TensorBoundsIntegrationBoundsAndDensity
import YangMills.Construction.ReflectionPositivity.LatticeFormulaForTheScalarProductProof
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ENNReal
noncomputable section
namespace YangMills.Construction.AdmissibleForm
open ConfigSpace
open ConfigSpace.UpperCombination (linComb lengthPart)
open ReflectionPositivityFromValues (AgreesOnTensors)
open SchwartzAxioms (seminormAt)
section Terms
theorem cast_mem_flatOffDiagonalAt {p r : ℕ} (e : p = r) {f : FnOrScalar p}
    (h : f ∈ flatOffDiagonalAt p) :
    (e ▸ f : FnOrScalar r) ∈ flatOffDiagonalAt r := by apply _root_.YangMills.Construction.ConfigSpace.DomainsAndFiniteSums.mem_flatOffDiagonalAt_cast <;> assumption
theorem seminormAt_cast {p r : ℕ} (e : p = r) (k : ℕ) (f : FnOrScalar p) :
    seminormAt k (e ▸ f : FnOrScalar r) = seminormAt k f := by
  subst e
  rfl
theorem mem_flatOffDiagonalAt_of_mem_flatSchwartzSet {p : ℕ}
    {f : TestSpaces.PointTuple (p + 1) → ℂ}
    (h : f ∈ TestSpaces.flatSchwartzSet (p + 1)) :
    f ∈ flatOffDiagonalAt (p + 1) :=
  (SchwartzAxioms.flatSchwartzSet_eq (n := p + 1)).subset h
theorem mem_flatSchwartzSet_of_mem_flatOffDiagonalAt {p : ℕ}
    {f : TestSpaces.PointTuple (p + 1) → ℂ}
    (h : f ∈ flatOffDiagonalAt (p + 1)) :
    f ∈ TestSpaces.flatSchwartzSet (p + 1) :=
  (SchwartzAxioms.flatSchwartzSet_eq (n := p + 1)).superset h
theorem const_mul_mem_flatSchwartzSet (hF : TestSpaces.Elementary.BasicProperties) {n : ℕ}
    (hn : 0 < n) (c : ℂ) {φ : TestSpaces.PointTuple n → ℂ}
    (h : φ ∈ TestSpaces.flatSchwartzSet n) :
    (fun x => c * φ x) ∈ TestSpaces.flatSchwartzSet n := by
  obtain ⟨⟨-, hW⟩, ⟨hd, -, -, -, -, -, he, -⟩, -⟩ := hF n hn
  obtain ⟨W, hWs⟩ := hW _ hd
  rw [he] at h ⊢
  have hmem : φ ∈ W := by
    rw [← SetLike.mem_coe, hWs]
    exact h
  have hsmul := W.smul_mem c hmem
  rw [← SetLike.mem_coe, hWs] at hsmul
  exact hsmul
theorem mem_flatSchwartzSet_of_positiveTime (hF : TestSpaces.Elementary.BasicProperties) {n : ℕ}
    (hn : 0 < n) {φ : TestSpaces.PointTuple n → ℂ}
    (h : φ ∈ SchwartzAxioms.positiveTimeSchwartz n) :
    φ ∈ TestSpaces.flatSchwartzSet n := by
  obtain ⟨-, ⟨-, -, -, -, -, -, -, hl⟩, -⟩ := hF n hn
  exact hl φ h.1 (Or.inl h.2)
theorem reflectConj_properties (hF : TestSpaces.Elementary.BasicProperties)
    (hO : TestFunctionOps.OperationsStatement) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    {φ : TestSpaces.PointTuple n → ℂ} (h : φ ∈ SchwartzAxioms.positiveTimeSchwartz n) :
    Motions.reflectConj φ ∈ TestSpaces.schwartzSet n ∧
      TestSpaces.VanishesToInfiniteOrderOff (Motions.reflectConj φ)
        (TestSpaces.negativeTimeLocus n) ∧
      Motions.reflectConj φ ∈ TestSpaces.flatSchwartzSet n ∧
      TestSpaces.weightedSeminorm k (Motions.reflectConj φ) = TestSpaces.weightedSeminorm k φ := by
  obtain ⟨-, hφ, -, -⟩ := (hO.1 n k hn hk 1 Motions.RigidMotion.timeReflection)
  obtain ⟨hK, hN, hf⟩ := hφ φ h.1
  have hs := hK.2.2.1
  have hflat := hf.1 h.2
  obtain ⟨-, ⟨-, -, -, -, -, -, -, hl⟩, -⟩ := hF n hn
  exact ⟨hs, hflat, hl _ hs (Or.inr hflat), hN.2.1⟩
theorem reflected_tensor_mem_and_le (hF : TestSpaces.Elementary.BasicProperties)
    (hO : TestFunctionOps.OperationsStatement)
    (hT : TestSpaces.TestSpaceFacts.Statement) {q q' : ℕ}
    (χ : FnOrScalar q) (ψ : FnOrScalar q')
    (hχ : χ ∈ flatOffPosTimeAt q) (hψ : ψ ∈ flatOffPosTimeAt q')
    {k : ℕ} (hk : 1 ≤ k) :
    tensorAt (flipConjAt χ) ψ ∈ flatOffDiagonalAt (q + q') ∧
      seminormAt k (tensorAt (flipConjAt χ) ψ) ≤
        seminormAt k χ * seminormAt k ψ := by
  obtain ⟨hTP, hNF, -, -⟩ := hT
  cases q with
  | zero =>
    cases q' with
    | zero =>
      refine ⟨Set.mem_univ _, ?_⟩
      change ENNReal.ofReal ‖(conj (show ℂ from χ) * (show ℂ from ψ) : ℂ)‖ ≤
        ENNReal.ofReal ‖(show ℂ from χ)‖ * ENNReal.ofReal ‖(show ℂ from ψ)‖
      rw [norm_mul, RCLike.norm_conj, ENNReal.ofReal_mul (norm_nonneg _)]
    | succ m =>
      have hpos := (SchwartzAxioms.positiveTimeSchwartz_eq (n := m + 1)).superset hψ
      have hfl := mem_flatSchwartzSet_of_positiveTime hF (Nat.succ_pos m) hpos
      have e : tensorAt (flipConjAt χ) ψ =
          (Nat.zero_add (m + 1)).symm ▸ smulAt (conj (show ℂ from χ)) ψ :=
        tensorAt_scalar_left (p' := m + 1) (conj (show ℂ from χ)) ψ
      rw [e]
      refine ⟨cast_mem_flatOffDiagonalAt _ (mem_flatOffDiagonalAt_of_mem_flatSchwartzSet
        (const_mul_mem_flatSchwartzSet hF (Nat.succ_pos m) (conj (show ℂ from χ)) hfl)), ?_⟩
      rw [seminormAt_cast]
      refine le_of_eq ?_
      have := hNF (m + 1) k (Nat.succ_pos m) hk (conj (show ℂ from χ)) ψ hpos.1
      rw [RCLike.norm_conj] at this
      exact this
  | succ p =>
    have hpos := (SchwartzAxioms.positiveTimeSchwartz_eq (n := p + 1)).superset hχ
    obtain ⟨hs, hneg, hfl, hnorm⟩ := reflectConj_properties hF hO (Nat.succ_pos p) hk hpos
    cases q' with
    | zero =>
      refine ⟨mem_flatOffDiagonalAt_of_mem_flatSchwartzSet
        (const_mul_mem_flatSchwartzSet hF (Nat.succ_pos p) (show ℂ from ψ) hfl), ?_⟩
      refine le_of_eq ?_
      have := hNF (p + 1) k (Nat.succ_pos p) hk (show ℂ from ψ) _ hs
      rw [hnorm] at this
      exact this.trans (mul_comm _ _)
    | succ m =>
      have hpos' := (SchwartzAxioms.positiveTimeSchwartz_eq (n := m + 1)).superset hψ
      obtain ⟨-, h₂, h₃⟩ :=
        hTP (p + 1) (m + 1) k (Nat.succ_pos p) (Nat.succ_pos m) hk _ hs _ hpos'.1
      refine ⟨mem_flatOffDiagonalAt_of_mem_flatSchwartzSet (h₃ hneg hpos'.2), ?_⟩
      have h₂' : seminormAt k (tensorAt (flipConjAt χ) ψ) ≤
          TestSpaces.weightedSeminorm k (Motions.reflectConj χ) *
            TestSpaces.weightedSeminorm k ψ := h₂
      rw [hnorm] at h₂'
      exact h₂'
variable {S : FlatSequence} {a : ℕ → ℝ} {kE : ℕ}
theorem norm_evalAt_le (hF : TestSpaces.Elementary.BasicProperties) (h : HasGrowthBound S a kE)
    {n : ℕ} (f : FnOrScalar n) (hf : f ∈ flatOffDiagonalAt n) {k : ℕ} (hkn : kE * n ≤ k) :
    ENNReal.ofReal ‖S.evalAt f‖ ≤ ENNReal.ofReal (a n) * seminormAt k f := by
  rw [FlatSequence.evalAt_of_mem S hf]
  cases n with
  | zero =>
    rw [h.isCLMSequence.1 ⟨f, hf⟩, h.coeff_zero]
    simp [seminormAt]
  | succ m =>
    have hb := h.bound m ⟨f, hf⟩
    have ht := mem_flatSchwartzSet_of_mem_flatOffDiagonalAt hf
    have hpos : 0 < kE * (m + 1) := Nat.mul_pos h.one_le (Nat.succ_pos m)
    have hfin : TestSpaces.weightedSeminorm (kE * (m + 1)) f ≠ ⊤ := (ht.1.2 _ hpos).ne
    have hmono : TestSpaces.weightedSeminorm (kE * (m + 1)) f ≤
        TestSpaces.weightedSeminorm k f :=
      ((hF (m + 1) (Nat.succ_pos m)).1.1 f ht.1 f ht.1 0 0).2.1 _ _ hpos hkn |>.1
    calc ENNReal.ofReal ‖S (m + 1) ⟨f, hf⟩‖
        ≤ ENNReal.ofReal (a (m + 1) * (TestSpaces.weightedSeminorm (kE * (m + 1)) f).toReal) :=
          ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal (a (m + 1)) * TestSpaces.weightedSeminorm (kE * (m + 1)) f := by
          rw [ENNReal.ofReal_mul (h.coeff_nonneg _), ENNReal.ofReal_toReal hfin]
      _ ≤ ENNReal.ofReal (a (m + 1)) * seminormAt k f := by
          gcongr
          exact hmono
theorem termEstimate (hF : TestSpaces.Elementary.BasicProperties)
    (hO : TestFunctionOps.OperationsStatement)
    (hT : TestSpaces.TestSpaceFacts.Statement)
    (h : HasGrowthBound S a kE) : TermEstimate S a kE := by
  intro q q' χ ψ k hk hkn
  obtain ⟨h₁, h₂⟩ := reflected_tensor_mem_and_le hF hO hT χ.1 ψ.1 χ.2 ψ.2 hk
  refine ⟨h₁, (norm_evalAt_le hF h _ h₁ hkn).trans ?_⟩
  rw [mul_assoc]
  gcongr
theorem seminormAt_zeroOfDegree (hF : TestSpaces.Elementary.BasicProperties) (q : ℕ) {k : ℕ}
    (hk : 1 ≤ k) (h : zeroOfDegree q ∈ flatOffPosTimeAt q) :
    seminormAt k (zeroOfDegree q) = 0 := by
  cases q with
  | zero => simp [seminormAt, zeroOfDegree]
  | succ m =>
    have hs := ((SchwartzAxioms.positiveTimeSchwartz_eq (n := m + 1)).superset h).1
    have hb := (((hF (m + 1) (Nat.succ_pos m)).1.1 _ hs _ hs 0 0).2.1 k k hk le_rfl).2.1
    simp only [norm_zero, ENNReal.ofReal_zero, zero_mul, add_zero, nonpos_iff_eq_zero] at hb
    refine Eq.trans ?_ hb
    refine congrArg (TestSpaces.weightedSeminorm k) (funext fun x => ?_)
    simp [TestSpaces.Elementary.linComb, zeroOfDegree]
theorem evalAt_tensor_eq_zero_of_zero (hF : TestSpaces.Elementary.BasicProperties)
    (hO : TestFunctionOps.OperationsStatement)
    (hT : TestSpaces.TestSpaceFacts.Statement)
    (h : HasGrowthBound S a kE) {q q' : ℕ}
    (χ : FnOrScalar q) (ψ : FnOrScalar q')
    (hχ : χ ∈ flatOffPosTimeAt q) (hψ : ψ ∈ flatOffPosTimeAt q')
    (hz : χ = zeroOfDegree q ∨ ψ = zeroOfDegree q') :
    S.evalAt (tensorAt (flipConjAt χ) ψ) = 0 := by
  have hk : 1 ≤ kE * (q + q') + 1 := by omega
  have hb := (termEstimate hF hO hT h) q q' ⟨χ, hχ⟩ ⟨ψ, hψ⟩ _ hk (by omega)
  have hzero : ENNReal.ofReal (a (q + q')) * seminormAt (kE * (q + q') + 1) χ *
      seminormAt (kE * (q + q') + 1) ψ = 0 := by
    rcases hz with rfl | rfl
    · rw [seminormAt_zeroOfDegree hF q hk hχ]
      simp
    · rw [seminormAt_zeroOfDegree hF q' hk hψ]
      simp
  have h₂ := hb.2
  simp only [hzero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h₂
  exact norm_le_zero_iff.1 h₂
theorem reflectionPairing_eq_sum_range (φ ψ : (q : ℕ) → FnOrScalar q) (q₀ : ℕ)
    (hz : ∀ q q', q₀ < q ∨ q₀ < q' →
      S.evalAt (tensorAt (flipConjAt (φ q)) (ψ q')) = 0) :
    S.reflectionPairing φ ψ =
      ∑ q ∈ Finset.range (q₀ + 1), ∑ q' ∈ Finset.range (q₀ + 1),
        S.evalAt (tensorAt (flipConjAt (φ q)) (ψ q')) := by apply _root_.YangMills.Construction.AdmissibleClustering.reflectionPairing_eq_finite_sum <;> assumption
theorem formEstimate (hF : TestSpaces.Elementary.BasicProperties)
    (hO : TestFunctionOps.OperationsStatement)
    (hT : TestSpaces.TestSpaceFacts.Statement)
    (hP : SesquilinearPosSemidefStatement)
    (h : HasGrowthBound S a kE) : FormEstimate S a kE := by
  refine ⟨(hP S h.isCLMSequence).1, fun Φ Ψ q₀ hq₀ hΦ hΨ => ?_⟩
  have e := reflectionPairing_eq_sum_range (S := S) (fun q => (Φ.1 q).1) (fun q => (Ψ.1 q).1) q₀
    fun q q' hq =>
      evalAt_tensor_eq_zero_of_zero hF hO hT h _ _ (Φ.1 q).2 (Ψ.1 q').2 (by
        rcases hq with hq | hq
        · exact Or.inl (hΦ q hq)
        · exact Or.inr (hΨ q' hq))
  rw [FlatSequence.reflectionForm, e]
  have hk : 1 ≤ 2 * kE * q₀ := by
    have := Nat.mul_pos (Nat.mul_pos (by norm_num : 0 < 2) h.one_le) hq₀
    omega
  refine (ENNReal.ofReal_le_ofReal (norm_sum_le _ _)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _]
  refine Finset.sum_le_sum fun q hq => ?_
  refine (ENNReal.ofReal_le_ofReal (norm_sum_le _ _)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _]
  refine Finset.sum_le_sum fun q' hq' => ?_
  have hq₁ : q ≤ q₀ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
  have hq₂ : q' ≤ q₀ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq')
  have hkq : kE * (q + q') ≤ 2 * kE * q₀ := by
    calc kE * (q + q') ≤ kE * (2 * q₀) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * kE * q₀ := by ring
  exact ((termEstimate hF hO hT h) q q' (Φ.1 q) (Ψ.1 q') _ hk hkq).2
end Terms
section Tuples
open SeparatedTuples (SepTuple push pushSpan pushList formalMul)
open TupleLists (toList)
theorem ofConfigFn_toConfigFn {n : ℕ} (f : FnOrScalar n) :
    ofConfigFn (toConfigFn f) = f := by
  cases n <;> rfl
theorem ofConfigFn_zero (r : ℕ) : ofConfigFn (fun _ : Config r => (0 : ℂ)) = zeroOfDegree r := by apply _root_.YangMills.Construction.AdmissibleClustering.ofConfigFn_zero <;> assumption
theorem toConfigFn_tupleTensor {q : ℕ} (f : Fin q → (Fin 4 → ℝ) → ℝ)
    (x : TestSpaces.PointTuple q) :
    toConfigFn (entryTensor f) x = ∏ i, (f i (x i) : ℂ) := by
  cases q with
  | zero => simp [toConfigFn, entryTensor]
  | succ q => rfl
theorem cast_eq_ofConfigFn {p r : ℕ} (e : p + 1 = r) (ψ : FnOrScalar (p + 1)) :
    (e ▸ ψ : FnOrScalar r) =
      ofConfigFn fun z : TestSpaces.PointTuple r =>
        (show TestSpaces.PointTuple (p + 1) → ℂ from ψ) fun i => z (Fin.cast e i) := by
  subst e
  rfl
theorem tensorAt_scalar_fn {m : ℕ} (a : ℂ) (b : TestSpaces.PointTuple (m + 1) → ℂ) :
    tensorAt (p := 0) (p' := m + 1) (conj a : ℂ) b =
      ofConfigFn (TestSpaces.tensorFun
        (Motions.reflectConj (fun _ : TestSpaces.PointTuple 0 => a)) b) := by
  refine (tensorAt_scalar_left (p' := m + 1) (conj a) b).trans
    ((cast_eq_ofConfigFn (Nat.zero_add (m + 1)).symm _).trans
      (congrArg ofConfigFn (funext fun z => ?_)))
  have e : (fun i => z (Fin.cast (Nat.zero_add (m + 1)).symm i)) = TestSpaces.rightPart z :=
    funext fun i => congrArg z (Fin.ext (by simp))
  change conj a * b _ = conj a * b _
  rw [e]
theorem tensorAt_fn_scalar {p : ℕ} (a : TestSpaces.PointTuple (p + 1) → ℂ) (b : ℂ) :
    tensorAt (p := p + 1) (p' := 0) (flipConj a) b =
      ofConfigFn (n := p + 1 + 0) (TestSpaces.tensorFun (Motions.reflectConj a)
        (fun _ : TestSpaces.PointTuple 0 => b)) := by
  change (fun y : TestSpaces.PointTuple (p + 1) => b * flipConj a y) =
    TestSpaces.tensorFun (q := p + 1) (q' := 0) (Motions.reflectConj a) (fun _ => b)
  funext z
  exact mul_comm _ _
theorem tensorAt_flipConjAt_eq {q q' : ℕ} (a : FnOrScalar q) (b : FnOrScalar q') :
    tensorAt (flipConjAt a) b =
      ofConfigFn (TestSpaces.tensorFun (Motions.reflectConj (toConfigFn a))
        (toConfigFn b)) := by
  cases q with
  | zero =>
    cases q' with
    | zero => rfl
    | succ m => exact tensorAt_scalar_fn a b
  | succ p =>
    cases q' with
    | zero => exact tensorAt_fn_scalar a b
    | succ m => rfl
theorem tensorAt_tupleTensor_eq {q q' : ℕ} (X : Fin q → (Fin 4 → ℝ) → ℝ)
    (Y : Fin q' → (Fin 4 → ℝ) → ℝ) :
    tensorAt (flipConjAt (entryTensor X)) (entryTensor Y) =
      ofConfigFn (TestSpaces.tensorProdComplex
        (Motions.concatTuple (Motions.reflectTuple X) Y)) := by
  rw [tensorAt_flipConjAt_eq]
  refine congrArg ofConfigFn (funext fun z => ?_)
  simp only [TestSpaces.tensorFun, Motions.reflectConj, toConfigFn_tupleTensor,
    TestSpaces.tensorProdComplex, TestSpaces.tensorProd, Motions.concatTuple, map_prod,
    Complex.conj_ofReal, Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    Motions.reflectTuple, Motions.reflectFun_eq]
  rw [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_prod]
  rfl
variable {S : FlatSequence}
theorem evalAt_tensorProdComplex (hF : TestSpaces.Elementary.BasicProperties)
    (hS : IsCLMSequence S) (L : SeparatedTuples.TupleFunctional)
    (hV : AgreesOnTensors (fun X => L (toList X)) S) {n : ℕ}
    (Z : TestSpaces.SepTupleOfCard n) (hs : TestSpaces.HasSmoothComponents Set.univ Z.1) :
    S.evalAt (ofConfigFn (TestSpaces.tensorProdComplex Z.1)) = (L (toList ⟨n, Z⟩) : ℂ) := by
  cases n with
  | zero =>
    have e : toList ⟨0, Z⟩ = SepTuple.nil := Subtype.ext (by simp [toList, SepTuple.nil])
    have h0 : ofConfigFn (n := 0) (TestSpaces.tensorProdComplex Z.1) ∈
        flatOffDiagonalAt 0 := Set.mem_univ _
    rw [e, L.map_nil, FlatSequence.evalAt_of_mem S h0]
    refine (hS.1 ⟨_, h0⟩).trans ?_
    simp [ofConfigFn, TestSpaces.tensorProdComplex, TestSpaces.tensorProd]
  | succ m =>
    have hm : ofConfigFn (n := m + 1) (TestSpaces.tensorProdComplex Z.1) ∈
        flatOffDiagonalAt (m + 1) := mem_flatOffDiagonalAt_of_mem_flatSchwartzSet
      (((hF (m + 1) (Nat.succ_pos m)).2.2.2.1 Set.univ isOpen_univ Z.1 Z.2).2 hs).2.1
    rw [FlatSequence.evalAt_of_mem S hm]
    exact hV m Z hs hm
theorem invMap_timeReflection :
    SeparatedTuples.invMap TimeAxis.timeReflection = TimeAxis.timeReflection := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.invMap_timeReflection <;> assumption
theorem pushList_timeReflection {q : ℕ} (X : Fin q → (Fin 4 → ℝ) → ℝ) :
    pushList TimeAxis.timeReflection (List.ofFn X) = List.ofFn (Motions.reflectTuple X) := by
  rw [pushList, List.map_ofFn, invMap_timeReflection]
  congr 1
  funext i
  simp only [Function.comp_apply, Motions.reflectTuple]
  rw [Motions.reflectFun_eq]
  rfl
theorem toList_val_eq_append {q q' : ℕ} (Z : TestSpaces.SepTupleOfCard (q + q'))
    (A : Fin q → (Fin 4 → ℝ) → ℝ) (B : Fin q' → (Fin 4 → ℝ) → ℝ)
    (hZ : Z.1 = Motions.concatTuple A B) :
    (toList ⟨q + q', Z⟩).1 = List.ofFn A ++ List.ofFn B := by
  change List.ofFn Z.1 = _
  rw [hZ]
  exact List.ofFn_fin_append A B
theorem juxt_push_eq_toList {Y Y' : SepTuple} {X X' : UpperFamily}
    (hY : ListMatchesFamily Y X) (hY' : ListMatchesFamily Y' X')
    (Z : TestSpaces.SepTupleOfCard (X.1 + X'.1))
    (hZ : Z.1 = Motions.concatTuple (Motions.reflectTuple X.2.1) X'.2.1) :
    SepTuple.juxt (push TimeAxis.timeReflection Y) Y' = toList ⟨_, Z⟩ := by
  have hlist : (toList ⟨_, Z⟩).1 =
      List.ofFn (Motions.reflectTuple X.2.1) ++ Y'.1 := by
    rw [toList_val_eq_append _ _ _ hZ, hY']
  have h₂ := (toList ⟨_, Z⟩).2
  rw [hlist] at h₂
  have hsep : SeparatedTuples.IsDisjointlySupported (pushList TimeAxis.timeReflection Y.1) := by
    rw [hY, pushList_timeReflection]
    exact ⟨fun f hf => h₂.1 f (List.mem_append_left _ hf), (List.pairwise_append.1 h₂.2).1⟩
  have hact : (push TimeAxis.timeReflection Y).1 = List.ofFn (Motions.reflectTuple X.2.1) := by
    rw [push, dif_pos hsep]
    change pushList TimeAxis.timeReflection Y.1 = _
    rw [hY]
    exact pushList_timeReflection _
  have hdef : SepTuple.Composable (push TimeAxis.timeReflection Y) Y' := by
    intro f hf g hg
    rw [hact] at hf
    exact (List.pairwise_append.1 h₂.2).2.2 f hf g hg
  exact Subtype.ext (by rw [SepTuple.juxt_val hdef, hact, hlist])
theorem reflectedPairValue_eq (L : SeparatedTuples.TupleFunctional) (Y Y' : SepTuple) :
    reflectedPairValue L Y Y' = (L (SepTuple.juxt (push TimeAxis.timeReflection Y) Y') : ℂ) := by apply _root_.YangMills.Construction.AdmissibleClustering.reflectedPairValue_eq <;> assumption
theorem disjointSupportTuples_of_separatedFamilies {q : ℕ} {f : Fin q → (Fin 4 → ℝ) → ℝ}
    (h : f ∈ separatedFamilies upperHalfSpace q) :
    f ∈ TestSpaces.disjointSupportTuples TestSpaces.upperHalfSpace q := by
  refine ⟨fun i => ?_, h.2⟩
  obtain ⟨-, a, b, c⟩ := mem_realC1CompactIn_iff.1 (h.1 i)
  exact ⟨a, b, c⟩
theorem hasSmoothComponents_of_separatedFamilies {q : ℕ} {f : Fin q → (Fin 4 → ℝ) → ℝ}
    (h : f ∈ separatedFamilies upperHalfSpace q) (hs : AllSmoothCompact f) :
    TestSpaces.HasSmoothComponents TestSpaces.upperHalfSpace f := by
  intro i
  obtain ⟨-, -, -, c⟩ := mem_realC1CompactIn_iff.1 (h.1 i)
  obtain ⟨-, a, b, -⟩ := mem_realSmoothCompactIn_iff.1 (hs i)
  exact ⟨a, b, c⟩
theorem lengthPart_self {ι : Type} [Fintype ι] {n : ℕ} (c : ι → ℂ)
    (f : ι → {f : Fin n → (Fin 4 → ℝ) → ℝ // f ∈ separatedFamilies upperHalfSpace n}) :
    lengthPart c (fun i => (⟨n, f i⟩ : UpperFamily)) n =
      ofConfigFn fun x => ∑ i, c i * toConfigFn (entryTensor (f i).1) x := by
  refine congrArg ofConfigFn (funext fun x => ?_)
  exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun _ => rfl) _ _ fun i => rfl
theorem lengthPart_of_ne {ι : Type} [Fintype ι] {n r : ℕ} (hr : r ≠ n) (c : ι → ℂ)
    (f : ι → {f : Fin n → (Fin 4 → ℝ) → ℝ // f ∈ separatedFamilies upperHalfSpace n}) :
    lengthPart c (fun i => (⟨n, f i⟩ : UpperFamily)) r = zeroOfDegree r := by
  have : IsEmpty {i // familyLength (UpperFamily.toSeparatedFamily ⟨n, f i⟩) = r} :=
    ⟨fun i => hr i.2.symm⟩
  rw [← ofConfigFn_zero r]
  refine congrArg ofConfigFn (funext fun x => ?_)
  exact Fintype.sum_empty _
end Tuples
section Combinations
open SeparatedTuples (SepTuple push pushSpan formalMul)
open TupleLists (toList)
open ConfigSpace.UpperCombination (ofFamily)
def flatPairing (S : FlatSequence) (F F' : UpperCombination) : ℂ :=
  S.reflectionPairing (combinationSequence F) (combinationSequence F')
def toAdmissibleSeq (hA : CombinationSequenceAdmissibleLinear)
    (F : UpperCombination) (hF : F.HasSmoothFamilies) : AdmissibleSeq :=
  ⟨fun q => ⟨combinationSequence F q, (hA.2.1 F hF).2.choose q⟩, (hA.2.1 F hF).2.choose_spec⟩
theorem hasSmoothFamilies_add (hA : CombinationSequenceAdmissibleLinear)
    {F F' : UpperCombination} (hF : F.HasSmoothFamilies) (hF' : F'.HasSmoothFamilies) (a b : ℂ) :
    (a • F + b • F').HasSmoothFamilies := by
  obtain ⟨W, hW⟩ := hA.2.2.1
  have h₁ : F ∈ W := by
    rw [← SetLike.mem_coe, hW]
    exact hF
  have h₂ : F' ∈ W := by
    rw [← SetLike.mem_coe, hW]
    exact hF'
  have h₃ := W.add_mem (W.smul_mem a h₁) (W.smul_mem b h₂)
  rw [← SetLike.mem_coe, hW] at h₃
  exact h₃
variable {S : FlatSequence}
theorem flatPairing_add_left (hA : CombinationSequenceAdmissibleLinear)
    (hP : SesquilinearPosSemidefStatement)
    (hS : IsCLMSequence S) {F₁ F₂ F' : UpperCombination}
    (h₁ : F₁.HasSmoothFamilies) (h₂ : F₂.HasSmoothFamilies) (h' : F'.HasSmoothFamilies)
    (a b : ℂ) :
    flatPairing S (a • F₁ + b • F₂) F' =
      conj a * flatPairing S F₁ F' + conj b * flatPairing S F₂ F' :=
  (hP S hS).1.2.2.1 a b (toAdmissibleSeq hA _ h₁) (toAdmissibleSeq hA _ h₂)
    (toAdmissibleSeq hA _ (hasSmoothFamilies_add hA h₁ h₂ a b)) (toAdmissibleSeq hA _ h')
    fun q => hA.2.2.2.1 a b _ _ h₁ h₂ q
theorem flatPairing_add_right (hA : CombinationSequenceAdmissibleLinear)
    (hP : SesquilinearPosSemidefStatement)
    (hS : IsCLMSequence S) {F F₁ F₂ : UpperCombination}
    (h : F.HasSmoothFamilies) (h₁ : F₁.HasSmoothFamilies) (h₂ : F₂.HasSmoothFamilies)
    (a b : ℂ) :
    flatPairing S F (a • F₁ + b • F₂) = a * flatPairing S F F₁ + b * flatPairing S F F₂ :=
  (hP S hS).1.2.2.2 a b (toAdmissibleSeq hA _ h) (toAdmissibleSeq hA _ h₁)
    (toAdmissibleSeq hA _ h₂) (toAdmissibleSeq hA _ (hasSmoothFamilies_add hA h₁ h₂ a b))
    fun q => hA.2.2.2.1 a b _ _ h₁ h₂ q
theorem flatPairing_sum_left (hA : CombinationSequenceAdmissibleLinear)
    (hP : SesquilinearPosSemidefStatement)
    (hS : IsCLMSequence S) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (T : ι → UpperCombination) (hT : ∀ i, (T i).HasSmoothFamilies) {F' : UpperCombination}
    (h' : F'.HasSmoothFamilies) :
    (∑ i ∈ s, c i • T i).HasSmoothFamilies ∧
      flatPairing S (∑ i ∈ s, c i • T i) F' = ∑ i ∈ s, conj (c i) * flatPairing S (T i) F' := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : ∑ i ∈ (∅ : Finset ι), c i • T i = (0 : ℂ) • F' + (0 : ℂ) • F' := by simp
    rw [e]
    exact ⟨hasSmoothFamilies_add hA h' h' 0 0, by
      rw [flatPairing_add_left hA hP hS h' h' h' 0 0]
      simp⟩
  | insert i s hi ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have e : c i • T i + ∑ j ∈ s, c j • T j = c i • T i + (1 : ℂ) • ∑ j ∈ s, c j • T j := by
      rw [one_smul]
    rw [e]
    refine ⟨hasSmoothFamilies_add hA (hT i) ih₁ _ _, ?_⟩
    rw [flatPairing_add_left hA hP hS (hT i) ih₁ h', ih₂]
    simp
theorem flatPairing_sum_right (hA : CombinationSequenceAdmissibleLinear)
    (hP : SesquilinearPosSemidefStatement)
    (hS : IsCLMSequence S) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (T : ι → UpperCombination) (hT : ∀ i, (T i).HasSmoothFamilies) {F : UpperCombination}
    (h : F.HasSmoothFamilies) :
    (∑ i ∈ s, c i • T i).HasSmoothFamilies ∧
      flatPairing S F (∑ i ∈ s, c i • T i) = ∑ i ∈ s, c i * flatPairing S F (T i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : ∑ i ∈ (∅ : Finset ι), c i • T i = (0 : ℂ) • F + (0 : ℂ) • F := by simp
    rw [e]
    exact ⟨hasSmoothFamilies_add hA h h 0 0, by
      rw [flatPairing_add_right hA hP hS h h h 0 0]
      simp⟩
  | insert i s hi ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have e : c i • T i + ∑ j ∈ s, c j • T j = c i • T i + (1 : ℂ) • ∑ j ∈ s, c j • T j := by
      rw [one_smul]
    rw [e]
    refine ⟨hasSmoothFamilies_add hA (hT i) ih₁ _ _, ?_⟩
    rw [flatPairing_add_right hA hP hS h (hT i) ih₁, ih₂]
    simp
theorem ofFamily_eq_linComb (X : UpperFamily) :
    ofFamily X = linComb (fun _ : Unit => (1 : ℂ)) fun _ => X := by
  simp [linComb]
theorem hasSmoothFamilies_ofFamily (hA : CombinationSequenceAdmissibleLinear)
    {X : UpperFamily} (hX : AllSmoothCompact X.2.1) :
    (ofFamily X).HasSmoothFamilies := by
  rw [ofFamily_eq_linComb]
  exact hA.1 Unit _ _ fun _ => hX
theorem combinationSequence_ofFamily_self (hA : CombinationSequenceAdmissibleLinear)
    {X : UpperFamily} (hX : AllSmoothCompact X.2.1) :
    combinationSequence (ofFamily X) X.1 = entryTensor X.2.1 := by
  refine ((hA.2.1 _ (hasSmoothFamilies_ofFamily hA hX)).1 Unit (fun _ => 1) (fun _ => X)
    (fun _ => hX) (ofFamily_eq_linComb X) X.1).trans ?_
  refine (lengthPart_self (fun _ : Unit => (1 : ℂ)) fun _ => X.2).trans ?_
  have e : (fun x => ∑ _ : Unit, (1 : ℂ) * toConfigFn (entryTensor X.2.1) x) =
      toConfigFn (entryTensor X.2.1) := funext fun x => by simp
  rw [e, ofConfigFn_toConfigFn]
theorem combinationSequence_ofFamily_of_ne (hA : CombinationSequenceAdmissibleLinear)
    {X : UpperFamily} (hX : AllSmoothCompact X.2.1) {r : ℕ} (hr : r ≠ X.1) :
    combinationSequence (ofFamily X) r = zeroOfDegree r :=
  ((hA.2.1 _ (hasSmoothFamilies_ofFamily hA hX)).1 Unit (fun _ => 1) (fun _ => X) (fun _ => hX)
    (ofFamily_eq_linComb X) r).trans (lengthPart_of_ne hr (fun _ : Unit => (1 : ℂ)) fun _ => X.2)
variable {a : ℕ → ℝ} {kE : ℕ}
theorem flatPairing_ofFamily (hF : TestSpaces.Elementary.BasicProperties)
    (hO : TestFunctionOps.OperationsStatement)
    (hT : TestSpaces.TestSpaceFacts.Statement)
    (hA : CombinationSequenceAdmissibleLinear)
    (h : HasGrowthBound S a kE) (L : SeparatedTuples.TupleFunctional)
    (hV : AgreesOnTensors (fun X => L (toList X)) S) {X X' : UpperFamily}
    (hX : AllSmoothCompact X.2.1)
    (hX' : AllSmoothCompact X'.2.1) {Y Y' : SepTuple} (hY : ListMatchesFamily Y X)
    (hY' : ListMatchesFamily Y' X') :
    flatPairing S (ofFamily X) (ofFamily X') = reflectedPairValue L Y Y' := by
  rw [flatPairing, FlatSequence.reflectionPairing, finsum_eq_single _ (X.1, X'.1)]
  · change S.evalAt (tensorAt (flipConjAt
      (combinationSequence (ofFamily X) X.1)) (combinationSequence (ofFamily X') X'.1)) = _
    rw [combinationSequence_ofFamily_self hA hX, combinationSequence_ofFamily_self hA hX',
      tensorAt_tupleTensor_eq]
    obtain ⟨hZ, hZs, -⟩ := hO.2 X.1 X'.1 X.2.1 X'.2.1
      (disjointSupportTuples_of_separatedFamilies X.2.2)
      (hasSmoothComponents_of_separatedFamilies X.2.2 hX)
      (disjointSupportTuples_of_separatedFamilies X'.2.2)
      (hasSmoothComponents_of_separatedFamilies X'.2.2 hX')
    have e := evalAt_tensorProdComplex hF h.isCLMSequence L hV ⟨_, hZ⟩ hZs
    rw [reflectedPairValue_eq, juxt_push_eq_toList hY hY' ⟨_, hZ⟩ rfl]
    exact e
  · rintro ⟨q, q'⟩ hp
    have hz : q ≠ X.1 ∨ q' ≠ X'.1 := by
      by_contra hn
      exact hp (Prod.ext (Classical.byContradiction fun e => hn (Or.inl e))
        (Classical.byContradiction fun e => hn (Or.inr e)))
    refine evalAt_tensor_eq_zero_of_zero hF hO hT h _ _
      ((hA.2.1 _ (hasSmoothFamilies_ofFamily hA hX)).2.choose q)
      ((hA.2.1 _ (hasSmoothFamilies_ofFamily hA hX')).2.choose q') ?_
    rcases hz with hz | hz
    · exact Or.inl (combinationSequence_ofFamily_of_ne hA hX hz)
    · exact Or.inr (combinationSequence_ofFamily_of_ne hA hX' hz)
theorem formOnTuples (hF : TestSpaces.Elementary.BasicProperties)
    (hO : TestFunctionOps.OperationsStatement)
    (hT : TestSpaces.TestSpaceFacts.Statement)
    (hA : CombinationSequenceAdmissibleLinear)
    (hP : SesquilinearPosSemidefStatement)
    (h : HasGrowthBound S a kE) (L : SeparatedTuples.TupleFunctional)
    (hV : AgreesOnTensors (fun X => L (toList X)) S) : FormOnTuples S L := by
  intro ι κ _ _ c c' X X' Y Y' hX hX' hY hY' Φ Ψ hΦ hΨ
  have hsum : S.reflectionForm Φ Ψ =
      ∑ i, ∑ j, conj (c i) * c' j * reflectedPairValue L (Y i) (Y' j) := by
    have e₁ : (fun q => (Φ.1 q).1) = combinationSequence (linComb c X) := funext hΦ
    have e₂ : (fun q => (Ψ.1 q).1) = combinationSequence (linComb c' X') := funext hΨ
    rw [FlatSequence.reflectionForm, e₁, e₂]
    change flatPairing S _ _ = _
    have sm : ∀ i, (ofFamily (X i)).HasSmoothFamilies :=
      fun i => hasSmoothFamilies_ofFamily hA (hX i)
    have sm' : ∀ j, (ofFamily (X' j)).HasSmoothFamilies :=
      fun j => hasSmoothFamilies_ofFamily hA (hX' j)
    have hL := (flatPairing_sum_left hA hP h.isCLMSequence Finset.univ c
      (fun i => ofFamily (X i)) sm (hA.1 κ c' X' hX')).2
    refine hL.trans (Finset.sum_congr rfl fun i _ => ?_)
    have hR := (flatPairing_sum_right hA hP h.isCLMSequence Finset.univ c'
      (fun j => ofFamily (X' j)) sm' (sm i)).2
    change conj (c i) * flatPairing S (ofFamily (X i)) (∑ j, c' j • ofFamily (X' j)) = _
    rw [hR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [flatPairing_ofFamily hF hO hT hA h L hV (hX i) (hX' j) (hY i) (hY' j)]
    ring
  refine ⟨hsum, fun G G' hG hG' => ?_⟩
  rw [hsum, ReflectionPositivity.TupleForm.reflectionForm]
  have hr : ReflectionPositivity.TupleForm.reflectConj G =
      ∑ i, conj (c i) • SeparatedTuples.basisVec (push TimeAxis.timeReflection (Y i)) := by
    change pushSpan _ (SeparatedTuples.conjugation G.1) = _
    rw [hG, SeparatedTuples.conjugation_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, pushSpan, SeparatedTuples.linearExtend_basisVec]
  rw [hr, hG', SeparatedTuples.formalMul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, SeparatedTuples.TupleFunctional.spanExtension,
    SeparatedTuples.linearExtend_basisVec, reflectedPairValue_eq, smul_eq_mul]
end Combinations
section Approximation
open ConfigSpace.UpperCombination (ofFamily)
theorem linCombAt_one_one_zero_right {r : ℕ} (x : FnOrScalar r) :
    linCombAt 1 1 x (zeroOfDegree r) = x := by
  cases r with
  | zero => exact (by simp : ∀ z : ℂ, (1 : ℂ) * z + 1 * 0 = z) x
  | succ r =>
    funext y
    exact (by simp : (1 : ℂ) * x y + 1 * 0 = x y)
theorem linCombAt_one_one_zero_left {r : ℕ} (x : FnOrScalar r) :
    linCombAt 1 1 (zeroOfDegree r) x = x := by
  cases r with
  | zero => exact (by simp : ∀ z : ℂ, (1 : ℂ) * 0 + 1 * z = z) x
  | succ r =>
    funext y
    exact (by simp : (1 : ℂ) * 0 + 1 * x y = x y)
theorem linCombAt_zero_zero {r : ℕ} (a b : ℂ) :
    linCombAt a b (zeroOfDegree r) (zeroOfDegree r) = zeroOfDegree r := by
  cases r with
  | zero => exact (by simp : a * 0 + b * 0 = (0 : ℂ))
  | succ r =>
    funext y
    exact (by simp : a * 0 + b * 0 = (0 : ℂ))
theorem separatedFamilies_of_disjointSupportTuples {q : ℕ} {f : Fin q → (Fin 4 → ℝ) → ℝ}
    (h : f ∈ TestSpaces.disjointSupportTuples TestSpaces.upperHalfSpace q) :
    f ∈ separatedFamilies upperHalfSpace q := by
  refine ⟨fun i => mem_realC1CompactIn_iff.2 ?_, h.2⟩
  obtain ⟨a, b, c⟩ := h.1 i
  exact ⟨isOpen_upperHalfSpace, a, b, c⟩
theorem allSmoothCompact_of_hasSmoothComponents {q : ℕ} {f : Fin q → (Fin 4 → ℝ) → ℝ}
    (h : TestSpaces.HasSmoothComponents TestSpaces.upperHalfSpace f) :
    AllSmoothCompact f := by
  intro i
  obtain ⟨a, b, -⟩ := h i
  exact mem_realSmoothCompactIn_iff.2 ⟨isOpen_univ, a, b, Set.subset_univ _⟩
theorem smoothApproximation (hT : TestSpaces.TestSpaceFacts.Statement)
    (hA : CombinationSequenceAdmissibleLinear) : SmoothApproximation := by
  intro Φ q₀ _ hΦ k ε hk hε
  have hE := hA.2.2.2.2.1
  have hE0 := hA.2.2.2.2.2.1
  have hE1 := hA.2.2.2.2.2.2
  have key : ∀ n, n ≤ q₀ → ∃ F : UpperCombination, F.HasSmoothFamilies ∧
      combinationSequence F 0 = (Φ.1 0).1 ∧
      (∀ r, 1 ≤ r → r ≤ n →
        seminormAt k ((Φ.1 r).1 - combinationSequence F r) ≤ ENNReal.ofReal ε) ∧
      ∀ r, n < r → combinationSequence F r = zeroOfDegree r := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨(show ℂ from (Φ.1 0).1) • ofFamily UpperFamily.nil +
        (0 : ℂ) • ofFamily UpperFamily.nil, hasSmoothFamilies_add hA hE hE _ _, ?_,
        fun r h₁ h₂ => by omega, fun r hr => ?_⟩
      · rw [hA.2.2.2.1 _ _ _ _ hE hE 0, hE0]
        exact (by simp : ∀ z : ℂ, z * 1 + 0 * 1 = z) _
      · rw [hA.2.2.2.1 _ _ _ _ hE hE r, hE1 r hr, linCombAt_zero_zero]
    | succ n ih =>
      intro hn
      obtain ⟨F, hF, h₀, h₁, h₂⟩ := ih (by omega)
      have hpos := (SchwartzAxioms.positiveTimeSchwartz_eq (n := n + 1)).superset (Φ.1 (n + 1)).2
      obtain ⟨m, c, f, -, hf, hclose⟩ :=
        ((hT.2.2.2 (n + 1) k (Nat.succ_pos n) hk).2 _ hpos.1 hpos.2 ε hε).1
      let g : Fin m → {f : Fin (n + 1) → (Fin 4 → ℝ) → ℝ //
          f ∈ separatedFamilies upperHalfSpace (n + 1)} :=
        fun i => ⟨f i, separatedFamilies_of_disjointSupportTuples (hf i).1⟩
      let X : Fin m → UpperFamily := fun i => ⟨n + 1, g i⟩
      have hXs : ∀ i, AllSmoothCompact (X i).2.1 :=
        fun i => allSmoothCompact_of_hasSmoothComponents (hf i).2
      have hG := hA.1 (Fin m) c X hXs
      have hseq := (hA.2.1 _ hG).1 (Fin m) c X hXs rfl
      have hlin := hA.2.2.2.1 1 1 F (linComb c X) hF hG
      have hother : ∀ r, r ≠ n + 1 →
          combinationSequence ((1 : ℂ) • F + (1 : ℂ) • linComb c X) r =
            combinationSequence F r := fun r hr => by
        rw [hlin, hseq, lengthPart_of_ne hr c g, linCombAt_one_one_zero_right]
      refine ⟨(1 : ℂ) • F + (1 : ℂ) • linComb c X, hasSmoothFamilies_add hA hF hG 1 1, ?_, ?_, ?_⟩
      · rw [hother 0 (by omega), h₀]
      · intro r h₁r hr
        rcases Nat.lt_or_ge r (n + 1) with hlt | hge
        · rw [hother r (by omega)]
          exact h₁ r h₁r (by omega)
        · obtain rfl : r = n + 1 := by omega
          rw [hlin, hseq, h₂ (n + 1) (by omega), linCombAt_one_one_zero_left, lengthPart_self c g]
          have e : (fun x => ∑ i, c i * toConfigFn (entryTensor (g i).1) x) =
              TestSpaces.TestSpaceFacts.tensorCombination c f :=
            funext fun x => by
              simp only [TestSpaces.TestSpaceFacts.tensorCombination,
                toConfigFn_tupleTensor, TestSpaces.tensorProd, Complex.ofReal_prod, g]
          rw [e]
          exact hclose
      · intro r hr
        rw [hother r (by omega)]
        exact h₂ r (by omega)
  obtain ⟨F, hF, h₀, h₁, h₂⟩ := key q₀ le_rfl
  exact ⟨F, hF, h₂, h₀, h₁⟩
end Approximation
theorem statement_holds (hF : TestSpaces.Elementary.BasicProperties)
    (hO : TestFunctionOps.OperationsStatement)
    (hT : TestSpaces.TestSpaceFacts.Statement)
    (hA : CombinationSequenceAdmissibleLinear)
    (hP : SesquilinearPosSemidefStatement) : Statement :=
  ⟨fun _ _ _ h => ⟨termEstimate hF hO hT h, formEstimate hF hO hT hP h,
    fun L hV => formOnTuples hF hO hT hA hP h L hV⟩, smoothApproximation hT hA⟩
end YangMills.Construction.AdmissibleForm
end
