import YangMills.Construction.Continuum.TermsBoundValuesOnTuplesAndApproximationForTheFormOnAdmissibleSequencesProof
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivityFromValues
open ConfigSpace (FnOrScalar ofConfigFn flipConjAt FlatSequence schwartzFlatOffDiagonal
  tensorAt toConfigFn zeroOfDegree)
open SeparatedTuples (SepTuple push pushSpan pushList formalMul basisVec supportedIn)
open TupleLists (toList)
section Members
variable {σ : TestSpaces.SepTuple → ℝ} {S : FlatSequence}
def onFlatSchwartzSet (S : FlatSequence) (n : ℕ)
    (φ : TestSpaces.flatSchwartzSet n) : ℂ :=
  S.evalAt (ofConfigFn φ.1)
theorem mem_offDiagonal_of_mem_flat {m : ℕ} {f : TestSpaces.PointTuple (m + 1) → ℂ}
    (h : f ∈ TestSpaces.flatSchwartzSet (m + 1)) : f ∈ schwartzFlatOffDiagonal (m + 1) :=
  (SchwartzAxioms.flatSchwartzSet_eq (n := m + 1)).subset h
theorem mem_flat_of_mem_offDiagonal {m : ℕ} {f : TestSpaces.PointTuple (m + 1) → ℂ}
    (h : f ∈ schwartzFlatOffDiagonal (m + 1)) : f ∈ TestSpaces.flatSchwartzSet (m + 1) :=
  (SchwartzAxioms.flatSchwartzSet_eq (n := m + 1)).superset h
theorem onFlatSchwartzSet_succ (S : FlatSequence) (m : ℕ)
    (φ : TestSpaces.flatSchwartzSet (m + 1)) (ψ : schwartzFlatOffDiagonal (m + 1))
    (h : φ.1 = ψ.1) : onFlatSchwartzSet S (m + 1) φ = S.atSucc m ψ := by
  obtain ⟨f, hf⟩ := φ
  obtain ⟨g, hg⟩ := ψ
  obtain rfl : f = g := h
  exact ConfigSpace.FlatSequence.evalAt_of_mem S (n := m + 1) hg
theorem exists_isBoundedExtensionFamily (hS : ConfigSpace.IsLinearFunctionalSeq S)
    (hC : ConfigSpace.IsContinuousSeq S) (hV : AgreesOnTensors σ S) :
    ∃ (k : ℕ → ℕ) (c : ℕ → ℝ),
      TestSpaces.IsBoundedExtensionFamily σ (onFlatSchwartzSet S) k c := by
  have hcont : ∀ m, SchwartzAxioms.IsContinuousOnFlat (onFlatSchwartzSet S (m + 1)) := by
    intro m
    refine (SchwartzAxioms.isContinuousOnFlat_iff _).2 ?_
    convert hC m using 1
    funext φ
    exact onFlatSchwartzSet_succ S m ⟨φ.1, mem_flat_of_mem_offDiagonal φ.2⟩ φ rfl
  have hex : ∀ n : ℕ, ∃ (k : ℕ) (c : ℝ), 1 ≤ n → 0 < k ∧ 0 ≤ c ∧
      ∀ φ : TestSpaces.flatSchwartzSet n,
        ENNReal.ofReal ‖onFlatSchwartzSet S n φ‖ ≤
          ENNReal.ofReal c * TestSpaces.weightedSeminorm k φ.1 := by
    intro n
    cases n with
    | zero => exact ⟨0, 0, fun hn => absurd hn (by norm_num)⟩
    | succ m =>
      obtain ⟨-, k, c, h₁, h₂, h₃⟩ := hcont m
      exact ⟨k, c, fun _ => ⟨h₁, h₂, h₃⟩⟩
  choose k c h using hex
  refine ⟨k, c, fun φ => ?_, fun n hn => ?_⟩
  · exact (ConfigSpace.FlatSequence.evalAt_of_mem S (n := 0)
      (Set.mem_univ _)).trans (hS.1 _)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨(hcont m).1, (h _ hn).1, (h _ hn).2.1, (h _ hn).2.2, fun X hX hm => ?_⟩
    rw [onFlatSchwartzSet_succ S m _ ⟨_, mem_offDiagonal_of_mem_flat hm⟩ rfl]
    exact hV m X hX _
theorem evalAt_zero_fn (hS : ConfigSpace.IsLinearFunctionalSeq S) {n : ℕ} (hn : 1 ≤ n)
    {f : TestSpaces.PointTuple n → ℂ} (hf : f = fun _ => 0) : S.evalAt (ofConfigFn f) = 0 := by
  cases n with
  | zero => omega
  | succ m =>
    subst hf
    by_cases h : (fun _ => 0 : TestSpaces.PointTuple (m + 1) → ℂ) ∈
        schwartzFlatOffDiagonal (m + 1)
    · have e := ConfigSpace.FlatSequence.evalAt_of_mem S (n := m + 1) h
      have l := hS.2 m 0 0 ⟨_, h⟩ ⟨_, h⟩ ⟨_, h⟩ (by funext x; simp)
      simp only [zero_mul, add_zero] at l
      exact e.trans l
    · exact dif_neg h
end Members
section Form
theorem pushList_timeReflection {q : ℕ} (X : Fin q → (Fin 4 → ℝ) → ℝ) :
    pushList TimeAxis.timeReflection (List.ofFn X) = List.ofFn (Motions.reflectTuple X) := by apply _root_.YangMills.Construction.AdmissibleForm.pushList_timeReflection <;> assumption
theorem toList_val_of_concat {q q' : ℕ} (Z : TestSpaces.SepTupleOfCard (q + q'))
    (A : Fin q → (Fin 4 → ℝ) → ℝ) (B : Fin q' → (Fin 4 → ℝ) → ℝ)
    (hZ : Z.1 = Motions.concatTuple A B) :
    (toList ⟨q + q', Z⟩).1 = List.ofFn A ++ List.ofFn B := by apply _root_.YangMills.Construction.AdmissibleForm.toList_val_eq_append <;> assumption
theorem sepTupleReflectionPositive_of_isFormPositive {σ : TestSpaces.SepTuple → ℝ}
    (h : IsFormPositive σ) : TestSpaces.SepTupleReflectionPositive σ := by
  intro I _ c X Z _ hZ
  classical
  let Y : ∀ ι, TestSpaces.SepTupleOfCard (X ι).1 := fun ι =>
    ⟨(X ι).2.1, fun i => ⟨((X ι).2.2.1 i).1, ((X ι).2.2.1 i).2.1, Set.subset_univ _⟩, (X ι).2.2.2⟩
  let L : I → SepTuple := fun ι => toList ⟨_, Y ι⟩
  have hL : ∀ ι, L ι ∈ supportedIn TimeAxis.upperHalfSpace := by
    intro ι f hf
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    exact ((X ι).2.2.1 i).2.2
  let F : ReflectionPositivity.TupleForm.PositiveSpan :=
    ⟨∑ ι, c ι • basisVec (L ι), Submodule.sum_mem _ fun ι _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨L ι, hL ι⟩, rfl⟩)⟩
  have hlist : ∀ ι ι', (toList ⟨_, Z ι ι'⟩).1 =
      List.ofFn (Motions.reflectTuple (X ι).2.1) ++ (L ι').1 :=
    fun ι ι' => toList_val_of_concat _ _ _ (hZ ι ι')
  have hsep : ∀ ι, SeparatedTuples.IsDisjointlySupported
      (pushList TimeAxis.timeReflection (L ι).1) := by
    intro ι
    rw [show (L ι).1 = List.ofFn (X ι).2.1 from rfl, pushList_timeReflection]
    have h₂ := (toList ⟨_, Z ι ι⟩).2
    rw [hlist] at h₂
    exact ⟨fun f hf => h₂.1 f (List.mem_append_left _ hf), (List.pairwise_append.1 h₂.2).1⟩
  have hpush : ∀ ι, (push TimeAxis.timeReflection (L ι)).1 =
      List.ofFn (Motions.reflectTuple (X ι).2.1) := by
    intro ι
    rw [push, dif_pos (hsep ι)]
    exact pushList_timeReflection _
  have hdef : ∀ ι ι', SeparatedTuples.SepTuple.Composable
      (push TimeAxis.timeReflection (L ι)) (L ι') := by
    intro ι ι' f hf g hg
    rw [hpush] at hf
    have h₂ := (toList ⟨_, Z ι ι'⟩).2
    rw [hlist] at h₂
    exact (List.pairwise_append.1 h₂.2).2.2 f hf g hg
  have hjuxt : ∀ ι ι', TupleLists.ofList
      (SeparatedTuples.SepTuple.juxt (push TimeAxis.timeReflection (L ι)) (L ι')) =
        ⟨_, Z ι ι'⟩ := by
    intro ι ι'
    have e : SeparatedTuples.SepTuple.juxt (push TimeAxis.timeReflection (L ι)) (L ι') =
        toList ⟨_, Z ι ι'⟩ :=
      Subtype.ext (by rw [SeparatedTuples.SepTuple.juxt_val (hdef ι ι'), hpush, hlist])
    rw [e, TupleLists.ofList_toList]
  have hF : WightmanReconstruction.linearExtension σ
      (formalMul (ReflectionPositivity.TupleForm.reflectConj F) F.1) =
      ∑ ι, ∑ ι', conj (c ι) * c ι' * (σ ⟨_, Z ι ι'⟩ : ℂ) := by
    have hr : ReflectionPositivity.TupleForm.reflectConj F =
        ∑ ι, conj (c ι) • basisVec (push TimeAxis.timeReflection (L ι)) := by
      change pushSpan TimeAxis.timeReflection
        (SeparatedTuples.conjugation (∑ ι, c ι • basisVec (L ι))) = _
      rw [SeparatedTuples.conjugation_sum, map_sum]
      refine Finset.sum_congr rfl fun ι _ => ?_
      rw [map_smul, pushSpan, SeparatedTuples.linearExtend_basisVec]
    rw [hr]
    change WightmanReconstruction.linearExtension σ (formalMul _
      (∑ ι, c ι • basisVec (L ι))) = _
    rw [SeparatedTuples.formalMul_sum, map_sum]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun ι' _ => ?_
    rw [map_smul, WightmanReconstruction.linearExtension, SeparatedTuples.linearExtend_basisVec,
      hjuxt, smul_eq_mul]
  have h₁ := h F
  rwa [hF] at h₁
end Form
section Terms
theorem tensorAt_flipConjAt_eq {q q' : ℕ} (a : FnOrScalar q) (b : FnOrScalar q') :
    tensorAt (flipConjAt a) b =
      ofConfigFn (TestSpaces.tensorFun (Motions.reflectConj (toConfigFn a)) (toConfigFn b)) := by apply _root_.YangMills.Construction.AdmissibleForm.tensorAt_flipConjAt_eq <;> assumption
theorem toConfigFn_zeroOfDegree (q : ℕ) :
    toConfigFn (zeroOfDegree q) = fun _ => 0 := by
  cases q <;> rfl
end Terms
theorem statement_holds (hP : TestSpaces.SchwingerPropertiesTransfer) : Statement := by
  intro σ S hσ hS hC hV hF
  obtain ⟨k, c, hb⟩ := exists_isBoundedExtensionFamily hS hC hV
  have hrp := (hP σ (onFlatSchwartzSet S) k c hσ hb).2.2
    (sepTupleReflectionPositive_of_isFormPositive hF)
  intro Φ hΦ
  obtain ⟨q₀, hq₀, hbig⟩ : ∃ q₀, 1 ≤ q₀ ∧ ∀ q, q₀ < q → (Φ q).1 = zeroOfDegree q := by
    obtain ⟨B, hB⟩ := hΦ.bddAbove
    refine ⟨B + 1, by omega, fun q hq => ?_⟩
    by_contra hne
    have := hB hne
    omega
  let φ : (q : ℕ) → TestSpaces.PointTuple q → ℂ := fun q => toConfigFn (Φ q).1
  have hfam : TestSpaces.IsPositiveTimeFlatFamily q₀ φ := by
    intro q hq _
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    exact (SchwartzAxioms.positiveTimeSchwartz_eq (n := m + 1)).superset (Φ (m + 1)).2
  obtain ⟨h, him, hre⟩ := hrp q₀ φ hq₀ hfam
  have e : S.reflectionPairing (fun q => (Φ q).1) (fun q => (Φ q).1) =
      ∑ q : Fin (q₀ + 1), ∑ q' : Fin (q₀ + 1),
        onFlatSchwartzSet S ((q : ℕ) + q') ⟨_, h q q'⟩ := by
    let G : ℕ → ℕ → ℂ := fun q q' => S.evalAt (ofConfigFn
      (TestSpaces.tensorFun (Motions.reflectConj (φ q)) (φ q')))
    have hG : ∀ p : ℕ × ℕ, S.evalAt (tensorAt (flipConjAt (Φ p.1).1)
        (Φ p.2).1) = G p.1 p.2 := fun p => by rw [tensorAt_flipConjAt_eq]
    have hz : ∀ q q', q₀ < q ∨ q₀ < q' → G q q' = 0 := by
      intro q q' hq
      refine evalAt_zero_fn hS (by omega) ?_
      funext z
      rcases hq with hq | hq
      · have e₁ : φ q = fun _ => 0 := by
          change toConfigFn (Φ q).1 = _
          rw [hbig q hq, toConfigFn_zeroOfDegree]
        simp [TestSpaces.tensorFun, Motions.reflectConj, e₁]
      · have e₁ : φ q' = fun _ => 0 := by
          change toConfigFn (Φ q').1 = _
          rw [hbig q' hq, toConfigFn_zeroOfDegree]
        simp [TestSpaces.tensorFun, e₁]
    have hs : (Function.support fun p : ℕ × ℕ => G p.1 p.2) ⊆
        ↑(Finset.range (q₀ + 1) ×ˢ Finset.range (q₀ + 1)) := by
      rintro ⟨q, q'⟩ hp
      by_contra hn
      refine hp (hz q q' ?_)
      simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio, not_and_or] at hn
      omega
    calc S.reflectionPairing (fun q => (Φ q).1) (fun q => (Φ q).1)
        = ∑ᶠ p : ℕ × ℕ, G p.1 p.2 := finsum_congr hG
      _ = ∑ p ∈ Finset.range (q₀ + 1) ×ˢ Finset.range (q₀ + 1), G p.1 p.2 :=
          finsum_eq_sum_of_support_subset _ hs
      _ = ∑ q ∈ Finset.range (q₀ + 1), ∑ q' ∈ Finset.range (q₀ + 1), G q q' :=
          Finset.sum_product _ _ _
      _ = ∑ q : Fin (q₀ + 1), ∑ q' : Fin (q₀ + 1), G q q' := by
          rw [Finset.sum_range]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_range]
      _ = _ := rfl
  rw [e]
  exact ⟨him, hre⟩
end YangMills.Construction.ReflectionPositivityFromValues
end
