import YangMills.Construction.Torus.CoefficientsOfATestFunctionOnTheBox
import YangMills.Construction.Torus.CutOffTimesPartialSumsConvergeInGradientNorm
import YangMills.Construction.Torus.FormOfACutOffAtTensors
import YangMills.Construction.Torus.FormOfACutOffIsABoundedLinearForm
import YangMills.Construction.Torus.GradientNormLipschitzConstantAndSharpNorm
import YangMills.Construction.Torus.GradientNormOfACutOffTimesAMode
import YangMills.Construction.Torus.RestrictionsSumsProductsAndTensorsOfTestFunctions
import Mathlib
set_option autoImplicit false
open Filter
open scoped ENNReal Topology
open YangMills.Construction.Torus.FourierBox
noncomputable section
namespace YangMills.Construction.AmbientPoints.CutoffSeriesAtTensorsProof
theorem tendsto_multilinearMap_of_prod_bound {ι : Type} [Fintype ι] [DecidableEq ι] {W : ι → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (M : MultilinearMap ℂ W ℂ)
    (N : ∀ i, W i → ℝ≥0∞) (c : ℝ)
    (hb : ∀ f, ENNReal.ofReal ‖M f‖ ≤ ENNReal.ofReal c * ∏ i, N i (f i))
    (f : ∀ i, W i) (hf : ∀ i, N i (f i) ≠ ⊤) (ft : ℕ+ → ∀ i, W i)
    (ht : ∀ i, Tendsto (fun t => N i (ft t i - f i)) atTop (𝓝 0)) :
    Tendsto (fun t => M (ft t)) atTop (𝓝 (M f)) := by
  have hsplit : ∀ t, M (ft t) = ∑ S : Finset ι, M (S.piecewise f (ft t - f)) := fun t => by
    rw [← M.map_add_univ, add_sub_cancel]
  have hterm : ∀ S : Finset ι, Tendsto (fun t => M (S.piecewise f (ft t - f))) atTop
      (𝓝 (if S = Finset.univ then M f else 0)) := by
    intro S
    by_cases hS : S = Finset.univ
    · subst hS
      simp only [Finset.piecewise_univ, if_true]
      exact tendsto_const_nhds
    · rw [if_neg hS]
      obtain ⟨l, hl⟩ : ∃ l, l ∉ S := by
        by_contra hne
        simp only [not_exists, not_not] at hne
        exact hS (Finset.eq_univ_iff_forall.2 hne)
      have hlim : ∀ i, Tendsto (fun t => N i (S.piecewise f (ft t - f) i)) atTop
          (𝓝 (if i ∈ S then N i (f i) else 0)) := by
        intro i
        by_cases hi : i ∈ S
        · simp only [Finset.piecewise_eq_of_mem _ _ _ hi, if_pos hi]
          exact tendsto_const_nhds
        · simp only [Finset.piecewise_eq_of_notMem _ _ _ hi, if_neg hi, Pi.sub_apply]
          exact ht i
      have hfin : ∀ i, (if i ∈ S then N i (f i) else 0) ≠ ⊤ := by
        intro i
        by_cases hi : i ∈ S
        · simpa only [if_pos hi] using hf i
        · simp only [if_neg hi]
          exact ENNReal.zero_ne_top
      have h1 : Tendsto (fun t => ENNReal.ofReal c * ∏ i, N i (S.piecewise f (ft t - f) i)) atTop
          (𝓝 (ENNReal.ofReal c * ∏ i, (if i ∈ S then N i (f i) else 0))) :=
        ENNReal.Tendsto.const_mul
          (ENNReal.tendsto_finsetProd_of_ne_top _ (fun i _ => hlim i) (fun i _ => hfin i))
          (Or.inr ENNReal.ofReal_ne_top)
      have h0 : ∏ i, (if i ∈ S then N i (f i) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ l) (if_neg hl)
      rw [h0, mul_zero] at h1
      have h2 : Tendsto (fun t => ENNReal.ofReal ‖M (S.piecewise f (ft t - f))‖) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le)
          (fun t => (hb _).trans (le_of_eq (by rfl)))
      have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h2
      refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
      simpa [Function.comp_def, ENNReal.toReal_ofReal] using h3
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Finset ι)) fun S _ => hterm S
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, ← hsplit] at hsum
  exact hsum
variable {s : Conventions.StandingParameters} {n : ℕ}
theorem isOpen_singletonTuples {A : Set (Pt s .euclidean)} (hA : IsOpen A) :
    IsOpen (singletonTuples A) :=
  hA.preimage (continuous_apply (0 : Fin 1))
theorem closedSupport_ofSinglePoint (u : Pt s .euclidean → ℂ) :
    closedSupport (ofSinglePoint u) = (fun y : Tuple s .euclidean 1 => y 0) ⁻¹' tsupport u := by
  have h := (Homeomorph.funUnique (Fin 1) (Pt s .euclidean)).preimage_closure
    (Function.support u)
  have h2 : {y : Tuple s .euclidean 1 | ofSinglePoint u y ≠ 0} =
      (Homeomorph.funUnique (Fin 1) (Pt s .euclidean)) ⁻¹' Function.support u := by
    ext y
    simp [ofSinglePoint]
  rw [closedSupport, h2, ← h]
  rfl
theorem mem_complexComponentSpace_of_testFn {O : Fin n → Set (Pt s .euclidean)} {i : Fin n}
    {u : Pt s .euclidean → ℂ}
    (hu : ofSinglePoint u ∈ testFns (singletonTuples (O i))) :
    u ∈ complexEntrySpace O i := by
  have hsupp := closedSupport_ofSinglePoint u
  have himage : tsupport u = (fun y : Tuple s .euclidean 1 => y 0) '' closedSupport (ofSinglePoint u) := by
    rw [hsupp, Set.image_preimage_eq]
    exact fun x => ⟨fun _ => x, rfl⟩
  refine ⟨⟨hu.1.1, fun m _ => hu.1.2 m le_top⟩, ?_, ?_⟩
  · rw [himage]
    exact hu.2.1.image (continuous_apply (0 : Fin 1))
  · rw [himage]
    rintro _ ⟨y, hy, rfl⟩
    exact hu.2.2 hy
theorem c1GradNorm_ne_top (hG : GradientC1Bounds.Statement)
    {Ω : Set (Tuple s .euclidean 1)} (hΩ : PartsDerivNormFacts Ω)
    {u : Pt s .euclidean → ℂ} (hu : ofSinglePoint u ∈ testFns Ω) :
    c1GradNorm u ≠ ⊤ := by
  have hnorm := (hΩ _ hu).2.2.2
  have hclass : IsCnAtPoint 1 u := ⟨hu.1.1, fun m _ => hu.1.2 m le_top⟩
  have hgrad : gradSupNorm u ≤ 2 * cnNorm 1 (ofSinglePoint u) := by
    refine iSup_le fun x => ?_
    have h1 := ((hG s .euclidean).1 u u hclass hclass).1 x
    obtain ⟨μ, hμ⟩ := exists_eq_ciSup_of_finite (f := fun μ => ‖partialAt μ u x‖)
    have h2 : ENNReal.ofReal ‖partialAt μ u x‖ ≤ cnNorm 1 (ofSinglePoint u) :=
      le_iSup_of_le (basisMultiIndex μ) (le_iSup_of_le (le_of_eq (basisMultiIndex_order μ))
        (le_iSup_of_le (fun _ => x) le_rfl))
    calc ENNReal.ofReal (gradNorm u x)
        ≤ ENNReal.ofReal (2 * ‖partialAt μ u x‖) :=
          ENNReal.ofReal_le_ofReal (by rw [show ‖partialAt μ u x‖ = _ from hμ]; exact h1)
      _ = 2 * ENNReal.ofReal ‖partialAt μ u x‖ := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          simp
      _ ≤ 2 * cnNorm 1 (ofSinglePoint u) := by gcongr
  refine ne_of_lt (max_lt ?_ (lt_of_le_of_lt hgrad ?_))
  · rw [tupleSupNorm_eq_cnNorm_zero]
    exact hnorm 0
  · exact ENNReal.mul_lt_top (by simp) (hnorm 1)
def testFnSubmodule (A : Set (Pt s .euclidean)) (hc : LinearCombFacts (singletonTuples A))
    (h0 : (0 : Tuple s .euclidean 1 → ℂ) ∈ testFns (singletonTuples A)) :
    Submodule ℂ (Pt s .euclidean → ℂ) where
  carrier := {u | ofSinglePoint u ∈ testFns (singletonTuples A)}
  add_mem' := by
    intro a b ha hb
    have := (hc _ ha _ hb 1 1).1
    rw [one_smul, one_smul] at this
    exact this
  zero_mem' := h0
  smul_mem' := by
    intro c a ha
    have := (hc _ ha _ ha c 0).1
    rw [zero_smul, add_zero] at this
    exact this
theorem coe_funUpdate {W : Fin n → Submodule ℂ (Pt s .euclidean → ℂ)} (f : ∀ i, W i) (i : Fin n)
    (w : W i) :
    (fun j => ((Function.update f i w j : W j) : Pt s .euclidean → ℂ)) =
      Function.update (fun j => ((f j : W j) : Pt s .euclidean → ℂ)) i w := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_of_ne hj]
def toMultilinearMap {O : Fin n → Set (Pt s .euclidean)}
    (W : Fin n → Submodule ℂ (Pt s .euclidean → ℂ))
    (hW : ∀ i, ∀ u ∈ W i, u ∈ complexEntrySpace O i)
    (B : (Fin n → Pt s .euclidean → ℂ) → ℂ) (hl : IsComplexMultilinearOnComponents O B) :
    MultilinearMap ℂ (fun i => W i) ℂ where
  toFun f := B fun i => (f i : Pt s .euclidean → ℂ)
  map_update_add' := by
    intro inst f i u v
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    simp only [coe_funUpdate]
    have := hl (fun j => (f j : Pt s .euclidean → ℂ)) (fun j => hW j _ (f j).2) i u v
      (hW i _ u.2) (hW i _ v.2) 1 1
    simpa using this
  map_update_smul' := by
    intro inst f i c u
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    simp only [coe_funUpdate]
    have := hl (fun j => (f j : Pt s .euclidean → ℂ)) (fun j => hW j _ (f j).2) i u u
      (hW i _ u.2) (hW i _ u.2) c 0
    simpa using this
theorem sum_piFinset_modesWithin {β : Type} [AddCommMonoid β] (t : ℕ) (F : (Fin n → Fin 4 → ℤ) → β) :
    ∑ r ∈ Fintype.piFinset fun _ : Fin n => (modesWithin t : Finset (Fin 4 → ℤ)), F r =
      ∑ k ∈ (modesWithin t : Finset (Fin (4 * n) → ℤ)), F fun i => blockOf k i := by
  symm
  refine Finset.sum_bij (fun k _ i => blockOf k i) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro k hk
    simp only [modesWithin, Fintype.mem_piFinset] at hk ⊢
    exact fun i μ => hk _
  · intro k _ k' _ heq
    funext j
    have hj := j.2
    have hi : (j : ℕ) / 4 < n := by omega
    have hμ : (j : ℕ) % 4 < 4 := by omega
    have h := congrFun (congrFun heq ⟨(j : ℕ) / 4, hi⟩) ⟨(j : ℕ) % 4, hμ⟩
    simp only [blockOf] at h
    have e : (⟨4 * ((j : ℕ) / 4) + (j : ℕ) % 4, by omega⟩ : Fin (4 * n)) = j :=
      Fin.ext (by simp only; omega)
    rwa [e] at h
  · intro r hr
    simp only [modesWithin, Fintype.mem_piFinset] at hr
    have hi : ∀ j : Fin (4 * n), (j : ℕ) / 4 < n := fun j => by have := j.2; omega
    have hμ : ∀ j : Fin (4 * n), (j : ℕ) % 4 < 4 := fun j => by omega
    refine ⟨fun j => r ⟨(j : ℕ) / 4, hi j⟩ ⟨(j : ℕ) % 4, hμ j⟩, ?_, ?_⟩
    · simp only [modesWithin, Fintype.mem_piFinset]
      exact fun j => hr _ _
    · funext i μ
      have hμ4 := μ.2
      have hi4 := i.2
      have hk : 4 * (i : ℕ) + (μ : ℕ) < 4 * n := by omega
      have e1 : (⟨(4 * (i : ℕ) + (μ : ℕ)) / 4, hi ⟨_, hk⟩⟩ : Fin n) = i :=
        Fin.ext (show (4 * (i : ℕ) + (μ : ℕ)) / 4 = i by omega)
      have e2 : (⟨(4 * (i : ℕ) + (μ : ℕ)) % 4, hμ ⟨_, hk⟩⟩ : Fin 4) = μ :=
        Fin.ext (show (4 * (i : ℕ) + (μ : ℕ)) % 4 = μ by omega)
      change r ⟨(4 * (i : ℕ) + (μ : ℕ)) / 4, hi ⟨_, hk⟩⟩ ⟨(4 * (i : ℕ) + (μ : ℕ)) % 4, hμ ⟨_, hk⟩⟩ =
        r i μ
      rw [e1, e2]
theorem tendsto_modesWithin {D : ℕ} :
    Tendsto (fun t : ℕ+ => (modesWithin (t : ℕ) : Finset (Fin D → ℤ))) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone ?_ ?_
  · intro a b hab k hk
    rw [mem_modesWithin] at hk ⊢
    exact hk.trans (by exact_mod_cast hab)
  · intro k
    refine ⟨⟨supNormInt k + 1, Nat.succ_pos _⟩, ?_⟩
    rw [mem_modesWithin]
    simp
theorem singletonTuples_subset_fundamentalBoxPow {ρ : ℝ} (hρ : 0 < ρ) {A : Set (Pt s .euclidean)}
    (hA : A ⊆ {u : Fin 4 → ℝ | TorusMetric.euclidNormVec u ≤ ρ}) :
    singletonTuples A ⊆ fundamentalBoxPow s 1 (4 * ρ) := by
  intro y hy j μ
  obtain rfl : j = 0 := Subsingleton.elim _ _
  have h1 : TorusMetric.euclidNormVec (y 0 : Fin 4 → ℝ) ≤ ρ := hA hy
  have h2 : |coord s μ (y 0)| ≤ TorusMetric.euclidNormVec (y 0 : Fin 4 → ℝ) :=
    Real.abs_le_sqrt (Finset.single_le_sum
      (f := fun ν => (coord s ν (y 0)) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ μ))
  have h3 := abs_le.1 (h2.trans h1)
  constructor <;> linarith [h3.1, h3.2]
theorem cutoffSeriesAtTensors_holds (hB : CutoffSeriesBoundedLinear)
    (hT : CutoffTimesFourierSumsConverge)
    (hC : FourierCoeffBounds)
    (hM : CutoffTimesModeGradNorm)
    (hG : GradientC1Bounds.Statement)
    (hR : TestFnOperations) : CutoffSeriesAtTensors := by
  intro s n ρ C O B χ hO hC0 hlin hbd hχ h hh
  have hn := hO.1
  have hρ := hO.2.1
  have hOi := hO.2.2
  have hP : 0 < 4 * ρ := by linarith
  have hRn := (hR s .euclidean 1 le_rfl).2.1
  have hOp : ∀ i, IsOpen (singletonTuples (O i)) := fun i => isOpen_singletonTuples (hOi i).1
  have hComb := fun i => (hRn _ (hOp i)).2.1
  have hParts := fun i => (hRn _ (hOp i)).2.2.1
  have hProd := fun i => (hRn _ (hOp i)).2.2.2
  have hzero : ∀ i, (0 : Tuple s .euclidean 1 → ℂ) ∈ testFns (singletonTuples (O i)) := by
    intro i
    have := (hComb i _ (hχ i) _ (hχ i) 0 0).1
    rwa [zero_smul, add_zero] at this
  let W : Fin n → Submodule ℂ (Pt s .euclidean → ℂ) :=
    fun i => testFnSubmodule (O i) (hComb i) (hzero i)
  have hW : ∀ i, ∀ u ∈ W i, u ∈ complexEntrySpace O i :=
    fun i u hu => mem_complexComponentSpace_of_testFn hu
  let M := toMultilinearMap W hW B hlin
  let e : ∀ i, (Fin 4 → ℤ) → W i := fun i κ =>
    ⟨fun x => (χ i x : ℂ) * fourierMode (4 * ρ) κ x, (hM s ρ hρ (O i) (χ i) κ (hOi i).1 (hχ i)).1⟩
  let a : Fin n → (Fin 4 → ℤ) → ℂ := fun i κ =>
    fourierCoeff (n := 1) (4 * ρ) (ofSinglePoint (h i)) κ
  let g : ∀ i, W i := fun i =>
    ⟨fun x => (χ i x : ℂ) * h i x,
      (hProd i (asFunctionOnOnePoint (χ i)) (ofSinglePoint (h i)) (hχ i).1 (hh i).1).2.2.1
        (Or.inl (hχ i))⟩
  let gt : ℕ+ → ∀ i, W i := fun t i => ∑ κ ∈ (modesWithin (t : ℕ) : Finset (Fin 4 → ℤ)), a i κ • e i κ
  have hgt : ∀ t i x, ((gt t i : W i) : Pt s .euclidean → ℂ) x =
      (χ i x : ℂ) * fourierPartialSum (n := 1) (4 * ρ) (ofSinglePoint (h i)) t x := by
    intro t i x
    simp only [gt, fourierPartialSum, Submodule.coe_sum, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun κ _ => ?_
    change a i κ * ((χ i x : ℂ) * fourierMode (4 * ρ) κ x) = _
    exact mul_left_comm _ _ _
  have hlim2 : Tendsto (fun t => M (gt t)) atTop (𝓝 (M g)) := by
    refine tendsto_multilinearMap_of_prod_bound M (fun i w => c1GradNorm (w : Pt s .euclidean → ℂ)) C
      (fun w => hbd _ fun i => hW i _ (w i).2) g
      (fun i => c1GradNorm_ne_top hG (hParts i) (g i).2) gt fun i => ?_
    have hχQ : asFunctionOnOnePoint (χ i) ∈ testFns (fundamentalBoxPow s 1 (4 * ρ)) :=
      testFns_mono (singletonTuples_subset_fundamentalBoxPow hρ (hOi i).2) (hχ i)
    refine (hT s (4 * ρ) hP (χ i) (h i) hχQ (hh i)).congr fun t => ?_
    congr 1
    funext x
    exact congrArg (· - (χ i x : ℂ) * h i x) (hgt t i x).symm
  have hexp : ∀ t : ℕ+, M (gt t) = ∑ k ∈ (modesWithin (t : ℕ) : Finset (Fin (4 * n) → ℤ)),
      fourierCoeff (4 * ρ) (tensorProd h) k * B (cutoffModeTuple (4 * ρ) χ k) := by
    intro t
    have h1 := M.map_sum_finset (fun i κ => a i κ • e i κ)
      (fun _ => (modesWithin (t : ℕ) : Finset (Fin 4 → ℤ)))
    have h2 : M (gt t) = ∑ r ∈ Fintype.piFinset
        fun _ : Fin n => (modesWithin (t : ℕ) : Finset (Fin 4 → ℤ)),
        (∏ i, a i (r i)) * M fun i => e i (r i) := by
      refine h1.trans (Finset.sum_congr rfl fun r _ => ?_)
      rw [M.map_smul_univ]
      rfl
    rw [h2, sum_piFinset_modesWithin]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [((hC s n (4 * ρ) hn hP).2.2.2 h hh).2 k]
    rfl
  have hsum := ((hB s n ρ C O B χ hO hC0 hbd hχ).1 (tensorProd h)
    ((hC s n (4 * ρ) hn hP).2.2.2 h hh).1).1
  have hlim1 : Tendsto (fun t : ℕ+ => ∑ k ∈ (modesWithin (t : ℕ) : Finset (Fin (4 * n) → ℤ)),
      fourierCoeff (4 * ρ) (tensorProd h) k * B (cutoffModeTuple (4 * ρ) χ k)) atTop
      (𝓝 (cutoffSeries (4 * ρ) B χ (tensorProd h))) :=
    hsum.hasSum.comp tendsto_modesWithin
  exact tendsto_nhds_unique hlim1 (hlim2.congr hexp)
end YangMills.Construction.AmbientPoints.CutoffSeriesAtTensorsProof
