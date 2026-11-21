import YangMills.Construction.Continuum.PlateauOfAFunctionOnTuples
import YangMills.Construction.EuclideanFunctionals.BracketOfTheParametrixProof
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.Continuum.IsometriesAndModuliOnFourSpaceProof
import YangMills.Construction.Continuum.MomentFunctionalsOnSymbols
import YangMills.Construction.Continuum.OneClassOfTuplesAndOneNotionOfMultilinearityProof
import YangMills.Construction.Geometry.Periodization
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefinedProof
import YangMills.Construction.TorusOrFourSpace.TwoFormsOfTheFamilyOnFourSpace
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped NNReal ENNReal ComplexOrder ComplexConjugate
noncomputable section
namespace YangMills.Construction.TimeAxisSymbols
open TorusTransport TorusTransport.TupleVectors TorusTransport.TestFunctionOrders
open TestFunctions (IsC1R4 setDistR4)
open FormsOperators (IsSesquilinear IsHermitianForm IsPosSemidefForm)
open PositiveFormReconstruction (rotateSpatial)
namespace MomentFunctionals
variable {D : TransportData}
theorem tsupport_realToComplex (f : RealFun (Fin 4 → ℝ)) :
    tsupport f.toComplex = tsupport f := by apply _root_.YangMills.Construction.TorusTransport.MotionFacts.tsupport_toComplex_eq <;> assumption
theorem ennSharpNorm_realToComplex (f : RealFun (Fin 4 → ℝ)) :
    Domain.euclidean.ennSharpNorm D f.toComplex = Domain.euclidean.ennSharpNorm D f := by
  simp only [Domain.ennSharpNorm, Domain.lipConst, ennSupNorm_toComplex, ennLipConst_toComplex]
theorem lipschitzOn_of_mem_c1SupportedIn {A : Set (Fin 4 → ℝ)} {f : RealFun (Fin 4 → ℝ)}
    (hf : f ∈ c1SupportedIn A) : Domain.euclidean.LipschitzOn D f :=
  lipschitzOn_of_isC1On D hf.1 hf.2.1
theorem mem_realC1Compact_of_mem {A : Set (Fin 4 → ℝ)} {f : RealFun (Fin 4 → ℝ)}
    (hf : f ∈ c1SupportedIn A) : f ∈ realC1Compact := by
  refine ⟨?_, ?_⟩
  · have h : ContDiff ℝ 1 f := hf.1
    exact Complex.ofRealCLM.contDiff.comp h
  · rw [tsupport_realToComplex]
    exact hf.2.1
theorem ennSharpNorm_lt_top {A : Set (Fin 4 → ℝ)} {f : RealFun (Fin 4 → ℝ)}
    (hf : f ∈ c1SupportedIn A) : Domain.euclidean.ennSharpNorm D f < ∞ := by
  have hc : Continuous f := (show ContDiff ℝ 1 f from hf.1).continuous
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hf.2.1
  have h₁ : ennSupNorm f < ∞ :=
    lt_of_le_of_lt (iSup_le fun u => ENNReal.ofReal_le_ofReal (hC u)) ENNReal.ofReal_lt_top
  have h₂ : Domain.euclidean.lipConst D f < ∞ := lipschitzOn_of_mem_c1SupportedIn hf
  exact max_lt h₁ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h₂)
theorem ennSharpNorm_comp_motion (hI : MotionFacts.MotionInvariance D)
    {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s) {A : Set (Fin 4 → ℝ)}
    {f : RealFun (Fin 4 → ℝ)} (hf : f ∈ c1SupportedIn A) :
    Domain.euclidean.ennSharpNorm D (f ∘ s) = Domain.euclidean.ennSharpNorm D f := by
  have hl : Domain.euclidean.LipschitzOn D f.toComplex := by
    have h₂ : Domain.euclidean.lipConst D f < ∞ := lipschitzOn_of_mem_c1SupportedIn hf
    show ennLipConst _ _ < ∞
    rw [ennLipConst_toComplex]
    exact h₂
  have hc : IsCompact (Domain.euclidean.fnSupport D f.toComplex) := by
    show IsCompact (tsupport f.toComplex)
    rw [tsupport_realToComplex]
    exact hf.2.1
  have h := ((hI s hs).1 f.toComplex hl hc).2.2.2.1
  rw [ennSharpNorm_realToComplex] at h
  rw [← h, ← ennSharpNorm_realToComplex (D := D) (f ∘ s)]
  rfl
theorem fn_mem_c1SupportedIn (X : SpaceTimeSymbol D) (i : Fin X.1.1) :
    X.1.2 i ∈ c1SupportedIn (entrySupp D (X.1.2 i)) := by
  obtain ⟨-, hk, -, hc, -⟩ := (mem_sepTuples_iff D _ X.1).mp X.2
  exact ⟨hc i, hk i, subset_rfl⟩
theorem mem_symbolsOfCard_of_mem {k : ℕ+} {f : Domain.euclidean.FnFamily D k ℝ}
    (hf : (⟨k, f⟩ : FnTuple) ∈ spaceTimeSymbols D) : f ∈ symbolsOfCard D k := by
  obtain ⟨hl, hk, hd, hc, -⟩ := (mem_sepTuples_iff D _ _).mp hf
  exact ⟨⟨hl, hk, fun i j hij => hd hij⟩, hc⟩
theorem mem_spaceTimeSymbols_of_mem_symbolsOfCard {k : ℕ+} {f : Domain.euclidean.FnFamily D k ℝ}
    (hf : f ∈ symbolsOfCard D k) : (⟨k, f⟩ : FnTuple) ∈ spaceTimeSymbols D :=
  (mem_spaceTimeSymbols_iff D _).mpr (Or.inr ⟨k, f, hf, rfl⟩)
section Products
variable (hS : SupportFacts.AllSupportFacts)
include hS
theorem mem_of_forall_mem_c1SupportedIn {k : ℕ+} {d R : ℝ} {hd : 0 < d} {hR : 0 < R}
    {A : Fin k → Set (Fin 4 → ℝ)} (hA : IsAdmissibleSets D d R hd hR A)
    {f : Domain.euclidean.FnFamily D k ℝ} (hf : ∀ i, f i ∈ c1SupportedIn (A i)) :
    f ∈ symbolsOfCard D k ∧ (⟨k, f⟩ : FnTuple) ∈ scaledSymbols D d R hd hR := by
  obtain ⟨hsep, hrad, hdist, -, -⟩ := (hS D).2.2.1 k d R hd hR A hA f
    fun l => ((hS D).2.2.2.2.2.2.1 (A l)).2.2 (hf l)
  have hsym : f ∈ symbolsOfCard D k := ⟨hsep, fun i => (hf i).1⟩
  exact ⟨hsym, Or.inr (Set.mem_iUnion.mpr
    ⟨k, f, ⟨mem_spaceTimeSymbols_of_mem_symbolsOfCard hsym, fun l => hrad l, hdist⟩, rfl⟩)⟩
theorem sub_mem_c1SupportedIn (D' : TransportData) {A : Set (Fin 4 → ℝ)}
    {f g : RealFun (Fin 4 → ℝ)} (hf : f ∈ c1SupportedIn A) (hg : g ∈ c1SupportedIn A) :
    f - g ∈ c1SupportedIn A := by
  obtain ⟨-, ⟨V, hV⟩, -⟩ := (hS D').2.2.2.2.2.2.1 A
  rw [← hV] at hf hg ⊢
  exact V.sub_mem hf hg
theorem lipschitzOnProducts {m : SpaceTimeSymbol D → ℝ} {bound : ℕ+ → ℝ → ℝ → ℝ≥0}
    (h₁ : IsNormedSymmMultilinear m) (h₂ : IsScaleBounded m bound) :
    LipschitzOnProducts m bound := by
  intro k d R hd hR A hA f f' hf hf'
  let Z : ℕ → Domain.euclidean.FnFamily D k ℝ := fun j l => if (l : ℕ) < j then f' l else f l
  have hZ : ∀ j l, Z j l ∈ c1SupportedIn (A l) := fun j l => by
    by_cases h : (l : ℕ) < j
    · simpa only [Z, h, if_true] using hf' l
    · simpa only [Z, h, if_false] using hf l
  have hZs : ∀ j, Z j ∈ symbolsOfCard D k := fun j =>
    (mem_of_forall_mem_c1SupportedIn hS hA (hZ j)).1
  let v : ℕ → ℝ := fun j => restrictCard m k ⟨Z j, hZs j⟩
  have e₀ : Z 0 = f := by
    funext l
    simp [Z]
  have e₁ : Z k = f' := by
    funext l
    simp [Z, l.2]
  have mf : (⟨k, f⟩ : FnTuple) ∈ spaceTimeSymbols D :=
    mem_spaceTimeSymbols_of_mem_symbolsOfCard (mem_of_forall_mem_c1SupportedIn hS hA hf).1
  have mf' : (⟨k, f'⟩ : FnTuple) ∈ spaceTimeSymbols D :=
    mem_spaceTimeSymbols_of_mem_symbolsOfCard (mem_of_forall_mem_c1SupportedIn hS hA hf').1
  refine ⟨mf, mf', ?_⟩
  have v₀ : m ⟨⟨k, f⟩, mf⟩ = v 0 := by
    show _ = m ⟨⟨k, Z 0⟩, _⟩
    simp only [e₀]
  have v₁ : m ⟨⟨k, f'⟩, mf'⟩ = v k := by
    show _ = m ⟨⟨k, Z k⟩, _⟩
    simp only [e₁]
  have step : ∀ i : Fin k, ENNReal.ofReal |v i - v (i + 1)| ≤
      (bound k d R : ℝ≥0∞) * (Domain.euclidean.ennSharpNorm D (f i - f' i) *
        ∏ l ∈ Finset.univ.erase i, max (Domain.euclidean.ennSharpNorm D (f l))
          (Domain.euclidean.ennSharpNorm D (f' l))) := by
    intro i
    have zi : Z i i = f i := by simp [Z]
    have zi' : Z (i + 1) i = f' i := by simp [Z]
    have zl : ∀ l, l ≠ i → Z i l = Z (i + 1) l := fun l hl => by
      have hl' : (l : ℕ) ≠ i := fun e => hl (Fin.ext e)
      have : (l : ℕ) < i ↔ (l : ℕ) < i + 1 := by omega
      simp only [Z, this]
    have wi : (1 : ℝ) • Z i i + (-1 : ℝ) • Z (i + 1) i = f i - f' i := by
      rw [zi, zi', one_smul, neg_one_smul, sub_eq_add_neg]
    let W : Domain.euclidean.FnFamily D k ℝ :=
      Function.update (Z i) i ((1 : ℝ) • Z i i + (-1 : ℝ) • Z (i + 1) i)
    have hWi : W i = f i - f' i := by
      simp only [W, Function.update_self, wi]
    have hWl : ∀ l, l ≠ i → W l = Z i l := fun l hl => by
      simp only [W, Function.update_of_ne hl]
    have hW : ∀ l, W l ∈ c1SupportedIn (A l) := fun l => by
      by_cases hl : l = i
      · subst hl
        rw [hWi]
        exact sub_mem_c1SupportedIn hS D (hf _) (hf' _)
      · rw [hWl l hl]
        exact hZ _ _
    obtain ⟨hWs, hWa⟩ := mem_of_forall_mem_c1SupportedIn hS hA hW
    have lin := h₁.multilinear k i ⟨Z i, hZs i⟩ ⟨Z (i + 1), hZs _⟩ zl 1 (-1) hWs
    have hv : restrictCard m k ⟨W, hWs⟩ = v i - v (i + 1) := by
      refine lin.trans ?_
      simp [v, sub_eq_add_neg]
    rw [← hv]
    refine (h₂ k d R hd hR W hWa).trans ?_
    refine mul_le_mul_right (?_ : _ ≤ _) _
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hWi]
    refine mul_le_mul_right (Finset.prod_le_prod' fun l hl => ?_) _
    have hl' : l ≠ i := (Finset.mem_erase.mp hl).1
    rw [hWl l hl']
    by_cases h : (l : ℕ) < i
    · simpa only [Z, h, if_true] using le_max_right _ _
    · simpa only [Z, h, if_false] using le_max_left _ _
  rw [v₀, v₁, Finset.mul_sum]
  have tel : v 0 - v k = ∑ i ∈ Finset.range k, (v i - v (i + 1)) :=
    (Finset.sum_range_sub' v k).symm
  rw [tel, Finset.sum_range (fun i => v i - v (i + 1))]
  calc ENNReal.ofReal |∑ i : Fin k, (v i - v (i + 1))|
      ≤ ENNReal.ofReal (∑ i : Fin k, |v i - v (i + 1)|) :=
        ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i : Fin k, ENNReal.ofReal |v i - v (i + 1)| :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _
    _ ≤ _ := Finset.sum_le_sum fun i _ => step i
end Products
theorem exists_pos_ofReal_le {ι : Type*} [Finite ι] {a : ι → ℝ≥0∞} (h : ∀ i, 0 < a i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ENNReal.ofReal ε ≤ a i := by apply _root_.YangMills.Construction.TestSpaces.UnifiedSeparatedTuples.exists_pos_ofReal_le_of_finite <;> assumption
theorem continuous_euclidNorm : Continuous (euclidNorm : (Fin 4 → ℝ) → ℝ) := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem exists_close_of_mem_closedNbhd {S : Set (Fin 4 → ℝ)} {η η' : ℝ} (hη : η < η')
    (hη' : 0 < η') {y : Fin 4 → ℝ} (hy : y ∈ closedNbhd S η) :
    ∃ z ∈ S, euclidNorm (y - z) < η' := by
  have h : setDistR4 {y} S < ENNReal.ofReal η' :=
    lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff hη').mpr hη)
  simp only [setDistR4, iInf_singleton, iInf_lt_iff] at h
  obtain ⟨z, hz, h⟩ := h
  exact ⟨z, hz, (ENNReal.ofReal_lt_ofReal_iff hη').mp h⟩
theorem mem_closedNbhd_of_close {S : Set (Fin 4 → ℝ)} {η : ℝ} {y z : Fin 4 → ℝ}
    (hz : z ∈ S) (h : euclidNorm (y - z) ≤ η) : y ∈ closedNbhd S η := by
  show setDistR4 {y} S ≤ _
  simp only [setDistR4, iInf_singleton]
  exact (iInf₂_le z hz).trans (ENNReal.ofReal_le_ofReal h)
theorem subset_closedNbhd (S : Set (Fin 4 → ℝ)) {η : ℝ} (hη : 0 ≤ η) :
    S ⊆ closedNbhd S η := fun y hy =>
  mem_closedNbhd_of_close hy (by simpa [TorusMetric.euclidNormVec] using hη)
theorem exists_isAdmissibleSets_closedNbhd (hS : SupportFacts.AllSupportFacts) {k : ℕ+}
    (S : Fin k → Set (Fin 4 → ℝ)) (hc : ∀ i, IsCompact (S i))
    (hd : ∀ i j, i ≠ j → Disjoint (S i) (S j)) {η₀ : ℝ} (h₀ : 0 < η₀) :
    ∃ (η R : ℝ) (hη : 0 < η) (hR : 0 < R), η ≤ η₀ ∧
      IsAdmissibleSets D η R hη hR fun i => closedNbhd (S i) η := by
  obtain ⟨ε, hε, hle⟩ := exists_pos_ofReal_le (ι := {p : Fin k × Fin k // p.1 ≠ p.2})
    (a := fun p => Domain.euclidean.setDist D (S p.1.1) (S p.1.2))
    fun p => (hS D).2.2.2.2.2.2.2.1 _ _ (hc _) (hc _) (hd _ _ p.2)
  have hb : ∀ i, ∃ C : ℝ, ∀ x ∈ S i, euclidNorm x ≤ C := fun i => by
    obtain ⟨C, hC⟩ := (hc i).exists_bound_of_continuousOn continuous_euclidNorm.continuousOn
    exact ⟨C, fun x hx => (le_abs_self _).trans (hC x hx)⟩
  choose C hC using hb
  set η : ℝ := min η₀ (ε / 3) with hηdef
  have hη : 0 < η := lt_min h₀ (by positivity)
  set B : ℝ := ∑ i, max (C i) 0 with hB
  have hCB : ∀ i, C i ≤ B := fun i =>
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun i => max (C i) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_univ i))
  have hR : 0 < B + 2 * η := by positivity
  refine ⟨η, B + 2 * η, hη, hR, min_le_left _ _, fun l => ⟨0, fun y hy => ?_⟩, fun l j hlj => ?_⟩
  · obtain ⟨z, hz, h⟩ := exists_close_of_mem_closedNbhd (η' := 2 * η) (by linarith)
      (by positivity) hy
    have h₁ := Periodization.euclidNormVec_triangle (y - z) z
    rw [sub_add_cancel] at h₁
    have h₂ := (hC l z hz).trans (hCB l)
    show TorusMetric.euclidNormVec (y - 0) ≤ _
    rw [sub_zero]
    linarith
  · have hfar := ((hS D).1 (S l) (S j) η η (hc l) (hc j) hη hη).1
    refine le_trans ?_ hfar
    refine ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top
      (ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top ?_)
    refine le_trans ?_ (hle ⟨(l, j), hlj⟩)
    rw [← ENNReal.ofReal_add hη.le hη.le, ← ENNReal.ofReal_add (by positivity) hη.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have : η ≤ ε / 3 := min_le_right _ _
    linarith
theorem entrySupp_actAny {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s) (t : FnTuple)
    (i : Fin t.1) : entrySupp D ((actAny hs t).2 i) =
      hs.toPerm.symm ⁻¹' entrySupp D (t.2 i) :=
  tsupport_comp_eq_preimage (t.2 i) (motionHomeomorph hs).symm
theorem translationMotion_symm_apply (v x : Fin 4 → ℝ) :
    (isEuclideanMotion_translationEquiv v).toPerm.symm x = x - v :=
  (Equiv.symm_apply_eq _).mpr (by simp)
theorem ennSharpNorm_motionSymbol_fn (hI : MotionFacts.MotionInvariance D)
    {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s) (X : SpaceTimeSymbol D)
    (i : Fin X.1.1) :
    Domain.euclidean.ennSharpNorm D ((motionSymbol hs X).1.2 i) =
      Domain.euclidean.ennSharpNorm D (X.1.2 i) :=
  ennSharpNorm_comp_motion hI hs.symm (fn_mem_c1SupportedIn X i)
theorem ennSharpNorm_zero :
    Domain.euclidean.ennSharpNorm D (0 : RealFun (Fin 4 → ℝ)) = 0 := by
  simp [Domain.ennSharpNorm, ennSupNorm, Domain.lipConst, ennLipConst]
section Translation
variable (hS : SupportFacts.AllSupportFacts)
  (hI : MotionFacts.MotionInvariance D) (hT : MotionFacts.TranslationModulusProps D)
include hS hI hT
theorem continuousInShift {m : SpaceTimeSymbol D → ℝ} {bound : ℕ+ → ℝ → ℝ → ℝ≥0}
    (h₁ : IsNormedSymmMultilinear m) (h₂ : IsScaleBounded m bound) :
    ContinuousInShift m := by
  intro X Y v h
  by_cases hn : X.1.1 + Y.1.1 = 0
  · have hdef : ∀ v', AppendDefined D X.1 (translateSymbol v' Y).1 := fun v' i => by
      have h₃ : (i : ℕ) < X.1.1 + Y.1.1 := i.2
      omega
    refine ⟨Eventually.of_forall hdef, fun ε hε => Eventually.of_forall fun v' => ⟨hdef v', ?_⟩⟩
    have e : sepAppend X (translateSymbol v' Y) (hdef v') =
        sepAppend X (translateSymbol v Y) h :=
      Subtype.ext (((fst_eq_zero_iff _).mp hn).trans ((fst_eq_zero_iff _).mp hn).symm)
    rw [e, sub_self, abs_zero]
    exact hε
  let k : ℕ+ := ⟨X.1.1 + Y.1.1, Nat.pos_of_ne_zero hn⟩
  let f : (Fin 4 → ℝ) → Fin (X.1.1 + Y.1.1) → RealFun (Fin 4 → ℝ) :=
    fun v' => Fin.append X.1.2 (translateSymbol v' Y).1.2
  let Z := sepAppend X (translateSymbol v Y) h
  have hmem : ∀ i, f v i ∈ c1SupportedIn (entrySupp D (f v i)) := fn_mem_c1SupportedIn Z
  obtain ⟨η, R, hη, hR, -, hA⟩ := exists_isAdmissibleSets_closedNbhd (D := D) hS (k := k)
    (fun i => entrySupp D (f v i)) (fun i => (hmem i).2.1)
    (fun i j hij => h hij) one_pos
  let A : Fin k → Set (Fin 4 → ℝ) := fun i => closedNbhd (entrySupp D (f v i)) η
  have key : ∀ v', euclidNorm (v' - v) ≤ η → ∀ i : Fin (X.1.1 + Y.1.1),
      f v' i ∈ c1SupportedIn (A i) := by
    intro v' hv i
    induction i using Fin.addCases with
    | left i =>
      have e : ∀ w, f w (Fin.castAdd _ i) = X.1.2 i := fun w => Fin.append_left _ _ i
      show f v' _ ∈ c1SupportedIn (closedNbhd (entrySupp D (f v _)) η)
      rw [e, e]
      have hx := fn_mem_c1SupportedIn X i
      exact ⟨hx.1, hx.2.1, hx.2.2.trans (subset_closedNbhd _ hη.le)⟩
    | right j =>
      have e : ∀ w, f w (Fin.natAdd _ j) = (translateSymbol w Y).1.2 j := fun w =>
        Fin.append_right _ _ j
      show f v' _ ∈ c1SupportedIn (closedNbhd (entrySupp D (f v _)) η)
      rw [e, e]
      have hx := fn_mem_c1SupportedIn (translateSymbol v' Y) j
      refine ⟨hx.1, hx.2.1, fun x hx' => ?_⟩
      have s₁ := entrySupp_actAny (D := D) (isEuclideanMotion_translationEquiv v') Y.1 j
      have s₂ := entrySupp_actAny (D := D) (isEuclideanMotion_translationEquiv v) Y.1 j
      have hx₁ : x - v' ∈ entrySupp D (Y.1.2 j) := by
        have : x ∈ (isEuclideanMotion_translationEquiv v').toPerm.symm ⁻¹' entrySupp D (Y.1.2 j) := by
          rw [← s₁]
          exact hx'
        rwa [Set.mem_preimage, translationMotion_symm_apply] at this
      have hx₂ : x - v' + v ∈ entrySupp D ((translateSymbol v Y).1.2 j) := by
        show _ ∈ entrySupp D ((actAny _ Y.1).2 j)
        rw [s₂, Set.mem_preimage, translationMotion_symm_apply, add_sub_cancel_right]
        exact hx₁
      refine mem_closedNbhd_of_close hx₂ ?_
      have e₁ : x - (x - v' + v) = v' - v := by abel
      rw [e₁]
      exact hv
  have hdef : ∀ v', euclidNorm (v' - v) ≤ η →
      AppendDefined D X.1 (translateSymbol v' Y).1 := fun v' hv i j hij =>
    (mem_of_forall_mem_c1SupportedIn hS hA (key v' hv)).1.1.pairwise_disjoint i j hij
  have hcv : Tendsto (fun v' : Fin 4 → ℝ => euclidNorm (v' - v)) (𝓝 v) (𝓝 0) := by
    have hc : Continuous fun v' : Fin 4 → ℝ => euclidNorm (v' - v) :=
      continuous_euclidNorm.comp (continuous_id.sub continuous_const)
    have := hc.tendsto v
    simpa [TorusMetric.euclidNormVec] using this
  have near : ∀ᶠ v' in 𝓝 v, euclidNorm (v' - v) ≤ η :=
    (hcv.eventually (Iio_mem_nhds hη)).mono fun _ hx => le_of_lt hx
  refine ⟨near.mono hdef, fun ε hε => ?_⟩
  have hfin : ∀ i, Domain.euclidean.ennSharpNorm D (f v i) < ∞ := fun i =>
    ennSharpNorm_lt_top (hmem i)
  have hsame : ∀ v' (i : Fin (X.1.1 + Y.1.1)), Domain.euclidean.ennSharpNorm D (f v' i) =
      Domain.euclidean.ennSharpNorm D (f v i) := by
    intro v' i
    induction i using Fin.addCases with
    | left i =>
      have e : ∀ w, f w (Fin.castAdd _ i) = X.1.2 i := fun w => Fin.append_left _ _ i
      rw [e, e]
    | right j =>
      have e : ∀ w, f w (Fin.natAdd _ j) = (translateSymbol w Y).1.2 j := fun w =>
        Fin.append_right _ _ j
      rw [e, e]
      exact (ennSharpNorm_motionSymbol_fn hI _ Y j).trans (ennSharpNorm_motionSymbol_fn hI _ Y j).symm
  let E : (Fin 4 → ℝ) → Fin (X.1.1 + Y.1.1) → ℝ≥0∞ := fun v' i =>
    Domain.euclidean.ennSharpNorm D (f v' i - f v i)
  have hE : ∀ i, Tendsto (fun v' => E v' i) (𝓝 v) (𝓝 0) := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      have e : ∀ w, f w (Fin.castAdd _ i) = X.1.2 i := fun w => Fin.append_left _ _ i
      have : ∀ v', E v' (Fin.castAdd _ i) = 0 := fun v' => by
        simp only [E, e, sub_self]
        exact ennSharpNorm_zero
      simp only [this]
      exact tendsto_const_nhds
    | right j =>
      have e : ∀ w, f w (Fin.natAdd _ j) = (translateSymbol w Y).1.2 j := fun w =>
        Fin.append_right _ _ j
      let g : realC1Compact := ⟨Y.1.2 j, mem_realC1Compact_of_mem (fn_mem_c1SupportedIn Y j)⟩
      have hup : ∀ v', E v' (Fin.natAdd _ j) ≤
          D.translationModulus g (Real.toNNReal (euclidNorm (v' - v))) := fun v' => by
        simp only [E, e, translateSymbol_fn]
        exact (hT g).2.2.1 v' v
      have hlim : Tendsto (fun v' : Fin 4 → ℝ =>
          D.translationModulus g (Real.toNNReal (euclidNorm (v' - v)))) (𝓝 v) (𝓝 0) := by
        refine (hT g).2.1.comp ?_
        have h₃ := (continuous_real_toNNReal.tendsto 0).comp hcv
        rw [Real.toNNReal_zero] at h₃
        exact h₃
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun _ => bot_le) hup
  let C : Fin k → ℝ≥0∞ := fun i => ∏ l ∈ Finset.univ.erase i,
    Domain.euclidean.ennSharpNorm D (f v l)
  have hC : ∀ i, C i ≠ ∞ := fun i =>
    (ENNReal.prod_lt_top fun l _ => hfin l).ne
  have hsum : Tendsto (fun v' => (bound k η R : ℝ≥0∞) * ∑ i : Fin k, E v' i * C i) (𝓝 v) (𝓝 0) := by
    have h₃ := ENNReal.Tendsto.const_mul (a := (bound k η R : ℝ≥0∞))
      (tendsto_finsetSum (Finset.univ : Finset (Fin k))
        fun i _ => ENNReal.Tendsto.mul_const (hE i) (Or.inr (hC i)))
      (Or.inr ENNReal.coe_ne_top)
    simpa using h₃
  have hsmall := hsum.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))
  filter_upwards [near, hsmall] with v' hv hs
  refine ⟨hdef v' hv, ?_⟩
  obtain ⟨hf, hf', hb⟩ := lipschitzOnProducts hS h₁ h₂ k η R hη hR A hA (f v') (f v) (key v' hv)
    (key v (by simpa [TorusMetric.euclidNormVec] using hη.le))
  have e : ∀ i : Fin k, ∏ l ∈ Finset.univ.erase i,
      max (Domain.euclidean.ennSharpNorm D (f v' l))
        (Domain.euclidean.ennSharpNorm D (f v l)) = C i := fun i =>
    Finset.prod_congr rfl fun l _ => by rw [hsame v' l, max_self]
  simp only [e] at hb
  have h₄ : ENNReal.ofReal |m ⟨_, hf⟩ - m ⟨_, hf'⟩| < ENNReal.ofReal ε := lt_of_le_of_lt hb hs
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp h₄
end Translation
theorem actAny_comp_congr {s₁ s₂ s₁' s₂' : (Fin 4 → ℝ) → Fin 4 → ℝ} (h₁ : IsEuclideanMotion s₁)
    (h₂ : IsEuclideanMotion s₂) (h₁' : IsEuclideanMotion s₁')
    (h₂' : IsEuclideanMotion s₂') (e : ∀ x, s₁ (s₂ x) = s₁' (s₂' x)) (t : FnTuple) :
    actAny h₁ (actAny h₂ t) = actAny h₁' (actAny h₂' t) := by
  have key : ∀ x, h₂.toPerm.symm (h₁.toPerm.symm x) = h₂'.toPerm.symm (h₁'.toPerm.symm x) := by
    intro x
    set y := h₂.toPerm.symm (h₁.toPerm.symm x) with hy
    have e₁ : s₁ (s₂ y) = x := by
      have a : s₂ y = h₁.toPerm.symm x := h₂.toPerm.apply_symm_apply _
      rw [a]
      exact h₁.toPerm.apply_symm_apply _
    rw [← e₁, e]
    have a₁ : h₁'.toPerm.symm (s₁' (s₂' y)) = s₂' y := h₁'.toPerm.symm_apply_apply _
    rw [a₁]
    exact (h₂'.toPerm.symm_apply_apply _).symm
  refine Sigma.ext rfl (heq_of_eq (funext fun i => funext fun x => ?_))
  show t.2 i (h₂.toPerm.symm (h₁.toPerm.symm x)) = t.2 i (h₂'.toPerm.symm (h₁'.toPerm.symm x))
  rw [key]
theorem actAny_of_eq_id {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (h : IsEuclideanMotion s) (e : ∀ x, s x = x)
    (t : FnTuple) : actAny h t = t := by
  refine Sigma.ext rfl (heq_of_eq (funext fun i => funext fun x => ?_))
  show t.2 i (h.toPerm.symm x) = t.2 i x
  rw [show h.toPerm.symm x = x from (Equiv.symm_apply_eq _).mpr (e x).symm]
theorem translationEquiv_zero_apply_eq (x : Fin 4 → ℝ) : translationEquiv 0 x = x := by
  simp [translationEquiv]
theorem actAny_actAny {s₁ s₂ s₃ : (Fin 4 → ℝ) → Fin 4 → ℝ} (h₁ : IsEuclideanMotion s₁)
    (h₂ : IsEuclideanMotion s₂) (h₃ : IsEuclideanMotion s₃)
    (e : ∀ x, s₁ (s₂ x) = s₃ x) (t : FnTuple) :
    actAny h₁ (actAny h₂ t) = actAny h₃ t := by
  rw [actAny_comp_congr h₁ h₂ h₃ (isEuclideanMotion_translationEquiv 0)
    (fun x => by rw [e, translationEquiv_zero_apply_eq]) t,
    actAny_of_eq_id (isEuclideanMotion_translationEquiv 0) translationEquiv_zero_apply_eq]
theorem actAny_actAny_of_inv {s₁ s₂ : (Fin 4 → ℝ) → Fin 4 → ℝ} (h₁ : IsEuclideanMotion s₁)
    (h₂ : IsEuclideanMotion s₂) (e : ∀ x, s₁ (s₂ x) = x) (t : FnTuple) :
    actAny h₁ (actAny h₂ t) = t := by
  rw [actAny_actAny h₁ h₂ (isEuclideanMotion_translationEquiv 0)
    (fun x => by rw [e, translationEquiv_zero_apply_eq]) t,
    actAny_of_eq_id (isEuclideanMotion_translationEquiv 0) translationEquiv_zero_apply_eq]
theorem reflectSymbol_reflectSymbol (X : SpaceTimeSymbol D) : reflectSymbol (reflectSymbol X) = X :=
  Subtype.ext (actAny_actAny_of_inv isEuclideanMotion_timeReflect isEuclideanMotion_timeReflect
    timeReflect_timeReflect X.1)
theorem translationEquiv_mem_affineHyperoctahedral (v : Fin 4 → ℝ) :
    ⇑(translationEquiv v) ∈ affineHyperoctahedral :=
  ⟨1, v, funext fun x => by simp [affinePair, translationEquiv]⟩
theorem sepAppend_congr {A A' B B' : SpaceTimeSymbol D} (a : A = A') (b : B = B')
    (h : AppendDefined D A.1 B.1) (h' : AppendDefined D A'.1 B'.1) :
    sepAppend A B h = sepAppend A' B' h' := by
  subst a b
  rfl
theorem eq_of_perm {m : SpaceTimeSymbol D → ℝ} (h₁ : IsNormedSymmMultilinear m)
    (X Y : SpaceTimeSymbol D) (σ : Fin Y.1.1 ≃ Fin X.1.1) (h : ∀ i, Y.1.2 i = X.1.2 (σ i)) :
    m X = m Y := by
  obtain ⟨⟨n, f⟩, hX⟩ := X
  obtain ⟨⟨n', g⟩, hY⟩ := Y
  have e : n' = n := by simpa using Fintype.card_congr σ
  subst e
  dsimp only at σ h
  have hg : g = fun i => f (σ i) := funext h
  subst hg
  rcases Nat.eq_zero_or_pos n' with rfl | hn
  · congr 1
    exact Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun i => i.elim0)))
  · exact h₁.symmetric ⟨n', hn⟩ ⟨f, mem_symbolsOfCard_of_mem (k := ⟨n', hn⟩) hX⟩ σ
theorem sepAppend_comm {m : SpaceTimeSymbol D → ℝ} (h₁ : IsNormedSymmMultilinear m)
    (X Y : SpaceTimeSymbol D) (hd : AppendDefined D X.1 Y.1)
    (hd' : AppendDefined D Y.1 X.1) :
    m (sepAppend X Y hd) = m (sepAppend Y X hd') := by
  refine eq_of_perm h₁ _ _ finAddFlip fun i => ?_
  show Fin.append Y.1.2 X.1.2 i = Fin.append X.1.2 Y.1.2 (finAddFlip i)
  induction i using Fin.addCases with
  | left i => rw [finAddFlip_apply_castAdd, Fin.append_left, Fin.append_right]
  | right j => rw [finAddFlip_apply_natAdd, Fin.append_left, Fin.append_right]
section Invariance
variable {m : SpaceTimeSymbol D → ℝ}
  (hAct : StabilizerAction.MotionsOnSymbols D)
  (h₃ : IsMotionInvariant m)
include hAct h₃
theorem reflectAppend_congr_motion {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s)
    (hm : s ∈ affineHyperoctahedral) (X Y X' Y' : PosSymbol D)
    (e₁ : motionSymbol hs (reflectSymbol (posToSymbol X)) = reflectSymbol (posToSymbol X'))
    (e₂ : motionSymbol hs (posToSymbol Y) = posToSymbol Y') :
    m (reflectAppend X Y) = m (reflectAppend X' Y') := by
  obtain ⟨-, -, -, hcat⟩ := hAct s s hs hs (reflectSymbol (posToSymbol X)) (posToSymbol Y)
  obtain ⟨hd', e⟩ := hcat (appendDefined_reflect X Y)
  have h := h₃ s hs hm (reflectAppend X Y)
  rw [← h]
  show m (motionSymbol hs (sepAppend _ _ _)) = _
  rw [← e]
  exact congrArg m (sepAppend_congr e₁ e₂ _ _)
theorem reflectAppend_swap (h₁ : IsNormedSymmMultilinear m) (X Y : PosSymbol D) :
    m (reflectAppend Y X) = m (reflectAppend X Y) := by
  obtain ⟨-, -, -, hcat⟩ := hAct timeReflect timeReflect isEuclideanMotion_timeReflect
    isEuclideanMotion_timeReflect (reflectSymbol (posToSymbol Y)) (posToSymbol X)
  obtain ⟨hd', e⟩ := hcat (appendDefined_reflect Y X)
  have h := h₃ timeReflect isEuclideanMotion_timeReflect
    (hyperplaneReflect_mem_affineHyperoctahedral 3 0) (reflectAppend Y X)
  rw [← h]
  show m (motionSymbol isEuclideanMotion_timeReflect (sepAppend _ _ _)) = _
  rw [← e]
  have hd₂ : AppendDefined D (posToSymbol Y).1 (reflectSymbol (posToSymbol X)).1 := by
    have h₂ := appendDefined_reflect X Y
    rw [appendDefined_iff (reflectSymbol (posToSymbol X)).2 (posToSymbol Y).2] at h₂
    exact (appendDefined_iff (posToSymbol Y).2
      (reflectSymbol (posToSymbol X)).2).mpr fun i j => (h₂ j i).symm
  have e₂ : sepAppend (motionSymbol isEuclideanMotion_timeReflect (reflectSymbol (posToSymbol Y)))
      (motionSymbol isEuclideanMotion_timeReflect (posToSymbol X)) hd' =
      sepAppend (posToSymbol Y) (reflectSymbol (posToSymbol X)) hd₂ :=
    sepAppend_congr (reflectSymbol_reflectSymbol _) rfl _ _
  rw [e₂]
  exact sepAppend_comm h₁ _ _ _ _
end Invariance
section Forms
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {q : V → V → ℂ}
theorem sesq_zero_left (hq : IsSesquilinear q) (G : V) : q 0 G = 0 := by
  have := hq.smul_left 0 0 G
  simpa using this
theorem sesq_zero_right (hq : IsSesquilinear q) (G : V) : q G 0 = 0 := by
  have := hq.smul_right 0 G 0
  simpa using this
theorem sesq_sum_left (hq : IsSesquilinear q) {ι : Type*} (s : Finset ι) (F : ι → V) (G : V) :
    q (∑ p ∈ s, F p) G = ∑ p ∈ s, q (F p) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sesq_zero_left hq G
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hq.add_left, ih]
theorem sesq_sum_right (hq : IsSesquilinear q) {ι : Type*} (s : Finset ι) (F : ι → V) (G : V) :
    q G (∑ p ∈ s, F p) = ∑ p ∈ s, q G (F p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sesq_zero_right hq G
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hq.add_right, ih]
theorem isSesquilinear_comp (hq : IsSesquilinear q) (A B : V →ₗ[ℂ] V) :
    IsSesquilinear fun F F' => q (A F) (B F') where
  add_left F₁ F₂ F' := by simp only [map_add, hq.add_left]
  smul_left c F F' := by simp only [map_smul, hq.smul_left]
  add_right F F₁ F₂ := by simp only [map_add, hq.add_right]
  smul_right c F F' := by simp only [map_smul, hq.smul_right]
end Forms
section Vectors
variable {O : Set (Fin 4 → ℝ)}
theorem sesq_linComb {q : SepSpan D O → SepSpan D O → ℂ} (hq : IsSesquilinear q) {ι κ : Type*}
    [Fintype ι] [Fintype κ] (c : ι → ℂ) (X : ι → SepTuple D O) (c' : κ → ℂ)
    (Y : κ → SepTuple D O) :
    q (linComb c X) (linComb c' Y) =
      ∑ p, ∑ r, conj (c p) * c' r * q (basisVec (X p)) (basisVec (Y r)) := by
  simp only [linComb, sesq_sum_left hq, sesq_sum_right hq, hq.smul_left, hq.smul_right]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  ring
theorem exists_eq_linComb (F : SepSpan D O) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (X : ι → SepTuple D O), F = linComb c X :=
  ⟨F.support, inferInstance, _, _, eq_linComb_support F⟩
theorem sesq_ext_basis {q₁ q₂ : SepSpan D O → SepSpan D O → ℂ} (h₁ : IsSesquilinear q₁)
    (h₂ : IsSesquilinear q₂)
    (h : ∀ X Y, q₁ (basisVec X) (basisVec Y) = q₂ (basisVec X) (basisVec Y))
    (F F' : SepSpan D O) : q₁ F F' = q₂ F F' := by
  obtain ⟨ι, _, c, X, rfl⟩ := exists_eq_linComb F
  obtain ⟨κ, _, c', Y, rfl⟩ := exists_eq_linComb F'
  rw [sesq_linComb h₁, sesq_linComb h₂]
  simp only [h]
theorem linearMap_ext_basis {W : Type*} [AddCommGroup W] [Module ℂ W] {A B : SepSpan D O →ₗ[ℂ] W}
    (h : ∀ X, A (basisVec X) = B (basisVec X)) : A = B :=
  (sepBasis D O).ext fun f => by rw [sepBasis_apply, h]
theorem conjCoeffs_add (F G : SepSpan D O) : conjCoeffs (F + G) = conjCoeffs F + conjCoeffs G :=
  Finsupp.mapRange_add (map_add _) F G
theorem conjCoeffs_smul (c : ℂ) (F : SepSpan D O) : conjCoeffs (c • F) = conj c • conjCoeffs F := by
  ext g
  simp [conjCoeffs]
end Vectors
theorem isSesquilinear_osForm (m : SpaceTimeSymbol D → ℝ) : IsSesquilinear (osForm m) where
  add_left F₁ F₂ F' := by simp only [osForm, conjCoeffs_add, map_add, LinearMap.add_apply]
  smul_left c F F' := by
    simp only [osForm, conjCoeffs_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  add_right F F₁ F₂ := by simp only [osForm, map_add]
  smul_right c F F' := by simp only [osForm, map_smul, smul_eq_mul]
theorem osForm_linComb (m : SpaceTimeSymbol D → ℝ) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℂ) (X : ι → PosSymbol D) (c' : κ → ℂ) (Y : κ → PosSymbol D) :
    osForm m (linComb c X) (linComb c' Y) =
      ∑ p, ∑ r, conj (c p) * c' r * ((m (reflectAppend (X p) (Y r)) : ℝ) : ℂ) := by
  rw [sesq_linComb (isSesquilinear_osForm m)]
  simp only [osForm_basisVec]
theorem isHermitianForm_osForm {m : SpaceTimeSymbol D → ℝ}
    (hAct : StabilizerAction.MotionsOnSymbols D)
    (h₁ : IsNormedSymmMultilinear m) (h₃ : IsMotionInvariant m) :
    IsHermitianForm (osForm m) where
  toIsSesquilinear := isSesquilinear_osForm m
  conj_symm F F' := by
    obtain ⟨ι, _, c, X, rfl⟩ := exists_eq_linComb F
    obtain ⟨κ, _, c', Y, rfl⟩ := exists_eq_linComb F'
    rw [osForm_linComb, osForm_linComb, map_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [reflectAppend_swap hAct h₃ h₁, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring
theorem isPosSemidefForm_osForm {m : SpaceTimeSymbol D → ℝ} (h₄ : IsReflPositive m) :
    IsPosSemidefForm (osForm m) where
  toIsSesquilinear := isSesquilinear_osForm m
  nonneg F := by
    obtain ⟨ι, _, c, X, rfl⟩ := exists_eq_linComb F
    rw [osForm_linComb]
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp
    · have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
      have h := h₄ _ hn (fun i => X ((Fintype.equivFin ι).symm i))
        (fun i => c ((Fintype.equivFin ι).symm i))
      have e : ∀ g : ι → ι → ℂ, ∑ p : Fin (Fintype.card ι), ∑ r : Fin (Fintype.card ι),
          g ((Fintype.equivFin ι).symm p) ((Fintype.equivFin ι).symm r) = ∑ p, ∑ r, g p r :=
        fun g => by
          rw [Equiv.sum_comp (Fintype.equivFin ι).symm
            (fun p => ∑ r : Fin (Fintype.card ι), g p ((Fintype.equivFin ι).symm r))]
          exact Finset.sum_congr rfl fun p _ =>
            Equiv.sum_comp (Fintype.equivFin ι).symm (fun r => g p r)
      rw [← e]
      exact h
theorem semigroupMap_basisVec (m : SpaceTimeSymbol D → ℝ) (t : ℝ≥0) (X : PosSymbol D) :
    (osPreHilbertData m).semigroupMap t (basisVec X) = basisVec (posTimeShift t X) :=
  linExtend_basisVec _ X
theorem translationMap_basisVec (m : SpaceTimeSymbol D → ℝ) (a : EuclideanBorel.Space 3)
    (X : PosSymbol D) :
    (osPreHilbertData m).translationMap a (basisVec X) = basisVec (posSpaceShift a.ofLp X) :=
  linExtend_basisVec _ X
theorem rotationMap_basisVec (m : SpaceTimeSymbol D → ℝ) (w : timeAxisStabilizer)
    (X : PosSymbol D) :
    (osPreHilbertData m).rotationMap w (basisVec X) = basisVec (posRotate w X) :=
  linExtend_basisVec _ X
theorem spaceTimePoint_add_zero (a a' : Fin 3 → ℝ) :
    spaceTimePoint (a + a') 0 = spaceTimePoint a 0 + spaceTimePoint a' 0 := by
  funext ν
  induction ν using Fin.lastCases with
  | last =>
    have e : ∀ b : Fin 3 → ℝ, spaceTimePoint b 0 (Fin.last 3) = 0 := fun b =>
      spaceTimePoint_last b 0
    rw [Pi.add_apply, e, e, e, add_zero]
  | cast j =>
    rw [Pi.add_apply, spaceTimePoint_castSucc, spaceTimePoint_castSucc, spaceTimePoint_castSucc,
      Pi.add_apply]
theorem spaceTimePoint_zero_zero : spaceTimePoint (0 : Fin 3 → ℝ) 0 = 0 := spaceTimePoint_init 0
section Relations
variable (m : SpaceTimeSymbol D → ℝ)
theorem osSemigroup_zero : (osPreHilbertData m).semigroupMap 0 = LinearMap.id :=
  linearMap_ext_basis fun X => by
    rw [semigroupMap_basisVec]
    exact congrArg TorusTransport.TupleVectors.basisVec (Subtype.ext (actAny_of_eq_id _ (fun x => by simp [translationEquiv]) _))
theorem osTranslation_zero : (osPreHilbertData m).translationMap 0 = LinearMap.id :=
  linearMap_ext_basis fun X => by
    rw [translationMap_basisVec]
    refine congrArg TorusTransport.TupleVectors.basisVec (Subtype.ext (actAny_of_eq_id _ (fun x => ?_) _))
    have e : (0 : EuclideanBorel.Space 3).ofLp = 0 := rfl
    rw [e, spaceTimePoint_zero_zero, translationEquiv_zero_apply_eq]
theorem osRotation_one : (osPreHilbertData m).rotationMap 1 = LinearMap.id :=
  linearMap_ext_basis fun X => by
    rw [rotationMap_basisVec]
    exact congrArg TorusTransport.TupleVectors.basisVec (Subtype.ext (actAny_of_eq_id _ (fun _ => rfl) _))
theorem osSemigroup_comp (t t' : ℝ≥0) : (osPreHilbertData m).semigroupMap t ∘ₗ
    (osPreHilbertData m).semigroupMap t' = (osPreHilbertData m).semigroupMap (t + t') :=
  linearMap_ext_basis fun X => by
    rw [LinearMap.comp_apply, semigroupMap_basisVec, semigroupMap_basisVec, semigroupMap_basisVec]
    refine congrArg TorusTransport.TupleVectors.basisVec (Subtype.ext (actAny_actAny _ _ _ (fun x => ?_) _))
    simp only [translationEquiv, Equiv.coe_addRight, NNReal.coe_add, add_smul]
    abel
theorem osTranslation_comp (a a' : EuclideanBorel.Space 3) : (osPreHilbertData m).translationMap a ∘ₗ
    (osPreHilbertData m).translationMap a' = (osPreHilbertData m).translationMap (a + a') :=
  linearMap_ext_basis fun X => by
    rw [LinearMap.comp_apply, translationMap_basisVec, translationMap_basisVec,
      translationMap_basisVec]
    refine congrArg TorusTransport.TupleVectors.basisVec (Subtype.ext (actAny_actAny _ _ _ (fun x => ?_) _))
    have e : (a + a').ofLp = a.ofLp + a'.ofLp := rfl
    rw [e, spaceTimePoint_add_zero]
    simp only [translationEquiv, Equiv.coe_addRight]
    abel
theorem osRotation_comp (w w' : timeAxisStabilizer) : (osPreHilbertData m).rotationMap w ∘ₗ
    (osPreHilbertData m).rotationMap w' = (osPreHilbertData m).rotationMap (w * w') :=
  linearMap_ext_basis fun X => by
    rw [LinearMap.comp_apply, rotationMap_basisVec, rotationMap_basisVec, rotationMap_basisVec]
    exact congrArg TorusTransport.TupleVectors.basisVec (Subtype.ext (actAny_actAny _ _ _ (fun _ => rfl) _))
theorem osTranslation_comm (a : EuclideanBorel.Space 3) (t : ℝ≥0) :
    (osPreHilbertData m).translationMap a ∘ₗ (osPreHilbertData m).semigroupMap t =
      (osPreHilbertData m).semigroupMap t ∘ₗ (osPreHilbertData m).translationMap a :=
  linearMap_ext_basis fun X => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, semigroupMap_basisVec, translationMap_basisVec,
      translationMap_basisVec, semigroupMap_basisVec]
    refine congrArg TorusTransport.TupleVectors.basisVec (Subtype.ext (actAny_comp_congr _ _ _ _ (fun x => ?_) _))
    simp only [translationEquiv, Equiv.coe_addRight]
    abel
variable {m}
variable (hC : StabilizerAction.CommRelations)
include hC
theorem osRotation_comm (w : timeAxisStabilizer) (t : ℝ≥0) :
    (osPreHilbertData m).rotationMap w ∘ₗ (osPreHilbertData m).semigroupMap t =
      (osPreHilbertData m).semigroupMap t ∘ₗ (osPreHilbertData m).rotationMap w :=
  linearMap_ext_basis fun X => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, semigroupMap_basisVec, rotationMap_basisVec,
      rotationMap_basisVec, semigroupMap_basisVec]
    refine congrArg TorusTransport.TupleVectors.basisVec (Subtype.ext (actAny_comp_congr _ _ _ _ (fun x => ?_) _))
    exact congrFun (hC w 0 t).2.2.2.2 x
theorem osRotation_translation (w : timeAxisStabilizer) (a : EuclideanBorel.Space 3) :
    (osPreHilbertData m).rotationMap w ∘ₗ (osPreHilbertData m).translationMap a =
      (osPreHilbertData m).translationMap (rotateSpatial w a) ∘ₗ
        (osPreHilbertData m).rotationMap w :=
  linearMap_ext_basis fun X => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, translationMap_basisVec, rotationMap_basisVec,
      rotationMap_basisVec, translationMap_basisVec]
    refine congrArg TorusTransport.TupleVectors.basisVec (Subtype.ext (actAny_comp_congr _ _ _ _ (fun x => ?_) _))
    exact congrFun (hC w a.ofLp 0).2.2.2.1 x
variable (hAct : StabilizerAction.MotionsOnSymbols D)
  (h₃ : IsMotionInvariant m)
include hAct h₃
theorem osForm_semigroup (t : ℝ≥0) (F F' : PosSymbolSpan D) :
    osForm m F ((osPreHilbertData m).semigroupMap t F') =
      osForm m ((osPreHilbertData m).semigroupMap t F) F' := by
  refine sesq_ext_basis (q₁ := fun F F' => osForm m (LinearMap.id F)
      ((osPreHilbertData m).semigroupMap t F'))
    (q₂ := fun F F' => osForm m ((osPreHilbertData m).semigroupMap t F) (LinearMap.id F'))
    (isSesquilinear_comp (isSesquilinear_osForm m) _ _)
    (isSesquilinear_comp (isSesquilinear_osForm m) _ _) (fun X Y => ?_) F F'
  simp only [LinearMap.id_apply, semigroupMap_basisVec, osForm_basisVec]
  refine congrArg _ (reflectAppend_congr_motion hAct h₃
    (isEuclideanMotion_translationEquiv (-((t : ℝ) • timeAxisVec)))
    (translationEquiv_mem_affineHyperoctahedral _) X (posTimeShift t Y) (posTimeShift t X) Y ?_ ?_)
  · refine Subtype.ext (actAny_comp_congr _ _ _ _ (fun x => ?_) _)
    have h := congrFun (hC 1 0 (t : ℝ)).2.2.1 x
    rw [neg_smul] at h
    exact h.symm
  · refine Subtype.ext (actAny_actAny_of_inv _ _ (fun x => ?_) _)
    simp [translationEquiv]
theorem osForm_translation (a : EuclideanBorel.Space 3) (F F' : PosSymbolSpan D) :
    osForm m ((osPreHilbertData m).translationMap a F)
      ((osPreHilbertData m).translationMap a F') = osForm m F F' := by
  refine sesq_ext_basis (q₁ := fun F F' => osForm m ((osPreHilbertData m).translationMap a F)
      ((osPreHilbertData m).translationMap a F'))
    (isSesquilinear_comp (isSesquilinear_osForm m) _ _) (isSesquilinear_osForm m)
    (fun X Y => ?_) F F'
  simp only [translationMap_basisVec, osForm_basisVec]
  refine congrArg _ (reflectAppend_congr_motion hAct h₃
    (isEuclideanMotion_translationEquiv (spaceTimePoint a.ofLp 0))
    (translationEquiv_mem_affineHyperoctahedral _) X Y (posSpaceShift a.ofLp X)
    (posSpaceShift a.ofLp Y) ?_ rfl).symm
  refine Subtype.ext (actAny_comp_congr _ _ _ _ (fun x => ?_) _)
  exact (congrFun (hC 1 a.ofLp 0).2.1 x).symm
theorem osForm_rotation (w : timeAxisStabilizer) (F F' : PosSymbolSpan D) :
    osForm m ((osPreHilbertData m).rotationMap w F)
      ((osPreHilbertData m).rotationMap w F') = osForm m F F' := by
  refine sesq_ext_basis (q₁ := fun F F' => osForm m ((osPreHilbertData m).rotationMap w F)
      ((osPreHilbertData m).rotationMap w F'))
    (isSesquilinear_comp (isSesquilinear_osForm m) _ _) (isSesquilinear_osForm m)
    (fun X Y => ?_) F F'
  simp only [rotationMap_basisVec, osForm_basisVec]
  refine congrArg _ (reflectAppend_congr_motion hAct h₃ (isEuclideanMotion_hyperoctahedral w.1)
    (coe_mem_affineHyperoctahedral w.1) X Y (posRotate w X) (posRotate w Y)
    ?_ rfl).symm
  refine Subtype.ext (actAny_comp_congr _ _ _ _ (fun x => ?_) _)
  exact (congrFun (hC w 0 0).1 x).symm
end Relations
variable (D) in
def IsScaled (d R : ℝ) (t : FnTuple) : Prop :=
  (∀ i, ∃ x, entrySupp D (t.2 i) ⊆ ballR4 x R) ∧
    ∀ i k, i ≠ k → ENNReal.ofReal d ≤
      Domain.euclidean.setDist D (entrySupp D (t.2 i)) (entrySupp D (t.2 k))
theorem isScaled_of_mem {d R : ℝ} {hd : 0 < d} {hR : 0 < R} {t : FnTuple}
    (h : t ∈ scaledSymbols D d R hd hR) : IsScaled D d R t := by
  rcases h with rfl | h
  · exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  · obtain ⟨n, f, hf, rfl⟩ := Set.mem_iUnion.mp h
    exact hf.2
theorem mem_scaledSymbols_of_isScaled {d R : ℝ} {hd : 0 < d} {hR : 0 < R} {t : FnTuple}
    (ht : t ∈ spaceTimeSymbols D) (h : IsScaled D d R t) : t ∈ scaledSymbols D d R hd hR := by
  obtain ⟨n, f⟩ := t
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inl ((fst_eq_zero_iff _).mp rfl)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨n, hn⟩, f, ⟨ht, h⟩, rfl⟩)
theorem le_setDist_iff {c : ℝ≥0∞} {A B : Set (Fin 4 → ℝ)} :
    c ≤ Domain.euclidean.setDist D A B ↔
      ∀ u ∈ A, ∀ v ∈ B, c ≤ ENNReal.ofReal (euclidNorm (u - v)) := by
  simp only [Domain.setDist, le_iInf_iff]
  rfl
theorem euclidNorm_sub_comm (x y : Fin 4 → ℝ) : euclidNorm (x - y) = euclidNorm (y - x) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem abs_last_le_euclidNorm (x : Fin 4 → ℝ) : |x 3| ≤ euclidNorm x := by apply _root_.YangMills.Construction.EuclideanFunctionals.ParametrixBracket.abs_apply_three_le <;> assumption
theorem isScaled_actAny {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s) {d R : ℝ}
    {t : FnTuple} (h : IsScaled D d R t) : IsScaled D d R (actAny hs t) := by
  have hdist : ∀ x y, euclidNorm (hs.toPerm.symm x - hs.toPerm.symm y) = euclidNorm (x - y) :=
    fun x y => hs.symm.isDistancePreserving x y
  refine ⟨fun i => ?_, fun i k hik => ?_⟩
  · obtain ⟨x, hx⟩ := h.1 i
    refine ⟨s x, fun y hy => ?_⟩
    have hy' : y ∈ hs.toPerm.symm ⁻¹' entrySupp D (t.2 i) :=
      (Set.ext_iff.mp (entrySupp_actAny (D := D) hs t i) y).mp hy
    have h₁ : euclidNorm (hs.toPerm.symm y - x) ≤ R := hx hy'
    have h₂ := hdist y (s x)
    rw [show hs.toPerm.symm (s x) = x from hs.toPerm.symm_apply_apply x] at h₂
    show euclidNorm (y - s x) ≤ R
    rw [← h₂]
    exact h₁
  · rw [le_setDist_iff]
    intro u hu v hv
    have hu' : u ∈ hs.toPerm.symm ⁻¹' entrySupp D (t.2 i) :=
      (Set.ext_iff.mp (entrySupp_actAny (D := D) hs t i) u).mp hu
    have hv' : v ∈ hs.toPerm.symm ⁻¹' entrySupp D (t.2 k) :=
      (Set.ext_iff.mp (entrySupp_actAny (D := D) hs t k) v).mp hv
    rw [← hdist]
    exact le_setDist_iff.mp (h.2 i k hik) _ hu' _ hv'
theorem isScaled_tupleAppend {d R : ℝ} {a b : FnTuple} (ha : IsScaled D d R a)
    (hb : IsScaled D d R b) (hf : ∀ i j, ∀ u ∈ entrySupp D (a.2 i),
      ∀ v ∈ entrySupp D (b.2 j), ENNReal.ofReal d ≤ ENNReal.ofReal (euclidNorm (u - v))) :
    IsScaled D d R (tupleAppend a b) := by
  have el : ∀ i, (tupleAppend a b).2 (Fin.castAdd _ i) = a.2 i := fun i =>
    Fin.append_left _ _ i
  have er : ∀ j, (tupleAppend a b).2 (Fin.natAdd _ j) = b.2 j := fun j =>
    Fin.append_right _ _ j
  refine ⟨fun i => ?_, fun i k hik => ?_⟩
  · induction i using Fin.addCases with
    | left i => rw [el]; exact ha.1 i
    | right j => rw [er]; exact hb.1 j
  · induction i using Fin.addCases with
    | left i =>
      induction k using Fin.addCases with
      | left k =>
        rw [el, el]
        exact ha.2 i k fun e => hik (by rw [e])
      | right k =>
        rw [el, er]
        exact le_setDist_iff.mpr (hf i k)
    | right i =>
      induction k using Fin.addCases with
      | left k =>
        rw [er, el]
        refine le_setDist_iff.mpr fun u hu v hv => ?_
        rw [euclidNorm_sub_comm]
        exact hf k i v hv u hu
      | right k =>
        rw [er, er]
        exact hb.2 i k fun e => hik (by rw [e])
theorem cardBound_coe (bound : ℕ+ → ℝ → ℝ → ℝ≥0) (k : ℕ+) (d R : ℝ) :
    cardBound bound k d R = bound k d R := by
  obtain ⟨n, hn⟩ := k
  cases n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ n => rfl
theorem sharpNormProd_of_len_zero {X : PosSymbol D} (h : X.1.1 = 0) :
    sharpNormProd X = 1 := by
  have : IsEmpty (Fin X.1.1) := by rw [h]; infer_instance
  simp [sharpNormProd]
theorem timeReflectMotion_symm_apply (x : Fin 4 → ℝ) :
    isEuclideanMotion_timeReflect.toPerm.symm x = timeReflect x :=
  (Equiv.symm_apply_eq _).mpr (timeReflect_timeReflect x).symm
theorem timeReflect_last (x : Fin 4 → ℝ) : timeReflect x 3 = -x 3 := by
  rw [timeReflect_apply]
  rfl
theorem abs_reflectAppend_posTimeShift_le (hI : MotionFacts.MotionInvariance D)
    {m : SpaceTimeSymbol D → ℝ} {bound : ℕ+ → ℝ → ℝ → ℝ≥0} (h₁ : IsNormedSymmMultilinear m)
    (h₂ : IsScaleBounded m bound) {δ d₀ R₀ : ℝ} (hd₀ : 0 < d₀) (hd₀δ : d₀ ≤ 2 * δ) (hR₀ : 0 < R₀)
    (X Y : PosSymbol D) (hX : ∀ i, entrySupp D (X.1.2 i) ⊆ {x | δ ≤ x 3})
    (hY : ∀ i, entrySupp D (Y.1.2 i) ⊆ {x | δ ≤ x 3})
    (hXs : X.1 ∈ scaledSymbols D d₀ R₀ hd₀ hR₀) (hYs : Y.1 ∈ scaledSymbols D d₀ R₀ hd₀ hR₀)
    (t : ℝ≥0) :
    ENNReal.ofReal |m (reflectAppend X (posTimeShift t Y))| ≤
      (cardBound bound (X.1.1 + Y.1.1) d₀ R₀ : ℝ≥0∞) *
        (sharpNormProd X * sharpNormProd Y) := by
  by_cases hn : X.1.1 + Y.1.1 = 0
  · have e : reflectAppend X (posTimeShift t Y) = unitSymbol D :=
      Subtype.ext ((fst_eq_zero_iff _).mp hn)
    have hx : X.1.1 = 0 := by omega
    have hy : Y.1.1 = 0 := by omega
    rw [e, h₁.unit_eq_one, hn, sharpNormProd_of_len_zero hx, sharpNormProd_of_len_zero hy]
    simp [cardBound]
  let k : ℕ+ := ⟨X.1.1 + Y.1.1, Nat.pos_of_ne_zero hn⟩
  let Z := reflectAppend X (posTimeShift t Y)
  let f : Fin k → RealFun (Fin 4 → ℝ) := Z.1.2
  have hZ : (⟨k, f⟩ : FnTuple) ∈ scaledSymbols D d₀ R₀ hd₀ hR₀ := by
    have a₁ : IsScaled D d₀ R₀ (reflectSymbol (posToSymbol X)).1 :=
      isScaled_actAny isEuclideanMotion_timeReflect (t := (posToSymbol X).1) (isScaled_of_mem hXs)
    have a₂ : IsScaled D d₀ R₀ (posToSymbol (posTimeShift t Y)).1 :=
      isScaled_actAny (isEuclideanMotion_translationEquiv ((t : ℝ) • timeAxisVec))
        (t := (posToSymbol Y).1) (isScaled_of_mem hYs)
    refine mem_scaledSymbols_of_isScaled Z.2 (isScaled_tupleAppend a₁ a₂ fun i j u hu v hv => ?_)
    have hu' := entrySupp_actAny (D := D) isEuclideanMotion_timeReflect X.1 i
    have hv' := entrySupp_actAny (D := D)
      (isEuclideanMotion_translationEquiv ((t : ℝ) • timeAxisVec)) Y.1 j
    have hu₁ : u ∈ isEuclideanMotion_timeReflect.toPerm.symm ⁻¹' entrySupp D (X.1.2 i) := by
      rw [← hu']
      exact hu
    have hv₁ : v ∈ (isEuclideanMotion_translationEquiv ((t : ℝ) • timeAxisVec)).toPerm.symm ⁻¹'
        entrySupp D (Y.1.2 j) := by
      rw [← hv']
      exact hv
    rw [Set.mem_preimage, timeReflectMotion_symm_apply] at hu₁
    rw [Set.mem_preimage, translationMotion_symm_apply] at hv₁
    have b₁ : δ ≤ timeReflect u 3 := hX i hu₁
    have b₂ : δ ≤ (v - (t : ℝ) • timeAxisVec) 3 := hY j hv₁
    rw [timeReflect_last] at b₁
    have e₃ : timeAxisVec 3 = 1 := by simp [PeriodicLattice.coordVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e₃, mul_one] at b₂
    have ht : (0 : ℝ) ≤ t := t.2
    have h₃ := abs_last_le_euclidNorm (u - v)
    have h₄ : 2 * δ ≤ |(u - v) 3| := by
      refine le_trans ?_ (neg_le_abs _)
      simp only [Pi.sub_apply]
      linarith
    exact ENNReal.ofReal_le_ofReal (hd₀δ.trans (h₄.trans h₃))
  have hb := h₂ k d₀ R₀ hd₀ hR₀ f hZ
  have e₁ : m (reflectAppend X (posTimeShift t Y)) =
      m ⟨⟨k, f⟩, admissibleSepTuples_subset D hd₀ hR₀ hZ⟩ := rfl
  rw [e₁, show X.1.1 + Y.1.1 = (k : ℕ) from rfl, cardBound_coe]
  refine hb.trans (mul_le_mul_right (le_of_eq ?_) _)
  show ∏ i : Fin (X.1.1 + Y.1.1), _ = _
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have e : f (Fin.castAdd _ i) = (reflectSymbol (posToSymbol X)).1.2 i := Fin.append_left _ _ i
    rw [e]
    exact ennSharpNorm_motionSymbol_fn hI _ (posToSymbol X) i
  · refine Finset.prod_congr rfl fun j _ => ?_
    have e : f (Fin.natAdd _ j) = (posToSymbol (posTimeShift t Y)).1.2 j :=
      Fin.append_right _ _ j
    rw [e]
    exact ennSharpNorm_motionSymbol_fn hI _ (posToSymbol Y) j
theorem semigroupMap_linComb (m : SpaceTimeSymbol D → ℝ) (t : ℝ≥0) {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (X : ι → PosSymbol D) :
    (osPreHilbertData m).semigroupMap t (linComb c X) =
      linComb c fun p => posTimeShift t (X p) :=
  linExtend_linComb _ c X
theorem translationMap_linComb (m : SpaceTimeSymbol D → ℝ) (a : EuclideanBorel.Space 3)
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (X : ι → PosSymbol D) :
    (osPreHilbertData m).translationMap a (linComb c X) =
      linComb c fun p => posSpaceShift a.ofLp (X p) :=
  linExtend_linComb _ c X
theorem supBound (hI : MotionFacts.MotionInvariance D) {m : SpaceTimeSymbol D → ℝ}
    {bound : ℕ+ → ℝ → ℝ → ℝ≥0} (h₁ : IsNormedSymmMultilinear m)
    (h₂ : IsScaleBounded m bound) : SupBound m bound := by
  intro n c X δ d₀ R₀ _ hd₀ hd₀δ hR₀ hsupp hscale
  refine iSup_le fun t => ?_
  rw [semigroupMap_linComb, osForm_linComb]
  calc ENNReal.ofReal ‖∑ p, ∑ r, conj (c p) * c r *
        ((m (reflectAppend (X p) (posTimeShift t (X r))) : ℝ) : ℂ)‖
      ≤ ENNReal.ofReal (∑ p, ∑ r, ‖conj (c p) * c r *
          ((m (reflectAppend (X p) (posTimeShift t (X r))) : ℝ) : ℂ)‖) := by
        refine ENNReal.ofReal_le_ofReal ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun p _ => norm_sum_le _ _))
    _ = ∑ p, ∑ r, ENNReal.ofReal ‖conj (c p) * c r *
          ((m (reflectAppend (X p) (posTimeShift t (X r))) : ℝ) : ℂ)‖ := by
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _]
        exact Finset.sum_congr rfl fun p _ =>
          ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _
    _ ≤ _ := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun r _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (norm_nonneg _)]
        have hb := abs_reflectAppend_posTimeShift_le hI h₁ h₂ hd₀ hd₀δ hR₀ (X p) (X r)
          (hsupp p) (hsupp r) (hscale p) (hscale r) t
        calc _ ≤ ENNReal.ofReal ‖c p‖ * ENNReal.ofReal ‖c r‖ *
              ((cardBound bound ((X p).1.1 + (X r).1.1) d₀ R₀ : ℝ≥0∞) *
                (sharpNormProd (X p) * sharpNormProd (X r))) :=
              mul_le_mul_right hb _
          _ = _ := by ring
theorem exists_eq_linComb_fin (F : PosSymbolSpan D) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (X : Fin n → PosSymbol D), F = linComb c X := by
  obtain ⟨ι, _, c, X, rfl⟩ := exists_eq_linComb F
  refine ⟨_, fun i => c ((Fintype.equivFin ι).symm i), fun i => X ((Fintype.equivFin ι).symm i), ?_⟩
  simp only [linComb]
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm fun p => c p • basisVec (X p)).symm
theorem exists_time_gap_and_scale (hS : SupportFacts.AllSupportFacts)
    {n : ℕ} (X : Fin n → PosSymbol D) :
    ∃ (δ d₀ R₀ : ℝ) (_ : 0 < δ) (hd₀ : 0 < d₀) (_ : d₀ ≤ 2 * δ) (hR₀ : 0 < R₀),
      (∀ p i, entrySupp D ((X p).1.2 i) ⊆ {x | δ ≤ x 3}) ∧
      ∀ p, (X p).1 ∈ scaledSymbols D d₀ R₀ hd₀ hR₀ := by
  have hpos : ∀ p i, entrySupp D ((X p).1.2 i) ⊆ posTimeHalf :=
    fun p => ((mem_posSymbols_iff D _).mp (X p).2).2
  have hsym : ∀ p, (X p).1 ∈ spaceTimeSymbols D := fun p =>
    ((mem_posSymbols_iff D _).mp (X p).2).1
  have hcomp : ∀ p i, IsCompact (entrySupp D ((X p).1.2 i)) := fun p i =>
    (fn_mem_c1SupportedIn ⟨_, hsym p⟩ i).2.1
  have hdisj : ∀ p, Pairwise fun i k => Disjoint (entrySupp D ((X p).1.2 i))
      (entrySupp D ((X p).1.2 k)) := fun p =>
    ((mem_sepTuples_iff D _ _).mp (hsym p)).2.2.1
  have h₁ : ∀ q : Σ p, Fin (X p).1.1, ∃ e : ℝ, 0 < e ∧
      entrySupp D ((X q.1).1.2 q.2) ⊆ {x | e ≤ x 3} := by
    rintro ⟨p, i⟩
    rcases (entrySupp D ((X p).1.2 i)).eq_empty_or_nonempty with he | he
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨z, hz, hmin⟩ := (hcomp p i).exists_isMinOn he
        (continuous_apply (3 : Fin 4)).continuousOn
      exact ⟨z 3, hpos p i hz, fun x hx => hmin hx⟩
  choose e he he' using h₁
  obtain ⟨δ, hδ, hδe⟩ := exists_pos_ofReal_le (a := fun q => ENNReal.ofReal (e q))
    fun q => ENNReal.ofReal_pos.mpr (he q)
  have hδe' : ∀ q, δ ≤ e q := fun q => (ENNReal.ofReal_le_ofReal_iff (he q).le).mp (hδe q)
  obtain ⟨ε, hε, hεd⟩ := exists_pos_ofReal_le
    (ι := Σ p, {ij : Fin (X p).1.1 × Fin (X p).1.1 // ij.1 ≠ ij.2})
    (a := fun q => Domain.euclidean.setDist D (entrySupp D ((X q.1).1.2 q.2.1.1))
      (entrySupp D ((X q.1).1.2 q.2.1.2)))
    fun q => (hS D).2.2.2.2.2.2.2.1 _ _ (hcomp _ _) (hcomp _ _) (hdisj q.1 q.2.2)
  have h₂ : ∀ q : Σ p, Fin (X p).1.1, ∃ C : ℝ, ∀ x ∈ entrySupp D ((X q.1).1.2 q.2),
      euclidNorm x ≤ C := by
    rintro ⟨p, i⟩
    obtain ⟨C, hC⟩ := (hcomp p i).exists_bound_of_continuousOn continuous_euclidNorm.continuousOn
    exact ⟨C, fun x hx => (le_abs_self _).trans (hC x hx)⟩
  choose C hC using h₂
  set B : ℝ := (∑ q, max (C q) 0) + 1 with hB
  have hB₀ : 0 < B := by
    have : 0 ≤ ∑ q, max (C q) 0 := Finset.sum_nonneg fun _ _ => le_max_right _ _
    linarith
  have hCB : ∀ q, C q ≤ B := fun q => by
    have h₃ := (le_max_left (C q) 0).trans (Finset.single_le_sum (f := fun q => max (C q) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_univ q))
    linarith
  have hd₀ : 0 < min ε (2 * δ) := lt_min hε (by positivity)
  refine ⟨δ, min ε (2 * δ), B, hδ, hd₀, min_le_right _ _, hB₀, fun p i => ?_, fun p => ?_⟩
  · exact fun x hx => (hδe' ⟨p, i⟩).trans (he' ⟨p, i⟩ hx)
  · refine mem_scaledSymbols_of_isScaled (hsym p) ⟨fun i => ⟨0, fun y hy => ?_⟩, fun i k hik => ?_⟩
    · show euclidNorm (y - 0) ≤ B
      rw [sub_zero]
      exact (hC ⟨p, i⟩ y hy).trans (hCB _)
    · exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (hεd ⟨p, ⟨(i, k), hik⟩⟩)
theorem osSemigroup_bddAbove (hS : SupportFacts.AllSupportFacts)
    (hI : MotionFacts.MotionInvariance D) {m : SpaceTimeSymbol D → ℝ}
    {bound : ℕ+ → ℝ → ℝ → ℝ≥0} (h₁ : IsNormedSymmMultilinear m)
    (h₂ : IsScaleBounded m bound) (F : PosSymbolSpan D) :
    BddAbove (Set.range fun t => ‖osForm m F ((osPreHilbertData m).semigroupMap t F)‖) := by
  obtain ⟨n, c, X, rfl⟩ := exists_eq_linComb_fin F
  obtain ⟨δ, d₀, R₀, hδ, hd₀, hd₀δ, hR₀, hsupp, hscale⟩ := exists_time_gap_and_scale hS X
  have hs := supBound hI h₁ h₂ n c X δ d₀ R₀ hδ hd₀ hd₀δ hR₀ hsupp hscale
  have hsym : ∀ p, (X p).1 ∈ spaceTimeSymbols D := fun p =>
    ((mem_posSymbols_iff D _).mp (X p).2).1
  have hP : ∀ p, sharpNormProd (X p) < ∞ := fun p =>
    ENNReal.prod_lt_top fun i _ => ennSharpNorm_lt_top (fn_mem_c1SupportedIn ⟨_, hsym p⟩ i)
  have hfin : (∑ p, ∑ r, ENNReal.ofReal ‖c p‖ * ENNReal.ofReal ‖c r‖ *
      (cardBound bound ((X p).1.1 + (X r).1.1) d₀ R₀ : ℝ≥0∞) *
      sharpNormProd (X p) * sharpNormProd (X r)) ≠ ∞ := by
    refine (ENNReal.sum_lt_top.mpr fun p _ => ENNReal.sum_lt_top.mpr fun r _ => ?_).ne
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) ENNReal.coe_lt_top) (hP p)) (hP r)
  refine ⟨(∑ p, ∑ r, ENNReal.ofReal ‖c p‖ * ENNReal.ofReal ‖c r‖ *
      (cardBound bound ((X p).1.1 + (X r).1.1) d₀ R₀ : ℝ≥0∞) *
      sharpNormProd (X p) * sharpNormProd (X r)).toReal, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp ((le_iSup (fun t : ℝ≥0 => ENNReal.ofReal
    ‖osForm m (linComb c X) ((osPreHilbertData m).semigroupMap t (linComb c X))‖) t).trans hs)
theorem tendsto_reflectAppend {m : SpaceTimeSymbol D → ℝ} (hc : ContinuousInShift m) {α : Type*}
    {l : Filter α} {v : α → Fin 4 → ℝ} (hv : Tendsto v l (𝓝 0)) (X Y : PosSymbol D)
    {Z : α → PosSymbol D}
    (hZ : ∀ a, posToSymbol (Z a) = translateSymbol (v a) (posToSymbol Y)) :
    Tendsto (fun a => m (reflectAppend X (Z a))) l (𝓝 (m (reflectAppend X Y))) := by
  have e₀ : translateSymbol 0 (posToSymbol Y) = posToSymbol Y :=
    Subtype.ext (actAny_of_eq_id _ translationEquiv_zero_apply_eq _)
  have h₀ : AppendDefined D (reflectSymbol (posToSymbol X)).1
      (translateSymbol 0 (posToSymbol Y)).1 := by
    rw [e₀]
    exact appendDefined_reflect X Y
  obtain ⟨-, h⟩ := hc (reflectSymbol (posToSymbol X)) (posToSymbol Y) 0 h₀
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  filter_upwards [hv.eventually (h ε hε)] with a ha
  obtain ⟨h', hlt⟩ := ha
  have a₁ : sepAppend (reflectSymbol (posToSymbol X))
      (translateSymbol (v a) (posToSymbol Y)) h' = reflectAppend X (Z a) :=
    sepAppend_congr rfl (hZ a).symm _ _
  have a₂ : sepAppend (reflectSymbol (posToSymbol X))
      (translateSymbol 0 (posToSymbol Y)) h₀ = reflectAppend X Y :=
    sepAppend_congr rfl e₀ _ _
  rw [a₁, a₂] at hlt
  exact hlt
theorem osSemigroup_tendsto {m : SpaceTimeSymbol D → ℝ} (hc : ContinuousInShift m)
    (F : PosSymbolSpan D) :
    Tendsto (fun t => osForm m F ((osPreHilbertData m).semigroupMap t F)) (𝓝[>] 0)
      (𝓝 (osForm m F F)) := by
  obtain ⟨ι, _, c, X, rfl⟩ := exists_eq_linComb F
  simp only [semigroupMap_linComb, osForm_linComb]
  have hv : Tendsto (fun t : ℝ≥0 => (t : ℝ) • timeAxisVec) (𝓝[>] 0) (𝓝 0) := by
    have h : Continuous fun t : ℝ≥0 => (t : ℝ) • timeAxisVec := by fun_prop
    have h₀ := h.tendsto 0
    simp only [NNReal.coe_zero, zero_smul] at h₀
    exact h₀.mono_left nhdsWithin_le_nhds
  refine tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun r _ => Tendsto.const_mul _ ?_
  exact (Complex.continuous_ofReal.tendsto _).comp
    (tendsto_reflectAppend hc hv (X p) (X r) fun t => posToSymbol_posTimeShift t (X r))
theorem osTranslation_tendsto {m : SpaceTimeSymbol D → ℝ} (hc : ContinuousInShift m)
    (F : PosSymbolSpan D) :
    Tendsto (fun a => osForm m F ((osPreHilbertData m).translationMap a F)) (𝓝 0)
      (𝓝 (osForm m F F)) := by
  obtain ⟨ι, _, c, X, rfl⟩ := exists_eq_linComb F
  simp only [translationMap_linComb, osForm_linComb]
  have hv : Tendsto (fun a : EuclideanBorel.Space 3 => spaceTimePoint a.ofLp 0) (𝓝 0) (𝓝 0) := by
    have h : Continuous fun a : EuclideanBorel.Space 3 => spaceTimePoint a.ofLp 0 := by
      refine continuous_pi fun ν => ?_
      induction ν using Fin.lastCases with
      | last =>
        have e : (fun a : EuclideanBorel.Space 3 => spaceTimePoint a.ofLp 0 (Fin.last 3)) =
            fun _ => 0 :=
          funext fun a => spaceTimePoint_last _ _
        rw [e]
        exact continuous_const
      | cast j =>
        have e : (fun a : EuclideanBorel.Space 3 => spaceTimePoint a.ofLp 0 j.castSucc) =
            fun a => a.ofLp j :=
          funext fun a => spaceTimePoint_castSucc _ _ _
        rw [e]
        fun_prop
    have h₀ := h.tendsto 0
    have e₀ : spaceTimePoint (0 : EuclideanBorel.Space 3).ofLp 0 = 0 := spaceTimePoint_zero_zero
    rwa [e₀] at h₀
  refine tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun r _ => Tendsto.const_mul _ ?_
  exact (Complex.continuous_ofReal.tendsto _).comp
    (tendsto_reflectAppend hc hv (X p) (X r) fun a => posToSymbol_posSpaceShift a.ofLp (X r))
theorem osForm_unitVec {m : SpaceTimeSymbol D → ℝ} (h₁ : IsNormedSymmMultilinear m) :
    osForm m (osPreHilbertData m).unitVec (osPreHilbertData m).unitVec = 1 := by
  show osForm m (basisVec posUnitSymbol) (basisVec posUnitSymbol) = 1
  rw [osForm_basisVec]
  have e : reflectAppend (D := D) posUnitSymbol posUnitSymbol = unitSymbol D :=
    Subtype.ext ((fst_eq_zero_iff _).mp rfl)
  rw [e, h₁.unit_eq_one]
  simp
theorem posMotion_posUnitSymbol {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s)
    (hp : Set.MapsTo s posTimeHalf posTimeHalf) :
    posMotion hs hp (posUnitSymbol (D := D)) = posUnitSymbol :=
  Subtype.ext (actAny_nilTuple hs)
theorem osPreHilbertData_isAdmissible (hS : SupportFacts.AllSupportFacts)
    (hI : MotionFacts.MotionInvariance D)
    (hC : StabilizerAction.CommRelations)
    (hAct : StabilizerAction.MotionsOnSymbols D)
    {m : SpaceTimeSymbol D → ℝ} {bound : ℕ+ → ℝ → ℝ → ℝ≥0} (h₁ : IsNormedSymmMultilinear m)
    (h₂ : IsScaleBounded m bound) (hc : ContinuousInShift m)
    (h₃ : IsMotionInvariant m) (h₄ : IsReflPositive m) :
    (osPreHilbertData m).IsAdmissible where
  hermitian := isHermitianForm_osForm hAct h₁ h₃
  posSemidef := isPosSemidefForm_osForm h₄
  form_unitVec := osForm_unitVec h₁
  semigroupMap_zero := osSemigroup_zero m
  translationMap_zero := osTranslation_zero m
  rotationMap_one := osRotation_one m
  semigroupMap_comp := osSemigroup_comp m
  translationMap_comp := osTranslation_comp m
  rotationMap_comp := osRotation_comp m
  translationMap_comm := osTranslation_comm m
  rotationMap_comm := osRotation_comm hC
  rotationMap_translationMap := osRotation_translation hC
  semigroupMap_unitVec t :=
    (semigroupMap_basisVec m t _).trans (congrArg TorusTransport.TupleVectors.basisVec (posMotion_posUnitSymbol _ _))
  translationMap_unitVec a :=
    (translationMap_basisVec m a _).trans (congrArg TorusTransport.TupleVectors.basisVec (posMotion_posUnitSymbol _ _))
  rotationMap_unitVec w :=
    (rotationMap_basisVec m w _).trans (congrArg TorusTransport.TupleVectors.basisVec (posMotion_posUnitSymbol _ _))
  form_semigroupMap := osForm_semigroup hC hAct h₃
  form_translationMap := osForm_translation hC hAct h₃
  form_rotationMap := osForm_rotation hC hAct h₃
  bddAbove_semigroup := osSemigroup_bddAbove hS hI h₁ h₂
  tendsto_semigroup := osSemigroup_tendsto hc
  tendsto_translation := osTranslation_tendsto hc
theorem euclidean_quotDist_eq (E : PeriodicSpace.Params) (y y' : Fin 4 → ℝ) :
    PeriodicSpace.Kind.quotDist E .euclidean y y' = TorusMetric.euclidNormVec (y - y') := by apply _root_.YangMills.Construction.PeriodicSpace.QuotientGeometry.quotDist_euclidean <;> assumption
theorem euclidean_supportQ_eq (E : PeriodicSpace.Params) (g : RealFun (Fin 4 → ℝ)) :
    PeriodicSpace.Kind.supportQ E .euclidean g = tsupport g :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure (euclidean_quotDist_eq E) _
theorem mem_euclidean_sepC1Tuples_iff (E : PeriodicSpace.Params) {n : ℕ}
    (g : Fin n → RealFun (Fin 4 → ℝ)) :
    g ∈ PeriodicSpace.Kind.sepC1Tuples E .euclidean n ↔
      (∀ i, IsC1R4 (g i)) ∧ (∀ i, IsCompact (tsupport (g i))) ∧
        ∀ i k, i ≠ k → Disjoint (tsupport (g i)) (tsupport (g k)) := by
  have hs := euclidean_supportQ_eq E
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, fun i => ?_, fun i k hik => ?_⟩
    · have h := h₂ i
      have e := hs (g i)
      exact (SeparatedTuplesR4.isCompactWrt_euclid_iff (euclidean_quotDist_eq E) _).mp
        (e ▸ h)
    · have h := h₃ i k hik
      have e := hs (g i)
      have e' := hs (g k)
      exact e ▸ e' ▸ h
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, fun i => ?_, fun i k hik => ?_⟩
    · have e := hs (g i)
      exact e.symm ▸ (SeparatedTuplesR4.isCompactWrt_euclid_iff (euclidean_quotDist_eq E) _).mpr
        (h₂ i)
    · have e := hs (g i)
      have e' := hs (g k)
      exact e.symm ▸ e'.symm ▸ h₃ i k hik
theorem euclidean_sharpNormQ_eq {g : RealFun (Fin 4 → ℝ)}
    (hl : Domain.euclidean.LipschitzOn D g) :
    PeriodicSpace.Kind.sharpNormQ (euclideanParams D) .euclidean g =
      Domain.euclidean.ennSharpNorm D g := by
  have e : TestFunctions.bestLipschitzConstant
      (fun y y' : Fin 4 → ℝ => PeriodicSpace.Kind.quotDist (euclideanParams D) .euclidean y y') g =
      TestFunctions.bestLipschitzConstant
        (fun y y' : Fin 4 → ℝ => Domain.euclidean.pointDist D y y') g :=
    congrArg (fun d => TestFunctions.bestLipschitzConstant d g)
      (funext₂ fun y y' => euclidean_quotDist_eq _ y y')
  have hM : (0 : ℝ) ≤ 40 * D.M := by linarith [D.one_le_M]
  have h₃ : ENNReal.ofReal (40 * D.M * TestFunctions.bestLipschitzConstant
      (fun y y' : Fin 4 → ℝ => PeriodicSpace.Kind.quotDist (euclideanParams D) .euclidean y y') g) =
      ENNReal.ofReal (40 * D.M) * Domain.euclidean.lipConst D g := by
    rw [ENNReal.ofReal_mul hM, e]
    exact congrArg _ (Domain.ofReal_bestLipschitzConstant_eq_lipConst D Domain.euclidean hl)
  exact congrArg (max (⨆ y, ENNReal.ofReal |g y|)) h₃
theorem ennSharpNorm_add_le (a b : RealFun (Fin 4 → ℝ)) :
    Domain.euclidean.ennSharpNorm D (a + b) ≤
      Domain.euclidean.ennSharpNorm D a + Domain.euclidean.ennSharpNorm D b := by
  have h₁ : ennSupNorm (a + b) ≤ ennSupNorm a + ennSupNorm b := by
    refine iSup_le fun u => ?_
    refine (ENNReal.ofReal_le_ofReal (norm_add_le (a u) (b u))).trans
      (ENNReal.ofReal_add_le.trans (add_le_add ?_ ?_))
    · exact le_iSup (fun u => ENNReal.ofReal ‖a u‖) u
    · exact le_iSup (fun u => ENNReal.ofReal ‖b u‖) u
  have h₂ : Domain.euclidean.lipConst D (a + b) ≤
      Domain.euclidean.lipConst D a + Domain.euclidean.lipConst D b := by
    refine iSup_le fun u => iSup_le fun v => iSup_le fun huv => ?_
    have hd : 0 ≤ Domain.euclidean.pointDist D u v := (Domain.euclidean.pointDist_pos D huv).le
    have h₃ : ‖(a + b) u - (a + b) v‖ / Domain.euclidean.pointDist D u v ≤
        ‖a u - a v‖ / Domain.euclidean.pointDist D u v +
          ‖b u - b v‖ / Domain.euclidean.pointDist D u v := by
      rw [← add_div]
      refine div_le_div_of_nonneg_right ?_ hd
      have e : (a + b) u - (a + b) v = (a u - a v) + (b u - b v) := by
        simp only [Pi.add_apply]
        ring
      rw [e]
      exact norm_add_le _ _
    refine (ENNReal.ofReal_le_ofReal h₃).trans (ENNReal.ofReal_add_le.trans (add_le_add ?_ ?_))
    · exact le_iSup₂_of_le u v (le_iSup (fun _ : u ≠ v => ENNReal.ofReal
        (‖a u - a v‖ / Domain.euclidean.pointDist D u v)) huv)
    · exact le_iSup₂_of_le u v (le_iSup (fun _ : u ≠ v => ENNReal.ofReal
        (‖b u - b v‖ / Domain.euclidean.pointDist D u v)) huv)
  refine max_le (h₁.trans (add_le_add (le_max_left _ _) (le_max_left _ _))) ?_
  refine (mul_le_mul_right h₂ _).trans ?_
  rw [mul_add]
  exact add_le_add (le_max_right _ _) (le_max_right _ _)
def doublePNat (k : ℕ+) : ℕ+ := ⟨(k : ℕ) + k, by positivity⟩
theorem isAdmissibleSets_reflect_append (hI : MotionFacts.MotionInvariance D) {k : ℕ+} {η R : ℝ}
    {hη : 0 < η} {hR : 0 < R} {T : Fin k → Set (Fin 4 → ℝ)}
    (hT : IsAdmissibleSets D η R hη hR T) (hpos : ∀ i, ∀ x ∈ T i, η / 2 ≤ x 3) :
    IsAdmissibleSets D η R hη hR (q := doublePNat k)
      (Fin.append (fun i => timeReflect ⁻¹' T i) T : Fin ((k : ℕ) + k) → Set (Fin 4 → ℝ)) := by
  have hθ := ((hI timeReflect isEuclideanMotion_timeReflect).2.1 k η R hη hR T hT).1
  let A : Fin ((k : ℕ) + k) → Set (Fin 4 → ℝ) := Fin.append (fun i => timeReflect ⁻¹' T i) T
  have el : ∀ i, A (Fin.castAdd _ i) = timeReflect ⁻¹' T i := fun i => Fin.append_left _ _ i
  have er : ∀ j, A (Fin.natAdd _ j) = T j := fun j => Fin.append_right _ _ j
  have hball : ∀ l : Fin ((k : ℕ) + k), ∃ x, A l ⊆ ballR4 x R := by
    intro l
    induction l using Fin.addCases with
    | left i => rw [el]; exact hθ.1 i
    | right j => rw [er]; exact hT.1 j
  have hcross : ∀ i j, ENNReal.ofReal η ≤
      Domain.euclidean.setDist D (timeReflect ⁻¹' T i) (T j) := fun i j => by
    refine le_setDist_iff.mpr fun u hu v hv => ENNReal.ofReal_le_ofReal ?_
    have b₁ := hpos i _ hu
    have b₂ := hpos j _ hv
    rw [timeReflect_last] at b₁
    refine le_trans ?_ (abs_last_le_euclidNorm (u - v))
    refine le_trans ?_ (neg_le_abs _)
    simp only [Pi.sub_apply]
    linarith
  have hdist : ∀ l j : Fin ((k : ℕ) + k), l ≠ j → ENNReal.ofReal η ≤
      Domain.euclidean.setDist D (A l) (A j) := by
    intro l j hlj
    induction l using Fin.addCases with
    | left l =>
      induction j using Fin.addCases with
      | left j =>
        rw [el, el]
        exact hθ.2 l j fun e => hlj (by rw [e])
      | right j =>
        rw [el, er]
        exact hcross l j
    | right l =>
      induction j using Fin.addCases with
      | left j =>
        rw [er, el]
        refine le_setDist_iff.mpr fun u hu v hv => ?_
        rw [euclidNorm_sub_comm]
        exact le_setDist_iff.mp (hcross j l) v hv u hu
      | right j =>
        rw [er, er]
        exact hT.2 l j fun e => hlj (by rw [e])
  exact ⟨hball, hdist⟩
theorem comp_timeReflect_mem {a : RealFun (Fin 4 → ℝ)} {B : Set (Fin 4 → ℝ)}
    (ha : a ∈ c1SupportedIn B) : a ∘ timeReflect ∈ c1SupportedIn (timeReflect ⁻¹' B) := by
  have e : tsupport (a ∘ timeReflect) = timeReflect ⁻¹' tsupport a :=
    tsupport_comp_eq_preimage a (motionHomeomorph isEuclideanMotion_timeReflect)
  refine ⟨(show ContDiff ℝ 1 a from ha.1).comp
    (contDiff_of_isEuclideanMotion isEuclideanMotion_timeReflect), ?_, ?_⟩
  · rw [e]
    exact (motionHomeomorph isEuclideanMotion_timeReflect).isCompact_preimage.mpr ha.2.1
  · rw [e]
    exact Set.preimage_mono ha.2.2
def mkPosSymbol {k : ℕ} (f : Fin k → RealFun (Fin 4 → ℝ))
    (hf : (⟨k, f⟩ : FnTuple) ∈ posSymbols D) : PosSymbol D := ⟨⟨k, f⟩, hf⟩
theorem reflectAppend_fn_mem {k : ℕ} {T : Fin k → Set (Fin 4 → ℝ)}
    {u v : Fin k → RealFun (Fin 4 → ℝ)} (hu : (⟨k, u⟩ : FnTuple) ∈ posSymbols D)
    (hv : (⟨k, v⟩ : FnTuple) ∈ posSymbols D) (hu' : ∀ i, u i ∈ c1SupportedIn (T i))
    (hv' : ∀ i, v i ∈ c1SupportedIn (T i)) (l : Fin (k + k)) :
    (reflectAppend (mkPosSymbol u hu) (mkPosSymbol v hv)).1.2 l ∈
      c1SupportedIn
        ((Fin.append (fun i => timeReflect ⁻¹' T i) T : Fin (k + k) → Set (Fin 4 → ℝ)) l) := by
  induction l using Fin.addCases with
  | left i =>
    rw [Fin.append_left]
    have e : (reflectAppend (mkPosSymbol u hu) (mkPosSymbol v hv)).1.2 (Fin.castAdd _ i) =
        u i ∘ timeReflect :=
      (Fin.append_left _ _ i).trans (reflectSymbol_fn (posToSymbol (mkPosSymbol u hu)) i)
    exact Eq.mpr (congrArg (fun h => h ∈ c1SupportedIn (timeReflect ⁻¹' T i)) e)
      (comp_timeReflect_mem (hu' i))
  | right j =>
    rw [Fin.append_right]
    have e : (reflectAppend (mkPosSymbol u hu) (mkPosSymbol v hv)).1.2 (Fin.natAdd _ j) =
        v j := Fin.append_right _ _ j
    exact Eq.mpr (congrArg (fun h => h ∈ c1SupportedIn (T j)) e) (hv' j)
theorem abs_reflectAppend_sub_le (hS : SupportFacts.AllSupportFacts)
    (hI : MotionFacts.MotionInvariance D) {m : SpaceTimeSymbol D → ℝ}
    {bound : ℕ+ → ℝ → ℝ → ℝ≥0} (h₁ : IsNormedSymmMultilinear m) (h₂ : IsScaleBounded m bound)
    {k : ℕ+} {η R : ℝ} {hη : 0 < η} {hR : 0 < R} {T : Fin k → Set (Fin 4 → ℝ)}
    (hA : IsAdmissibleSets D η R hη hR (q := doublePNat k)
      (Fin.append (fun i => timeReflect ⁻¹' T i) T : Fin ((k : ℕ) + k) → Set (Fin 4 → ℝ)))
    {f u v : Fin k → RealFun (Fin 4 → ℝ)}
    (hf : (⟨k, f⟩ : FnTuple) ∈ posSymbols D) (hu : (⟨k, u⟩ : FnTuple) ∈ posSymbols D)
    (hv : (⟨k, v⟩ : FnTuple) ∈ posSymbols D)
    (hf' : ∀ i, f i ∈ c1SupportedIn (T i))
    (hu' : ∀ i, u i ∈ c1SupportedIn (T i))
    (hv' : ∀ i, v i ∈ c1SupportedIn (T i)) {e : ℝ≥0∞} (he : e ≤ 1)
    (hue : ∀ i, Domain.euclidean.ennSharpNorm D (u i - f i) ≤ e)
    (hve : ∀ i, Domain.euclidean.ennSharpNorm D (v i - f i) ≤ e) :
    ENNReal.ofReal |m (reflectAppend (mkPosSymbol u hu) (mkPosSymbol v hv)) -
        m (reflectAppend (mkPosSymbol f hf) (mkPosSymbol f hf))| ≤
      e * ((bound (doublePNat k) η R : ℝ≥0∞) * ∑ i : Fin (doublePNat k),
        ∏ l ∈ Finset.univ.erase i, (Domain.euclidean.ennSharpNorm D
          ((reflectAppend (mkPosSymbol f hf) (mkPosSymbol f hf)).1.2 l) + 1)) := by
  let Z := reflectAppend (mkPosSymbol u hu) (mkPosSymbol v hv)
  let Z₀ := reflectAppend (mkPosSymbol f hf) (mkPosSymbol f hf)
  let g : Fin (doublePNat k) → RealFun (Fin 4 → ℝ) := Z.1.2
  let g₀ : Fin (doublePNat k) → RealFun (Fin 4 → ℝ) := Z₀.1.2
  have hg := reflectAppend_fn_mem hu hv hu' hv'
  have hg₀ := reflectAppend_fn_mem hf hf hf' hf'
  obtain ⟨hz, hz₀, hb⟩ := lipschitzOnProducts hS h₁ h₂ (doublePNat k) η R hη hR _ hA g g₀ hg hg₀
  refine (show ENNReal.ofReal |m Z - m Z₀| ≤ _ from hb).trans ?_
  have hdiff : ∀ l : Fin ((k : ℕ) + k),
      Domain.euclidean.ennSharpNorm D (g l - g₀ l) ≤ e := by
    intro l
    induction l using Fin.addCases with
    | left i =>
      have e₁ : g (Fin.castAdd _ i) = u i ∘ timeReflect :=
        (Fin.append_left _ _ i).trans (reflectSymbol_fn (posToSymbol (mkPosSymbol u hu)) i)
      have e₂ : g₀ (Fin.castAdd _ i) = f i ∘ timeReflect :=
        (Fin.append_left _ _ i).trans (reflectSymbol_fn (posToSymbol (mkPosSymbol f hf)) i)
      rw [e₁, e₂]
      have e₃ : u i ∘ timeReflect - f i ∘ timeReflect = (u i - f i) ∘ timeReflect := rfl
      rw [e₃, ennSharpNorm_comp_motion hI isEuclideanMotion_timeReflect
        (sub_mem_c1SupportedIn hS D (hu' i) (hf' i))]
      exact hue i
    | right j =>
      have e₁ : g (Fin.natAdd _ j) = v j := Fin.append_right _ _ j
      have e₂ : g₀ (Fin.natAdd _ j) = f j := Fin.append_right _ _ j
      rw [e₁, e₂]
      exact hve j
  have hmax : ∀ l : Fin (doublePNat k), max (Domain.euclidean.ennSharpNorm D (g l))
      (Domain.euclidean.ennSharpNorm D (g₀ l)) ≤
        Domain.euclidean.ennSharpNorm D (g₀ l) + 1 := fun l => by
    refine max_le ?_ le_self_add
    have e₁ : g l = (g l - g₀ l) + g₀ l := (sub_add_cancel _ _).symm
    calc Domain.euclidean.ennSharpNorm D (g l)
        = Domain.euclidean.ennSharpNorm D ((g l - g₀ l) + g₀ l) := by rw [← e₁]
      _ ≤ Domain.euclidean.ennSharpNorm D (g l - g₀ l) +
            Domain.euclidean.ennSharpNorm D (g₀ l) := ennSharpNorm_add_le _ _
      _ ≤ 1 + Domain.euclidean.ennSharpNorm D (g₀ l) :=
          add_le_add ((hdiff l).trans he) le_rfl
      _ = _ := add_comm _ _
  calc (bound (doublePNat k) η R : ℝ≥0∞) * ∑ i : Fin (doublePNat k),
        Domain.euclidean.ennSharpNorm D (g i - g₀ i) * ∏ l ∈ Finset.univ.erase i,
          max (Domain.euclidean.ennSharpNorm D (g l))
            (Domain.euclidean.ennSharpNorm D (g₀ l))
      ≤ (bound (doublePNat k) η R : ℝ≥0∞) * ∑ i : Fin (doublePNat k), e *
          ∏ l ∈ Finset.univ.erase i, (Domain.euclidean.ennSharpNorm D (g₀ l) + 1) := by
        refine mul_le_mul_right (Finset.sum_le_sum fun i _ => ?_) _
        exact mul_le_mul' (hdiff i) (Finset.prod_le_prod' fun l _ => hmax l)
    _ = _ := by
        rw [← Finset.mul_sum, mul_left_comm]
theorem exists_unitOrDense_close (hS : SupportFacts.AllSupportFacts)
    (hI : MotionFacts.MotionInvariance D)
    (hF : PeriodicSpace.EuclideanFamilyForms.Statement) {m : SpaceTimeSymbol D → ℝ}
    {bound : ℕ+ → ℝ → ℝ → ℝ≥0} (h₁ : IsNormedSymmMultilinear m)
    (h₂ : IsScaleBounded m bound) (C : DenseChoice D) (X : PosSymbol D) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Y : PosSymbol D, IsUnitOrDense C Y ∧
      (osForm m (basisVec X - basisVec Y) (basisVec X - basisVec Y)).re < ε := by
  obtain ⟨⟨k₀, f⟩, hX⟩ := X
  by_cases hk : k₀ = 0
  · subst hk
    refine ⟨⟨⟨0, f⟩, hX⟩, Or.inl ((fst_eq_zero_iff _).mp rfl), ?_⟩
    rw [sub_self, sesq_zero_left (isSesquilinear_osForm m)]
    simpa using hε
  have hk₀ : 0 < k₀ := Nat.pos_of_ne_zero hk
  let k : ℕ+ := ⟨k₀, hk₀⟩
  have hsym : (⟨k₀, f⟩ : FnTuple) ∈ spaceTimeSymbols D := ((mem_posSymbols_iff D _).mp hX).1
  have hmem : ∀ i, f i ∈ c1SupportedIn (entrySupp D (f i)) :=
    fn_mem_c1SupportedIn ⟨_, hsym⟩
  have hdisj : Pairwise fun i j => Disjoint (entrySupp D (f i)) (entrySupp D (f j)) :=
    ((mem_sepTuples_iff D _ _).mp hsym).2.2.1
  obtain ⟨δ, -, -, hδ, -, -, -, hsupp, -⟩ :=
    exists_time_gap_and_scale hS (fun _ : Fin 1 => (⟨⟨k₀, f⟩, hX⟩ : PosSymbol D))
  have hδS : ∀ i, ∀ x ∈ entrySupp D (f i), δ ≤ x 3 := fun i x hx => hsupp 0 i hx
  obtain ⟨η, R, hη, hR, hηδ, hA⟩ := exists_isAdmissibleSets_closedNbhd (D := D) hS (k := k)
    (fun i => entrySupp D (f i)) (fun i => (hmem i).2.1) (fun i j hij => hdisj hij)
    (η₀ := δ / 2) (by positivity)
  let T : Fin k → Set (Fin 4 → ℝ) := fun i => closedNbhd (entrySupp D (f i)) η
  let W : Fin k₀ → Set (Fin 4 → ℝ) := fun i =>
    {x | ∃ z ∈ entrySupp D (f i), euclidNorm (x - z) < η}
  have hTt : ∀ i, ∀ x ∈ T i, δ / 4 ≤ x 3 := fun i x hx => by
    obtain ⟨z, hz, h⟩ := exists_close_of_mem_closedNbhd (η' := 3 * δ / 4) (by linarith)
      (by positivity) hx
    have h₃ := (abs_last_le_euclidNorm (x - z)).trans_lt h
    have h₄ := hδS i z hz
    have h₅ := neg_abs_le ((x - z) 3)
    simp only [Pi.sub_apply] at h₅ h₃
    linarith
  have hAA := isAdmissibleSets_reflect_append hI hA fun i x hx =>
    (by linarith : η / 2 ≤ δ / 4).trans (hTt i x hx)
  have hWT : ∀ i, W i ⊆ T i := fun i x ⟨z, hz, h⟩ => mem_closedNbhd_of_close hz h.le
  have hSW : ∀ i, entrySupp D (f i) ⊆ W i := fun i x hx =>
    ⟨x, hx, by simpa [TorusMetric.euclidNormVec] using hη⟩
  have hWo : ∀ i, IsOpen (W i) := fun i => by
    have e : W i = ⋃ z ∈ entrySupp D (f i), {x | euclidNorm (x - z) < η} := by
      ext x
      simp [W]
    rw [e]
    exact isOpen_biUnion fun z _ =>
      isOpen_lt (continuous_euclidNorm.comp (continuous_id.sub continuous_const))
        continuous_const
  let Xf : PosSymbol D := mkPosSymbol f hX
  let K : ℝ≥0∞ := (bound (doublePNat k) η R : ℝ≥0∞) * ∑ i : Fin (doublePNat k),
    ∏ l ∈ Finset.univ.erase i,
      (Domain.euclidean.ennSharpNorm D ((reflectAppend Xf Xf).1.2 l) + 1)
  have hK : K ≠ ∞ := by
    refine (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.sum_lt_top.mpr fun i _ =>
      ENNReal.prod_lt_top fun l _ => ?_)).ne
    exact ENNReal.add_lt_top.mpr
      ⟨ennSharpNorm_lt_top (fn_mem_c1SupportedIn (reflectAppend Xf Xf) l), ENNReal.one_lt_top⟩
  set Kr : ℝ := K.toReal with hKr
  have hKr₀ : 0 ≤ Kr := ENNReal.toReal_nonneg
  set e : ℝ := min 1 (ε / (4 * (Kr + 1))) with he
  have he₀ : 0 < e := lt_min one_pos (by positivity)
  have he₁ : e ≤ 1 := min_le_left _ _
  have heK : 3 * (e * Kr) < ε := by
    have h₃ : e ≤ ε / (4 * (Kr + 1)) := min_le_right _ _
    have h₄ : e * (4 * (Kr + 1)) ≤ ε := (le_div_iff₀ (by positivity)).mp h₃
    nlinarith
  obtain ⟨hEq, -, hApp⟩ := (hF (euclideanParams D)).1 C.dense C.isCountable
  have hfsep : f ∈ PeriodicSpace.Kind.sepC1Tuples (euclideanParams D) .euclidean k₀ :=
    (mem_euclidean_sepC1Tuples_iff _ f).mpr
      ⟨fun i => (hmem i).1, fun i => (hmem i).2.1, fun i j hij => hdisj hij⟩
  obtain ⟨φ, hφ₁, hφ₂, hφ₃, -, hφ₅⟩ := hApp k₀ hk₀ f hfsep W
    (fun i => (SeparatedTuplesR4.isOpenWrt_euclid_iff (euclidean_quotDist_eq _) _).mpr (hWo i))
    (fun i => by
      have e₁ := euclidean_supportQ_eq (euclideanParams D) (f i)
      exact e₁ ▸ hSW i)
  let f₁ : Fin k₀ → PeriodicSpace.Kind.euclidean.Pt (euclideanParams D) → ℝ := f
  have hev : ∀ᶠ l in atTop, ∀ i, PeriodicSpace.Kind.sharpNormQ (euclideanParams D) .euclidean
      (φ l i - f₁ i) < ENNReal.ofReal e :=
    eventually_all.mpr fun i => (hφ₅ i).eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr he₀))
  obtain ⟨l, hl⟩ := hev.exists
  let v : Fin k₀ → RealFun (Fin 4 → ℝ) := φ l
  have hne : ∀ (g : Fin k₀ → RealFun (Fin 4 → ℝ)),
      (⟨k₀, g⟩ : Σ n : ℕ, Fin n → RealFun (Fin 4 → ℝ)) ≠ ⟨0, Fin.elim0⟩ := fun g e₁ =>
    hk (congrArg Sigma.fst e₁)
  have hvsep : v ∈ PeriodicSpace.Kind.sepC1Tuples (euclideanParams D) .euclidean k₀ := by
    rcases hφ₂ l with h | h
    · exact absurd h (hne v)
    · exact h.2.1
  obtain ⟨hv₁, hv₂, hv₃⟩ := (mem_euclidean_sepC1Tuples_iff _ v).mp hvsep
  have hvS : ∀ i, tsupport (v i) ⊆ W i := fun i => by
    have e₁ := euclidean_supportQ_eq (euclideanParams D) (v i)
    exact e₁ ▸ hφ₃ l i
  have hv : (⟨k₀, v⟩ : FnTuple) ∈ posSymbols D :=
    (mem_sepTuples_iff D _ _).mpr ⟨fun i => lipschitzOn_of_isC1On D (hv₁ i) (hv₂ i), hv₂,
      fun i j hij => hv₃ i j hij, hv₁,
      fun i x hx => (by linarith [hTt i x (hWT i (hvS i hx))] : (0 : ℝ) < x 3)⟩
  have hv' : ∀ i, v i ∈ c1SupportedIn (T i) := fun i =>
    ⟨hv₁ i, hv₂ i, (hvS i).trans (hWT i)⟩
  have hf' : ∀ i, f i ∈ c1SupportedIn (T i) := fun i =>
    ⟨(hmem i).1, (hmem i).2.1, (hSW i).trans (hWT i)⟩
  have hve : ∀ i, Domain.euclidean.ennSharpNorm D (v i - f i) ≤ ENNReal.ofReal e := fun i => by
    have hl₁ := lipschitzOn_of_mem_c1SupportedIn (D := D)
      (sub_mem_c1SupportedIn hS D (hv' i) (hf' i))
    rw [← euclidean_sharpNormQ_eq hl₁]
    exact (hl i).le
  have hfe : ∀ i, Domain.euclidean.ennSharpNorm D (f i - f i) ≤ ENNReal.ofReal e := fun i => by
    rw [sub_self, ennSharpNorm_zero]
    exact bot_le
  have he' : ENNReal.ofReal e ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal he₁
  let Y : PosSymbol D := mkPosSymbol v hv
  have near₁ := abs_reflectAppend_sub_le hS hI h₁ h₂ hAA hX hX hv hf' hf' hv' he' hfe hve
  have near₂ := abs_reflectAppend_sub_le hS hI h₁ h₂ hAA hX hv hX hf' hv' hf' he' hve hfe
  have near₃ := abs_reflectAppend_sub_le hS hI h₁ h₂ hAA hX hv hv hf' hv' hv' he' hve hve
  have toR : ∀ a : ℝ, ENNReal.ofReal |a| ≤ ENNReal.ofReal e * K → |a| ≤ e * Kr := fun a h => by
    have e₁ : ENNReal.ofReal e * K = ENNReal.ofReal (e * Kr) := by
      rw [ENNReal.ofReal_mul he₀.le, hKr, ENNReal.ofReal_toReal hK]
    rw [e₁] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have b₁ : |m (reflectAppend Xf Y) - m (reflectAppend Xf Xf)| ≤ e * Kr :=
    toR _ near₁
  have b₂ : |m (reflectAppend Y Xf) - m (reflectAppend Xf Xf)| ≤ e * Kr :=
    toR _ near₂
  have b₃ : |m (reflectAppend Y Y) - m (reflectAppend Xf Xf)| ≤ e * Kr :=
    toR _ near₃
  refine ⟨Y, Or.inr ?_, ?_⟩
  · have h₃ : (⟨k₀, v⟩ : Σ n : ℕ, Fin n → RealFun (Fin 4 → ℝ)) ∈
        PeriodicSpace.Kind.tupleFamily (euclideanParams D) .euclidean C.dense := by
      rcases hφ₁ l with h | h
      · exact absurd h (hne v)
      · exact h
    rw [hEq] at h₃
    exact h₃
  · have e₁ : basisVec (⟨⟨k₀, f⟩, hX⟩ : PosSymbol D) - basisVec Y =
        linComb ![(1 : ℂ), -1] ![Xf, Y] := by
      simp [linComb, Fin.sum_univ_two, sub_eq_add_neg, Xf, mkPosSymbol]
    rw [e₁, osForm_linComb]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [map_one, map_neg, one_mul, mul_one, neg_mul, mul_neg, neg_neg, Complex.add_re,
      Complex.neg_re, Complex.ofReal_re]
    have c₁ := (abs_le.mp b₁).1
    have c₂ := (abs_le.mp b₂).1
    have c₃ := (abs_le.mp b₃).2
    have c₄ := (abs_le.mp b₁).2
    have c₅ := (abs_le.mp b₂).2
    have c₆ := (abs_le.mp b₃).1
    linarith
theorem exists_gaussianRational_close (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ w ∈ gaussianRationals, ‖z - w‖ < ε := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show z.re - ε / 2 < z.re by linarith)
  obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn (show z.im - ε / 2 < z.im by linarith)
  refine ⟨(a : ℂ) + (b : ℂ) * Complex.I, ⟨a, b, rfl⟩, ?_⟩
  refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
  have e₁ : (z - ((a : ℂ) + (b : ℂ) * Complex.I)).re = z.re - a := by simp
  have e₂ : (z - ((a : ℂ) + (b : ℂ) * Complex.I)).im = z.im - b := by simp
  rw [e₁, e₂, abs_of_pos (by linarith), abs_of_pos (by linarith)]
  linarith
theorem zero_mem_rationalSpan (C : DenseChoice D) : 0 ∈ rationalSpan C :=
  ⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, fun p => p.elim0, by simp [linComb]⟩
theorem add_mem_rationalSpan {C : DenseChoice D} {F G : PosSymbolSpan D}
    (hF : F ∈ rationalSpan C) (hG : G ∈ rationalSpan C) : F + G ∈ rationalSpan C := by
  obtain ⟨n, c, X, hc, hX, rfl⟩ := hF
  obtain ⟨n', c', X', hc', hX', rfl⟩ := hG
  refine ⟨n + n', Fin.append c c', Fin.append X X', fun p => ?_, fun p => ?_, ?_⟩
  · induction p using Fin.addCases with
    | left p => rw [Fin.append_left]; exact hc p
    | right p => rw [Fin.append_right]; exact hc' p
  · induction p using Fin.addCases with
    | left p => rw [Fin.append_left]; exact hX p
    | right p => rw [Fin.append_right]; exact hX' p
  · simp [linComb, Fin.sum_univ_add]
theorem smul_basisVec_mem_rationalSpan {C : DenseChoice D} {c : ℂ}
    (hc : c ∈ gaussianRationals) {Y : PosSymbol D} (hY : IsUnitOrDense C Y) :
    c • basisVec Y ∈ rationalSpan C :=
  ⟨1, fun _ => c, fun _ => Y, fun _ => hc, fun _ => hY, by simp [linComb]⟩
theorem rationalSpan_countable
    (hF : PeriodicSpace.EuclideanFamilyForms.Statement) (C : DenseChoice D) :
    (rationalSpan C).Countable := by
  obtain ⟨hEq, ⟨-, hcount, -⟩, -⟩ := (hF (euclideanParams D)).1 C.dense C.isCountable
  let val : PosSymbol D → Σ n : ℕ, Fin n →
      PeriodicSpace.Kind.euclidean.Pt (euclideanParams D) → ℝ := fun X => X.1
  have hinj : Function.Injective val := fun a b h => Subtype.ext h
  have hE : {X : PosSymbol D | IsUnitOrDense C X}.Countable := by
    refine (hcount.preimage_of_injOn hinj.injOn).mono fun X hX => ?_
    rcases hX with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      show X.1 ∈ PeriodicSpace.Kind.tupleFamily (euclideanParams D) .euclidean C.dense
      rw [hEq]
      exact h
  have : Countable {X : PosSymbol D | IsUnitOrDense C X} := hE.to_subtype
  let φ : (Σ n : ℕ, (Fin n → ℚ × ℚ) × (Fin n → {X : PosSymbol D | IsUnitOrDense C X})) →
      PosSymbolSpan D := fun a =>
    linComb (fun p => ((a.2.1 p).1 : ℂ) + ((a.2.1 p).2 : ℂ) * Complex.I) fun p => (a.2.2 p).1
  refine (Set.countable_range φ).mono ?_
  rintro F ⟨n, c, X, hc, hX, rfl⟩
  choose a b hab using hc
  exact ⟨⟨n, fun p => (a p, b p), fun p => ⟨X p, hX p⟩⟩, by simp only [φ, ← hab]⟩
theorem rationalSpanDense (hS : SupportFacts.AllSupportFacts)
    (hI : MotionFacts.MotionInvariance D)
    (hF : PeriodicSpace.EuclideanFamilyForms.Statement)
    (hQ : FormsOperators.PosFormQuotient) {m : SpaceTimeSymbol D → ℝ}
    {bound : ℕ+ → ℝ → ℝ → ℝ≥0} (h₁ : IsNormedSymmMultilinear m)
    (h₂ : IsScaleBounded m bound) (hH : IsHermitianForm (osForm m))
    (hP : IsPosSemidefForm (osForm m)) (C : DenseChoice D) :
    RationalSpanDense m C := by
  refine ⟨rationalSpan_countable hF C, fun F ε hε => ?_⟩
  obtain ⟨-, ⟨p, hp⟩, -⟩ := hQ (PosSymbolSpan D) (osForm m) hH hP
  have hnn : ∀ G, 0 ≤ (osForm m G G).re := fun G => (Complex.le_def.mp (hP.nonneg G)).1
  have him : ∀ G, (osForm m G G).im = 0 := fun G => (Complex.le_def.mp (hP.nonneg G)).2.symm
  have hsq : ∀ G, p G ^ 2 = (osForm m G G).re := fun G => by
    rw [hp, FormsOperators.qNorm, Real.sq_sqrt (hnn G)]
  have happ : ∀ (F : PosSymbolSpan D) (ε' : ℝ), 0 < ε' →
      ∃ F₀ ∈ rationalSpan C, p (F - F₀) < ε' := by
    intro F
    induction F using Finsupp.induction_linear with
    | zero =>
      intro ε' hε'
      exact ⟨0, zero_mem_rationalSpan C, by simpa using hε'⟩
    | add F G hF' hG' =>
      intro ε' hε'
      obtain ⟨F₀, hF₀, h₃⟩ := hF' (ε' / 2) (by positivity)
      obtain ⟨G₀, hG₀, h₄⟩ := hG' (ε' / 2) (by positivity)
      refine ⟨F₀ + G₀, add_mem_rationalSpan hF₀ hG₀, ?_⟩
      have e₁ : F + G - (F₀ + G₀) = (F - F₀) + (G - G₀) := by abel
      rw [e₁]
      exact (map_add_le_add p _ _).trans_lt (by linarith)
    | single X c =>
      intro ε' hε'
      set P := p (basisVec X) with hPdef
      have hP₀ : 0 ≤ P := apply_nonneg p _
      obtain ⟨c', hc', hcc⟩ := exists_gaussianRational_close c (ε := ε' / (2 * (P + 1)))
        (by positivity)
      set e₂ := ε' / (2 * (‖c'‖ + 1)) with he₂
      have he₂₀ : 0 < e₂ := by positivity
      obtain ⟨Y, hY, hlt⟩ := exists_unitOrDense_close hS hI hF h₁ h₂ C X (ε := e₂ ^ 2)
        (by positivity)
      refine ⟨c' • basisVec Y, smul_basisVec_mem_rationalSpan hc' hY, ?_⟩
      have hpe : p (basisVec X - basisVec Y) < e₂ := by
        rw [← hsq] at hlt
        exact lt_of_pow_lt_pow_left₀ 2 he₂₀.le hlt
      have e₁ : Finsupp.single X c - c' • basisVec Y =
          (c - c') • basisVec X + c' • (basisVec X - basisVec Y) := by
        have e₃ : Finsupp.single X c = c • basisVec X := by
          simp [TorusTransport.TupleVectors.basisVec]
        rw [e₃]
        module
      rw [e₁]
      refine (map_add_le_add p _ _).trans_lt ?_
      rw [map_smul_eq_mul, map_smul_eq_mul]
      have h₃ : ‖c - c'‖ * (2 * (P + 1)) < ε' := (lt_div_iff₀ (by positivity)).mp hcc
      have h₄ : ‖c'‖ * p (basisVec X - basisVec Y) ≤ ‖c'‖ * e₂ :=
        mul_le_mul_of_nonneg_left hpe.le (norm_nonneg _)
      have h₅ : e₂ * (2 * (‖c'‖ + 1)) = ε' := div_mul_cancel₀ _ (by positivity)
      have h₆ : 0 ≤ ‖c - c'‖ := norm_nonneg _
      have h₇ : 0 ≤ ‖c'‖ := norm_nonneg _
      nlinarith
  obtain ⟨F₀, hF₀, h₃⟩ := happ F (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  refine ⟨F₀, hF₀, ?_⟩
  refine Complex.lt_def.mpr ⟨?_, ?_⟩
  · rw [Complex.ofReal_re, ← hsq]
    have h₄ := pow_lt_pow_left₀ h₃ (apply_nonneg p _) two_ne_zero
    rwa [Real.sq_sqrt hε.le] at h₄
  · rw [him, Complex.ofReal_im]
theorem holds (hIso : StabilizerAction.Statement)
    (hMod : MotionFacts.Statement)
    (hS : SupportFacts.AllSupportFacts)
    (hComp : FormsOperators.FormsAndCompletions)
    (hF : PeriodicSpace.EuclideanFamilyForms.Statement) : Statement := by
  intro D m bound h₁ h₂
  have hI := (hMod D).1
  have hc := continuousInShift hS hI (hMod D).2.1 h₁ h₂
  refine ⟨lipschitzOnProducts hS h₁ h₂, hc, fun h₃ h₄ => ?_⟩
  have hAct := hIso.2.2 D
  exact ⟨osPreHilbertData_isAdmissible hS hI hIso.2.1.1 hAct h₁ h₂ hc h₃ h₄, supBound hI h₁ h₂,
    fun C => rationalSpanDense hS hI hF hComp.2.1 h₁ h₂
      (isHermitianForm_osForm hAct h₁ h₃) (isPosSemidefForm_osForm h₄) C⟩
end MomentFunctionals
end YangMills.Construction.TimeAxisSymbols
end
