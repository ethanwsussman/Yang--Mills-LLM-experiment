import YangMills.Construction.Continuum.FlatFunctionsTensorsOfSubTuplesAndSmoothTuples
import YangMills.Construction.BoundsOnEverySide.MovingTuplesOfALimitAlongStatesProof
import YangMills.Construction.Continuum.ExtensionToTheSchwartzFunctionsFlatOnTheDiagonals
import YangMills.Construction.Continuum.FactsOfConfigurationSpaceAndItsTestFunctions
import YangMills.Construction.Continuum.FirstFactsOnTheTestSpacesProof
import YangMills.Construction.Continuum.GrowthConditionFromAPowerBoundOnSeparatedTuples
import YangMills.Construction.Continuum.OneSpaceOfTestFunctionsFlatTensorsAndTheDualProof
import YangMills.Construction.Continuum.SupremaOfASmoothFunctionAndTheVectorSpaceOfSchwartzFunctionsProof
import Mathlib
set_option autoImplicit false
open scoped ENNReal ContDiff
noncomputable section
namespace YangMills.Construction.SeparatedPowerBound
theorem one_add_pow_le_two_rpow_mul (t : ℝ) (ht : 0 ≤ t) {k p : ℕ} (hkp : k ≤ p) :
    (1 + t) ^ k ≤ (2 : ℝ) ^ ((k : ℝ) / 2) * (1 + t ^ 2) ^ ((p : ℝ) / 2) := by apply _root_.YangMills.Construction.Continuum.UnifiedTestSpace.one_add_pow_le_weight <;> assumption
theorem one_add_sq_rpow_le_pow (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    (1 + t ^ 2) ^ ((k : ℝ) / 2) ≤ (1 + t) ^ k := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzSuprema.japanese_le_one_add_pow <;> assumption
theorem tupleNorm_nonneg {n : ℕ} (x : TestSpaces.PointTuple n) : 0 ≤ TestSpaces.tupleNorm x := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzSuprema.zero_le_euclidNorm <;> assumption
theorem decaySeminorm_le_weightedSeminorm {n : ℕ} {k q p : ℕ} (hp : max k q ≤ p)
    (φ : TestSpaces.PointTuple n → ℂ) :
    ConfigSpace.decaySeminorm k q φ ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2)) * TestSpaces.weightedSeminorm p φ := by
  refine iSup_le fun α => iSup_le fun hα => iSup_le fun x => ?_
  have hk : k ≤ p := le_trans (le_max_left _ _) hp
  have hq : TestSpaces.idxOrder α ≤ p := le_trans hα (le_trans (le_max_right _ _) hp)
  have hx := tupleNorm_nonneg x
  have hle : ENNReal.ofReal ((1 + TestSpaces.tupleNorm x ^ 2) ^ ((p : ℝ) / 2) *
      ‖TestSpaces.multiDeriv α φ x‖) ≤ TestSpaces.weightedSeminorm p φ :=
    le_iSup_of_le x (le_iSup_of_le α (le_iSup_of_le hq le_rfl))
  calc ENNReal.ofReal ((1 + ConfigSpace.euclidNorm x) ^ k *
        ‖ConfigSpace.iteratedPartial α φ x‖)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2) *
          ((1 + TestSpaces.tupleNorm x ^ 2) ^ ((p : ℝ) / 2) *
            ‖TestSpaces.multiDeriv α φ x‖)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (one_add_pow_le_two_rpow_mul _ hx hk) (norm_nonneg _)
    _ = ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2)) *
          ENNReal.ofReal ((1 + TestSpaces.tupleNorm x ^ 2) ^ ((p : ℝ) / 2) *
            ‖TestSpaces.multiDeriv α φ x‖) :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ _ := by gcongr
theorem weightedSeminorm_le_decaySeminorm {n : ℕ} (p : ℕ) (φ : TestSpaces.PointTuple n → ℂ) :
    TestSpaces.weightedSeminorm p φ ≤ ConfigSpace.decaySeminorm p p φ := by
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ?_
  refine le_trans ?_ (le_iSup_of_le α (le_iSup_of_le hα (le_iSup_of_le x le_rfl)))
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (one_add_sq_rpow_le_pow _ (tupleNorm_nonneg x) p)
    (norm_nonneg _)
theorem finite_setOf_idxOrder_le (n p : ℕ) :
    {α : TestSpaces.MultiIdx4 n | TestSpaces.idxOrder α ≤ p}.Finite := by apply _root_.YangMills.Construction.TestSpaces.Elementary.finite_setOf_idxOrder_le <;> assumption
theorem decaySeminorm_lt_top {n : ℕ} {φ : TestSpaces.PointTuple n → ℂ}
    (hφ : φ ∈ ConfigSpace.schwartzSet n) (p : ℕ) : ConfigSpace.decaySeminorm p p φ < ⊤ := by
  classical
  set F := (finite_setOf_idxOrder_le n p).toFinset
  set g : TestSpaces.MultiIdx4 n → ℝ≥0∞ := fun α =>
    ⨆ x, ENNReal.ofReal ((1 + ConfigSpace.euclidNorm x) ^ p *
      ‖ConfigSpace.iteratedPartial α φ x‖)
  have hsum : ∑ α ∈ F, g α < ⊤ := ENNReal.sum_lt_top.2 fun α _ => hφ.2 p α
  refine lt_of_le_of_lt ?_ hsum
  refine iSup_le fun α => iSup_le fun hα => ?_
  exact Finset.single_le_sum (f := g) (fun _ _ => zero_le)
    ((finite_setOf_idxOrder_le n p).mem_toFinset.2 hα)
theorem testFlatSchwartz_eq (n : ℕ) :
    TestSpaces.flatSchwartzSet n = ConfigSpace.flatSchwartzSet n := by
  have hdiag : ∀ x : TestSpaces.PointTuple n,
      x ∈ ConfigSpace.diagonalSet n ↔ x ∈ TestSpaces.diagonalLocus n := by
    intro x
    rw [TestSpaces.mem_diagonalLocus_iff]
    simp only [ConfigSpace.diagonalSet, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  ext φ
  constructor
  · rintro ⟨⟨hs, hw⟩, hf⟩
    refine ⟨⟨hs, fun k α => ?_⟩, fun α x hx => hf α x ((hdiag x).1 hx)⟩
    set p := max (max k (TestSpaces.idxOrder α)) 1
    have hp : 0 < p := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hb : ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2)) * TestSpaces.weightedSeminorm p φ < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hw p hp)
    refine lt_of_le_of_lt ?_ hb
    refine le_trans ?_
      (decaySeminorm_le_weightedSeminorm (q := TestSpaces.idxOrder α) (le_max_left _ _) φ)
    exact le_iSup_of_le α (le_iSup_of_le le_rfl le_rfl)
  · rintro ⟨hs, hf⟩
    exact ⟨⟨hs.1, fun k _ =>
      lt_of_le_of_lt (weightedSeminorm_le_decaySeminorm k φ) (decaySeminorm_lt_top hs k)⟩,
      fun α x hx => hf α x ((hdiag x).2 hx)⟩
def reParts {n : ℕ} (φ : ConfigSpace.FnTuple n) : Fin n → (Fin 4 → ℝ) → ℝ :=
  fun i y => (φ i y).re
def ofRealParts {n : ℕ} (f : Fin n → (Fin 4 → ℝ) → ℝ) : ConfigSpace.FnTuple n :=
  fun i => ConfigurationSpace.ofRealFun (f i)
theorem ofRealParts_reParts {n : ℕ} {φ : ConfigSpace.FnTuple n}
    (hφ : ∀ i, SmoothMaps.IsRealValued (φ i)) : ofRealParts (reParts φ) = φ := by
  funext i y
  exact Complex.ext (by simp [ofRealParts, reParts, ConfigurationSpace.ofRealFun])
    (by simpa [ofRealParts, reParts, ConfigurationSpace.ofRealFun] using (hφ i y).symm)
theorem reParts_ofRealParts {n : ℕ} (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    reParts (ofRealParts f) = f := by
  funext i y
  simp [ofRealParts, reParts, ConfigurationSpace.ofRealFun]
theorem tsupport_ofRealFun (f : (Fin 4 → ℝ) → ℝ) :
    tsupport (ConfigurationSpace.ofRealFun f) = tsupport f := by apply _root_.YangMills.Construction.FlatTensors.tsupport_ofReal_comp <;> assumption
theorem reParts_mem {n : ℕ} {φ : ConfigSpace.FnTuple n}
    (hφ : φ ∈ ConfigSpace.smoothRealTupleSet n) : reParts φ ∈ SmoothSepR4.smoothSepR4 n := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hφ
  have hc : ofRealParts (reParts φ) = φ := ofRealParts_reParts fun i => (h1 i).1
  have hts : ∀ i, tsupport (reParts φ i) = tsupport (φ i) := fun i => by
    conv_rhs => rw [← hc]
    exact (tsupport_ofRealFun _).symm
  have hsm : ∀ i, ContDiff ℝ ∞ (reParts φ i) := fun i =>
    Complex.reCLM.contDiff.comp (h3 i)
  have hcs : ∀ i, HasCompactSupport (reParts φ i) := fun i => by
    unfold HasCompactSupport
    rw [hts i]
    exact (h1 i).2.2.1
  refine ⟨⟨fun i => ⟨(hsm i).of_le (by simp), hcs i, Set.subset_univ _⟩, fun i i' hne => ?_⟩,
    fun i => ⟨hsm i, hcs i, Set.subset_univ _⟩⟩
  show Disjoint _ _
  rw [hts i, hts i']
  exact h2 i i' hne
theorem ofRealParts_mem {n : ℕ} {f : Fin n → (Fin 4 → ℝ) → ℝ} (hf : f ∈ SmoothSepR4.smoothSepR4 n) :
    ofRealParts f ∈ ConfigSpace.smoothRealTupleSet n := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hf
  have hsm : ∀ i, ContDiff ℝ ∞ (ofRealParts f i) := fun i =>
    Complex.ofRealCLM.contDiff.comp (h3 i).1
  refine ⟨⟨fun i => ⟨fun y => by simp [ofRealParts, ConfigurationSpace.ofRealFun],
    (hsm i).of_le (by simp), ?_, Set.subset_univ _⟩, fun i i' hne => ?_⟩, hsm⟩
  · exact (h1 i).2.1.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  · simp only [ofRealParts, tsupport_ofRealFun]
    exact h2 hne
theorem ofRealFun_reParts {n : ℕ} {φ : ConfigSpace.FnTuple n}
    (hφ : φ ∈ ConfigSpace.smoothRealTupleSet n) (i : Fin n) :
    ConfigurationSpace.ofRealFun (reParts φ i) = φ i :=
  congrFun (ofRealParts_reParts fun i => (hφ.1.1 i).1) i
theorem tsupport_reParts {n : ℕ} {φ : ConfigSpace.FnTuple n}
    (hφ : φ ∈ ConfigSpace.smoothRealTupleSet n) (i : Fin n) :
    tsupport (reParts φ i) = tsupport (φ i) := by
  rw [← tsupport_ofRealFun, ofRealFun_reParts hφ]
def liftForm {n : ℕ} (Φ : TestSpaces.SepTupleOfCard n → ℝ) :
    ConfigSpace.smoothRealTupleSet n → ℝ :=
  fun φ => Φ ⟨reParts φ.1, (reParts_mem φ.2).1⟩
theorem liftForm_multilinear {n : ℕ} {Φ : TestSpaces.SepTupleOfCard n → ℝ}
    (hΦ : TestSpaces.IsMultilinearOnSep Φ) :
    ConfigSpace.IsRealMultilinearSmooth (liftForm Φ) := by
  intro i h h' hag
  constructor
  · intro s hs
    have := hΦ i 1 1 ⟨reParts h.1, (reParts_mem h.2).1⟩
      ⟨reParts h'.1, (reParts_mem h'.2).1⟩ ⟨reParts s.1, (reParts_mem s.2).1⟩
      (fun j hj => by funext y; simp [reParts, hag j hj])
      (by funext y; simp [reParts, hs])
      (fun j hj => by funext y; simp [reParts, hs, Function.update_of_ne hj])
    simpa [liftForm] using this
  · intro lam s hs
    have := hΦ i lam 0 ⟨reParts h.1, (reParts_mem h.2).1⟩
      ⟨reParts h.1, (reParts_mem h.2).1⟩ ⟨reParts s.1, (reParts_mem s.2).1⟩
      (fun j hj => rfl)
      (by funext y; simp [reParts, hs])
      (fun j hj => by funext y; simp [reParts, hs, Function.update_of_ne hj])
    simpa [liftForm] using this
theorem sharpNormR4_eq (hF : ConfigurationSpace.ConfigSpaceTestFunctionFacts) (M : ℝ)
    {f : (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ (TestSpaces.c1CompactSupp Set.univ : Set ((Fin 4 → ℝ) → ℝ)))
    (hsm : ContDiff ℝ ∞ f) :
    TestFunctions.sharpNormR4 M f =
      max (TestFunctions.uniformNorm (ConfigurationSpace.ofRealFun f))
        (40 * M * ConfigSpace.gradSupNorm (ConfigurationSpace.ofRealFun f)) := by
  rw [(hF.2 f hf).2.2 M, ConfigGradients.toReal_gradSup hsm]
  congr 1
  simp [TestFunctions.uniformNorm, ConfigurationSpace.ofRealFun]
theorem liftForm_bounded (hF : ConfigurationSpace.ConfigSpaceTestFunctionFacts) {M : ℝ}
    (hM : 1 ≤ M) {n : ℕ} (hn : 2 ≤ n) {a : ℕ} {G : ℝ} (hG : 0 ≤ G)
    {Φ : TestSpaces.SepTupleOfCard n → ℝ}
    (hm : TestSpaces.IsMultilinearOnSep Φ)
    (hb : ∀ d : ℝ, 0 < d → ∀ X : TestSpaces.SepTupleOfCard n, SeparatedBound.SupportedSeparated 1 d X →
      |Φ X| ≤ G * max 1 (d ^ (-(a : ℤ))) * SeparatedBound.sharpNormProd M X) :
    ConfigSpace.SeparatedBallBound (40 * M) a G (liftForm Φ) := by
  refine ⟨hn, by positivity, hG, liftForm_multilinear hm, fun d hd φ hs hsep => ?_⟩
  have hsup : SeparatedBound.SupportedSeparated 1 d
      (⟨reParts φ.1, (reParts_mem φ.2).1⟩ : TestSpaces.SepTupleOfCard n) := by
    refine ⟨fun i => ?_, ?_⟩
    · obtain ⟨B, ϱ, ⟨a₀, rfl⟩, hϱ, hsub⟩ := hs i
      refine ⟨a₀, ?_⟩
      rw [tsupport_reParts φ.2]
      exact hsub.trans fun y hy => le_trans hy hϱ
    · refine le_iInf fun i => le_iInf fun i' => le_iInf fun hne => ?_
      simp only [tsupport_reParts φ.2]
      exact hsep.2 i i' hne
  have hprod : SeparatedBound.sharpNormProd M
      (⟨reParts φ.1, (reParts_mem φ.2).1⟩ : TestSpaces.SepTupleOfCard n) =
      ∏ i, max (TestFunctions.uniformNorm (φ.1 i))
        (40 * M * ConfigSpace.gradSupNorm (φ.1 i)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    have h1 := reParts_mem φ.2
    rw [sharpNormR4_eq hF M (h1.1.1 i) (h1.2 i).1, ofRealFun_reParts φ.2]
  rw [← hprod]
  exact hb d hd _ hsup
theorem flatSchwartzSet_eq (hF : ConfigurationSpace.ConfigSpaceTestFunctionFacts)
    {n : ℕ} (hn : 1 ≤ n) : ConfigurationSpace.flatSchwartzSet n = ConfigSpace.flatSchwartzSet n := by
  obtain ⟨-, -, -, -, -, h, -, -⟩ := hF.1 n hn
  rw [← testFlatSchwartz_eq]
  exact h.2.2
theorem sobolevWeightNorm_eq (hF : ConfigurationSpace.ConfigSpaceTestFunctionFacts) {n : ℕ}
    (hn : 1 ≤ n) (φ : ConfigurationSpace.flatSchwartzSet n) {p : ℕ} (hp : 1 ≤ p) :
    ConfigurationSpace.sobolevWeightNorm p φ.1 = TestSpaces.weightedSeminorm p φ.1 := by
  obtain ⟨-, -, -, -, -, h, -, -⟩ := hF.1 n hn
  exact h.2.1 φ.1 φ.2.1 p hp
theorem extendsToFlat_of_isFlatExtension (hF : ConfigurationSpace.ConfigSpaceTestFunctionFacts)
    {n : ℕ} (hn : 1 ≤ n) {Φ : TestSpaces.SepTupleOfCard n → ℝ}
    (hs : ConfigurationSpace.flatSchwartzSet n = ConfigSpace.flatSchwartzSet n)
    {S : ConfigSpace.flatSchwartzSet n → ℂ}
    (hS : FlatExtension.IsFlatExtension (liftForm Φ) S) :
    SeparatedBound.ExtendsToFlat Φ (fun ψ => S ⟨ψ.1, hs.le ψ.2⟩) := by
  obtain ⟨-, -, -, -, hDual, -, -, -⟩ := hF.1 n hn
  obtain ⟨⟨hadd, hsm⟩, k, q, b, hb0, hb⟩ := hS.1
  have hlin : ConfigurationSpace.IsLinearOnFlatSchwartz
      (fun ψ : ConfigurationSpace.flatSchwartzSet n => S ⟨ψ.1, hs.le ψ.2⟩) :=
    ⟨fun φ φ' χ e => hadd _ _ _ e, fun c φ χ e => hsm c _ _ e⟩
  refine ⟨(hDual _ hlin).2 ⟨max (max k q) 1, b * (2 : ℝ) ^ ((k : ℝ) / 2), by positivity,
    fun φ => ?_⟩, fun f hf hmem => ?_⟩
  · have hp : 1 ≤ max (max k q) 1 := le_max_right _ _
    calc ENNReal.ofReal ‖S ⟨φ.1, hs.le φ.2⟩‖
        ≤ ENNReal.ofReal b * ConfigSpace.decaySeminorm k q φ.1 := hb _
      _ ≤ ENNReal.ofReal b * (ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2)) *
            TestSpaces.weightedSeminorm (max (max k q) 1) φ.1) := by
          gcongr
          exact decaySeminorm_le_weightedSeminorm (le_max_left _ _) _
      _ = _ := by
          rw [sobolevWeightNorm_eq hF hn φ hp, ENNReal.ofReal_mul hb0, mul_assoc]
  · obtain ⟨χ, hχ, hv⟩ := hS.2 ⟨ofRealParts f, ofRealParts_mem hf⟩
    have e : (⟨ConfigurationSpace.ofRealFun (TestSpaces.tensorProd f), hs.le hmem⟩ :
        ConfigSpace.flatSchwartzSet n) = χ := by
      refine Subtype.ext ?_
      rw [hχ]
      funext x
      simp [ConfigurationSpace.ofRealFun, TestSpaces.tensorProd, ConfigSpace.tensorProd,
        ofRealParts]
    have e2 : (⟨reParts (ofRealParts f), (reParts_mem (ofRealParts_mem hf)).1⟩ :
        TestSpaces.SepTupleOfCard n) = ⟨f, hf.1⟩ := Subtype.ext (reParts_ofRealParts f)
    show S _ = _
    rw [e, hv]
    simp only [liftForm]
    rw [e2]
theorem isFlatExtension_of_extendsToFlat (hF : ConfigurationSpace.ConfigSpaceTestFunctionFacts)
    {n : ℕ} (hn : 1 ≤ n) {Φ : TestSpaces.SepTupleOfCard n → ℝ}
    (hs : ConfigurationSpace.flatSchwartzSet n = ConfigSpace.flatSchwartzSet n)
    {T : ConfigurationSpace.flatSchwartzSet n → ℂ} (hT : SeparatedBound.ExtendsToFlat Φ T) :
    FlatExtension.IsFlatExtension (liftForm Φ)
      (fun χ => T ⟨χ.1, hs.ge χ.2⟩) := by
  obtain ⟨-, -, -, hCmp, hDual, -, hFlat, hTens⟩ := hF.1 n hn
  have hlin := hT.1.1
  obtain ⟨k', b, hb0, hb⟩ := (hDual T hlin).1 hT.1
  refine ⟨⟨⟨fun φ φ' χ e => hlin.1 _ _ _ e, fun c φ χ e => hlin.2 c _ _ e⟩,
    k' + 1, k' + 1, b, hb0, fun χ => ?_⟩, fun φ => ?_⟩
  · have hχ : χ.1 ∈ ConfigurationSpace.flatSchwartzSet n := hs.ge χ.2
    calc ENNReal.ofReal ‖T ⟨χ.1, hs.ge χ.2⟩‖
        ≤ ENNReal.ofReal b * ConfigurationSpace.sobolevWeightNorm k' χ.1 := hb ⟨χ.1, hχ⟩
      _ ≤ ENNReal.ofReal b * ConfigurationSpace.sobolevWeightNorm (k' + 1) χ.1 := by
          gcongr
          exact (hCmp χ.1 hχ.1 k' 0 (k' + 1)).2.2 (by omega)
      _ = ENNReal.ofReal b * TestSpaces.weightedSeminorm (k' + 1) χ.1 := by
          rw [sobolevWeightNorm_eq hF hn ⟨χ.1, hχ⟩ (by omega)]
      _ ≤ _ := by
          gcongr
          exact weightedSeminorm_le_decaySeminorm _ _
  · have hf := reParts_mem φ.2
    have hm : ConfigurationSpace.ofRealFun (TestSpaces.tensorProd (reParts φ.1)) ∈
        ConfigurationSpace.flatSchwartzSet n :=
      hFlat.2.2.2 (hTens _ hf)
    have e : ConfigurationSpace.ofRealFun (TestSpaces.tensorProd (reParts φ.1)) =
        ConfigSpace.tensorProd φ.1 := by
      funext x
      have : ∀ i, ((reParts φ.1 i (x i) : ℝ) : ℂ) = φ.1 i (x i) := fun i =>
        congrFun (ofRealFun_reParts φ.2 i) (x i)
      simp [ConfigurationSpace.ofRealFun, TestSpaces.tensorProd, ConfigSpace.tensorProd, this]
    refine ⟨⟨ConfigSpace.tensorProd φ.1, hs.le (e ▸ hm)⟩, rfl, ?_⟩
    have e2 : (⟨ConfigSpace.tensorProd φ.1, hs.ge (hs.le (e ▸ hm))⟩ :
        ConfigurationSpace.flatSchwartzSet n) =
        ⟨ConfigurationSpace.ofRealFun (TestSpaces.tensorProd (reParts φ.1)), hm⟩ :=
      Subtype.ext e.symm
    show T _ = _
    rw [e2]
    exact hT.2 _ hf hm
theorem extension_of_separatedBallBound
    (hE : FlatSchwartzExtension.UniqueBoundedExtension)
    (hF : ConfigurationSpace.ConfigSpaceTestFunctionFacts)
    {n : ℕ} (hn : 2 ≤ n) {c : ℝ} (hc : 0 < c) {a : ℕ} {G : ℝ} (hG : 0 ≤ G)
    {Φ : TestSpaces.SepTupleOfCard n → ℝ}
    (hB : ConfigSpace.SeparatedBallBound c a G (liftForm Φ)) :
    (∃! T, SeparatedBound.ExtendsToFlat Φ T) ∧
      (∀ T, SeparatedBound.ExtendsToFlat Φ T → ∀ φ : ConfigurationSpace.flatSchwartzSet n,
        ENNReal.ofReal ‖T φ‖ ≤
          ENNReal.ofReal (ExtensionConstants.extConst n a *
              ConfigSpace.maxOneWeight c ^ n * G) *
            ConfigSpace.decaySeminorm (4 * n + 2) (10 * n + a - 2) φ.1) ∧
      ExtensionConstants.extConst n a ≤
        ExtensionConstants.extFactor * ExtensionConstants.extBase ^ (n + a) *
          (n.factorial : ℝ) ^ 19 := by
  have hn1 : 1 ≤ n := by omega
  have hs := flatSchwartzSet_eq hF hn1
  obtain ⟨⟨S₀, hS₀, huniq⟩, hbound, hconst⟩ := hE n c a G _ hn hc hG hB
  refine ⟨⟨_, extendsToFlat_of_isFlatExtension hF hn1 hs hS₀, fun T hT => ?_⟩, fun T hT φ => ?_,
    hconst⟩
  · have := huniq _ (isFlatExtension_of_extendsToFlat hF hn1 hs hT)
    funext ψ
    exact congrFun this ⟨ψ.1, hs.le ψ.2⟩
  · exact hbound _ (isFlatExtension_of_extendsToFlat hF hn1 hs hT) ⟨φ.1, hs.le φ.2⟩
theorem block_eq_of_mem {n : ℕ} {η : Finset (Finset (Fin n))}
    (hη : ClusterExpansion.SymGraph.IsPartition η)
    {b b' : Finset (Fin n)} (hb : b ∈ η) (hb' : b' ∈ η) {i : Fin n} (hi : i ∈ b) (hi' : i ∈ b') :
    b = b' := by
  by_contra hne
  exact Finset.disjoint_left.1 (hη.2.1 hb hb' hne) hi hi'
theorem exists_block_mem {n : ℕ} {η : Finset (Finset (Fin n))}
    (hη : ClusterExpansion.SymGraph.IsPartition η) (i : Fin n) : ∃ b ∈ η, i ∈ b := by
  have hi := (Finset.ext_iff.1 hη.2.2 i).2 (Finset.mem_univ i)
  simp only [Finset.mem_biUnion, id] at hi
  exact hi
theorem isPartition_of_mem {n : ℕ} {η : Finset (Finset (Fin n))}
    (hη : η ∈ TestSpaces.partitionsNoSingletons (Fin n)) :
    ClusterExpansion.SymGraph.IsPartition η ∧ ∀ J ∈ η, 2 ≤ J.card := by
  simp only [TestSpaces.partitionsNoSingletons, ClusterExpansion.SymGraph.partitions,
    Finset.mem_filter, Finset.mem_univ, true_and] at hη
  exact hη
theorem biUnion_id_eq_univ {n : ℕ} {η : Finset (Finset (Fin n))}
    (hη : ClusterExpansion.SymGraph.IsPartition η) : η.biUnion id = Finset.univ :=
  Finset.eq_univ_of_forall fun i => by
    obtain ⟨b, hb, hi⟩ := exists_block_mem hη i
    exact Finset.mem_biUnion.2 ⟨b, hb, hi⟩
def InSameBlock {n : ℕ} (η : Finset (Finset (Fin n))) (i j : Fin n) : Prop :=
  ∃ b ∈ η, i ∈ b ∧ j ∈ b
def blockMin {n : ℕ} (η : Finset (Finset (Fin n))) (i : Fin n) : ℕ :=
  sInf {j : ℕ | ∃ h : j < n, InSameBlock η i ⟨j, h⟩}
theorem inSameBlock_refl {n : ℕ} {η : Finset (Finset (Fin n))}
    (hη : ClusterExpansion.SymGraph.IsPartition η) (i : Fin n) : InSameBlock η i i := by
  obtain ⟨b, hb, hi⟩ := exists_block_mem hη i
  exact ⟨b, hb, hi, hi⟩
theorem inSameBlock_symm {n : ℕ} {η : Finset (Finset (Fin n))} {i j : Fin n}
    (hij : InSameBlock η i j) : InSameBlock η j i := by
  obtain ⟨b, hb, hi, hj⟩ := hij
  exact ⟨b, hb, hj, hi⟩
theorem inSameBlock_trans {n : ℕ} {η : Finset (Finset (Fin n))}
    (hη : ClusterExpansion.SymGraph.IsPartition η)
    {i j k : Fin n} (hij : InSameBlock η i j) (hjk : InSameBlock η j k) : InSameBlock η i k := by
  obtain ⟨b, hb, hi, hj⟩ := hij
  obtain ⟨b', hb', hj', hk⟩ := hjk
  obtain rfl := block_eq_of_mem hη hb hb' hj hj'
  exact ⟨b, hb, hi, hk⟩
theorem blockMin_spec {n : ℕ} {η : Finset (Finset (Fin n))}
    (hη : ClusterExpansion.SymGraph.IsPartition η)
    (i : Fin n) : ∃ hl : blockMin η i < n, InSameBlock η i ⟨blockMin η i, hl⟩ := by
  have hne : {j : ℕ | ∃ h : j < n, InSameBlock η i ⟨j, h⟩}.Nonempty :=
    ⟨i.1, i.2, inSameBlock_refl hη i⟩
  exact Nat.sInf_mem hne
theorem blockMin_le {n : ℕ} {η : Finset (Finset (Fin n))}
    (hη : ClusterExpansion.SymGraph.IsPartition η) (i : Fin n) : blockMin η i ≤ i.1 :=
  Nat.sInf_le ⟨i.2, inSameBlock_refl hη i⟩
theorem blockMin_eq_of_inSameBlock {n : ℕ} {η : Finset (Finset (Fin n))}
    (hη : ClusterExpansion.SymGraph.IsPartition η)
    {i j : Fin n} (hij : InSameBlock η i j) : blockMin η i = blockMin η j := by
  unfold blockMin
  congr 1
  ext k
  constructor
  · rintro ⟨hk, hs⟩
    exact ⟨hk, inSameBlock_trans hη (inSameBlock_symm hij) hs⟩
  · rintro ⟨hk, hs⟩
    exact ⟨hk, inSameBlock_trans hη hij hs⟩
theorem inSameBlock_iff_blockMin_eq {n : ℕ} {η : Finset (Finset (Fin n))}
    (hη : ClusterExpansion.SymGraph.IsPartition η)
    (i j : Fin n) : InSameBlock η i j ↔ blockMin η i = blockMin η j := by
  refine ⟨blockMin_eq_of_inSameBlock hη, fun he => ?_⟩
  obtain ⟨hl, hs⟩ := blockMin_spec hη i
  obtain ⟨hl', hs'⟩ := blockMin_spec hη j
  have e : (⟨blockMin η i, hl⟩ : Fin n) = ⟨blockMin η j, hl'⟩ := Fin.ext he
  rw [e] at hs
  exact inSameBlock_trans hη hs (inSameBlock_symm hs')
theorem block_eq_filter_blockMin {n : ℕ} {η : Finset (Finset (Fin n))}
    (hη : ClusterExpansion.SymGraph.IsPartition η)
    {b : Finset (Fin n)} (hb : b ∈ η) {i : Fin n} (hi : i ∈ b) :
    b = Finset.univ.filter fun j => blockMin η i = blockMin η j := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← inSameBlock_iff_blockMin_eq hη]
  constructor
  · intro hj
    exact ⟨b, hb, hi, hj⟩
  · rintro ⟨b', hb', hi', hj'⟩
    obtain rfl := block_eq_of_mem hη hb hb' hi hi'
    exact hj'
theorem subset_of_blockMin_eq {n : ℕ} {η η' : Finset (Finset (Fin n))}
    (hη : ClusterExpansion.SymGraph.IsPartition η) (hη' : ClusterExpansion.SymGraph.IsPartition η')
    (he : ∀ i, blockMin η i = blockMin η' i) : η ⊆ η' := by
  intro b hb
  obtain ⟨i, hi⟩ := hη.1 b hb
  obtain ⟨b', hb', hi'⟩ := exists_block_mem hη' i
  have : b = b' := by
    rw [block_eq_filter_blockMin hη hb hi, block_eq_filter_blockMin hη' hb' hi']
    simp only [he]
  exact this ▸ hb'
theorem card_partitionsNoSingletons_le (n : ℕ) :
    (TestSpaces.partitionsNoSingletons (Fin n)).card ≤ n.factorial := by
  classical
  let F : Finset (Finset (Fin n)) → (∀ i : Fin n, Fin (i.1 + 1)) := fun η i =>
    ⟨min (blockMin η i) i.1, by omega⟩
  have hcard : Fintype.card (∀ i : Fin n, Fin (i.1 + 1)) = n.factorial := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Fin.prod_univ_eq_prod_range (fun i => i + 1) n, Finset.prod_range_add_one_eq_factorial]
  rw [← hcard, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn F (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
  intro η hη η' hη' he
  have h := (isPartition_of_mem (Finset.mem_coe.1 hη)).1
  have h' := (isPartition_of_mem (Finset.mem_coe.1 hη')).1
  have hl : ∀ i, blockMin η i = blockMin η' i := by
    intro i
    have := congrArg Fin.val (congrFun he i)
    simp only [F] at this
    rwa [min_eq_left (blockMin_le h i), min_eq_left (blockMin_le h' i)] at this
  exact Finset.Subset.antisymm (subset_of_blockMin_eq h h' hl)
    (subset_of_blockMin_eq h' h fun i => (hl i).symm)
theorem sum_card_eq {n : ℕ} {η : Finset (Finset (Fin n))}
    (hη : ClusterExpansion.SymGraph.IsPartition η) : ∑ J ∈ η, J.card = n := by
  have hc := Finset.card_biUnion (s := η) (t := id) fun x hx y hy hxy => hη.2.1 hx hy hxy
  rw [biUnion_id_eq_univ hη] at hc
  simpa using hc.symm
theorem prod_factorial_card_le {n : ℕ} {η : Finset (Finset (Fin n))}
    (hη : ClusterExpansion.SymGraph.IsPartition η) : ∏ J ∈ η, J.card.factorial ≤ n.factorial := by
  have hd := Nat.prod_factorial_dvd_factorial_sum η (fun J => J.card)
  rw [sum_card_eq hη] at hd
  exact Nat.le_of_dvd (Nat.factorial_pos n) hd
theorem sharpNormR4_nonneg (M : ℝ) (f : (Fin 4 → ℝ) → ℝ) :
    0 ≤ TestFunctions.sharpNormR4 M f := by apply _root_.YangMills.Construction.BoundsOnEverySide.TranslatedTuples.sharpNormR4_nonneg <;> assumption
theorem sharpNormProd_sepRestrict {n : ℕ} (M : ℝ) (X : TestSpaces.SepTupleOfCard n)
    (J : Finset (Fin n)) :
    SeparatedBound.sharpNormProd M (TestSpaces.sepRestrict X J) =
      ∏ i ∈ J, TestFunctions.sharpNormR4 M (X.1 i) := by
  classical
  unfold SeparatedBound.sharpNormProd
  rw [← Finset.prod_coe_sort J (fun i => TestFunctions.sharpNormR4 M (X.1 i))]
  refine Fintype.prod_equiv (J.orderIsoOfFin rfl).toEquiv _ _ fun k => ?_
  simp [TestSpaces.sepRestrict, SchwingerFunctions.restrictTuple, Finset.coe_orderIsoOfFin_apply]
theorem supportedSeparated_sepRestrict {n : ℕ} {R d : ℝ} (X : TestSpaces.SepTupleOfCard n)
    (hX : SeparatedBound.SupportedSeparated R d X) (J : Finset (Fin n)) :
    SeparatedBound.SupportedSeparated R d (TestSpaces.sepRestrict X J) := by
  refine ⟨fun k => hX.1 _, ?_⟩
  refine le_iInf fun i => le_iInf fun i' => le_iInf fun hii => ?_
  have hne : J.orderEmbOfFin rfl i ≠ J.orderEmbOfFin rfl i' := fun e =>
    hii ((J.orderEmbOfFin rfl).injective e)
  exact hX.2.trans (iInf_le_of_le _ (iInf_le_of_le _ (iInf_le_of_le hne le_rfl)))
theorem abs_centred_le (M k b : ℝ) (hk : 0 ≤ k) (hb : 0 ≤ b) (S : SeparatedBound.CorrelationFamily)
    (n : ℕ) (X : TestSpaces.SepTupleOfCard n)
    (hS : ∀ (J : Finset (Fin n)) (hJ : 2 ≤ J.card), |S J.card hJ (TestSpaces.sepRestrict X J)| ≤
      b ^ J.card * (J.card.factorial : ℝ) ^ k *
        SeparatedBound.sharpNormProd M (TestSpaces.sepRestrict X J)) :
    |TestSpaces.centredOfCumulants S ⟨n, X⟩| ≤
      b ^ n * (n.factorial : ℝ) ^ (k + 1) * SeparatedBound.sharpNormProd M X := by
  classical
  have hf0 : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hP : 0 ≤ SeparatedBound.sharpNormProd M X :=
    Finset.prod_nonneg fun i _ => sharpNormR4_nonneg M _
  set Q : ℝ := b ^ n * (n.factorial : ℝ) ^ k * SeparatedBound.sharpNormProd M X with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have term : ∀ η : {η // η ∈ TestSpaces.partitionsNoSingletons (Fin n)},
      |∏ J ∈ η.1.attach,
        S J.1.card (TestSpaces.two_le_card_of_mem_partitionsNoSingletons η.2 J.2)
          (TestSpaces.sepRestrict X J.1)| ≤ Q := by
    rintro ⟨η, hη⟩
    obtain ⟨hpart, h2⟩ := isPartition_of_mem hη
    rw [Finset.abs_prod]
    calc ∏ J ∈ η.attach, |S J.1.card (TestSpaces.two_le_card_of_mem_partitionsNoSingletons hη J.2)
          (TestSpaces.sepRestrict X J.1)|
        ≤ ∏ J ∈ η.attach, (b ^ J.1.card * (J.1.card.factorial : ℝ) ^ k *
            SeparatedBound.sharpNormProd M (TestSpaces.sepRestrict X J.1)) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun J _ => hS J.1 _
      _ = ∏ J ∈ η, (b ^ J.card * (J.card.factorial : ℝ) ^ k *
            SeparatedBound.sharpNormProd M (TestSpaces.sepRestrict X J)) :=
          Finset.prod_attach η fun J => b ^ J.card * (J.card.factorial : ℝ) ^ k *
            SeparatedBound.sharpNormProd M (TestSpaces.sepRestrict X J)
      _ = b ^ n * ((∏ J ∈ η, J.card.factorial : ℕ) : ℝ) ^ k *
            SeparatedBound.sharpNormProd M X := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
            Finset.prod_pow_eq_pow_sum, sum_card_eq hpart,
            Nat.cast_prod, Real.finsetProd_rpow _ _ fun J _ => by positivity]
          congr 1
          simp only [sharpNormProd_sepRestrict]
          unfold SeparatedBound.sharpNormProd
          have e := Finset.prod_biUnion (s := η) (t := id)
            (f := fun i => TestFunctions.sharpNormR4 M (X.1 i))
            (fun x hx y hy hxy => hpart.2.1 hx hy hxy)
          rw [biUnion_id_eq_univ hpart] at e
          exact e.symm
      _ ≤ Q := by
          have e2 : ((∏ J ∈ η, J.card.factorial : ℕ) : ℝ) ^ k ≤ (n.factorial : ℝ) ^ k :=
            Real.rpow_le_rpow (by positivity)
              (by exact_mod_cast prod_factorial_card_le hpart) hk
          rw [hQ]
          gcongr
  unfold TestSpaces.centredOfCumulants
  have hsum : |∑ η ∈ (TestSpaces.partitionsNoSingletons (Fin n)).attach, ∏ J ∈ η.1.attach,
      S J.1.card (TestSpaces.two_le_card_of_mem_partitionsNoSingletons η.2 J.2)
        (TestSpaces.sepRestrict X J.1)| ≤
      ((TestSpaces.partitionsNoSingletons (Fin n)).card : ℝ) * Q := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ Q fun η _ => term η).trans ?_
    simp
  refine hsum.trans ?_
  have hc : ((TestSpaces.partitionsNoSingletons (Fin n)).card : ℝ) ≤ n.factorial := by
    exact_mod_cast card_partitionsNoSingletons_le n
  calc ((TestSpaces.partitionsNoSingletons (Fin n)).card : ℝ) * Q ≤ n.factorial * Q :=
        mul_le_mul_of_nonneg_right hc hQ0
    _ = b ^ n * (n.factorial : ℝ) ^ (k + 1) * SeparatedBound.sharpNormProd M X := by
        rw [Real.rpow_add hf0, Real.rpow_one, hQ]
        ring
theorem one_le_extBaseMax : 1 ≤ SeparatedBound.extBaseMax := le_max_left _ _
theorem extFactorAbs_nonneg : 0 ≤ SeparatedBound.extFactorAbs := abs_nonneg _
theorem extConst_le {n a : ℕ}
    (h : ExtensionConstants.extConst n a ≤
      ExtensionConstants.extFactor * ExtensionConstants.extBase ^ (n + a) *
        (n.factorial : ℝ) ^ 19) :
    ExtensionConstants.extConst n a ≤
      SeparatedBound.extFactorAbs * SeparatedBound.extBaseMax ^ (n + a) *
        (n.factorial : ℝ) ^ 19 := by
  refine h.trans ?_
  have hf : (0 : ℝ) ≤ (n.factorial : ℝ) ^ 19 := by positivity
  refine mul_le_mul_of_nonneg_right ?_ hf
  have h1 : ExtensionConstants.extBase ^ (n + a) ≤ SeparatedBound.extBaseMax ^ (n + a) := by
    refine (le_abs_self _).trans ?_
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) _
  have h2 : ExtensionConstants.extFactor = SeparatedBound.extFactorAbs := by
    simp [SeparatedBound.extFactorAbs, ExtensionConstants.extFactor]
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
theorem two_rpow_half_eq (n : ℕ) :
    (2 : ℝ) ^ (((4 * n + 2 : ℕ) : ℝ) / 2) = 2 * 4 ^ n := by
  have : (((4 * n + 2 : ℕ) : ℝ) / 2) = ((2 * n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_natCast, pow_succ, pow_mul]
  norm_num
  ring
theorem max_one_zpow_pow {d : ℝ} (hd : 0 < d) (a m : ℕ) :
    max 1 (d ^ (-(a : ℤ))) ^ m = max 1 (d ^ (-((a * m : ℕ) : ℤ))) := by
  have e1 : d ^ (-(a : ℤ)) = d⁻¹ ^ a := by
    rw [zpow_neg, inv_pow, zpow_natCast]
  have e2 : d ^ (-((a * m : ℕ) : ℤ)) = (d⁻¹ ^ a) ^ m := by
    rw [zpow_neg, zpow_natCast, ← pow_mul, inv_pow]
  rw [e1, e2]
  rcases le_total 1 (d⁻¹ ^ a) with h | h
  · rw [max_eq_right h, max_eq_right (one_le_pow₀ h)]
  · rw [max_eq_left h, max_eq_left (pow_le_one₀ (by positivity) h), one_pow]
theorem bound_in_sobolevWeightNorm (hF : ConfigurationSpace.ConfigSpaceTestFunctionFacts) {n : ℕ}
    (hn : 1 ≤ n) {E W : ℝ} {k q p : ℕ} (hkq : max k q ≤ p) (hp : 1 ≤ p)
    (hW : E * (2 : ℝ) ^ ((k : ℝ) / 2) ≤ W) (z : ℂ) (φ : ConfigurationSpace.flatSchwartzSet n)
    (h : ENNReal.ofReal ‖z‖ ≤
      ENNReal.ofReal E * ConfigSpace.decaySeminorm k q φ.1) :
    ENNReal.ofReal ‖z‖ ≤ ENNReal.ofReal W * ConfigurationSpace.sobolevWeightNorm p φ.1 := by
  calc ENNReal.ofReal ‖z‖
      ≤ ENNReal.ofReal E * (ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2)) *
          TestSpaces.weightedSeminorm p φ.1) := by
        refine h.trans ?_
        gcongr
        exact decaySeminorm_le_weightedSeminorm hkq _
    _ = ENNReal.ofReal (E * (2 : ℝ) ^ ((k : ℝ) / 2)) *
          ConfigurationSpace.sobolevWeightNorm p φ.1 := by
        rw [sobolevWeightNorm_eq hF hn φ hp, ENNReal.ofReal_mul' (by positivity), mul_assoc]
    _ ≤ _ := by gcongr
theorem bound_at_power (hF : ConfigurationSpace.ConfigSpaceTestFunctionFacts) {M : ℝ}
    (hM : 1 ≤ M) {n : ℕ} (hn : 2 ≤ n) {a : ℕ} {C x : ℝ} (hC : 0 ≤ C)
    (hconst : ExtensionConstants.extConst n (a * n) ≤
      ExtensionConstants.extFactor * ExtensionConstants.extBase ^ (n + a * n) *
        (n.factorial : ℝ) ^ 19)
    (z : ℂ) (φ : ConfigurationSpace.flatSchwartzSet n)
    (h : ENNReal.ofReal ‖z‖ ≤
      ENNReal.ofReal (ExtensionConstants.extConst n (a * n) *
          ConfigSpace.maxOneWeight (40 * M) ^ n * (C ^ n * (n.factorial : ℝ) ^ x)) *
        ConfigSpace.decaySeminorm (4 * n + 2) (10 * n + a * n - 2) φ.1) :
    ENNReal.ofReal ‖z‖ ≤
      ENNReal.ofReal (2 * SeparatedBound.extFactorAbs * powerBase M a C ^ n *
          (n.factorial : ℝ) ^ (19 + x)) *
        ConfigurationSpace.sobolevWeightNorm ((10 + a) * n) φ.1 := by
  have hw : ConfigSpace.maxOneWeight (40 * M) = 40 * M := by
    unfold ConfigSpace.maxOneWeight
    exact max_eq_right (by linarith)
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hkq : max (4 * n + 2) (10 * n + a * n - 2) ≤ (10 + a) * n := by
    have : (10 + a) * n = 10 * n + a * n := by ring
    omega
  have hp : 1 ≤ (10 + a) * n := by nlinarith
  refine bound_in_sobolevWeightNorm hF (by omega) hkq hp ?_ _ φ h
  rw [hw, two_rpow_half_eq]
  have hrest : 0 ≤ (40 * M) ^ n * (C ^ n * (n.factorial : ℝ) ^ x) * (2 * 4 ^ n) := by positivity
  have h1 := mul_le_mul_of_nonneg_right (extConst_le hconst) hrest
  have e19 : (n.factorial : ℝ) ^ (19 + x) = (n.factorial : ℝ) ^ 19 * (n.factorial : ℝ) ^ x := by
    rw [Real.rpow_add hf]
    norm_cast
  have hbase : powerBase M a C ^ n =
      (40 * M) ^ n * 4 ^ n * SeparatedBound.extBaseMax ^ (n + a * n) * C ^ n := by
    have : SeparatedBound.extBaseMax ^ (n + a * n) = (SeparatedBound.extBaseMax ^ (1 + a)) ^ n := by
      rw [← pow_mul]
      congr 1
      ring
    rw [this, powerBase, show 160 * M * SeparatedBound.extBaseMax ^ (1 + a) * C =
      40 * M * 4 * SeparatedBound.extBaseMax ^ (1 + a) * C by ring]
    simp only [mul_pow]
  calc _ = ExtensionConstants.extConst n (a * n) *
        ((40 * M) ^ n * (C ^ n * (n.factorial : ℝ) ^ x) * (2 * 4 ^ n)) := by ring
    _ ≤ _ := h1
    _ = _ := by
        rw [e19, hbase]
        ring
theorem zero_mem_flatSchwartzDualSet (n : ℕ) :
    (0 : ConfigurationSpace.flatSchwartzSet n → ℂ) ∈ ConfigurationSpace.flatSchwartzDualSet n :=
  ⟨⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩, 0, 0, 0, le_rfl, fun _ => by simp⟩
theorem schwinger_of_momentSequence (hF : ConfigurationSpace.ConfigSpaceTestFunctionFacts)
    {S : SeparatedBound.CorrelationFamily} {Q : GrowthSequences.FlatSeq}
    (hQ : SeparatedBound.IsMomentSequence S Q)
    (hseq : GrowthSequences.IsDistribSeq Q) {s : ℕ} (hs : 1 ≤ s) {c K x : ℝ} (hc : 0 ≤ c)
    (hK : 0 ≤ K) (hg : GrowthForms.GeomBound Q s c K x) :
    ∃ T, TestSpaces.IsSchwingerFamily (TestSpaces.centredOfCumulants S) T ∧
      SeparatedBound.MatchesMembers Q T ∧
      ∀ n, 1 ≤ n → ∀ φ : TestSpaces.flatSchwartzSet n,
        ENNReal.ofReal ‖T n φ‖ ≤
          ENNReal.ofReal (c * K ^ n * (n.factorial : ℝ) ^ x) *
            TestSpaces.weightedSeminorm (s * n) φ.1 := by
  classical
  have hset : ∀ n, 1 ≤ n →
      ConfigurationSpace.flatSchwartzSet n = TestSpaces.flatSchwartzSet n :=
    fun n hn => by
      obtain ⟨-, -, -, -, -, h, -, -⟩ := hF.1 n hn
      exact h.2.2
  let T : (n : ℕ) → TestSpaces.flatSchwartzSet n → ℂ := fun n φ =>
    if h : 1 ≤ n then Q.posTerm n h ⟨φ.1, (hset n h).ge φ.2⟩ else φ.1 fun _ => 0
  have hT : ∀ n (h : 1 ≤ n) (φ : TestSpaces.flatSchwartzSet n),
      T n φ = Q.posTerm n h ⟨φ.1, (hset n h).ge φ.2⟩ := fun n h φ => dif_pos h
  have hbd : ∀ n, 1 ≤ n → ∀ φ : TestSpaces.flatSchwartzSet n,
      ENNReal.ofReal ‖T n φ‖ ≤
        ENNReal.ofReal (c * K ^ n * (n.factorial : ℝ) ^ x) *
          TestSpaces.weightedSeminorm (s * n) φ.1 := by
    intro n hn φ
    rw [hT n hn φ, ← sobolevWeightNorm_eq hF hn ⟨φ.1, (hset n hn).ge φ.2⟩ (by nlinarith)]
    exact hg n hn _
  refine ⟨T, ⟨fun n hn => ⟨?_, ⟨s * n, c * K ^ n * (n.factorial : ℝ) ^ x, by nlinarith,
    by positivity, hbd n hn⟩, fun X hX h => ?_⟩,
    fun φ => (dif_neg (by omega)).trans (congrArg φ.1 (Subsingleton.elim _ _))⟩,
    fun n hn φ φ' e => ?_, hbd⟩
  · intro a b φ ψ χ e
    obtain ⟨-, -, -, -, -, -, hFlat, -⟩ := hF.1 n hn
    have hl := hFlat.2.1
    have hlin := (hseq.2 n hn).1
    have m1 : a • φ.1 ∈ ConfigurationSpace.flatSchwartzSet n :=
      hl.2.2 a _ ((hset n hn).ge φ.2)
    have m2 : b • ψ.1 ∈ ConfigurationSpace.flatSchwartzSet n :=
      hl.2.2 b _ ((hset n hn).ge ψ.2)
    rw [hT n hn, hT n hn, hT n hn]
    rw [hlin.1 ⟨_, m1⟩ ⟨_, m2⟩ _ e, hlin.2 a ⟨φ.1, (hset n hn).ge φ.2⟩ ⟨_, m1⟩ rfl,
      hlin.2 b ⟨ψ.1, (hset n hn).ge ψ.2⟩ ⟨_, m2⟩ rfl]
  · rw [hT n hn]
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      rw [hQ.2.1 hn, TestSpaces.centredOfCumulants_single]
      simp
    · have hsm : X.1 ∈ SmoothSepR4.smoothSepR4 n := ⟨X.2, hX⟩
      exact (hQ.2.2 n h2).2 X.1 hsm _
  · rw [hT n hn]
    exact congrArg _ (Subtype.ext e)
theorem mul_max_one_pow {d C : ℝ} (hd : 0 < d) (a n : ℕ) :
    (C * max 1 (d ^ (-(a : ℤ)))) ^ n = C ^ n * max 1 (d ^ (-((a * n : ℕ) : ℤ))) := by
  rw [mul_pow, max_one_zpow_pow hd]
theorem growthFromPowerSepBound (hE : FlatSchwartzExtension.UniqueBoundedExtension)
    (hF : ConfigurationSpace.ConfigSpaceTestFunctionFacts)
    (hT : GrowthForms.GrowthFormsEquiv) : GrowthFromPowerSepBound := by
  intro M a C k S hM hC hk hml hfun hbound
  have hfact : ∀ n : ℕ, (0 : ℝ) < (n.factorial : ℝ) := fun n => by
    exact_mod_cast Nat.factorial_pos n
  have hB0 : 0 ≤ SeparatedBound.extBaseMax := le_trans zero_le_one one_le_extBaseMax
  have hL : 0 ≤ powerBase M a C := by unfold powerBase; positivity
  have hc' : 0 ≤ 2 * SeparatedBound.extFactorAbs := by
    have := extFactorAbs_nonneg; positivity
  have hG : ∀ (x : ℝ) (n : ℕ), 0 ≤ C ^ n * (n.factorial : ℝ) ^ x := fun x n =>
    mul_nonneg (pow_nonneg hC n) (Real.rpow_nonneg (hfact n).le _)
  have hBc : ∀ (n : ℕ) (hn : 2 ≤ n), ConfigSpace.SeparatedBallBound (40 * M) (a * n)
      (C ^ n * (n.factorial : ℝ) ^ k) (liftForm (S n hn)) := by
    intro n hn
    refine liftForm_bounded hF hM hn (hG k n) (hml n hn) fun d hd X hX => ?_
    refine (hbound n hn d hd X hX).trans (le_of_eq ?_)
    rw [mul_max_one_pow hd]
    ring
  have hextc := fun (n : ℕ) (hn : 2 ≤ n) =>
    extension_of_separatedBallBound hE hF hn (c := 40 * M) (by positivity) (a := a * n)
      (hG k n) (hBc n hn)
  have hmom : ∀ (n : ℕ), 2 ≤ n → ∀ d : ℝ, 0 < d → ∀ X : TestSpaces.SepTupleOfCard n,
      SeparatedBound.SupportedSeparated 1 d X →
        |TestSpaces.centredOfCumulants S ⟨n, X⟩| ≤
          (C * max 1 (d ^ (-(a : ℤ)))) ^ n * (n.factorial : ℝ) ^ (k + 1) *
            SeparatedBound.sharpNormProd M X := by
    intro n hn d hd X hX
    refine abs_centred_le M k _ hk (mul_nonneg hC (le_trans zero_le_one (le_max_left _ _))) S n X
      fun J hJ => ?_
    exact hbound _ hJ d hd _ (supportedSeparated_sepRestrict X hX J)
  have hBm : ∀ (n : ℕ) (hn : 2 ≤ n), ConfigSpace.SeparatedBallBound (40 * M) (a * n)
      (C ^ n * (n.factorial : ℝ) ^ (k + 1))
      (liftForm fun X : TestSpaces.SepTupleOfCard n => TestSpaces.centredOfCumulants S ⟨n, X⟩) := by
    intro n hn
    refine liftForm_bounded hF hM hn (hG _ n) (hfun.2 n (by omega)) fun d hd X hX => ?_
    refine (hmom n hn d hd X hX).trans (le_of_eq ?_)
    rw [mul_max_one_pow hd]
    ring
  have hextm := fun (n : ℕ) (hn : 2 ≤ n) =>
    extension_of_separatedBallBound hE hF hn (c := 40 * M) (by positivity) (a := a * n)
      (hG _ n) (hBm n hn)
  have hmomb : ∀ (n : ℕ) (hn : 2 ≤ n) (T : ConfigurationSpace.flatSchwartzSet n → ℂ),
      SeparatedBound.ExtendsToFlat
        (fun X : TestSpaces.SepTupleOfCard n => TestSpaces.centredOfCumulants S ⟨n, X⟩) T →
      ∀ φ : ConfigurationSpace.flatSchwartzSet n,
        ENNReal.ofReal ‖T φ‖ ≤
          ENNReal.ofReal (2 * SeparatedBound.extFactorAbs * powerBase M a C ^ n *
              (n.factorial : ℝ) ^ (20 + k)) *
            ConfigurationSpace.sobolevWeightNorm ((10 + a) * n) φ.1 := by
    intro n hn T hTe φ
    obtain ⟨-, hbd, hconst⟩ := hextm n hn
    have := bound_at_power hF hM hn hC hconst _ φ (hbd T hTe φ)
    rwa [show (19 + (k + 1) : ℝ) = 20 + k by ring] at this
  have hseq : ∀ Q, SeparatedBound.IsMomentSequence S Q → GrowthSequences.IsDistribSeq Q := by
    intro Q hQ
    refine ⟨hQ.1, fun n hn => ?_⟩
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      rw [hQ.2.1 hn]
      exact zero_mem_flatSchwartzDualSet 1
    · exact (hQ.2.2 n h2).1
  have hgeom : ∀ Q, SeparatedBound.IsMomentSequence S Q →
      GrowthForms.GeomBound Q (10 + a) (2 * SeparatedBound.extFactorAbs) (powerBase M a C)
        (20 + k) := by
    intro Q hQ n hn φ
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      rw [hQ.2.1 hn]
      simp
    · exact hmomb n h2 _ (hQ.2.2 n h2) φ
  have hx : (0 : ℝ) ≤ 20 + k := by linarith
  have hexists : ∃ Q, SeparatedBound.IsMomentSequence S Q := by
    classical
    refine ⟨⟨id, fun n _ => if h : 2 ≤ n then ((hextm n h).1).choose else 0⟩, rfl, fun h => ?_,
      fun n hn => ?_⟩
    · simp
    · show SeparatedBound.ExtendsToFlat _ (dite _ _ _)
      rw [dif_pos hn]
      exact ((hextm n hn).1).choose_spec.1
  have hs : 1 ≤ 10 + a := by omega
  refine
    { existsUnique_extension := fun n hn => (hextc n hn).1
      extension_bound := fun n hn T hTe φ => ?_
      centred_bound := hmom
      existsUnique_centred_extension := fun n hn => (hextm n hn).1
      moment_geomBound := hgeom
      isSchwingerFamily := fun Q hQ => ?_
      growthBound := fun ϰ hϰ => ?_
      growthWith := fun Q hQ => ?_ }
  · obtain ⟨-, hbd, hconst⟩ := hextc n hn
    exact bound_at_power hF hM hn hC hconst _ φ (hbd T hTe φ)
  · obtain ⟨T, h1, h2, -⟩ :=
      schwinger_of_momentSequence hF hQ (hseq Q hQ) hs hc' hL (hgeom Q hQ)
    exact ⟨T, h1, h2⟩
  · obtain ⟨Q, hQ⟩ := hexists
    obtain ⟨T, h1, -, h3⟩ :=
      schwinger_of_momentSequence hF hQ (hseq Q hQ) hs hc' hL (hgeom Q hQ)
    refine ⟨by omega, hc', hL, by linarith, T, h1, fun n hn φ => (h3 n hn φ).trans ?_⟩
    gcongr ?_ * _
    apply ENNReal.ofReal_le_ofReal
    have h1f : (1 : ℝ) ≤ n.factorial := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1f hϰ) (by positivity)
  · have := (hT.2 Q (hseq Q hQ)).1 (10 + a) _ _ _ (by omega) hc' hL hx (hgeom Q hQ)
    exact this
end YangMills.Construction.SeparatedPowerBound
end
