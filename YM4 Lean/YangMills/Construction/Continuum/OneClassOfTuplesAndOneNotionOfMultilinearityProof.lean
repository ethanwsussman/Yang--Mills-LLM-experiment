import YangMills.Construction.QuaternionicWilsonModel.TheDefaultCasesAreUnusedProof
import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.Continuum.OneClassOfTuplesAndOneNotionOfMultilinearity
import YangMills.Construction.Continuum.OperationsOnFunctionsOfSeveralPoints
import YangMills.Construction.Continuum.SubTuplesIsometriesAndTheConjugateOnFourSpace
import YangMills.Construction.Cumulants.PartitionsMomentsAndTheCentredFunctionalOfAFamily
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TestSpaces.UnifiedSeparatedTuples
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open YangMills.Construction.TestFunctions (setDistR4 HasSeparatedSupportsR4)
open YangMills.Construction.TorusMetric (euclidNormVec)
variable {s : Conventions.StandingParameters} {n : ℕ}
theorem tsupport_pt_eq (f : (Fin 4 → ℝ) → ℝ) :
    (@tsupport (AmbientPoints.Pt s .euclidean) ℝ _ _ f : Set (Fin 4 → ℝ)) = tsupport f := by apply _root_.YangMills.Construction.R4TupleForms.tsupport_pt_euclidean <;> assumption
theorem isCompact_tsupport_pt_iff (f : (Fin 4 → ℝ) → ℝ) :
    @IsCompact (AmbientPoints.Pt s .euclidean) _
        (@tsupport (AmbientPoints.Pt s .euclidean) ℝ _ _ f) ↔ HasCompactSupport f := by apply _root_.YangMills.Construction.R4TupleForms.isCompact_tsupport_pt_iff_hasCompactSupport <;> assumption
theorem mem_ambientSeparated_iff (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    (f : Fin n → AmbientPoints.Pt s .euclidean → ℝ) ∈
      AmbientPoints.separatedTuples s .euclidean n ↔ f ∈ disjointSupportTuples Set.univ n := by apply _root_.YangMills.Construction.Continuum.SeparatedFourTuples.mem_separatedTuples_iff <;> assumption
theorem mem_c1CompactlySupportedIn_iff {A : Set (Fin 4 → ℝ)} {f : (Fin 4 → ℝ) → ℝ} :
    (f : AmbientPoints.Pt s .euclidean → ℝ) ∈
        AmbientPoints.c1CompactlySupportedIn (s := s) (E := .euclidean) A ↔
      ContDiff ℝ 1 f ∧ HasCompactSupport f ∧ tsupport f ⊆ A := by
  refine and_congr Iff.rfl (and_congr (isCompact_tsupport_pt_iff f) ?_)
  exact Iff.of_eq (congrArg (fun B : Set (Fin 4 → ℝ) => B ⊆ A) (tsupport_pt_eq (s := s) f))
def toAmbient (X : SepTupleOfCard n) : AmbientPoints.separatedTuples s .euclidean n :=
  ⟨X.1, (mem_ambientSeparated_iff X.1).2 X.2⟩
def ofAmbient (f : AmbientPoints.separatedTuples s .euclidean n) : SepTupleOfCard n :=
  ⟨f.1, (mem_ambientSeparated_iff f.1).1 f.2⟩
theorem exists_pos_ofReal_le_of_finite {ι : Type*} [Finite ι] (g : ι → ENNReal)
    (h : ∀ i, 0 < g i) : ∃ d : ℝ, 0 < d ∧ ∀ i, ENNReal.ofReal d ≤ g i := by
  rcases isEmpty_or_nonempty ι with he | hne
  · exact ⟨1, one_pos, fun i => (he.false i).elim⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min g
  obtain ⟨r, hr₀, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (h i₀)
  refine ⟨r, by exact_mod_cast hr₀, fun i => ?_⟩
  rw [ENNReal.ofReal_coe_nnreal]
  exact hr.le.trans (hi₀ i)
theorem pairwiseSeparated_of_isCompact_of_disjoint {C : Fin n → Set (Fin 4 → ℝ)}
    (hC : ∀ i, IsCompact (C i))
    (h : ∀ i k, i ≠ k → Disjoint (C i) (C k)) : SchwingerFunctions.PairwiseSeparated C := by
  obtain ⟨d, hd, hle⟩ := exists_pos_ofReal_le_of_finite
    (ι := {p : Fin n × Fin n // p.1 ≠ p.2})
    (fun p => setDistR4 (C p.1.1) (C p.1.2))
    (fun p => SeparatedTuplesR4.setDistR4_pos_of_disjoint (hC _) (hC _).isClosed
      (h _ _ p.2))
  exact ⟨d, hd, fun i k hik => hle ⟨(i, k), hik⟩⟩
theorem disjoint_of_setDistR4_pos {A B : Set (Fin 4 → ℝ)} (h : 0 < setDistR4 A B) :
    Disjoint A B := by
  rw [Set.disjoint_left]
  intro x hA hB
  have h₁ : setDistR4 A B ≤ ENNReal.ofReal (euclidNormVec (x - x)) :=
    iInf₂_le_of_le x hA (iInf₂_le x hB)
  have h₂ : ENNReal.ofReal (euclidNormVec (x - x)) = 0 := by
    simp [euclidNormVec]
  rw [h₂] at h₁
  exact absurd h (not_lt.2 h₁)
theorem setDistR4_anti {A A' B B' : Set (Fin 4 → ℝ)} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    setDistR4 A B ≤ setDistR4 A' B' :=
  le_iInf₂ fun a ha => le_iInf₂ fun b hb => iInf₂_le_of_le a (hA ha) (iInf₂_le b (hB hb))
theorem disjointSupportTuples_univ_eq_sepAtPositiveDist (n : ℕ) :
    disjointSupportTuples Set.univ n = sepAtPositiveDist n := by
  ext f
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun i => ⟨(h₁ i).1, (h₁ i).2.1⟩, ?_⟩
    obtain ⟨d, hd, hle⟩ := pairwiseSeparated_of_isCompact_of_disjoint
      (C := fun i => tsupport (f i)) (fun i => (h₁ i).2.1) (fun i k hik => h₂ hik)
    exact ⟨d, hd, hle⟩
  · rintro ⟨h₁, d, hd, hle⟩
    exact ⟨fun i => ⟨(h₁ i).1, (h₁ i).2, Set.subset_univ _⟩, fun i k hik =>
      disjoint_of_setDistR4_pos ((ENNReal.ofReal_pos.2 hd).trans_le (hle i k hik))⟩
theorem tupleClasses_coincide (s : Conventions.StandingParameters) (n : ℕ) :
    TupleClassesCoincide s n := by
  refine ⟨?_, disjointSupportTuples_univ_eq_sepAtPositiveDist n⟩
  ext f
  exact mem_ambientSeparated_iff f
theorem isMultilinearOnSep_iff_isLinearOnSeparatedCompacts (Φ : SepTupleOfCard n → ℝ) :
    IsMultilinearOnSep Φ ↔ IsLinearOnSeparatedCompacts Φ := by
  classical
  constructor
  · intro h C _ _ i b b' X X' X'' _ _ hXX' hi hj
    exact h i b b' X X' X'' hXX' hi hj
  · intro h i b b' X X' X'' hXX' hi hj
    have hK : ∀ (Y : SepTupleOfCard n) j, IsCompact (tsupport (Y.1 j)) :=
      fun Y j => (Y.2.1 j).2.1
    obtain ⟨C, hCi, hCl⟩ : ∃ C : Fin n → Set (Fin 4 → ℝ),
        C i = tsupport (X.1 i) ∪ tsupport (X'.1 i) ∧ ∀ l, l ≠ i → C l = tsupport (X.1 l) :=
      ⟨fun l => if l = i then tsupport (X.1 i) ∪ tsupport (X'.1 i) else tsupport (X.1 l),
        if_pos rfl, fun l hl => if_neg hl⟩
    have hcompact : ∀ l, IsCompact (C l) := by
      intro l
      by_cases hl : l = i
      · rw [hl, hCi]
        exact (hK X i).union (hK X' i)
      · rw [hCl l hl]
        exact hK X l
    have hdi : ∀ l, l ≠ i → Disjoint (C i) (C l) := by
      intro l hl
      rw [hCi, hCl l hl]
      refine Set.disjoint_union_left.2 ⟨X.2.2 hl.symm, ?_⟩
      rw [hXX' l hl]
      exact X'.2.2 hl.symm
    have hdis : ∀ l k, l ≠ k → Disjoint (C l) (C k) := by
      intro l k hlk
      by_cases hl : l = i
      · subst hl
        exact hdi k hlk.symm
      · by_cases hk : k = i
        · subst hk
          exact (hdi l hl).symm
        · rw [hCl l hl, hCl k hk]
          exact X.2.2 hlk
    have hX : ∀ j, tsupport (X.1 j) ⊆ C j := by
      intro j
      by_cases hj' : j = i
      · rw [hj', hCi]
        exact Set.subset_union_left
      · rw [hCl j hj']
    have hX' : ∀ j, tsupport (X'.1 j) ⊆ C j := by
      intro j
      by_cases hj' : j = i
      · rw [hj', hCi]
        exact Set.subset_union_right
      · rw [hCl j hj', hXX' j hj']
    exact h C hcompact (pairwiseSeparated_of_isCompact_of_disjoint hcompact hdis) i b b' X X' X''
      hX hX' hXX' hi hj
theorem mem_c1Submodule_of_mem_c1CompactSupp {C : Set (Fin 4 → ℝ)} {f : (Fin 4 → ℝ) → ℝ}
    (hf : f ∈ c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) (hC : tsupport f ⊆ C) :
    (f : AmbientPoints.Pt s .euclidean → ℝ) ∈
      AmbientPoints.c1Submodule (s := s) (E := .euclidean) C :=
  mem_c1CompactlySupportedIn_iff.2 ⟨hf.1, hf.2.1, hC⟩
theorem isLinearOnSeparatedCompacts_of_isTupleMultilinear
    {Ψ : AmbientPoints.separatedTuples s .euclidean n → ℝ}
    {Φ : SepTupleOfCard n → ℝ} (hΨ : AgreeOnComponents Ψ Φ) (h : AmbientPoints.IsTupleMultilinear Ψ) :
    IsLinearOnSeparatedCompacts Φ := by
  classical
  intro C hC hsep i b b' X X' X'' hX hX' hXX' hi hj
  have hpos : Pairwise fun k l =>
      AmbientPoints.PositivelySeparated s .euclidean (C k) (C l) := by
    obtain ⟨d, hd, hle⟩ := hsep
    exact fun k l hkl => ((ENNReal.ofReal_pos.2 hd).trans_le (hle k l hkl)).ne'
  obtain ⟨L, hL⟩ := h C hpos
  let g : (j : Fin n) → AmbientPoints.c1Submodule (s := s) (E := .euclidean) (C j) :=
    fun j => ⟨X.1 j, mem_c1Submodule_of_mem_c1CompactSupp (X.2.1 j) (hX j)⟩
  let y : AmbientPoints.c1Submodule (s := s) (E := .euclidean) (C i) :=
    ⟨X'.1 i, mem_c1Submodule_of_mem_c1CompactSupp (X'.2.1 i) (hX' i)⟩
  have hlin : L (Function.update g i (b • g i + b' • y)) =
      b * L (Function.update g i (g i)) + b' * L (Function.update g i y) := by
    rw [L.map_update_add, L.map_update_smul, L.map_update_smul]
    simp only [smul_eq_mul]
  have e₁ : L (Function.update g i (b • g i + b' • y)) = Φ X'' := by
    rw [hL]
    refine hΨ _ X'' (funext fun j => ?_)
    by_cases hji : j = i
    · subst hji
      simp only [Function.update_self]
      exact hi.symm
    · simp only [Function.update_of_ne hji]
      exact (hj j hji).symm
  have e₂ : L (Function.update g i (g i)) = Φ X := by
    rw [hL]
    refine hΨ _ X (funext fun j => ?_)
    by_cases hji : j = i
    · subst hji
      simp only [Function.update_self]
      rfl
    · simp only [Function.update_of_ne hji]
      rfl
  have e₃ : L (Function.update g i y) = Φ X' := by
    rw [hL]
    refine hΨ _ X' (funext fun j => ?_)
    by_cases hji : j = i
    · subst hji
      simp only [Function.update_self]
      rfl
    · simp only [Function.update_of_ne hji]
      exact hXX' j hji
  rw [e₁, e₂, e₃] at hlin
  exact hlin
theorem isTupleMultilinear_of_isMultilinearOnSep
    {Ψ : AmbientPoints.separatedTuples s .euclidean n → ℝ}
    {Φ : SepTupleOfCard n → ℝ} (hΨ : AgreeOnComponents Ψ Φ) (h : IsMultilinearOnSep Φ) :
    AmbientPoints.IsTupleMultilinear Ψ := by
  intro A hA
  let T : ((i : Fin n) → AmbientPoints.c1Submodule (A i)) → SepTupleOfCard n := fun g =>
    ofAmbient ⟨fun i => (g i : AmbientPoints.Pt s .euclidean → ℝ),
      AmbientPoints.mem_separatedTuples_of_forall_mem_c1 hA fun i => (g i).2⟩
  have hT : ∀ g, Ψ ⟨fun i => (g i : AmbientPoints.Pt s .euclidean → ℝ),
      AmbientPoints.mem_separatedTuples_of_forall_mem_c1 hA fun i => (g i).2⟩ =
      Φ (T g) := fun g => hΨ _ _ rfl
  refine ⟨{ toFun := fun g => Φ (T g), map_update_add' := ?_, map_update_smul' := ?_ },
    fun g => (hT g).symm⟩
  · intro _ m i x y
    have := h i 1 1 (T (Function.update m i x)) (T (Function.update m i y))
      (T (Function.update m i (x + y)))
      (fun j hj => by
        change (Function.update m i x j).1 = (Function.update m i y j).1
        rw [Function.update_of_ne hj, Function.update_of_ne hj])
      (by
        funext u
        change (Function.update m i (x + y) i).1 u =
          (1 : ℝ) * (Function.update m i x i).1 u + (1 : ℝ) * (Function.update m i y i).1 u
        simp only [Function.update_self]
        rw [one_mul, one_mul]
        rfl)
      (fun j hj => by
        change (Function.update m i (x + y) j).1 = (Function.update m i x j).1
        rw [Function.update_of_ne hj, Function.update_of_ne hj])
    simpa using this
  · intro _ m i c x
    have := h i c 0 (T (Function.update m i x)) (T (Function.update m i x))
      (T (Function.update m i (c • x))) (fun _ _ => rfl)
      (by
        funext u
        change (Function.update m i (c • x) i).1 u =
          c * (Function.update m i x i).1 u + (0 : ℝ) * (Function.update m i x i).1 u
        simp only [Function.update_self]
        rw [zero_mul, add_zero]
        rfl)
      (fun j hj => by
        change (Function.update m i (c • x) j).1 = (Function.update m i x j).1
        rw [Function.update_of_ne hj, Function.update_of_ne hj])
    simpa using this
theorem multilinearNotions_coincide (s : Conventions.StandingParameters) (n : ℕ) :
    MultilinearNotionsCoincide s n :=
  fun _ Φ hΨ =>
    ⟨⟨fun h => (isMultilinearOnSep_iff_isLinearOnSeparatedCompacts Φ).2
        (isLinearOnSeparatedCompacts_of_isTupleMultilinear hΨ h),
        isTupleMultilinear_of_isMultilinearOnSep hΨ⟩,
      isMultilinearOnSep_iff_isLinearOnSeparatedCompacts Φ⟩
theorem mem_disjointSupportTuples_of_tsupport_subset {C : Fin n → Set (Fin 4 → ℝ)}
    (hC : SchwingerFunctions.PairwiseSeparated C) {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (hf : ∀ k, SchwingerFunctions.IsC1c (f k) ∧ tsupport (f k) ⊆ C k) :
    f ∈ disjointSupportTuples Set.univ n := by
  obtain ⟨d, hd, hle⟩ := hC
  rw [disjointSupportTuples_univ_eq_sepAtPositiveDist]
  exact ⟨fun k => (hf k).1, d, hd, fun i k hik =>
    (hle i k hik).trans (setDistR4_anti (hf i).2 (hf k).2)⟩
theorem update_isC1c_and_tsupport_subset {C : Fin n → Set (Fin 4 → ℝ)}
    {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (hf : ∀ k, SchwingerFunctions.IsC1c (f k) ∧ tsupport (f k) ⊆ C k) {i : Fin n}
    {g : (Fin 4 → ℝ) → ℝ} (hg : SchwingerFunctions.IsC1c g) (hgC : tsupport g ⊆ C i)
    (k : Fin n) :
    SchwingerFunctions.IsC1c (Function.update f i g k) ∧
      tsupport (Function.update f i g k) ⊆ C k := by
  by_cases hk : k = i
  · rw [hk, Function.update_self]
    exact ⟨hg, hgC⟩
  · rw [Function.update_of_ne hk]
    exact hf k
theorem linearCombination_isC1c_and_tsupport_subset {C : Set (Fin 4 → ℝ)} (hC : IsCompact C)
    {g h : (Fin 4 → ℝ) → ℝ} (hg : SchwingerFunctions.IsC1c g) (hgC : tsupport g ⊆ C)
    (hh : SchwingerFunctions.IsC1c h) (hhC : tsupport h ⊆ C) (a b : ℝ) :
    SchwingerFunctions.IsC1c (a • g + b • h) ∧ tsupport (a • g + b • h) ⊆ C := by
  have hsub : tsupport (a • g + b • h) ⊆ C := by
    refine closure_minimal (fun x hx => ?_) hC.isClosed
    by_contra hxC
    have hg₀ : g x = 0 := by
      by_contra h'
      exact hxC (hgC (subset_tsupport g h'))
    have hh₀ : h x = 0 := by
      by_contra h'
      exact hxC (hhC (subset_tsupport h h'))
    exact hx (by simp [hg₀, hh₀])
  have hc : ContDiff ℝ 1 (a • g + b • h) :=
    (ContDiff.const_smul a hg.1).add (ContDiff.const_smul b hh.1)
  exact ⟨⟨hc, hC.of_isClosed_subset (isClosed_tsupport _) hsub⟩, hsub⟩
theorem isContinuumSchwingerFamily_of_agreesWithFamily
    {S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ}
    {F : AmbientPoints.ConnectedFamily s .euclidean} (hS : AgreesWithFamily S F) :
    SchwingerFunctions.IsContinuumSchwingerFamily S := by
  intro n hn C hC hsep f hf i g h a b hg hgC hh hhC
  have hcomb := linearCombination_isC1c_and_tsupport_subset (hC i) hg hgC hh hhC a b
  let X : SepTupleOfCard n := ⟨Function.update f i g,
    mem_disjointSupportTuples_of_tsupport_subset hsep
      (update_isC1c_and_tsupport_subset hf hg hgC)⟩
  let X' : SepTupleOfCard n := ⟨Function.update f i h,
    mem_disjointSupportTuples_of_tsupport_subset hsep
      (update_isC1c_and_tsupport_subset hf hh hhC)⟩
  let X'' : SepTupleOfCard n := ⟨Function.update f i (a • g + b • h),
    mem_disjointSupportTuples_of_tsupport_subset hsep
      (update_isC1c_and_tsupport_subset hf hcomb.1 hcomb.2)⟩
  let Φ : SepTupleOfCard n → ℝ := fun Y => F.fn n hn (toAmbient Y)
  have hone : AgreeOnComponents (F.fn n hn) Φ := fun f' Y hY =>
    congrArg _ (Subtype.ext hY)
  have hlin := isLinearOnSeparatedCompacts_of_isTupleMultilinear hone (F.fn_multilinear n hn)
    C hC hsep i a b X X' X''
    (fun j => (update_isC1c_and_tsupport_subset hf hg hgC j).2)
    (fun j => (update_isC1c_and_tsupport_subset hf hh hhC j).2)
    (fun j hj => by simp only [X, X', Function.update_of_ne hj])
    (by simp only [X, X', X'', Function.update_self])
    (fun j hj => by simp only [X, X'', Function.update_of_ne hj])
  have r₁ : S n (Function.update f i (a • g + b • h)) = (Φ X'' : ℂ) := hS n hn (toAmbient X'')
  have r₂ : S n (Function.update f i g) = (Φ X : ℂ) := hS n hn (toAmbient X)
  have r₃ : S n (Function.update f i h) = (Φ X' : ℂ) := hS n hn (toAmbient X')
  rw [r₁, r₂, r₃, hlin]
  simp only [Complex.ofReal_add, Complex.ofReal_mul]
theorem isRealValued_of_agreesWithFamily {S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ}
    {F : AmbientPoints.ConnectedFamily s .euclidean} (hS : AgreesWithFamily S F) :
    IsRealValued S := by
  intro n hn f hf
  rw [← disjointSupportTuples_univ_eq_sepAtPositiveDist] at hf
  have h : S n f = _ := hS n hn ⟨f, (mem_ambientSeparated_iff f).2 hf⟩
  rw [h]
  exact Complex.ofReal_im _
open Classical in
def schwingerOfConnected (F : AmbientPoints.ConnectedFamily s .euclidean) (n : ℕ)
    (f : Fin n → (Fin 4 → ℝ) → ℝ) : ℂ :=
  if h : 2 ≤ n ∧ f ∈ (AmbientPoints.separatedTuples s .euclidean n :
      Set (Fin n → (Fin 4 → ℝ) → ℝ)) then
    ((F.fn n h.1 ⟨f, h.2⟩ : ℝ) : ℂ)
  else 0
theorem agreesWithFamily_schwingerOfConnected (F : AmbientPoints.ConnectedFamily s .euclidean) :
    AgreesWithFamily (schwingerOfConnected F) F := fun _ hn f => dif_pos ⟨hn, f.2⟩
def reOnCard (S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ) (n : ℕ) (X : SepTupleOfCard n) : ℝ :=
  (S n X.1).re
theorem reOnCard_isLinearOnSeparatedCompacts {S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ}
    (hS : SchwingerFunctions.IsContinuumSchwingerFamily S) (n : ℕ) (hn : 2 ≤ n) :
    IsLinearOnSeparatedCompacts (reOnCard S n) := by
  intro C hC hsep i b b' X X' X'' hX hX' hXX' hi hj
  have hf : ∀ k, SchwingerFunctions.IsC1c (X.1 k) ∧ tsupport (X.1 k) ⊆ C k :=
    fun k => ⟨⟨(X.2.1 k).1, (X.2.1 k).2.1⟩, hX k⟩
  have hlin := hS n hn C hC hsep X.1 hf i (X.1 i) (X'.1 i) b b' (hf i).1 (hf i).2
    ⟨(X'.2.1 i).1, (X'.2.1 i).2.1⟩ (hX' i)
  have e₁ : Function.update X.1 i (b • X.1 i + b' • X'.1 i) = X''.1 := by
    funext j
    by_cases hji : j = i
    · rw [hji, Function.update_self, hi]
    · rw [Function.update_of_ne hji, hj j hji]
  have e₂ : Function.update X.1 i (X'.1 i) = X'.1 := by
    funext j
    by_cases hji : j = i
    · rw [hji, Function.update_self]
    · rw [Function.update_of_ne hji, hXX' j hji]
  rw [e₁, Function.update_eq_self, e₂] at hlin
  change (S n X''.1).re = b * (S n X.1).re + b' * (S n X'.1).re
  rw [hlin]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
def connectedOfSchwinger (s : Conventions.StandingParameters)
    {S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ}
    (hS : SchwingerFunctions.IsContinuumSchwingerFamily S) :
    AmbientPoints.ConnectedFamily s .euclidean where
  fn n _ f := reOnCard S n (ofAmbient f)
  fn_multilinear n hn := isTupleMultilinear_of_isMultilinearOnSep (fun f X hX =>
    congrArg _ (Subtype.ext hX))
    ((isMultilinearOnSep_iff_isLinearOnSeparatedCompacts _).2
      (reOnCard_isLinearOnSeparatedCompacts hS n hn))
theorem agreesWithFamily_connectedOfSchwinger (s : Conventions.StandingParameters)
    {S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ}
    (hS : SchwingerFunctions.IsContinuumSchwingerFamily S) (hr : IsRealValued S) :
    AgreesWithFamily S (connectedOfSchwinger s hS) := by
  intro n hn f
  have hf : f.1 ∈ sepAtPositiveDist n := by
    rw [← disjointSupportTuples_univ_eq_sepAtPositiveDist]
    exact (mem_ambientSeparated_iff f.1).1 f.2
  exact Complex.ext (by simp [connectedOfSchwinger, reOnCard, ofAmbient])
    (by simpa using hr n hn f.1 hf)
theorem connectedFamily_eq_of_agreesWithFamily {S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ}
    {F F' : AmbientPoints.ConnectedFamily s .euclidean} (h : AgreesWithFamily S F)
    (h' : AgreesWithFamily S F') : F = F' := by
  have key : F.fn = F'.fn := by
    funext n hn X
    exact Complex.ofReal_injective ((h n hn X).symm.trans (h' n hn X))
  cases F
  cases F'
  dsimp only at key
  subst key
  rfl
theorem families_coincide (s : Conventions.StandingParameters) : FamiliesCoincide s :=
  ⟨fun F => ⟨⟨schwingerOfConnected F, agreesWithFamily_schwingerOfConnected F⟩, fun _ h =>
      ⟨isContinuumSchwingerFamily_of_agreesWithFamily h, isRealValued_of_agreesWithFamily h⟩⟩,
    fun _ hS hr => ⟨connectedOfSchwinger s hS, agreesWithFamily_connectedOfSchwinger s hS hr,
      fun _ h' => connectedFamily_eq_of_agreesWithFamily h'
        (agreesWithFamily_connectedOfSchwinger s hS hr)⟩⟩
def ambientOfSepTuple (Y : SepTuple) :
    AmbientPoints.allSeparatedTuples s .euclidean :=
  ⟨⟨Y.1, Y.2.1⟩, (mem_ambientSeparated_iff Y.2.1).2 Y.2.2⟩
def sepTupleOfAmbient (X : AmbientPoints.allSeparatedTuples s .euclidean) :
    SepTuple :=
  ⟨X.1.1, ⟨X.1.2, (mem_ambientSeparated_iff X.1.2).1 X.2⟩⟩
theorem eq_ambientOfSepTuple {X : AmbientPoints.allSeparatedTuples s .euclidean}
    {Y : SepTuple} (h : SameTuple X Y) : X = ambientOfSepTuple Y :=
  Subtype.ext h
theorem agreeOnSameTuples_iff {σ : AmbientPoints.allSeparatedTuples s .euclidean → ℝ}
    {σ' : SepTuple → ℝ} :
    AgreeOnSameTuples σ σ' ↔ ∀ Y, σ (ambientOfSepTuple Y) = σ' Y :=
  ⟨fun h Y => h _ Y rfl, fun h X Y hXY => by rw [eq_ambientOfSepTuple hXY, h]⟩
theorem agreeOnTuples_ofLength {σ : AmbientPoints.allSeparatedTuples s .euclidean → ℝ}
    {σ' : SepTuple → ℝ} (h : AgreeOnSameTuples σ σ') (n : ℕ) :
    AgreeOnComponents (AmbientPoints.ofLength σ n) (fun X : SepTupleOfCard n => σ' ⟨n, X⟩) :=
  fun f X hX => h _ _ (congrArg (fun g => (⟨n, g⟩ : AmbientPoints.FunctionTuple s .euclidean))
    hX)
theorem functionals_coincide (s : Conventions.StandingParameters) : FunctionalsCoincide s := by
  refine ⟨fun σ => ⟨fun Y => σ (ambientOfSepTuple Y), agreeOnSameTuples_iff.2 fun _ => rfl⟩,
    fun σ' => ⟨fun X => σ' (sepTupleOfAmbient X), agreeOnSameTuples_iff.2 fun _ => rfl⟩,
    fun σ σ' h => ?_⟩
  have hempty : σ ⟨AmbientPoints.nilTuple s .euclidean,
      AmbientPoints.nilTuple_mem_allSeparatedTuples⟩ =
      σ' sepTupleNil := agreeOnSameTuples_iff.1 h sepTupleNil
  refine and_congr (by rw [hempty]) (forall₂_congr fun n _ => ?_)
  have h' := multilinearNotions_coincide s n _ _ (agreeOnTuples_ofLength h n)
  exact h'.1
theorem apply_restrictSeparated_eq {σ : AmbientPoints.allSeparatedTuples s .euclidean → ℝ}
    {σ' : SepTuple → ℝ} (h : AgreeOnSameTuples σ σ')
    {f : AmbientPoints.separatedTuples s .euclidean n} {X : SepTupleOfCard n}
    (hX : (f.1 : Fin n → (Fin 4 → ℝ) → ℝ) = X.1) (J : Finset (Fin n)) :
    σ (AmbientPoints.toAllSeparated (AmbientPoints.restrictSeparated f J)) =
      σ' ⟨J.card, sepRestrict X J⟩ :=
  h _ _ (congrArg (fun g : Fin n → (Fin 4 → ℝ) → ℝ =>
    (⟨J.card, fun k => g (J.orderEmbOfFin rfl k)⟩ :
      AmbientPoints.FunctionTuple s .euclidean)) hX)
theorem agreeOnTuples_connectedOf_cumulant
    {σ : AmbientPoints.allSeparatedTuples s .euclidean → ℝ}
    {σ' : SepTuple → ℝ} (h : AgreeOnSameTuples σ σ') (n : ℕ) :
    AgreeOnComponents (AmbientPoints.connectedOf σ n) (cumulant σ') := by
  intro f X hX
  refine Finset.sum_bij (fun π _ => π.parts) (fun π _ => ?_) (fun π _ π' _ e => ?_)
    (fun η hη => ?_) (fun π _ => ?_)
  · simp only [ClusterExpansion.SymGraph.partitions, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact isPartition_parts π
  · exact Finpartition.ext e
  · simp only [ClusterExpansion.SymGraph.partitions, Finset.mem_filter, Finset.mem_univ,
      true_and] at hη
    exact ⟨finpartitionOfIsPartition hη, Finset.mem_univ _, rfl⟩
  · simp only [SetPartition.blockCount]
    exact congrArg _ (Finset.prod_congr rfl fun J _ => apply_restrictSeparated_eq h hX J)
theorem agreeOnSameTuples_centred (F : AmbientPoints.ConnectedFamily s .euclidean)
    (G : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ)
    (hG : ∀ (n : ℕ) (hn : 2 ≤ n), AgreeOnComponents (F.fn n hn) (G n hn)) :
    AgreeOnSameTuples F.centred (centredOfCumulants G) := by
  refine agreeOnSameTuples_iff.2 fun Y => ?_
  rw [centredOfCumulants_eq_blockProductSum, blockProductSum]
  change ∑ π ∈ SetPartition.singletonFree Y.1, _ = _
  rw [← SetPartition.atLeastTwoPartitions_univ, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← Finset.prod_attach]
  refine Finset.prod_congr rfl fun J _ => ?_
  have h2 := SetPartition.two_le_card_of_mem_atLeastTwoPartitions π.2 J.2
  exact (dif_pos h2).trans (hG _ h2 _ _ rfl)
theorem cumulantFormulas_agree (s : Conventions.StandingParameters) : CumulantFormulasAgree s :=
  ⟨fun _ _ _ h n _ => agreeOnTuples_connectedOf_cumulant h n, agreeOnSameTuples_centred⟩
theorem euclidNormVec_mulVec {R : Matrix (Fin 4) (Fin 4) ℝ}
    (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    euclidNormVec (R.mulVec v) = euclidNormVec v := by apply _root_.YangMills.Construction.ConfigSpace.euclidNormVec_orth_mulVec <;> assumption
theorem euclidNormVec_toFun_sub (r : Motions.RigidMotion) (x y : Fin 4 → ℝ) :
    euclidNormVec (r.toFun x - r.toFun y) = euclidNormVec (x - y) := by apply _root_.YangMills.Construction.ConditionDefaults.isEuclidIsometry_rigidMotion <;> assumption
theorem isometries_are_rigidMotions
    (hY : Tower.OrthogonalMotions.Classification) (s : Conventions.StandingParameters) :
    IsometriesAreRigidMotions s := by
  ext m
  constructor
  · rintro ⟨r, hr, hrm⟩
    obtain ⟨R, hR, v, h⟩ := hY.2.1 m fun x y => by
      rw [← hrm x, ← hrm y]
      exact hr x y
    exact ⟨R, hR, v, h⟩
  · intro hm
    obtain ⟨r, rfl⟩ := Motions.RigidMotion.exists_toFun_eq hm
    exact ⟨⟨r.toFun, r.invFun, r.invFun_toFun, r.toFun_invFun⟩,
      fun x y => euclidNormVec_toFun_sub r x y, fun _ => rfl⟩
theorem allConjuncts_hold (hY : Tower.OrthogonalMotions.Classification) : AllConditionsHold :=
  fun s => ⟨fun n _ => ⟨tupleClasses_coincide s n, multilinearNotions_coincide s n⟩,
    families_coincide s, functionals_coincide s, cumulantFormulas_agree s,
    isometries_are_rigidMotions hY s⟩
end YangMills.Construction.TestSpaces.UnifiedSeparatedTuples
end
