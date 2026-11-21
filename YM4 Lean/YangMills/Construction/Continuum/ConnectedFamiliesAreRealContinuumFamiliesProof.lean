import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.Continuum.ConnectedFamiliesAreRealContinuumFamilies
import YangMills.Construction.Continuum.OneClassOfTuplesAndOneNotionOfMultilinearityProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.ReflectionPositivity.AxisMirror (MirrorData Ambient)
open YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient (compactC1 separatedN
  compactC1SuppIn evalOrZero IsSeparatedMultilinear ConnectedFamily)
open YangMills.Construction.TestFunctions (setDistR4 HasSeparatedSupportsR4)
noncomputable section
namespace YangMills.Construction.SchwingerFunctions.RealConnected
variable {n : ℕ}
def tupleValue {D : MirrorData} (φ : separatedN D Ambient.euclidean n → ℝ)
    (f : Fin n → (Fin 4 → ℝ) → ℝ) : ℝ :=
  evalOrZero φ (List.ofFn f)
theorem closedSupport_euclidean (D : MirrorData) (f : (Fin 4 → ℝ) → ℝ) :
    (Ambient.closedSupport D Ambient.euclidean f : Set (Fin 4 → ℝ)) = tsupport f := by apply _root_.YangMills.Construction.R4TupleForms.closedSupport_euclidean_eq <;> assumption
theorem mem_compactC1_euclidean_iff (D : MirrorData) (f : (Fin 4 → ℝ) → ℝ) :
    f ∈ compactC1 D ℝ Ambient.euclidean ↔ IsC1c f := by
  refine and_congr Iff.rfl ?_
  rw [closedSupport_euclidean D f]
  exact SeparatedTuplesR4.isCompactWrt_euclid_iff (fun _ _ => rfl) _
theorem mem_compactC1SuppIn_euclidean_iff (D : MirrorData) {A : Set (Fin 4 → ℝ)}
    {f : (Fin 4 → ℝ) → ℝ} :
    f ∈ compactC1SuppIn D Ambient.euclidean A ↔ IsC1c f ∧ tsupport f ⊆ A := by
  refine and_congr (mem_compactC1_euclidean_iff D f) ?_
  rw [closedSupport_euclidean D f]
  exact Iff.rfl
theorem setDistR4_mono {A A' B B' : Set (Fin 4 → ℝ)} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    setDistR4 A B ≤ setDistR4 A' B' := by apply _root_.YangMills.Construction.TestSpaces.UnifiedSeparatedTuples.setDistR4_anti <;> assumption
theorem exists_pos_real_le_of_finite {ι : Type*} [Finite ι] (g : ι → ENNReal)
    (h : ∀ i, 0 < g i) : ∃ d : ℝ, 0 < d ∧ ∀ i, ENNReal.ofReal d ≤ g i := by apply _root_.YangMills.Construction.TestSpaces.UnifiedSeparatedTuples.exists_pos_ofReal_le_of_finite <;> assumption
theorem pairwiseSeparated_of_setDistR4_pos {C : Fin n → Set (Fin 4 → ℝ)}
    (h : Pairwise fun i j => 0 < setDistR4 (C i) (C j)) : PairwiseSeparated C := by
  obtain ⟨d, hd, hle⟩ := exists_pos_real_le_of_finite
    (ι := {p : Fin n × Fin n // p.1 ≠ p.2})
    (fun p => setDistR4 (C p.1.1) (C p.1.2)) (fun p => h p.2)
  exact ⟨d, hd, fun i k hik => hle ⟨(i, k), hik⟩⟩
theorem posDistOfCompactDisjoint_holds : PosDistOfCompactDisjoint := by
  refine ⟨fun Q Q' hQ hQ' h =>
    SeparatedTuplesR4.setDistR4_pos_of_disjoint hQ hQ'.isClosed h, fun A B h => ?_⟩
  rw [Set.disjoint_left]
  intro x hA hB
  have h₁ : setDistR4 A B ≤ ENNReal.ofReal (TorusMetric.euclidNormVec (x - x)) :=
    iInf₂_le_of_le x hA (iInf₂_le x hB)
  have h₂ : ENNReal.ofReal (TorusMetric.euclidNormVec (x - x)) = 0 := by
    simp [TorusMetric.euclidNormVec]
  rw [h₂] at h₁
  exact absurd h (not_lt.2 h₁)
theorem isAdmissibleTuple_iff (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    IsAdmissibleTuple f ↔ (∀ i, IsC1c (f i)) ∧
      ∀ i k, i ≠ k → Disjoint (tsupport (f i)) (tsupport (f k)) := by
  constructor
  · rintro ⟨h₁, d, hd, hsep⟩
    exact ⟨h₁, fun i k hik => posDistOfCompactDisjoint_holds.2 _ _
      ((ENNReal.ofReal_pos.2 hd).trans_le (hsep i k hik))⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    obtain ⟨d, hd, hle⟩ := pairwiseSeparated_of_setDistR4_pos (C := fun i => tsupport (f i))
      (fun i k hik => posDistOfCompactDisjoint_holds.1 _ _ (h₁ i).2.isCompact (h₁ k).2.isCompact
        (h₂ i k hik))
    exact ⟨d, And.intro hd hle⟩
theorem ofFn_mem_separatedN_iff (D : MirrorData) (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    List.ofFn f ∈ separatedN D Ambient.euclidean n ↔ IsAdmissibleTuple f := by
  rw [isAdmissibleTuple_iff]
  have hp : List.Pairwise (fun a b : (Fin 4 → ℝ) → ℝ =>
        Disjoint (Ambient.closedSupport D Ambient.euclidean a)
          (Ambient.closedSupport D Ambient.euclidean b)) (List.ofFn f) ↔
      ∀ ⦃i k : Fin n⦄, i < k →
        Disjoint (Ambient.closedSupport D Ambient.euclidean (f i))
          (Ambient.closedSupport D Ambient.euclidean (f k)) :=
    List.pairwise_ofFn
  constructor
  · rintro ⟨-, h₁, h₂⟩
    refine ⟨fun i => (mem_compactC1_euclidean_iff D _).1
      (h₁ _ ((List.mem_ofFn' _ _).2 ⟨i, rfl⟩)), ?_⟩
    intro i k hik
    rcases lt_or_gt_of_ne hik with h | h
    · have h₃ := hp.1 h₂ h
      rwa [closedSupport_euclidean D, closedSupport_euclidean D] at h₃
    · have h₃ := hp.1 h₂ h
      rw [closedSupport_euclidean D, closedSupport_euclidean D] at h₃
      exact h₃.symm
  · rintro ⟨h₁, h₂⟩
    refine ⟨List.length_ofFn, fun g hg => ?_, hp.2 fun i k hik => ?_⟩
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
      exact (mem_compactC1_euclidean_iff D _).2 (h₁ i)
    · rw [closedSupport_euclidean D, closedSupport_euclidean D]
      exact h₂ i k hik.ne
theorem separatedSupportsIffMem_holds : SeparatedSupportsIffMem := by
  intro D n _ f
  constructor
  · rintro ⟨h₁, h₂⟩
    exact (ofFn_mem_separatedN_iff D f).2 ⟨fun i => (mem_compactC1_euclidean_iff D _).1 (h₁ i), h₂⟩
  · intro h
    obtain ⟨h₁, h₂⟩ := (ofFn_mem_separatedN_iff D f).1 h
    exact ⟨fun i => (mem_compactC1_euclidean_iff D _).2 (h₁ i), h₂⟩
theorem compactProductsMem_holds : CompactProductsMem := by
  intro D n _ Q hQ f hf
  exact Ambient.ofFn_mem_separatedN D Ambient.euclidean hQ.2 hf
theorem linear_of_linearOnCompactProducts {D : MirrorData}
    {Ψ : separatedN D Ambient.euclidean n → ℝ} (h : IsLinearOnCompactProducts D Ψ)
    (A : Fin n → Set (Fin 4 → ℝ)) (hA : Pairwise fun i j => 0 < setDistR4 (A i) (A j))
    (f : Fin n → (Fin 4 → ℝ) → ℝ) (hf : ∀ i, f i ∈ compactC1SuppIn D Ambient.euclidean (A i))
    (i : Fin n) (g : (Fin 4 → ℝ) → ℝ) (hg : g ∈ compactC1SuppIn D Ambient.euclidean (A i))
    (s t : ℝ) :
    tupleValue Ψ (Function.update f i (s • f i + t • g)) =
      s * tupleValue Ψ f + t * tupleValue Ψ (Function.update f i g) := by
  have hf' : ∀ k, IsC1c (f k) ∧ tsupport (f k) ⊆ A k :=
    fun k => (mem_compactC1SuppIn_euclidean_iff D).1 (hf k)
  have hg' : IsC1c g ∧ tsupport g ⊆ A i := (mem_compactC1SuppIn_euclidean_iff D).1 hg
  classical
  obtain ⟨Q, hQi, hQk⟩ : ∃ Q : Fin n → Set (Fin 4 → ℝ),
      Q i = tsupport (f i) ∪ tsupport g ∧ ∀ k, k ≠ i → Q k = tsupport (f k) :=
    ⟨fun k => if k = i then tsupport (f i) ∪ tsupport g else tsupport (f k), if_pos rfl,
      fun k hk => if_neg hk⟩
  have hQA : ∀ k, Q k ⊆ A k := by
    intro k
    by_cases hk : k = i
    · rw [hk, hQi]
      exact union_subset (hf' i).2 hg'.2
    · rw [hQk k hk]
      exact (hf' k).2
  have hcompact : ∀ k, IsCompact (Q k) := by
    intro k
    by_cases hk : k = i
    · rw [hk, hQi]
      exact (hf' i).1.2.isCompact.union hg'.1.2.isCompact
    · rw [hQk k hk]
      exact (hf' k).1.2.isCompact
  have hfQ : ∀ k, f k ∈ compactC1SuppIn D Ambient.euclidean (Q k) := by
    intro k
    refine (mem_compactC1SuppIn_euclidean_iff D).2 ⟨(hf' k).1, ?_⟩
    by_cases hk : k = i
    · rw [hk, hQi]
      exact subset_union_left
    · rw [hQk k hk]
  have hgQ : g ∈ compactC1SuppIn D Ambient.euclidean (Q i) :=
    (mem_compactC1SuppIn_euclidean_iff D).2 ⟨hg'.1, by rw [hQi]; exact subset_union_right⟩
  exact h Q ⟨hcompact, fun k l hkl => lt_of_lt_of_le (hA hkl)
    (setDistR4_mono (hQA k) (hQA l))⟩ f hfQ i g hgQ s t
theorem multilinearIffLinearOnCompactProducts_holds :
    MultilinearIffLinearOnCompactProducts := by
  intro D n _ Ψ
  constructor
  · intro h Q hQ f hf i g hg s t
    exact h Q hQ.2 f hf i g hg s t
  · intro h A hA f hf i g hg s t
    exact linear_of_linearOnCompactProducts h A hA f hf i g hg s t
theorem isC1c_linearCombination {C : Set (Fin 4 → ℝ)} (hC : IsCompact C)
    {g h : (Fin 4 → ℝ) → ℝ} (hg : IsC1c g) (hgC : tsupport g ⊆ C)
    (hh : IsC1c h) (hhC : tsupport h ⊆ C) (a b : ℝ) :
    IsC1c (a • g + b • h) ∧ tsupport (a • g + b • h) ⊆ C := by apply _root_.YangMills.Construction.TestSpaces.UnifiedSeparatedTuples.linearCombination_isC1c_and_tsupport_subset <;> assumption
theorem isAdmissibleTuple_of_supportedIn {C : Fin n → Set (Fin 4 → ℝ)} (hC : PairwiseSeparated C)
    {f : Fin n → (Fin 4 → ℝ) → ℝ} (hf : ∀ k, IsC1c (f k) ∧ tsupport (f k) ⊆ C k) :
    IsAdmissibleTuple f := by
  obtain ⟨d, hd, hle⟩ := hC
  refine ⟨fun k => (hf k).1, d, ?_⟩
  exact And.intro hd fun i k hik =>
    (hle i k hik).trans (setDistR4_mono (hf i).2 (hf k).2)
theorem update_supportedIn {C : Fin n → Set (Fin 4 → ℝ)} {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (hf : ∀ k, IsC1c (f k) ∧ tsupport (f k) ⊆ C k) {i : Fin n}
    {g : (Fin 4 → ℝ) → ℝ} (hg : IsC1c g) (hgC : tsupport g ⊆ C i) (k : Fin n) :
    IsC1c (Function.update f i g k) ∧
      tsupport (Function.update f i g k) ⊆ C k := by apply _root_.YangMills.Construction.TestSpaces.UnifiedSeparatedTuples.update_isC1c_and_tsupport_subset <;> assumption
theorem isContinuumSchwingerFamily_of_matchesConnected {D : MirrorData}
    {S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ}
    {F : ConnectedFamily D Ambient.euclidean} (hS : MatchesConnected S F) :
    IsContinuumSchwingerFamily S := by
  intro n hn C hC hsep f hf i g h a b hg hgC hh hhC
  have hpos : Pairwise fun k l => 0 < Ambient.setDist D Ambient.euclidean
      (C k) (C l) := by
    obtain ⟨d, hd, hle⟩ := hsep
    exact fun k l hkl => lt_of_lt_of_le (ENNReal.ofReal_pos.2 hd) (hle k l hkl)
  have hcomb := isC1c_linearCombination (hC i) hg hgC hh hhC a b
  have t₁ := isAdmissibleTuple_of_supportedIn hsep (update_supportedIn hf hcomb.1 hcomb.2)
  have t₂ := isAdmissibleTuple_of_supportedIn hsep (update_supportedIn hf hg hgC)
  have t₃ := isAdmissibleTuple_of_supportedIn hsep (update_supportedIn hf hh hhC)
  have hlin : tupleValue (F.fn n hn) (Function.update (Function.update f i g) i
        (a • Function.update f i g i + b • h)) =
      a * tupleValue (F.fn n hn) (Function.update f i g) +
        b * tupleValue (F.fn n hn) (Function.update (Function.update f i g) i h) :=
    F.fn_multilinear n hn C hpos (Function.update f i g)
      (fun k => (mem_compactC1SuppIn_euclidean_iff D).2 (update_supportedIn hf hg hgC k)) i h
      ((mem_compactC1SuppIn_euclidean_iff D).2 ⟨hh, hhC⟩) a b
  simp only [Function.update_self, Function.update_idem] at hlin
  have r₁ : S n (Function.update f i (a • g + b • h)) =
      (tupleValue (F.fn n hn) (Function.update f i (a • g + b • h)) : ℝ) := hS n hn _ t₁
  have r₂ : S n (Function.update f i g) =
      (tupleValue (F.fn n hn) (Function.update f i g) : ℝ) := hS n hn _ t₂
  have r₃ : S n (Function.update f i h) =
      (tupleValue (F.fn n hn) (Function.update f i h) : ℝ) := hS n hn _ t₃
  rw [r₁, r₂, r₃, hlin]
  simp only [Complex.ofReal_add, Complex.ofReal_mul]
theorem isRealValued_of_matchesConnected {D : MirrorData}
    {S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ}
    {F : ConnectedFamily D Ambient.euclidean} (hS : MatchesConnected S F) :
    IsRealValued S := fun n hn f hf => by
  rw [hS n hn f hf]
  exact Complex.ofReal_im _
def ofConnected {D : MirrorData} (F : ConnectedFamily D Ambient.euclidean) (n : ℕ)
    (f : Fin n → (Fin 4 → ℝ) → ℝ) : ℂ :=
  open Classical in if hn : 2 ≤ n then ((evalOrZero (F.fn n hn) (List.ofFn f) : ℝ) : ℂ) else 0
theorem matchesConnected_ofConnected {D : MirrorData} (F : ConnectedFamily D Ambient.euclidean) :
    MatchesConnected (ofConnected F) F := fun _ hn _ _ => dif_pos hn
theorem exists_ofFn_eq {D : MirrorData} {X : Ambient.FnList D Ambient.euclidean}
    (hX : X ∈ separatedN D Ambient.euclidean n) :
    ∃ f : Fin n → (Fin 4 → ℝ) → ℝ, List.ofFn f = X := by
  obtain ⟨rfl, -⟩ := hX
  exact ⟨X.get, List.ofFn_get X⟩
def components {D : MirrorData} (X : separatedN D Ambient.euclidean n) :
    Fin n → (Fin 4 → ℝ) → ℝ :=
  Classical.choose (exists_ofFn_eq X.2)
theorem ofFn_components {D : MirrorData} (X : separatedN D Ambient.euclidean n) :
    List.ofFn (components X) = X.1 :=
  Classical.choose_spec (exists_ofFn_eq X.2)
theorem mem_separatedN_of_eq_val {D : MirrorData} {X : separatedN D Ambient.euclidean n}
    {Y : Ambient.FnList D Ambient.euclidean} (h : Y = X.1) :
    Y ∈ separatedN D Ambient.euclidean n := by
  subst h
  exact X.2
theorem evalOrZero_of_eq_val {D : MirrorData} (φ : separatedN D Ambient.euclidean n → ℝ)
    {X : separatedN D Ambient.euclidean n}
    {Y : Ambient.FnList D Ambient.euclidean} (h : Y = X.1) :
    evalOrZero φ Y = φ X := by
  subst h
  exact dif_pos X.2
theorem tupleValue_components {D : MirrorData} (φ : separatedN D Ambient.euclidean n → ℝ)
    (X : separatedN D Ambient.euclidean n) : tupleValue φ (components X) = φ X :=
  evalOrZero_of_eq_val φ (ofFn_components X)
def realPart (D : MirrorData) (S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ) (n : ℕ)
    (X : separatedN D Ambient.euclidean n) : ℝ :=
  (S n (components X)).re
theorem tupleValue_realPart (D : MirrorData) (S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ)
    {f : Fin n → (Fin 4 → ℝ) → ℝ} (hf : IsAdmissibleTuple f) :
    tupleValue (realPart D S n) f = (S n f).re := by
  have hm := (ofFn_mem_separatedN_iff D f).2 hf
  have he : components (⟨List.ofFn f, hm⟩ : separatedN D Ambient.euclidean n) = f :=
    List.ofFn_injective (ofFn_components _)
  have hv : tupleValue (realPart D S n) f = realPart D S n ⟨List.ofFn f, hm⟩ := dif_pos hm
  rw [hv, realPart, he]
theorem realPart_isSeparatedMultilinear (D : MirrorData)
    {S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ}
    (hS : IsContinuumSchwingerFamily S) (n : ℕ) (hn : 2 ≤ n) :
    IsSeparatedMultilinear D Ambient.euclidean (realPart D S n) := by
  refine (multilinearIffLinearOnCompactProducts_holds D n (by omega) _).2 ?_
  intro Q hQ f hf i g hg s t
  have hf' : ∀ k, IsC1c (f k) ∧ tsupport (f k) ⊆ Q k :=
    fun k => (mem_compactC1SuppIn_euclidean_iff D).1 (hf k)
  have hg' : IsC1c g ∧ tsupport g ⊆ Q i := (mem_compactC1SuppIn_euclidean_iff D).1 hg
  have hsep := pairwiseSeparated_of_setDistR4_pos hQ.2
  have hcomb := isC1c_linearCombination (hQ.1 i) (hf' i).1 (hf' i).2 hg'.1 hg'.2 s t
  have t₁ := isAdmissibleTuple_of_supportedIn hsep (update_supportedIn hf' hcomb.1 hcomb.2)
  have t₂ := isAdmissibleTuple_of_supportedIn hsep hf'
  have t₃ := isAdmissibleTuple_of_supportedIn hsep (update_supportedIn hf' hg'.1 hg'.2)
  have hlin := hS n hn Q hQ.1 hsep f hf' i (f i) g s t (hf' i).1 (hf' i).2 hg'.1 hg'.2
  rw [Function.update_eq_self] at hlin
  exact show tupleValue (realPart D S n) (Function.update f i (s • f i + t • g)) =
      s * tupleValue (realPart D S n) f +
        t * tupleValue (realPart D S n) (Function.update f i g) from by
    rw [tupleValue_realPart D S t₁, tupleValue_realPart D S t₂, tupleValue_realPart D S t₃, hlin]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
def toConnectedFamily (D : MirrorData) {S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ}
    (hS : IsContinuumSchwingerFamily S) : ConnectedFamily D Ambient.euclidean where
  fn n _ := realPart D S n
  fn_multilinear n hn := realPart_isSeparatedMultilinear D hS n hn
theorem matchesConnected_toConnectedFamily (D : MirrorData)
    {S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ}
    (hS : IsContinuumSchwingerFamily S) (hr : IsRealValued S) :
    MatchesConnected S (toConnectedFamily D hS) := by
  intro n hn f hf
  have hv : tupleValue ((toConnectedFamily D hS).fn n hn) f = (S n f).re :=
    tupleValue_realPart D S hf
  exact show S n f = (tupleValue ((toConnectedFamily D hS).fn n hn) f : ℝ) from by
    rw [hv]
    exact Complex.ext (by simp) (by simpa using hr n hn f hf)
theorem connectedFamily_eq_of_matchesConnected {D : MirrorData}
    {S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → ℝ) → ℂ}
    {F F' : ConnectedFamily D Ambient.euclidean} (h : MatchesConnected S F)
    (h' : MatchesConnected S F') : F = F' := by
  have key : F.fn = F'.fn := by
    funext n hn X
    have ht := (ofFn_mem_separatedN_iff D _).1 (mem_separatedN_of_eq_val (ofFn_components X))
    have h₃ : tupleValue (F.fn n hn) (components X) = tupleValue (F'.fn n hn) (components X) :=
      Complex.ofReal_injective ((h n hn _ ht).symm.trans (h' n hn _ ht))
    rwa [tupleValue_components, tupleValue_components] at h₃
  cases F
  cases F'
  dsimp only at key
  subst key
  rfl
theorem connectedFamiliesCorrespond_holds : ConnectedFamiliesCorrespond := fun D =>
  ⟨fun F => ⟨⟨ofConnected F, matchesConnected_ofConnected F⟩, fun _ h =>
      ⟨isContinuumSchwingerFamily_of_matchesConnected h, isRealValued_of_matchesConnected h⟩⟩,
    fun _ hS hr => ⟨toConnectedFamily D hS, matchesConnected_toConnectedFamily D hS hr,
      fun _ h' => connectedFamily_eq_of_matchesConnected h'
        (matchesConnected_toConnectedFamily D hS hr)⟩⟩
theorem connectedRealFamilies_holds : ConnectedRealFamilies :=
  ⟨posDistOfCompactDisjoint_holds, separatedSupportsIffMem_holds,
    compactProductsMem_holds, multilinearIffLinearOnCompactProducts_holds,
    connectedFamiliesCorrespond_holds⟩
end YangMills.Construction.SchwingerFunctions.RealConnected
