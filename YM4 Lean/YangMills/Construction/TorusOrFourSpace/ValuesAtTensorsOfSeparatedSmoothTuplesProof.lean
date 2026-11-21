import YangMills.Construction.TorusOrFourSpace.FunctionalBoundedInTheSharpNormIsADistributionProof
import YangMills.Construction.TorusOrFourSpace.ValuesAtTensorsOfSeparatedSmoothTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.SeparatedTensors
theorem prop_of_sum_pieces {X : Type*} [AddCommMonoid X] {n : ℕ} (W P : Fin n → Set X)
    (Q : (Fin n → X) → Prop) (hP : ∀ l, P l ⊆ W l)
    (hzeroW : ∀ l, (0 : X) ∈ W l) (haddW : ∀ l u v, u ∈ W l → v ∈ W l → u + v ∈ W l)
    (hzero : ∀ h : Fin n → X, (∀ l, h l ∈ W l) → ∀ i, Q (Function.update h i 0))
    (hadd : ∀ h : Fin n → X, (∀ l, h l ∈ W l) → ∀ i u v, u ∈ W i → v ∈ W i →
      Q (Function.update h i u) → Q (Function.update h i v) →
        Q (Function.update h i (u + v)))
    (hbase : ∀ h : Fin n → X, (∀ l, h l ∈ P l) → Q h)
    (f : Fin n → X) (r : Fin n → ℕ) (g : ∀ l, Fin (r l) → X)
    (hg : ∀ l a, g l a ∈ P l) (hf : ∀ l, f l = ∑ a, g l a) : Q f := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.prop_of_finite_sums <;> assumption
variable {D : Params} {E : Kind}
theorem const_apply_zero_eq (y : E.Tuple D 1) :
    (fun _ => y ⟨0, (1 : ℕ+).pos⟩) = y := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.const_fin_one <;> assumption
theorem singleSet_eq_boxSet (A : Set (E.Pt D)) :
    Tuple.singleSet D E A =
      Tuple.boxSet D E (n := 1) fun _ => A := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.singleSet_eq_boxSet <;> assumption
theorem quotDist_self_nonpos (H3 : TupleFacts.AllFacts)
    (y : E.Pt D) : quotDist D E y y ≤ 0 := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.quotDist_self_nonpos <;> assumption
theorem mem_supportQ_of_ne_zero (H3 : TupleFacts.AllFacts)
    {u : E.Pt D → ℝ} {y : E.Pt D} (hy : u y ≠ 0) : y ∈ supportQ D E u :=
  fun _ hr => ⟨y, hy, lt_of_le_of_lt (quotDist_self_nonpos H3 y) hr⟩
theorem isC1Fn_of_isSmoothFn {u : E.Pt D → ℝ} (hu : IsSmoothFn D E u) :
    IsC1Fn D E u := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.isC1Fn_of_isSmoothFn <;> assumption
theorem cutoffTensor_mem_testFns (H2 : SmoothIffSmoothAsTuple)
    (H3 : TupleFacts.AllFacts) {n : ℕ+}
    {f : FnTuple D E (n : ℕ)} (hf : f ∈ sepC1Tuples D E (n : ℕ))
    (hs : ∀ i, IsSmoothFn D E (f i)) :
    Tuple.cutoffTensor D E f ∈ Tuple.testFns D E (pairwiseDistinct D E n) := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.cutoffTensor_mem <;> assumption
def TensorValueEq (S : Hierarchy D E) {n : ℕ+} (hn : 2 ≤ (n : ℕ))
    (T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ)
    (h : FnTuple D E (n : ℕ)) : Prop :=
  ∀ (hφ : h ∈ sepC1Tuples D E (n : ℕ))
    (hF : Tuple.cutoffTensor D E h ∈
      Tuple.testFns D E (pairwiseDistinct D E n)),
    T ⟨_, hF⟩ = ((S.func (n : ℕ) hn ⟨h, hφ⟩ : ℝ) : ℂ)
def smoothSupportedIn (A : Set (E.Pt D)) : Set (E.Pt D → ℝ) :=
  {u | IsSmoothFn D E u ∧ u ∈ c1SupportedIn D E A}
def ballPieces (K : Set (E.Pt D)) (η : ℝ) : Set (E.Pt D → ℝ) :=
  {g | g ∈ smoothSupportedIn K ∧ ∃ y ∈ K,
    (fun z => (g z : ℂ)) ∈ Tuple.singleTestFns D E (openBallAt D E y η)}
theorem cutoffTensor_update {n : ℕ+} (h : FnTuple D E (n : ℕ)) (i : Fin (n : ℕ))
    (w : E.Pt D → ℝ) (y : E.Tuple D n) :
    Tuple.cutoffTensor D E (Function.update h i w) y =
      (w (y i) : ℂ) * ∏ j ∈ Finset.univ.erase i, (h j (y j) : ℂ) := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.cutoffTensor_update <;> assumption
theorem update_mem_smoothSupportedIn {n : ℕ+} {A : Fin (n : ℕ) → Set (E.Pt D)}
    {h : FnTuple D E (n : ℕ)}
    (hh : ∀ l, h l ∈ smoothSupportedIn (A l)) (i : Fin (n : ℕ)) {w : E.Pt D → ℝ}
    (hw : w ∈ smoothSupportedIn (A i)) (l : Fin (n : ℕ)) :
    Function.update h i w l ∈ smoothSupportedIn (A l) := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.update_mem_smoothSupportedIn <;> assumption
theorem mem_sepC1Tuples_of_disjoint
    (H4 : DisjointProducts.Claim) {n : ℕ+}
    {A : Fin (n : ℕ) → Set (E.Pt D)} (hA : ∀ l l', l ≠ l' → Disjoint (A l) (A l'))
    {h : FnTuple D E (n : ℕ)} (hh : ∀ l, h l ∈ smoothSupportedIn (A l)) :
    h ∈ sepC1Tuples D E (n : ℕ) := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.mem_sepC1Tuples_of_smooth <;> assumption
theorem tensorValueEq_update_zero (H4 : DisjointProducts.Claim)
    (S : Hierarchy D E) {n : ℕ+} (hn : 2 ≤ (n : ℕ))
    {T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ}
    (hT : Tuple.IsDistrib T) (h : FnTuple D E (n : ℕ)) (i : Fin (n : ℕ)) :
    TensorValueEq S hn T (Function.update h i 0) := by
  intro hφ hF
  have hS := (H4 D E (n : ℕ) n.pos).2.2.2.1 (S.func (n : ℕ) hn) (S.multilinear _ hn)
    ⟨_, hφ⟩ i (by simp)
  have h0 : T ⟨_, hF⟩ = 0 := by
    have := hT.1.2 0 ⟨_, hF⟩ ⟨_, hF⟩ (by
      funext y
      simp [cutoffTensor_update])
    simpa using this
  rw [h0, hS]
  simp
theorem tensorValueEq_update_add (H2 : SmoothIffSmoothAsTuple)
    (H3 : TupleFacts.AllFacts)
    (H4 : DisjointProducts.Claim)
    (S : Hierarchy D E) {n : ℕ+} (hn : 2 ≤ (n : ℕ))
    {T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ}
    (hT : Tuple.IsDistrib T)
    {A : Fin (n : ℕ) → Set (E.Pt D)} (hA : ∀ l l', l ≠ l' → Disjoint (A l) (A l'))
    {h : FnTuple D E (n : ℕ)} (hh : ∀ l, h l ∈ smoothSupportedIn (A l)) (i : Fin (n : ℕ))
    {u v : E.Pt D → ℝ} (hu : u ∈ smoothSupportedIn (A i)) (hv : v ∈ smoothSupportedIn (A i))
    (gu : TensorValueEq S hn T (Function.update h i u))
    (gv : TensorValueEq S hn T (Function.update h i v)) :
    TensorValueEq S hn T (Function.update h i (u + v)) := by
  intro hφ hF
  have sepU := mem_sepC1Tuples_of_disjoint H4 hA (update_mem_smoothSupportedIn hh i hu)
  have sepV := mem_sepC1Tuples_of_disjoint H4 hA (update_mem_smoothSupportedIn hh i hv)
  have FU := cutoffTensor_mem_testFns H2 H3 sepU fun l => (update_mem_smoothSupportedIn hh i hu l).1
  have FV := cutoffTensor_mem_testFns H2 H3 sepV fun l => (update_mem_smoothSupportedIn hh i hv l).1
  have lin := hT.1.1 ⟨_, FU⟩ ⟨_, FV⟩ ⟨_, hF⟩ (by
    funext y
    simp only [Pi.add_apply, cutoffTensor_update]
    push_cast
    ring)
  have e : (1 : ℝ) • u + (1 : ℝ) • v = u + v := by simp
  have hw : Function.update h i ((1 : ℝ) • u + (1 : ℝ) • v) ∈ sepC1Tuples D E (n : ℕ) := by
    rw [e]
    exact hφ
  have nl := ((H4 D E (n : ℕ) n.pos).2.2.1 (S.func (n : ℕ) hn) (S.multilinear _ hn) A hA).2
    h (fun l _ => (hh l).2) i u hu.2 v hv.2 1 1 sepU sepV hw
  have e2 : S.func (n : ℕ) hn ⟨_, hφ⟩ = S.func (n : ℕ) hn ⟨_, hw⟩ :=
    congrArg _ (Subtype.ext (by simp only [e]))
  rw [lin, gu sepU FU, gv sepV FV, e2, nl]
  push_cast
  ring
theorem tensorValueEq_of_balls (S : Hierarchy D E) {n : ℕ+} (hn : 2 ≤ (n : ℕ))
    {T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ}
    (hT : S.IsOffDiagDistrib hn T) {η d : ℝ} {c : E.Tuple D n}
    (hadm : AdmissibleWith D E η d fun i => openBallAt D E (c i) η)
    {h : FnTuple D E (n : ℕ)}
    (hm : ∀ l, (fun z => (h l z : ℂ)) ∈
      Tuple.singleTestFns D E (openBallAt D E (c l) η)) :
    TensorValueEq S hn T h := by
  intro _ _
  obtain ⟨hsub, -, hval⟩ := hT.2 _ ⟨η, d, hadm⟩
  obtain ⟨_, _, e⟩ := hval h hm
  exact e
theorem exists_sum_ballPieces (H2 : SmoothIffSmoothAsTuple)
    (H3 : TupleFacts.AllFacts)
    (H5 : PartitionsOfUnity.Statement)
    {K : Set (E.Pt D)} (hK : IsCompactQ D E K) (hne : K.Nonempty) {η : ℝ} (hη : 0 < η)
    (hopen : ∀ y ∈ K, IsOpenQ D E (openBallAt D E y η))
    {u : E.Pt D → ℝ} (hu : IsSmoothFn D E u) (hsupp : supportQ D E u ⊆ K) :
    ∃ (r : ℕ) (g : Fin r → E.Pt D → ℝ), (∀ a, g a ∈ ballPieces K η) ∧ u = ∑ a, g a := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.exists_ball_pieces <;> assumption
theorem exists_uniform_separation (H4 : DisjointProducts.Claim) {n : ℕ+}
    {A : Fin (n : ℕ) → Set (E.Pt D)} (hK : ∀ l, IsCompactQ D E (A l))
    (hA : ∀ l l', l ≠ l' → Disjoint (A l) (A l')) (hne : ∀ l, (A l).Nonempty) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i k, i ≠ k → ∀ y ∈ A i, ∀ y' ∈ A k, δ ≤ quotDist D E y y' := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.exists_uniform_sep <;> assumption
theorem sepSmoothTensorValues_holds (H1 : AdmissibleProductFacts)
    (H2 : SmoothIffSmoothAsTuple)
    (H3 : TupleFacts.AllFacts)
    (H4 : DisjointProducts.Claim)
    (H5 : PartitionsOfUnity.Statement) : SepSmoothTensorValues := by
  intro D E C S _ n hn T hT f hf hs
  have hF := cutoffTensor_mem_testFns H2 H3 hf hs
  refine ⟨hf, hF, ?_⟩
  suffices hg : TensorValueEq S hn T f from hg hf hF
  have hdisj : ∀ l l', l ≠ l' → Disjoint (supportQ D E (f l)) (supportQ D E (f l')) := hf.2.2
  by_cases hz : ∃ i, f i = 0
  · obtain ⟨i, hi⟩ := hz
    have e : Function.update f i 0 = f := by
      rw [← hi]
      exact Function.update_eq_self _ _
    have h1 := tensorValueEq_update_zero H4 S hn hT.1 f i
    rwa [e] at h1
  have hne : ∀ l, (supportQ D E (f l)).Nonempty := fun l => by
    have h0 : f l ≠ 0 := fun h => hz ⟨l, h⟩
    obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
    exact ⟨y, mem_supportQ_of_ne_zero H3 hy⟩
  obtain ⟨δ, hδ, hsep⟩ := exists_uniform_separation H4 hf.2.1 hdisj hne
  obtain ⟨η, hη, hadm⟩ := (H1 D E n).2.2.1 δ hδ
  have hadm' : ∀ c : E.Tuple D n, (∀ i, c i ∈ supportQ D E (f i)) →
      AdmissibleWith D E η (δ / 3) fun i => openBallAt D E (c i) η := fun c hc =>
    hadm c fun i k e => hsep i k e _ (hc i) _ (hc k)
  choose c₀ hc₀ using hne
  have hopen : ∀ l, ∀ y ∈ supportQ D E (f l), IsOpenQ D E (openBallAt D E y η) := by
    classical
    intro l y hy
    have h1 := (hadm' (Function.update c₀ l y) fun i => by
      by_cases e : i = l
      · subst e
        simpa using hy
      · simpa [Function.update_of_ne e] using hc₀ i).isOpen_mem l
    simpa using h1
  have hpieces := fun l => exists_sum_ballPieces H2 H3 H5 (hf.2.1 l) ⟨_, hc₀ l⟩ hη (hopen l) (hs l)
    subset_rfl
  choose r g hg hsum using hpieces
  refine prop_of_sum_pieces (fun l => smoothSupportedIn (supportQ D E (f l)))
    (fun l => ballPieces (supportQ D E (f l)) η) (TensorValueEq S hn T) (fun l _ hp => hp.1)
    ?_ ?_ (fun h _ i => tensorValueEq_update_zero H4 S hn hT.1 h i)
    (fun h hh i u v hu hv gu gv => tensorValueEq_update_add H2 H3 H4 S hn hT.1 hdisj hh i hu hv gu gv)
    ?_ f r g hg hsum
  · intro l
    obtain ⟨Wl, hWl⟩ := (H4 D E (n : ℕ) n.pos).1.1 (supportQ D E (f l))
    refine ⟨contDiff_const, ?_⟩
    rw [← hWl]
    exact Wl.zero_mem
  · intro l u v hu hv
    obtain ⟨Wl, hWl⟩ := (H4 D E (n : ℕ) n.pos).1.1 (supportQ D E (f l))
    refine ⟨ContDiff.add hu.1 hv.1, ?_⟩
    have hu2 := hu.2
    have hv2 := hv.2
    rw [← hWl] at hu2 hv2 ⊢
    exact Wl.add_mem hu2 hv2
  · intro h hh
    have hc : ∀ l, ∃ y ∈ supportQ D E (f l),
        (fun z => (h l z : ℂ)) ∈ Tuple.singleTestFns D E (openBallAt D E y η) :=
      fun l => (hh l).2
    choose c hcA hcm using hc
    exact tensorValueEq_of_balls S hn hT (hadm' c hcA) hcm
end YangMills.Construction.PeriodicSpace.Kind.SeparatedTensors
