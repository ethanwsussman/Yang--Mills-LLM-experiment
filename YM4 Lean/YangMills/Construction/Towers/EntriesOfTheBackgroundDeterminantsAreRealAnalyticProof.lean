import YangMills.Construction.Towers.BackgroundFormOfTheFunctionalOnASideProof
import YangMills.Construction.Towers.BackgroundGaugeFunctionalIsFormedAtTheTrivialPoint
import YangMills.Construction.Towers.EntriesOfTheBackgroundDeterminantsAreRealAnalytic
import YangMills.Construction.Towers.IteratesOfTheCovariantAveragesHaveRealAnalyticEntries
import YangMills.Construction.Towers.SumsProductsAndCompositesOfRealAnalyticFunctions
import YangMills.Construction.Towers.TermsOfTheBackgroundOperatorAreRealAnalytic
import Mathlib
set_option autoImplicit false
open Set Filter
open YangMills.Construction.Matrices
open YangMills.Construction.Tower
open YangMills.Construction.Tower.RealQuadraticTransposes
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.BackgroundDeterminants
def realTraceForm (X : ComplexMatrix2) : ComplexMatrix2 →ₗ[ℝ] ℝ where
  toFun Y := (ComplexMatrix2.halfTrace (X * Y)).re
  map_add' Y Y' := by
    simp [ComplexMatrix2.halfTrace, mul_add, Matrix.trace_add]
  map_smul' c Y := by
    simp [ComplexMatrix2.halfTrace, Matrix.trace_smul, ComplexMatrix2.fullTrace]
    ring
def realPairingForm {ι : Type*} [Fintype ι] (f : ι → ComplexMatrix2) :
    (ι → ComplexMatrix2) →ₗ[ℝ] ℝ :=
  ∑ i, realTraceForm (f i) ∘ₗ LinearMap.proj i
theorem realPairingForm_apply {ι : Type*} [Fintype ι] (f A : ι → ComplexMatrix2) :
    realPairingForm f A = ∑ i, realTraceForm (f i) (A i) := by
  simp [realPairingForm, LinearMap.sum_apply]
theorem traceFinsumPairing_re {ι : Type*} [Fintype ι] (f A : ι → ComplexMatrix2) :
    (traceFinsumPairing f A).re = realPairingForm f A := by
  rw [realPairingForm_apply, traceFinsumPairing, finsum_eq_sum_of_fintype, Complex.re_sum]
  rfl
def edgeRealForm {L n k j : ℕ} [Fintype (PositiveEdge L n k j)] (x : Edge L n k j → ComplexMatrix2) :
    (Edge L n k j → ComplexMatrix2) →ₗ[ℝ] ℝ :=
  realPairingForm (restrictToPositiveEdges x) ∘ₗ
    LinearMap.funLeft ℝ ComplexMatrix2 fun c : PositiveEdge L n k j => (c.1 : Edge L n k j)
theorem edgeRealForm_eq {L n k j : ℕ} [Fintype (PositiveEdge L n k j)]
    (x A : Edge L n k j → ComplexMatrix2) : edgeRealForm x A = (edgeFormPairing x A).re :=
  (traceFinsumPairing_re _ _).symm
theorem exists_orthonormal_expansion {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (c : InnerProductSpace.Core ℝ V) :
    ∃ (d : ℕ) (e : Fin d → V), (∀ x : V, x = ∑ a, c.inner (e a) x • e a) ∧
      ∀ x y : V, c.inner x y = ∑ a, c.inner x (e a) * c.inner (e a) y := by
  letI := c.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c.toCore
  refine ⟨_, stdOrthonormalBasis ℝ V, fun x => ?_, fun x y => ?_⟩
  · exact ((stdOrthonormalBasis ℝ V).sum_repr' x).symm
  · exact ((stdOrthonormalBasis ℝ V).sum_inner_mul_inner x y).symm
theorem core_inner_comm {V : Type} [AddCommGroup V] [Module ℝ V] (c : InnerProductSpace.Core ℝ V)
    (x y : V) : c.inner x y = c.inner y x := by
  simpa using c.conj_inner_symm y x
theorem core_inner_sum_left {V : Type} [AddCommGroup V] [Module ℝ V]
    (c : InnerProductSpace.Core ℝ V)
    {ι : Type*} (s : Finset ι) (t : ι → ℝ) (x : ι → V) (y : V) :
    c.inner (∑ a ∈ s, t a • x a) y = ∑ a ∈ s, t a * c.inner (x a) y := by
  letI := c.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c.toCore
  change inner ℝ (∑ a ∈ s, t a • x a) y = ∑ a ∈ s, t a * inner ℝ (x a) y
  simp [sum_inner, inner_smul_left]
theorem coe_eq_sum_inner_smul {α : Type} {p : Submodule ℝ (α → ComplexMatrix2)} {d : ℕ}
    (c : InnerProductSpace.Core ℝ p) {e : Fin d → p}
    (h : ∀ x : p, x = ∑ a, c.inner (e a) x • e a)
    (x : p) : (x : α → ComplexMatrix2) = ∑ a, c.inner (e a) x • (e a : α → ComplexMatrix2) := by
  conv_lhs => rw [h x]
  simp
section Brackets
variable {L n k : ℕ}
def edgeBracket (u x y z : ComplexMatrix2) : ComplexMatrix2 :=
  (Complex.I / 2) • ⁅x + ComplexMatrix2.conjugateBy u y, z⁆
theorem edgeBracket_add_left (u x x' y y' z : ComplexMatrix2) :
    edgeBracket u (x + x') (y + y') z = edgeBracket u x y z + edgeBracket u x' y' z := by
  simp only [edgeBracket, ComplexMatrix2.conjugateBy, Ring.lie_def, mul_add, add_mul]
  module
theorem edgeBracket_smul_left (c : ℝ) (u x y z : ComplexMatrix2) :
    edgeBracket u (c • x) (c • y) z = c • edgeBracket u x y z := by
  simp only [edgeBracket, ComplexMatrix2.conjugateBy, Ring.lie_def, mul_add, add_mul,
    ← Complex.coe_smul, mul_smul_comm, smul_mul_assoc]
  module
theorem edgeBracket_add_right (u x y z z' : ComplexMatrix2) :
    edgeBracket u x y (z + z') = edgeBracket u x y z + edgeBracket u x y z' := by
  simp only [edgeBracket, Ring.lie_def, mul_add, add_mul]
  module
theorem edgeBracket_smul_right (c : ℝ) (u x y z : ComplexMatrix2) :
    edgeBracket u x y (c • z) = c • edgeBracket u x y z := by
  simp only [edgeBracket, Ring.lie_def, ← Complex.coe_smul, mul_smul_comm, smul_mul_assoc]
  module
def extendOddlyLinear : (Edge L n k 0 → ComplexMatrix2) →ₗ[ℝ] Edge L n k 0 → ComplexMatrix2 where
  toFun := extendOddly
  map_add' f g := by
    funext b
    simp only [extendOddly, Pi.add_apply]
    split_ifs
    · rfl
    · abel
  map_smul' c f := by
    funext b
    simp only [extendOddly, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · rfl
    · simp
def bracketValues (U : Edge L n k 0 → ComplexMatrix2) (l : Vertex L n k 0 → ComplexMatrix2)
    (B : Edge L n k 0 → ComplexMatrix2) : Edge L n k 0 → ComplexMatrix2 :=
  fun b => edgeBracket (U b) (l b.source) (l b.target) (B b)
theorem bracketTerm_eq (U : Edge L n k 0 → ComplexMatrix2) (l : Vertex L n k 0 → ComplexMatrix2)
    (B : Edge L n k 0 → ComplexMatrix2) :
    bracketTerm U l B = extendOddlyLinear (bracketValues U l B) := rfl
def bracketBilinear (U : Edge L n k 0 → ComplexMatrix2) :
    (Vertex L n k 0 → ComplexMatrix2) →ₗ[ℝ] (Edge L n k 0 → ComplexMatrix2) →ₗ[ℝ]
      Edge L n k 0 → ComplexMatrix2 :=
  LinearMap.mk₂ ℝ (bracketTerm U)
    (fun l l' B => by
      rw [bracketTerm_eq, bracketTerm_eq, bracketTerm_eq, ← map_add]
      congr 1
      funext b
      exact edgeBracket_add_left _ _ _ _ _ _)
    (fun c l B => by
      rw [bracketTerm_eq, bracketTerm_eq, ← map_smul]
      congr 1
      funext b
      exact edgeBracket_smul_left _ _ _ _ _)
    (fun l B B' => by
      rw [bracketTerm_eq, bracketTerm_eq, bracketTerm_eq, ← map_add]
      congr 1
      funext b
      exact edgeBracket_add_right _ _ _ _ _)
    (fun c l B => by
      rw [bracketTerm_eq, bracketTerm_eq, ← map_smul]
      congr 1
      funext b
      exact edgeBracket_smul_right _ _ _ _ _)
theorem bracketTerm_sum_left (U : Edge L n k 0 → ComplexMatrix2) {ι : Type*} (s : Finset ι)
    (t : ι → ℝ) (x : ι → Vertex L n k 0 → ComplexMatrix2) (B : Edge L n k 0 → ComplexMatrix2) :
    bracketTerm U (∑ a ∈ s, t a • x a) B = ∑ a ∈ s, t a • bracketTerm U (x a) B := by
  change bracketBilinear U _ B = ∑ a ∈ s, t a • bracketBilinear U (x a) B
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
theorem bracketTerm_sum_right (U : Edge L n k 0 → ComplexMatrix2) {ι : Type*} (s : Finset ι)
    (t : ι → ℝ) (l : Vertex L n k 0 → ComplexMatrix2) (x : ι → Edge L n k 0 → ComplexMatrix2) :
    bracketTerm U l (∑ a ∈ s, t a • x a) = ∑ a ∈ s, t a • bracketTerm U l (x a) := by
  change bracketBilinear U l _ = ∑ a ∈ s, t a • bracketBilinear U l (x a)
  simp only [map_sum, map_smul]
end Brackets
section AnalyticOnNeighbourhoods
variable {L n k : ℕ}
structure AnalyticAlgebraOn (𝒰 : Set (Edge L n k 0 → ComplexMatrix2)) : Prop where
  const (c : ℝ) : IsAnalyticFieldFunction 𝒰 fun _ => c
  add {F G : (Edge L n k 0 → ComplexMatrix2) → ℝ} : IsAnalyticFieldFunction 𝒰 F →
    IsAnalyticFieldFunction 𝒰 G → IsAnalyticFieldFunction 𝒰 fun U => F U + G U
  mul {F G : (Edge L n k 0 → ComplexMatrix2) → ℝ} : IsAnalyticFieldFunction 𝒰 F →
    IsAnalyticFieldFunction 𝒰 G → IsAnalyticFieldFunction 𝒰 fun U => F U * G U
  congr {F G : (Edge L n k 0 → ComplexMatrix2) → ℝ} : IsAnalyticFieldFunction 𝒰 F → EqOn F G 𝒰 →
    IsAnalyticFieldFunction 𝒰 G
namespace AnalyticAlgebraOn
variable {𝒰 : Set (Edge L n k 0 → ComplexMatrix2)}
theorem sum (h : AnalyticAlgebraOn 𝒰) {ι : Type*} (s : Finset ι)
    {G : ι → (Edge L n k 0 → ComplexMatrix2) → ℝ}
    (hG : ∀ a ∈ s, IsAnalyticFieldFunction 𝒰 (G a)) :
    IsAnalyticFieldFunction 𝒰 fun U => ∑ a ∈ s, G a U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact h.add (hG a (Finset.mem_insert_self a s))
      (ih fun b hb => hG b (Finset.mem_insert_of_mem hb))
theorem sub (h : AnalyticAlgebraOn 𝒰) {F G : (Edge L n k 0 → ComplexMatrix2) → ℝ}
    (hF : IsAnalyticFieldFunction 𝒰 F) (hG : IsAnalyticFieldFunction 𝒰 G) :
    IsAnalyticFieldFunction 𝒰 fun U => F U - G U :=
  h.congr (h.add hF (h.mul (h.const (-1)) hG)) fun U _ => by ring
theorem pairing_form (h : AnalyticAlgebraOn 𝒰) {ι : Type*} [Fintype ι] (f : ι → ComplexMatrix2)
    {A : (Edge L n k 0 → ComplexMatrix2) → ι → ComplexMatrix2}
    (hA : ∀ (i : ι) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ), IsAnalyticFieldFunction 𝒰 fun U => φ (A U i)) :
    IsAnalyticFieldFunction 𝒰 fun U => realPairingForm f (A U) :=
  h.congr (h.sum Finset.univ fun i _ => hA i (realTraceForm (f i))) fun U _ =>
    (realPairingForm_apply f (A U)).symm
theorem edge_form (h : AnalyticAlgebraOn 𝒰) {j : ℕ} [Fintype (PositiveEdge L n k j)]
    (x : Edge L n k j → ComplexMatrix2) {A : (Edge L n k 0 → ComplexMatrix2) → Edge L n k j → ComplexMatrix2}
    (hA : ∀ (c : PositiveEdge L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
      IsAnalyticFieldFunction 𝒰 fun U => φ (A U c.1)) :
    IsAnalyticFieldFunction 𝒰 fun U => edgeRealForm x (A U) :=
  h.pairing_form (restrictToPositiveEdges x) (A := fun U => restrictToPositiveEdges (A U)) hA
end AnalyticAlgebraOn
theorem exists_nhd_inter (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {𝒰₁ 𝒰₂ : Set (Edge L n k 0 → ComplexMatrix2)} {P : (Edge L n k 0 → ComplexMatrix2) → Prop}
    (h₁ : IsOpenNhdOfOne 𝒰₁) (h₂ : IsOpenNhdOfOne 𝒰₂)
    (hne : EventuallyNearIdentity (fieldSpace L n k 0) P) :
    ∃ 𝒰 : Set (Edge L n k 0 → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧ 𝒰 ⊆ 𝒰₁ ∧ 𝒰 ⊆ 𝒰₂ ∧
      ∀ U ∈ 𝒰, P U := by
  have A := ((hE L hL k 0 (Nat.zero_le k)).1 n hn).2.2.2.2.2.2.2.2.1
  obtain ⟨O₁, hO₁, e₁⟩ := (A 𝒰₁ h₁.1.1).2 h₁.1.2
  obtain ⟨O₂, hO₂, e₂⟩ := (A 𝒰₂ h₂.1.1).2 h₂.1.2
  have hne' : {U | P U} ∈ 𝓝[fieldSpace L n k 0] trivialField L n k 0 := hne
  obtain ⟨O, hO, h1O, hOs⟩ := mem_nhdsWithin.1 hne'
  have t₁ : trivialField L n k 0 ∈ O₁ ∩ fieldSpace L n k 0 := by
    rw [← e₁]
    exact h₁.2
  have t₂ : trivialField L n k 0 ∈ O₂ ∩ fieldSpace L n k 0 := by
    rw [← e₂]
    exact h₂.2
  have hsub : ((O ∩ O₁) ∩ O₂) ∩ fieldSpace L n k 0 ⊆ fieldSpace L n k 0 :=
    inter_subset_right
  refine ⟨((O ∩ O₁) ∩ O₂) ∩ fieldSpace L n k 0,
    ⟨⟨hsub, (A _ hsub).1 ⟨_, (hO.inter hO₁).inter hO₂, rfl⟩⟩, ⟨⟨⟨h1O, t₁.1⟩, t₂.1⟩, t₁.2⟩⟩,
    fun V hV => ?_, fun V hV => ?_, fun V hV => hOs ⟨hV.1.1.1, hV.2⟩⟩
  · rw [e₁]
    exact ⟨hV.1.1.2, hV.2⟩
  · rw [e₂]
    exact ⟨hV.1.2, hV.2⟩
theorem linearMapWithValues_apply {α β : Type*} {p : Submodule ℝ (α → ComplexMatrix2)}
    {p' : Submodule ℝ (β → ComplexMatrix2)} {f : (α → ComplexMatrix2) → β → ComplexMatrix2}
    (h : ∃ T : p →ₗ[ℝ] p', ∀ x : p, (T x : β → ComplexMatrix2) = f x) (x : p) :
    (linearMapWithValues p p' f x : β → ComplexMatrix2) = f x := by apply _root_.YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide.linearMapWithValues_apply <;> assumption
theorem iterCovariantDeriv_eventually_linear (hY : RealLinearMaps.RealLinearMapsStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    EventuallyNearIdentity (fieldSpace L n k 0) fun U =>
      ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k, ∀ B : edgeFormSpace L n k 0,
        (T B : Edge L n k k → ComplexMatrix2) =
          iterCovariantDeriv L n k U k (B : Edge L n k 0 → ComplexMatrix2) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  exact ((hY L n (i + 1) hL hn hk).1 i (Nat.lt_succ_self i)).iterCovariantDeriv_isLinear
theorem iterAverage_eventually_linear (hY : RealLinearMaps.RealLinearMapsStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    EventuallyNearIdentity (fieldSpace L n k 0) fun U =>
      ∃ T : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k,
        ∀ l : vertexFunctionSpace L n k 0,
        (T l : Vertex L n k k → ComplexMatrix2) =
          iterAdjointCubeAverage L n k U k (l : Vertex L n k 0 → ComplexMatrix2) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  exact ((hY L n (i + 1) hL hn hk).1 i (Nat.lt_succ_self i)).iterAdjointCubeAverage_isLinear
end AnalyticOnNeighbourhoods
theorem entries_analytic
    (hIter : CovariantIteratesAnalyticEntries)
    (hTerms : BackgroundTermsAnalytic)
    (hY : RealLinearMaps.RealLinearMapsStatement)
    (hQ : RealQuadraticTransposes.Statement)
    (hE : BondSetFields.ProductStructureHolds)
    (hS : FiniteSideFormSpaces)
    (hP : FaceSums.FacesAndPairings)
    (hAlg : AnalyticFieldFunctionsClosed)
    (hForm : BackgroundFunctionalWellDefinedAtTrivialField) :
    BackgroundDeterminantEntriesAnalytic := by
  classical
  intro L n k hL hn hk
  obtain ⟨hfin₀, fd₀, -, c₀, hc₀⟩ := hS L n k 0 hL hn (Nat.zero_le k)
  obtain ⟨hfink, -, -, -, -⟩ := hS L n k k hL hn le_rfl
  have hvert₀ : Finite (Vertex L n k 0) := Set.finite_univ_iff.mp
    (((hP L hL k 0 (Nat.zero_le k)).1 n hn).2.1 Set.univ).2.1
  have hvertk : Finite (Vertex L n k k) := Set.finite_univ_iff.mp
    (((hP L hL k k le_rfl).1 n hn).2.1 Set.univ).2.1
  letI : Fintype (PositiveEdge L n k 0) := Fintype.ofFinite _
  letI : Fintype (PositiveEdge L n k k) := Fintype.ofFinite _
  letI : Fintype (Vertex L n k 0) := Fintype.ofFinite _
  letI : Fintype (Vertex L n k k) := Fintype.ofFinite _
  have hEs : VertexFunctionsEuclidean L n k 0 ∧ VertexFunctionsEuclidean L n k k := by
    by_contra hno
    apply (hForm L n k hL hn hk).2
    unfold ghostSaddleDet saddleDetOnVertexFunctions
    rw [dif_neg hno]
  obtain ⟨fds₀, s₀, hs₀⟩ := hEs.1
  obtain ⟨fdsk, sk, hsk⟩ := hEs.2
  obtain ⟨q, f, hf, hfp⟩ := exists_orthonormal_expansion c₀
  obtain ⟨d, e, he, hep⟩ := exists_orthonormal_expansion s₀
  obtain ⟨r, g, -, hgp⟩ := exists_orthonormal_expansion sk
  obtain ⟨𝒰₁, h𝒰₁, hdc₁, hdr₁, hav₁⟩ := hIter L n k k hL hn hk le_rfl
  obtain ⟨𝒰₂, h𝒰₂, hA₂, hq₂, hcm₂, hdf₂⟩ := hTerms L n k hL hn hk
  obtain ⟨hDT, hnear⟩ := hQ L n k hL hn hk
  have hTower := (hY L n k hL hn hk).2
  obtain ⟨𝒰, h𝒰, hs₁, hs₂, hPU⟩ := exists_nhd_inter
    (P := fun U => (TermsRealValued U ∧ TransposeProperties U ∧ BackgroundOperatorProperties U) ∧
      (∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k, ∀ B : edgeFormSpace L n k 0,
        (T B : Edge L n k k → ComplexMatrix2) =
          iterCovariantDeriv L n k U k (B : Edge L n k 0 → ComplexMatrix2)) ∧
      ∃ T : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k,
        ∀ l : vertexFunctionSpace L n k 0,
        (T l : Vertex L n k k → ComplexMatrix2) =
          iterAdjointCubeAverage L n k U k (l : Vertex L n k 0 → ComplexMatrix2))
    hE hL hn h𝒰₁ h𝒰₂ (by
      have a₁ := hnear
      have a₂ := iterCovariantDeriv_eventually_linear hY hL hn hk
      have a₃ := iterAverage_eventually_linear hY hL hn hk
      unfold EventuallyNearIdentity at a₁ a₂ a₃ ⊢
      filter_upwards [a₁, a₂, a₃] with U b₁ b₂ b₃
      exact ⟨b₁, b₂, b₃⟩)
  have hop := h𝒰.1
  obtain ⟨hconst, hsp, hmono, hcongr, -⟩ := hAlg L n k 0 0 hL hn (Nat.zero_le k) (Nat.zero_le k)
  have alg : AnalyticAlgebraOn 𝒰 :=
    ⟨fun c => hconst 𝒰 c hop, fun h₁ h₂ => (hsp _ _ _ h₁ h₂).1, fun h₁ h₂ => (hsp _ _ _ h₁ h₂).2,
      fun h₁ h₂ => hcongr _ _ _ h₁ h₂⟩
  have hdiff : ∀ (x : Edge L n k 0 → ComplexMatrix2) (l : vertexFunctionSpace L n k 0),
      IsAnalyticFieldFunction 𝒰 fun U =>
        edgeRealForm x (covDiff U (l : Vertex L n k 0 → ComplexMatrix2)) :=
    fun x l => alg.edge_form x fun c φ => hmono _ _ _ (hdf₂ l c.1 φ) hop hs₂
  have hcomm : ∀ (x : Edge L n k 0 → ComplexMatrix2) (l : vertexFunctionSpace L n k 0)
      (B : edgeFormSpace L n k 0),
      IsAnalyticFieldFunction 𝒰 fun U => edgeRealForm x
        (bracketTerm U (l : Vertex L n k 0 → ComplexMatrix2) (B : Edge L n k 0 → ComplexMatrix2)) :=
    fun x l B => alg.edge_form x fun c φ => hmono _ _ _ (hcm₂ l B c.1 φ) hop hs₂
  have hsec : ∀ (x : PositiveEdge L n k k → ComplexMatrix2) (B B' : edgeFormSpace L n k 0),
      IsAnalyticFieldFunction 𝒰 fun U => realPairingForm x (iterQuadraticTerm U B B') :=
    fun x B B' => alg.pairing_form x fun c φ => hmono _ _ _ (hq₂ B B' c φ) hop hs₂
  have hdc : ∀ (x : Edge L n k k → ComplexMatrix2) (B : edgeFormSpace L n k 0),
      IsAnalyticFieldFunction 𝒰 fun U => edgeRealForm x
        (iterCovariantDeriv L n k U k (B : Edge L n k 0 → ComplexMatrix2)) :=
    fun x B => alg.edge_form x fun c φ => hmono _ _ _ (hdc₁ B c φ) hop hs₁
  have hav : ∀ (x : Vertex L n k k → ComplexMatrix2) (l : vertexFunctionSpace L n k 0),
      IsAnalyticFieldFunction 𝒰 fun U => realPairingForm x
        (iterAdjointCubeAverage L n k U k (l : Vertex L n k 0 → ComplexMatrix2)) :=
    fun x l => alg.pairing_form x fun y φ => hmono _ _ _ (hav₁ l y φ) hop hs₁
  have hbg : ∀ (x : Vertex L n k 0 → ComplexMatrix2) (B : edgeFormSpace L n k 0),
      IsAnalyticFieldFunction 𝒰 fun U => realPairingForm x
        (backgroundGaugeParameter U (B : Edge L n k 0 → ComplexMatrix2)) := by
    intro x B
    refine alg.pairing_form x fun y φ => ?_
    by_cases h : ∃ y' : Vertex L n k k, (y' : PeriodicLattice.FourTorus L n) = y
    · refine alg.congr (hmono _ _ _ (hdr₁ B h.choose φ) hop hs₁) fun U _ => ?_
      simp only [backgroundGaugeParameter, extendByZero, dif_pos h]
    · refine alg.congr (alg.const 0) fun U _ => ?_
      simp only [backgroundGaugeParameter, extendByZero, dif_neg h, map_zero]
  have hconf : ∀ U ∈ 𝒰, U ∈ fieldSpace L n k 0 := fun U hU => hop.1 hU
  have hDlin : ∀ U ∈ 𝒰, ∀ l : vertexFunctionSpace L n k 0,
      (covDiffLinear L n k U l : Edge L n k 0 → ComplexMatrix2) =
        covDiff U (l : Vertex L n k 0 → ComplexMatrix2) := fun U hU l =>
    linearMapWithValues_apply (hTower.covDiff_isLinear 0 (Nat.zero_le k) U (hconf U hU)) l
  have hClin : ∀ U ∈ 𝒰, ∀ B : edgeFormSpace L n k 0,
      (iterCovariantDerivLinear L n k U B : Edge L n k k → ComplexMatrix2) =
        iterCovariantDeriv L n k U k (B : Edge L n k 0 → ComplexMatrix2) := fun U hU B =>
    linearMapWithValues_apply (hPU U hU).2.1 B
  have hAlin : ∀ U ∈ 𝒰, ∀ l : vertexFunctionSpace L n k 0,
      (iterAverageLinear L n k U l : Vertex L n k k → ComplexMatrix2) =
        iterAdjointCubeAverage L n k U k (l : Vertex L n k 0 → ComplexMatrix2) := fun U hU l =>
    linearMapWithValues_apply (hPU U hU).2.2 l
  have hDTr : ∀ U ∈ 𝒰, ∀ (x : edgeFormSpace L n k 0) (l : vertexFunctionSpace L n k 0),
      traceFinsumPairing (covDiffRealTranspose L n k U x : Vertex L n k 0 → ComplexMatrix2)
          (l : Vertex L n k 0 → ComplexMatrix2) =
        edgeFormPairing (x : Edge L n k 0 → ComplexMatrix2)
          (covDiffLinear L n k U l : Edge L n k 0 → ComplexMatrix2) := by
    intro U hU x l
    obtain ⟨T, -, -, -, h⟩ := hDT 0 (Nat.zero_le k) U (hconf U hU)
    exact h x l
  have hATr : ∀ U ∈ 𝒰, ∀ (x : vertexFunctionSpace L n k k) (l : vertexFunctionSpace L n k 0),
      traceFinsumPairing (iterAverageRealTranspose L n k U x : Vertex L n k 0 → ComplexMatrix2)
          (l : Vertex L n k 0 → ComplexMatrix2) =
        traceFinsumPairing (x : Vertex L n k k → ComplexMatrix2)
          (iterAverageLinear L n k U l : Vertex L n k k → ComplexMatrix2) := by
    intro U hU x l
    obtain ⟨T, -, -, -, h⟩ := (hPU U hU).1.2.1.average_transpose
    exact h x l
  have hi₀ : ∀ x y : edgeFormSpace L n k 0, c₀.inner x y =
      edgeRealForm (x : Edge L n k 0 → ComplexMatrix2) (y : Edge L n k 0 → ComplexMatrix2) :=
    fun x y => by
    rw [edgeRealForm_eq, hc₀, Complex.ofReal_re]
  have hiS : ∀ x y : vertexFunctionSpace L n k 0, s₀.inner x y =
      realPairingForm (x : Vertex L n k 0 → ComplexMatrix2) (y : Vertex L n k 0 → ComplexMatrix2) :=
    fun x y => by
    rw [← traceFinsumPairing_re, hs₀ x y]
  have hiK : ∀ x y : vertexFunctionSpace L n k k, sk.inner x y =
      realPairingForm (x : Vertex L n k k → ComplexMatrix2) (y : Vertex L n k k → ComplexMatrix2) :=
    fun x y => by
    rw [← traceFinsumPairing_re, hsk x y]
  refine ⟨𝒰, h𝒰, ?_, ?_, ?_, ?_⟩
  · intro J B μ
    obtain ⟨sf, hsf⟩ : ∃ sf : Fin d → (Edge L n k 0 → ComplexMatrix2) → ℝ, ∀ a U, sf a U =
        realPairingForm (e a).1 (backgroundGaugeParameter U B.1) := ⟨_, fun _ _ => rfl⟩
    have hsfA : ∀ a, IsAnalyticFieldFunction 𝒰 (sf a) := fun a =>
      alg.congr (hbg (e a).1 B) fun U _ => (hsf a U).symm
    have hσ : ∀ U ∈ 𝒰, ∃ s : vertexFunctionSpace L n k 0, s.1 = backgroundGaugeParameter U B.1 ∧
        ∀ a, s₀.inner (e a) s = sf a U := by
      intro U hU
      obtain ⟨σ, h⟩ := (hPU U hU).1.2.2.gaugeParameter_linear
      exact ⟨σ B, (h B).2, fun a => by rw [hiS, (h B).2, hsf]⟩
    have hsexp : ∀ U ∈ 𝒰, backgroundGaugeParameter U B.1 = ∑ a, sf a U • (e a).1 := by
      intro U hU
      obtain ⟨s, h₁, h₂⟩ := hσ U hU
      rw [← h₁, coe_eq_sum_inner_smul s₀ he s]
      simp only [h₂]
    have hDexp : ∀ U ∈ 𝒰, covDiff U (backgroundGaugeParameter U B.1) =
        ∑ a, sf a U • covDiff U (e a).1 := by
      intro U hU
      obtain ⟨s, h₁, h₂⟩ := hσ U hU
      rw [← h₁, ← hDlin U hU s]
      conv_lhs => rw [he s]
      simp only [map_sum, map_smul, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul,
        hDlin U hU, h₂]
    obtain ⟨tf, htf⟩ : ∃ tf : Fin q → (Edge L n k 0 → ComplexMatrix2) → ℝ, ∀ c U, tf c U =
        edgeRealForm (f c).1 (covDiff U (backgroundGaugeParameter U B.1)) :=
      ⟨_, fun _ _ => rfl⟩
    have htfA : ∀ c, IsAnalyticFieldFunction 𝒰 (tf c) := fun c =>
      alg.congr (alg.sum Finset.univ (G := fun a U =>
        sf a U * edgeRealForm (f c).1 (covDiff U (e a).1))
        fun a _ => alg.mul (hsfA a) (hdiff _ (e a))) fun U hU => by
          rw [htf, hDexp U hU, map_sum]
          simp only [map_smul, smul_eq_mul]
    have hDform : ∀ U ∈ 𝒰, covDiff U (backgroundGaugeParameter U B.1) =
        ∑ c, tf c U • (f c).1 := by
      intro U hU
      obtain ⟨s, h₁, -⟩ := hσ U hU
      have h := coe_eq_sum_inner_smul c₀ hf (covDiffLinear L n k U s)
      rw [hDlin U hU s, h₁] at h
      rw [h]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hi₀, hDlin U hU s, h₁, htf]
    have hT₁ : ∀ U ∈ 𝒰, edgeRealForm J.1 (bracketTerm U (backgroundGaugeParameter U B.1) B.1) =
        ∑ a, sf a U * edgeRealForm J.1 (bracketTerm U (e a).1 B.1) := by
      intro U hU
      rw [hsexp U hU, bracketTerm_sum_left, map_sum]
      simp only [map_smul, smul_eq_mul]
    have hT₂ : ∀ U ∈ 𝒰, edgeRealForm J.1 (bracketTerm U (backgroundGaugeParameter U B.1)
          (covDiff U (backgroundGaugeParameter U B.1))) =
        ∑ a, sf a U * ∑ c, tf c U * edgeRealForm J.1 (bracketTerm U (e a).1 (f c).1) := by
      intro U hU
      rw [hDform U hU, hsexp U hU, bracketTerm_sum_left, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [bracketTerm_sum_right, map_smul, map_sum, smul_eq_mul]
      simp only [map_smul, smul_eq_mul]
    have hτ : ∀ U ∈ 𝒰, backgroundShift L n k U B =
        ∑ c, (edgeRealForm (f c).1 B.1 + tf c U) • f c := by
      intro U hU
      conv_lhs => rw [hf (backgroundShift L n k U B)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hi₀, (hPU U hU).1.2.2.backgroundShift_apply B, map_add, htf]
    have hT₃ : ∀ U ∈ 𝒰, realPairingForm (restrictToPositiveEdges μ.1)
          (iterQuadraticTerm U (backgroundShift L n k U B) (backgroundShift L n k U B)) =
        ∑ c, (edgeRealForm (f c).1 B.1 + tf c U) *
          ∑ c', (edgeRealForm (f c').1 B.1 + tf c' U) *
          realPairingForm (restrictToPositiveEdges μ.1) (iterQuadraticTerm U (f c') (f c)) := by
      intro U hU
      rw [hτ U hU]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    obtain ⟨w, hw⟩ : ∃ w : Fin d → (Edge L n k 0 → ComplexMatrix2) → ℝ, ∀ a U, w a U =
        edgeRealForm B.1 (covDiff U (e a).1) := ⟨_, fun _ _ => rfl⟩
    have hwA : ∀ a, IsAnalyticFieldFunction 𝒰 (w a) := fun a =>
      alg.congr (hdiff _ (e a)) fun U _ => (hw a U).symm
    obtain ⟨v, hv⟩ : ∃ v : Fin d → Fin d → (Edge L n k 0 → ComplexMatrix2) → ℝ, ∀ a b U, v a b U =
        ∑ i, realPairingForm (g i).1 (iterAdjointCubeAverage L n k U k (e b).1) *
          realPairingForm (g i).1 (iterAdjointCubeAverage L n k U k (e a).1) :=
      ⟨_, fun _ _ _ => rfl⟩
    have hvA : ∀ a b, IsAnalyticFieldFunction 𝒰 (v a b) := fun a b =>
      alg.congr (alg.sum Finset.univ (G := fun i U =>
        realPairingForm (g i).1 (iterAdjointCubeAverage L n k U k (e b).1) *
          realPairingForm (g i).1 (iterAdjointCubeAverage L n k U k (e a).1))
        fun i _ => alg.mul (hav _ _) (hav _ _)) fun U _ => (hv a b U).symm
    have hwi : ∀ U ∈ 𝒰, ∀ a, s₀.inner (e a) (covDiffRealTranspose L n k U B) = w a U := by
      intro U hU a
      rw [core_inner_comm, hs₀, hDTr U hU, hw, edgeRealForm_eq, hDlin U hU]
    have hvi : ∀ U ∈ 𝒰, ∀ a b, sk.inner (iterAverageLinear L n k U (e b))
        (iterAverageLinear L n k U (e a)) = v a b U := by
      intro U hU a b
      rw [hgp, hv]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [core_inner_comm sk _ (g i), hiK, hiK, hAlin U hU, hAlin U hU]
    have hG : ∀ U ∈ 𝒰, ∀ a, s₀.inner (e a) (gaugeSliceResidual U B) =
        w a U - (L : ℝ) ^ (4 * k) * ∑ b, w b U * v a b U := by
      intro U hU a
      have hx : s₀.inner (e a) (iterAverageRealTranspose L n k U
          (iterAverageLinear L n k U (covDiffRealTranspose L n k U B))) =
          ∑ b, w b U * v a b U := by
        rw [core_inner_comm, hs₀, hATr U hU, ← hsk]
        conv_lhs => rw [he (covDiffRealTranspose L n k U B)]
        rw [map_sum]
        simp only [map_smul]
        rw [core_inner_sum_left sk]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hwi U hU b, hvi U hU a b]
      rw [← hx, ← hwi U hU a, hiS, hiS, hiS]
      simp only [gaugeSliceResidual, AddSubgroupClass.coe_sub, SetLike.val_smul, map_sub, map_smul,
        smul_eq_mul]
    have hN : ∀ U ∈ 𝒰, traceFinsumNorm (gaugeSliceResidual U B).1 ^ 2 =
        ∑ a, (w a U - (L : ℝ) ^ (4 * k) * ∑ b, w b U * v a b U) *
          (w a U - (L : ℝ) ^ (4 * k) * ∑ b, w b U * v a b U) := by
      intro U hU
      have h := hs₀ (gaugeSliceResidual U B) (gaugeSliceResidual U B)
      have hnn : 0 ≤ (traceFinsumPairing (gaugeSliceResidual U B).1
          (gaugeSliceResidual U B).1).re := by
        rw [← h]
        exact s₀.re_inner_nonneg _
      unfold traceFinsumNorm
      rw [Real.sq_sqrt hnn, ← h, hep]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [core_inner_comm s₀ _ (e a), hG U hU a]
    have hA : IsAnalyticFieldFunction 𝒰 fun U => leftSecondDeriv (plaquetteAction L n k) U B.1 B.1 :=
      hmono _ _ _ (hA₂ B B) hop hs₂
    have hA₁ : IsAnalyticFieldFunction 𝒰 fun U =>
        ∑ a, sf a U * edgeRealForm J.1 (bracketTerm U (e a).1 B.1) :=
      alg.sum Finset.univ fun a _ => alg.mul (hsfA a) (hcomm _ (e a) B)
    have hA₂' : IsAnalyticFieldFunction 𝒰 fun U =>
        ∑ a, sf a U * ∑ c, tf c U * edgeRealForm J.1 (bracketTerm U (e a).1 (f c).1) :=
      alg.sum Finset.univ fun a _ => alg.mul (hsfA a)
        (alg.sum Finset.univ fun c _ => alg.mul (htfA c) (hcomm _ (e a) (f c)))
    have huA : ∀ c, IsAnalyticFieldFunction 𝒰 fun U => edgeRealForm (f c).1 B.1 + tf c U :=
      fun c => alg.add (alg.const _) (htfA c)
    have hA₃ : IsAnalyticFieldFunction 𝒰 fun U =>
        ∑ c, (edgeRealForm (f c).1 B.1 + tf c U) *
          ∑ c', (edgeRealForm (f c').1 B.1 + tf c' U) *
          realPairingForm (restrictToPositiveEdges μ.1) (iterQuadraticTerm U (f c') (f c)) :=
      alg.sum Finset.univ fun c _ => alg.mul (huA c)
        (alg.sum Finset.univ fun c' _ => alg.mul (huA c') (hsec _ (f c') (f c)))
    have hGA : ∀ a, IsAnalyticFieldFunction 𝒰 fun U =>
        w a U - (L : ℝ) ^ (4 * k) * ∑ b, w b U * v a b U := fun a =>
      alg.sub (hwA a) (alg.mul (alg.const _)
        (alg.sum Finset.univ fun b _ => alg.mul (hwA b) (hvA a b)))
    have hA₄ : IsAnalyticFieldFunction 𝒰 fun U =>
        ∑ a, (w a U - (L : ℝ) ^ (4 * k) * ∑ b, w b U * v a b U) *
          (w a U - (L : ℝ) ^ (4 * k) * ∑ b, w b U * v a b U) :=
      alg.sum Finset.univ fun a _ => alg.mul (hGA a) (hGA a)
    refine alg.congr (alg.add (alg.add hA (alg.sub (alg.add (alg.mul (alg.const 2) hA₁) hA₂') hA₃))
      hA₄) fun U hU => ?_
    unfold backgroundHessianForm sourceQuadraticForm
    rw [hN U hU, traceFinsumPairing_re, ← edgeRealForm_eq, ← edgeRealForm_eq, hT₁ U hU, hT₂ U hU,
      hT₃ U hU]
  · intro B C
    refine alg.congr (hdc C B) fun U hU => ?_
    rw [edgeRealForm_eq, hClin U hU]
  · intro l l'
    refine alg.congr (alg.sum Finset.univ (G := fun a U =>
      edgeRealForm (f a : Edge L n k 0 → ComplexMatrix2)
          (covDiff U (l : Vertex L n k 0 → ComplexMatrix2)) *
        edgeRealForm (f a : Edge L n k 0 → ComplexMatrix2)
          (covDiff U (l' : Vertex L n k 0 → ComplexMatrix2)))
      fun a _ => alg.mul (hdiff _ l) (hdiff _ l')) fun U hU => ?_
    rw [(hPU U hU).1.2.1.covDiff_transpose_symmetric l l', hDTr U hU, hc₀, Complex.ofReal_re, hfp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [core_inner_comm c₀ _ (f a), hi₀, hi₀, hDlin U hU, hDlin U hU]
  · intro l x
    refine alg.congr (hav x l) fun U hU => ?_
    rw [← traceFinsumPairing_re, hAlin U hU]
end YangMills.Construction.Tower.BackgroundDeterminants
end
