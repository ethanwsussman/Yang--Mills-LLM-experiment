import YangMills.Construction.TorusOrFourSpace.ChartsOfAnAdmissibleFamilyProof
import YangMills.Construction.TorusOrFourSpace.ComplexClassesOfOnePoint
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.ComplexSupportedClasses
open Kind MetricNotions
open TupleFacts
open Kind.Tuple (complexC1SupportedIn singleTestFns singleSet ofSingle)
section Generic
variable {X : Type*} {d : X → X → ℝ}
private theorem closureWrt_isClosedWrt (tri : ∀ x y z : X, d x z ≤ d x y + d y z) (Z : Set X) :
    IsClosedWrt d (closureWrt d Z) := by apply _root_.YangMills.SharedProofs.p11892 <;> assumption
private theorem isCompactWrt_of_closed_subset {S T : Set X} (hS : IsCompactWrt d S)
    (hT : IsClosedWrt d T) (hTS : T ⊆ S) : IsCompactWrt d T := by apply _root_.YangMills.SharedProofs.p5019 <;> assumption
private theorem isCompactWrt_union {S T : Set X} (hS : IsCompactWrt d S)
    (hT : IsCompactWrt d T) : IsCompactWrt d (S ∪ T) := by apply _root_.YangMills.SharedProofs.p57694 <;> assumption
end Generic
variable (D : Params) (E : Kind)
private def idx0 : Fin ((1 : ℕ+) : ℕ) := ⟨0, (1 : ℕ+).pos⟩
private theorem quotDist_nonneg (y y' : E.Pt D) : 0 ≤ Kind.quotDist D E y y' := by apply _root_.YangMills.Construction.PeriodicSpace.QuotientGeometry.quotDist_nonneg <;> assumption
private theorem tupleDist_single (y y' : E.Tuple D 1) :
    Tuple.tupleDist D E y y' = Kind.quotDist D E (y idx0) (y' idx0) := by
  show Real.sqrt (∑ i : Fin 1, Kind.quotDist D E (y i) (y' i) ^ 2) = _
  rw [Fin.sum_univ_one]
  exact Real.sqrt_sq (quotDist_nonneg D E _ _)
private theorem boxSet_const_eq (S : Set (E.Pt D)) :
    Tuple.boxSet D E (n := 1) (fun _ => S) = singleSet D E S := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.AdmissibleCharts.boxSet_one <;> assumption
private theorem isCompactT_singleSet_iff (hProd : BoxSetFacts D E 1)
    (hProj : EvalLipschitzCompact D E 1) (S : Set (E.Pt D)) :
    Tuple.IsCompactT D E (singleSet D E S) ↔ Kind.IsCompactQ D E S := by
  constructor
  · intro hK
    have h := (hProj idx0).2 _ hK
    have himg : (fun y : E.Tuple D 1 => y idx0) '' singleSet D E S = S := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hz
        exact ⟨fun _ => z, hz, rfl⟩
    rwa [himg] at h
  · intro hS
    have h := (hProd fun _ => S).2.2 fun _ => hS
    rwa [boxSet_const_eq] at h
private theorem isOpenT_singleSet (hProd : BoxSetFacts D E 1) {O : Set (E.Pt D)}
    (hO : Kind.IsOpenQ D E O) : Tuple.IsOpenT D E (singleSet D E O) := by
  have h := (hProd fun _ => O).1 fun _ => hO
  rwa [boxSet_const_eq] at h
private theorem singleSet_subset_iff (S O : Set (E.Pt D)) :
    singleSet D E S ⊆ singleSet D E O ↔ S ⊆ O := by
  constructor
  · intro h z hz
    exact h (a := fun _ => z) hz
  · intro h y hy
    exact h hy
private theorem supportT_ofSingle (φ : E.Pt D → ℂ) :
    Tuple.supportT D E (ofSingle D E φ) =
      singleSet D E (Kind.supportQ D E φ) := by
  ext y
  constructor
  · intro hy r hr
    obtain ⟨y', hy', hd⟩ := hy r hr
    exact ⟨y' idx0, hy', by rwa [tupleDist_single] at hd⟩
  · intro hy r hr
    obtain ⟨z, hz, hd⟩ := hy r hr
    exact ⟨fun _ => z, hz, by rw [tupleDist_single]; exact hd⟩
private theorem supportQ_ofReal (g : E.Pt D → ℝ) :
    Kind.supportQ D E (fun y => (g y : ℂ)) = Kind.supportQ D E g := by
  have h : {y | (g y : ℂ) ≠ 0} = {y | g y ≠ 0} := by
    ext y
    simp
  exact congrArg (Kind.closureQ D E) h
abbrev _root_.YangMills.SharedProofs.p40645 := @supportQ_ofReal
private theorem supportT_mono {F G : E.Tuple D 1 → ℂ} (h : ∀ y, G y ≠ 0 → F y ≠ 0) :
    Tuple.supportT D E G ⊆ Tuple.supportT D E F := by
  intro y hy r hr
  obtain ⟨y', hy', hd⟩ := hy r hr
  exact ⟨y', h y' hy', hd⟩
private theorem mem_complexC1_iff (hProd : BoxSetFacts D E 1)
    (hProj : EvalLipschitzCompact D E 1) (O : Set (E.Pt D))
    (h : E.Pt D → ℂ) :
    h ∈ complexC1SupportedIn D E O ↔
      Tuple.IsClassC D E 1 (ofSingle D E h) ∧
        Tuple.IsCompactT D E (Tuple.supportT D E (ofSingle D E h)) ∧
        Tuple.supportT D E (ofSingle D E h) ⊆ singleSet D E O := by
  rw [supportT_ofSingle, isCompactT_singleSet_iff D E hProd hProj, singleSet_subset_iff]
  rfl
private theorem ofReal_mem_iff (hTwo : SingleC1Agree D E) (O : Set (E.Pt D))
    (g : E.Pt D → ℝ) :
    g ∈ Kind.c1SupportedIn D E O ↔ (fun y => (g y : ℂ)) ∈ complexC1SupportedIn D E O := by
  have hc := (hTwo g).1
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨hc.2 h1, ?_, ?_⟩
    · rw [supportQ_ofReal]
      exact h2
    · rw [supportQ_ofReal]
      exact h3
  · rintro ⟨h1, h2, h3⟩
    rw [supportQ_ofReal] at h2 h3
    exact ⟨hc.1 h1, h2, h3⟩
private theorem linComb_mem (hProd : BoxSetFacts D E 1)
    (hProj : EvalLipschitzCompact D E 1) (hMetric : DistIsMetric D E 1)
    (hSupp : SupportAddMul D E 1) (hKept : ClassCAddMulParts D E 1)
    {O : Set (E.Pt D)} {f g : E.Pt D → ℂ} (hf : f ∈ complexC1SupportedIn D E O)
    (hg : g ∈ complexC1SupportedIn D E O) (a b : ℂ) :
    a • f + b • g ∈ complexC1SupportedIn D E O := by
  rw [mem_complexC1_iff D E hProd hProj] at hf hg ⊢
  obtain ⟨f1, f2, f3⟩ := hf
  obtain ⟨g1, g2, g3⟩ := hg
  have heq : ofSingle D E (a • f + b • g) = a • ofSingle D E f + b • ofSingle D E g := rfl
  rw [heq]
  have hsub := (hSupp (ofSingle D E f) (ofSingle D E g) a b).1
  exact ⟨(hKept 1 _ _ f1 g1).1 a b,
    isCompactWrt_of_closed_subset (isCompactWrt_union f2 g2)
      (closureWrt_isClosedWrt hMetric.2.2.2 _) hsub,
    hsub.trans (Set.union_subset f3 g3)⟩
private theorem zero_mem_complexC1 (hProd : BoxSetFacts D E 1)
    (hProj : EvalLipschitzCompact D E 1) (hEmpty : TestFnsEmpty D E 1)
    (O : Set (E.Pt D)) : (0 : E.Pt D → ℂ) ∈ complexC1SupportedIn D E O := by
  have h0 : (0 : E.Tuple D 1 → ℂ) ∈
      Tuple.testFns D E (∅ : Set (E.Tuple D 1)) := by
    rw [hEmpty]
    exact Set.mem_singleton _
  rw [mem_complexC1_iff D E hProd hProj]
  exact ⟨h0.1 1, h0.2.1, h0.2.2.trans (Set.empty_subset _)⟩
private theorem mem_of_dominated (hProd : BoxSetFacts D E 1)
    (hProj : EvalLipschitzCompact D E 1) (hMetric : DistIsMetric D E 1)
    {O : Set (E.Pt D)} {h k : E.Pt D → ℂ} (hh : h ∈ complexC1SupportedIn D E O)
    (hk : Tuple.IsClassC D E 1 (ofSingle D E h) →
      Tuple.IsClassC D E 1 (ofSingle D E k))
    (hz : ∀ y, k y ≠ 0 → h y ≠ 0) : k ∈ complexC1SupportedIn D E O := by
  rw [mem_complexC1_iff D E hProd hProj] at hh ⊢
  obtain ⟨h1, h2, h3⟩ := hh
  have hsub : Tuple.supportT D E (ofSingle D E k) ⊆
      Tuple.supportT D E (ofSingle D E h) :=
    supportT_mono D E fun y => hz _
  exact ⟨hk h1, isCompactWrt_of_closed_subset h2 (closureWrt_isClosedWrt hMetric.2.2.2 _) hsub,
    hsub.trans h3⟩
theorem complexSupportedClassesClaim_of_tupleFacts (h : TupleFacts.AllFacts) :
    ComplexSupportedClassesClaim := by
  intro D E O hO
  obtain ⟨-, -, hMetric, -, -, -, -, -, -, -, -, hProd, hProj, -, -, hNorm, hTwo, hSupp, hKept,
    hTest, hEmpty, -, -, -⟩ := h D E 1
  have hΩ := isOpenT_singleSet D E hProd hO
  obtain ⟨⟨S, hS⟩, hStable⟩ := hTest _ hΩ
  have hTestIn : singleTestFns D E O ⊆ complexC1SupportedIn D E O := by
    intro φ hφ
    rw [mem_complexC1_iff D E hProd hProj]
    exact ⟨hφ.1 1, hφ.2.1, hφ.2.2⟩
  have hRe : ∀ k ∈ complexC1SupportedIn D E O,
      (fun y => ((k y).re : ℂ)) ∈ complexC1SupportedIn D E O := by
    intro k hk
    refine mem_of_dominated D E hProd hProj hMetric hk
      (fun h1 => (hKept 1 _ _ h1 h1).2.2.1) fun y hy h0 => hy ?_
    simp [h0]
  have hIm : ∀ k ∈ complexC1SupportedIn D E O,
      (fun y => ((k y).im : ℂ)) ∈ complexC1SupportedIn D E O := by
    intro k hk
    refine mem_of_dominated D E hProd hProj hMetric hk
      (fun h1 => (hKept 1 _ _ h1 h1).2.2.2.1) fun y hy h0 => hy ?_
    simp [h0]
  refine ⟨⟨{ carrier := complexC1SupportedIn D E O
             add_mem' := ?_
             zero_mem' := zero_mem_complexC1 D E hProd hProj hEmpty O
             smul_mem' := ?_ }, rfl⟩,
    ⟨S.comap (LinearMap.funLeft ℂ ℂ fun y : E.Tuple D 1 => y idx0), ?_⟩,
    hTestIn, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g hf hg
    have hc := linComb_mem D E hProd hProj hMetric hSupp hKept hf hg 1 1
    simpa using hc
  · intro c f hf
    have hc := linComb_mem D E hProd hProj hMetric hSupp hKept hf hf c 0
    simpa using hc
  · ext φ
    show (LinearMap.funLeft ℂ ℂ fun y : E.Tuple D 1 => y idx0) φ ∈
      (S : Set (E.Tuple D 1 → ℂ)) ↔ _
    rw [hS]
    rfl
  · intro φ hφ
    exact ⟨(hStable _ hφ).1, (hStable _ hφ).2.1⟩
  · intro g hg
    exact (ofReal_mem_iff D E hTwo O g).2 (hTestIn hg)
  · intro g hg
    exact (ofReal_mem_iff D E hTwo O g).1 hg
  · intro k hk
    exact ⟨(ofReal_mem_iff D E hTwo O _).2 (hRe k hk), (ofReal_mem_iff D E hTwo O _).2 (hIm k hk)⟩
  · intro k hk
    have hk' := (mem_complexC1_iff D E hProd hProj O k).1 hk
    exact hNorm 1 _ hk'.1 hk'.2.1
end YangMills.Construction.PeriodicSpace.ComplexSupportedClasses
