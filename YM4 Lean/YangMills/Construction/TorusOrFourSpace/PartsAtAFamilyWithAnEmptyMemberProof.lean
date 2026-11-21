import YangMills.Construction.TorusOrFourSpace.DistanceOpenSetsDerivativesAndTensorsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsOnProductsOfC1Classes
import YangMills.Construction.TorusOrFourSpace.PartsAtAFamilyWithAnEmptyMember
import Mathlib
set_option autoImplicit false
open scoped ENNReal
namespace YangMills.Construction.PeriodicSpace.Kind
theorem emptyMemberBoxProperties_holds
    (facts : TupleFacts.AllFacts)
    (prods : DisjointProducts.Claim) :
    EmptyMemberBoxProperties.Statement := by
  intro D E C S _ n hn R d G hG hE
  obtain ⟨i₀, hi₀⟩ := hE
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hprod, -, -, -, -, -, -, -, hstable, hemp, -, htens, -⟩ :=
    facts D E n
  obtain ⟨-, -, hmetric₁, -, -, -, -, -, -, -, -, -, hproj₁, -, -, -, -, -, -, -, hemp₁, -, -, -⟩ :=
    facts D E 1
  obtain ⟨hcl, hsep, -, hvan, -⟩ := prods D E (n : ℕ) n.pos
  have hBoxEmpty : Tuple.boxSet D E G = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun y hy => ?_
    have h : y i₀ ∈ G i₀ := hy i₀
    rw [hi₀] at h
    exact h
  have hD : Tuple.testFns D E (Tuple.boxSet D E G) = {0} := by
    rw [hBoxEmpty]
    exact hemp
  have hzero : ∀ F : Tuple.testFns D E (Tuple.boxSet D E G),
      F.1 = 0 := fun F => Set.mem_singleton_iff.mp ((Set.ext_iff.mp hD F.1).mp F.2)
  have hmem0 : (0 : E.Tuple D n → ℂ) ∈
      Tuple.testFns D E (Tuple.boxSet D E G) :=
    (Set.ext_iff.mp hD 0).mpr rfl
  have hopen : Tuple.IsOpenT D E (Tuple.boxSet D E G) :=
    (hprod G).1 hG.isOpen_mem
  have hder : ∀ α, Tuple.partialDeriv D E α (0 : E.Tuple D n → ℂ) = 0 := fun α =>
    Set.mem_singleton_iff.mp ((Set.ext_iff.mp hD _).mp (((hstable _ hopen).2 0 hmem0).2.2.1 α))
  have hnorm : ∀ ν, Tuple.cNorm D E ν (0 : E.Tuple D n → ℂ) = 0 := by
    intro ν
    simp only [Tuple.cNorm, ENNReal.iSup_eq_zero]
    intro α _ y
    rw [hder α]
    simp
  have hlin : ∀ T : Tuple.testFns D E (Tuple.boxSet D E G) → ℂ,
      Tuple.IsComplexLinearForm T → ∀ F, T F = 0 := by
    intro T hT F
    have h := hT.2 0 F F (by rw [hzero F]; simp)
    simpa using h
  have hbound : ∀ T : Tuple.testFns D E (Tuple.boxSet D E G) → ℂ,
      Tuple.IsComplexLinearForm T → ∀ K ν, Tuple.HasOrderBoundOn T K ν := by
    intro T hT K ν
    refine ⟨0, fun F _ => ?_⟩
    rw [hlin T hT F]
    simp
  have hself : ∀ z : E.Pt D, quotDist D E z z ≤ 0 := by
    intro z
    have h := (hproj₁ ⟨0, (1 : ℕ+).pos⟩).1 (fun _ => z) (fun _ => z)
    rw [(hmetric₁.2.1 _ _).mpr rfl] at h
    exact h
  have hdisj : ∀ l l', l ≠ l' → Disjoint (G l) (G l') := by
    intro l l' hll
    rw [Set.disjoint_left]
    intro z hz hz'
    have h₁ := hG.sep_le_setInfDist l l' hll
    have h₂ : setInfDist D E (G l) (G l') ≤ ENNReal.ofReal (quotDist D E z z) :=
      (iInf₂_le z hz).trans (iInf₂_le z hz')
    rw [ENNReal.ofReal_of_nonpos (hself z)] at h₂
    have h₃ : ENNReal.ofReal d = 0 := le_antisymm (h₁.trans h₂) bot_le
    exact absurd hG.sep_pos (not_lt.mpr (ENNReal.ofReal_eq_zero.mp h₃))
  have hone : ∀ φ : E.Pt D → ℂ,
      φ ∈ Tuple.singleTestFns D E (G i₀) → φ = 0 := by
    intro φ hφ
    have hs : Tuple.singleSet D E (G i₀) = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun y hy => ?_
      have h : y ⟨0, (1 : ℕ+).pos⟩ ∈ G i₀ := hy
      rw [hi₀] at h
      exact h
    have h : Tuple.ofSingle D E φ ∈
        Tuple.testFns D E (Tuple.singleSet D E (G i₀)) := hφ
    rw [hs, hemp₁] at h
    funext y
    exact congrFun (Set.mem_singleton_iff.mp h) (fun _ => y)
  have hT₀ : Tuple.IsComplexLinearForm
      (fun _ : Tuple.testFns D E (Tuple.boxSet D E G) => (0 : ℂ)) :=
    ⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩
  have hvalue : ∀ φ, Tuple.IsCutoffFamily D E G φ → S.ValueAtTensor hn
      (fun _ : Tuple.testFns D E (Tuple.boxSet D E G) => (0 : ℂ))
      φ := by
    intro φ hφ
    have hclass : φ ∈ productSet D E (fun l => c1SupportedIn D E (G l)) :=
      fun l _ => hcl.2 (G l) (hG.isOpen_mem l) (φ l) (hφ l)
    have hsepφ : φ ∈ sepC1Tuples D E (n : ℕ) := hsep G hdisj hclass
    have hF : Tuple.cutoffTensor D E φ ∈
        Tuple.testFns D E (Tuple.boxSet D E G) :=
      htens G (fun i y => (φ i y : ℂ)) hG.isOpen_mem hφ
    have hentry : φ i₀ = 0 := by
      funext y
      have h := congrFun (hone _ (hφ i₀)) y
      simpa using h
    refine ⟨hsepφ, hF, ?_⟩
    have h := hvan (S.func (n : ℕ) hn) (S.multilinear (n : ℕ) hn) ⟨φ, hsepφ⟩ i₀ hentry
    rw [h]
    simp
  refine ⟨⟨fun _ => 0, ⟨⟨hT₀, fun K _ _ => ⟨0, hbound _ hT₀ K 0⟩⟩, hvalue⟩,
      fun T hT => funext fun F => hlin T hT.1.1 F⟩, ?_, fun _ => hD, fun T hT =>
      ⟨fun hne => absurd (hne i₀) (by rw [hi₀]; exact Set.not_nonempty_empty),
        fun _ F => hlin T hT.1.1 F, hT.1, fun K _ _ => hbound T hT.1.1 K _⟩⟩
  intro F
  refine ⟨fun _ => F, fun _ => ⟨0, fun k => k.elim0, fun k => k.elim0, ?_⟩,
    ⟨Tuple.supportT D E F.1, F.2.2.1, F.2.2.2, subset_rfl, fun _ => subset_rfl⟩, fun ν => ?_⟩
  · simpa using hzero F
  · simp only [sub_self, hnorm]
    exact tendsto_const_nhds
end YangMills.Construction.PeriodicSpace.Kind
