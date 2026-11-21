import YangMills.Construction.Analysis.MultilinearTelescopingBound
import YangMills.Construction.TorusOrFourSpace.ApproximationByMembersOfTheFamily
import YangMills.Construction.TorusOrFourSpace.ClassC1FunctionsProductsAndNeighbourhoods
import YangMills.Construction.TorusOrFourSpace.CountableFamilyOfACountableChoice
import YangMills.Construction.TorusOrFourSpace.FamiliesOfDenseSetsAndMembersOfTheFamily
import YangMills.Construction.TorusOrFourSpace.NeighbourhoodsOfCompactSetsInTheDiagonalExtraction
import YangMills.Construction.TorusOrFourSpace.QuotientMapCompactSetsAndFunctionsOfClassC1
import Mathlib
set_option autoImplicit false
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.DiagonalLimits.FamilyApproximation
open Kind
variable {D : Params} {E : Kind}
theorem prod_term_le {n : ℕ} (l : Fin n) (a b : Fin n → ℝ) (e t : ℝ) (ha : ∀ k, 0 ≤ a k)
    (hb : ∀ k, 0 ≤ b k) (he : 0 ≤ e) (het : e ≤ t) (hba : ∀ k, b k ≤ a k + t) :
    e * (∏ k ∈ Finset.Iio l, b k) * ∏ k ∈ Finset.Ioi l, a k ≤
      t * ∏ k ∈ Finset.univ.erase l, (a k + t) := by
  have ht : 0 ≤ t := he.trans het
  have hsplit : Finset.univ.erase l = Finset.Iio l ∪ Finset.Ioi l := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Iio,
      Finset.mem_Ioi]
    exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim ne_of_lt ne_of_gt⟩
  have hdisj : Disjoint (Finset.Iio l) (Finset.Ioi l) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    exact lt_asymm (Finset.mem_Iio.1 hk) (Finset.mem_Ioi.1 hk')
  rw [hsplit, Finset.prod_union hdisj, ← mul_assoc]
  have h1 : ∏ k ∈ Finset.Iio l, b k ≤ ∏ k ∈ Finset.Iio l, (a k + t) :=
    Finset.prod_le_prod (fun k _ => hb k) fun k _ => hba k
  have h2 : ∏ k ∈ Finset.Ioi l, a k ≤ ∏ k ∈ Finset.Ioi l, (a k + t) :=
    Finset.prod_le_prod (fun k _ => ha k) fun k _ => le_add_of_nonneg_right ht
  have hb0 : 0 ≤ ∏ k ∈ Finset.Iio l, b k := Finset.prod_nonneg fun k _ => hb k
  have ha0 : 0 ≤ ∏ k ∈ Finset.Ioi l, a k := Finset.prod_nonneg fun k _ => ha k
  have hat0 : 0 ≤ ∏ k ∈ Finset.Iio l, (a k + t) := hb0.trans h1
  exact mul_le_mul (mul_le_mul het h1 hb0 ht) h2 ha0 (mul_nonneg ht hat0)
theorem thickenings_compact_separated (hNbhd : CompactNhdProperties) {n : ℕ}
    (f : FnTuple D E n) (hf : f ∈ sepC1Tuples D E n) (d : ℝ) (hd : 0 < d)
    (hdf : ENNReal.ofReal d ≤ supportGap D E f) :
    ThickeningsCompactSeparated D E f hf d hd := by
  have h3 : 0 < d / 3 := div_pos hd three_pos
  refine ⟨fun i => ?_, fun i k hik => ?_, fun ρ hρ hρ' hS i => ?_⟩
  · exact (hNbhd D E _ _ (hf.2.1 i) (hf.2.1 i) (d / 3) (d / 3) h3 h3).1.2.1
  · have hsep : ENNReal.ofReal d ≤ setInfDist D E (supportQ D E (f i)) (supportQ D E (f k)) :=
      hdf.trans ((iInf_le _ i).trans ((iInf_le _ k).trans (iInf_le _ hik)))
    have key := (hNbhd D E _ _ (hf.2.1 i) (hf.2.1 k) (d / 3) (d / 3) h3 h3).2.1.1
    refine le_trans ?_ key
    have e : ENNReal.ofReal (d / 3) =
        ENNReal.ofReal d - ENNReal.ofReal (d / 3) - ENNReal.ofReal (d / 3) := by
      rw [← ENNReal.ofReal_sub _ h3.le, ← ENNReal.ofReal_sub _ h3.le]
      congr 1
      ring
    exact e.le.trans (tsub_le_tsub_right (tsub_le_tsub_right hsep _) _)
  · have hball : supportQ D E (f i) ⊆ centredBall D E (ENNReal.ofReal ρ.toReal) := by
      rw [ENNReal.ofReal_toReal hρ'.ne]
      exact hS i
    exact (hNbhd D E _ _ (hf.2.1 i) (hf.2.1 i) (d / 3) (d / 3) h3 h3).2.2 ρ.toReal
      (ENNReal.toReal_pos hρ.ne' hρ'.ne) hball
theorem exists_familyApproximant (hNbhd : CompactNhdProperties)
    (hQuot : Kind.QuotientCompactC1.Claim)
    (hCount : CountableChoiceFamilyFacts)
    (hElem : C1ProductsAndThickenings.Statement)
    (hFacts : DenseFamilies.Claim)
    (F : DenseChoiceFamily D E) {n : ℕ} (hn : 1 ≤ n) (f : FnTuple D E n)
    (hf : f ∈ sepC1Tuples D E n) (d : ℝ) (hd : 0 < d)
    (hdf : ENNReal.ofReal d ≤ supportGap D E f) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : FnTuple D E n, IsFamilyApproximant D E f hf d hd F ε φ := by
  have h3 : 0 < d / 3 := div_pos hd three_pos
  have hI := thickenings_compact_separated hNbhd f hf d hd hdf
  have hdist0 : ∀ z : E.Pt D, quotDist D E z z = 0 := fun z =>
    ((hQuot D E).1.2.1 z z).2 rfl
  have hopen : ∀ i, IsOpenQ D E (openSupportThickening D E f hf d hd i) ∧
      supportQ D E (f i) ⊆ openSupportThickening D E f hf d hd i ∧
      openSupportThickening D E f hf d hd i ⊆
        closedSupportThickening D E f hf d hd i := fun i => by
    obtain ⟨h1, -, h2, h4, -⟩ := (hNbhd D E _ _ (hf.2.1 i) (hf.2.1 i) (d / 3) (d / 3) h3 h3).1
    exact ⟨h1, h2, h4⟩
  have hQ : ∀ i, ∃ Q ∈ supportStock D E, supportQ D E (f i) ⊆ Q ∧
      Q ⊆ openSupportThickening D E f hf d hd i := fun i =>
    (hCount D E).2.2.1 _ _ (hf.2.1 i) (hopen i).1 (hopen i).2.1
  choose Q hQs hSQ hQW using hQ
  let Q' : Fin n → supportStock D E := fun i => ⟨Q i, hQs i⟩
  have hdisj : Pairwise fun i j => Disjoint (Q' i : Set (E.Pt D)) (Q' j : Set (E.Pt D)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hzA := (hopen i).2.2 (hQW i hzi)
    have hzA' := (hopen j).2.2 (hQW j hzj)
    have hle : setInfDist D E (closedSupportThickening D E f hf d hd i)
        (closedSupportThickening D E f hf d hd j) ≤ ENNReal.ofReal (quotDist D E z z) :=
      iInf₂_le_of_le z hzA (iInf₂_le z hzA')
    have hpos := hI.2.1 i j hij
    rw [hdist0, ENNReal.ofReal_zero] at hle
    have h0 : ENNReal.ofReal (d / 3) ≤ 0 := hpos.trans hle
    exact absurd (ENNReal.ofReal_pos.2 h3) (not_lt.2 h0)
  have hfmem : ∀ i, f i ∈ c1VanishingOutside D E (Q' i : Set (E.Pt D)) := fun i =>
    ⟨hf.1 i, fun y hy => by
      by_contra hne
      refine hy (hSQ i ?_)
      intro r hr
      exact ⟨y, hne, by rw [hdist0]; exact hr⟩⟩
  have hdense : ∀ i, ∃ g ∈ F.sets (Q' i), euclidC1Norm D E (f i - g) < ENNReal.ofReal ε :=
    fun i => (F.isDense (Q' i)).2.2 _ (hfmem i) ε hε
  choose φ hφ hφε using hdense
  have hformed : F.Builds φ Q' := ⟨hdisj, hφ⟩
  have hmember : (⟨n, φ⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ F.tuples := ⟨hn, Q', hformed⟩
  have hM := ((hFacts D E).2 F n hn).2 φ Q' hmember hformed
  refine ⟨φ, hmember, fun i => ⟨(hφε i).le, ?_, (hM.2.1 i).trans (hQW i), (hopen i).2.2⟩⟩
  obtain ⟨hEq, ⟨W, hWeq⟩, -⟩ := (hFacts D E).1.1 _ (hQs i)
  have hsub : f i - φ i ∈ c1VanishingOutside D E (Q i) := by
    rw [← hWeq]
    refine W.sub_mem ?_ ?_
    · change f i ∈ (W : Set (E.Pt D → ℝ))
      rw [hWeq]
      exact hfmem i
    · change φ i ∈ (W : Set (E.Pt D → ℝ))
      rw [hWeq]
      exact (F.isDense (Q' i)).2.1 (hφ i)
  have hcl : f i - φ i ∈ c1SupportedIn D E (Q i) := hEq ▸ hsub
  have hsharp := ((hElem D E).1.1 _ hcl.1 hcl.2.1).2.2.2.2
  have hM0 : 0 ≤ 40 * D.M := by
    have := D.one_le_M
    linarith
  calc sharpNormQ D E (f i - φ i)
      ≤ ENNReal.ofReal (40 * D.M) * euclidC1Norm D E (f i - φ i) := hsharp
    _ ≤ ENNReal.ofReal (40 * D.M) * ENNReal.ofReal ε := by gcongr; exact (hφε i).le
    _ = ENNReal.ofReal (40 * D.M * ε) := (ENNReal.ofReal_mul hM0).symm
theorem multilinear_stable_under_approx (hNbhd : CompactNhdProperties)
    (hElem : C1ProductsAndThickenings.Statement)
    (hClasses : VectorClasses.Claim)
    (hFacts : DenseFamilies.Claim)
    (hForms : Multilinear.MultilinearTelescopingBound)
    (F : DenseChoiceFamily D E) {n : ℕ} (hn : 1 ≤ n) (f : FnTuple D E n)
    (hf : f ∈ sepC1Tuples D E n) (d : ℝ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    MultilinearStableUnderApprox D E f hf d hd F ε := by
  intro φ hφ c hc Ψ hΨ hb
  have h3 : 0 < d / 3 := div_pos hd three_pos
  have hM0 : 0 ≤ 40 * D.M := by
    have := D.one_le_M
    linarith
  set A := closedSupportThickening D E f hf d hd with hA
  have hSA : ∀ i, supportQ D E (f i) ⊆ A i := fun i => by
    obtain ⟨-, -, h2, h4, -⟩ := (hNbhd D E _ _ (hf.2.1 i) (hf.2.1 i) (d / 3) (d / 3) h3 h3).1
    exact h2.trans h4
  have hfc : ∀ i, f i ∈ c1SupportedIn D E (A i) := fun i => ⟨hf.1 i, hf.2.1 i, hSA i⟩
  obtain ⟨Q, hQ⟩ := ((hFacts D E).2 F n hn).1 φ hφ.1
  have hMem := ((hFacts D E).2 F n hn).2 φ Q hφ.1 hQ
  have hφc : ∀ i, φ i ∈ c1SupportedIn D E (A i) := fun i =>
    ⟨(hMem.1 i).1, (hMem.1 i).2.1, ((hφ.2 i).2.2.1).trans ((hφ.2 i).2.2.2)⟩
  have hW : ∀ l, ∃ W : Submodule ℝ (E.Pt D → ℝ),
      (W : Set (E.Pt D → ℝ)) = c1SupportedIn D E (A l) := fun l => ((hClasses D E).1 (A l)).2.1
  choose W hW using hW
  have hWm : ∀ l (x : W l), (x : E.Pt D → ℝ) ∈ c1SupportedIn D E (A l) := fun l x => by
    rw [← hW l]
    exact x.2
  have hWc : ∀ l (u : E.Pt D → ℝ), u ∈ c1SupportedIn D E (A l) → u ∈ W l := fun l u hu => by
    change u ∈ (W l : Set (E.Pt D → ℝ))
    rw [hW l]
    exact hu
  have hN := (hClasses D E).2.1.2
  have hUniv : ∀ l (x : W l), (x : E.Pt D → ℝ) ∈ lipschitzSupportedIn D E Set.univ := fun l x => by
    have h' := (hElem D E).1.2.1 (A l) (hWm l x)
    exact ⟨h'.1, h'.2.1, Set.subset_univ _⟩
  have hAdd : ∀ l (x y : W l), sharpNormReal D E ((x + y : W l) : E.Pt D → ℝ) ≤
      sharpNormReal D E (x : E.Pt D → ℝ) + sharpNormReal D E (y : E.Pt D → ℝ) := by
    intro l x y
    have hx := (hN.lt_top _ (hUniv l x)).ne
    have hy := (hN.lt_top _ (hUniv l y)).ne
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hx, hy⟩)
      (hN.add_le _ (hUniv l x) _ (hUniv l y))
    rwa [ENNReal.toReal_add hx hy] at this
  have hSmul : ∀ l (a : ℝ) (x : W l), sharpNormReal D E ((a • x : W l) : E.Pt D → ℝ) =
      ‖a‖ * sharpNormReal D E (x : E.Pt D → ℝ) := by
    intro l a x
    have := hN.smul _ (hUniv l x) a
    simp only [sharpNormReal, Submodule.coe_smul]
    rw [this, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg a), Real.norm_eq_abs]
  let p : ∀ l, Seminorm ℝ (W l) := fun l =>
    Seminorm.of (fun h => sharpNormReal D E (h : E.Pt D → ℝ)) (hAdd l) (hSmul l)
  have hmem : ∀ x : (∀ l, W l), (fun l => (x l : E.Pt D → ℝ)) ∈
      thickeningC1Product D E f hf d hd := fun x l _ => hWm l (x l)
  have hU : ∀ (m : ∀ l, W l) (i : Fin n) (x : W i),
      (fun l => (Function.update m i x l : E.Pt D → ℝ)) =
        Function.update (fun l => (m l : E.Pt D → ℝ)) i (x : E.Pt D → ℝ) := by
    intro m i x
    funext l
    by_cases h : l = i
    · subst h
      simp
    · simp [Function.update_of_ne h]
  have hUm : ∀ (m : ∀ l, W l) (i : Fin n) (x : W i),
      Function.update (fun l => (m l : E.Pt D → ℝ)) i (x : E.Pt D → ℝ) ∈
        thickeningC1Product D E f hf d hd := by
    intro m i x
    rw [← hU]
    exact hmem _
  have hlin : ∀ (m : ∀ l, W l) (i : Fin n) (x y : W i) (α β : ℝ),
      Ψ ⟨_, hmem (Function.update m i (α • x + β • y))⟩ =
        α * Ψ ⟨_, hmem (Function.update m i x)⟩ + β * Ψ ⟨_, hmem (Function.update m i y)⟩ := by
    intro m i x y α β
    have key := hΨ.2 (fun l => (m l : E.Pt D → ℝ)) (hmem m) i x (hWm i x) y (hWm i y) α β
      (hUm m i x) (hUm m i y) (hUm m i (α • x + β • y))
    have e0 : Ψ ⟨_, hmem (Function.update m i (α • x + β • y))⟩ =
        Ψ ⟨_, hUm m i (α • x + β • y)⟩ := congrArg Ψ (Subtype.ext (hU _ _ _))
    have e1 : Ψ ⟨_, hmem (Function.update m i x)⟩ = Ψ ⟨_, hUm m i x⟩ :=
      congrArg Ψ (Subtype.ext (hU _ _ _))
    have e2 : Ψ ⟨_, hmem (Function.update m i y)⟩ = Ψ ⟨_, hUm m i y⟩ :=
      congrArg Ψ (Subtype.ext (hU _ _ _))
    rw [e0, e1, e2]
    exact key
  let M : MultilinearMap ℝ (fun l => W l) ℝ :=
    { toFun := fun x => Ψ ⟨_, hmem x⟩
      map_update_add' := by
        intro inst m i x y
        obtain rfl : inst = (fun a b => instDecidableEqFin n a b) := Subsingleton.elim _ _
        have := hlin m i x y 1 1
        simpa using this
      map_update_smul' := by
        intro inst m i a x
        obtain rfl : inst = (fun a b => instDecidableEqFin n a b) := Subsingleton.elim _ _
        have := hlin m i x x a 0
        simpa using this }
  have hbound : ∀ h : (∀ l, W l), |M h| ≤ c * ∏ l, p l (h l) := by
    intro h
    have hfin : ENNReal.ofReal c * ∏ l, sharpNormQ D E (h l : E.Pt D → ℝ) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.prod_ne_top fun l _ => (hN.lt_top _ (hUniv l (h l))).ne)
    have key := ENNReal.toReal_mono hfin (hb ⟨_, hmem h⟩)
    rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_ofReal hc,
      ENNReal.toReal_prod] at key
    exact key
  let f' : ∀ l, W l := fun l => ⟨f l, hWc l _ (hfc l)⟩
  let g' : ∀ l, W l := fun l => ⟨φ l, hWc l _ (hφc l)⟩
  refine ⟨hmem f', hmem g', ?_⟩
  have key := (hForms n hn (fun l => W l) p c hc M hbound f' g').1
  refine le_trans key (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) hc)
  have hε' : 0 ≤ 40 * D.M * ε := mul_nonneg hM0 hε.le
  have het : ∀ k, p k (f' k - g' k) ≤ 40 * D.M * ε := fun k =>
    ENNReal.toReal_le_of_le_ofReal hε' (hφ.2 k).2.1
  refine prod_term_le l (fun k => p k (f' k)) (fun k => p k (g' k)) (p l (f' l - g' l))
    (40 * D.M * ε) (fun k => apply_nonneg _ _) (fun k => apply_nonneg _ _) (apply_nonneg _ _)
    (het l) fun k => ?_
  have hsub : p k (g' k) ≤ p k (f' k) + p k (f' k - g' k) := by
    have h := map_sub_le_add (p k) (f' k) (f' k - g' k)
    simpa using h
  have hk := het k
  change p k (g' k) ≤ p k (f' k) + 40 * D.M * ε
  linarith
theorem approxDefect_tendsto {n : ℕ} (f : FnTuple D E n) :
    Filter.Tendsto (approxDefect D E f) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (approxDefect D E f) := by
    change Continuous fun ε : ℝ => ∑ i, 40 * D.M * ε *
      ∏ l ∈ Finset.univ.erase i, (sharpNormReal D E (f l) + 40 * D.M * ε)
    fun_prop
  have h0 : approxDefect D E f 0 = 0 := by
    simp [approxDefect]
  have h := hc.tendsto 0
  rw [h0] at h
  exact h.mono_left nhdsWithin_le_nhds
theorem statement_holds (hNbhd : CompactNhdProperties)
    (hQuot : Kind.QuotientCompactC1.Claim)
    (hCount : CountableChoiceFamilyFacts)
    (hElem : C1ProductsAndThickenings.Statement)
    (hClasses : VectorClasses.Claim)
    (hFacts : DenseFamilies.Claim)
    (hForms : Multilinear.MultilinearTelescopingBound) :
    DiagonalLimits.FamilyApproximation.Statement := by
  intro D E F n hn f hf d hd hdf ε hε
  have hn1 : 1 ≤ n := by omega
  exact ⟨thickenings_compact_separated hNbhd f hf d hd hdf,
    exists_familyApproximant hNbhd hQuot hCount hElem hFacts F hn1 f hf d hd hdf ε hε,
    multilinear_stable_under_approx hNbhd hElem hClasses hFacts hForms F hn1 f hf d hd ε hε,
    approxDefect_tendsto f⟩
end YangMills.Construction.PeriodicSpace.DiagonalLimits.FamilyApproximation
end
