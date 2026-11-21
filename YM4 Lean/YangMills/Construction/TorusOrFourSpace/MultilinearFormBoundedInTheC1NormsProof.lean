import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNormProof
import YangMills.Construction.TorusOrFourSpace.DistanceOpenSetsDerivativesAndTensorsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.FormsOfACutOffOnThePeriodBox
import YangMills.Construction.TorusOrFourSpace.MultilinearFormBoundedInTheC1Norms
import YangMills.Construction.TorusOrFourSpace.SmallFactsOnLiftsProductsAndDistributions
import YangMills.Construction.TorusOrFourSpace.TensorApproximationsUnderACutOff
import Mathlib
set_option autoImplicit false
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.Tuple
variable {D : Params} {E : Kind} {n : ℕ+}
private theorem isCompactWrt_union {X : Type*} {d : X → X → ℝ} {A A' : Set X}
    (hA : MetricNotions.IsCompactWrt d A) (hA' : MetricNotions.IsCompactWrt d A') :
    MetricNotions.IsCompactWrt d (A ∪ A') := by apply _root_.YangMills.SharedProofs.p57694 <;> assumption
private theorem mem_cell_of_euclidNormVec_le {r : ℝ} (hr : 0 < r) (u : Fin 4 → ℝ)
    (hu : TorusMetric.euclidNormVec u ≤ r) : u ∈ PeriodCell.cell (4 * r) := by
  intro μ
  have h1 : (u μ) ^ 2 ≤ ∑ ν, (u ν) ^ 2 :=
    Finset.single_le_sum (f := fun ν => (u ν) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
  have h2 : |u μ| ≤ r :=
    calc |u μ| = Real.sqrt ((u μ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (∑ ν, (u ν) ^ 2) := Real.sqrt_le_sqrt h1
      _ ≤ r := hu
  have h3 := abs_le.mp h2
  constructor <;> linarith [h3.1, h3.2]
abbrev _root_.YangMills.SharedProofs.p89512 := @mem_cell_of_euclidNormVec_le
private theorem map_finset_sum_of_linear {Ω : Set (E.Tuple D n)}
    {S : Submodule ℂ (E.Tuple D n → ℂ)}
    (hS : (S : Set (E.Tuple D n → ℂ)) = testFns D E Ω)
    {T : testFns D E Ω → ℂ} (hT : IsComplexLinearForm T)
    {τ : (E.Tuple D n → ℂ) → ℂ} (hτ : ∀ F : testFns D E Ω, τ F.1 = T F)
    {ι : Type*} (s : Finset ι) (f : ι → E.Tuple D n → ℂ)
    (hf : ∀ l ∈ s, f l ∈ testFns D E Ω) :
    τ (∑ l ∈ s, f l) = ∑ l ∈ s, τ (f l) := by
  classical
  have hmem : ∀ G, G ∈ testFns D E Ω ↔ G ∈ S := fun G => by
    rw [← hS]
    rfl
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (0 : E.Tuple D n → ℂ) ∈ testFns D E Ω := (hmem _).2 S.zero_mem
    have h1 := hT.2 0 ⟨0, h0⟩ ⟨0, h0⟩ (by simp)
    simp only [Finset.sum_empty]
    calc τ 0 = T ⟨0, h0⟩ := hτ ⟨0, h0⟩
      _ = 0 * T ⟨0, h0⟩ := h1
      _ = 0 := zero_mul _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : ∀ l ∈ s, f l ∈ testFns D E Ω := fun l hl =>
      hf l (Finset.mem_insert_of_mem hl)
    have ha' := hf a (Finset.mem_insert_self a s)
    have hsum : (∑ l ∈ s, f l) ∈ testFns D E Ω :=
      (hmem _).2 (sum_mem fun l hl => (hmem _).1 (hs l hl))
    have hadd : (f a + ∑ l ∈ s, f l) ∈ testFns D E Ω :=
      (hmem _).2 (S.add_mem ((hmem _).1 ha') ((hmem _).1 hsum))
    have h1 := hT.1 ⟨f a, ha'⟩ ⟨_, hsum⟩ ⟨_, hadd⟩ rfl
    calc τ (f a + ∑ l ∈ s, f l) = T ⟨_, hadd⟩ := hτ ⟨_, hadd⟩
      _ = T ⟨f a, ha'⟩ + T ⟨_, hsum⟩ := h1
      _ = τ (f a) + τ (∑ l ∈ s, f l) :=
        congrArg₂ (· + ·) (hτ ⟨f a, ha'⟩).symm (hτ ⟨_, hsum⟩).symm
      _ = τ (f a) + ∑ l ∈ s, τ (f l) := by rw [ih hs]
private theorem apply_tensorProd_eq {O : Fin (n : ℕ) → Set (E.Pt D)}
    (hcf : ∀ i, ComplexSupportedFacts D E (O i)) (hO : ∀ i, Kind.IsOpenQ D E (O i))
    (hTT : TupleFacts.TensorTestFns D E n)
    (hML : TupleFacts.TensorMultilinear D E n)
    {c : ℝ} {B : C1Components D E O → ℝ} {Bc : (Fin (n : ℕ) → E.Pt D → ℂ) → ℂ}
    (hBc : IsBoundedComplexMultiform D E O c Bc)
    (hval : ∀ g : ∀ i, Kind.c1SupportedIn D E (O i), Bc (fun i y => ((g i).1 y : ℂ)) = (B g : ℂ))
    {T : testFns D E (boxSet D E O) → ℂ} (hT : IsDistribExtending B T)
    (S : Finset (Fin (n : ℕ))) :
    ∀ h : Fin (n : ℕ) → E.Pt D → ℂ, (∀ i, h i ∈ singleTestFns D E (O i)) →
      (∀ i, i ∉ S → ∃ g : E.Pt D → ℝ, h i = fun y => (g y : ℂ)) →
      ∀ hF : tensorProd D E h ∈ testFns D E (boxSet D E O), T ⟨_, hF⟩ = Bc h := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro h hm hr hF
    choose g hg using fun i => hr i (by simp)
    have hh : h = fun i y => (g i y : ℂ) := funext hg
    subst hh
    obtain ⟨hφ, hF', e⟩ := hT.2 g hm
    exact e.trans (hval fun i => ⟨g i, hφ i⟩).symm
  | insert a S ha ih =>
    intro h hm hr hF
    let u : E.Pt D → ℂ := fun y => ((h a y).re : ℂ)
    let v : E.Pt D → ℂ := fun y => ((h a y).im : ℂ)
    obtain ⟨hu, hv⟩ : u ∈ singleTestFns D E (O a) ∧
        v ∈ singleTestFns D E (O a) := (hcf a).2.2.2.1 _ (hm a)
    obtain ⟨Sb, hSb⟩ := (hcf a).2.1
    have hw : Complex.I • v ∈ singleTestFns D E (O a) := by
      have hv' : v ∈ Sb := by
        rw [← SetLike.mem_coe, hSb]
        exact hv
      rw [← hSb]
      exact Sb.smul_mem _ hv'
    have hupd : ∀ w ∈ singleTestFns D E (O a), ∀ i,
        Function.update h a w i ∈ singleTestFns D E (O i) := by
      intro w hw' i
      by_cases e : i = a
      · rw [Function.update_apply, if_pos e, e]
        exact hw'
      · rw [Function.update_apply, if_neg e]
        exact hm i
    have hreal : ∀ w : E.Pt D → ℂ, (∃ g : E.Pt D → ℝ, w = fun y => (g y : ℂ)) →
        ∀ i, i ∉ S → ∃ g : E.Pt D → ℝ, Function.update h a w i = fun y => (g y : ℂ) := by
      intro w hwr i hi
      by_cases e : i = a
      · rw [Function.update_apply, if_pos e]
        exact hwr
      · rw [Function.update_apply, if_neg e]
        exact hr i (by simp [Finset.mem_insert, e, hi])
    have hfu := hTT O _ hO (hupd u hu)
    have hfv := hTT O _ hO (hupd v hv)
    have hfw := hTT O _ hO (hupd _ hw)
    have hdec : u + Complex.I • v = h a := by
      funext y
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, u, v]
      rw [mul_comm]
      exact Complex.re_add_im _
    have hh : Function.update h a (u + Complex.I • v) = h := by
      rw [hdec, Function.update_eq_self]
    have e1 := (hML h a u (Complex.I • v) 1).1
    rw [hh] at e1
    have e2 := (hML h a v v Complex.I).2
    have s1 := hT.1.1.1 ⟨_, hfu⟩ ⟨_, hfw⟩ ⟨_, hF⟩ e1
    have s2 := hT.1.1.2 Complex.I ⟨_, hfv⟩ ⟨_, hfw⟩ e2
    have hcl : ∀ i, h i ∈ complexC1SupportedIn D E (O i) := fun i => (hcf i).2.2.1 (hm i)
    have b1 := hBc.1 h a u (Complex.I • v) hcl ((hcf a).2.2.1 hu) ((hcf a).2.2.1 hw)
    rw [hh] at b1
    have b2 := hBc.2.1 h a v Complex.I hcl ((hcf a).2.2.1 hv)
    rw [s1, s2, ih _ (hupd u hu) (hreal u ⟨_, rfl⟩) hfu, ih _ (hupd v hv) (hreal v ⟨_, rfl⟩) hfv,
      b1, b2]
theorem c1BoundedForm_isDistribution (hTA : PeriodCell.TensorApproxUnderCutoff)
    (hForms : PeriodCell.CutoffFormsExist)
    (hExt : ComplexExtensionClaim)
    (hClass : ComplexSupportedClassesClaim)
    (hModes : PeriodCell.CutoffModeBounds)
    (hPts : TupleFacts.AllFacts)
    (hFacts : LiftsProductsDistributions.Statement) :
    C1BoundedFormDistribution := by
  intro D n r c hr hc O hO hOr B hlinB hbdB
  obtain ⟨-, -, hMetric, -, -, -, -, -, -, -, -, hProd, hProj, -, -, -, -, -, -, hStable, -, -,
    hTT, hML⟩ := hPts D Kind.euclidean n
  obtain ⟨-, -, -, -, -, -, hSeq⟩ := hFacts D Kind.euclidean
  obtain ⟨exCut, cutFor, sub, approx⟩ := hTA D n r hr O hO hOr
  obtain ⟨Bc, hBc, hval⟩ := hExt D Kind.euclidean n c hc O hO B hlinB hbdB
  obtain ⟨Tc, hTc⟩ := hForms D n r c hr hc O hO hOr Bc hBc
  have hcf : ∀ i, ComplexSupportedFacts D Kind.euclidean (O i) := fun i =>
    hClass D Kind.euclidean (O i) (hO i)
  have hcell : ∀ i, O i ⊆ PeriodCell.cell (4 * r) := fun i u hu =>
    mem_cell_of_euclidNormVec_le hr u (hOr i u hu)
  have hincell : ∀ i, singleTestFns D Kind.euclidean (O i) ⊆
      singleTestFns D Kind.euclidean (PeriodCell.cell (4 * r)) := fun i =>
    (hModes D r hr (O i) (hO i) (hcell i)).1
  have hBoxOpen : IsOpenT D Kind.euclidean (boxSet D Kind.euclidean O) := (hProd O).1 hO
  obtain ⟨Sp, hSp⟩ := (hStable _ hBoxOpen).1
  have hmemS : ∀ G, G ∈ testFns D Kind.euclidean (boxSet D Kind.euclidean O) ↔ G ∈ Sp :=
    fun G => by
      rw [← hSp]
      rfl
  have hlinP : ∀ χ, IsCutoffFamily D Kind.euclidean O χ →
      IsComplexLinearForm
        (fun F : testFns D Kind.euclidean (boxSet D Kind.euclidean O) => Tc χ F.1) :=
    fun χ hχ =>
      ⟨fun F G H h => (hTc χ hχ).1.1 ⟨F.1, sub F.2⟩ ⟨G.1, sub G.2⟩ ⟨H.1, sub H.2⟩ h,
        fun a F H h => (hTc χ hχ).1.2 a ⟨F.1, sub F.2⟩ ⟨H.1, sub H.2⟩ h⟩
  have hfin : ∀ χ, IsCutoffFamily D Kind.euclidean O χ →
      ENNReal.ofReal (2 ^ (n : ℕ) * c * cutoffBound n r) *
        (∏ i, c1NormSingleReal D Kind.euclidean (χ i)) < ⊤ := by
    intro χ hχ
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact ENNReal.prod_lt_top fun i _ =>
      ((hcf i).2.2.2.2.2.2.2 _ ((hcf i).2.2.1 (hχ i)))
  have hbd : ∀ χ, IsCutoffFamily D Kind.euclidean O χ →
      ∀ F : testFns D Kind.euclidean (boxSet D Kind.euclidean O),
        ENNReal.ofReal ‖Tc χ F.1‖ ≤
          ENNReal.ofReal (2 ^ (n : ℕ) * c * cutoffBound n r) *
            (∏ i, c1NormSingleReal D Kind.euclidean (χ i)) *
              cNorm D Kind.euclidean (5 * (n : ℕ) + 1) F.1 :=
    fun χ hχ F => (hTc χ hχ).2.1 F.1 (sub F.2)
  have hserve : ∀ χ, IsCutoffFamily D Kind.euclidean O χ → ∃ C : ℝ≥0,
      ∀ F : testFns D Kind.euclidean (boxSet D Kind.euclidean O),
        ENNReal.ofReal ‖Tc χ F.1‖ ≤
          (C : ℝ≥0∞) * cNorm D Kind.euclidean (5 * (n : ℕ) + 1) F.1 := by
    intro χ hχ
    refine ⟨(ENNReal.ofReal (2 ^ (n : ℕ) * c * cutoffBound n r) *
      (∏ i, c1NormSingleReal D Kind.euclidean (χ i))).toNNReal, fun F => ?_⟩
    rw [ENNReal.coe_toNNReal (hfin χ hχ).ne]
    exact hbd χ hχ F
  have hdist : ∀ χ, IsCutoffFamily D Kind.euclidean O χ →
      IsDistrib
        (fun F : testFns D Kind.euclidean (boxSet D Kind.euclidean O) => Tc χ F.1) := by
    intro χ hχ
    refine ⟨hlinP χ hχ, fun K _ _ => ⟨5 * (n : ℕ) + 1, ?_⟩⟩
    obtain ⟨C, hC⟩ := hserve χ hχ
    exact ⟨C, fun F _ => hC F⟩
  have hmode : ∀ χ, IsCutoffFamily D Kind.euclidean O χ → ∀ (i : Fin (n : ℕ)) (q : Fin 4 → ℤ),
      PeriodCell.cutoffMode D (4 * r) (χ i) q ∈ singleTestFns D Kind.euclidean (O i) :=
    fun χ hχ i q =>
      (((hModes D r hr (O i) (hO i) (hcell i)).2.2 (χ i) (hχ i)).1 _
        ((hModes D r hr (O i) (hO i) (hcell i)).2.1 q)).1
  have hswap : ∀ χ χ', IsCutoffFamily D Kind.euclidean O χ →
      IsCutoffFamily D Kind.euclidean O χ' →
      ∀ (F : (Kind.euclidean).Tuple D n → ℂ) (t : ℕ+),
        Tc χ' (PeriodCell.cutoffFourierSum D (4 * r) χ F t) =
          ∑ k ∈ IntCoords.cubeUpTo t, PeriodCell.fourierCoeff D (4 * r) F k *
            Bc fun i y => (χ' i y : ℂ) * PeriodCell.cutoffMode D (4 * r) (χ i) (k.block i) y := by
    intro χ χ' hχ hχ' F t
    have hten : ∀ k : IntCoords n,
        tensorProd D Kind.euclidean
            (fun i => PeriodCell.cutoffMode D (4 * r) (χ i) (k.block i)) ∈
          testFns D Kind.euclidean (boxSet D Kind.euclidean O) :=
      fun k => hTT O _ hO fun i => hmode χ hχ i _
    have hsm : ∀ k : IntCoords n, PeriodCell.fourierCoeff D (4 * r) F k •
        tensorProd D Kind.euclidean
            (fun i => PeriodCell.cutoffMode D (4 * r) (χ i) (k.block i)) ∈
          testFns D Kind.euclidean (boxSet D Kind.euclidean O) :=
      fun k => (hmemS _).2 (Sp.smul_mem _ ((hmemS _).1 (hten k)))
    unfold PeriodCell.cutoffFourierSum
    rw [map_finset_sum_of_linear hSp (hlinP χ' hχ') (τ := Tc χ') (fun _ => rfl) _ _
      (fun k _ => hsm k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := (hlinP χ' hχ').2 (PeriodCell.fourierCoeff D (4 * r) F k) ⟨_, hten k⟩ ⟨_, hsm k⟩ rfl
    exact h1.trans (congrArg _ ((hTc χ' hχ').2.2 _ fun i => hincell i (hmode χ hχ i _)))
  have hindep : ∀ (F : testFns D Kind.euclidean (boxSet D Kind.euclidean O)) (χ χ'),
      IsCutoffOf D Kind.euclidean χ F → IsCutoffOf D Kind.euclidean χ' F →
        Tc χ F.1 = Tc χ' F.1 := by
    intro F χ χ' h h'
    obtain ⟨Fs, hFs, -, hconv⟩ := approx F χ h
    obtain ⟨Fs', hFs', -, hconv'⟩ := approx F χ' h'
    have l1 := hSeq n _ hBoxOpen _ (hdist χ' h'.1) Fs F hconv
    have l2 := hSeq n _ hBoxOpen _ (hdist χ h.1) Fs' F hconv'
    have e : ∀ t, Tc χ' (Fs t).1 = Tc χ (Fs' t).1 := by
      intro t
      rw [hFs t, hFs' t, hswap χ χ' h.1 h'.1, hswap χ' χ h'.1 h.1]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hfun : (fun (i : Fin (n : ℕ)) (y : (Kind.euclidean).Pt D) =>
            (χ' i y : ℂ) * PeriodCell.cutoffMode D (4 * r) (χ i) (k.block i) y) =
          fun i y => (χ i y : ℂ) * PeriodCell.cutoffMode D (4 * r) (χ' i) (k.block i) y := by
        funext i y
        simp only [PeriodCell.cutoffMode]
        ring
      rw [hfun]
    exact tendsto_nhds_unique l2 (Filter.Tendsto.congr e l1)
  have hcommon : ∀ K, IsCompactT D Kind.euclidean K → K ⊆ boxSet D Kind.euclidean O →
      ∃ χ, IsCutoffFamily D Kind.euclidean O χ ∧
        ∀ F : testFns D Kind.euclidean (boxSet D Kind.euclidean O),
          supportT D Kind.euclidean F.1 ⊆ K → IsCutoffOf D Kind.euclidean χ F := by
    intro K hK hKO
    obtain ⟨χ, hχ, h1⟩ := exCut (fun i => (fun y : (Kind.euclidean).Tuple D n => y i) '' K)
      (fun i => (hProj i).2 K hK) (by
        rintro i _ ⟨y, hy, rfl⟩
        exact hKO hy i)
    exact ⟨χ, hχ, fun F hF => cutFor F χ hχ fun i y hy => h1 i _ ⟨y, hF hy, rfl⟩⟩
  have hpick : ∀ F : testFns D Kind.euclidean (boxSet D Kind.euclidean O),
      ∃ χ, IsCutoffOf D Kind.euclidean χ F := by
    intro F
    obtain ⟨χ, -, h⟩ := hcommon _ F.2.2.1 F.2.2.2
    exact ⟨χ, h F subset_rfl⟩
  choose pick hpickspec using hpick
  obtain ⟨T0, hT0def⟩ : ∃ T0 : testFns D Kind.euclidean (boxSet D Kind.euclidean O) → ℂ,
      ∀ F, T0 F = Tc (pick F) F.1 := ⟨_, fun _ => rfl⟩
  have hT0 : ∀ (F : testFns D Kind.euclidean (boxSet D Kind.euclidean O)) (χ),
      IsCutoffOf D Kind.euclidean χ F → T0 F = Tc χ F.1 := fun F χ h => by
    rw [hT0def]
    exact hindep F _ χ (hpickspec F) h
  have hT0lin : IsComplexLinearForm T0 := by
    constructor
    · intro F G H hH
      obtain ⟨χ, hχ, hcut⟩ := hcommon _
        (isCompactWrt_union (isCompactWrt_union F.2.2.1 G.2.2.1) H.2.2.1)
        (Set.union_subset (Set.union_subset F.2.2.2 G.2.2.2) H.2.2.2)
      rw [hT0 F χ (hcut F (Set.subset_union_left.trans Set.subset_union_left)),
        hT0 G χ (hcut G (Set.subset_union_right.trans Set.subset_union_left)),
        hT0 H χ (hcut H Set.subset_union_right)]
      exact (hlinP χ hχ).1 F G H hH
    · intro a F H hH
      obtain ⟨χ, hχ, hcut⟩ := hcommon _ (isCompactWrt_union F.2.2.1 H.2.2.1)
        (Set.union_subset F.2.2.2 H.2.2.2)
      rw [hT0 F χ (hcut F Set.subset_union_left), hT0 H χ (hcut H Set.subset_union_right)]
      exact (hlinP χ hχ).2 a F H hH
  have hT0order : ∀ K, IsCompactT D Kind.euclidean K → K ⊆ boxSet D Kind.euclidean O →
      HasOrderBoundOn T0 K (5 * (n : ℕ) + 1) := by
    intro K hK hKO
    obtain ⟨χ, hχ, hcut⟩ := hcommon K hK hKO
    obtain ⟨C, hC⟩ := hserve χ hχ
    refine ⟨C, fun F hF => ?_⟩
    rw [hT0 F χ (hcut F hF)]
    exact hC F
  have hT0dist : IsDistrib T0 := ⟨hT0lin, fun K hK hKO => ⟨_, hT0order K hK hKO⟩⟩
  have hself : ∀ (i : Fin (n : ℕ)) (y : (Kind.euclidean).Pt D),
      Kind.quotDist D Kind.euclidean y y ≤ 0 := by
    intro i y
    have h := (hProj i).1 (fun _ => y) (fun _ => y)
    rw [(hMetric.2.1 _ _).2 rfl] at h
    exact h
  have hT0form : IsDistribExtending B T0 := by
    refine ⟨hT0dist, fun φ hφ => ?_⟩
    have hφ1 : ∀ i, φ i ∈ Kind.c1SupportedIn D Kind.euclidean (O i) := fun i =>
      (hcf i).2.2.2.2.1 _ (hφ i)
    have hF : tensorProd D Kind.euclidean (fun i y => (φ i y : ℂ)) ∈
        testFns D Kind.euclidean (boxSet D Kind.euclidean O) := hTT O _ hO hφ
    refine ⟨hφ1, hF, ?_⟩
    have hcl : ∀ i, (fun y => (φ i y : ℂ)) ∈ complexC1SupportedIn D Kind.euclidean (O i) :=
      fun i => (hcf i).2.2.1 (hφ i)
    obtain ⟨χ, hχ, h1⟩ :=
      exCut (fun i => Kind.supportQ D Kind.euclidean fun y => (φ i y : ℂ))
        (fun i => (hcl i).2.1) (fun i => (hcl i).2.2)
    have hmul : ∀ i y, (χ i y : ℂ) * (φ i y : ℂ) = (φ i y : ℂ) := by
      intro i y
      by_cases hy : (φ i y : ℂ) = 0
      · rw [hy, mul_zero]
      · have hs : y ∈ Kind.supportQ D Kind.euclidean fun y => (φ i y : ℂ) := by
          show ∀ s : ℝ, 0 < s → ∃ z ∈ {z | (φ i z : ℂ) ≠ 0}, Kind.quotDist D Kind.euclidean y z < s
          intro s hs
          exact ⟨y, hy, lt_of_le_of_lt (hself i y) hs⟩
        rw [h1 i y hs]
        simp
    have hcutF : IsCutoffOf D Kind.euclidean χ ⟨_, hF⟩ := by
      refine ⟨hχ, ?_⟩
      funext y
      show (∏ i, (χ i (y i) : ℂ)) * ∏ i, (φ i (y i) : ℂ) = ∏ i, (φ i (y i) : ℂ)
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => hmul i (y i)
    rw [hT0 _ χ hcutF]
    have e := (hTc χ hχ).2.2 (fun i y => (φ i y : ℂ)) fun i => hincell i (hφ i)
    have e2 : (fun (i : Fin (n : ℕ)) (y : (Kind.euclidean).Pt D) => (χ i y : ℂ) * (φ i y : ℂ)) =
        fun i y => (φ i y : ℂ) := by
      funext i y
      exact hmul i y
    exact e.trans ((congrArg Bc e2).trans (hval fun i => ⟨φ i, hφ1 i⟩))
  have hsumBc : ∀ T, IsDistribExtending B T →
      ∀ (G : testFns D Kind.euclidean (boxSet D Kind.euclidean O)) (m : ℕ)
        (φ : Fin m → Fin (n : ℕ) → (Kind.euclidean).Pt D → ℂ),
        (∀ l i, φ l i ∈ singleTestFns D Kind.euclidean (O i)) →
        G.1 = ∑ l, tensorProd D Kind.euclidean (φ l) → T G = ∑ l, Bc (φ l) := by
    intro T hT G m φ hφ hG
    classical
    let τ : ((Kind.euclidean).Tuple D n → ℂ) → ℂ := fun H =>
      if h : H ∈ testFns D Kind.euclidean (boxSet D Kind.euclidean O) then T ⟨H, h⟩ else 0
    have hτ : ∀ F : testFns D Kind.euclidean (boxSet D Kind.euclidean O), τ F.1 = T F :=
      fun F => dif_pos F.2
    have hten : ∀ l, tensorProd D Kind.euclidean (φ l) ∈
        testFns D Kind.euclidean (boxSet D Kind.euclidean O) := fun l => hTT O _ hO (hφ l)
    have hs := map_finset_sum_of_linear hSp hT.1.1 hτ Finset.univ
      (fun l => tensorProd D Kind.euclidean (φ l)) (fun l _ => hten l)
    calc T G = τ G.1 := (hτ G).symm
      _ = τ (∑ l, tensorProd D Kind.euclidean (φ l)) := by rw [hG]
      _ = ∑ l, τ (tensorProd D Kind.euclidean (φ l)) := hs
      _ = ∑ l, Bc (φ l) := Finset.sum_congr rfl fun l _ =>
        (hτ ⟨_, hten l⟩).trans
          (apply_tensorProd_eq hcf hO hTT hML hBc hval hT Finset.univ (φ l) (hφ l)
            (fun i hi => absurd (Finset.mem_univ i) hi) (hten l))
  have huniq : ∀ T', IsDistribExtending B T' → T' = T0 := by
    intro T' hT'
    funext F
    obtain ⟨Fs, -, hfs, hconv⟩ := approx F (pick F) (hpickspec F)
    have e : ∀ t, T' (Fs t) = T0 (Fs t) := by
      intro t
      obtain ⟨m, φ, hφ, hG⟩ := hfs t
      rw [hsumBc T' hT' (Fs t) m φ (fun l i => (hφ l i).1) hG,
        hsumBc T0 hT0form (Fs t) m φ (fun l i => (hφ l i).1) hG]
    exact tendsto_nhds_unique (hSeq n _ hBoxOpen T' hT'.1 Fs F hconv)
      (Filter.Tendsto.congr (fun t => (e t).symm) (hSeq n _ hBoxOpen T0 hT0dist Fs F hconv))
  refine ⟨fun F => ⟨?_, ?_, ?_⟩, ExistsUnique.intro T0 hT0form huniq, ?_⟩
  · intro χ hχ h
    exact cutFor F χ hχ fun i y hy => h i _ ⟨y, hy, rfl⟩
  · obtain ⟨χ, hχ, h1⟩ := exCut
      (fun i => coordProj D Kind.euclidean i (supportT D Kind.euclidean F.1))
      (fun i => (hProj i).2 _ F.2.2.1) (by
        rintro i _ ⟨y, hy, rfl⟩
        exact F.2.2.2 hy i)
    exact ⟨χ, hχ, h1⟩
  · intro χ hχ
    obtain ⟨Fs, -, hfs, hconv⟩ := approx F χ hχ
    exact ⟨Fs, hfs, hconv⟩
  · intro T hT
    have hTeq := huniq T hT
    subst hTeq
    refine ⟨fun F χ h => ?_, hT0dist, hT0order⟩
    rw [hT0 F χ h]
    exact hbd χ h.1 F
end YangMills.Construction.PeriodicSpace.Kind.Tuple
