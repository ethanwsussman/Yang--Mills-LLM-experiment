import YangMills.Construction.ReflectionPositivity.FactsOnSeparatedTuplesAndIsometriesOfOneTorus
import YangMills.Construction.ReflectionPositivity.FunctionsOfClassC1OnOneTorus
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import YangMills.Construction.Torus.LipschitzTuplesWithDisjointSupportsOnATorus
import YangMills.Construction.Torus.OneSpaceOneDistanceOneClassOfTestFunctions
import Mathlib
set_option autoImplicit false
open scoped ENNReal
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
noncomputable section
namespace YangMills.Construction.TorusLipschitzTuples
open YangMills.Construction.ReflectionPositivity
variable {s : Conventions.StandingParameters}
theorem tsupport_eq_supp (h : AmbientPoints.Pt s .torus → ℝ) :
    tsupport h = TorusTuples.supp (s := s) h :=
  AmbientPoints.closure_eq_closureWrt (Function.support h)
theorem closedSupport_axisMirror_eq_tsupport (β : ℝ) (hβ : 0 < β)
    (h : AmbientPoints.Pt s .torus → ℝ) :
    Ambient.closedSupport (axisMirrorData s β hβ) .torus h = tsupport h :=
  (AmbientPoints.closure_eq_closureWrt (Function.support h)).symm
theorem isCompact_univ_pt (hc : CutoffMirrors.TorusMetricSpace.MetricTorusFacts) :
    IsCompact (Set.univ : Set (AmbientPoints.Pt s .torus)) :=
  (AmbientPoints.isCompact_iff_isCompactWrt _).2 (hc (TorusTuples.unitData s)).1.2.2.2.2
theorem isCompact_tsupport_pt
    (hc : CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (h : AmbientPoints.Pt s .torus → ℝ) : IsCompact (tsupport h) :=
  (isCompact_univ_pt hc).of_isClosed_subset (isClosed_tsupport h) (Set.subset_univ _)
theorem list_get_ofFn_cast {n : ℕ} (f : Fin n → s.Torus → ℝ) (l : Fin (List.ofFn f).length) :
    (List.ofFn f).get l = f (l.cast List.length_ofFn) := by
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  rfl
theorem disjoint_iff_inter_eq_empty_of_eq {X : Type*} {A B A' B' : Set X} (hA : A = A')
    (hB : B = B') : Disjoint A B ↔ A' ∩ B' = ∅ := by
  subst hA hB
  exact Set.disjoint_iff_inter_eq_empty
theorem disjoint_tsupport_iff_supp_inter (g h : AmbientPoints.Pt s .torus → ℝ) :
    Disjoint (tsupport g) (tsupport h) ↔
      (TorusTuples.unitData s).supp g ∩ (TorusTuples.unitData s).supp h = ∅ :=
  disjoint_iff_inter_eq_empty_of_eq (tsupport_eq_supp g) (tsupport_eq_supp h)
theorem mem_lipTuples_iff
    (hc : CutoffMirrors.TorusMetricSpace.MetricTorusFacts) {n : ℕ}
    (f : FnFamily s n) : f ∈ lipTuples s n ↔ TorusTuples.IsDisjointFamily (s := s) f := by
  constructor
  · rintro ⟨hlip, -, hdis⟩
    exact ⟨fun l => hlip l, fun l l' hl => (disjoint_tsupport_iff_supp_inter _ _).1 (hdis l l' hl)⟩
  · rintro ⟨hlip, hdis⟩
    exact ⟨fun l => hlip l, fun l => isCompact_tsupport_pt hc _, fun l l' hl =>
      (disjoint_tsupport_iff_supp_inter _ _).2 (hdis l l' hl)⟩
theorem supportGap_eq_gap {n : ℕ} (f : FnFamily s n) :
    AmbientPoints.supportGap f = TorusTuples.gap (componentList s f) := by
  have hd : ∀ i i' : Fin n, AmbientPoints.setDist s .torus (tsupport (f i)) (tsupport (f i')) =
      TorusCutoffs.setDist (TorusTuples.supp (s := s) (f i)) (TorusTuples.supp (s := s) (f i')) :=
    fun i i' => by
      rw [tsupport_eq_supp, tsupport_eq_supp]
      rfl
  have hg : ∀ l : Fin (List.ofFn f).length, (componentList s f).get l = f (l.cast List.length_ofFn) :=
    fun l => list_get_ofFn_cast f l
  have hD : ∀ l l' : Fin (List.ofFn f).length,
      TorusCutoffs.setDist (TorusTuples.supp (s := s) ((componentList s f).get l))
        (TorusTuples.supp (s := s) ((componentList s f).get l')) =
      AmbientPoints.setDist s .torus (tsupport (f (l.cast List.length_ofFn)))
        (tsupport (f (l'.cast List.length_ofFn))) := fun l l' =>
    (congrArg₂ (fun A B : s.Torus → ℝ => TorusCutoffs.setDist (TorusTuples.supp (s := s) A)
      (TorusTuples.supp (s := s) B)) (hg l) (hg l')).trans (hd _ _).symm
  apply le_antisymm
  · refine Finset.le_inf fun p hp => ?_
    have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    exact (iInf_le_of_le (p.1.cast List.length_ofFn) (iInf_le_of_le (p.2.cast List.length_ofFn)
      (iInf_le_of_le (fun e => hne (Fin.cast_injective _ e)) le_rfl))).trans_eq (hD p.1 p.2).symm
  · refine le_iInf fun i => le_iInf fun i' => le_iInf fun hne => ?_
    have hp : ((i.cast List.length_ofFn.symm, i'.cast List.length_ofFn.symm) :
        Fin (componentList s f).length × Fin (componentList s f).length) ∈
        (Finset.univ.offDiag : Finset (Fin (componentList s f).length × Fin (componentList s f).length)) := by
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
      exact fun e => hne (Fin.cast_injective _ e)
    exact (Finset.inf_le hp).trans_eq (hD _ _)
theorem supportGap_pos
    (hc : CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (ht : TorusTuples.SeparationAndSymmetry.Statement) {n : ℕ} (hn : 2 ≤ n)
    {f : FnFamily s n} (hf : f ∈ lipTuples s n) : 0 < AmbientPoints.supportGap f := by
  rw [supportGap_eq_gap]
  exact (ht s).1 _ ((TorusTuples.isDisjointTuple_ofFn f).2 ((mem_lipTuples_iff hc f).1 hf))
    (hn.trans_eq (List.length_ofFn (f := f)).symm)
theorem disjointTuples_eq_image_lipTuples
    (hc : CutoffMirrors.TorusMetricSpace.MetricTorusFacts) (n : ℕ) :
    TorusTuples.disjointTuples s n = componentList s '' lipTuples s n := by
  ext X
  constructor
  · rintro ⟨hX, hl⟩
    refine ⟨TorusTuples.componentFamily X hl, (mem_lipTuples_iff hc _).2 ?_,
      TorusTuples.ofFn_componentFamily X hl⟩
    refine (TorusTuples.isDisjointTuple_ofFn _).1 ?_
    rw [TorusTuples.ofFn_componentFamily]
    exact hX
  · rintro ⟨f, hf, rfl⟩
    exact ⟨(TorusTuples.isDisjointTuple_ofFn f).2 ((mem_lipTuples_iff hc f).1 hf),
      List.length_ofFn⟩
theorem componentList_mem_disjointC1Tuples_iff {q : ℕ} (f : FnFamily s q) :
    componentList s f ∈ TorusTuples.disjointC1Tuples s q ↔
      TorusTuples.IsDisjointFamily (s := s) f ∧ ∀ i, TorusCutoffs.IsC1 (s := s) (f i) := by
  constructor
  · rintro ⟨⟨hdis, -⟩, hC⟩
    exact ⟨(TorusTuples.isDisjointTuple_ofFn f).1 hdis,
      fun i => hC _ ((List.mem_ofFn' _ _).2 ⟨i, rfl⟩)⟩
  · rintro ⟨hdis, hC⟩
    refine ⟨⟨(TorusTuples.isDisjointTuple_ofFn f).2 hdis, List.length_ofFn⟩, fun g hg => ?_⟩
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact hC i
theorem isLipschitzReal_of_isC1 (h1 : TorusC1.C1Properties)
    {g : s.Torus → ℝ} (hg : TorusCutoffs.IsC1 (s := s) g) :
    TorusTuples.IsLipschitzReal (s := s) g :=
  (h1 s g hg).2.1.2.1
theorem mem_ambient_separatedTuples_iff
    (hc : CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (h1 : TorusC1.C1Properties) {q : ℕ} (f : FnFamily s q) :
    f ∈ AmbientPoints.separatedTuples s .torus q ↔
      TorusTuples.IsDisjointFamily (s := s) f ∧ ∀ i, TorusCutoffs.IsC1 (s := s) (f i) := by
  constructor
  · rintro ⟨hC, hdis⟩
    exact ⟨⟨fun l => isLipschitzReal_of_isC1 h1 (hC l).1, fun l l' hl =>
      (disjoint_tsupport_iff_supp_inter _ _).1 (hdis hl)⟩, fun i => (hC i).1⟩
  · rintro ⟨⟨-, hdis⟩, hC⟩
    exact ⟨fun i => ⟨hC i, isCompact_tsupport_pt hc _⟩, fun l l' hl =>
      (disjoint_tsupport_iff_supp_inter _ _).2 (hdis l l' hl)⟩
theorem mem_compactC1_iff
    (hc : CutoffMirrors.TorusMetricSpace.MetricTorusFacts) (β : ℝ)
    (hβ : 0 < β) (g : AmbientPoints.Pt s .torus → ℝ) :
    g ∈ Ambient.compactC1 (axisMirrorData s β hβ) ℝ .torus ↔
      TorusCutoffs.IsC1 (s := s) g := by
  constructor
  · exact fun h => h.1
  · refine fun h => ⟨h, ?_⟩
    rw [closedSupport_axisMirror_eq_tsupport]
    exact (AmbientPoints.isCompact_iff_isCompactWrt _).1 (isCompact_tsupport_pt hc g)
theorem componentList_mem_separatedN_iff
    (hc : CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (h1 : TorusC1.C1Properties) (β : ℝ) (hβ : 0 < β) {q : ℕ} (f : FnFamily s q) :
    componentList s f ∈ Ambient.separatedN (axisMirrorData s β hβ) .torus q ↔
      TorusTuples.IsDisjointFamily (s := s) f ∧ ∀ i, TorusCutoffs.IsC1 (s := s) (f i) := by
  have hdis : ∀ i j, Disjoint (Ambient.closedSupport (axisMirrorData s β hβ) .torus (f i))
      (Ambient.closedSupport (axisMirrorData s β hβ) .torus (f j)) ↔
        TorusTuples.supp (s := s) (f i) ∩ TorusTuples.supp (s := s) (f j) = ∅ := fun i j =>
    disjoint_iff_inter_eq_empty_of_eq
      ((closedSupport_axisMirror_eq_tsupport β hβ _).trans (tsupport_eq_supp _))
      ((closedSupport_axisMirror_eq_tsupport β hβ _).trans (tsupport_eq_supp _))
  constructor
  · rintro ⟨-, hmem, hpair⟩
    have hC : ∀ i, TorusCutoffs.IsC1 (s := s) (f i) := fun i =>
      (mem_compactC1_iff hc β hβ _).1 (hmem _ ((List.mem_ofFn' _ _).2 ⟨i, rfl⟩))
    refine ⟨⟨fun l => isLipschitzReal_of_isC1 h1 (hC l), fun l l' hl => ?_⟩, hC⟩
    have hp := List.pairwise_ofFn.1 hpair
    rcases lt_or_gt_of_ne hl with hlt | hlt
    · exact (hdis _ _).1 (hp hlt)
    · rw [Set.inter_comm]
      exact (hdis _ _).1 (hp hlt)
  · rintro ⟨⟨-, hsep⟩, hC⟩
    refine ⟨List.length_ofFn, fun g hg => ?_, List.pairwise_ofFn.2 fun i j hij => ?_⟩
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
      exact (mem_compactC1_iff hc β hβ _).2 (hC i)
    · exact (hdis _ _).2 (hsep i j hij.ne)
theorem exists_componentList_eq {q : ℕ} {X : TorusTuples.FnTuple s ℝ} (h : X.length = q) :
    ∃ f : FnFamily s q, componentList s f = X :=
  ⟨TorusTuples.componentFamily X h, TorusTuples.ofFn_componentFamily X h⟩
theorem disjointC1Tuples_eq_image
    {q : ℕ} {A : Set (FnFamily s q)}
    (hA : ∀ f : FnFamily s q, f ∈ A ↔
      TorusTuples.IsDisjointFamily (s := s) f ∧ ∀ i, TorusCutoffs.IsC1 (s := s) (f i)) :
    TorusTuples.disjointC1Tuples s q = componentList s '' A := by
  ext X
  constructor
  · intro hX
    obtain ⟨f, rfl⟩ := exists_componentList_eq hX.1.2
    exact ⟨f, (hA f).2 ((componentList_mem_disjointC1Tuples_iff f).1 hX), rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact (componentList_mem_disjointC1Tuples_iff f).2 ((hA f).1 hf)
theorem sepTuples_eq_separatedTuples
    (hs : AmbientPoints.Identification.AllCoincide) {q : ℕ} (hq : 1 ≤ q) :
    AmbientPoints.sepTuples s .torus q = AmbientPoints.separatedTuples s .torus q :=
  (hs s .torus).sepTuples_eq q hq
theorem multilinear_update_combination {n : ℕ} {Φ : TorusTuples.disjointTuples s n → ℝ}
    (hΦ : TorusTuples.IsMultilinear Φ) {F F' : Fin n → s.Torus → ℝ} (l : Fin n) (b b' : ℝ)
    (hF : TorusTuples.IsDisjointFamily (s := s) F)
    (hF' : TorusTuples.IsDisjointFamily (s := s) F')
    (hag : ∀ i, i ≠ l → F i = F' i)
    (m : componentList s (Function.update F l (b • F l + b' • F' l)) ∈ TorusTuples.disjointTuples s n)
    (m' : componentList s F ∈ TorusTuples.disjointTuples s n)
    (m'' : componentList s F' ∈ TorusTuples.disjointTuples s n) :
    Φ ⟨_, m⟩ = b * Φ ⟨_, m'⟩ + b' * Φ ⟨_, m''⟩ := by
  have e₁ : Function.update F l (F l) = F := Function.update_eq_self l F
  have e₂ : Function.update F l (F' l) = F' := by
    funext i
    by_cases hi : i = l
    · subst hi
      simp
    · simp [Function.update_of_ne hi, hag i hi]
  have h₁ : TorusTuples.IsDisjointFamily (s := s) (Function.update F l (F l)) := by
    rw [e₁]
    exact hF
  have h₂ : TorusTuples.IsDisjointFamily (s := s) (Function.update F l (F' l)) := by
    rw [e₂]
    exact hF'
  have lip : ∀ j, TorusTuples.IsLipschitzReal (s := s) (F j) := hF.1
  have lip' : ∀ j, TorusTuples.IsLipschitzReal (s := s) (F' j) := hF'.1
  have k := (hΦ l F (b • F l) (b' • F' l) lip ((lip l).smul b) ((lip' l).smul b')
    (h₁.update_smul b) (h₂.update_smul b')).1
  have k₁ := (hΦ l F (F l) (F l) lip (lip l) (lip l) h₁ h₁).2 b
  have k₂ := (hΦ l F (F' l) (F' l) lip (lip' l) (lip' l) h₂ h₂).2 b'
  have t₁ : Φ (TorusTuples.disjointTupleOf _ h₁) = Φ ⟨_, m'⟩ :=
    congrArg Φ (Subtype.ext (congrArg List.ofFn e₁))
  have t₂ : Φ (TorusTuples.disjointTupleOf _ h₂) = Φ ⟨_, m''⟩ :=
    congrArg Φ (Subtype.ext (congrArg List.ofFn e₂))
  rw [← t₁, ← t₂]
  exact k.trans (congrArg₂ (· + ·) k₁ k₂)
theorem restrictionIsMultilinearForm_holds (h1 : TorusC1.C1Properties)
    (hc : CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (hs : AmbientPoints.Identification.AllCoincide) :
    RestrictionIsMultilinearForm s := by
  intro n hn Φ hΦ Ψ hΨ
  have E := sepTuples_eq_separatedTuples (s := s) hs (q := n) (by omega)
  have fam : ∀ f : AmbientPoints.sepTuples s .torus n,
      TorusTuples.IsDisjointFamily (s := s) f.1 := fun f =>
    ((mem_ambient_separatedTuples_iff hc h1 f.1).1 (E ▸ f.2)).1
  have mem : ∀ f : AmbientPoints.sepTuples s .torus n,
      componentList s f.1 ∈ TorusTuples.disjointTuples s n := fun f =>
    ⟨(TorusTuples.isDisjointTuple_ofFn _).2 (fam f), List.length_ofFn⟩
  refine ⟨fun f => ?_, ?_⟩
  · rw [hΨ f (mem f)]
    simp
  · intro l b b' f f' hag h
    rw [hΨ ⟨_, h⟩ (mem _), hΨ f (mem f), hΨ f' (mem f')]
    have main := multilinear_update_combination hΦ l b b' (fam f) (fam f') hag (mem ⟨_, h⟩)
      (mem f) (mem f')
    exact (congrArg (fun z : ℝ => (z : ℂ)) main).trans (by push_cast; rfl)
theorem mem_compactC1SuppIn_iff
    (hc : CutoffMirrors.TorusMetricSpace.MetricTorusFacts) (β : ℝ)
    (hβ : 0 < β) (A : Set (AmbientPoints.Pt s .torus))
    (g : AmbientPoints.Pt s .torus → ℝ) :
    g ∈ Ambient.compactC1SuppIn (axisMirrorData s β hβ) .torus A ↔
      g ∈ AmbientPoints.c1CompactlySupportedIn A := by
  constructor
  · rintro ⟨hC, hA⟩
    refine ⟨(mem_compactC1_iff hc β hβ g).1 hC, isCompact_tsupport_pt hc g, ?_⟩
    rw [← closedSupport_axisMirror_eq_tsupport β hβ]
    exact hA
  · rintro ⟨hC, -, hA⟩
    refine ⟨(mem_compactC1_iff hc β hβ g).2 hC, ?_⟩
    rw [closedSupport_axisMirror_eq_tsupport]
    exact hA
theorem formIsMultilinearFunctional_holds (h1 : TorusC1.C1Properties)
    (hc : CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (hs : AmbientPoints.Identification.AllCoincide) :
    FormIsMultilinearFunctional s := by
  intro q hq Ψ _ hmult
  have E := sepTuples_eq_separatedTuples (s := s) hs hq
  have toT : ∀ {F : FnFamily s q}, F ∈ AmbientPoints.separatedTuples s .torus q →
      F ∈ AmbientPoints.sepTuples s .torus q := fun h => by
    rw [E]
    exact h
  refine ⟨fun Ψ' hlink A hA => ?_, fun β hβ Ψ' hlink A hA f hf i g hg a t => ?_⟩
  · have comb : ∀ (F F' : FnFamily s q) (hF : F ∈ AmbientPoints.separatedTuples s .torus q)
        (hF' : F' ∈ AmbientPoints.separatedTuples s .torus q) (l : Fin q) (b b' : ℝ),
        (∀ i, i ≠ l → F i = F' i) → ∀ C : FnFamily s q,
        C = Function.update F l (b • F l + b' • F' l) →
        ∀ hC : C ∈ AmbientPoints.separatedTuples s .torus q,
          Ψ' ⟨C, hC⟩ = b * Ψ' ⟨F, hF⟩ + b' * Ψ' ⟨F', hF'⟩ := by
      intro F F' hF hF' l b b' hag C hCe hC
      subst hCe
      have c := hmult l b b' ⟨F, toT hF⟩ ⟨F', toT hF'⟩ hag (toT hC)
      rw [hlink ⟨_, hC⟩ (toT hC), hlink ⟨F, hF⟩ (toT hF), hlink ⟨F', hF'⟩ (toT hF')] at c
      exact_mod_cast c
    have hmem : ∀ g : (i : Fin q) → AmbientPoints.c1Submodule (A i),
        (fun i => (g i : AmbientPoints.Pt s .torus → ℝ)) ∈
          AmbientPoints.separatedTuples s .torus q := fun g =>
      AmbientPoints.mem_separatedTuples_of_forall_mem_c1 hA fun i => (g i).2
    have lin : ∀ (g : (i : Fin q) → AmbientPoints.c1Submodule (A i)) (i : Fin q)
        (x y : AmbientPoints.c1Submodule (A i)) (b b' : ℝ),
        Ψ' ⟨_, hmem (Function.update g i (b • x + b' • y))⟩ =
          b * Ψ' ⟨_, hmem (Function.update g i x)⟩ + b' * Ψ' ⟨_, hmem (Function.update g i y)⟩ := by
      intro g i x y b b'
      refine comb _ _ (hmem _) (hmem _) i b b' (fun k hk => ?_) _ ?_ (hmem _)
      · simp [Function.update_of_ne hk]
      · funext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Function.update_of_ne hj]
    refine ⟨{ toFun := fun g => Ψ' ⟨_, hmem g⟩, map_update_add' := ?_, map_update_smul' := ?_ },
      fun g => rfl⟩
    · intro inst g i x y
      obtain rfl : inst = fun a b => instDecidableEqFin q a b := Subsingleton.elim _ _
      have key := lin g i x y 1 1
      rw [one_smul, one_smul, one_mul, one_mul] at key
      exact key
    · intro inst g i c x
      obtain rfl : inst = fun a b => instDecidableEqFin q a b := Subsingleton.elim _ _
      have key := lin g i x x c 0
      rw [zero_smul, add_zero, zero_mul, add_zero] at key
      exact key
  · have hsup : ∀ {j : Fin q} {u : AmbientPoints.Pt s .torus → ℝ},
        u ∈ Ambient.compactC1SuppIn (axisMirrorData s β hβ) .torus (A j) ↔
          u ∈ AmbientPoints.c1Submodule
            (show Set (AmbientPoints.Pt s .torus) from A j) := fun {j u} =>
      mem_compactC1SuppIn_iff hc β hβ (A j) u
    have hcomb : a • f i + t • g ∈ Ambient.compactC1SuppIn (axisMirrorData s β hβ) .torus (A i) :=
      hsup.2 (Submodule.add_mem _ (Submodule.smul_mem _ a (hsup.1 (hf i)))
        (Submodule.smul_mem _ t (hsup.1 hg)))
    have hup : ∀ {u}, u ∈ Ambient.compactC1SuppIn (axisMirrorData s β hβ) .torus (A i) → ∀ j,
        Function.update f i u j ∈ Ambient.compactC1SuppIn (axisMirrorData s β hβ) .torus (A j) := by
      intro u hu j
      by_cases hj : j = i
      · subst hj
        simpa using hu
      · simpa [Function.update_of_ne hj] using hf j
    have m₀ := Ambient.ofFn_mem_separatedN _ _ hA hf
    have m₁ := Ambient.ofFn_mem_separatedN _ _ hA (hup hg)
    have m₂ := Ambient.ofFn_mem_separatedN _ _ hA (hup hcomb)
    have toSep : ∀ F : FnFamily s q,
        componentList s F ∈ Ambient.separatedN (axisMirrorData s β hβ) .torus q →
          F ∈ AmbientPoints.sepTuples s .torus q := fun F h =>
      toT ((mem_ambient_separatedTuples_iff hc h1 F).2
        ((componentList_mem_separatedN_iff hc h1 β hβ F).1 h))
    have h₂ : Function.update f i (a • f i + t • Function.update f i g i) ∈
        AmbientPoints.sepTuples s .torus q := by
      rw [Function.update_self]
      exact toSep _ m₂
    have hag : ∀ k, k ≠ i → f k = Function.update f i g k := fun k hk =>
      (Function.update_of_ne hk _ _).symm
    have c : Ψ ⟨_, h₂⟩ = (a : ℂ) * Ψ ⟨f, toSep f m₀⟩ +
        (t : ℂ) * Ψ ⟨Function.update f i g, toSep _ m₁⟩ :=
      hmult i a t ⟨f, toSep f m₀⟩ ⟨Function.update f i g, toSep _ m₁⟩ hag h₂
    have e : Ψ ⟨_, h₂⟩ = Ψ ⟨_, toSep _ m₂⟩ :=
      congrArg Ψ (Subtype.ext (congrArg (fun u => Function.update f i (a • f i + t • u))
        (Function.update_self i g f)))
    rw [e, hlink ⟨_, toSep _ m₂⟩ m₂, hlink ⟨f, toSep f m₀⟩ m₀,
      hlink ⟨Function.update f i g, toSep _ m₁⟩ m₁] at c
    rw [show Ambient.evalOrZero Ψ' _ = _ from dif_pos m₂,
      show Ambient.evalOrZero Ψ' _ = _ from dif_pos m₀,
      show Ambient.evalOrZero Ψ' _ = _ from dif_pos m₁]
    exact_mod_cast c
theorem torusLipschitzTupleFacts_holds (ht : TorusTuples.SeparationAndSymmetry.Statement)
    (h1 : TorusC1.C1Properties)
    (hc : CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (hs : AmbientPoints.Identification.AllCoincide) : TorusLipschitzTupleFacts := by
  intro s
  refine ⟨fun n hn f hf => supportGap_pos hc ht hn hf, fun n hn => ?_,
    fun n _ f _ d hd => ?_, fun n _ => ?_, fun n _ => disjointTuples_eq_image_lipTuples hc n,
    fun n _ f _ => supportGap_eq_gap f, fun q hq => ⟨?_, ?_, fun β hβ => ?_⟩,
    restrictionIsMultilinearForm_holds h1 hc hs, formIsMultilinearFunctional_holds h1 hc hs⟩
  · ext f
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hf
      by_cases htop : AmbientPoints.supportGap f = ∞
      · exact ⟨1, one_pos, hf, by rw [htop]; exact le_top⟩
      · exact ⟨_, ENNReal.toReal_pos (supportGap_pos hc ht hn hf).ne' htop, hf,
          (ENNReal.ofReal_toReal htop).le⟩
    · rintro ⟨d, -, hf, -⟩
      exact hf
  · exact (AmbientPoints.supportsApartBy_torus_iff f d).symm.trans
      ⟨And.right, fun h => ⟨hd, h⟩⟩
  · rw [← disjointTuples_eq_image_lipTuples hc n]
    exact fun X h => h.1
  · refine disjointC1Tuples_eq_image fun f => ?_
    rw [sepTuples_eq_separatedTuples hs hq]
    exact mem_ambient_separatedTuples_iff hc h1 f
  · exact disjointC1Tuples_eq_image (mem_ambient_separatedTuples_iff hc h1)
  · ext X
    constructor
    · intro hX
      obtain ⟨f, rfl⟩ := exists_componentList_eq hX.1.2
      exact (componentList_mem_separatedN_iff hc h1 β hβ f).2
        ((componentList_mem_disjointC1Tuples_iff f).1 hX)
    · intro hX
      obtain ⟨f, rfl⟩ := exists_componentList_eq hX.1
      exact (componentList_mem_disjointC1Tuples_iff f).2
        ((componentList_mem_separatedN_iff hc h1 β hβ f).1 hX)
end YangMills.Construction.TorusLipschitzTuples
end
