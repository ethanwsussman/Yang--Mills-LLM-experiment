import YangMills.Construction.Geometry.Periodization
import YangMills.Construction.LimitTheorem.RepresentativeAndTheIdentificationsProof
import YangMills.Construction.PassageToTheLimit.WhatPassesToTheLimitProof
import YangMills.Construction.TorusOrFourSpace.BallsTuplesInABallAndAdmissibleTuplesOfFourSpace
import YangMills.Construction.TorusOrFourSpace.CentredMomentsOfBoundedForms
import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNorm
import YangMills.Construction.TorusOrFourSpace.ClassesOfTuplesAndTheSeparation
import YangMills.Construction.TorusOrFourSpace.FunctionsOfClassC1WithCompactSupportOnFourSpace
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.CentredMoments
open YangMills.Construction.Multilinear YangMills.Construction.PeriodicSpace.GrowingDomains
theorem partitionBound_nonneg {q : ℕ} {c : ℕ → ℝ} (hc : ∀ k, 2 ≤ k → k ≤ q → 0 ≤ c k) :
    0 ≤ partitionBound q c := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.LimitPassage.partitionBound_nonneg <;> assumption
theorem nonSingletonPartitions_one : SetPartition.nonSingletonPartitions 1 = ∅ := by apply _root_.YangMills.SharedProofs.p2697 <;> assumption
theorem abstractBounds_holds (hF : BoundedMultilinearEstimates) : AbstractBounds := by
  intro q hq V _ _ p c hc Ψ hΨ
  obtain ⟨hA, hB⟩ := hF q hq V p
  obtain ⟨⟨G, hG⟩, hbound⟩ := hB Ψ
  have hb := hbound c hc hΨ
  have hb0 := partitionBound_nonneg hc
  have hGe : ⇑G = partitionSum Ψ := funext hG
  refine ⟨(isMultilinearFun_iff_exists_multilinearMap _).mpr ⟨G, hGe⟩, hb, ?_, ?_⟩
  · intro f f'
    have h := hA G _ hb0 (fun h => by rw [hG]; exact hb h) f f'
    rw [hG, hG] at h
    exact h.1.trans h.2
  · rintro rfl
    refine ⟨fun h => Finset.sum_eq_zero fun π _ => absurd π.2 (by simp [nonSingletonPartitions_one]), ?_⟩
    rw [partitionBound, nonSingletonPartitions_one, Finset.sum_empty]
section EvaluationMaps
variable {D : Params} {E : Kind}
def coeTuple {n : ℕ} {W : Fin n → Submodule ℝ (E.Pt D → ℝ)} (u : ∀ l, W l) :
    FnTuple D E n :=
  fun l => (u l : E.Pt D → ℝ)
theorem coeTuple_mem_productSet {n : ℕ} {W : Fin n → Submodule ℝ (E.Pt D → ℝ)} (u : ∀ l, W l) :
    coeTuple u ∈ productSet D E (fun l => (W l : Set (E.Pt D → ℝ))) :=
  fun l _ => (u l).2
theorem coeTuple_update {n : ℕ} {W : Fin n → Submodule ℝ (E.Pt D → ℝ)} (u : ∀ l, W l)
    (i : Fin n) (w : W i) :
    coeTuple (Function.update u i w) =
      Function.update (coeTuple u) i (w : E.Pt D → ℝ) := by
  funext l
  by_cases h : l = i
  · subst h
    simp [coeTuple]
  · simp [coeTuple, Function.update_of_ne h]
def restrictToSubmodules {n : ℕ} {W : Fin n → Submodule ℝ (E.Pt D → ℝ)} {K : Set (FnTuple D E n)}
    (hsub : productSet D E (fun l => (W l : Set (E.Pt D → ℝ))) ⊆ K) (Ψ : K → ℝ)
    (u : ∀ l, W l) : ℝ :=
  Ψ ⟨coeTuple u, hsub (coeTuple_mem_productSet u)⟩
theorem isMultilinearFun_restrictToSubmodules {n : ℕ} {W : Fin n → Submodule ℝ (E.Pt D → ℝ)}
    {K : Set (FnTuple D E n)}
    (hsub : productSet D E (fun l => (W l : Set (E.Pt D → ℝ))) ⊆ K) {Ψ : K → ℝ}
    (hΨ : IsMultilinearOn D E K Ψ) : IsMultilinearFun (restrictToSubmodules hsub Ψ) := by
  intro x i
  have hagree : ∀ a b : W i, ∀ l, l ≠ i →
      coeTuple (Function.update x i a) l = coeTuple (Function.update x i b) l := by
    intro a b l hl
    simp [coeTuple, Function.update_of_ne hl]
  refine ⟨fun a b => ?_, fun c a => ?_⟩
  · have e : coeTuple (Function.update x i (a + b)) =
        Function.update (coeTuple (Function.update x i a)) i
          (coeTuple (Function.update x i a) i +
            coeTuple (Function.update x i b) i) := by
      funext l
      by_cases h : l = i
      · subst h
        simp [coeTuple]
      · simp [coeTuple, Function.update_of_ne h]
    have hm := e ▸ hsub (coeTuple_mem_productSet (Function.update x i (a + b)))
    have h := (hΨ i ⟨_, hsub (coeTuple_mem_productSet (Function.update x i a))⟩
      ⟨_, hsub (coeTuple_mem_productSet (Function.update x i b))⟩ (hagree a b)).1 hm
    exact (congrArg Ψ (Subtype.ext e)).trans h
  · have e : coeTuple (Function.update x i (c • a)) =
        Function.update (coeTuple (Function.update x i a)) i
          (c • coeTuple (Function.update x i a) i) := by
      funext l
      by_cases h : l = i
      · subst h
        simp [coeTuple]
      · simp [coeTuple, Function.update_of_ne h]
    have hm := e ▸ hsub (coeTuple_mem_productSet (Function.update x i (c • a)))
    have h := (hΨ i ⟨_, hsub (coeTuple_mem_productSet (Function.update x i a))⟩
      ⟨_, hsub (coeTuple_mem_productSet (Function.update x i a))⟩ (fun _ _ => rfl)).2 c hm
    exact (congrArg Ψ (Subtype.ext e)).trans h
theorem isMultilinearOnProduct_of_restrict {n : ℕ} {W : Fin n → Submodule ℝ (E.Pt D → ℝ)}
    {K : Set (FnTuple D E n)}
    (hsub : productSet D E (fun l => (W l : Set (E.Pt D → ℝ))) ⊆ K) {Ψ : K → ℝ}
    (hM : IsMultilinearFun (restrictToSubmodules hsub Ψ)) :
    IsMultilinearOnProduct D E K (fun l => (W l : Set (E.Pt D → ℝ))) Ψ := by
  refine ⟨hsub, fun g hg i u hu v hv α β h₁ h₂ h₃ => ?_⟩
  let x : ∀ l, W l := fun l => ⟨g l, hg l (Set.mem_univ l)⟩
  let u' : W i := ⟨u, hu⟩
  let v' : W i := ⟨v, hv⟩
  have hval : ∀ (w : W i) (hw : Function.update g i (w : E.Pt D → ℝ) ∈ K),
      restrictToSubmodules hsub Ψ (Function.update x i w) = Ψ ⟨_, hw⟩ :=
    fun w hw => congrArg Ψ (Subtype.ext (coeTuple_update x i w))
  have L := hM x i
  have e₁ := L.map_add (α • u') (β • v')
  have e₂ := L.map_smul α u'
  have e₃ := L.map_smul β v'
  simp only [smul_eq_mul] at e₁ e₂ e₃
  rw [← hval u' h₁, ← hval v' h₂, ← e₂, ← e₃, ← e₁]
  exact (hval (α • u' + β • v') h₃).symm
def sharpSeminorm (hC : VectorClasses.Claim)
    (W : Submodule ℝ (E.Pt D → ℝ)) (hW : ∀ u ∈ W, u ∈ lipschitzSupportedIn D E Set.univ) :
    Seminorm ℝ W :=
  Seminorm.of (fun u => (sharpNormQ D E (u : E.Pt D → ℝ)).toReal)
    (fun u v => by
      have hn := (hC D E).2.1.2
      have hu := hW u u.2
      have hv := hW v v.2
      calc (sharpNormQ D E ((u + v : W) : E.Pt D → ℝ)).toReal
          ≤ (sharpNormQ D E (u : E.Pt D → ℝ) + sharpNormQ D E (v : E.Pt D → ℝ)).toReal :=
            ENNReal.toReal_mono
              (ENNReal.add_ne_top.mpr ⟨(hn.lt_top _ hu).ne, (hn.lt_top _ hv).ne⟩)
              (hn.add_le _ hu _ hv)
        _ = _ := ENNReal.toReal_add (hn.lt_top _ hu).ne (hn.lt_top _ hv).ne)
    (fun a u => by
      have hn := (hC D E).2.1.2
      show (sharpNormQ D E (a • (u : E.Pt D → ℝ))).toReal = _
      rw [hn.smul _ (hW u u.2), ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg a),
        Real.norm_eq_abs])
theorem ofReal_mul_prod_toReal {ι : Type*} (s : Finset ι) {b : ℝ} (hb : 0 ≤ b) (a : ι → ℝ≥0∞)
    (ha : ∀ l, a l ≠ ∞) :
    ENNReal.ofReal b * ∏ l ∈ s, a l = ENNReal.ofReal (b * ∏ l ∈ s, (a l).toReal) := by
  rw [ENNReal.ofReal_mul hb, ENNReal.ofReal_prod_of_nonneg fun _ _ => ENNReal.toReal_nonneg]
  congr 1
  exact Finset.prod_congr rfl fun l _ => (ENNReal.ofReal_toReal (ha l)).symm
theorem ofReal_mul_sum_toReal {q : ℕ} {b : ℝ} (hb : 0 ≤ b) (a x y : Fin q → ℝ≥0∞)
    (ha : ∀ l, a l ≠ ∞) (hx : ∀ l, x l ≠ ∞) (hy : ∀ l, y l ≠ ∞) :
    ENNReal.ofReal b * ∑ l, a l * ∏ l' ∈ Finset.univ.erase l, (x l' + y l') =
      ENNReal.ofReal (b * ∑ l, (a l).toReal *
        ∏ l' ∈ Finset.univ.erase l, ((x l').toReal + (y l').toReal)) := by
  have hp : ∀ l, 0 ≤ ∏ l' ∈ Finset.univ.erase l, ((x l').toReal + (y l').toReal) := fun l =>
    Finset.prod_nonneg fun _ _ => add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_mul hb,
    ENNReal.ofReal_sum_of_nonneg fun l _ => mul_nonneg ENNReal.toReal_nonneg (hp l)]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (ha l),
    ENNReal.ofReal_prod_of_nonneg fun _ _ =>
      add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (hx k), ENNReal.ofReal_toReal (hy k)]
theorem satisfiesFormBounds_of_real (hC : VectorClasses.Claim) {q : ℕ}
    {W : Fin q → Submodule ℝ (E.Pt D → ℝ)}
    (hW : ∀ l, ∀ u ∈ W l, u ∈ lipschitzSupportedIn D E Set.univ) {K : Set (FnTuple D E q)}
    (hsub : productSet D E (fun l => (W l : Set (E.Pt D → ℝ))) ⊆ K) {Ψ : K → ℝ} {b : ℝ}
    (hb : 0 ≤ b)
    (h₁ : ∀ u : ∀ l, W l, |restrictToSubmodules hsub Ψ u| ≤
      b * ∏ l, (sharpNormQ D E (u l : E.Pt D → ℝ)).toReal)
    (h₂ : ∀ f f' : ∀ l, W l, |restrictToSubmodules hsub Ψ f - restrictToSubmodules hsub Ψ f'| ≤
      b * ∑ l, (sharpNormQ D E ((f l - f' l : W l) : E.Pt D → ℝ)).toReal *
        ∏ l' ∈ Finset.univ.erase l, ((sharpNormQ D E (f l' : E.Pt D → ℝ)).toReal +
          (sharpNormQ D E (f' l' : E.Pt D → ℝ)).toReal)) :
    SatisfiesFormBounds D E K (fun l => (W l : Set (E.Pt D → ℝ))) Ψ b := by
  have hfin : ∀ (l : Fin q) (u : W l), sharpNormQ D E (u : E.Pt D → ℝ) ≠ ∞ := fun l u =>
    ((hC D E).2.1.2.lt_top _ (hW l u u.2)).ne
  constructor
  · intro h hh
    let u : ∀ l, W l := fun l => ⟨h.1 l, hh l (Set.mem_univ l)⟩
    have e : Ψ h = restrictToSubmodules hsub Ψ u := congrArg Ψ (Subtype.ext rfl)
    have e' := ofReal_mul_prod_toReal Finset.univ hb (fun l => sharpNormQ D E (u l : E.Pt D → ℝ))
      (fun l => hfin l (u l))
    rw [e]
    exact (ENNReal.ofReal_le_ofReal (h₁ u)).trans_eq e'.symm
  · intro f f' hf hf'
    let u : ∀ l, W l := fun l => ⟨f.1 l, hf l (Set.mem_univ l)⟩
    let v : ∀ l, W l := fun l => ⟨f'.1 l, hf' l (Set.mem_univ l)⟩
    have e : Ψ f = restrictToSubmodules hsub Ψ u := congrArg Ψ (Subtype.ext rfl)
    have e₂ : Ψ f' = restrictToSubmodules hsub Ψ v := congrArg Ψ (Subtype.ext rfl)
    have e' := ofReal_mul_sum_toReal hb
      (fun l => sharpNormQ D E ((u l - v l : W l) : E.Pt D → ℝ))
      (fun l => sharpNormQ D E (u l : E.Pt D → ℝ))
      (fun l => sharpNormQ D E (v l : E.Pt D → ℝ))
      (fun l => hfin l _) (fun l => hfin l _) (fun l => hfin l _)
    rw [e, e₂]
    exact (ENNReal.ofReal_le_ofReal (h₂ u v)).trans_eq e'.symm
theorem satisfiesFormBounds_of_multilinear (hF : BoundedMultilinearEstimates)
    (hC : VectorClasses.Claim) {q : ℕ} (hq : 1 ≤ q)
    {W : Fin q → Submodule ℝ (E.Pt D → ℝ)}
    (hW : ∀ l, ∀ u ∈ W l, u ∈ lipschitzSupportedIn D E Set.univ) {K : Set (FnTuple D E q)}
    (hsub : productSet D E (fun l => (W l : Set (E.Pt D → ℝ))) ⊆ K) {Ψ : K → ℝ}
    (hΨ : IsMultilinearOn D E K Ψ) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ h : K, h.1 ∈ productSet D E (fun l => (W l : Set (E.Pt D → ℝ))) →
      ENNReal.ofReal |Ψ h| ≤ ENNReal.ofReal b * ∏ l, sharpNormQ D E (h.1 l)) :
    SatisfiesFormBounds D E K (fun l => (W l : Set (E.Pt D → ℝ))) Ψ b := by
  have hfin : ∀ (l : Fin q) (u : W l), sharpNormQ D E (u : E.Pt D → ℝ) ≠ ∞ := fun l u =>
    ((hC D E).2.1.2.lt_top _ (hW l u u.2)).ne
  have h₁ : ∀ u : ∀ l, W l, |restrictToSubmodules hsub Ψ u| ≤
      b * ∏ l, (sharpNormQ D E (u l : E.Pt D → ℝ)).toReal := by
    intro u
    have h := hb ⟨coeTuple u, hsub (coeTuple_mem_productSet u)⟩ (coeTuple_mem_productSet u)
    have e := ofReal_mul_prod_toReal Finset.univ hb0 (fun l => sharpNormQ D E (u l : E.Pt D → ℝ))
      (fun l => hfin l (u l))
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hb0 (Finset.prod_nonneg fun _ _ =>
      ENNReal.toReal_nonneg))).mp (h.trans_eq e)
  obtain ⟨G, hG⟩ := (isMultilinearFun_iff_exists_multilinearMap _).mp
    (isMultilinearFun_restrictToSubmodules hsub hΨ)
  let p : ∀ l, Seminorm ℝ (W l) := fun l => sharpSeminorm hC (W l) (hW l)
  refine satisfiesFormBounds_of_real hC hW hsub hb0 h₁ fun f f' => ?_
  have h := (hF q hq (fun l => W l) p).1 G b hb0 (fun u => by rw [hG]; exact h₁ u) f f'
  rw [hG] at h
  exact h.1.trans h.2
theorem momentSum_eq_partitionSum {q : ℕ} (F : FunctionalSystem D E)
    {W : Fin q → Submodule ℝ (E.Pt D → ℝ)}
    (hdom : ∀ (I : Finset (Fin q)) (hI : 2 ≤ I.card), productSet D E
      (fun i : Fin I.card => (W (I.orderEmbOfFin rfl i) : Set (E.Pt D → ℝ))) ⊆
        F.domain I.card hI)
    (Φf : BlockForms fun l => W l)
    (hΦf : ∀ I hI, ⇑(Φf I hI) = restrictToSubmodules (W := fun i => W (I.orderEmbOfFin rfl i))
      (hdom I hI) (F.eval I.card hI))
    (u : ∀ l, W l) (hf : F.Defined (coeTuple u)) :
    F.momentSum (coeTuple u) hf = partitionSum Φf u := by
  have hset : SetPartition.singletonFree q = SetPartition.nonSingletonPartitions q :=
    ((SetPartition.nonSingletonPartitions_eq_atLeastTwoPartitions q).trans
      (SetPartition.atLeastTwoPartitions_univ q)).symm
  unfold FunctionalSystem.momentSum partitionSum
  refine Finset.sum_bij (fun π _ => ⟨π.1, hset ▸ π.2⟩) (fun _ _ => Finset.mem_attach _ _)
    (fun a _ b _ h => Subtype.ext (Subtype.mk.inj h))
    (fun b _ => ⟨⟨b.1, hset.symm ▸ b.2⟩, Finset.mem_attach _ _, rfl⟩) (fun π _ => ?_)
  refine Finset.prod_congr rfl fun I _ => ?_
  exact (congrFun (hΦf I.1 _) _).symm
theorem prod_orderEmbOfFin_eq {q : ℕ} (I : Finset (Fin q)) (X : Fin q → ℝ) :
    ∏ i : Fin I.card, X (I.orderEmbOfFin rfl i) = ∏ l ∈ I, X l := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.LimitPassage.prod_comp_orderEmbOfFin <;> assumption
theorem momentSum_form (hF : BoundedMultilinearEstimates)
    (hC : VectorClasses.Claim) (F : FunctionalSystem D E) {q : ℕ}
    (hq : 1 ≤ q) {W : Fin q → Submodule ℝ (E.Pt D → ℝ)}
    (hW : ∀ l, ∀ u ∈ W l, u ∈ lipschitzSupportedIn D E Set.univ)
    (hdom : ∀ (I : Finset (Fin q)) (hI : 2 ≤ I.card), productSet D E
      (fun i : Fin I.card => (W (I.orderEmbOfFin rfl i) : Set (E.Pt D → ℝ))) ⊆
        F.domain I.card hI)
    (hlin : ∀ (I : Finset (Fin q)) (hI : 2 ≤ I.card),
      IsMultilinearOn D E (F.domain I.card hI) (F.eval I.card hI))
    (c : ℕ → ℝ) (hc : ∀ k, 2 ≤ k → k ≤ q → 0 ≤ c k)
    (hb : ∀ (I : Finset (Fin q)) (hI : 2 ≤ I.card) (g : F.domain I.card hI),
      g.1 ∈ productSet D E
        (fun i : Fin I.card => (W (I.orderEmbOfFin rfl i) : Set (E.Pt D → ℝ))) →
      ENNReal.ofReal |F.eval I.card hI g| ≤
        ENNReal.ofReal (c I.card) * ∏ i, sharpNormQ D E (g.1 i))
    {K : Set (FnTuple D E q)}
    (hsub : productSet D E (fun l => (W l : Set (E.Pt D → ℝ))) ⊆ K)
    (hK : ∀ f ∈ K, F.Defined f) (Ψ : K → ℝ)
    (hΨ : ∀ f : K, Ψ f = F.momentSum f.1 (hK f.1 f.2)) :
    IsMultilinearOnProduct D E K (fun l => (W l : Set (E.Pt D → ℝ))) Ψ ∧
      SatisfiesFormBounds D E K (fun l => (W l : Set (E.Pt D → ℝ))) Ψ
        (partitionBound q c) := by
  have hfin : ∀ (l : Fin q) (u : W l), sharpNormQ D E (u : E.Pt D → ℝ) ≠ ∞ := fun l u =>
    ((hC D E).2.1.2.lt_top _ (hW l u u.2)).ne
  have hex : ∀ (I : Finset (Fin q)) (hI : 2 ≤ I.card),
      ∃ G : MultilinearMap ℝ (fun i : Fin I.card => ↥(W (I.orderEmbOfFin rfl i))) ℝ,
        ⇑G = restrictToSubmodules (W := fun i => W (I.orderEmbOfFin rfl i)) (hdom I hI)
          (F.eval I.card hI) :=
    fun I hI => (isMultilinearFun_iff_exists_multilinearMap _).mp
      (isMultilinearFun_restrictToSubmodules _ (hlin I hI))
  choose Φf hΦf using hex
  let p : ∀ l, Seminorm ℝ (W l) := fun l => sharpSeminorm hC (W l) (hW l)
  have hblock : ∀ (I : Finset (Fin q)) (hI : 2 ≤ I.card) (h : ∀ l, W l),
      |Φf I hI (restrictOrdered h I)| ≤ c I.card * ∏ l ∈ I, p l (h l) := by
    intro I hI h
    have hcI : 0 ≤ c I.card := hc _ hI (by simpa using Finset.card_le_univ I)
    have hm := coeTuple_mem_productSet (W := fun i => W (I.orderEmbOfFin rfl i))
      (restrictOrdered h I)
    have hbd := hb I hI ⟨_, hdom I hI hm⟩ hm
    have e := ofReal_mul_prod_toReal Finset.univ hcI
      (fun i : Fin I.card => sharpNormQ D E (h (I.orderEmbOfFin rfl i) : E.Pt D → ℝ))
      (fun i => hfin _ _)
    have hr := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hcI (Finset.prod_nonneg fun _ _ =>
      ENNReal.toReal_nonneg))).mp (hbd.trans_eq e)
    rw [congrFun (hΦf I hI) (restrictOrdered h I)]
    refine hr.trans_eq ?_
    rw [← prod_orderEmbOfFin_eq I (fun l => p l (h l))]
    rfl
  obtain ⟨hM, hB, hD, -⟩ := abstractBounds_holds hF q hq (fun l => W l) p c hc Φf hblock
  have hread : restrictToSubmodules hsub Ψ = partitionSum Φf := by
    funext u
    have hm := hsub (coeTuple_mem_productSet u)
    exact (hΨ ⟨_, hm⟩).trans (momentSum_eq_partitionSum F hdom Φf hΦf u (hK _ hm))
  refine ⟨isMultilinearOnProduct_of_restrict hsub (hread ▸ hM),
    satisfiesFormBounds_of_real hC hW hsub (partitionBound_nonneg hc) ?_ ?_⟩
  · intro u
    rw [hread]
    exact hB u
  · intro f f'
    rw [hread]
    exact hD f f'
end EvaluationMaps
section OnEuclidean
variable {D : Params}
theorem lipschitzSupportedIn_subset_univ {E : Kind} {A : Set (E.Pt D)} :
    lipschitzSupportedIn D E A ⊆ lipschitzSupportedIn D E Set.univ :=
  fun _ h => ⟨h.1, h.2.1, Set.subset_univ _⟩
theorem c1SupportedIn_subset_lipschitz
    (hN : CompactlySupportedC1Bounds) (hD : IsLatticePowerScale D)
    {A : Set (euclidean.Pt D)} : c1SupportedIn D euclidean A ⊆ lipschitzSupportedIn D euclidean A :=
  fun h hh => ⟨(hN D hD h hh.1 hh.2.1).2.2.1, hh.2.1, hh.2.2⟩
theorem setInfDist_anti {E : Kind} {S S' T T' : Set (E.Pt D)} (hS : S ⊆ S') (hT : T ⊆ T') :
    setInfDist D E S' T' ≤ setInfDist D E S T :=
  le_trans (biInf_mono hS) (iInf₂_mono fun _ _ => biInf_mono hT)
theorem mem_lipTuplesSpacedInBalls {E : Kind} {q k : ℕ} {d R : ℝ} {A : Fin q → Set (E.Pt D)}
    (hA : SetsInBallsSeparated D E d R A) {e : Fin k → Fin q} (he : Function.Injective e)
    {g : FnTuple D E k} (hg : ∀ i, g i ∈ lipschitzSupportedIn D E (A (e i))) :
    g ∈ lipTuplesSpacedInBalls D E k d R := by
  refine ⟨fun i => (hg i).1, fun i => ?_, fun i k hik =>
    (hA.2 _ _ (he.ne hik)).trans (setInfDist_anti (hg i).2.2 (hg k).2.2)⟩
  obtain ⟨S, hS, hAS⟩ := hA.1 (e i)
  exact ⟨S, hS, (hg i).2.2.trans hAS⟩
theorem inBallPairwiseApart_of_separated {E : Kind} {q k : ℕ} {d R : ℝ}
    {A : Fin q → Set (E.Pt D)}
    (hd : 0 < d) (hA : SetsInBallsSeparated D E d R A) {ρ : ℝ≥0∞}
    (hρ : ∀ l, A l ⊆ centredBall D E ρ) {e : Fin k → Fin q} (he : Function.Injective e) :
    InBallPairwiseApart D E ρ (fun i => A (e i)) :=
  ⟨fun _ => hρ _, fun _ _ hik =>
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hd) (hA.2 _ _ (he.ne hik))⟩
theorem subset_centredBall_top {E : Kind} (A : Set (E.Pt D)) : A ⊆ centredBall D E ∞ := by
  rw [centredBall, if_pos rfl]
  exact Set.subset_univ _
theorem momentBound_eq_partitionBound (C : BoundFamily) (q : ℕ) (d R : ℝ) :
    C.momentBound q d R = partitionBound q (fun k => C.val k d R) := by
  have hset : SetPartition.singletonFree q = SetPartition.nonSingletonPartitions q :=
    ((SetPartition.nonSingletonPartitions_eq_atLeastTwoPartitions q).trans
      (SetPartition.atLeastTwoPartitions_univ q)).symm
  rw [BoundFamily.momentBound, hset]
  rfl
theorem hierarchyBounds_holds (hF : BoundedMultilinearEstimates)
    (hP : MultilinearProducts.Statement)
    (hN : CompactlySupportedC1Bounds)
    (hC : VectorClasses.Claim) (hD : IsLatticePowerScale D) :
    HierarchyBounds D := by
  intro C Φ hΦ q hq d R hd hR A hA
  have hΦ' : Φ.IsBoundedBy C := hΦ
  choose Wc hWc using fun B : Set (euclidean.Pt D) => ((hC D euclidean).1 B).2.1
  let W : Fin q → Submodule ℝ (euclidean.Pt D → ℝ) := fun l => Wc (A l)
  have hset : (fun l => c1SupportedIn D euclidean (A l)) =
      fun l => (W l : Set (euclidean.Pt D → ℝ)) := funext fun l => (hWc _).symm
  have hmem : ∀ (B : Set (euclidean.Pt D)) (u : euclidean.Pt D → ℝ), u ∈ Wc B →
      u ∈ c1SupportedIn D euclidean B := by
    intro B u hu
    have h : u ∈ (Wc B : Set (euclidean.Pt D → ℝ)) := hu
    rwa [hWc] at h
  have hW : ∀ l, ∀ u ∈ W l, u ∈ lipschitzSupportedIn D euclidean Set.univ := fun l u hu =>
    lipschitzSupportedIn_subset_univ (c1SupportedIn_subset_lipschitz hN hD (hmem _ u hu))
  have hprod : ∀ {k : ℕ}, 1 ≤ k → ∀ e : Fin k → Fin q, Function.Injective e →
      productSet D euclidean (fun i => (W (e i) : Set (euclidean.Pt D → ℝ))) ⊆
        sepC1Tuples D euclidean k := by
    intro k hk e he g hg
    have hA' := inBallPairwiseApart_of_separated hd hA
      (fun l => subset_centredBall_top (A l)) he
    exact (((hP D euclidean k hk).1 ∞ (by simp)).1.1 _ hA'
      (fun i _ => hmem _ _ (hg i (Set.mem_univ i)))).1
  have hbd : ∀ {k : ℕ} (hk : 2 ≤ k) (e : Fin k → Fin q), Function.Injective e →
      ∀ g : sepC1Tuples D euclidean k,
      g.1 ∈ productSet D euclidean (fun i => (W (e i) : Set (euclidean.Pt D → ℝ))) →
      ENNReal.ofReal |Φ.func k hk g| ≤
        ENNReal.ofReal (C.val k d R) * ∏ i, sharpNormQ D euclidean (g.1 i) :=
    fun hk e he g hg => hΦ' _ hk d R hd hR g (mem_lipTuplesSpacedInBalls hA he fun i =>
      c1SupportedIn_subset_lipschitz hN hD (hmem _ _ (hg i (Set.mem_univ i))))
  have hsub : productSet D euclidean (fun l => (W l : Set (euclidean.Pt D → ℝ))) ⊆
      sepC1Tuples D euclidean q := hprod hq id Function.injective_id
  obtain ⟨h₁, h₂⟩ := momentSum_form hF hC Φ.toFunctionalSystem hq hW
    (fun I hI => hprod (by omega) _ (I.orderEmbOfFin rfl).injective)
    (fun I hI => Φ.multilinear _ hI) (fun k => C.val k d R)
    (fun k hk _ => C.nonneg k hk d R hd hR)
    (fun I hI g hg => hbd hI _ (I.orderEmbOfFin rfl).injective g hg) hsub
    (fun f hf => Φ.defined_of_mem_sepC1Tuples hf) Φ.momentFun (fun f => rfl)
  rw [hset, momentBound_eq_partitionBound]
  exact ⟨h₁, h₂, fun hq₂ => satisfiesFormBounds_of_multilinear hF hC hq hW hsub
    (Φ.multilinear q hq₂) (C.nonneg q hq₂ d R hd hR) fun h hh =>
      hbd hq₂ id Function.injective_id h hh⟩
theorem partialHierarchyBounds_holds (hF : BoundedMultilinearEstimates)
    (hP : MultilinearProducts.Statement)
    (hC : VectorClasses.Claim) : PartialHierarchyBounds D := by
  intro C J₀ ρ S q hq d R hd hRad A hA j hj hAj
  have hR : 0 < R := hRad
  choose Wc hWc using fun B : Set (euclidean.Pt D) => ((hC D euclidean).1 B).1
  let W : Fin q → Submodule ℝ (euclidean.Pt D → ℝ) := fun l => Wc (A l)
  have hset : (fun l => lipschitzSupportedIn D euclidean (A l)) =
      fun l => (W l : Set (euclidean.Pt D → ℝ)) := funext fun l => (hWc _).symm
  have hmem : ∀ (B : Set (euclidean.Pt D)) (u : euclidean.Pt D → ℝ), u ∈ Wc B →
      u ∈ lipschitzSupportedIn D euclidean B := by
    intro B u hu
    have h : u ∈ (Wc B : Set (euclidean.Pt D → ℝ)) := hu
    rwa [hWc] at h
  have hW : ∀ l, ∀ u ∈ W l, u ∈ lipschitzSupportedIn D euclidean Set.univ := fun l u hu =>
    lipschitzSupportedIn_subset_univ (hmem _ u hu)
  have hprod : ∀ {k : ℕ}, 1 ≤ k → ∀ e : Fin k → Fin q, Function.Injective e →
      productSet D euclidean (fun i => (W (e i) : Set (euclidean.Pt D → ℝ))) ⊆
        sepLipTuplesWithin D euclidean k (centredBall D euclidean (ρ j)) := by
    intro k hk e he g hg
    have hA' := inBallPairwiseApart_of_separated hd hA hAj he
    exact ((hP D euclidean k hk).1 (ρ j) (S.radii.pos j)).2.1 _ hA'
      (fun i _ => hmem _ _ (hg i (Set.mem_univ i)))
  have hbd : ∀ {k : ℕ} (hk : 2 ≤ k), k ≤ q → ∀ e : Fin k → Fin q, Function.Injective e →
      ∀ g : sepLipTuplesWithin D euclidean k (centredBall D euclidean (ρ j)),
      g.1 ∈ productSet D euclidean (fun i => (W (e i) : Set (euclidean.Pt D → ℝ))) →
      ENNReal.ofReal |S.func j k hk g| ≤
        ENNReal.ofReal (C.val k d R) * ∏ i, sharpNormQ D euclidean (g.1 i) :=
    fun hk hkq e he g hg => S.boundedFrom _ hk R hRad j (hj _ hk hkq) d hd g
      (mem_lipTuplesSpacedInBalls hA he fun i => hmem _ _ (hg i (Set.mem_univ i)))
  have hsub : productSet D euclidean (fun l => (W l : Set (euclidean.Pt D → ℝ))) ⊆
      sepLipTuplesWithin D euclidean q (centredBall D euclidean (ρ j)) :=
    hprod hq id Function.injective_id
  obtain ⟨h₁, h₂⟩ := momentSum_form hF hC
    (S.toPartialHierarchySeq.toFunctionalSystem j) hq hW
    (fun I hI => hprod (by omega) _ (I.orderEmbOfFin rfl).injective)
    (fun I hI => S.multilinear j _ hI) (fun k => C.val k d R)
    (fun k hk _ => C.nonneg k hk d R hd hR)
    (fun I hI g hg => hbd hI (by simpa using Finset.card_le_univ I) _
      (I.orderEmbOfFin rfl).injective g hg) hsub
    (fun f hf => S.toPartialHierarchySeq.defined_of_mem_sepLipTuplesWithin j hf)
    (S.toPartialHierarchySeq.momentFun j) (fun f => rfl)
  rw [hset, momentBound_eq_partitionBound]
  exact ⟨h₁, h₂, fun hq₂ => satisfiesFormBounds_of_multilinear hF hC hq hW hsub
    (S.multilinear j q hq₂) (C.nonneg q hq₂ d R hd hR) fun h hh =>
      hbd hq₂ le_rfl id Function.injective_id h hh⟩
def alongIndexSet (J : Sequences.PNatIndexSet) : Filter ℕ+ := atTop ⊓ 𝓟 J.carrier
theorem eventually_alongIndexSet_iff {J : Sequences.PNatIndexSet} {P : ℕ+ → Prop} :
    (∀ᶠ j in alongIndexSet J, P j) ↔ DiagonalLimits.EventuallyAlong J P := by
  unfold alongIndexSet
  rw [eventually_inf_principal, eventually_atTop]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨((a : ℕ) : ℤ), fun j hj hle =>
      ha j ((PNat.coe_le_coe _ _).mp (by exact_mod_cast hle)) hj⟩
  · rintro ⟨j', h⟩
    refine ⟨Nat.succPNat j'.toNat, fun j hle hj => h j hj ?_⟩
    have : j'.toNat + 1 ≤ ((j : ℕ+) : ℕ) := (PNat.coe_le_coe _ _).mpr hle
    omega
theorem eventually_mem_alongIndexSet (J : Sequences.PNatIndexSet) :
    ∀ᶠ j in alongIndexSet J, j ∈ J.carrier :=
  eventually_alongIndexSet_iff.mpr ⟨0, fun _ hj _ => hj⟩
theorem tendsToAlong_iff_tendsto {J : Sequences.PNatIndexSet} {j₀ : ℤ}
    {w : (J.filterGe j₀).carrier → ℂ} {z' : ℂ} {z : ℝ} (hz : z' = (z : ℂ)) (v : ℕ+ → ℝ)
    (hv : ∀ j h, w ⟨j, h⟩ = (v j : ℂ)) :
    DiagonalLimits.TendsToAlong J j₀ w z' ↔ Tendsto v (alongIndexSet J) (𝓝 z) := by
  have hnorm : ∀ j h, ‖w ⟨j, h⟩ - z'‖ = dist (v j) z := by
    intro j h
    rw [hv, hz, ← Complex.ofReal_sub, Complex.norm_real, Real.dist_eq, Real.norm_eq_abs]
  constructor
  · intro H
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨j', h⟩ := H ε hε
    refine eventually_alongIndexSet_iff.mpr ⟨max j' j₀, fun j hj hle => ?_⟩
    have hm : j ∈ (J.filterGe j₀).carrier := ⟨hj, (le_max_right _ _).trans hle⟩
    show dist (v j) z < ε
    rw [← hnorm j hm]
    exact h j hj ((le_max_left _ _).trans hle) hm
  · intro H ε hε
    obtain ⟨j', h⟩ := eventually_alongIndexSet_iff.mp (Metric.tendsto_nhds.mp H ε hε)
    exact ⟨j', fun j hj hle hm => by rw [hnorm]; exact h j hj hle⟩
variable {J₀ J : Sequences.PNatIndexSet} {ρ : J₀.carrier → ℝ≥0∞}
open Classical in
def extendedEval (T : PartialHierarchySeq D euclidean J₀ ρ)
    (hJ : J.carrier ⊆ J₀.carrier) (n : ℕ) (hn : 2 ≤ n) (g : FnTuple D euclidean n) (j : ℕ+) : ℝ :=
  if h : ∃ hj : j ∈ J.carrier,
      g ∈ sepLipTuplesWithin D euclidean n (centredBall D euclidean (ρ ⟨j, hJ hj⟩)) then
    T.func ⟨j, hJ h.1⟩ n hn ⟨g, h.2⟩
  else 0
open Classical in
def extendedMoment (T : PartialHierarchySeq D euclidean J₀ ρ)
    (hJ : J.carrier ⊆ J₀.carrier) {q : ℕ} (G : J.carrier → FnTuple D euclidean q) (j : ℕ+) : ℝ :=
  if h : ∃ hj : j ∈ J.carrier, G ⟨j, hj⟩ ∈
      sepLipTuplesWithin D euclidean q (centredBall D euclidean (ρ ⟨j, hJ hj⟩)) then
    T.momentFun ⟨j, hJ h.1⟩ ⟨G ⟨j, h.1⟩, h.2⟩
  else 0
theorem momentsTendToAlong_of_tendsto (T : PartialHierarchySeq D euclidean J₀ ρ)
    (hJ : J.carrier ⊆ J₀.carrier) {q : ℕ} (G : J.carrier → FnTuple D euclidean q) (z : ℝ)
    (j' : ℤ)
    (hG : ∀ j : (J.filterGe j').carrier, G ⟨j.1, j.2.1⟩ ∈
      sepLipTuplesWithin D euclidean q (centredBall D euclidean (ρ ⟨j.1, hJ j.2.1⟩)))
    (hT : Tendsto (extendedMoment T hJ G) (alongIndexSet J) (𝓝 z)) :
    T.MomentsTendToAlong J hJ G z := by
  refine ⟨j', hG, (tendsToAlong_iff_tendsto rfl _ fun j h => ?_).mpr hT⟩
  have e : extendedMoment T hJ G j = T.momentFun ⟨j, hJ h.1⟩ ⟨_, hG ⟨j, h⟩⟩ :=
    dif_pos ⟨h.1, hG ⟨j, h⟩⟩
  rw [e]
theorem tendsto_extendedMoment_const (T : PartialHierarchySeq D euclidean J₀ ρ)
    (hJ : J.carrier ⊆ J₀.carrier) (Φ : SepFunctionals D euclidean)
    (hconv : T.TendsToPointwiseAlong J hJ Φ) {q : ℕ} (f : sepC1Tuples D euclidean q)
    (hev : ∀ᶠ j in alongIndexSet J, ∃ hj : j ∈ J.carrier, f.1 ∈
      sepLipTuplesWithin D euclidean q (centredBall D euclidean (ρ ⟨j, hJ hj⟩))) :
    Tendsto (extendedMoment T hJ fun _ => f.1) (alongIndexSet J)
      (𝓝 (momentFunOfSep Φ f)) := by
  have hI : ∀ (I : Finset (Fin q)) (hI : 2 ≤ I.card),
      Tendsto (extendedEval T hJ I.card hI (restrictTuple D euclidean f.1 I)) (alongIndexSet J)
        (𝓝 (Φ I.card hI ⟨restrictTuple D euclidean f.1 I,
          restrictTuple_mem_sepC1Tuples D euclidean f.2 I⟩)) := by
    intro I hI
    obtain ⟨j', hf, hc⟩ := hconv I.card hI
      ⟨_, restrictTuple_mem_sepC1Tuples D euclidean f.2 I⟩
    refine (tendsToAlong_iff_tendsto rfl _ fun j h => ?_).mp hc
    have e : extendedEval T hJ I.card hI (restrictTuple D euclidean f.1 I) j =
        T.func ⟨j, hJ h.1⟩ I.card hI ⟨_, hf ⟨j, h⟩⟩ := dif_pos ⟨h.1, hf ⟨j, h⟩⟩
    rw [e]
  have hT : Tendsto (fun j => ∑ π ∈ (SetPartition.singletonFree q).attach,
      ∏ I ∈ π.1.parts.attach, extendedEval T hJ I.1.card
        (two_le_card_of_mem_singletonFree π.2 I.2)
        (restrictTuple D euclidean f.1 I.1) j) (alongIndexSet J)
      (𝓝 (momentFunOfSep Φ f)) :=
    tendsto_finsetSum _ fun π _ => tendsto_finsetProd _ fun I _ => hI I.1 _
  refine hT.congr' (hev.mono fun j hj => ?_)
  obtain ⟨hj, hg⟩ := hj
  have e : extendedMoment T hJ (fun _ => f.1) j = T.momentFun ⟨j, hJ hj⟩ ⟨f.1, hg⟩ :=
    dif_pos ⟨hj, hg⟩
  rw [e]
  unfold PartialHierarchySeq.momentFun FunctionalSystem.momentSum
  refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun I _ => ?_
  exact dif_pos ⟨hj, restrictTuple_mem_sepLipTuplesWithin D euclidean hg I.1⟩
theorem centredBall_subset {E : Kind} {r : ℝ} {ρ' : ℝ≥0∞} (h : ENNReal.ofReal r < ρ') :
    centredBall D E (ENNReal.ofReal r) ⊆ centredBall D E ρ' := by
  intro y hy
  rw [centredBall, if_neg ENNReal.ofReal_ne_top] at hy
  by_cases hρ : ρ' = ∞
  · rw [centredBall, if_pos hρ]
    exact Set.mem_univ _
  · rw [centredBall, if_neg hρ]
    exact lt_of_lt_of_le hy (ENNReal.toReal_mono hρ h.le)
theorem eventually_radius_gt (T : PartialHierarchySeq D euclidean J₀ ρ)
    (hJ : J.carrier ⊆ J₀.carrier) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ j in alongIndexSet J, ∀ hj : j ∈ J.carrier, ENNReal.ofReal r < ρ ⟨j, hJ hj⟩ := by
  obtain ⟨j', h⟩ := T.radii.eventually_gt r hr
  exact eventually_alongIndexSet_iff.mpr ⟨j', fun j hj hle _ => h j (hJ hj) hle (hJ hj)⟩
theorem eventually_mem_sepLipTuplesWithin (hN : CompactlySupportedC1Bounds)
    (hD : IsLatticePowerScale D) (hT : YangMills.Construction.PeriodicSpace.TupleClasses.Statement)
    (T : PartialHierarchySeq D euclidean J₀ ρ) (hJ : J.carrier ⊆ J₀.carrier) {q : ℕ}
    {f : FnTuple D euclidean q} (hf : f ∈ sepC1Tuples D euclidean q) :
    ∀ᶠ j in alongIndexSet J, ∃ hj : j ∈ J.carrier,
      f ∈ sepLipTuplesWithin D euclidean q (centredBall D euclidean (ρ ⟨j, hJ hj⟩)) := by
  obtain ⟨r, hr, hsupp⟩ : ∃ r : ℝ, 0 < r ∧
      ∀ i, supportQ D euclidean (f i) ⊆ centredBall D euclidean (ENNReal.ofReal r) := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · exact ⟨1, one_pos, fun i => i.elim0⟩
    · obtain ⟨ρ', h0, hf', hm⟩ := (hT D euclidean q hq).2.2.2.1 f hf
      refine ⟨ρ'.toReal, ENNReal.toReal_pos h0.ne' hf'.ne, fun i => ?_⟩
      rw [ENNReal.ofReal_toReal hf'.ne]
      exact hm.2 i
  filter_upwards [eventually_radius_gt T hJ hr, eventually_mem_alongIndexSet J] with j h₁ h₂
  exact ⟨h₂, ⟨fun i => (hN D hD (f i) (hf.1 i) (hf.2.1 i)).2.2.1, hf.2⟩,
    fun i => (hsupp i).trans (centredBall_subset (h₁ h₂))⟩
theorem exists_centredBall_superset {q : ℕ} {d R : ℝ} {A : Fin q → Set (euclidean.Pt D)}
    (hR : 0 < R) (hA : SetsInBallsSeparated D euclidean d R A) :
    ∃ r : ℝ, 0 < r ∧ ∀ l, A l ⊆ centredBall D euclidean (ENNReal.ofReal r) := by
  have h : ∀ l, ∃ x, A l ⊆ closedBallAbout D euclidean x R := fun l => by
    obtain ⟨S, ⟨_, x, rfl⟩, hS⟩ := hA.1 l
    exact ⟨x, hS⟩
  choose x hx using h
  have key : ∀ y z : Fin 4 → ℝ, quotDist D euclidean y z ≤ R →
      quotDist D euclidean y (origin D euclidean) ≤ R + TorusMetric.euclidNormVec z := by
    intro y z hyz
    have e₁ := EuclideanCase.quotDist_euclidean_eq D y z
    have e₂ : quotDist D euclidean y (origin D euclidean) = TorusMetric.euclidNormVec (y - 0) :=
      EuclideanCase.quotDist_euclidean_eq D y 0
    have t := Periodization.euclidNormVec_triangle (y - z) z
    rw [sub_add_cancel] at t
    rw [e₂, sub_zero]
    rw [e₁] at hyz
    linarith
  have hnn : ∀ l, 0 ≤ TorusMetric.euclidNormVec (x l) := fun _ => Real.sqrt_nonneg _
  have hsum : 0 ≤ ∑ l, TorusMetric.euclidNormVec (x l) := Finset.sum_nonneg fun l _ => hnn l
  refine ⟨∑ l, TorusMetric.euclidNormVec (x l) + R + 1, by linarith, fun l y hy => ?_⟩
  rw [centredBall, if_neg ENNReal.ofReal_ne_top]
  show quotDist D euclidean y (origin D euclidean) < _
  rw [ENNReal.toReal_ofReal (by linarith)]
  have h₁ := key y (x l) (hx l hy)
  have h₂ := Finset.single_le_sum (fun l _ => hnn l) (Finset.mem_univ l)
  linarith
theorem sub_mem_and_toReal_sharpNormQ_le (hC : VectorClasses.Claim)
    {E : Kind} {u v : E.Pt D → ℝ} (hu : u ∈ lipschitzSupportedIn D E Set.univ)
    (hv : v ∈ lipschitzSupportedIn D E Set.univ) :
    u - v ∈ lipschitzSupportedIn D E Set.univ ∧
      (sharpNormQ D E u).toReal ≤ (sharpNormQ D E v).toReal + (sharpNormQ D E (u - v)).toReal := by
  have hn := (hC D E).2.1.2
  obtain ⟨W₀, hW₀⟩ := ((hC D E).1 Set.univ).1
  have hm : u - v ∈ lipschitzSupportedIn D E Set.univ := by
    rw [← hW₀] at hu hv ⊢
    exact W₀.sub_mem hu hv
  refine ⟨hm, ?_⟩
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨(hn.lt_top _ hv).ne, (hn.lt_top _ hm).ne⟩) (hn.add_le v hv _ hm)
  rwa [add_sub_cancel, ENNReal.toReal_add (hn.lt_top _ hv).ne (hn.lt_top _ hm).ne] at h
theorem momentConvergence_holds (hP : MultilinearProducts.Statement)
    (hN : CompactlySupportedC1Bounds)
    (hC : VectorClasses.Claim)
    (hT : YangMills.Construction.PeriodicSpace.TupleClasses.Statement) (hD : IsLatticePowerScale D)
    (h₃ : PartialHierarchyBounds D) : MomentConvergence D := by
  intro C J₀ ρ S J hJ Φ hconv
  have hfixed : ∀ (q : ℕ) (f : sepC1Tuples D euclidean q),
      Tendsto (extendedMoment S.toPartialHierarchySeq hJ fun _ => f.1) (alongIndexSet J)
        (𝓝 (momentFunOfSep Φ f)) := fun q f =>
    tendsto_extendedMoment_const S.toPartialHierarchySeq hJ Φ hconv f
      (eventually_mem_sepLipTuplesWithin hN hD hT S.toPartialHierarchySeq hJ f.2)
  refine ⟨fun q f => ?_, ?_⟩
  · obtain ⟨j', hj'⟩ := eventually_alongIndexSet_iff.mp
      (eventually_mem_sepLipTuplesWithin hN hD hT S.toPartialHierarchySeq hJ f.2)
    refine momentsTendToAlong_of_tendsto _ hJ _ _ j' (fun j => ?_) (hfixed q f)
    obtain ⟨_, h⟩ := hj' j.1 j.2.1 j.2.2
    exact h
  intro q hq d R hd hR A hA f F hf hFm hlim
  have hRad : R ∈ allowedRadii D euclidean := hR
  have hcl : ∀ l, c1SupportedIn D euclidean (A l) ⊆ lipschitzSupportedIn D euclidean (A l) :=
    fun l => c1SupportedIn_subset_lipschitz hN hD
  have hfS : f ∈ sepC1Tuples D euclidean q :=
    (((hP D euclidean q hq).1 ∞ (by simp)).1.1 _
      (inBallPairwiseApart_of_separated (e := id) hd hA (fun l => subset_centredBall_top (A l))
        Function.injective_id) hf).1
  refine ⟨hfS, ?_⟩
  obtain ⟨r, hr, hAr⟩ := exists_centredBall_superset hR hA
  have hgood : ∀ᶠ j in alongIndexSet J, ∃ hj : j ∈ J.carrier,
      (∀ (n : ℕ) (hn : 2 ≤ n), n ≤ q → S.threshold n hn R hRad ≤ (((j : ℕ+) : ℕ) : ℤ)) ∧
      ∀ l, A l ⊆ centredBall D euclidean (ρ ⟨j, hJ hj⟩) := by
    have h₁ : ∀ᶠ j : ℕ+ in alongIndexSet J, ∀ n ∈ Finset.range (q + 1), ∀ hn : 2 ≤ n,
        S.threshold n hn R hRad ≤ (((j : ℕ+) : ℕ) : ℤ) := by
      refine (Filter.eventually_all_finset _).mpr fun n _ => ?_
      by_cases hn : 2 ≤ n
      · exact eventually_alongIndexSet_iff.mpr ⟨S.threshold n hn R hRad, fun j _ hle _ => hle⟩
      · exact Eventually.of_forall fun j h => absurd h hn
    filter_upwards [h₁, eventually_radius_gt S.toPartialHierarchySeq hJ hr,
      eventually_mem_alongIndexSet J] with j a b c
    exact ⟨c, fun n hn hnq => a n (Finset.mem_range.mpr (by omega)) hn,
      fun l => (hAr l).trans (centredBall_subset (b c))⟩
  obtain ⟨j₁, hj₁⟩ := eventually_alongIndexSet_iff.mp hgood
  have hFl : ∀ j, F j ∈ productSet D euclidean (fun l => lipschitzSupportedIn D euclidean (A l)) :=
    fun j l _ => hcl l (hFm j l (Set.mem_univ l))
  have hfl : f ∈ productSet D euclidean (fun l => lipschitzSupportedIn D euclidean (A l)) :=
    fun l _ => hcl l (hf l (Set.mem_univ l))
  refine momentsTendToAlong_of_tendsto S.toPartialHierarchySeq hJ F _ j₁ (fun j => ?_) ?_
  · obtain ⟨_, a, b⟩ := hj₁ j.1 j.2.1 j.2.2
    exact (h₃ C J₀ ρ S q hq d R hd hRad A hA ⟨j.1, hJ j.2.1⟩ a b).1.1 (hFl _)
  have hu : ∀ {u} (l : Fin q), u ∈ lipschitzSupportedIn D euclidean (A l) →
      u ∈ lipschitzSupportedIn D euclidean Set.univ := fun _ h => lipschitzSupportedIn_subset_univ h
  have hfin : ∀ {u}, u ∈ lipschitzSupportedIn D euclidean Set.univ →
      sharpNormQ D euclidean u ≠ ∞ :=
    fun h => ((hC D euclidean).2.1.2.lt_top _ h).ne
  classical
  let s : Fin q → ℕ+ → ℝ := fun l j =>
    if h : j ∈ J.carrier then (sharpNormQ D euclidean (F ⟨j, h⟩ l - f l)).toReal else 0
  have hs : ∀ l, Tendsto (s l) (alongIndexSet J) (𝓝 0) := fun l =>
    (tendsToAlong_iff_tendsto Complex.ofReal_zero.symm (s l) fun j h => by
      simp only [s]
      rw [dif_pos h.1]).mp (hlim l)
  let a : Fin q → ℝ := fun l => (sharpNormQ D euclidean (f l)).toReal
  have hb0 : 0 ≤ C.momentBound q d R := by
    rw [momentBound_eq_partitionBound]
    exact partitionBound_nonneg fun k hk _ => C.nonneg k hk d R hd hR
  have hTz : Tendsto (fun j => C.momentBound q d R * ∑ l, s l j *
      ∏ l' ∈ Finset.univ.erase l, (2 * a l' + s l' j)) (alongIndexSet J) (𝓝 0) := by
    have h : Tendsto (fun j => C.momentBound q d R * ∑ l, s l j *
        ∏ l' ∈ Finset.univ.erase l, (2 * a l' + s l' j)) (alongIndexSet J)
        (𝓝 (C.momentBound q d R * ∑ l : Fin q, (0 : ℝ) *
          ∏ l' ∈ Finset.univ.erase l, (2 * a l' + 0))) :=
      tendsto_const_nhds.mul (tendsto_finsetSum _ fun l _ =>
        (hs l).mul (tendsto_finsetProd _ fun l' _ => tendsto_const_nhds.add (hs l')))
    simpa using h
  have hbd : ∀ᶠ j in alongIndexSet J, ‖extendedMoment S.toPartialHierarchySeq hJ F j -
      extendedMoment S.toPartialHierarchySeq hJ (fun _ => f) j‖ ≤
        C.momentBound q d R * ∑ l, s l j * ∏ l' ∈ Finset.univ.erase l, (2 * a l' + s l' j) := by
    filter_upwards [hgood] with j hj
    obtain ⟨hj, a₁, a₂⟩ := hj
    have hform := h₃ C J₀ ρ S q hq d R hd hRad A hA ⟨j, hJ hj⟩ a₁ a₂
    have kF := hform.1.1 (hFl ⟨j, hj⟩)
    have kf := hform.1.1 hfl
    have e₁ : extendedMoment S.toPartialHierarchySeq hJ F j =
        S.toPartialHierarchySeq.momentFun ⟨j, hJ hj⟩ ⟨_, kF⟩ := dif_pos ⟨hj, kF⟩
    have e₂ : extendedMoment S.toPartialHierarchySeq hJ (fun _ => f) j =
        S.toPartialHierarchySeq.momentFun ⟨j, hJ hj⟩ ⟨_, kf⟩ := dif_pos ⟨hj, kf⟩
    rw [e₁, e₂, Real.norm_eq_abs]
    have hb := hform.2.1.2 ⟨_, kF⟩ ⟨_, kf⟩ (hFl ⟨j, hj⟩) hfl
    have hFu : ∀ l, F ⟨j, hj⟩ l ∈ lipschitzSupportedIn D euclidean Set.univ := fun l =>
      hu l (hFl ⟨j, hj⟩ l (Set.mem_univ l))
    have hfu : ∀ l, f l ∈ lipschitzSupportedIn D euclidean Set.univ := fun l =>
      hu l (hfl l (Set.mem_univ l))
    have eq := ofReal_mul_sum_toReal hb0
      (fun l => sharpNormQ D euclidean (F ⟨j, hj⟩ l - f l))
      (fun l => sharpNormQ D euclidean (F ⟨j, hj⟩ l))
      (fun l => sharpNormQ D euclidean (f l))
      (fun l => hfin (sub_mem_and_toReal_sharpNormQ_le hC (hFu l) (hfu l)).1)
      (fun l => hfin (hFu l)) (fun l => hfin (hfu l))
    have hnn : ∀ k : Fin q, 0 ≤ (sharpNormQ D euclidean (F ⟨j, hj⟩ k)).toReal +
        (sharpNormQ D euclidean (f k)).toReal := fun _ =>
      add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    have hr' := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hb0 (Finset.sum_nonneg fun l _ =>
      mul_nonneg ENNReal.toReal_nonneg (Finset.prod_nonneg fun k _ => hnn k)))).mp
      (hb.trans_eq eq)
    refine hr'.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) hb0)
    have hsl : ∀ l, s l j = (sharpNormQ D euclidean (F ⟨j, hj⟩ l - f l)).toReal := fun l =>
      dif_pos hj
    rw [hsl l]
    refine mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun k _ => hnn k) fun k _ => ?_) ENNReal.toReal_nonneg
    rw [hsl k]
    have := (sub_mem_and_toReal_sharpNormQ_le hC (hFu k) (hfu k)).2
    simp only [a]
    linarith
  have hdiff := squeeze_zero_norm' hbd hTz
  have hsum := (hfixed q ⟨f, hfS⟩).add hdiff
  rw [add_zero] at hsum
  exact hsum.congr fun j => by ring
end OnEuclidean
theorem statement_holds (hF : BoundedMultilinearEstimates)
    (hP : MultilinearProducts.Statement)
    (hN : CompactlySupportedC1Bounds)
    (hC : VectorClasses.Claim)
    (hT : YangMills.Construction.PeriodicSpace.TupleClasses.Statement) : Statement :=
  ⟨abstractBounds_holds hF, fun _ hD =>
    ⟨hierarchyBounds_holds hF hP hN hC hD, partialHierarchyBounds_holds hF hP hC,
      momentConvergence_holds hP hN hC hT hD (partialHierarchyBounds_holds hF hP hC)⟩⟩
end YangMills.Construction.PeriodicSpace.Kind.CentredMoments
