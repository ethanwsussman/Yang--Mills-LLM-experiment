import YangMills.Construction.Analysis.MultilinearTelescopingBound
import YangMills.Construction.TorusOrFourSpace.BoundOfC1FormsAtEveryRadius
import YangMills.Construction.TorusOrFourSpace.ClassC1FunctionsProductsAndNeighbourhoods
import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNorm
import YangMills.Construction.TorusOrFourSpace.EffectiveConstantHoldsOnATorus
import YangMills.Construction.TorusOrFourSpace.FactsOnTheEffectiveConstants
import YangMills.Construction.TorusOrFourSpace.TheTwoKindsOfSequencesOfC1Forms
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.UniformBounds
theorem setInfDist_anti {D : Params} {E : Kind} {S S' T T' : Set (E.Pt D)}
    (hST : S ⊆ T) (hST' : S' ⊆ T') : setInfDist D E T T' ≤ setInfDist D E S S' :=
  le_iInf₂ fun z hz => le_iInf₂ fun z' hz' =>
    (iInf₂_le z (hST hz)).trans (iInf₂_le z' (hST' hz'))
theorem isMultilinearProd_of_isMultilinearOn {D : Params} {E : Kind} {n : ℕ}
    {K : Set (FnTuple D E n)} {Ψ : K → ℝ} (hΨ : IsMultilinearOn D E K Ψ)
    (V : Fin n → Submodule ℝ (E.Pt D → ℝ))
    (hIn : ∀ x : (∀ l, V l), (fun l => (x l : E.Pt D → ℝ)) ∈ K) :
    IsMultilinearProd fun x : (∀ l, V l) => Ψ ⟨fun l => (x l : E.Pt D → ℝ), hIn x⟩ := by
  intro x i
  have hoff : ∀ u v : V i, ∀ l, l ≠ i →
      ((Function.update x i u l : V l) : E.Pt D → ℝ) =
        ((Function.update x i v l : V l) : E.Pt D → ℝ) := by
    intro u v l hl
    simp [Function.update_of_ne hl]
  refine ⟨fun u v => ?_, fun a u => ?_⟩
  · have e : (fun l => ((Function.update x i (u + v) l : V l) : E.Pt D → ℝ)) =
        Function.update (fun l => ((Function.update x i u l : V l) : E.Pt D → ℝ)) i
          (((Function.update x i u i : V i) : E.Pt D → ℝ) +
            ((Function.update x i v i : V i) : E.Pt D → ℝ)) := by
      funext l
      by_cases hl : l = i
      · subst hl
        simp
      · simp [Function.update_of_ne hl]
    have hsum := hIn (Function.update x i (u + v))
    rw [e] at hsum
    have key := (hΨ i ⟨_, hIn (Function.update x i u)⟩ ⟨_, hIn (Function.update x i v)⟩
      (hoff u v)).1 hsum
    exact (congrArg Ψ (Subtype.ext e)).trans key
  · have e : (fun l => ((Function.update x i (a • u) l : V l) : E.Pt D → ℝ)) =
        Function.update (fun l => ((Function.update x i u l : V l) : E.Pt D → ℝ)) i
          (a • ((Function.update x i u i : V i) : E.Pt D → ℝ)) := by
      funext l
      by_cases hl : l = i
      · subst hl
        simp
      · simp [Function.update_of_ne hl]
    have hsmul := hIn (Function.update x i (a • u))
    rw [e] at hsmul
    have key := (hΨ i ⟨_, hIn (Function.update x i u)⟩ ⟨_, hIn (Function.update x i u)⟩
      (hoff u u)).2 a hsmul
    exact (congrArg Ψ (Subtype.ext e)).trans key
theorem isMultilinearOn_congr_domain {D : Params} {E : Kind} {n : ℕ}
    {K K' : Set (FnTuple D E n)} (hK : K = K') {Ψ : K → ℝ}
    (hΨ : IsMultilinearOn D E K Ψ) :
    IsMultilinearOn D E K' fun f => Ψ ⟨f.1, hK.symm ▸ f.2⟩ := by
  subst hK
  exact hΨ
def sharpSeminorm {D : Params} {E : Kind}
    (hNorm : VectorClasses.IsNormOn D E (lipschitzSupportedIn D E Set.univ) (sharpNormQ D E))
    (V : Submodule ℝ (E.Pt D → ℝ)) (hV : ∀ u ∈ V, u ∈ lipschitzSupportedIn D E Set.univ) :
    Seminorm ℝ V :=
  Seminorm.of (fun u => sharpNormReal D E (u : E.Pt D → ℝ))
    (fun u v => by
      have hu := hNorm.lt_top _ (hV _ u.2)
      have hv := hNorm.lt_top _ (hV _ v.2)
      have key := hNorm.add_le _ (hV _ u.2) _ (hV _ v.2)
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hu.ne, hv.ne⟩) key
      rwa [ENNReal.toReal_add hu.ne hv.ne] at this)
    (fun a u => by
      have key := hNorm.smul _ (hV _ u.2) a
      change (sharpNormQ D E (a • (u : E.Pt D → ℝ))).toReal = _
      rw [key, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg a), Real.norm_eq_abs]
      rfl)
theorem equicontinuityBounds_of_bound {D : Params} {E : Kind} {n : ℕ} (hn : 1 ≤ n)
    (hForms : Multilinear.MultilinearTelescopingBound)
    (hNorm : VectorClasses.IsNormOn D E (lipschitzSupportedIn D E Set.univ) (sharpNormQ D E))
    (V : Fin n → Submodule ℝ (E.Pt D → ℝ))
    (hV : ∀ l, ∀ u ∈ V l, u ∈ lipschitzSupportedIn D E Set.univ)
    (Φ : (∀ l, V l) → ℝ) (hΦ : IsMultilinearProd Φ) (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ x : (∀ l, V l), ENNReal.ofReal |Φ x| ≤
      ENNReal.ofReal c * ∏ l, sharpNormQ D E (x l : E.Pt D → ℝ))
    (f g : ∀ l, V l) :
    EquicontinuityBounds D E c (Φ f) (Φ g) (fun l => (f l : E.Pt D → ℝ))
      (fun l => (g l : E.Pt D → ℝ)) := by
  let Ψ : MultilinearMap ℝ (fun l => V l) ℝ :=
    { toFun := Φ
      map_update_add' := by
        intro inst x i u v
        obtain rfl : inst = (fun a b => instDecidableEqFin n a b) := Subsingleton.elim _ _
        exact (hΦ x i).map_add u v
      map_update_smul' := by
        intro inst x i a u
        obtain rfl : inst = (fun a b => instDecidableEqFin n a b) := Subsingleton.elim _ _
        exact (hΦ x i).map_smul a u }
  have hbound : ∀ x : (∀ l, V l),
      |Ψ x| ≤ c * ∏ l, sharpSeminorm hNorm (V l) (hV l) (x l) := by
    intro x
    have hfin : ENNReal.ofReal c * ∏ l, sharpNormQ D E (x l : E.Pt D → ℝ) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.prod_ne_top fun l _ => (hNorm.lt_top _ (hV l _ (x l).2)).ne)
    have key := ENNReal.toReal_mono hfin (hb x)
    rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_ofReal hc,
      ENNReal.toReal_prod] at key
    exact key
  exact hForms n hn (fun l => V l) (fun l => sharpSeminorm hNorm (V l) (hV l)) c hc Ψ hbound f g
theorem bound_of_mem_productSet
    (hTorus : TorusEffectiveBound.Claim)
    (hElem : C1ProductsAndThickenings.Statement)
    {D : Params} {E : Kind} {θ : RadiusRatio} (P : TorusPartitionChoice D θ)
    {C : BoundFamily} {J₀ : Sequences.PNatIndexSet} {ρ : J₀.carrier → ℝ≥0∞}
    (Ψ : BoundedC1FormSeq D E J₀ ρ C) {n : ℕ} (hn : 2 ≤ n) {d R : ℝ} (hd : 0 < d)
    (hR : 0 < R) {A : Fin n → Set (E.Pt D)}
    (hA : InBallsAndSeparated D E A d R) (j : J₀.carrier)
    (hj : Ψ.thresholdAtRadius θ n hn R hR ≤ (((j.1 : ℕ+) : ℕ) : ℤ))
    (x : sepC1TuplesInBall D E n (ρ j))
    (hx : x.1 ∈ productSet D E fun l => c1SupportedIn D E (A l)) :
    ENNReal.ofReal |Ψ.func j n hn x| ≤
      ENNReal.ofReal (effConstAt P E C n d R) *
        ∏ l, sharpNormQ D E (x.1 l) := by
  have hmem : ∀ l, x.1 l ∈ c1SupportedIn D E (A l) := fun l => hx l (Set.mem_univ l)
  have hdist : ∀ i k, i ≠ k →
      ENNReal.ofReal d ≤ setInfDist D E (supportQ D E (x.1 i)) (supportQ D E (x.1 k)) :=
    fun i k hik => (hA.2 i k hik).trans
      (setInfDist_anti (hmem i).2.2 (hmem k).2.2)
  by_cases hadm : R ∈ allowedRadii D E
  · rw [effConstAt_of_mem P E C n d hadm]
    have hs : Ψ.thresholdAtRadius θ n hn R hR = Ψ.threshold n hn R hadm := dif_pos hadm
    rw [hs] at hj
    refine Ψ.boundedFrom n hn R hadm j hj d hd x ⟨fun i => ?_, fun i => ?_, hdist⟩
    · exact ((hElem D E).1.2.1 (A i) (hmem i)).1
    · obtain ⟨S, hS, hAS⟩ := hA.1 i
      exact ⟨S, hS, (hmem i).2.2.trans hAS⟩
  · have hE : E = torus := by
      cases E with
      | euclidean => exact absurd (Set.mem_Ioi.2 hR) hadm
      | torus => rfl
    subst hE
    have hρ : ρ j = ∞ := Ψ.radii.eq_top_of_torus rfl j
    have hKeq : sepC1TuplesInBall D torus n (ρ j) = sepC1Tuples D torus n := by
      rw [hρ]
      exact sepC1TuplesInBall_top D torus n
    have hs : Ψ.thresholdAtRadius θ n hn R hR =
        Ψ.threshold n hn (ballRadius D θ torus)
          (ballRadius_mem_allowedRadii D θ torus) := dif_neg hadm
    rw [hs] at hj
    have hmult := isMultilinearOn_congr_domain hKeq (Ψ.multilinear j n hn)
    obtain ⟨hiff, hres⟩ := hTorus D θ P C n hn d hd _ hmult (fun g hg =>
      Ψ.boundedFrom n hn _ (ballRadius_mem_allowedRadii D θ torus) j hj d hd _ hg)
    have hsep : ENNReal.ofReal d ≤ supportGap D torus x.1 :=
      le_iInf fun i => le_iInf fun k => le_iInf fun hik => hdist i k hik
    exact (hres R ((hiff R).2 ⟨hR, hadm⟩)).2 ⟨x.1, hKeq ▸ x.2⟩ hsep
theorem boundedC1FormSeq_bounds
    (hClasses : VectorClasses.Claim)
    (hElem : C1ProductsAndThickenings.Statement)
    (hProducts : MultilinearProducts.Statement)
    (hFacts : EffectiveConstantFacts.Claim)
    (hTorus : TorusEffectiveBound.Claim)
    (hForms : Multilinear.MultilinearTelescopingBound)
    {D : Params} {E : Kind} {θ : RadiusRatio} (P : TorusPartitionChoice D θ)
    {C : BoundFamily} {J₀ : Sequences.PNatIndexSet} {ρ : J₀.carrier → ℝ≥0∞}
    (Ψ : BoundedC1FormSeq D E J₀ ρ C) {n : ℕ} (hn : 2 ≤ n) {d R : ℝ} (hd : 0 < d)
    (hR : 0 < R) {A : Fin n → Set (E.Pt D)}
    (hA : InBallsAndSeparated D E A d R) (j : J₀.carrier)
    (hj : Ψ.thresholdAtRadius θ n hn R hR ≤ (((j.1 : ℕ+) : ℕ) : ℤ))
    (hAj : ∀ l, A l ⊆ centredBall D E (ρ j)) :
    MultilinearOnClasses D E (sepC1TuplesInBall D E n (ρ j))
        (Ψ.func j n hn) (fun l => c1SupportedIn D E (A l)) ∧
      BoundedEquicontOnClasses D E (sepC1TuplesInBall D E n (ρ j))
        (Ψ.func j n hn) (fun l => c1SupportedIn D E (A l))
        (effConstAt P E C n d R) := by
  have hn1 : 1 ≤ n := by omega
  have hK : productSet D E (fun l => c1SupportedIn D E (A l)) ⊆
      sepC1TuplesInBall D E n (ρ j) :=
    ((hProducts D E n hn1).1 (ρ j) (Ψ.radii.pos j)).1.1 A
      ⟨hAj, fun l l' hll => lt_of_lt_of_le (ENNReal.ofReal_pos.2 hd) (hA.2 l l' hll)⟩
  have hsub : ∀ l, ∃ W : Submodule ℝ (E.Pt D → ℝ),
      (W : Set (E.Pt D → ℝ)) = c1SupportedIn D E (A l) :=
    fun l => ((hClasses D E).1 (A l)).2.1
  choose V hV using hsub
  have hmemV : ∀ l (u : E.Pt D → ℝ), u ∈ V l ↔ u ∈ c1SupportedIn D E (A l) := fun l u => by
    rw [← hV l]
    rfl
  have hIn : ∀ x : (∀ l, V l), (fun l => (x l : E.Pt D → ℝ)) ∈
      sepC1TuplesInBall D E n (ρ j) :=
    fun x => hK fun l _ => (hmemV l _).1 (x l).2
  have hmulti := isMultilinearProd_of_isMultilinearOn (Ψ.multilinear j n hn) V hIn
  have hLip : ∀ l, ∀ u ∈ V l, u ∈ lipschitzSupportedIn D E Set.univ := fun l u hu => by
    have hu' := (hElem D E).1.2.1 (A l) ((hmemV l u).1 hu)
    exact ⟨hu'.1, hu'.2.1, Set.subset_univ _⟩
  have hc : 0 ≤ effConstAt P E C n d R :=
    hFacts.2.2.1 D θ P E C n hn d R hd hR
  have hbound := bound_of_mem_productSet hTorus hElem P Ψ hn hd hR hA j hj
  refine ⟨⟨V, hV, hIn, hmulti⟩, hK, hbound, fun f g hf hg => ?_⟩
  exact equicontinuityBounds_of_bound hn1 hForms (hClasses D E).2.1.2 V hLip _ hmulti _ hc
    (fun x => hbound ⟨_, hIn x⟩ fun l _ => (hmemV l _).1 (x l).2)
    (fun l => ⟨f.1 l, (hmemV l _).2 (hf l (Set.mem_univ l))⟩)
    (fun l => ⟨g.1 l, (hmemV l _).2 (hg l (Set.mem_univ l))⟩)
theorem uniformC1Bounds
    (hClasses : VectorClasses.Claim)
    (hElem : C1ProductsAndThickenings.Statement)
    (hProducts : MultilinearProducts.Statement)
    (hFacts : EffectiveConstantFacts.Claim)
    (hKinds : C1FormSeqKinds.Statement)
    (hTorus : TorusEffectiveBound.Claim)
    (hForms : Multilinear.MultilinearTelescopingBound) :
    UniformC1Bounds := by
  intro D E θ P C
  refine ⟨?_, ?_⟩
  · intro J₀ ρ Ψ n hn d R hd hR A hA j hj hAj
    exact boundedC1FormSeq_bounds hClasses hElem hProducts hFacts hTorus hForms P Ψ hn hd hR hA
      j hj hAj
  · intro Φ hΦ n hn d R hd hR A hA
    obtain ⟨Ψ, hfam, hstart⟩ := (hKinds D θ E C).2.2.2 Φ hΦ
    let j : {k : ℕ+ // k ∈ (Set.univ : Set ℕ+)} := ⟨1, Set.mem_univ _⟩
    have hj : Ψ.thresholdAtRadius θ n hn R hR ≤ (((j.1 : ℕ+) : ℕ) : ℤ) := by
      rw [hstart n hn R hR]
      simp [j]
    have hAj : ∀ l, A l ⊆ centredBall D E ((fun _ => ∞) j) := fun l => by
      simp [centredBall]
    have key := (boundedC1FormSeq_bounds hClasses hElem hProducts hFacts hTorus hForms P Ψ hn hd
      hR hA j hj hAj).2
    have hKeq := sepC1TuplesInBall_top D E n
    have hval : ∀ (f : sepC1Tuples D E n) (hf : f.1 ∈ sepC1TuplesInBall D E n ∞),
        Ψ.func j n hn ⟨f.1, hf⟩ = Φ.func n hn f :=
      fun f hf => hfam.2 j n hn ⟨f.1, hf⟩
    refine ⟨fun f hf => hKeq ▸ key.1 hf, fun x hx => ?_, fun f g hf hg => ?_⟩
    · have hb := key.2.1 ⟨x.1, hKeq.symm ▸ x.2⟩ hx
      rwa [hval x] at hb
    · have hb := key.2.2 ⟨f.1, hKeq.symm ▸ f.2⟩ ⟨g.1, hKeq.symm ▸ g.2⟩ hf hg
      rwa [hval f, hval g] at hb
end YangMills.Construction.PeriodicSpace.Kind.UniformBounds
