import YangMills.Construction.ColdChainAtEveryLevel.AnalyticCoordinatesOfAColdTopProof
import YangMills.Construction.ColdChainAtEveryLevel.MixedDerivativesOfAComposite
import YangMills.Construction.ColdChainAtEveryLevel.RotationDerivativeOfARestrictionProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.BlockAverages
namespace EvaluationMixedDeriv
variable {F : BlockFrame}
section Calculus
variable {A W E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
theorem iteratedFDeriv_comp_continuousLinearMap (g : A →L[ℝ] W) {f : W → E} {x : A} (hf : AnalyticAt ℝ f (g x))
    (m : ℕ) (v : Fin m → A) :
    iteratedFDeriv ℝ m (f ∘ g) x v = iteratedFDeriv ℝ m f (g x) (fun l => g (v l)) := by apply _root_.YangMills.Construction.BlockAverages.DerivAlongRotation.iteratedFDeriv_comp_clm_of_analyticAt <;> assumption
theorem iteratedFDeriv_succ_comp_add_const (f : A → W) (c : W) (p : ℕ) (x : A) :
    iteratedFDeriv ℝ (p + 1) (fun ζ => f ζ + c) x = iteratedFDeriv ℝ (p + 1) f x := by
  have he : fderiv ℝ (fun ζ => f ζ + c) = fderiv ℝ f := by
    funext y
    exact fderiv_add_const c
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, he]
theorem iteratedFDeriv_one_id_apply (x : A) (v : Fin 1 → A) :
    iteratedFDeriv ℝ 1 (fun ζ : A => ζ) x v = v 0 := by
  rw [iteratedFDeriv_one_apply]
  have : fderiv ℝ (fun ζ : A => ζ) x = ContinuousLinearMap.id ℝ A := fderiv_fun_id
  rw [this]
  rfl
theorem iteratedFDeriv_id_of_two_le (x : A) (p : ℕ) (hp : 2 ≤ p) :
    iteratedFDeriv ℝ p (fun ζ : A => ζ) x = 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have he : fderiv ℝ (fun ζ : A => ζ) = fun _ => ContinuousLinearMap.id ℝ A := by
    funext y
    exact fderiv_fun_id
  rw [iteratedFDeriv_succ_eq_comp_right, he]
  have hq : q ≠ 0 := by omega
  simp [iteratedFDeriv_const_of_ne hq]
end Calculus
section Coordinates
variable {S : Finset F.Cell}
abbrev LocalChartSpace (S : Finset F.Cell) : Type :=
  (↥(innerBonds S 0) → imaginaryQuaternions) × ((j : Fin F.depth) → ↥(innerBonds S (j.1 + 1)) → imaginaryQuaternions)
def toLocal (S : Finset F.Cell) (U : ChainChart F) : LocalChartSpace S :=
  (fun b => U.fine b.1.1 b.1.2, fun j b => U.coarse j.1 b.1.1 b.1.2)
open Classical in
def ofLocal (x : LocalChartSpace S) : ChainChart F :=
  ⟨fun y i => if h : (y, i) ∈ innerBonds S 0 then x.1 ⟨(y, i), h⟩ else 0,
    fun j y i => if h' : j < F.depth then
      if h : (y, i) ∈ innerBonds S (j + 1) then x.2 ⟨j, h'⟩ ⟨(y, i), h⟩ else 0 else 0⟩
theorem ofLocal_fine (x : LocalChartSpace S) {b : F.Site 0 × Fin 4} (hb : b ∈ innerBonds S 0) :
    (ofLocal x).fine b.1 b.2 = x.1 ⟨b, hb⟩ := by
  simp [ofLocal, hb]
theorem ofLocal_coarse (x : LocalChartSpace S) {j : ℕ} (hj : j < F.depth) {b : F.Site (j + 1) × Fin 4}
    (hb : b ∈ innerBonds S (j + 1)) :
    (ofLocal x).coarse j b.1 b.2 = x.2 ⟨j, hj⟩ ⟨b, hb⟩ := by
  simp [ofLocal, hb, hj]
theorem chartAgreeOn_trans {U U' U'' : ChainChart F} (h : ChartEqOnBonds S U U')
    (h' : ChartEqOnBonds S U' U'') : ChartEqOnBonds S U U'' :=
  ⟨fun b hb => (h.1 b hb).trans (h'.1 b hb), fun j hj c hc => (h.2 j hj c hc).trans (h'.2 j hj c hc)⟩
def chartCombination {ι : Type} [Fintype ι] (y : ι → ℝ) (A : ι → ChainChart F) : ChainChart F :=
  ⟨fun x i => ∑ l, y l • (A l).fine x i, fun j x i => ∑ l, y l • (A l).coarse j x i⟩
theorem chartAgreeOn_combination_ofLocal {ι : Type} [Fintype ι] (y : ι → ℝ) (x : ι → LocalChartSpace S) :
    ChartEqOnBonds S (chartCombination y fun l => ofLocal (x l)) (ofLocal (∑ l, y l • x l)) := by
  refine ⟨fun b hb => ?_, fun j hj c hc => ?_⟩
  · rw [ofLocal_fine _ hb]
    simp only [chartCombination, ofLocal_fine _ hb, Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply]
  · have hj' : j < F.depth := by
      simp only [BlockFrame.top] at hj
      omega
    rw [ofLocal_coarse _ hj' hc]
    simp only [chartCombination, ofLocal_coarse _ hj' hc, Prod.snd_sum, Prod.smul_snd, Finset.sum_apply,
      Pi.smul_apply]
theorem chartShiftAlong_sum_smul {ι κ : Type} [Fintype ι] [Fintype κ] (U : ChainChart F) (A : ι → ChainChart F)
    (y : κ → ι → ℝ) (t : κ → ℝ) :
    chartShiftAlong U A (∑ i, t i • y i) = chartShiftAlong U (fun i => chartCombination (y i) A) t := by
  have key : ∀ (M : Type) [AddCommMonoid M] [Module ℝ M] (f : ι → M),
      ∑ l, (∑ i, t i • y i : ι → ℝ) l • f l = ∑ i, t i • ∑ l, y i l • f l := by
    intro M _ _ f
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, Finset.smul_sum, mul_smul]
    rw [Finset.sum_comm]
  simp only [chartShiftAlong, chartCombination]
  congr 1
  · funext x i
    rw [key]
  · funext j x i
    rw [key]
theorem localNorm_congr {R : F.FieldChain} {A A' : ChainChart F} (z : F.Cell) (h : ChartEqOnBonds S A A') :
    localNorm S R A (oneSiteWeights F) z = localNorm S R A' (oneSiteWeights F) z := by apply _root_.YangMills.Construction.BlockAverages.AnalyticChart.localNorm_congr <;> assumption
theorem topVariationAlong_bondSpread {k : ℕ} {ι : Type} [Fintype ι] (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (η : ι → Fin k → ℝ) (t : ι → ℝ) :
    topVariationAlong (fun β => bondSpread c X (η β)) t = bondSpread c X (∑ β, t β • η β) := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.topVariationAlong_bondSpread <;> assumption
theorem topVariationAlong_sum_smul {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι → F.Site F.top → Fin 4 → imaginaryQuaternions) (y : κ → ι → ℝ) (t : κ → ℝ) :
    topVariationAlong e (∑ i, t i • y i) = topVariationAlong (fun i => topVariationAlong e (y i)) t := by
  funext a b
  simp only [topVariationAlong, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, Finset.smul_sum,
    mul_smul]
  rw [Finset.sum_comm]
theorem localDirectionSize_nonneg (R : F.FieldChain) (B : Finset (F.Site F.top × Fin 4)) (z : F.Cell)
    (A : ChainChart F) (e : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    0 ≤ localDirectionSize S R B z A e := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.localDirectionSize_nonneg <;> assumption
theorem topVariationNorm_bondSpread_single_le {k : ℕ} (B : Finset (F.Site F.top × Fin 4))
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) (l : Fin k) :
    topVariationNorm B (bondSpread c X (Pi.single l 1)) ≤ if c l ∈ B then 1 else 0 := by
  classical
  have he : ∀ b : F.Site F.top × Fin 4, ‖bondSpread c X (Pi.single l 1) b.1 b.2‖ = if c l = b then 1 else 0 := by
    intro b
    have h1 : bondSpread c X (Pi.single l 1) b.1 b.2 = if c l = b then X l else 0 := by
      simp only [bondSpread]
      rw [Finset.sum_eq_single l]
      · simp
      · intro l' _ hl'
        simp [Pi.single_eq_of_ne hl']
      · intro h
        exact absurd (Finset.mem_univ l) h
    rw [h1]
    split_ifs
    · exact hX l
    · simp
  unfold topVariationNorm
  simp only [he]
  rw [Finset.sum_ite_eq]
theorem topVariationNorm_part_le {k p : ℕ} (B : Finset (F.Site F.top × Fin 4)) (z : F.Cell)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) (δ : ℝ)
    (hδ : 0 ≤ δ) (r₀ : ℕ) (hB : ∀ b ∈ B, cellSupDist z b.1 ≤ r₀) (hp : 1 ≤ p) (f : Fin p → Fin k) :
    topVariationNorm B (bondSpread c X (iteratedFDeriv ℝ p (fun ζ : Fin k → ℝ => ζ) 0 fun l => Pi.single (f l) 1)) ≤
      Real.exp (δ * r₀) * Real.exp (-δ * bondListDistance z (c ∘ f)) := by
  classical
  have hpos : 0 ≤ Real.exp (δ * r₀) * Real.exp (-δ * bondListDistance z (c ∘ f)) := by positivity
  by_cases h1 : p = 1
  · subst h1
    rw [iteratedFDeriv_one_id_apply]
    refine (topVariationNorm_bondSpread_single_le B c X hX (f 0)).trans ?_
    split_ifs with hm
    · have h2 : bondListDistance z (c ∘ f) ≤ r₀ := by
        refine Finset.sup_le fun l _ => ?_
        have : l = 0 := Subsingleton.elim _ _
        subst this
        exact hB _ hm
      have h3 : (bondListDistance z (c ∘ f) : ℝ) ≤ r₀ := by exact_mod_cast h2
      rw [← Real.exp_add]
      have h4 : 0 ≤ δ * r₀ + -δ * bondListDistance z (c ∘ f) := by nlinarith
      exact Real.one_le_exp h4
    · exact hpos
  · have h2 : 2 ≤ p := by omega
    rw [iteratedFDeriv_id_of_two_le _ _ h2]
    have he : bondSpread c X (0 : Fin k → ℝ) = fun _ _ => 0 := by
      funext y i
      simp [bondSpread]
    simp only [zero_apply]
    rw [he]
    simpa [topVariationNorm] using hpos
end Coordinates
end EvaluationMixedDeriv
theorem localMixedDeriv_holds (hC : Analytic.FaaDiBrunoAnalyticProperty) :
    localMixedDerivStatement := by
  classical
  open EvaluationMixedDeriv in
  intro F E _ _ _ S R z B Ck Dk U Φ δ r₀ k c X T hδ hCk hDk hΦ hX hB h0 hfine hcoarse hdec
  have : FiniteDimensional ℝ imaginaryQuaternions := inferInstance
  have : CompleteSpace imaginaryQuaternions := FiniteDimensional.complete ℝ imaginaryQuaternions
  let bs := Module.finBasis ℝ (LocalChartSpace S × (Fin k → ℝ))
  set d := Module.finrank ℝ (LocalChartSpace S × (Fin k → ℝ)) with hd
  let A : Fin d → ChainChart F := fun β => ofLocal (bs β).1
  let e : Fin d → F.Site F.top → Fin 4 → imaginaryQuaternions := fun β => bondSpread c X (bs β).2
  let Ψ : (Fin d → ℝ) → E := fun t => Φ (chartShiftAlong U A t) (topVariationAlong e t)
  have hΨ : AnalyticAt ℝ Ψ 0 := hΦ.analyticAt A e
  let x₀ : LocalChartSpace S := toLocal S (T 0)
  let Lb : (LocalChartSpace S × (Fin k → ℝ)) →L[ℝ] (Fin d → ℝ) :=
    (bs.equivFunL : _ ≃L[ℝ] _).toContinuousLinearMap
  let Q : (Fin k → ℝ) → LocalChartSpace S × (Fin k → ℝ) := fun ζ => (toLocal S (T ζ) + -x₀, ζ)
  let τ : (Fin k → ℝ) → (Fin d → ℝ) := fun ζ => Lb (Q ζ)
  have hloc : AnalyticAt ℝ (fun ζ => toLocal S (T ζ)) 0 := by
    refine AnalyticAt.prod ?_ ?_
    · rw [analyticAt_pi_iff]
      exact fun b => hfine b.1 b.2
    · rw [analyticAt_pi_iff]
      intro j
      rw [analyticAt_pi_iff]
      exact fun b => hcoarse j.1 (by simp only [BlockFrame.top]; omega) b.1 b.2
  have hQ : AnalyticAt ℝ Q 0 := (hloc.add analyticAt_const).prod analyticAt_id
  have hτ : AnalyticAt ℝ τ 0 := Lb.analyticAt _ |>.comp hQ
  have hQ0 : Q 0 = 0 := by
    simp only [Q, x₀]
    ext <;> simp
  have hτ0 : τ 0 = 0 := by
    simp only [τ, hQ0, map_zero]
  have hrec : ∀ ζ, ∑ β, τ ζ β • bs β = Q ζ := fun ζ => bs.sum_equivFun (Q ζ)
  have key : ∀ ζ, Φ (T ζ) (bondSpread c X ζ) = Ψ (τ ζ) := by
    intro ζ
    have hturn : topVariationAlong e (τ ζ) = bondSpread c X ζ := by
      have h1 := topVariationAlong_bondSpread c X (fun β => (bs β).2) (τ ζ)
      have h2 : ∑ β, τ ζ β • (bs β).2 = ζ := by
        have := congrArg Prod.snd (hrec ζ)
        simpa [Prod.snd_sum] using this
      rw [h2] at h1
      exact h1
    have hsame : ChartEqOnBonds S (T ζ) (chartShiftAlong U A (τ ζ)) := by
      have h1 := chartAgreeOn_combination_ofLocal (S := S) (τ ζ) (fun β => (bs β).1)
      have h2 : ∑ β, τ ζ β • (bs β).1 = toLocal S (T ζ) + -x₀ := by
        have := congrArg Prod.fst (hrec ζ)
        simpa [Prod.fst_sum] using this
      rw [h2] at h1
      refine ⟨fun b hb => ?_, fun j hj c' hc' => ?_⟩
      · have e1 := h1.1 b hb
        have e2 := h0.1 b hb
        rw [ofLocal_fine _ hb] at e1
        show (T ζ).fine b.1 b.2 = U.fine b.1 b.2 + ∑ l, τ ζ l • (A l).fine b.1 b.2
        have e3 : ∑ l, τ ζ l • (A l).fine b.1 b.2 = (toLocal S (T ζ) + -x₀).1 ⟨b, hb⟩ := e1
        rw [e3, ← e2]
        simp [toLocal, x₀]
      · have hj' : j < F.depth := by
          simp only [BlockFrame.top] at hj
          omega
        have e1 := h1.2 j hj c' hc'
        have e2 := h0.2 j hj c' hc'
        rw [ofLocal_coarse _ hj' hc'] at e1
        show (T ζ).coarse j c'.1 c'.2 = U.coarse j c'.1 c'.2 + ∑ l, τ ζ l • (A l).coarse j c'.1 c'.2
        have e3 : ∑ l, τ ζ l • (A l).coarse j c'.1 c'.2 = (toLocal S (T ζ) + -x₀).2 ⟨j, hj'⟩ ⟨c', hc'⟩ := e1
        rw [e3, ← e2]
        simp [toLocal, x₀]
    show Φ (T ζ) (bondSpread c X ζ) = Φ (chartShiftAlong U A (τ ζ)) (topVariationAlong e (τ ζ))
    rw [hturn]
    exact hΦ.congr_of_agree _ _ _ hsame
  have hH : (fun ζ : Fin k → ℝ => Φ (T ζ) (bondSpread c X ζ)) = Ψ ∘ τ := funext key
  have hΨτ : AnalyticAt ℝ Ψ (τ 0) := by rw [hτ0]; exact hΨ
  set M : ℝ := Real.exp (δ * r₀) with hMdef
  have hM0 : 0 ≤ M := (Real.exp_pos _).le
  have hexp : ∀ (m : ℕ) (e' : Fin m ↪ Fin k), 1 ≤ m →
      ∃ A₁ : (cP : OrderedFinpartition m) → Fin cP.length → ChainChart F,
        (∀ cP i, ChartEqOnBonds S (A₁ cP i) (mixedDerivativeChart T (partEmbedding e' cP i))) ∧
        iteratedFDeriv ℝ m (fun ζ : Fin k → ℝ => Φ (T ζ) (bondSpread c X ζ)) 0 (fun l => Pi.single (e' l) 1) =
          ∑ cP : OrderedFinpartition m,
            localIteratedDeriv Φ U (A₁ cP) fun i => partSpread c X (partEmbedding e' cP i) := by
    intro m e' hm
    have per : ∀ cP : OrderedFinpartition m, ∃ A₁ : Fin cP.length → ChainChart F,
        (∀ i, ChartEqOnBonds S (A₁ i) (mixedDerivativeChart T (partEmbedding e' cP i))) ∧
        iteratedFDeriv ℝ cP.length Ψ (τ 0)
            (fun i => iteratedFDeriv ℝ (cP.partSize i) τ 0 ((fun l => Pi.single (e' l) 1) ∘ cP.emb i)) =
          localIteratedDeriv Φ U A₁ fun i => partSpread c X (partEmbedding e' cP i) := by
      intro cP
      set v : Fin m → (Fin k → ℝ) := fun l => Pi.single (e' l) 1 with hv
      set y : Fin cP.length → Fin d → ℝ := fun i => iteratedFDeriv ℝ (cP.partSize i) τ 0 (v ∘ cP.emb i) with hy
      let Lm : (Fin cP.length → ℝ) →L[ℝ] (Fin d → ℝ) :=
        ∑ i, (ContinuousLinearMap.proj i : (Fin cP.length → ℝ) →L[ℝ] ℝ).smulRight (y i)
      have hLm : ∀ t, Lm t = ∑ i, t i • y i := by
        intro t
        simp [Lm]
      have hLm0 : Lm 0 = 0 := map_zero _
      have hLs : ∀ i, Lm (Pi.single i 1) = y i := by
        intro i
        rw [hLm, Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [Pi.single_eq_of_ne hj]
        · intro h
          exact absurd (Finset.mem_univ i) h
      set A' : Fin cP.length → ChainChart F := fun i => chartCombination (y i) A with hA'
      set e2 : Fin cP.length → F.Site F.top → Fin 4 → imaginaryQuaternions :=
        fun i => topVariationAlong e (y i) with he2
      have hterm : iteratedFDeriv ℝ cP.length Ψ (τ 0) y = localIteratedDeriv Φ U A' e2 := by
        have h1 : (fun t : Fin cP.length → ℝ => Φ (chartShiftAlong U A' t) (topVariationAlong e2 t)) = Ψ ∘ Lm := by
          funext t
          show Φ (chartShiftAlong U A' t) (topVariationAlong e2 t) =
            Φ (chartShiftAlong U A (Lm t)) (topVariationAlong e (Lm t))
          rw [hLm, chartShiftAlong_sum_smul, topVariationAlong_sum_smul]
        unfold localIteratedDeriv
        rw [h1, iteratedFDeriv_comp_continuousLinearMap Lm (by rw [hLm0]; exact hΨ), hLm0, hτ0]
        congr 1
        funext i
        exact (hLs i).symm
      have parts : ∀ i, ChartEqOnBonds S (A' i) (mixedDerivativeChart T (partEmbedding e' cP i)) ∧
          e2 i = partSpread c X (partEmbedding e' cP i) := by
        intro i
        have hp : 1 ≤ cP.partSize i := cP.partSize_pos i
        obtain ⟨q, hq⟩ : ∃ q, cP.partSize i = q + 1 := ⟨cP.partSize i - 1, by omega⟩
        set w : Fin (cP.partSize i) → (Fin k → ℝ) := v ∘ cP.emb i with hw
        have cQ : ContDiffAt ℝ (cP.partSize i) Q 0 := hQ.contDiffAt.of_le (by exact_mod_cast le_top)
        have cV : ContDiffAt ℝ (cP.partSize i) (fun ζ => toLocal S (T ζ)) 0 :=
          hloc.contDiffAt.of_le (by exact_mod_cast le_top)
        have hyi : y i = Lb (iteratedFDeriv ℝ (cP.partSize i) Q 0 w) := by
          have := Lb.iteratedFDeriv_comp_left cQ (le_refl ((cP.partSize i : ℕ) : WithTop ℕ∞))
          exact congrArg (fun g => g w) this
        have hrecon : ∑ β, y i β • bs β = iteratedFDeriv ℝ (cP.partSize i) Q 0 w := by
          rw [hyi]
          exact bs.sum_equivFun _
        have hfst : (iteratedFDeriv ℝ (cP.partSize i) Q 0 w).1 =
            iteratedFDeriv ℝ (cP.partSize i) (fun ζ => toLocal S (T ζ)) 0 w := by
          have h1 := (ContinuousLinearMap.fst ℝ (LocalChartSpace S) (Fin k → ℝ)).iteratedFDeriv_comp_left cQ
            (le_refl ((cP.partSize i : ℕ) : WithTop ℕ∞))
          have h2 := congrArg (fun g => g w) h1
          have h3 : (ContinuousLinearMap.fst ℝ (LocalChartSpace S) (Fin k → ℝ)) ∘ Q =
              fun ζ => toLocal S (T ζ) + -x₀ := rfl
          rw [h3] at h2
          have h4 : iteratedFDeriv ℝ (cP.partSize i) (fun ζ => toLocal S (T ζ) + -x₀) 0 =
              iteratedFDeriv ℝ (cP.partSize i) (fun ζ => toLocal S (T ζ)) 0 := by
            rw [hq]
            exact iteratedFDeriv_succ_comp_add_const _ _ q 0
          rw [h4] at h2
          exact h2.symm
        have hsnd : (iteratedFDeriv ℝ (cP.partSize i) Q 0 w).2 =
            iteratedFDeriv ℝ (cP.partSize i) (fun ζ : Fin k → ℝ => ζ) 0 w := by
          have h1 := (ContinuousLinearMap.snd ℝ (LocalChartSpace S) (Fin k → ℝ)).iteratedFDeriv_comp_left cQ
            (le_refl ((cP.partSize i : ℕ) : WithTop ℕ∞))
          have h2 := congrArg (fun g => g w) h1
          exact h2.symm
        have hsame1 : ChartEqOnBonds S (A' i)
            (ofLocal (iteratedFDeriv ℝ (cP.partSize i) (fun ζ => toLocal S (T ζ)) 0 w)) := by
          have h1 := chartAgreeOn_combination_ofLocal (S := S) (y i) (fun β => (bs β).1)
          have h2 : ∑ β, y i β • (bs β).1 =
              iteratedFDeriv ℝ (cP.partSize i) (fun ζ => toLocal S (T ζ)) 0 w := by
            rw [← hfst, ← hrecon, Prod.fst_sum]
            rfl
          rw [h2] at h1
          exact h1
        have hsame2 : ChartEqOnBonds S
            (ofLocal (iteratedFDeriv ℝ (cP.partSize i) (fun ζ => toLocal S (T ζ)) 0 w))
            (mixedDerivativeChart T (partEmbedding e' cP i)) := by
          refine ⟨fun b hb => ?_, fun j hj c' hc' => ?_⟩
          · rw [ofLocal_fine _ hb]
            let Pj : LocalChartSpace S →L[ℝ] imaginaryQuaternions :=
              (ContinuousLinearMap.proj (⟨b, hb⟩ : ↥(innerBonds S 0))).comp (ContinuousLinearMap.fst ℝ _ _)
            have h1 := Pj.iteratedFDeriv_comp_left cV (le_refl ((cP.partSize i : ℕ) : WithTop ℕ∞))
            exact (congrArg (fun g => g w) h1).symm
          · have hj' : j < F.depth := by
              simp only [BlockFrame.top] at hj
              omega
            rw [ofLocal_coarse _ hj' hc']
            let P1 : ((j : Fin F.depth) → ↥(innerBonds S (j.1 + 1)) → imaginaryQuaternions) →L[ℝ]
                (↥(innerBonds S (j + 1)) → imaginaryQuaternions) :=
              ContinuousLinearMap.proj (⟨j, hj'⟩ : Fin F.depth)
            let P2 : (↥(innerBonds S (j + 1)) → imaginaryQuaternions) →L[ℝ] imaginaryQuaternions :=
              ContinuousLinearMap.proj ⟨c', hc'⟩
            let Pj : LocalChartSpace S →L[ℝ] imaginaryQuaternions :=
              P2.comp (P1.comp (ContinuousLinearMap.snd ℝ _ _))
            have h1 := Pj.iteratedFDeriv_comp_left cV (le_refl ((cP.partSize i : ℕ) : WithTop ℕ∞))
            exact (congrArg (fun g => g w) h1).symm
        refine ⟨chartAgreeOn_trans hsame1 hsame2, ?_⟩
        have h1 := topVariationAlong_bondSpread c X (fun β => (bs β).2) (y i)
        have h2 : ∑ β, y i β • (bs β).2 = iteratedFDeriv ℝ (cP.partSize i) (fun ζ : Fin k → ℝ => ζ) 0 w := by
          rw [← hsnd, ← hrecon, Prod.snd_sum]
          rfl
        rw [h2] at h1
        exact h1
      refine ⟨A', fun i => (parts i).1, ?_⟩
      have he : e2 = fun i => partSpread c X (partEmbedding e' cP i) := funext fun i => (parts i).2
      rw [← he]
      exact hterm
    choose A₁ hA₁ hE using per
    refine ⟨A₁, hA₁, ?_⟩
    rw [hH, hC m _ _ E Ψ τ 0 hτ hΨτ]
    exact Finset.sum_congr rfl fun cP _ => hE cP
  refine ⟨by rw [hH]; exact hΨτ.comp hτ, hexp, ?_⟩
  intro m e' hm
  obtain ⟨A₁, hA₁, hE⟩ := hexp m e' hm
  rw [hE]
  unfold mixedDerivConstant
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun cP _ => ?_)
  refine (hΦ.iteratedDeriv_le _ (A₁ cP) _).trans ?_
  have slot : ∀ i, localDirectionSize S R B z (A₁ cP i) (partSpread c X (partEmbedding e' cP i)) ≤
      (Dk (cP.partSize i) + M) * Real.exp (-δ * bondListDistance z (c ∘ partEmbedding e' cP i)) := by
    intro i
    have hp : 1 ≤ cP.partSize i := cP.partSize_pos i
    have hnear : localNorm S R (A₁ cP i) (oneSiteWeights F) z ≤
        Dk (cP.partSize i) * Real.exp (-δ * bondListDistance z (c ∘ partEmbedding e' cP i)) := by
      rw [localNorm_congr z (hA₁ cP i)]
      exact hdec _ (partEmbedding e' cP i) hp
    have hturn : topVariationNorm B (partSpread c X (partEmbedding e' cP i)) ≤
        M * Real.exp (-δ * bondListDistance z (c ∘ partEmbedding e' cP i)) :=
      topVariationNorm_part_le B z c X hX δ hδ r₀ hB hp (fun l => partEmbedding e' cP i l)
    unfold localDirectionSize
    rw [add_mul]
    exact add_le_add hnear hturn
  have hsum : (bondListDistance z (c ∘ e') : ℝ) ≤
      ∑ i, (bondListDistance z (c ∘ partEmbedding e' cP i) : ℝ) := by
    have h1 : bondListDistance z (c ∘ e') ≤ ∑ i, bondListDistance z (c ∘ partEmbedding e' cP i) := by
      refine Finset.sup_le fun l _ => ?_
      obtain ⟨i, j, rfl⟩ := cP.cover l
      have h2 : cellSupDist z (c (partEmbedding e' cP i j)).1 ≤
          bondListDistance z (c ∘ partEmbedding e' cP i) :=
        Finset.le_sup (f := fun l' : Fin (cP.partSize i) => cellSupDist z ((c ∘ partEmbedding e' cP i) l').1)
          (Finset.mem_univ j)
      exact h2.trans (Finset.single_le_sum (f := fun i => bondListDistance z (c ∘ partEmbedding e' cP i))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    exact_mod_cast h1
  have hprod : ∏ i, localDirectionSize S R B z (A₁ cP i) (partSpread c X (partEmbedding e' cP i)) ≤
      (∏ i, (Dk (cP.partSize i) + M)) * Real.exp (-δ * bondListDistance z (c ∘ e')) := by
    refine (Finset.prod_le_prod (fun i _ => localDirectionSize_nonneg R B z _ _) (fun i _ => slot i)).trans ?_
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) ?_
    · rw [← Finset.mul_sum]
      nlinarith
    · exact Finset.prod_nonneg fun i _ => add_nonneg (hDk _) hM0
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hprod (hCk _)
end YangMills.Construction.BlockAverages
end
