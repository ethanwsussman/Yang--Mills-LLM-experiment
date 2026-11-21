import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsOfSeveralVariablesProof
import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.DirichletOperator.DerivativeBoundsOfTheFunctionsOfACubeProof
import YangMills.Construction.SourcesAndGluing.LogarithmDerivativesPartitionsCumulantsAndConnectedFunctions
import Mathlib

section
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.SeveralVariableCalculus
variable {n : ℕ}
def PartialsHolomorphicCommute (U : Set (Coordinates.ComplexCoordinates n))
    (F : Coordinates.ComplexCoordinates n → ℂ) : Prop :=
  ∀ i j : Fin n, HolomorphicOnSet U (partialDeriv i F) ∧
    EqOn (partialDeriv i (partialDeriv j F)) (partialDeriv j (partialDeriv i F)) U
def SumProductRules (U : Set (Coordinates.ComplexCoordinates n))
    (F G : Coordinates.ComplexCoordinates n → ℂ) : Prop :=
  HolomorphicOnSet U (fun z => F z + G z) ∧ HolomorphicOnSet U (fun z => F z * G z) ∧
    ∀ i : Fin n,
      EqOn (partialDeriv i fun z => F z + G z)
        (fun z => partialDeriv i F z + partialDeriv i G z) U ∧
      EqOn (partialDeriv i fun z => F z * G z)
        (fun z => partialDeriv i F z * G z + F z * partialDeriv i G z) U
def disjointCovers (k : ℕ) (J : Finset (Fin n)) : Finset (Fin k → Finset (Fin n)) :=
  Finset.univ.filter fun S =>
    (∀ a b : Fin k, a ≠ b → Disjoint (S a) (S b)) ∧ Finset.univ.biUnion S = J
def GeneralLeibniz {k : ℕ} (U : Set (Coordinates.ComplexCoordinates n))
    (G : Fin k → Coordinates.ComplexCoordinates n → ℂ) : Prop :=
  ∀ J : Finset (Fin n),
    EqOn (setPartial J fun z => ∏ a, G a z)
      (fun z => ∑ S ∈ disjointCovers k J, ∏ a, setPartial (S a) (G a) z) U
def ChainRuleScalar (U : Set (Coordinates.ComplexCoordinates n))
    (F : Coordinates.ComplexCoordinates n → ℂ) : Prop :=
  ∀ (V : Set ℂ) (g : ℂ → ℂ), IsOpen V → DifferentiableOn ℂ g V → MapsTo F U V →
    HolomorphicOnSet U (g ∘ F) ∧
      ∀ i : Fin n,
        EqOn (partialDeriv i (g ∘ F)) (fun z => deriv g (F z) * partialDeriv i F z) U
def ChainRuleLinear (U : Set (Coordinates.ComplexCoordinates n))
    (F : Coordinates.ComplexCoordinates n → ℂ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ (A : Coordinates.ComplexCoordinates m →ₗ[ℂ] Coordinates.ComplexCoordinates n)
    (a : Fin n → Fin m → ℂ), (∀ t i, A t i = ∑ l, a i l * t l) →
    IsOpen (A ⁻¹' U) ∧ HolomorphicOnSet (A ⁻¹' U) (F ∘ A) ∧
      ∀ l : Fin m,
        EqOn (partialDeriv l (F ∘ A)) (fun t => ∑ i, a i l * partialDeriv i F (A t)) (A ⁻¹' U)
def CauchyBound (U : Set (Coordinates.ComplexCoordinates n))
    (F : Coordinates.ComplexCoordinates n → ℂ) : Prop :=
  ∀ (a : Coordinates.ComplexCoordinates n) (i : Fin n) (r : ℝ), a ∈ U → 0 < r →
    (∀ w : ℂ, ‖w‖ ≤ r → a + w • coordVector i ∈ U) →
    ∃ M : ℝ,
      IsGreatest ((fun w : ℂ => ‖F (a + w • coordVector i)‖) '' Metric.sphere 0 r) M ∧
        ‖partialDeriv i F a‖ ≤ r⁻¹ * M
def Claim : Prop :=
  ∀ (n k : ℕ), 1 ≤ n → ∀ hk : 1 ≤ k, ∀ U : Set (Coordinates.ComplexCoordinates n), IsOpen U →
    ∀ (F : Coordinates.ComplexCoordinates n → ℂ) (G : Fin k → Coordinates.ComplexCoordinates n → ℂ),
      HolomorphicOnSet U F → (∀ a, HolomorphicOnSet U (G a)) →
      PartialsHolomorphicCommute U F ∧
        SumProductRules U F (G ⟨0, hk⟩) ∧
        GeneralLeibniz U G ∧
        ChainRuleScalar U F ∧
        ChainRuleLinear U F ∧
        CauchyBound U F
end YangMills.Construction.SourcesAndGluing.SeveralVariableCalculus
end
end

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.SeveralVariableCalculus
variable {n : ℕ}
private def singleCoord : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
private theorem singleCoord_funUnique_symm (w : ℂ) :
    singleCoord ((Equiv.funUnique (Fin 1) ℂ).symm w) = w := by
  simp [singleCoord]
private theorem differentiableOn_and_contDiffOn_of_holomorphicOnSet
    (h : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {U : Set (Coordinates.ComplexCoordinates n)} (hU : IsOpen U)
    {F : Coordinates.ComplexCoordinates n → ℂ}
    (hF : HolomorphicOnSet U F) : DifferentiableOn ℂ F U ∧ ContDiffOn ℝ ∞ F U := by
  have hc := (holomorphicOnSet_iff_complexCoordinates U F).1 hF
  obtain ⟨-, hs, hd, -, -⟩ := (h.1 n U hU).1 1 _ hc
  have hback : (singleCoord.restrictScalars ℝ) ∘ ((Equiv.funUnique (Fin 1) ℂ).symm ∘ F) = F := by
    funext z
    exact singleCoord_funUnique_symm (F z)
  constructor
  · intro z hz
    obtain ⟨L, hL⟩ := hd z hz
    have h1 := (singleCoord.restrictScalars ℝ).hasFDerivAt.comp z hL
    rw [hback] at h1
    exact (hasFDerivAt_of_restrictScalars ℝ (f' := singleCoord.comp L) h1
      (by ext; rfl)).differentiableAt.differentiableWithinAt
  · have h1 := (singleCoord.restrictScalars ℝ).contDiff.comp_contDiffOn hs
    rwa [hback] at h1
private theorem hasDerivAt_affineLine (a c : Coordinates.ComplexCoordinates n) (ζ : ℂ) :
    HasDerivAt (fun ζ : ℂ => a + ζ • c) c ζ := by
  simpa using ((hasDerivAt_id ζ).smul_const c).const_add a
private theorem holomorphicOnSet_of_differentiableOn {U : Set (Coordinates.ComplexCoordinates n)}
    (hU : IsOpen U) {F : Coordinates.ComplexCoordinates n → ℂ} (hF : DifferentiableOn ℂ F U) :
    HolomorphicOnSet U F := by
  rw [holomorphicOnSet_iff_complexCoordinates]
  have hcl : ∀ z ∈ U, DifferentiableAt ℂ ((Equiv.funUnique (Fin 1) ℂ).symm ∘ F) z := by
    intro z hz
    have hz' := (hF z hz).differentiableAt (hU.mem_nhds hz)
    refine differentiableAt_pi.2 fun j => ?_
    simpa using hz'
  refine ⟨hU, fun z hz => (hcl z hz).continuousAt.continuousWithinAt, ?_⟩
  intro a ha j
  have hline : ContinuousAt
      (fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) 0 :=
    (hasDerivAt_affineLine a _ 0).continuousAt
  have hev : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j ∈ U :=
    hline.eventually (hU.mem_nhds (by simpa using ha))
  filter_upwards [hev] with ζ hζ
  exact DifferentiableAt.comp
    (f := fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) ζ
    (hcl _ hζ) (hasDerivAt_affineLine a _ ζ).differentiableAt
private theorem hasDerivAt_partialDeriv {F : Coordinates.ComplexCoordinates n → ℂ}
    {a : Coordinates.ComplexCoordinates n} (hF : DifferentiableAt ℂ F a) (i : Fin n) :
    HasDerivAt (fun ζ : ℂ => F (a + ζ • coordVector i)) (partialDeriv i F a) 0 := by
  have h1 : HasDerivAt (fun ζ : ℂ => F (a + ζ • coordVector i))
      (fderiv ℂ F a (coordVector i)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hF.hasFDerivAt (hasDerivAt_affineLine a _ 0) (by simp)
  have h2 : partialDeriv i F a = fderiv ℂ F a (coordVector i) := h1.deriv
  rw [h2]
  exact h1
private theorem partialDeriv_eq_fderiv {F : Coordinates.ComplexCoordinates n → ℂ}
    {a : Coordinates.ComplexCoordinates n} (hF : DifferentiableAt ℂ F a) (i : Fin n) :
    partialDeriv i F a = fderiv ℂ F a (coordVector i) := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.partialDeriv_eq_fderiv <;> assumption
private theorem exists_clm_restrictScalars_eq (D : Coordinates.ComplexCoordinates n →L[ℝ] ℂ)
    (hI : ∀ v, D (Complex.I • v) = Complex.I * D v) :
    ∃ L : Coordinates.ComplexCoordinates n →L[ℂ] ℂ, L.restrictScalars ℝ = D := by
  refine ⟨⟨{ toFun := D, map_add' := D.map_add, map_smul' := ?_ }, D.continuous⟩, ?_⟩
  · intro c v
    have hc : c • v = c.re • v + c.im • (Complex.I • v) := by
      funext j
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
      nth_rewrite 1 [← Complex.re_add_im c]
      ring
    simp only [RingHom.id_apply]
    rw [hc, D.map_add, D.map_smul, D.map_smul, hI, smul_eq_mul, Complex.real_smul,
      Complex.real_smul]
    nth_rewrite 3 [← Complex.re_add_im c]
    ring
  · ext v
    rfl
private theorem two_le_top_withTop : (2 : WithTop ℕ∞) ≤ ∞ := by apply _root_.YangMills.Construction.PartitionCubes.CubeFunctionDerivBounds.two_le_infty <;> assumption
private theorem exists_hasFDerivAt_partialDeriv {U : Set (Coordinates.ComplexCoordinates n)}
    (hU : IsOpen U) {F : Coordinates.ComplexCoordinates n → ℂ} (hd : DifferentiableOn ℂ F U)
    (hs : ContDiffOn ℝ ∞ F U) (i : Fin n) {a : Coordinates.ComplexCoordinates n} (ha : a ∈ U) :
    ∃ L : Coordinates.ComplexCoordinates n →L[ℂ] ℂ, HasFDerivAt (partialDeriv i F) L a ∧
      ∀ c, L c = fderiv ℝ (fderiv ℝ F) a c (coordVector i) := by
  have hsa : ContDiffAt ℝ ∞ F a := hs.contDiffAt (hU.mem_nhds ha)
  have hGd : DifferentiableAt ℝ (fderiv ℝ F) a :=
    (hsa.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hsym : IsSymmSndFDerivAt ℝ F a := hsa.isSymmSndFDerivAt (by simpa using two_le_top_withTop)
  have hR : ∀ z ∈ U, ∀ v, fderiv ℝ F z v = fderiv ℂ F z v := by
    intro z hz v
    have hz' := ((hd z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt.restrictScalars ℝ
    rw [hz'.fderiv]
    rfl
  set D := fderiv ℝ (fderiv ℝ F) a with hD
  have happ : ∀ w, HasFDerivAt (fun z => fderiv ℝ F z w)
      ((ContinuousLinearMap.apply ℝ ℂ w).comp D) a := fun w =>
    (ContinuousLinearMap.apply ℝ ℂ w).hasFDerivAt.comp a hGd.hasFDerivAt
  have hI : ∀ v w, D w (Complex.I • v) = Complex.I * D w v := by
    intro v w
    have h1 := happ (Complex.I • v)
    have h2 : HasFDerivAt (fun z => fderiv ℝ F z (Complex.I • v))
        (Complex.I • (ContinuousLinearMap.apply ℝ ℂ v).comp D) a := by
      refine ((happ v).const_mul Complex.I).congr_of_eventuallyEq ?_
      filter_upwards [hU.mem_nhds ha] with z hz
      rw [hR z hz, hR z hz, map_smul, smul_eq_mul]
    have h3 := congrArg (fun T : Coordinates.ComplexCoordinates n →L[ℝ] ℂ => T w) (h1.unique h2)
    simpa using h3
  obtain ⟨L, hL⟩ := exists_clm_restrictScalars_eq ((ContinuousLinearMap.apply ℝ ℂ
    (coordVector i)).comp D) (by
      intro v
      have h1 : D (Complex.I • v) (coordVector i) = Complex.I * D v (coordVector i) := by
        rw [hsym.eq, hI, hsym.eq]
      simpa using h1)
  refine ⟨L, ?_, ?_⟩
  · have h1 := happ (coordVector i)
    rw [← hL] at h1
    refine (hasFDerivAt_of_restrictScalars ℝ h1 rfl).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds ha] with z hz
    rw [hR z hz]
    exact partialDeriv_eq_fderiv ((hd z hz).differentiableAt (hU.mem_nhds hz)) i
  · intro c
    have := congrArg (fun T : Coordinates.ComplexCoordinates n →L[ℝ] ℂ => T c) hL
    simpa using this
private theorem holomorphicOnSet_partialDeriv
    (h : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {U : Set (Coordinates.ComplexCoordinates n)} (hU : IsOpen U)
    {F : Coordinates.ComplexCoordinates n → ℂ}
    (hF : HolomorphicOnSet U F) (i : Fin n) : HolomorphicOnSet U (partialDeriv i F) := by
  obtain ⟨hd, hs⟩ := differentiableOn_and_contDiffOn_of_holomorphicOnSet h hU hF
  refine holomorphicOnSet_of_differentiableOn hU fun a ha => ?_
  obtain ⟨L, hL, -⟩ := exists_hasFDerivAt_partialDeriv hU hd hs i ha
  exact hL.differentiableAt.differentiableWithinAt
private theorem partialDeriv_comm
    (h : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {U : Set (Coordinates.ComplexCoordinates n)} (hU : IsOpen U)
    {F : Coordinates.ComplexCoordinates n → ℂ}
    (hF : HolomorphicOnSet U F) (i i' : Fin n) :
    EqOn (partialDeriv i (partialDeriv i' F)) (partialDeriv i' (partialDeriv i F)) U := by
  obtain ⟨hd, hs⟩ := differentiableOn_and_contDiffOn_of_holomorphicOnSet h hU hF
  intro a ha
  obtain ⟨L, hL, hLc⟩ := exists_hasFDerivAt_partialDeriv hU hd hs i ha
  obtain ⟨L', hL', hLc'⟩ := exists_hasFDerivAt_partialDeriv hU hd hs i' ha
  have hsym : IsSymmSndFDerivAt ℝ F a :=
    (hs.contDiffAt (hU.mem_nhds ha)).isSymmSndFDerivAt (by simpa using two_le_top_withTop)
  rw [partialDeriv_eq_fderiv hL'.differentiableAt, partialDeriv_eq_fderiv hL.differentiableAt,
    hL.fderiv, hL'.fderiv, hLc, hLc', hsym.eq]
private theorem partialDeriv_congr {U : Set (Coordinates.ComplexCoordinates n)} (hU : IsOpen U)
    {f g : Coordinates.ComplexCoordinates n → ℂ} (hfg : EqOn f g U) (i : Fin n) :
    EqOn (partialDeriv i f) (partialDeriv i g) U := by apply _root_.YangMills.Construction.SeveralComplexVariables.coordDeriv_eqOn_of_eqOn <;> assumption
abbrev _root_.YangMills.SharedProofs.p36449 := @partialDeriv_congr
private theorem holomorphicOnSet_iteratedPartials
    (h : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {U : Set (Coordinates.ComplexCoordinates n)} (hU : IsOpen U)
    {F : Coordinates.ComplexCoordinates n → ℂ}
    (hF : HolomorphicOnSet U F) (l : List (Fin n)) : HolomorphicOnSet U (iteratedPartials l F) := by
  induction l with
  | nil => exact hF
  | cons i l ih => exact holomorphicOnSet_partialDeriv h hU ih i
private theorem setPartial_insert_of_lt {i : Fin n} {J : Finset (Fin n)} (hi : ∀ x ∈ J, i < x)
    (F : Coordinates.ComplexCoordinates n → ℂ) :
    setPartial (insert i J) F = partialDeriv i (setPartial J F) := by
  have hn : i ∉ J := fun hm => lt_irrefl _ (hi i hm)
  simp only [setPartial]
  rw [Finset.sort_insert (fun a b => a ≤ b) (fun b hb => (hi b hb).le) hn]
  rfl
private theorem mem_disjointCovers {k : ℕ} {J : Finset (Fin n)} {S : Fin k → Finset (Fin n)} :
    S ∈ disjointCovers k J ↔
      (∀ l l' : Fin k, l ≠ l' → Disjoint (S l) (S l')) ∧ Finset.univ.biUnion S = J := by
  simp [disjointCovers]
private theorem subset_of_mem_disjointCovers {k : ℕ} {J : Finset (Fin n)}
    {S : Fin k → Finset (Fin n)} (hS : S ∈ disjointCovers k J) (l : Fin k) : S l ⊆ J := by
  rw [← (mem_disjointCovers.1 hS).2]
  exact Finset.subset_biUnion_of_mem S (Finset.mem_univ l)
private theorem disjointCovers_empty (k : ℕ) :
    disjointCovers (n := n) k ∅ = {fun _ => ∅} := by
  ext S
  rw [Finset.mem_singleton]
  constructor
  · intro hS
    funext l
    exact Finset.subset_empty.1 (subset_of_mem_disjointCovers hS l)
  · rintro rfl
    refine mem_disjointCovers.2 ⟨fun _ _ _ => by simp, ?_⟩
    ext x
    simp
private theorem sum_disjointCovers_insert {k : ℕ} {J : Finset (Fin n)} {i : Fin n} (hi : i ∉ J)
    (t : (Fin k → Finset (Fin n)) → ℂ) :
    ∑ S ∈ disjointCovers k (insert i J), t S =
      ∑ S ∈ disjointCovers k J, ∑ l : Fin k, t (Function.update S l (insert i (S l))) := by
  have hnot : ∀ S ∈ disjointCovers k J, ∀ l, i ∉ S l := fun S hS l hm =>
    hi (subset_of_mem_disjointCovers hS l hm)
  rw [← Finset.sum_product' (f := fun S l => t (Function.update S l (insert i (S l))))]
  symm
  refine Finset.sum_bij (fun p _ => Function.update p.1 p.2 (insert i (p.1 p.2))) ?_ ?_ ?_ ?_
  · rintro ⟨S, l⟩ hp
    have hS : S ∈ disjointCovers k J := (Finset.mem_product.1 hp).1
    obtain ⟨hdis, hun⟩ := mem_disjointCovers.1 hS
    refine mem_disjointCovers.2 ⟨?_, ?_⟩
    · intro m m' hne
      by_cases hm : m = l
      · subst hm
        have hm' : m' ≠ m := fun e => hne e.symm
        simp only [Function.update_self, Function.update_of_ne hm']
        exact Finset.disjoint_insert_left.2 ⟨hnot S hS m', hdis m m' hne⟩
      · by_cases hm' : m' = l
        · subst hm'
          simp only [Function.update_self, Function.update_of_ne hm]
          exact Finset.disjoint_insert_right.2 ⟨hnot S hS m, hdis m m' hne⟩
        · simp only [Function.update_of_ne hm, Function.update_of_ne hm']
          exact hdis m m' hne
    · ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨m, hx⟩
        by_cases hm : m = l
        · subst hm
          rw [Function.update_self, Finset.mem_insert] at hx
          exact hx.imp_right fun hx => subset_of_mem_disjointCovers hS m hx
        · rw [Function.update_of_ne hm] at hx
          exact Or.inr (subset_of_mem_disjointCovers hS m hx)
      · rintro (rfl | hx)
        · exact ⟨l, by simp⟩
        · rw [← hun, Finset.mem_biUnion] at hx
          obtain ⟨m, -, hx⟩ := hx
          refine ⟨m, ?_⟩
          by_cases hm : m = l
          · subst hm
            simp [hx]
          · rwa [Function.update_of_ne hm]
  · rintro ⟨S, l⟩ hp ⟨S', l'⟩ hp' he
    have hS : S ∈ disjointCovers k J := (Finset.mem_product.1 hp).1
    have hS' : S' ∈ disjointCovers k J := (Finset.mem_product.1 hp').1
    simp only at he
    have hl : l = l' := by
      by_contra hne
      have h1 := congrFun he l
      rw [Function.update_self, Function.update_of_ne hne] at h1
      exact hnot S' hS' l (h1 ▸ Finset.mem_insert_self i (S l))
    subst hl
    have hSS : S = S' := by
      funext m
      by_cases hm : m = l
      · subst hm
        have h1 := congrFun he m
        rw [Function.update_self, Function.update_self] at h1
        have h2 := congrArg (fun T => Finset.erase T i) h1
        simpa [Finset.erase_insert (hnot S hS m), Finset.erase_insert (hnot S' hS' m)] using h2
      · have h1 := congrFun he m
        rwa [Function.update_of_ne hm, Function.update_of_ne hm] at h1
    rw [hSS]
  · intro S' hS'
    obtain ⟨hdis, hun⟩ := mem_disjointCovers.1 hS'
    have hmem : i ∈ Finset.univ.biUnion S' := by
      rw [hun]
      exact Finset.mem_insert_self i J
    obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.1 hmem
    have hother : ∀ m, m ≠ l → i ∉ S' m := fun m hm hx =>
      Finset.disjoint_left.1 (hdis m l hm) hx hl
    refine ⟨(Function.update S' l ((S' l).erase i), l), ?_, ?_⟩
    · refine Finset.mem_product.2 ⟨mem_disjointCovers.2 ⟨?_, ?_⟩, Finset.mem_univ l⟩
      · intro m m' hne
        by_cases hm : m = l
        · subst hm
          have hm' : m' ≠ m := fun e => hne e.symm
          simp only [Function.update_self, Function.update_of_ne hm']
          exact (hdis m m' hne).mono_left (Finset.erase_subset _ _)
        · by_cases hm' : m' = l
          · subst hm'
            simp only [Function.update_self, Function.update_of_ne hm]
            exact (hdis m m' hne).mono_right (Finset.erase_subset _ _)
          · simp only [Function.update_of_ne hm, Function.update_of_ne hm']
            exact hdis m m' hne
      · ext x
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨m, hx⟩
          have hx' : x ∈ S' m ∧ x ≠ i := by
            by_cases hm : m = l
            · subst hm
              rw [Function.update_self, Finset.mem_erase] at hx
              exact ⟨hx.2, hx.1⟩
            · rw [Function.update_of_ne hm] at hx
              exact ⟨hx, fun e => hother m hm (e ▸ hx)⟩
          have hxi : x ∈ insert i J := by
            rw [← hun]
            exact Finset.mem_biUnion.2 ⟨m, Finset.mem_univ m, hx'.1⟩
          exact (Finset.mem_insert.1 hxi).resolve_left hx'.2
        · intro hx
          have hxi : x ∈ Finset.univ.biUnion S' := by
            rw [hun]
            exact Finset.mem_insert_of_mem hx
          obtain ⟨m, -, hxm⟩ := Finset.mem_biUnion.1 hxi
          have hne : x ≠ i := fun e => hi (e ▸ hx)
          refine ⟨m, ?_⟩
          by_cases hm : m = l
          · subst hm
            rw [Function.update_self]
            exact Finset.mem_erase.2 ⟨hne, hxm⟩
          · rwa [Function.update_of_ne hm]
    · funext m
      by_cases hm : m = l
      · subst hm
        simp [Finset.insert_erase hl]
      · simp [Function.update_of_ne hm]
  · intro p _
    rfl
private theorem generalLeibniz_holds
    (h : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {U : Set (Coordinates.ComplexCoordinates n)} (hU : IsOpen U) {k : ℕ}
    {Fs : Fin k → Coordinates.ComplexCoordinates n → ℂ}
    (hFs : ∀ l, HolomorphicOnSet U (Fs l)) : GeneralLeibniz U Fs := by
  intro J
  induction J using Finset.induction_on_min with
  | empty =>
    intro z _
    simp [disjointCovers_empty, setPartial_empty]
  | insert i J hi ih =>
    have hiJ : i ∉ J := fun hm => lt_irrefl _ (hi i hm)
    intro a ha
    have hT : ∀ (S : Finset (Fin n)) (l : Fin k),
        DifferentiableAt ℂ (setPartial S (Fs l)) a := fun S l =>
      ((differentiableOn_and_contDiffOn_of_holomorphicOnSet h hU
        (F := setPartial S (Fs l))
        (holomorphicOnSet_iteratedPartials h hU (hFs l) _)).1 a ha).differentiableAt
        (hU.mem_nhds ha)
    have hline : HasDerivAt
        (fun ζ : ℂ => ∑ S ∈ disjointCovers k J, ∏ l,
          setPartial (S l) (Fs l) (a + ζ • coordVector i))
        (∑ S ∈ disjointCovers k J, ∑ l₀ : Fin k,
          (∏ l ∈ Finset.univ.erase l₀,
            setPartial (S l) (Fs l) (a + (0 : ℂ) • coordVector i)) •
          partialDeriv i (setPartial (S l₀) (Fs l₀)) a) 0 :=
      HasDerivAt.fun_sum fun S _ =>
        HasDerivAt.fun_finsetProd fun l _ => hasDerivAt_partialDeriv (hT (S l) l) i
    rw [setPartial_insert_of_lt hi, partialDeriv_congr hU ih i ha]
    change partialDeriv i _ a =
      ∑ S ∈ disjointCovers k (insert i J), ∏ l, setPartial (S l) (Fs l) a
    rw [sum_disjointCovers_insert hiJ]
    refine hline.deriv.trans (Finset.sum_congr rfl fun S hS => Finset.sum_congr rfl fun l₀ _ => ?_)
    have hmin : ∀ x ∈ S l₀, i < x := fun x hx => hi x (subset_of_mem_disjointCovers hS l₀ hx)
    rw [← setPartial_insert_of_lt hmin, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l₀),
      Function.update_self, smul_eq_mul, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl), zero_smul, add_zero]
private theorem sumProductRules_holds {U : Set (Coordinates.ComplexCoordinates n)} (hU : IsOpen U)
    {F G : Coordinates.ComplexCoordinates n → ℂ} (hF : DifferentiableOn ℂ F U)
    (hG : DifferentiableOn ℂ G U) :
    SumProductRules U F G := by
  refine ⟨holomorphicOnSet_of_differentiableOn hU (hF.fun_add hG),
    holomorphicOnSet_of_differentiableOn hU (hF.fun_mul hG), fun i => ⟨?_, ?_⟩⟩
  · intro a ha
    have h1 := hasDerivAt_partialDeriv ((hF a ha).differentiableAt (hU.mem_nhds ha)) i
    have h2 := hasDerivAt_partialDeriv ((hG a ha).differentiableAt (hU.mem_nhds ha)) i
    exact (h1.fun_add h2).deriv
  · intro a ha
    have h1 := hasDerivAt_partialDeriv ((hF a ha).differentiableAt (hU.mem_nhds ha)) i
    have h2 := hasDerivAt_partialDeriv ((hG a ha).differentiableAt (hU.mem_nhds ha)) i
    have h3 := (h1.fun_mul h2).deriv
    simp only [zero_smul, add_zero] at h3
    exact h3
private theorem chainRuleScalar_holds {U : Set (Coordinates.ComplexCoordinates n)} (hU : IsOpen U)
    {F : Coordinates.ComplexCoordinates n → ℂ} (hF : DifferentiableOn ℂ F U) :
    ChainRuleScalar U F := by
  intro V φ hV hφ hmap
  have hφ' : ∀ a ∈ U, HasDerivAt φ (deriv φ (F a)) (F a) := fun a ha =>
    ((hφ (F a) (hmap ha)).differentiableAt (hV.mem_nhds (hmap ha))).hasDerivAt
  have hF' : ∀ a ∈ U, DifferentiableAt ℂ F a := fun a ha =>
    (hF a ha).differentiableAt (hU.mem_nhds ha)
  have hc : ∀ a ∈ U, HasFDerivAt (φ ∘ F) (deriv φ (F a) • fderiv ℂ F a) a := fun a ha =>
    (hφ' a ha).comp_hasFDerivAt a (hF' a ha).hasFDerivAt
  refine ⟨holomorphicOnSet_of_differentiableOn hU fun a ha =>
    (hc a ha).differentiableAt.differentiableWithinAt, fun i a ha => ?_⟩
  change partialDeriv i (φ ∘ F) a = deriv φ (F a) * partialDeriv i F a
  rw [partialDeriv_eq_fderiv (hc a ha).differentiableAt, (hc a ha).fderiv,
    partialDeriv_eq_fderiv (hF' a ha)]
  simp
private theorem chainRuleLinear_holds {U : Set (Coordinates.ComplexCoordinates n)} (hU : IsOpen U)
    {F : Coordinates.ComplexCoordinates n → ℂ} (hF : DifferentiableOn ℂ F U) :
    ChainRuleLinear U F := by
  intro n' _ A a hA
  have hAc : Continuous A := A.continuous_of_finiteDimensional
  have hopen : IsOpen (A ⁻¹' U) := hU.preimage hAc
  have hF' : ∀ t ∈ A ⁻¹' U, DifferentiableAt ℂ F (A t) := fun t ht =>
    (hF (A t) ht).differentiableAt (hU.mem_nhds ht)
  let Ac : Coordinates.ComplexCoordinates n' →L[ℂ] Coordinates.ComplexCoordinates n := ⟨A, hAc⟩
  have hc : ∀ t ∈ A ⁻¹' U, HasFDerivAt (F ∘ A) ((fderiv ℂ F (A t)).comp Ac) t := fun t ht =>
    (hF' t ht).hasFDerivAt.comp t Ac.hasFDerivAt
  refine ⟨hopen, holomorphicOnSet_of_differentiableOn hopen fun t ht =>
    (hc t ht).differentiableAt.differentiableWithinAt, fun l t ht => ?_⟩
  have hbasis : A (coordVector l) = ∑ i, a i l • coordVector i := by
    funext j
    rw [hA]
    simp [coordVector, Finset.sum_apply, Pi.single_apply]
  rw [partialDeriv_eq_fderiv (hc t ht).differentiableAt, (hc t ht).fderiv]
  change fderiv ℂ F (A t) (A (coordVector l)) = ∑ i, a i l * partialDeriv i F (A t)
  rw [hbasis, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, partialDeriv_eq_fderiv (hF' t ht)]
private theorem cauchyBound_holds {U : Set (Coordinates.ComplexCoordinates n)} (hU : IsOpen U)
    {F : Coordinates.ComplexCoordinates n → ℂ} (hF : DifferentiableOn ℂ F U) : CauchyBound U F := by
  intro a i ϱ _ hϱ hin
  have hg : ∀ ζ : ℂ, ‖ζ‖ ≤ ϱ →
      DifferentiableAt ℂ (fun ζ : ℂ => F (a + ζ • coordVector i)) ζ := fun ζ hζ =>
    (((hF _ (hin ζ hζ)).differentiableAt (hU.mem_nhds (hin ζ hζ))).hasFDerivAt.comp_hasDerivAt
      ζ (hasDerivAt_affineLine a _ ζ)).differentiableAt
  have hcont : ContinuousOn (fun ζ : ℂ => ‖F (a + ζ • coordVector i)‖)
      (Metric.sphere (0 : ℂ) ϱ) := fun ζ hζ =>
    (hg ζ (by simpa using hζ.le)).continuousAt.norm.continuousWithinAt
  obtain ⟨ζ₀, hζ₀, hmax⟩ := (isCompact_sphere (0 : ℂ) ϱ).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 hϱ.le) hcont
  refine ⟨‖F (a + ζ₀ • coordVector i)‖, ⟨⟨ζ₀, hζ₀, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨ζ, hζ, rfl⟩
    exact hmax hζ
  · have hdc : DiffContOnCl ℂ (fun ζ : ℂ => F (a + ζ • coordVector i))
        (Metric.ball (0 : ℂ) ϱ) := by
      refine DifferentiableOn.diffContOnCl fun ζ hζ => ?_
      rw [closure_ball (0 : ℂ) hϱ.ne'] at hζ
      exact (hg ζ (by simpa using hζ)).differentiableWithinAt
    have h1 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hϱ hdc
      (C := ‖F (a + ζ₀ • coordVector i)‖) fun ζ hζ => hmax hζ
    rw [div_eq_inv_mul] at h1
    exact h1
theorem claim_of_powerSeriesHolomorphy
    (h : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    Claim := by
  intro n k _ hk U hU F Fs hF hFs
  have hd := (differentiableOn_and_contDiffOn_of_holomorphicOnSet h hU hF).1
  have hd0 := (differentiableOn_and_contDiffOn_of_holomorphicOnSet h hU (hFs ⟨0, hk⟩)).1
  exact ⟨fun i i' => ⟨holomorphicOnSet_partialDeriv h hU hF i, partialDeriv_comm h hU hF i i'⟩,
    sumProductRules_holds hU hd hd0, generalLeibniz_holds h hU hFs, chainRuleScalar_holds hU hd,
    chainRuleLinear_holds hU hd, cauchyBound_holds hU hd⟩
end YangMills.Construction.SourcesAndGluing.SeveralVariableCalculus
