import YangMills.Construction.Matrices.FactsOnFunctionsAndOperatorsOfSeveralVariablesOnG
import YangMills.Construction.TransferOperators.ComponentFunctionsOfTheProjections
import YangMills.Construction.TransferOperators.FactsOfTheSquareRootOfTheBondKernel
import YangMills.Construction.TransferOperators.PolynomialThroughTheBondKernelAtSmoothFunctions
import YangMills.Construction.TransferOperators.SeriesOfTheOperatorHatConverges
import YangMills.Construction.TransferOperators.SymmetryBoundsAndInvarianceOfTheBondKernelAndTheLayerEnergyProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter YangMills.Construction.Matrices.ComplexMatrix2 YangMills.Construction.TransferOperators
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.SpinHarmonics.LinkKernelPolynomial
section Kernel
variable {K : Type} [Finite K]
theorem integrable_haarPi_of_continuous {g : (K → specialUnitary) → ℂ} (hg : Continuous g) :
    Integrable g (haarPi K) :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
theorem continuous_linkProductKernel (β : ℝ) (hser : SqrtLinkFacts.KernelExpansions β K) :
    Continuous fun p : (K → specialUnitary) × (K → specialUnitary) => linkProductKernel β p.1 p.2 :=
  hser.2.2.2.continuous (Frequently.of_forall fun _ =>
    continuous_finsetSum _ fun l _ => continuous_const.mul (continuous_isotypicKernel l))
theorem continuous_linkProductKernel_left (β : ℝ)
    (hser : SqrtLinkFacts.KernelExpansions β K) (w : K → specialUnitary) :
    Continuous fun v : K → specialUnitary => linkProductKernel β v w :=
  Continuous.comp (g := fun p : (K → specialUnitary) × (K → specialUnitary) => linkProductKernel β p.1 p.2)
    (f := fun v : K → specialUnitary => (v, w)) (continuous_linkProductKernel β hser)
    (continuous_id.prodMk continuous_const)
theorem hasSum_integral_linkProductKernel_mul (β : ℝ)
    (hser : SqrtLinkFacts.KernelExpansions β K)
    (hsym : ∀ (l : K → HalfNatural) (u u' : K → specialUnitary),
      isotypicKernel l u u' = isotypicKernel l u' u)
    (hcomp : ∀ (l : K → HalfNatural) (H : C(K → specialUnitary, ℂ)) (u : K → specialUnitary),
      isotypicPartSum l (toHaarL2 (H : (K → specialUnitary) → ℂ)) u =
        ∫ u', isotypicKernel l u u' * H u' ∂haarPi K)
    (Φ : C(K → specialUnitary, ℂ)) (w : K → specialUnitary) :
    HasSum (fun l : K → HalfNatural => charCoeffProd β l *
        isotypicPartSum l (toHaarL2 (Φ : (K → specialUnitary) → ℂ)) w)
      (∫ v, linkProductKernel β v w * Φ v ∂haarPi K) := by
  have hslice : Continuous fun v : K → specialUnitary => (v, w) := continuous_id.prodMk continuous_const
  have hsec : ∀ A : (K → specialUnitary) × (K → specialUnitary) → ℂ, Continuous A →
      Integrable (fun v => A (v, w) * Φ v) (haarPi K) := fun A hA =>
    integrable_haarPi_of_continuous ((hA.comp hslice).mul Φ.continuous)
  have hcs : ∀ s : Finset (K → HalfNatural), Continuous fun p : (K → specialUnitary) × (K → specialUnitary) =>
      ∑ l ∈ s, charCoeffProd β l * isotypicKernel l p.1 p.2 := fun s =>
    continuous_finsetSum _ fun l _ => continuous_const.mul (continuous_isotypicKernel l)
  have key : ∀ s : Finset (K → HalfNatural),
      ∑ l ∈ s, charCoeffProd β l * isotypicPartSum l (toHaarL2 (Φ : (K → specialUnitary) → ℂ)) w =
        ∫ v, (∑ l ∈ s, charCoeffProd β l * isotypicKernel l v w) * Φ v ∂haarPi K := by
    intro s
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [hcomp, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp only [hsym l w v, mul_assoc]
    · intro l _
      exact hsec (fun p => charCoeffProd β l * isotypicKernel l p.1 p.2)
        (continuous_const.mul (continuous_isotypicKernel l))
  have hu := hser.2.2.2
  change Tendsto _ (SummationFilter.unconditional _).filter _
  rw [SummationFilter.unconditional_filter, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hu (ε / (2 * (‖Φ‖ + 1))) (by positivity)] with s hs
  rw [key s, dist_comm, dist_eq_norm,
    ← integral_sub (hsec _ (continuous_linkProductKernel β hser)) (hsec _ (hcs s))]
  have hb : ∀ v, ‖linkProductKernel β v w * Φ v -
      (∑ l ∈ s, charCoeffProd β l * isotypicKernel l v w) * Φ v‖ ≤
        ε / (2 * (‖Φ‖ + 1)) * (‖Φ‖ + 1) := by
    intro v
    rw [← sub_mul, norm_mul]
    have h₁ : ‖linkProductKernel β v w - ∑ l ∈ s, charCoeffProd β l * isotypicKernel l v w‖ ≤
        ε / (2 * (‖Φ‖ + 1)) := by
      have := hs (v, w)
      rw [dist_eq_norm] at this
      exact this.le
    have h₂ : ‖Φ v‖ ≤ ‖Φ‖ + 1 := (Φ.norm_coe_le_norm v).trans (by linarith)
    exact mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
  have hint := norm_integral_le_of_norm_le_const (μ := haarPi K)
    (Eventually.of_forall hb)
  have hval : ε / (2 * (‖Φ‖ + 1)) * (‖Φ‖ + 1) = ε / 2 := by
    field_simp
  simp only [probReal_univ, mul_one] at hint
  rw [hval] at hint
  linarith
theorem hasSum_isotypicPartSum_apply (hcomp : ∀ (l : K → HalfNatural) (H : C(K → specialUnitary, ℂ)) (u : K → specialUnitary),
      isotypicPartSum l (toHaarL2 (H : (K → specialUnitary) → ℂ)) u =
        ∫ u', isotypicKernel l u u' * H u' ∂haarPi K)
    (hfix : ∀ (l l' : K → HalfNatural) (ψ : C(K → specialUnitary, ℂ)), ψ ∈ prodCoeffSpan l →
      isotypicPartSum l (toHaarL2 (ψ : (K → specialUnitary) → ℂ)) = ψ ∧
      (l' ≠ l → isotypicPartSum l' (toHaarL2 (ψ : (K → specialUnitary) → ℂ)) = 0))
    {ϰ : HalfNatural} {H : C(K → specialUnitary, ℂ)} (hH : H ∈ truncatedCoeffSpan K ϰ) (u : K → specialUnitary) :
    HasSum (fun l : K → HalfNatural => isotypicPartSum l (toHaarL2 (H : (K → specialUnitary) → ℂ)) u)
      (H u) := by
  have hint : ∀ (l : K → HalfNatural) (G : C(K → specialUnitary, ℂ)) (x : K → specialUnitary),
      Integrable (fun x' => isotypicKernel l x x' * G x') (haarPi K) := fun l G x =>
    integrable_haarPi_of_continuous
      (((continuous_isotypicKernel l).comp (continuous_const.prodMk continuous_id)).mul
        G.continuous)
  let S : Submodule ℂ C(K → specialUnitary, ℂ) :=
    { carrier := {G | ∀ x, HasSum (fun l : K → HalfNatural =>
        ∫ x', isotypicKernel l x x' * G x' ∂haarPi K) (G x)}
      add_mem' := by
        intro a b ha hb x
        have e : ∀ l : K → HalfNatural, ∫ x', isotypicKernel l x x' * (a + b) x' ∂haarPi K =
            (∫ x', isotypicKernel l x x' * a x' ∂haarPi K) +
              ∫ x', isotypicKernel l x x' * b x' ∂haarPi K := fun l => by
          rw [← integral_add (hint l a x) (hint l b x)]
          refine integral_congr_ae (Eventually.of_forall fun x' => ?_)
          simp [mul_add]
        change HasSum (fun l : K → HalfNatural =>
          ∫ x', isotypicKernel l x x' * (a + b) x' ∂haarPi K) (a x + b x)
        rw [funext e]
        exact (ha x).add (hb x)
      zero_mem' := by
        intro x
        simp
      smul_mem' := by
        intro c a ha x
        have e : ∀ l : K → HalfNatural, ∫ x', isotypicKernel l x x' * (c • a) x' ∂haarPi K =
            c * ∫ x', isotypicKernel l x x' * a x' ∂haarPi K := fun l => by
          rw [← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun x' => ?_)
          simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
          ring
        change HasSum (fun l : K → HalfNatural =>
          ∫ x', isotypicKernel l x x' * (c • a) x' ∂haarPi K) (c * a x)
        rw [funext e]
        exact (ha x).mul_left c }
  have hle : truncatedCoeffSpan K ϰ ≤ S := by
    refine iSup₂_le fun l _ ψ hψ x => ?_
    have h := hasSum_single (f := fun l' : K → HalfNatural =>
      ∫ x', isotypicKernel l' x x' * ψ x' ∂haarPi K) l (fun l' hl' => by
        have := hcomp l' ψ x
        rw [(hfix l l' ψ hψ).2 hl'] at this
        simpa using this.symm)
    have h₀ : ∫ x', isotypicKernel l x x' * ψ x' ∂haarPi K = ψ x := by
      rw [← hcomp l ψ x, (hfix l l ψ hψ).1]
    rw [h₀] at h
    exact h
  have h := hle hH u
  simpa only [hcomp] using h
end Kernel
section Hat
variable {J : Type} [Finite J]
omit [Finite J] in
theorem restrictTo_glue (B : Set J) (v : ↥B → specialUnitary) (z : ↥Bᶜ → specialUnitary) :
    restrictTo B (glue B v z) = v :=
  congrArg Prod.fst ((splitEquiv (X := specialUnitary) B).right_inv (v, z))
omit [Finite J] in
theorem restrictTo_compl_glue (B : Set J) (v : ↥B → specialUnitary) (z : ↥Bᶜ → specialUnitary) :
    restrictTo Bᶜ (glue B v z) = z :=
  congrArg Prod.snd ((splitEquiv (X := specialUnitary) B).right_inv (v, z))
def linkKernelCLM (β : ℝ) (B : Set J) (w : ↥B → specialUnitary) (z : ↥Bᶜ → specialUnitary)
    (hc : Continuous fun v : ↥B → specialUnitary => linkProductKernel β v w) :
    C(J → specialUnitary, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun H => ∫ v, linkProductKernel β v w * fibreAt B H z v ∂haarPi ↥B
      map_add' := fun H H' => by
        have hi : ∀ G : C(J → specialUnitary, ℂ),
            Integrable (fun v => linkProductKernel β v w * fibreAt B G z v) (haarPi ↥B) := fun G =>
          integrable_haarPi_of_continuous (hc.mul (fibreAt B G z).continuous)
        rw [← integral_add (hi H) (hi H')]
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        change linkProductKernel β v w * (H (glue B v z) + H' (glue B v z)) =
          linkProductKernel β v w * H (glue B v z) + linkProductKernel β v w * H' (glue B v z)
        ring
      map_smul' := fun a H => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        change linkProductKernel β v w * (a * H (glue B v z)) =
          a * (linkProductKernel β v w * H (glue B v z))
        ring }
    ‖(⟨_, hc⟩ : C(↥B → specialUnitary, ℂ))‖ (fun H => by
      have hb : ∀ v : ↥B → specialUnitary, ‖linkProductKernel β v w * fibreAt B H z v‖ ≤
          ‖(⟨_, hc⟩ : C(↥B → specialUnitary, ℂ))‖ * ‖H‖ := fun v => by
        rw [norm_mul]
        exact mul_le_mul ((⟨_, hc⟩ : C(↥B → specialUnitary, ℂ)).norm_coe_le_norm v)
          (H.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
      have h := norm_integral_le_of_norm_le_const (μ := haarPi ↥B)
        (Eventually.of_forall hb)
      simp only [probReal_univ, mul_one] at h
      exact h)
theorem linkKernelCLM_apply (β : ℝ) (B : Set J) (w : ↥B → specialUnitary) (z : ↥Bᶜ → specialUnitary)
    (hc : Continuous fun v : ↥B → specialUnitary => linkProductKernel β v w) (H : C(J → specialUnitary, ℂ)) :
    linkKernelCLM β B w z hc H =
      ∫ v, linkProductKernel β v w * fibreAt B H z v ∂haarPi ↥B := rfl
theorem fibreAt_partIsotypicProjC (B : Set J) (l : ↥B → HalfNatural) (G : C(J → specialUnitary, ℂ))
    (z : ↥Bᶜ → specialUnitary)
    (hcomp : ∀ (l : ↥B → HalfNatural) (H : C(↥B → specialUnitary, ℂ)) (u : ↥B → specialUnitary),
      isotypicPartSum l (toHaarL2 (H : (↥B → specialUnitary) → ℂ)) u =
        ∫ u', isotypicKernel l u u' * H u' ∂haarPi ↥B) :
    fibreAt B (partIsotypicProjC B l G) z =
      isotypicPartSum l (toHaarL2 (fibreAt B G z : (↥B → specialUnitary) → ℂ)) := by
  ext v
  rw [hcomp]
  change (∫ v', isotypicKernel l (restrictTo B (glue B v z)) v' *
      G (glue B v' (restrictTo Bᶜ (glue B v z))) ∂haarPi ↥B) = _
  rw [restrictTo_glue, restrictTo_compl_glue]
  rfl
omit [Finite J] in
theorem fibreAt_mulPullback (B : Set J) (f : (↥B → specialUnitary) → ℂ) (hf : IsRealEntryPolynomial f)
    (G : C(J → specialUnitary, ℂ)) (z : ↥Bᶜ → specialUnitary) :
    fibreAt B (mulPullback B f hf G) z =
      (⟨f, hf.1.continuous⟩ : C(↥B → specialUnitary, ℂ)) * fibreAt B G z := by
  ext v
  change f (restrictTo B (glue B v z)) * G (glue B v z) = _
  rw [restrictTo_glue]
  rfl
theorem isEntryPolynomial_mul {K : Type} {a b : (K → specialUnitary) → ℂ} (ha : IsEntryPolynomial a)
    (hb : IsEntryPolynomial b) : IsEntryPolynomial fun u => a u * b u := by apply _root_.YangMills.Construction.TransferOperators.KernelSymmetryAndGaugeInvariance.isEntryPolynomial_mul <;> assumption
theorem charCoeffProd_ne_zero (β : ℝ) {K : Type} [Finite K]
    (h : ∀ l : HalfNatural, 0 < (weightCharCoeff β l).re) (l : K → HalfNatural) :
    charCoeffProd β l ≠ 0 := by
  let _ : Fintype K := Fintype.ofFinite K
  rw [charCoeffProd, finprod_eq_prod_of_fintype, Finset.prod_ne_zero_iff]
  intro b _ hb
  have := h (l b)
  rw [hb] at this
  simp at this
theorem hasSum_hatSeriesTerm (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ) (hf : IsRealEntryPolynomial f)
    (F : C(J → specialUnitary, ℂ)) (hF : F ∈ hatSummableSet β B f hf) :
    HasSum (hatSeriesTerm β B f hf F) (hatSum β B f hf F) := by
  have h₀ : ∑' p : (↥B → HalfNatural) × (↥B → HalfNatural), ‖hatSeriesTerm β B f hf F p‖ₑ ≠ ∞ := by
    have : ∀ p, ‖hatSeriesTerm β B f hf F p‖ₑ =
        ‖charCoeffRatio β p.1 p.2‖ₑ * ‖hatSummand B f hf F p.1 p.2‖ₑ := fun p => enorm_smul _ _
    simp_rw [this]
    exact (show _ < ∞ from hF).ne
  have h₁ : Summable fun p => ‖hatSeriesTerm β B f hf F p‖ := by
    simpa only [toReal_enorm] using ENNReal.summable_toReal h₀
  exact h₁.of_norm.hasSum
end Hat
theorem polyThroughLinkKernelSmooth (hRoot : SqrtLinkFacts.SqrtLinkKernelFacts)
    (hSeveral : SeveralVariables.SeveralVariablesFacts)
    (hCoefficients : BondWeightCharCoeffStatement)
    (hComponents : IsotypicPartSums.Statement)
    (hSeries : HatSeriesConvergesStatement) : PolyThroughLinkKernelSmoothStatement := by
  intro J _ _ β B f hf hβ hB F w z hF
  have : Nonempty ↥B := hB.to_subtype
  have hser := ((hRoot β hβ).1 ↥B).2.1
  have hsev := fun (l : ↥B → HalfNatural) => hSeveral ↥B l ⟨0⟩
  have hsym : ∀ (l : ↥B → HalfNatural) (u u' : ↥B → specialUnitary),
      isotypicKernel l u u' = isotypicKernel l u' u := fun l u u' =>
    ((hsev l).1.2.2.2.2.1 u u').2
  have hpoly : ∀ (l : ↥B → HalfNatural) (ψ : C(↥B → specialUnitary, ℂ)), ψ ∈ prodCoeffSpan l →
      IsEntryPolynomial (ψ : (↥B → specialUnitary) → ℂ) := fun l ψ hψ =>
    (hsev l).2.2.2.2.2.1.2.1 ψ hψ
  have hfin := (hsev fun _ => ⟨0⟩).2.2.2.2.2.2.2.1
  obtain ⟨hmem, hcomp, hfix⟩ := hComponents ↥B
  obtain ⟨D, hD⟩ := (hfin f hf.1).2
  have hdom : F ∈ hatSummableSet β B f hf := (hSeries J β B f hf D hβ hB hD F hF).2.2.2.2.2.2.1
  have hc : Continuous fun v : ↥B → specialUnitary => linkProductKernel β v w :=
    continuous_linkProductKernel_left β hser w
  have hne : ∀ l : ↥B → HalfNatural, charCoeffProd β l ≠ 0 :=
    charCoeffProd_ne_zero β fun l => ((hCoefficients.2 β hβ).2.1 l).2.1
  let Fz : C(↥B → specialUnitary, ℂ) := fibreAt B F z
  let fC : C(↥B → specialUnitary, ℂ) := ⟨f, hf.1.continuous⟩
  let T : (↥B → HalfNatural) → C(↥B → specialUnitary, ℂ) := fun l =>
    fC * isotypicPartSum l (toHaarL2 (Fz : (↥B → specialUnitary) → ℂ))
  have hsection : ∀ l l' : ↥B → HalfNatural, fibreAt B (hatSummand B f hf F l l') z =
      isotypicPartSum l' (toHaarL2 (T l : (↥B → specialUnitary) → ℂ)) := by
    intro l l'
    rw [hatSummand, fibreAt_partIsotypicProjC B l' _ z hcomp, fibreAt_mulPullback,
      fibreAt_partIsotypicProjC B l _ z hcomp]
  have hterm : ∀ l l' : ↥B → HalfNatural,
      linkKernelCLM β B w z hc (hatSeriesTerm β B f hf F (l, l')) =
        charCoeffProd β l *
          isotypicPartSum l' (toHaarL2 (T l : (↥B → specialUnitary) → ℂ)) w := by
    intro l l'
    have h₁ : hatSeriesTerm β B f hf F (l, l') =
        charCoeffRatio β l l' • hatSummand B f hf F l l' := rfl
    set Φ : C(↥B → specialUnitary, ℂ) := isotypicPartSum l' (toHaarL2 (T l : (↥B → specialUnitary) → ℂ)) with hΦ
    have hΦmem : Φ ∈ prodCoeffSpan l' := (hmem l' _).1
    have h₂ := hasSum_integral_linkProductKernel_mul β hser hsym hcomp Φ w
    have h₃ : HasSum (fun l'' : ↥B → HalfNatural => charCoeffProd β l'' *
        isotypicPartSum l'' (toHaarL2 (Φ : (↥B → specialUnitary) → ℂ)) w)
        (charCoeffProd β l' * Φ w) := by
      have h := hasSum_single (f := fun l'' : ↥B → HalfNatural => charCoeffProd β l'' *
        isotypicPartSum l'' (toHaarL2 (Φ : (↥B → specialUnitary) → ℂ)) w) l' (fun l'' hl'' => by
          simp only [(hfix l' l'' Φ hΦmem).2 hl'']
          simp)
      simpa only [(hfix l' l' Φ hΦmem).1] using h
    have h₄ := h₂.unique h₃
    rw [h₁, map_smul, linkKernelCLM_apply, hsection, ← hΦ, h₄, charCoeffRatio, smul_eq_mul]
    field_simp [hne l']
  have hfibre : ∀ l : ↥B → HalfNatural, HasSum (fun l' : ↥B → HalfNatural =>
      linkKernelCLM β B w z hc (hatSeriesTerm β B f hf F (l, l')))
      (charCoeffProd β l * T l w) := by
    intro l
    have hψ := (hmem l (toHaarL2 (Fz : (↥B → specialUnitary) → ℂ))).1
    obtain ⟨H, hH, hHT⟩ := ((hfin _ (isEntryPolynomial_mul hf.1 (hpoly l _ hψ))).1).choose_spec
    have hTH : T l = H := ContinuousMap.ext hHT
    have h := hasSum_isotypicPartSum_apply hcomp hfix (hTH ▸ hH) w
    simp_rw [hterm]
    exact h.mul_left _
  have hall := ((linkKernelCLM β B w z hc).hasSum (hasSum_hatSeriesTerm β B f hf F hdom))
  have hsum := hall.prod_fiberwise hfibre
  have hright := (hasSum_integral_linkProductKernel_mul β hser hsym hcomp Fz w).mul_left (f w)
  have hsame : (fun l : ↥B → HalfNatural => charCoeffProd β l * T l w) =
      fun l => f w * (charCoeffProd β l *
        isotypicPartSum l (toHaarL2 (Fz : (↥B → specialUnitary) → ℂ)) w) := by
    funext l
    change charCoeffProd β l * (f w * _) = _
    ring
  rw [hsame] at hsum
  exact hright.unique hsum
end YangMills.Construction.SpinHarmonics.LinkKernelPolynomial
end
