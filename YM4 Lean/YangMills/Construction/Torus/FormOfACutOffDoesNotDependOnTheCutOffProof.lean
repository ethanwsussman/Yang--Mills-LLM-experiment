import YangMills.Construction.Torus.CoefficientsOfATestFunctionOnTheBox
import YangMills.Construction.Torus.FormOfACutOffAtTensors
import YangMills.Construction.Torus.FormOfACutOffDoesNotDependOnTheCutOff
import YangMills.Construction.Torus.FormOfACutOffIsABoundedLinearForm
import YangMills.Construction.Torus.GradientNormLipschitzConstantAndSharpNorm
import YangMills.Construction.Torus.GradientNormOfACutOffTimesAMode
import YangMills.Construction.Torus.PartialSumsInsideACutOffConverge
import YangMills.Construction.Torus.RestrictionsSumsProductsAndTensorsOfTestFunctions
import Mathlib
set_option autoImplicit false
open Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.AmbientPoints.CutoffIndep
open YangMills.Construction.Torus.FourierBox YangMills.Construction.TorusMetric YangMills.Construction.Conventions
variable {s : StandingParameters} {n : ℕ}
theorem mem_fundamentalBox_of_norm_le {r : ℝ} (hr : 0 < r) {p : Pt s .euclidean}
    (hp : euclidNormVec (fun μ => coord s μ p) ≤ r) :
    p ∈ fundamentalBox s (4 * r) := by
  intro μ
  have habs : |coord s μ p| ≤ euclidNormVec fun μ => coord s μ p := by
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun ν => (coord s ν p) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
  have hle := abs_le.1 (habs.trans hp)
  constructor <;> linarith [hle.1, hle.2]
theorem sum_smul_mem_and_map {U : Set (Tuple s .euclidean n)} {ι : Type}
    (hlin : LinearCombFacts U) {G : Tuple s .euclidean n → ℂ}
    (hG : G ∈ testFns U) (Λ : (Tuple s .euclidean n → ℂ) → ℂ)
    (hΛ : IsComplexLinearForm fun φ : testFns U => Λ φ.1) (I : Finset ι) (a : ι → ℂ)
    (φ : ι → Tuple s .euclidean n → ℂ) (hφ : ∀ j ∈ I, φ j ∈ testFns U) :
    (∑ j ∈ I, a j • φ j) ∈ testFns U ∧ Λ (∑ j ∈ I, a j • φ j) = ∑ j ∈ I, a j * Λ (φ j) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have hzero : (0 : Tuple s .euclidean n → ℂ) ∈ testFns U := by
      have h := (hlin G hG G hG 0 0).1
      simpa using h
    have hval : Λ 0 = 0 * Λ G := hΛ.2 0 ⟨G, hG⟩ ⟨0, hzero⟩ (by simp)
    simp only [Finset.sum_empty]
    exact ⟨hzero, by rw [hval, zero_mul]⟩
  | insert b I hb ih =>
    obtain ⟨hI, hΛI⟩ := ih fun j hj => hφ j (Finset.mem_insert_of_mem hj)
    have hφb := hφ b (Finset.mem_insert_self b I)
    have hab : a b • φ b ∈ testFns U := by
      have h := (hlin _ hφb _ hφb (a b) 0).1
      simpa using h
    have hadd : a b • φ b + ∑ j ∈ I, a j • φ j ∈ testFns U := by
      have h := (hlin _ hφb _ hI (a b) 1).1
      simpa using h
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    refine ⟨hadd, ?_⟩
    have e1 : Λ (a b • φ b + ∑ j ∈ I, a j • φ j) = Λ (a b • φ b) + Λ (∑ j ∈ I, a j • φ j) :=
      hΛ.1 ⟨_, hab⟩ ⟨_, hI⟩ ⟨_, hadd⟩ rfl
    have e2 : Λ (a b • φ b) = a b * Λ (φ b) := hΛ.2 (a b) ⟨_, hφb⟩ ⟨_, hab⟩ rfl
    rw [e1, e2, hΛI]
theorem cutoffSeriesIndepOfCutoff_of_parts (hBdd : CutoffSeriesBoundedLinear)
    (hAtTens : CutoffSeriesAtTensors)
    (hConv : CutoffPartialSumsTendsto)
    (hCoeff : FourierCoeffBounds)
    (hModeGrad : CutoffTimesModeGradNorm)
    (hC1 : GradientC1Bounds.Statement)
    (hOps : TestFnOperations) : CutoffSeriesIndepOfCutoff := by
  intro s n r C O B hO hC hLin hB F χ χ' hχ hχ'
  obtain ⟨hn, hr, hOi⟩ := id hO
  have hpos : 0 < 4 * r := by positivity
  have hopen : IsOpen (fundamentalBoxPow s n (4 * r)) := isOpen_fundamentalBoxPow s n (4 * r)
  have hlc : LinearCombFacts (fundamentalBoxPow s n (4 * r)) :=
    ((hOps s .euclidean n hn).2.1 _ hopen).2.1
  have hin : ∀ i, ∀ p ∈ O i, p ∈ fundamentalBox s (4 * r) := fun i p hp =>
    mem_fundamentalBox_of_norm_le hr ((hOi i).2 hp)
  have hsub : boxSet O ⊆ fundamentalBoxPow s n (4 * r) := fun y hy i =>
    hin i _ (hy i (Set.mem_univ i))
  have hF : F.1 ∈ testFns (fundamentalBoxPow s n (4 * r)) := testFns_mono hsub F.2
  have hFactor : ∀ ψ : Fin n → Pt s .euclidean → ℝ, IsCutoff O ψ →
      ∀ (k : Fin (4 * n) → ℤ) (i : Fin n),
        ofSinglePoint (cutoffModeTuple (4 * r) ψ k i) ∈
          testFns (fundamentalBoxPow s 1 (4 * r)) := by
    intro ψ hψ k i
    have h := (hModeGrad s r hr (O i) (ψ i) (blockOf k i) (hOi i).1 (hψ i)).1
    have hsub1 : singletonTuples (O i) ⊆ fundamentalBoxPow s 1 (4 * r) := fun y hy j => by
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      exact hin i _ hy
    exact testFns_mono hsub1 h
  have hProd : ∀ ψ : Fin n → Pt s .euclidean → ℝ, IsCutoff O ψ →
      ∀ k : Fin (4 * n) → ℤ,
        tensorProd (cutoffModeTuple (4 * r) ψ k) ∈ testFns (fundamentalBoxPow s n (4 * r)) :=
    fun ψ hψ k => ((hCoeff s n (4 * r) hn hpos).2.2.2 _ (hFactor ψ hψ k)).1
  have hExpand : ∀ ψ₁ ψ₂ : Fin n → Pt s .euclidean → ℝ, IsCutoff O ψ₁ → IsCutoff O ψ₂ →
      ∀ t : ℕ+, cutoffPartialSum (4 * r) ψ₂ F.1 t ∈
          testFns (fundamentalBoxPow s n (4 * r)) ∧
        cutoffSeries (4 * r) B ψ₁ (cutoffPartialSum (4 * r) ψ₂ F.1 t) =
          ∑ k ∈ (modesWithin (t : ℕ) : Finset (Fin (4 * n) → ℤ)), fourierCoeff (4 * r) F.1 k *
            B fun i x => (ψ₁ i x : ℂ) * ((ψ₂ i x : ℂ) * fourierMode (4 * r) (blockOf k i) x) := by
    intro ψ₁ ψ₂ hψ₁ hψ₂ t
    have e : cutoffPartialSum (4 * r) ψ₂ F.1 t =
        ∑ k ∈ (modesWithin (t : ℕ) : Finset (Fin (4 * n) → ℤ)),
          fourierCoeff (4 * r) F.1 k • tensorProd (cutoffModeTuple (4 * r) ψ₂ k) := by
      funext y
      simp [cutoffPartialSum, Finset.sum_apply]
    have h := sum_smul_mem_and_map hlc hF (cutoffSeries (4 * r) B ψ₁)
      (hBdd s n r C O B ψ₁ hO hC hB hψ₁).2 (modesWithin (t : ℕ))
      (fourierCoeff (4 * r) F.1) (fun k => tensorProd (cutoffModeTuple (4 * r) ψ₂ k))
      (fun k _ => hProd ψ₂ hψ₂ k)
    rw [e]
    refine ⟨h.1, h.2.trans (Finset.sum_congr rfl fun k _ => ?_)⟩
    rw [hAtTens s n r C O B ψ₁ hO hC hLin hB hψ₁ _ (hFactor ψ₂ hψ₂ k)]
    rfl
  have hTends : ∀ ψ₁ ψ₂ : Fin n → Pt s .euclidean → ℝ, IsCutoff O ψ₁ → IsCutoffFor ψ₂ F →
      Tendsto (fun t : ℕ+ => cutoffSeries (4 * r) B ψ₁ (cutoffPartialSum (4 * r) ψ₂ F.1 t))
        atTop (𝓝 (cutoffSeries (4 * r) B ψ₁ F.1)) := by
    intro ψ₁ ψ₂ hψ₁ hψ₂
    obtain ⟨hbd, hlinear⟩ := hBdd s n r C O B ψ₁ hO hC hB hψ₁
    have hcv := hConv s n r O hO F ψ₂ hψ₂
    obtain ⟨M, hMdef⟩ : ∃ M : ℝ≥0∞, M = ∏ i, c1GradNorm fun x => (ψ₁ i x : ℂ) := ⟨_, rfl⟩
    have hMfin : M ≠ ⊤ := by
      rw [hMdef]
      refine ENNReal.prod_ne_top fun i _ => ?_
      have hi := hψ₁ i
      have hreg : IsCnAtPoint 1 fun x => (ψ₁ i x : ℂ) := by
        have hsm : IsCnOn Set.univ ⊤
            (ofSinglePoint (fun x => (ψ₁ i x : ℂ)) ∘ tupleProj s .euclidean 1) := hi.1
        exact ⟨hsm.1, fun m _ => hsm.2 m le_top⟩
      exact ((hC1 s .euclidean).2 ⟨1, Set.mem_Ici.2 le_rfl⟩ (ψ₁ i) hreg hi.2.1).1.ne
    obtain ⟨K, hKdef⟩ : ∃ K : ℝ≥0∞, K = ENNReal.ofReal (C * bumpNumber n r) * M := ⟨_, rfl⟩
    have hKfin : K ≠ ⊤ := by
      rw [hKdef]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMfin
    have hdiff : ∀ t : ℕ+,
        ENNReal.ofReal ‖cutoffSeries (4 * r) B ψ₁ (cutoffPartialSum (4 * r) ψ₂ F.1 t) -
            cutoffSeries (4 * r) B ψ₁ F.1‖ ≤
          K * cnNorm (5 * n + 1) (cutoffPartialSum (4 * r) ψ₂ F.1 t - F.1) := by
      intro t
      have hPt := (hExpand ψ₁ ψ₂ hψ₁ hψ₂.1 t).1
      have hsubF : cutoffPartialSum (4 * r) ψ₂ F.1 t - F.1 ∈
          testFns (fundamentalBoxPow s n (4 * r)) := by
        have h := (hlc _ hPt _ hF 1 (-1)).1
        have e : (1 : ℂ) • cutoffPartialSum (4 * r) ψ₂ F.1 t + (-1 : ℂ) • F.1 =
            cutoffPartialSum (4 * r) ψ₂ F.1 t - F.1 := by
          simp [sub_eq_add_neg]
        rwa [e] at h
      have hsplit : cutoffSeries (4 * r) B ψ₁ (cutoffPartialSum (4 * r) ψ₂ F.1 t) =
          cutoffSeries (4 * r) B ψ₁ (cutoffPartialSum (4 * r) ψ₂ F.1 t - F.1) +
            cutoffSeries (4 * r) B ψ₁ F.1 :=
        hlinear.1 ⟨_, hsubF⟩ ⟨_, hF⟩ ⟨_, hPt⟩ (by simp)
      rw [hsplit, add_sub_cancel_right, hKdef, hMdef]
      exact (hbd _ hsubF).2
    have hzero : Tendsto
        (fun t : ℕ+ => K * cnNorm (5 * n + 1) (cutoffPartialSum (4 * r) ψ₂ F.1 t - F.1))
        atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (hcv.2.2.2 (5 * n + 1)) (Or.inr hKfin)
      simpa using h
    have hE : Tendsto (fun t : ℕ+ => ENNReal.ofReal
        ‖cutoffSeries (4 * r) B ψ₁ (cutoffPartialSum (4 * r) ψ₂ F.1 t) -
          cutoffSeries (4 * r) B ψ₁ F.1‖) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero (fun _ => zero_le) hdiff
    have hR : Tendsto (fun t : ℕ+ =>
        ‖cutoffSeries (4 * r) B ψ₁ (cutoffPartialSum (4 * r) ψ₂ F.1 t) -
          cutoffSeries (4 * r) B ψ₁ F.1‖) atTop (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hE
      simpa [Function.comp_def, ENNReal.toReal_ofReal (norm_nonneg _)] using h
    exact tendsto_iff_norm_sub_tendsto_zero.2 hR
  have hA := hTends χ χ' hχ.1 hχ'
  have hB' := hTends χ' χ hχ'.1 hχ
  refine tendsto_nhds_unique hA (hB'.congr fun t => ?_)
  rw [(hExpand χ' χ hχ'.1 hχ.1 t).2, (hExpand χ χ' hχ.1 hχ'.1 t).2]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (fun (i : Fin n) (x : Pt s .euclidean) =>
      (χ' i x : ℂ) * ((χ i x : ℂ) * fourierMode (4 * r) (blockOf k i) x)) =
      fun i x => (χ i x : ℂ) * ((χ' i x : ℂ) * fourierMode (4 * r) (blockOf k i) x) := by
    funext i x
    ring
  rw [e]
end YangMills.Construction.AmbientPoints.CutoffIndep
