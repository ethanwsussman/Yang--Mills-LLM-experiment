import YangMills.Construction.TorusOrFourSpace.ComplexClassesOfOnePointProof
import YangMills.Construction.TorusOrFourSpace.ModesOfACutOffOnThePeriodBoxProof
import YangMills.Construction.TorusOrFourSpace.MultilinearFormBoundedInTheC1NormsProof
import YangMills.Construction.TorusOrFourSpace.PartialSumsUnderATestFunction
import YangMills.Construction.TorusOrFourSpace.PartitionsOfUnityOnCompactSubsetsOfPowers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PeriodCell.TensorApproxProof
private theorem fin_one_pnat_eq (i : Fin ((1 : ℕ+) : ℕ)) : i = ⟨0, (1 : ℕ+).pos⟩ := by apply _root_.YangMills.Construction.PeriodicSpace.PeriodCell.CutoffModeLemmas.fin_one_index_eq <;> assumption
open Kind.Tuple
private theorem boxSet_single (D : Params) (E : Kind) (A : Set (E.Pt D)) :
    boxSet D E (n := 1) (fun _ => A) = singleSet D E A := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.AdmissibleCharts.boxSet_one <;> assumption
private theorem mem_cell_of_norm_le {ρ : ℝ} (hρ : 0 < ρ) (u : Fin 4 → ℝ)
    (h : TorusMetric.euclidNormVec u ≤ ρ) : u ∈ cell (4 * ρ) := by apply _root_.YangMills.SharedProofs.p89512 <;> assumption
private theorem fourierChar_eq_prod {n : ℕ+} (P : ℝ) (k : IntCoords n) (u : Coords n) :
    fourierChar P k u = ∏ i, fourierCharR4 P (k.block i) (u.block i) := by apply _root_.YangMills.Construction.PeriodicSpace.PeriodCell.Fourier.fourierChar_eq_prod_blocks <;> assumption
private def truncOnTuples (D : Params) {n : ℕ+} (P : ℝ)
    (F : Kind.euclidean.Tuple D n → ℂ) (t : ℕ+) :
    Kind.euclidean.Tuple D n → ℂ :=
  fun y => ∑ k ∈ IntCoords.cubeUpTo t,
    fourierCoeff D P F k * ∏ i, fourierCharR4 P (k.block i) (y i)
private theorem truncOnTuples_comp (D : Params) {n : ℕ+} (P : ℝ)
    (F : Kind.euclidean.Tuple D n → ℂ) (t : ℕ+) :
    truncOnTuples D P F t ∘ proj D Kind.euclidean = fourierPartialSum D P F t := by
  funext u
  simp only [Function.comp, truncOnTuples, fourierPartialSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fourierChar_eq_prod]
  rfl
private theorem cutoffFourierSum_eq_mul (D : Params) {n : ℕ+} (P : ℝ)
    (χ : Fin (n : ℕ) → Kind.euclidean.Pt D → ℝ)
    (F : Kind.euclidean.Tuple D n → ℂ) (t : ℕ+) :
    cutoffFourierSum D P χ F t =
      cutoffTensor D Kind.euclidean χ * truncOnTuples D P F t := by
  funext y
  simp only [cutoffFourierSum, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, tensorProd, cutoffTensor,
    cutoffMode, truncOnTuples, smul_eq_mul, Finset.prod_mul_distrib]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring
private theorem supportQ_ofReal (D : Params) (E : Kind) (u : E.Pt D → ℝ) :
    Kind.supportQ D E (fun y => (u y : ℂ)) = Kind.supportQ D E u := by apply _root_.YangMills.SharedProofs.p40645 <;> assumption
private theorem smul_tensorProd_eq (D : Params) {n : ℕ+} (i₀ : Fin (n : ℕ)) (c : ℂ)
    (a b : Fin (n : ℕ) → Kind.euclidean.Pt D → ℂ) :
    c • tensorProd D Kind.euclidean (fun i y => a i y * b i y) =
      tensorProd D Kind.euclidean
        (fun i y => a i y * ((if i = i₀ then c else 1) * b i y)) := by
  funext y
  simp only [Pi.smul_apply, tensorProd, smul_eq_mul]
  have h : ∀ i, a i (y i) * ((if i = i₀ then c else 1) * b i (y i)) =
      (if i = i₀ then c else 1) * (a i (y i) * b i (y i)) := fun i => by ring
  simp only [h]
  have h2 : ∏ i, (if i = i₀ then c else 1) * (a i (y i) * b i (y i)) =
      (∏ i, if i = i₀ then c else 1) * ∏ i, a i (y i) * b i (y i) := Finset.prod_mul_distrib
  rw [h2, Finset.prod_ite_eq' Finset.univ i₀ (fun _ => c)]
  simp
theorem tensorApproxUnderCutoff_holds (hAn : PartitionsOfUnity.Statement)
    (hClass : ComplexSupportedClassesClaim)
    (hModes : CutoffModeBounds)
    (hUnder : FourierTruncationsConverge)
    (hPts : TupleFacts.AllFacts) :
    TensorApproxUnderCutoff := by
  intro D n ρ hρ O hO hOρ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hProd1, -, -, -, -, -, -, hKept1, -, -, -, -, -⟩ :=
    hPts D Kind.euclidean 1
  obtain ⟨-, -, hMetric, -, -, -, -, -, -, -, -, hProdn, -, -, -, -, -, hSupp, -, hStable, -,
    hTensClass, hTensTest, -⟩ := hPts D Kind.euclidean n
  have hcell : ∀ i, O i ⊆ cell (4 * ρ) := fun i u hu => mem_cell_of_norm_le hρ u (hOρ i u hu)
  have hProdCell : boxSet D Kind.euclidean O ⊆ cellPow D n (4 * ρ) :=
    fun y hy i => hcell i (hy i)
  have hThird : Kind.Tuple.testFns D Kind.euclidean
      (boxSet D Kind.euclidean O) ⊆ PeriodCell.cellTestFns D n (4 * ρ) :=
    fun F hF => ⟨hF.1, hF.2.1, hF.2.2.trans hProdCell⟩
  refine ⟨?_, ?_, hThird, ?_⟩
  · intro K hK hKO
    have hchoice : ∀ i, ∃ c : Kind.euclidean.Pt D → ℝ,
        (fun y => (c y : ℂ)) ∈ singleTestFns D Kind.euclidean (O i) ∧
          ∀ y ∈ K i, c y = 1 := by
      intro i
      have hKc : Kind.Tuple.IsCompactT D Kind.euclidean
          (singleSet D Kind.euclidean (K i)) := by
        rw [← boxSet_single]
        exact (hProd1 fun _ => K i).2.2 fun _ => hK i
      have hOc : Kind.Tuple.IsOpenT D Kind.euclidean
          (singleSet D Kind.euclidean (O i)) := by
        rw [← boxSet_single]
        exact (hProd1 fun _ => O i).1 fun _ => hO i
      have hsub : singleSet D Kind.euclidean (K i) ⊆
          singleSet D Kind.euclidean (O i) := fun y hy => hKO i hy
      obtain ⟨φ, hφ, hval, N, ⟨U, -, hKU, hUN⟩, hφN⟩ :=
        (hAn D Kind.euclidean 1).2 _ _ hKc hOc hsub
      have hy1 : ∀ y : Kind.euclidean.Tuple D 1, (fun _ => y ⟨0, (1 : ℕ+).pos⟩) = y := by
        intro y
        funext j
        rw [fin_one_pnat_eq j]
      refine ⟨fun y => (φ fun _ => y).re, ?_, ?_⟩
      · have hkey : ofSingle D Kind.euclidean
            (fun y => (((φ fun _ => y).re : ℝ) : ℂ)) = φ := by
          funext y
          obtain ⟨s, -, hs⟩ := hval y
          simp only [ofSingle]
          rw [hy1 y, hs]
          simp
        show ofSingle D Kind.euclidean (fun y => (((φ fun _ => y).re : ℝ) : ℂ)) ∈
          Kind.Tuple.testFns D Kind.euclidean
            (singleSet D Kind.euclidean (O i))
        rw [hkey]
        exact hφ
      · intro y hy
        have hmem : (fun _ => y : Kind.euclidean.Tuple D 1) ∈ N :=
          hUN (hKU hy)
        show (φ fun _ => y).re = 1
        rw [hφN _ hmem]
        simp
    choose χ hχ1 hχ2 using hchoice
    exact ⟨χ, hχ1, hχ2⟩
  · intro F χ hχ h1
    refine ⟨hχ, ?_⟩
    funext y
    show cutoffTensor D Kind.euclidean χ y * F.1 y = F.1 y
    by_cases hy : F.1 y = 0
    · simp [hy]
    · have hys : y ∈ Kind.Tuple.supportT D Kind.euclidean F.1 := by
        show ∀ r : ℝ, 0 < r → ∃ z ∈ {z | F.1 z ≠ 0},
          Kind.Tuple.tupleDist D Kind.euclidean y z < r
        intro r hr
        refine ⟨y, hy, ?_⟩
        rw [(hMetric.2.1 y y).2 rfl]
        exact hr
      have h2 : cutoffTensor D Kind.euclidean χ y = 1 := by
        simp only [cutoffTensor, tensorProd]
        exact Finset.prod_eq_one fun i _ => by rw [h1 i y hys]; simp
      rw [h2, one_mul]
  · intro F χ hχF
    have hcut : ∀ i, (fun y => (χ i y : ℂ)) ∈
        singleTestFns D Kind.euclidean (O i) := hχF.1
    have hcut' : ∀ i, ofSingle D Kind.euclidean (fun y => (χ i y : ℂ)) ∈
        Kind.Tuple.testFns D Kind.euclidean
          (singleSet D Kind.euclidean (O i)) := hcut
    have hProdOpen : Kind.Tuple.IsOpenT D Kind.euclidean
        (boxSet D Kind.euclidean O) := (hProdn O).1 hO
    have hθ : cutoffTensor D Kind.euclidean χ ∈
        Kind.Tuple.testFns D Kind.euclidean
          (boxSet D Kind.euclidean O) :=
      hTensTest O (fun i y => (χ i y : ℂ)) hO hcut
    obtain ⟨hGs, hGt⟩ := hUnder D n (4 * ρ) (by positivity) _ (hThird hθ) _ (hThird F.2)
      (fun t => truncOnTuples D (4 * ρ) F.1 t)
      (fun t => truncOnTuples_comp D (4 * ρ) F.1 t)
    have hmem : ∀ t, cutoffFourierSum D (4 * ρ) χ F.1 t ∈
        Kind.Tuple.testFns D Kind.euclidean
          (boxSet D Kind.euclidean O) := by
      intro t
      rw [cutoffFourierSum_eq_mul, mul_comm]
      exact ((hStable _ hProdOpen).2 _ hθ).2.2.2.1 _ (hGs t)
    have hc : ∀ i, χ i ∈ Kind.c1SupportedIn D Kind.euclidean (O i) := fun i =>
      (hClass D Kind.euclidean (O i) (hO i)).2.2.2.2.1 (χ i) (hcut i)
    have hKc : Kind.Tuple.IsCompactT D Kind.euclidean
        (boxSet D Kind.euclidean fun i => Kind.supportQ D Kind.euclidean (χ i)) :=
      (hProdn _).2.2 fun i => (hc i).2.1
    have hKO : (boxSet D Kind.euclidean fun i => Kind.supportQ D Kind.euclidean (χ i)) ⊆
        boxSet D Kind.euclidean O := fun y hy i => (hc i).2.2 (hy i)
    have hθK : Kind.Tuple.supportT D Kind.euclidean (cutoffTensor D Kind.euclidean χ) ⊆
        boxSet D Kind.euclidean fun i => Kind.supportQ D Kind.euclidean (χ i) := by
      have h := (hTensClass 1 (fun i y => (χ i y : ℂ)) fun i => (hcut' i).1 1).2.2
      simp only [supportQ_ofReal] at h
      exact h
    have hFK : Kind.Tuple.supportT D Kind.euclidean F.1 ⊆
        boxSet D Kind.euclidean fun i => Kind.supportQ D Kind.euclidean (χ i) := by
      have h : Kind.Tuple.supportT D Kind.euclidean F.1 =
          Kind.Tuple.supportT D Kind.euclidean
            (cutoffTensor D Kind.euclidean χ * F.1) := by
        rw [hχF.2]
      rw [h]
      exact ((hSupp _ F.1 1 1).2).trans (Set.inter_subset_left.trans hθK)
    refine ⟨fun t => ⟨_, hmem t⟩, fun t => rfl, ?_, ?_⟩
    · intro t
      have hsmooth : ∀ (s : ℂ) (κ : Fin 4 → ℤ), Kind.Tuple.IsSmoothT D Kind.euclidean
          (ofSingle D Kind.euclidean fun y => s * fourierCharR4 (4 * ρ) κ y) := by
        intro s κ ν
        let i : Fin (n : ℕ) := ⟨0, n.pos⟩
        have he := ((hModes D ρ hρ (O i) (hO i) (hcell i)).2.1 κ) ν
        have h := (hKept1 ν _ _ he he).1 s 0
        have hEq : (ofSingle D Kind.euclidean fun y => s * fourierCharR4 (4 * ρ) κ y) =
            s • ofSingle D Kind.euclidean (fourierCharR4 (4 * ρ) κ) +
              (0 : ℂ) • ofSingle D Kind.euclidean (fourierCharR4 (4 * ρ) κ) := by
          funext y
          simp [ofSingle]
        rw [hEq]
        exact h
      let i₀ : Fin (n : ℕ) := ⟨0, n.pos⟩
      let e := (IntCoords.cubeUpTo (p := n) t).equivFin
      refine ⟨(IntCoords.cubeUpTo (p := n) t).card,
        fun l i y => (χ i y : ℂ) *
          ((if i = i₀ then fourierCoeff D (4 * ρ) F.1 (e.symm l).1 else 1) *
            fourierCharR4 (4 * ρ) ((e.symm l).1.block i) y), ?_, ?_⟩
      · intro l i
        have h := ((hModes D ρ hρ (O i) (hO i) (hcell i)).2.2 (χ i) (hcut i)).1 _
          (hsmooth (if i = i₀ then fourierCoeff D (4 * ρ) F.1 (e.symm l).1 else 1)
            ((e.symm l).1.block i))
        exact h
      · show cutoffFourierSum D (4 * ρ) χ F.1 t = _
        unfold cutoffFourierSum
        rw [← Finset.sum_coe_sort, ← Equiv.sum_comp e.symm]
        refine Finset.sum_congr rfl fun l _ => ?_
        exact smul_tensorProd_eq D i₀ _ (fun i y => (χ i y : ℂ))
          (fun i => fourierCharR4 (4 * ρ) ((e.symm l).1.block i))
    · refine ⟨⟨_, hKc, hKO, hFK, fun t => ?_⟩, fun ν => ?_⟩
      · show Kind.Tuple.supportT D Kind.euclidean
          (cutoffFourierSum D (4 * ρ) χ F.1 t) ⊆ _
        rw [cutoffFourierSum_eq_mul]
        exact ((hSupp _ _ 1 1).2).trans (Set.inter_subset_left.trans hθK)
      · have h : ∀ t, cutoffFourierSum D (4 * ρ) χ F.1 t - F.1 =
            cutoffTensor D Kind.euclidean χ * (truncOnTuples D (4 * ρ) F.1 t - F.1) := by
          intro t
          rw [mul_sub, hχF.2, cutoffFourierSum_eq_mul]
        simp only [h]
        exact hGt ν
end YangMills.Construction.PeriodicSpace.PeriodCell.TensorApproxProof
