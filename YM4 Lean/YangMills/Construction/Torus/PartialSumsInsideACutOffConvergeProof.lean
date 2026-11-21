import YangMills.Construction.Torus.CoveringMapOpenAndCompactSetsAndDerivativesOfTuplesProof
import YangMills.Construction.Torus.CoveringMapOpenAndCompactSetsAndDerivativesOfTuples
import YangMills.Construction.Torus.NormOfAProductAndMultiplesOfTensors
import YangMills.Construction.Torus.PartialSumsConvergeOnTheBox
import YangMills.Construction.Torus.PartialSumsInsideACutOffConverge
import YangMills.Construction.Torus.RestrictionsSumsProductsAndTensorsOfTestFunctions
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.AmbientPoints
open Torus.FourierBox
namespace CutoffPartialSums
section Partials
variable {D : ℕ}
def AllPartialsCont (G : (Fin D → ℝ) → ℂ) : Prop := ∀ r, ContinuousPartialsUpTo univ r G
theorem AllPartialsCont.lineDifferentiableAt {G : (Fin D → ℝ) → ℂ} (h : AllPartialsCont G)
    (j : Fin D) (x : Fin D → ℝ) : LineDifferentiableAt ℝ G x (Pi.single j 1) :=
  (h 1).2 j |>.1 x (mem_univ x)
theorem AllPartialsCont.partialDerivFn {G : (Fin D → ℝ) → ℂ} (h : AllPartialsCont G)
    (j : Fin D) : AllPartialsCont (AmbientPoints.partialDeriv j G) := by apply _root_.YangMills.Construction.AmbientPoints.TupleTopology.AllContinuousPartials.partialDeriv <;> assumption
theorem hasLineDerivAt_partial_add {A B : (Fin D → ℝ) → ℂ} (hA : AllPartialsCont A)
    (hB : AllPartialsCont B) (j : Fin D) (x : Fin D → ℝ) :
    HasLineDerivAt ℝ (A + B) (AmbientPoints.partialDeriv j A x +
      AmbientPoints.partialDeriv j B x) x (Pi.single j 1) := by
  have da := (hA.lineDifferentiableAt j x).hasLineDerivAt
  have db := (hB.lineDifferentiableAt j x).hasLineDerivAt
  unfold HasLineDerivAt at da db ⊢
  exact da.add db
theorem hasLineDerivAt_partial_smul {A : (Fin D → ℝ) → ℂ} (hA : AllPartialsCont A) (c : ℂ)
    (j : Fin D) (x : Fin D → ℝ) :
    HasLineDerivAt ℝ (c • A) (c * AmbientPoints.partialDeriv j A x) x (Pi.single j 1) := by
  have da := (hA.lineDifferentiableAt j x).hasLineDerivAt
  unfold HasLineDerivAt at da ⊢
  exact da.const_mul c
theorem partialDeriv_add {A B : (Fin D → ℝ) → ℂ} (hA : AllPartialsCont A)
    (hB : AllPartialsCont B) (j : Fin D) :
    AmbientPoints.partialDeriv j (A + B) =
      AmbientPoints.partialDeriv j A + AmbientPoints.partialDeriv j B := by
  funext x
  exact (hasLineDerivAt_partial_add hA hB j x).lineDeriv
theorem partialDeriv_smul {A : (Fin D → ℝ) → ℂ} (hA : AllPartialsCont A) (c : ℂ) (j : Fin D) :
    AmbientPoints.partialDeriv j (c • A) = c • AmbientPoints.partialDeriv j A := by
  funext x
  exact (hasLineDerivAt_partial_smul hA c j x).lineDeriv
theorem AllPartialsCont.add {A B : (Fin D → ℝ) → ℂ} (hA : AllPartialsCont A)
    (hB : AllPartialsCont B) : AllPartialsCont (A + B) := by
  intro r
  induction r generalizing A B with
  | zero => exact ContinuousOn.add (hA 0) (hB 0)
  | succ r ih =>
    refine ⟨ContinuousOn.add (hA (r + 1)).continuousOn (hB (r + 1)).continuousOn, fun j => ?_⟩
    refine ⟨fun x _ => (hasLineDerivAt_partial_add hA hB j x).lineDifferentiableAt, ?_⟩
    rw [partialDeriv_add hA hB]
    exact ih (hA.partialDerivFn j) (hB.partialDerivFn j)
theorem AllPartialsCont.smul {A : (Fin D → ℝ) → ℂ} (hA : AllPartialsCont A) (c : ℂ) :
    AllPartialsCont (c • A) := by
  intro r
  induction r generalizing A with
  | zero => exact ContinuousOn.const_smul (hA 0) c
  | succ r ih =>
    refine ⟨ContinuousOn.const_smul (hA (r + 1)).continuousOn c, fun j => ?_⟩
    refine ⟨fun x _ => (hasLineDerivAt_partial_smul hA c j x).lineDifferentiableAt, ?_⟩
    rw [partialDeriv_smul hA]
    exact ih (hA.partialDerivFn j)
theorem allPartialsCont_zero : AllPartialsCont (0 : (Fin D → ℝ) → ℂ) := by
  intro r
  exact continuousPartialsUpTo_of_contDiff r contDiff_const
def IsLinearOnAllPartials (L : ((Fin D → ℝ) → ℂ) → (Fin D → ℝ) → ℂ) : Prop :=
  (∀ U, AllPartialsCont U → AllPartialsCont (L U)) ∧
    (∀ U V, AllPartialsCont U → AllPartialsCont V → L (U + V) = L U + L V) ∧
    ∀ (a : ℂ) U, AllPartialsCont U → L (a • U) = a • L U
theorem isLinearOnAllPartials_id : IsLinearOnAllPartials (D := D) id := by
  refine ⟨fun U hU => hU, ?_, ?_⟩
  · intro U V _ _
    rfl
  · intro a U _
    rfl
theorem IsLinearOnAllPartials.comp {L M : ((Fin D → ℝ) → ℂ) → (Fin D → ℝ) → ℂ}
    (hL : IsLinearOnAllPartials L) (hM : IsLinearOnAllPartials M) :
    IsLinearOnAllPartials (fun G => L (M G)) := by
  obtain ⟨hL0, hL1, hL2⟩ := hL
  obtain ⟨hM0, hM1, hM2⟩ := hM
  refine ⟨fun U hU => hL0 (M U) (hM0 U hU), fun U V hU hV => ?_, fun a U hU => ?_⟩
  · show L (M (U + V)) = L (M U) + L (M V)
    rw [hM1 U V hU hV]
    exact hL1 (M U) (M V) (hM0 U hU) (hM0 V hV)
  · show L (M (a • U)) = a • L (M U)
    rw [hM2 a U hU]
    exact hL2 a (M U) (hM0 U hU)
theorem isLinearOnAllPartials_partialDeriv (j : Fin D) :
    IsLinearOnAllPartials (AmbientPoints.partialDeriv j) := by
  refine ⟨fun U hU => hU.partialDerivFn j, fun U V hU hV => ?_, fun a U hU => ?_⟩
  · exact partialDeriv_add hU hV j
  · exact partialDeriv_smul hU a j
theorem isLinearOnAllPartials_iterate (j : Fin D) (m : ℕ) :
    IsLinearOnAllPartials (AmbientPoints.partialDeriv j)^[m] := by
  induction m with
  | zero => exact isLinearOnAllPartials_id
  | succ m ih =>
    have key : (AmbientPoints.partialDeriv j)^[m + 1] =
        fun U => AmbientPoints.partialDeriv j ((AmbientPoints.partialDeriv j)^[m] U) := by
      funext U
      exact Function.iterate_succ_apply' _ _ _
    rw [key]
    exact (isLinearOnAllPartials_partialDeriv j).comp ih
theorem isLinearOnAllPartials_iteratedPartial (α : PowerSeries.MultiIndex D) :
    IsLinearOnAllPartials (iteratedPartial α) := by
  suffices hl : ∀ l : List (Fin D), IsLinearOnAllPartials
      (fun G => l.foldr (fun j H => (AmbientPoints.partialDeriv j)^[α j] H) G) from hl _
  intro l
  induction l with
  | nil => exact isLinearOnAllPartials_id
  | cons j l ih => exact (isLinearOnAllPartials_iterate j (α j)).comp ih
theorem IsLinearOnAllPartials.map_sum {L : ((Fin D → ℝ) → ℂ) → (Fin D → ℝ) → ℂ}
    (hL : IsLinearOnAllPartials L) {ι : Type} (S : Finset ι) (c : ι → ℂ)
    (G : ι → (Fin D → ℝ) → ℂ) (hG : ∀ k, AllPartialsCont (G k)) :
    AllPartialsCont (∑ k ∈ S, c k • G k) ∧ L (∑ k ∈ S, c k • G k) = ∑ k ∈ S, c k • L (G k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h0 := hL.2.2 0 0 allPartialsCont_zero
    exact ⟨by simpa using allPartialsCont_zero, by simpa using h0⟩
  | insert k S hk ih =>
    obtain ⟨ihc, ihL⟩ := ih
    have hck : AllPartialsCont (c k • G k) := (hG k).smul (c k)
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    refine ⟨hck.add ihc, ?_⟩
    rw [hL.2.1 _ _ hck ihc, hL.2.2 _ _ (hG k), ihL]
end Partials
theorem cutoffPartialSumsTendsto_holds (htop : TupleTopology.Holds)
    (hrest : TestFnOperations)
    (hleib : ProductNorms.ProductBoundsClaim)
    (hfour : FourierPartialSums.Statement) : CutoffPartialSumsTendsto := by
  intro s n ρ O hO F χ hχ
  rcases hO with ⟨hn, hρ, hbox⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 4 * ρ := ⟨4 * ρ, rfl⟩
  rw [← hPdef]
  have hP : 0 < P := by rw [hPdef]; positivity
  have hOpenBox : IsOpen (boxSet O) := isOpen_set_pi finite_univ fun i _ => (hbox i).1
  rcases (htop s .euclidean).1 n hn with ⟨hcover, hmaps, -, -, hderivs⟩
  rcases (hrest s .euclidean n hn).2.1 _ hOpenBox with ⟨-, -, hnorms, hmul⟩
  have hproj : Continuous (tupleProj s .euclidean n) := by
    simpa using (hmaps.2.2.2.2.2 (Tuple s .euclidean n) id).1 continuous_id
  obtain ⟨T, hT⟩ : ∃ T : Tuple s .euclidean n → ℂ, T = cutoffTensor χ := ⟨cutoffTensor χ, rfl⟩
  have hTfix : T * F.1 = F.1 := by
    subst hT
    exact hχ.2
  have hTmem : T ∈ testFns (boxSet O) := by
    subst hT
    exact ((hrest s .euclidean n hn).2.2.2 O (fun i y => (χ i y : ℂ)) (fun i => (hbox i).1)
      fun i => hχ.1 i).1
  have hinBox : boxSet O ⊆ fundamentalBoxPow s n P := by
    intro y hy i μ
    have hnorm : TorusMetric.euclidNormVec (y i) ≤ ρ := (hbox i).2 (hy i (mem_univ i))
    have hcoord : |coord s μ (y i)| ≤ ρ := by
      refine le_trans (Real.abs_le_sqrt ?_) hnorm
      exact Finset.single_le_sum
        (f := fun ν => (coord s ν (y i)) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
    obtain ⟨hlo, hhi⟩ := abs_le.1 hcoord
    constructor <;> rw [hPdef] <;> linarith
  have hFbox : F.1 ∈ testFns (fundamentalBoxPow s n P) := testFns_mono hinBox F.2
  obtain ⟨G, hG⟩ : ∃ G : ℕ+ → Tuple s .euclidean n → ℂ, G = fun (t : ℕ+) y =>
      ∑ k ∈ modesWithin (t : ℕ), fourierCoeff P F.1 k *
        tensorProd (s := s) (E := .euclidean)
          (fun i => fourierMode P (Torus.FourierBox.blockOf k i)) y := ⟨_, rfl⟩
  have hGlift : ∀ t, G t ∘ tupleProj s .euclidean n = fourierPartialSum P F.1 t := by
    intro t
    funext u
    rw [hG]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fourierMode_eq_tensorProd s P k u]
  have hGsmooth : ∀ t, IsSmoothFn (G t) := fun t => by
    change IsCnOn univ ⊤ (G t ∘ tupleProj s .euclidean n)
    rw [hGlift t]
    exact isCnOn_fourierPartialSum P F.1 t
  have hmodeSplit : ∀ (k : Fin (4 * n) → ℤ) (y : Tuple s .euclidean n),
      tensorProd (cutoffModeTuple P χ k) y = T y * tensorProd (s := s) (E := .euclidean)
        (fun i => fourierMode P (Torus.FourierBox.blockOf k i)) y := by
    intro k y
    rw [hT]
    exact Finset.prod_mul_distrib
  have hsplit : ∀ t, cutoffPartialSum P χ F.1 t = T * G t := by
    intro t
    funext y
    rw [hG]
    change ∑ k ∈ modesWithin (t : ℕ), fourierCoeff P F.1 k * tensorProd (cutoffModeTuple P χ k) y =
      T y * ∑ k ∈ modesWithin (t : ℕ), fourierCoeff P F.1 k * tensorProd (s := s) (E := .euclidean)
        (fun i => fourierMode P (Torus.FourierBox.blockOf k i)) y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hmodeSplit k y]
    ring
  obtain ⟨H, hH⟩ : ∃ H : ℕ+ → Tuple s .euclidean n → ℂ, H = fun t => G t - F.1 := ⟨_, rfl⟩
  have hFpart : AllPartialsCont (F.1 ∘ tupleProj s .euclidean n) := fun r => F.2.1.2 r le_top
  have hmodePart : ∀ k : Fin (4 * n) → ℤ, AllPartialsCont (fourierMode P k) := fun k r =>
    continuousPartialsUpTo_of_contDiff r (contDiff_fourierMode P k)
  have hHlift : ∀ t, H t ∘ tupleProj s .euclidean n =
      (∑ k ∈ modesWithin (t : ℕ), fourierCoeff P F.1 k • fourierMode P k) +
        (-1 : ℂ) • (F.1 ∘ tupleProj s .euclidean n) := by
    intro t
    funext u
    have hu : G t (tupleProj s .euclidean n u) = fourierPartialSum P F.1 t u :=
      congrFun (hGlift t) u
    rw [hH]
    simp only [Function.comp_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply,
      smul_eq_mul, hu, fourierPartialSum]
    ring
  have hHpart : ∀ t, AllPartialsCont (H t ∘ tupleProj s .euclidean n) := fun t => by
    rw [hHlift t]
    exact (isLinearOnAllPartials_id.map_sum _ _ _ hmodePart).1.add (hFpart.smul _)
  have hHsmooth : ∀ t, IsSmoothFn (H t) := fun t => ⟨isOpen_univ, fun m _ => hHpart t m⟩
  have hHderiv : ∀ (t : ℕ+) (α : PowerSeries.MultiIndex (4 * n)) (u : Fin (4 * n) → ℝ),
      multiDeriv α (H t) (tupleProj s .euclidean n u) =
        (∑ k ∈ modesWithin (t : ℕ), fourierCoeff P F.1 k * iteratedPartial α (fourierMode P k) u) -
          multiDeriv α F.1 (tupleProj s .euclidean n u) := by
    intro t α u
    have hLα := isLinearOnAllPartials_iteratedPartial α
    have hsumα := hLα.map_sum (modesWithin (t : ℕ)) (fourierCoeff P F.1) (fourierMode P) hmodePart
    have hsum0 := isLinearOnAllPartials_id.map_sum (modesWithin (t : ℕ)) (fourierCoeff P F.1)
      (fourierMode P) hmodePart
    have hHu : multiDeriv α (H t) (tupleProj s .euclidean n u) =
        iteratedPartial α (H t ∘ tupleProj s .euclidean n) u :=
      congrFun (multiDeriv_comp_tupleProj ((hderivs ⊤ (H t) (hHsmooth t)).1 α le_top).1.exists) u
    have hFu : multiDeriv α F.1 (tupleProj s .euclidean n u) =
        iteratedPartial α (F.1 ∘ tupleProj s .euclidean n) u :=
      congrFun (multiDeriv_comp_tupleProj ((hderivs ⊤ F.1 F.2.1).1 α le_top).1.exists) u
    rw [hHu, hFu, hHlift, hLα.2.1 _ _ hsum0.1 (hFpart.smul _), hLα.2.2 _ _ hFpart, hsumα.2]
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    ring
  have hboxNe : (fundamentalBoxPow s n P).Nonempty := by
    refine ⟨tupleProj s .euclidean n 0, ?_⟩
    refine (tupleProj_mem_fundamentalBoxPow_iff s n P 0).2 fun j => ?_
    constructor <;> simp <;> linarith
  have hTsupp : SupportedIn T (fundamentalBoxPow s n P) := hTmem.2.2.trans hinBox
  have hHbdd : ∀ (t : ℕ+) (α : PowerSeries.MultiIndex (4 * n)), ∃ C : ℝ,
      ∀ y ∈ fundamentalBoxPow s n P, ‖multiDeriv α (H t) y‖ ≤ C := by
    intro t α
    have hcont : Continuous (multiDeriv α (H t) ∘ tupleProj s .euclidean n) :=
      ((hderivs ⊤ (H t) (hHsmooth t)).1 α le_top).2.1.comp hproj
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := fun _ : Fin (4 * n) => -P / 2)
      (b := fun _ => P / 2)).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨C, ?_⟩
    intro y hy
    obtain ⟨u, rfl⟩ := hcover.1 y
    have hu := (tupleProj_mem_fundamentalBoxPow_iff s n P u).1 hy
    exact hC u ⟨fun j => (hu j).1.le, fun j => (hu j).2.le⟩
  refine ⟨fun t => ?_, F.2, ⟨closedSupport T, hTmem.2.1, hTmem.2.2, ?_, fun t => ?_⟩, fun r => ?_⟩
  · rw [hsplit]
    exact (hmul T (G t) hTmem.1 (hGsmooth t)).2.2.1 (Or.inl hTmem)
  · have hsuppF := (hmul T F.1 hTmem.1 F.2.1).2.1
    rw [hTfix] at hsuppF
    exact hsuppF.trans inter_subset_left
  · rw [hsplit]
    exact (hmul T (G t) hTmem.1 (hGsmooth t)).2.1.trans inter_subset_left
  obtain ⟨err, herr⟩ : ∃ err : PowerSeries.MultiIndex (4 * n) → ℕ+ → ℝ≥0∞, err = fun β (t : ℕ+) =>
      ⨆ v ∈ fundamentalCube (4 * n) P, ENNReal.ofReal
        ‖(∑ k ∈ modesWithin (t : ℕ), fourierCoeff P F.1 k * iteratedPartial β (fourierMode P k) v) -
          multiDeriv β F.1 (tupleProj s .euclidean n v)‖ := ⟨_, rfl⟩
  have hsumLim : ∀ S : Finset (PowerSeries.MultiIndex (4 * n)),
      Tendsto (fun t => ∑ β ∈ S, err β t) atTop (𝓝 0) := by
    intro S
    have hβ : ∀ β ∈ S, Tendsto (err β) atTop (𝓝 0) := by
      intro β _
      rw [herr]
      exact hfour s n hn P hP F.1 hFbox β
    simpa using tendsto_finsetSum S hβ
  have hHnorm : ∀ t, ProductNorms.cnNormOn r (fundamentalBoxPow s n P) (H t) ≤
      ∑ β ∈ Fintype.piFinset (fun _ : Fin (4 * n) => Finset.range (r + 1)), err β t := by
    intro t
    unfold ProductNorms.cnNormOn
    refine iSup_le fun α => iSup_le fun hα => iSup₂_le fun y hy => ?_
    have hαS : α ∈ Fintype.piFinset (fun _ : Fin (4 * n) => Finset.range (r + 1)) := by
      refine Fintype.mem_piFinset.2 fun j => Finset.mem_range.2 ?_
      have hj : α j ≤ α.order := Finset.single_le_sum (f := fun i => α i)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    obtain ⟨u, rfl⟩ := hcover.1 y
    have hu := (tupleProj_mem_fundamentalBoxPow_iff s n P u).1 hy
    rw [hHderiv]
    refine le_trans ?_ (Finset.single_le_sum (f := fun β => err β t) (fun _ _ => zero_le) hαS)
    rw [herr]
    exact le_iSup₂ (f := fun w _ => ENNReal.ofReal
      ‖(∑ k ∈ modesWithin (t : ℕ), fourierCoeff P F.1 k * iteratedPartial α (fourierMode P k) w) -
        multiDeriv α F.1 (tupleProj s .euclidean n w)‖) u hu
  have hTnorm : cnNorm r T < ⊤ := (hnorms T hTmem).2.2.2 r
  have hTcn : IsCn (r : ℕ∞) T := ⟨isOpen_univ, fun m _ => hTmem.1.2 m le_top⟩
  have hbound : Tendsto (fun t => 2 ^ r * cnNorm r T *
      ∑ β ∈ Fintype.piFinset (fun _ : Fin (4 * n) => Finset.range (r + 1)), err β t)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := 2 ^ r * cnNorm r T)
      (hsumLim (Fintype.piFinset fun _ : Fin (4 * n) => Finset.range (r + 1)))
      (Or.inr (ENNReal.mul_ne_top (by simp) hTnorm.ne))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => zero_le) fun t => ?_
  have hgap : cutoffPartialSum P χ F.1 t - F.1 = fun y => T y * H t y := by
    funext y
    have hy : T y * F.1 y = F.1 y := congrFun hTfix y
    rw [hsplit, hH]
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [mul_sub, hy]
  have hprodBound := ((hleib s .euclidean n hn r).2.1 T (H t) (fundamentalBoxPow s n P) hTcn
    ⟨isOpen_univ, fun m _ => hHsmooth t |>.2 m le_top⟩ hTnorm hboxNe hTsupp
    fun α _ => hHbdd t α).2
  change cnNorm r (cutoffPartialSum P χ F.1 t - F.1) ≤ _
  rw [hgap]
  refine hprodBound.trans ?_
  gcongr
  exact hHnorm t
end CutoffPartialSums
end YangMills.Construction.AmbientPoints
