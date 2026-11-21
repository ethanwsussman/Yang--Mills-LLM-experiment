import YangMills.Construction.TorusOrFourSpace.CoefficientsOfTestFunctionsOnThePeriodBox
import YangMills.Construction.TorusOrFourSpace.FormsOfACutOffOnThePeriodBox
import YangMills.Construction.TorusOrFourSpace.ModesOfACutOffOnThePeriodBox
import YangMills.Construction.TorusOrFourSpace.PartialSumsUnderATestFunction
import YangMills.Construction.TorusOrFourSpace.WeightedSumOfCoefficientsOfATestFunction
import Mathlib
set_option autoImplicit false
open Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PeriodCell.CutoffForms
open Kind.Tuple
theorem tendsto_multilinear_of_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (f : MultilinearMap ℂ M ℂ) (N : ∀ i, M i → ℝ≥0∞) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hf : ∀ m, ENNReal.ofReal ‖f m‖ ≤ C * ∏ i, N i (m i))
    (b : ∀ i, M i) (hb : ∀ i, N i (b i) ≠ ⊤)
    {α : Type*} {l : Filter α} (d : α → ∀ i, M i)
    (hd : ∀ i, Tendsto (fun t => N i (d t i)) l (𝓝 0)) :
    Tendsto (fun t => f (d t + b)) l (𝓝 (f b)) := by
  have hpiece : ∀ s : Finset ι, s.Nonempty →
      Tendsto (fun t => f (s.piecewise (d t) b)) l (𝓝 0) := by
    intro s hne
    have hprod : Tendsto (fun t => ∏ i, N i (s.piecewise (d t) b i)) l
        (𝓝 (∏ i, (if i ∈ s then 0 else N i (b i)))) := by
      apply ENNReal.tendsto_finsetProd_of_ne_top
      · intro i _
        by_cases hi : i ∈ s
        · simpa [Finset.piecewise, hi] using hd i
        · simpa [Finset.piecewise, hi] using tendsto_const_nhds
      · intro i _
        by_cases hi : i ∈ s <;> simp [hi, hb i]
    obtain ⟨j, hj⟩ := hne
    have hzero : (∏ i, (if i ∈ s then (0 : ℝ≥0∞) else N i (b i))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
    rw [hzero] at hprod
    have hCt : Tendsto (fun t => C * ∏ i, N i (s.piecewise (d t) b i)) l (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hprod (Or.inr hC)
    have hz : Tendsto (fun t => ENNReal.ofReal ‖f (s.piecewise (d t) b)‖) l (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hCt (fun _ => bot_le)
        (fun t => hf _)
    have hr : Tendsto (fun t => ‖f (s.piecewise (d t) b)‖) l (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hz
      simpa [Function.comp_def, ENNReal.toReal_ofReal (norm_nonneg _)] using this
    exact tendsto_zero_iff_norm_tendsto_zero.2 hr
  have hsum : Tendsto (fun t => ∑ s : Finset ι, f (s.piecewise (d t) b)) l
      (𝓝 (∑ s : Finset ι, if s = ∅ then f b else 0)) := by
    apply tendsto_finsetSum
    intro s _
    by_cases hs : s = ∅
    · subst hs
      simpa using tendsto_const_nhds
    · simpa [hs] using hpiece s (Finset.nonempty_iff_ne_empty.2 hs)
  simpa [MultilinearMap.map_add_univ] using hsum
theorem subset_cell_of_norm_le {ρ : ℝ} (hρ : 0 < ρ) {U : Set (Fin 4 → ℝ)}
    (hU : ∀ u ∈ U, TorusMetric.euclidNormVec u ≤ ρ) : U ⊆ cell (4 * ρ) := by
  intro u hu μ
  have hle := hU u hu
  have habs : |u μ| ≤ TorusMetric.euclidNormVec u := by
    unfold TorusMetric.euclidNormVec
    exact Real.abs_le_sqrt
      (Finset.single_le_sum (f := fun μ => u μ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ μ))
  have hb := abs_le.1 (habs.trans hle)
  constructor <;> linarith [hb.1, hb.2]
theorem ofSingle_mem_cellTestFns {D : Params} {P : ℝ} {φ : Kind.euclidean.Pt D → ℂ}
    (hφ : φ ∈ singleTestFns D Kind.euclidean (cell P)) :
    ofSingle D Kind.euclidean φ ∈ cellTestFns D 1 P := by
  have e : cellPow D 1 P = singleSet D Kind.euclidean (cell P) := by
    ext y
    constructor
    · intro hy
      exact hy _
    · intro hy i
      have hi : i = ⟨0, (1 : ℕ+).pos⟩ := Fin.ext (by
        have hlt := i.2
        have hone : (((1 : ℕ+)) : ℕ) = 1 := rfl
        show (i : ℕ) = 0
        omega)
      rw [hi]
      exact hy
  show ofSingle D Kind.euclidean φ ∈
    Kind.Tuple.testFns D Kind.euclidean (cellPow D 1 P)
  rw [e]
  exact hφ
def blockEquiv (n : ℕ+) : IntCoords n ≃ (Fin (n : ℕ) → IntCoords 1) where
  toFun k i := k.block i
  invFun r j := r ⟨(j : ℕ) / 4, by have := j.2; omega⟩
    ⟨(j : ℕ) % 4, by have hone : (((1 : ℕ+)) : ℕ) = 1 := rfl; omega⟩
  left_inv k := by
    funext j
    exact congrArg k (Fin.ext (Nat.div_add_mod _ 4))
  right_inv r := by
    funext i μ
    have hlt := μ.2
    have hone : (((1 : ℕ+)) : ℕ) = 1 := rfl
    exact congrArg₂ (fun (a : Fin (n : ℕ)) (c : Fin (4 * ((1 : ℕ+) : ℕ))) => r a c)
      (Fin.ext (by show (4 * (i : ℕ) + (μ : ℕ)) / 4 = i; omega))
      (Fin.ext (by show (4 * (i : ℕ) + (μ : ℕ)) % 4 = μ; omega))
theorem mem_cubeUpTo_iff_blocks {n : ℕ+} (t : ℕ+) (k : IntCoords n) :
    k ∈ IntCoords.cubeUpTo t ↔
      blockEquiv n k ∈ Fintype.piFinset fun _ => IntCoords.cubeUpTo (p := 1) t := by
  simp only [IntCoords.cubeUpTo, Fintype.mem_piFinset]
  constructor
  · intro hk i μ
    exact hk _
  · intro hk j
    have := hk ⟨(j : ℕ) / 4, by have := j.2; omega⟩
      ⟨(j : ℕ) % 4, by have hone : (((1 : ℕ+)) : ℕ) = 1 := rfl; omega⟩
    have e : k j = blockEquiv n k ⟨(j : ℕ) / 4, by have := j.2; omega⟩
        ⟨(j : ℕ) % 4, by have hone : (((1 : ℕ+)) : ℕ) = 1 := rfl; omega⟩ :=
      congrArg k (Fin.ext (Nat.div_add_mod _ 4).symm)
    rw [e]
    exact this
theorem tendsto_cubeUpTo {n : ℕ+} :
    Tendsto (fun t : ℕ+ => (IntCoords.cubeUpTo t : Finset (IntCoords n))) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone
  · intro t t' htt k hk
    rw [IntCoords.mem_cubeUpTo] at hk ⊢
    exact hk.trans (by exact_mod_cast htt)
  · intro k
    refine ⟨Nat.succPNat k.maxAbs, ?_⟩
    rw [IntCoords.mem_cubeUpTo, Nat.succPNat_coe]
    omega
theorem block_zero_of_one (u : Coords 1) :
    (Coords.block u ⟨0, (1 : ℕ+).pos⟩ : Fin 4 → ℝ) = u := by
  funext μ
  exact congrArg u (Fin.ext (by show 4 * 0 + (μ : ℕ) = μ; omega))
def modeComponents (D : Params) {n : ℕ+} (ρ : ℝ) (χ : Fin (n : ℕ) → Kind.euclidean.Pt D → ℝ)
    (k : IntCoords n) : Fin (n : ℕ) → Kind.euclidean.Pt D → ℂ :=
  fun i => cutoffMode D (4 * ρ) (χ i) (k.block i)
def formSeries (D : Params) {n : ℕ+} (ρ : ℝ)
    (Bc : (Fin (n : ℕ) → Kind.euclidean.Pt D → ℂ) → ℂ)
    (χ : Fin (n : ℕ) → Kind.euclidean.Pt D → ℝ)
    (F : Kind.euclidean.Tuple D n → ℂ) : ℂ :=
  ∑' k : IntCoords n, fourierCoeff D (4 * ρ) F k * Bc (modeComponents D ρ χ k)
def toMultilinear {D : Params} {E : Kind} {n : ℕ+} {O : Fin (n : ℕ) → Set (E.Pt D)} {c : ℝ}
    {Bc : (Fin (n : ℕ) → E.Pt D → ℂ) → ℂ} (hB : IsBoundedComplexMultiform D E O c Bc)
    (S : ∀ _ : Fin (n : ℕ), Submodule ℂ (E.Pt D → ℂ))
    (hS : ∀ i, (S i : Set (E.Pt D → ℂ)) = complexC1SupportedIn D E (O i)) :
    MultilinearMap ℂ (fun i => S i) ℂ where
  toFun g := Bc fun i => (g i).1
  map_update_add' := by
    intro inst g l x y
    have hinst : inst = fun a b => instDecidableEqFin _ a b := Subsingleton.elim _ _
    subst hinst
    have hmem : ∀ i (z : S i), z.1 ∈ complexC1SupportedIn D E (O i) := fun i z => by
      rw [← hS i]
      exact z.2
    have e : ∀ z : S l, (fun i => (Function.update g l z i).1) =
        Function.update (fun i => (g i).1) l z.1 := by
      intro z
      funext i
      by_cases hil : i = l
      · subst hil
        simp
      · simp [Function.update_of_ne hil]
    simp only [e]
    exact hB.1 _ l x.1 y.1 (fun i => hmem i _) (hmem l x) (hmem l y)
  map_update_smul' := by
    intro inst g l a x
    have hinst : inst = fun a b => instDecidableEqFin _ a b := Subsingleton.elim _ _
    subst hinst
    have hmem : ∀ i (z : S i), z.1 ∈ complexC1SupportedIn D E (O i) := fun i z => by
      rw [← hS i]
      exact z.2
    have e : ∀ z : S l, (fun i => (Function.update g l z i).1) =
        Function.update (fun i => (g i).1) l z.1 := by
      intro z
      funext i
      by_cases hil : i = l
      · subst hil
        simp
      · simp [Function.update_of_ne hil]
    simp only [e]
    exact hB.2.1 _ l x.1 a (fun i => hmem i _) (hmem l x)
theorem norm_form_modeComponents_le (hclass : ComplexSupportedClassesClaim)
    (hmodes : CutoffModeBounds) {D : Params} {n : ℕ+} {ρ c : ℝ} (hρ : 0 < ρ)
    {O : Fin (n : ℕ) → Set (Kind.euclidean.Pt D)}
    (hO : ∀ i, Kind.IsOpenQ D Kind.euclidean (O i)) (hcell : ∀ i, O i ⊆ cell (4 * ρ))
    {Bc : (Fin (n : ℕ) → Kind.euclidean.Pt D → ℂ) → ℂ}
    (hB : IsBoundedComplexMultiform D Kind.euclidean O c Bc)
    {χ : Fin (n : ℕ) → Kind.euclidean.Pt D → ℝ} (hχ : IsCutoffFamily D Kind.euclidean O χ)
    (k : IntCoords n) :
    ‖Bc (modeComponents D ρ χ k)‖ ≤
      (ENNReal.ofReal (2 ^ (n : ℕ) * c) *
        ∏ i, c1NormSingleReal D Kind.euclidean (χ i)).toReal * freqWeight ρ k := by
  have hm := fun i => hmodes D ρ hρ (O i) (hO i) (hcell i)
  have hfacts := fun i => hclass D Kind.euclidean (O i) (hO i)
  have hmem : ∀ i, modeComponents D ρ χ k i ∈ complexC1SupportedIn D Kind.euclidean (O i) := fun i =>
    (hfacts i).2.2.1 (((hm i).2.2 (χ i) (hχ i)).1 _ ((hm i).2.1 (k.block i))).1
  have hfin : ∀ i, c1NormSingleReal D Kind.euclidean (χ i) ≠ ⊤ := fun i =>
    ((hfacts i).2.2.2.2.2.2.2 _ ((hfacts i).2.2.1 (hχ i))).ne
  have hA : ENNReal.ofReal (2 ^ (n : ℕ) * c) *
      ∏ i, c1NormSingleReal D Kind.euclidean (χ i) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.prod_ne_top fun i _ => hfin i)
  have hscale : 0 < cutoffScale ρ := by
    unfold cutoffScale
    have := Real.pi_pos
    positivity
  have hnn : ∀ i : Fin (n : ℕ),
      0 ≤ 1 + intVecNorm (k.block i) / cutoffScale ρ := fun i => by
    have : 0 ≤ intVecNorm (k.block i) := Real.sqrt_nonneg _
    positivity
  have hw : 0 ≤ freqWeight ρ k := Finset.prod_nonneg fun i _ => hnn i
  have hbound := hB.2.2 _ hmem
  have hprod : ∏ i, c1NormSingle D Kind.euclidean (modeComponents D ρ χ k i) ≤
      (∏ i, c1NormSingleReal D Kind.euclidean (χ i)) * ENNReal.ofReal (freqWeight ρ k) := by
    unfold freqWeight
    rw [ENNReal.ofReal_prod_of_nonneg fun i _ => hnn i, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod' fun i _ => ((hm i).2.2 (χ i) (hχ i)).2 (k.block i)
  have hle : ENNReal.ofReal ‖Bc (modeComponents D ρ χ k)‖ ≤
      (ENNReal.ofReal (2 ^ (n : ℕ) * c) *
        ∏ i, c1NormSingleReal D Kind.euclidean (χ i)) * ENNReal.ofReal (freqWeight ρ k) := by
    rw [mul_assoc]
    exact hbound.trans (mul_le_mul_right hprod _)
  have hreal := (ENNReal.ofReal_le_iff_le_toReal
    (ENNReal.mul_ne_top hA ENNReal.ofReal_ne_top)).1 hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hw] at hreal
theorem formSeries_tensorProd (hcoef : FourierCoeffBounds)
    (hclass : ComplexSupportedClassesClaim) (hmodes : CutoffModeBounds)
    (htrunc : FourierTruncationsConverge) {D : Params} {n : ℕ+} {ρ c : ℝ}
    (hρ : 0 < ρ) {O : Fin (n : ℕ) → Set (Kind.euclidean.Pt D)}
    (hO : ∀ i, Kind.IsOpenQ D Kind.euclidean (O i)) (hcell : ∀ i, O i ⊆ cell (4 * ρ))
    {Bc : (Fin (n : ℕ) → Kind.euclidean.Pt D → ℂ) → ℂ}
    (hB : IsBoundedComplexMultiform D Kind.euclidean O c Bc)
    {χ : Fin (n : ℕ) → Kind.euclidean.Pt D → ℝ} (hχ : IsCutoffFamily D Kind.euclidean O χ)
    {h : Fin (n : ℕ) → Kind.euclidean.Pt D → ℂ}
    (hh : ∀ i, h i ∈ singleTestFns D Kind.euclidean (cell (4 * ρ)))
    (hs : Summable fun k : IntCoords n =>
      fourierCoeff D (4 * ρ) (tensorProd D Kind.euclidean h) k * Bc (modeComponents D ρ χ k)) :
    formSeries D ρ Bc χ (tensorProd D Kind.euclidean h) = Bc fun i y => (χ i y : ℂ) * h i y := by
  have hP : 0 < 4 * ρ := by positivity
  choose S hS using fun i => (hclass D Kind.euclidean (O i) (hO i)).1
  have hmem : ∀ i u, u ∈ complexC1SupportedIn D Kind.euclidean (O i) → u ∈ S i := fun i u hu => by
    rw [← hS i] at hu
    exact hu
  have hmem' : ∀ i (z : S i), z.1 ∈ complexC1SupportedIn D Kind.euclidean (O i) := fun i z => by
    rw [← hS i]
    exact z.2
  have htest := fun i => (hclass D Kind.euclidean (O i) (hO i)).2.2.1
  have hfinite := fun i => (hclass D Kind.euclidean (O i) (hO i)).2.2.2.2.2.2.2
  have hm := fun i => hmodes D ρ hρ (O i) (hO i) (hcell i)
  let f := toMultilinear hB S hS
  let mode : ∀ i, IntCoords 1 → S i := fun i κ =>
    ⟨cutoffMode D (4 * ρ) (χ i) κ,
      hmem i _ (htest i (((hm i).2.2 (χ i) (hχ i)).1 _ ((hm i).2.1 κ)).1)⟩
  let b : ∀ i, S i := fun i =>
    ⟨fun y => (χ i y : ℂ) * h i y, hmem i _ (htest i (((hm i).2.2 (χ i) (hχ i)).1 (h i) (hh i).1).1)⟩
  let co : Fin (n : ℕ) → IntCoords 1 → ℂ := fun i κ =>
    fourierCoeff (p := 1) D (4 * ρ) (ofSingle D Kind.euclidean (h i)) κ
  let a : ℕ+ → ∀ i, S i := fun t i => ∑ κ ∈ IntCoords.cubeUpTo t, co i κ • mode i κ
  let d : ℕ+ → ∀ i, S i := fun t i => a t i - b i
  have hexpand : ∀ t : ℕ+, f (a t) = ∑ k ∈ IntCoords.cubeUpTo t,
      fourierCoeff D (4 * ρ) (tensorProd D Kind.euclidean h) k * Bc (modeComponents D ρ χ k) := by
    intro t
    refine (f.map_sum_finset (fun i κ => co i κ • mode i κ)
      (fun _ => IntCoords.cubeUpTo t)).trans ?_
    refine (Finset.sum_equiv (blockEquiv n) (mem_cubeUpTo_iff_blocks t) ?_).symm
    intro k _
    rw [f.map_smul_univ, ((hcoef D n (4 * ρ) hP).2.2.2.2.2.2.2.2.2.2 h hh).2 k]
    rfl
  have hlim1 : Tendsto (fun t : ℕ+ => ∑ k ∈ IntCoords.cubeUpTo t,
      fourierCoeff D (4 * ρ) (tensorProd D Kind.euclidean h) k * Bc (modeComponents D ρ χ k)) atTop
      (𝓝 (formSeries D ρ Bc χ (tensorProd D Kind.euclidean h))) :=
    hs.hasSum.comp tendsto_cubeUpTo
  have hd : ∀ i, Tendsto (fun t => c1NormSingle D Kind.euclidean (d t i).1) atTop (𝓝 0) := by
    intro i
    let G : ℕ+ → Kind.euclidean.Tuple D 1 → ℂ := fun t y =>
      ∑ κ ∈ IntCoords.cubeUpTo t, co i κ * fourierCharR4 (4 * ρ) κ (y ⟨0, (1 : ℕ+).pos⟩)
    have hG : ∀ t, G t ∘ proj D Kind.euclidean =
        fourierPartialSum D (4 * ρ) (ofSingle D Kind.euclidean (h i)) t := by
      intro t
      funext u
      refine Finset.sum_congr rfl fun κ _ => ?_
      have e : (proj D Kind.euclidean u) ⟨0, (1 : ℕ+).pos⟩ = u := block_zero_of_one u
      show co i κ * fourierCharR4 (4 * ρ) κ
        ((proj D Kind.euclidean u) ⟨0, (1 : ℕ+).pos⟩) = _
      rw [e]
      rfl
    have hlim := (htrunc D 1 (4 * ρ) hP
      (ofSingle D Kind.euclidean fun y => (χ i y : ℂ))
      (ofSingle_mem_cellTestFns ((hm i).1 (hχ i)))
      (ofSingle D Kind.euclidean (h i)) (ofSingle_mem_cellTestFns (hh i)) G hG).2 1
    refine hlim.congr fun t => ?_
    unfold c1NormSingle
    congr 1
    funext y
    show (χ i (y ⟨0, (1 : ℕ+).pos⟩) : ℂ) * (G t y - h i (y ⟨0, (1 : ℕ+).pos⟩)) =
      (d t i).1 (y ⟨0, (1 : ℕ+).pos⟩)
    simp only [d, a, b, mode, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul,
      Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, G, cutoffMode, mul_sub,
      Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun κ _ => by ring
  have hlim2 : Tendsto (fun t => f (d t + b)) atTop (𝓝 (f b)) :=
    tendsto_multilinear_of_bound f (fun i z => c1NormSingle D Kind.euclidean z.1)
      (ENNReal.ofReal (2 ^ (n : ℕ) * c)) ENNReal.ofReal_ne_top
      (fun m => hB.2.2 _ fun i => hmem' i _) b (fun i => (hfinite i _ (hmem' i _)).ne) d hd
  have hab : ∀ t, d t + b = a t := fun t => by
    funext i
    exact sub_add_cancel _ _
  have hlim3 : Tendsto (fun t : ℕ+ => ∑ k ∈ IntCoords.cubeUpTo t,
      fourierCoeff D (4 * ρ) (tensorProd D Kind.euclidean h) k * Bc (modeComponents D ρ χ k)) atTop
      (𝓝 (f b)) :=
    hlim2.congr fun t => by rw [hab t, hexpand t]
  exact tendsto_nhds_unique hlim1 hlim3
theorem cutoffFormsExist (hcoef : FourierCoeffBounds)
    (hclass : ComplexSupportedClassesClaim) (hmodes : CutoffModeBounds)
    (htrunc : FourierTruncationsConverge)
    (hweights : WeightedFourierSum) : CutoffFormsExist := by
  intro D n ρ c hρ hc O hO hball Bc hB
  refine ⟨formSeries D ρ Bc, fun χ hχ => ?_⟩
  have hP : 0 < 4 * ρ := by positivity
  have hcell : ∀ i, O i ⊆ cell (4 * ρ) := fun i => subset_cell_of_norm_le hρ (hball i)
  have hfacts := fun i => hclass D Kind.euclidean (O i) (hO i)
  have hfin : ∀ i, c1NormSingleReal D Kind.euclidean (χ i) ≠ ⊤ := fun i =>
    ((hfacts i).2.2.2.2.2.2.2 _ ((hfacts i).2.2.1 (hχ i))).ne
  set A : ℝ≥0∞ := ENNReal.ofReal (2 ^ (n : ℕ) * c) *
    ∏ i, c1NormSingleReal D Kind.euclidean (χ i) with hAdef
  have hA : A ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.prod_ne_top fun i _ => hfin i)
  have hbd := norm_form_modeComponents_le hclass hmodes hρ hO hcell hB hχ
  have hterm : ∀ F (k : IntCoords n),
      ‖fourierCoeff D (4 * ρ) F k * Bc (modeComponents D ρ χ k)‖ ≤
        A.toReal * (‖fourierCoeff D (4 * ρ) F k‖ * freqWeight ρ k) := by
    intro F k
    rw [norm_mul]
    calc ‖fourierCoeff D (4 * ρ) F k‖ * ‖Bc (modeComponents D ρ χ k)‖
        ≤ ‖fourierCoeff D (4 * ρ) F k‖ * (A.toReal * freqWeight ρ k) :=
          mul_le_mul_of_nonneg_left (hbd k) (norm_nonneg _)
      _ = _ := by ring
  have hsn : ∀ F ∈ cellTestFns D n (4 * ρ), Summable fun k : IntCoords n =>
      ‖fourierCoeff D (4 * ρ) F k * Bc (modeComponents D ρ χ k)‖ := fun F hF =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm F)
      ((hweights D n ρ hρ F hF).1.mul_left _)
  have hsum : ∀ F ∈ cellTestFns D n (4 * ρ), Summable fun k : IntCoords n =>
      fourierCoeff D (4 * ρ) F k * Bc (modeComponents D ρ χ k) := fun F hF => (hsn F hF).of_norm
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro F G H hH
    show formSeries D ρ Bc χ H.1 = formSeries D ρ Bc χ F.1 + formSeries D ρ Bc χ G.1
    unfold formSeries
    rw [← (hsum F.1 F.2).tsum_add (hsum G.1 G.2)]
    refine tsum_congr fun k => ?_
    have e : fourierCoeff D (4 * ρ) H.1 k =
        fourierCoeff D (4 * ρ) F.1 k + fourierCoeff D (4 * ρ) G.1 k :=
      ((hcoef D n (4 * ρ) hP).1 k).1 F G H hH
    rw [e, add_mul]
  · intro a F H hH
    show formSeries D ρ Bc χ H.1 = a * formSeries D ρ Bc χ F.1
    unfold formSeries
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    have e : fourierCoeff D (4 * ρ) H.1 k = a * fourierCoeff D (4 * ρ) F.1 k :=
      ((hcoef D n (4 * ρ) hP).1 k).2 a F H hH
    rw [e, mul_assoc]
  · intro F hF
    obtain ⟨hW, hWb⟩ := hweights D n ρ hρ F hF
    have hnorm : ‖formSeries D ρ Bc χ F‖ ≤ A.toReal *
        ∑' k : IntCoords n, ‖fourierCoeff D (4 * ρ) F k‖ * freqWeight ρ k := by
      rw [← tsum_mul_left]
      exact (norm_tsum_le_tsum_norm (hsn F hF)).trans
        ((hsn F hF).tsum_le_tsum (hterm F) (hW.mul_left _))
    calc ENNReal.ofReal ‖formSeries D ρ Bc χ F‖
        ≤ ENNReal.ofReal (A.toReal *
            ∑' k : IntCoords n, ‖fourierCoeff D (4 * ρ) F k‖ * freqWeight ρ k) :=
          ENNReal.ofReal_le_ofReal hnorm
      _ = A * ENNReal.ofReal
            (∑' k : IntCoords n, ‖fourierCoeff D (4 * ρ) F k‖ * freqWeight ρ k) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hA]
      _ ≤ A * (ENNReal.ofReal (cutoffBound n ρ) *
            cNorm D Kind.euclidean (5 * (n : ℕ) + 1) F) :=
          mul_le_mul_right hWb _
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ (n : ℕ) * c), hAdef]
          ring
  · intro h hh
    obtain ⟨hT, -⟩ := (hcoef D n (4 * ρ) hP).2.2.2.2.2.2.2.2.2.2 h hh
    exact formSeries_tensorProd hcoef hclass hmodes htrunc hρ hO hcell hB hχ hh (hsum _ hT)
end YangMills.Construction.PeriodicSpace.PeriodCell.CutoffForms
