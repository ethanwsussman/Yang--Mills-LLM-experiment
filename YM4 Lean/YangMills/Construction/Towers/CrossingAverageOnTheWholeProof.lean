import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATower
import YangMills.Construction.Towers.CountsOfCrossingsOnTheWhole
import YangMills.Construction.Towers.CrossingAverageOnASideProof
import YangMills.Construction.Towers.CrossingAverageOnTheWhole
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.CrossingSmoothingBound
open Matrices
open PeriodicOperators
open PeriodicOperators.Quotients (MapsFiniteNorm finiteNormSpace)
open InfiniteLattice (AmbientSpace)
theorem pauliCoeff_smul_pauliFamily (z : ℂ) (a' a : Fin 3) :
    pauliCoeff a' (z • ComplexMatrix2.pauliFamily a) = if a' = a then z else 0 := by apply _root_.YangMills.Construction.Tower.CrossingSmoothingContraction.pauliCoeff_smul_pauliFamily <;> assumption
theorem list_sum_map_eq_ite_of_nodup {α : Type} (g : α → ComplexMatrix2) (e₀ : α) (M : ComplexMatrix2)
    (l : List α) (hnd : l.Nodup) (hg : open Classical in ∀ β ∈ l, g β = if β = e₀ then M else 0) :
    open Classical in (l.map g).sum = if e₀ ∈ l then M else 0 := by apply _root_.YangMills.Construction.Tower.CrossingSmoothingContraction.list_sum_map_eq_ite_of_nodup <;> assumption
theorem piSingle_one_self {ι : Type} (d : DecidableEq ι) (j : ι) :
    @Pi.single ι (fun _ => ℂ) _ d j 1 j = 1 :=
  Pi.single_eq_same _ _
theorem piSingle_one_of_ne {ι : Type} (d : DecidableEq ι) {j j' : ι} (h : j' ≠ j) :
    @Pi.single ι (fun _ => ℂ) _ d j 1 j' = 0 :=
  Pi.single_eq_of_ne h _
variable {L k i : ℕ}
theorem ofCoeffs_basis_of_positive (a : Fin 3) (e₀ : PosEdge L k i)
    (f : Fin 3 × PosEdge L k i → ℂ)
    (hf : f (a, e₀) = 1) (hf' : ∀ q, q ≠ (a, e₀) → f q = 0) (β : FullSpace.Edge L k i)
    (hβ : β.IsPositivelyOriented) :
    open Classical in
    (FullSpace.edgePauliCoordinates L k i).ofCoeffs f β = if β = e₀.1 then ComplexMatrix2.pauliFamily a else 0 := by
  classical
  have key : ofPauliCoeffs f ⟨β, hβ⟩ = if β = e₀.1 then ComplexMatrix2.pauliFamily a else 0 := by
    unfold ofPauliCoeffs
    by_cases e : β = e₀.1
    · subst e
      rw [if_pos rfl, Finset.sum_eq_single a]
      · rw [show ((a, (⟨e₀.1, hβ⟩ : PosEdge L k i))) = (a, e₀) from rfl, hf, one_smul]
      · intro a' _ h
        have : ((a', (⟨e₀.1, hβ⟩ : PosEdge L k i))) ≠ (a, e₀) := fun q =>
          h (congrArg Prod.fst q)
        rw [hf' _ this, zero_smul]
      · simp
    · rw [if_neg e]
      refine Finset.sum_eq_zero fun a' _ => ?_
      have : ((a', (⟨β, hβ⟩ : PosEdge L k i))) ≠ (a, e₀) := fun q =>
        e (congrArg Subtype.val (congrArg Prod.snd q))
      rw [hf' _ this, zero_smul]
  dsimp only [FullSpace.edgePauliCoordinates]
  unfold FullSpace.extendOddly
  rw [if_pos hβ]
  beta_reduce
  rw [dif_pos hβ]
  exact key
theorem pauliCoeff_smoothing_basis (c : PosEdge L k (i + 1))
    (hform : ∀ x : FullSpace.Vertex L k i,
      x ∈ FullSpace.cubeVertices L (meshAt L k i) c.1.initial →
        (FullSpace.crossingPath c.1 x).Nodup ∧
          ∀ β ∈ FullSpace.crossingPath c.1 x, β.IsPositivelyOriented)
    (a' a : Fin 3) (e₀ : PosEdge L k i) (f : Fin 3 × PosEdge L k i → ℂ)
    (hf : f (a, e₀) = 1) (hf' : ∀ q, q ≠ (a, e₀) → f q = 0)
    (hT : (FullSpace.crossingSites L k i (i + 1) c.1 e₀.1).Finite) :
    pauliCoeff a'
        (((L : ℝ)⁻¹ • FullSpace.crossingSmoothing L (a := meshAt L k (i + 1))
          (a' := meshAt L k i) ((FullSpace.edgePauliCoordinates L k i).ofCoeffs f)) c.1) =
      if a' = a then
        ((((L : ℝ)⁻¹ * (L : ℝ) ^ (-4 : ℤ) *
          ((FullSpace.crossingSites L k i (i + 1) c.1 e₀.1).ncard : ℝ) : ℝ)) : ℂ)
      else 0 := by
  classical
  set F : InfiniteLattice.Link (meshAt L k i) → ComplexMatrix2 :=
    (FullSpace.edgePauliCoordinates L k i).ofCoeffs f with hF
  have h1 : i + 1 - i = 1 := by omega
  have hsum : ∑ᶠ x ∈ FullSpace.cubeVertices L (meshAt L k i) c.1.initial,
      FullSpace.edgeFormPathSum F (FullSpace.crossingPath c.1 x) =
      (((FullSpace.crossingSites L k i (i + 1) c.1 e₀.1).ncard : ℂ)) • ComplexMatrix2.pauliFamily a := by
    have hstep : ∀ x ∈ FullSpace.cubeVertices L (meshAt L k i) c.1.initial,
        FullSpace.edgeFormPathSum F (FullSpace.crossingPath c.1 x) =
          if e₀.1 ∈ FullSpace.crossingPath c.1 x then ComplexMatrix2.pauliFamily a else 0 := by
      intro x hx
      obtain ⟨hnd, hpos⟩ := hform x hx
      exact list_sum_map_eq_ite_of_nodup F e₀.1 (ComplexMatrix2.pauliFamily a) _ hnd fun β hβ =>
        ofCoeffs_basis_of_positive a e₀ f hf hf' β (hpos β hβ)
    rw [finsum_mem_congr rfl hstep]
    have hind : ∑ᶠ x ∈ FullSpace.cubeVertices L (meshAt L k i) c.1.initial,
        (if e₀.1 ∈ FullSpace.crossingPath c.1 x then ComplexMatrix2.pauliFamily a else 0) =
        ∑ᶠ x ∈ FullSpace.crossingSites L k i (i + 1) c.1 e₀.1, ComplexMatrix2.pauliFamily a := by
      rw [finsum_mem_def, finsum_mem_def]
      congr 1
      funext x
      by_cases hx : x ∈ FullSpace.cubeVertices L (meshAt L k i) c.1.initial
      · by_cases hb : e₀.1 ∈ FullSpace.crossingPath c.1 x
        · have : x ∈ FullSpace.crossingSites L k i (i + 1) c.1 e₀.1 :=
            ⟨by rw [h1]; exact hx, hb⟩
          rw [Set.indicator_of_mem hx, Set.indicator_of_mem this, if_pos hb]
        · have : x ∉ FullSpace.crossingSites L k i (i + 1) c.1 e₀.1 := fun q => hb q.2
          rw [Set.indicator_of_mem hx, Set.indicator_of_notMem this, if_neg hb]
      · have : x ∉ FullSpace.crossingSites L k i (i + 1) c.1 e₀.1 := fun q =>
          hx (by have := q.1; rw [h1] at this; exact this)
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem this]
    rw [hind, finsum_mem_eq_finite_toFinset_sum _ hT, Finset.sum_const,
      Set.ncard_eq_toFinset_card _ hT, Nat.cast_smul_eq_nsmul]
  have hreal : ∀ (r : ℝ) (M : ComplexMatrix2), r • M = (r : ℂ) • M := fun r M => by
    ext p q
    simp [Matrix.smul_apply]
  rw [Pi.smul_apply]
  unfold FullSpace.crossingSmoothing
  rw [hsum, hreal, smul_smul, smul_smul, pauliCoeff_smul_pauliFamily]
  by_cases e : a' = a
  · rw [if_pos e, if_pos e]
    simp only [PeriodicLattice.inverseFourthPowerWeight]
    push_cast
    ring
  · rw [if_neg e, if_neg e]
theorem conjKernel_apply (θ : AmbientSpace) (c : PosEdge L k (i + 1))
    (hform : ∀ x : FullSpace.Vertex L k i,
      x ∈ FullSpace.cubeVertices L (meshAt L k i) c.1.initial →
        (FullSpace.crossingPath c.1 x).Nodup ∧
          ∀ β ∈ FullSpace.crossingPath c.1 x, β.IsPositivelyOriented)
    (a' a : Fin 3) (e₀ : PosEdge L k i)
    (hT : (FullSpace.crossingSites L k i (i + 1) c.1 e₀.1).Finite) :
    conjKernel L k i θ (a', c) (a, e₀) =
      Complex.exp (bilinDot (toComplexVec θ)
          (toComplexVec ((c.1.initial : AmbientSpace) - (e₀.1.initial : AmbientSpace)))) *
        if a' = a then
          ((((L : ℝ)⁻¹ * (L : ℝ) ^ (-4 : ℤ) *
            ((FullSpace.crossingSites L k i (i + 1) c.1 e₀.1).ncard : ℝ) : ℝ)) : ℂ)
        else 0 := by
  classical
  rw [← pauliCoeff_smoothing_basis c hform a' a e₀ _ (piSingle_one_self _ (a, e₀))
    (fun q h => piSingle_one_of_ne _ h) hT]
  rfl
theorem norm_exp_bilinDot_le (θ v : AmbientSpace) {r : ℝ} (hv : ∀ μ, |v μ| ≤ r) :
    ‖Complex.exp (bilinDot (toComplexVec θ) (toComplexVec v))‖ ≤
      Real.exp (TorusMetric.l1NormVec θ * r) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have e : (bilinDot (toComplexVec θ) (toComplexVec v)).re = ∑ μ, θ μ * v μ := by
    unfold bilinDot toComplexVec
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [e]
  unfold TorusMetric.l1NormVec
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun μ _ => ?_
  calc θ μ * v μ ≤ |θ μ * v μ| := le_abs_self _
    _ = |θ μ| * |v μ| := abs_mul _ _
    _ ≤ |θ μ| * r := mul_le_mul_of_nonneg_left (hv μ) (abs_nonneg _)
theorem hasSum_of_finite_support_finsum {α : Type} (g : α → ℝ) (hg : (Function.support g).Finite)
    {s : ℝ} (h : ∑ᶠ x, g x = s) : HasSum g s := by
  have hs : HasSum g (∑ x ∈ hg.toFinset, g x) :=
    hasSum_sum_of_ne_finset_zero fun x hx => by simpa using hx
  rwa [← finsum_eq_sum_of_support_toFinset_subset g hg (Finset.Subset.refl _), h] at hs
theorem normBound_holds (hCounts : FullSpace.CrossingCounts)
    (hSchur : SchurTest.Holds)
    (hB : BlockPathContourPivotStatement) : NormBound := by
  classical
  intro L hL k i hik θ
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  have hspos : ∀ m, 0 < meshAt L k m := fun m => zpow_pos hLr _
  have hscale : meshAt L k (i + 1) = (L : ℝ) * meshAt L k i := by
    unfold meshAt
    rw [show ((i + 1 : ℕ) : ℤ) - (k : ℤ) = 1 + ((i : ℤ) - (k : ℤ)) by push_cast; ring,
      zpow_add₀ hLr.ne', zpow_one]
  have h1 : i + 1 - i = 1 := by omega
  have hBl : FullSpace.RefinedCubesPartition L k 1 (i + 1) :=
    (hB L hL k 1 (i + 1) (by omega) (by omega) hik).2.1
  have hsub : ∀ y : FullSpace.Vertex L k (i + 1),
      FullSpace.cubeOfOrder L (meshAt L k i) 1 y ⊆
        (InfiniteLattice.latticeSubgroup (meshAt L k i) : Set AmbientSpace) :=
    hBl.subset_sublattice
  have hnc : ∀ y : FullSpace.Vertex L k (i + 1),
      (FullSpace.cubeOfOrder L (meshAt L k i) 1 y).ncard = L ^ (4 * 1) := hBl.ncard_eq
  have himg : ∀ y : FullSpace.Vertex L k (i + 1),
      Subtype.val '' FullSpace.cubeVertices L (meshAt L k i) y =
        FullSpace.cubeOfOrder L (meshAt L k i) 1 y := by
    intro y
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      exact ⟨⟨p, hsub y hp⟩, hp, rfl⟩
  have hcard : ∀ y : FullSpace.Vertex L k (i + 1),
      (FullSpace.cubeVertices L (meshAt L k i) y).ncard = L ^ 4 := by
    intro y
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg y, hnc y]
  have hfin : ∀ y : FullSpace.Vertex L k (i + 1),
      (FullSpace.cubeVertices L (meshAt L k i) y).Finite := by
    intro y
    refine Set.finite_of_ncard_pos ?_
    rw [hcard y]
    positivity
  have hT : ∀ (c : PosEdge L k (i + 1)) (e₀ : PosEdge L k i),
      (FullSpace.crossingSites L k i (i + 1) c.1 e₀.1).Finite := by
    intro c e₀
    refine (hfin c.1.initial).subset fun x hx => ?_
    have := hx.1
    rw [h1] at this
    exact this
  obtain ⟨hrow, hcol, hform, hnear⟩ := hCounts L hL k i (i + 1) (by omega) (by omega) hik
  rw [h1] at hrow hcol
  have hform' : ∀ (c : PosEdge L k (i + 1)) (x : FullSpace.Vertex L k i),
      x ∈ FullSpace.cubeVertices L (meshAt L k i) c.1.initial →
        (FullSpace.crossingPath c.1 x).Nodup ∧
          ∀ β ∈ FullSpace.crossingPath c.1 x, β.IsPositivelyOriented := by
    intro c x hx
    exact hform c x (by rw [h1]; exact hx)
  obtain ⟨E, hE⟩ : ∃ E, E = TorusMetric.l1NormVec θ * (3 / 2 * meshAt L k (i + 1)) :=
    ⟨_, rfl⟩
  set K : ℝ := (L : ℝ)⁻¹ * (L : ℝ) ^ (-4 : ℤ) with hK
  have hExp : 0 < Real.exp E := Real.exp_pos _
  let n : PosEdge L k (i + 1) → PosEdge L k i → ℝ := fun c e₀ =>
    ((FullSpace.crossingSites L k i (i + 1) c.1 e₀.1).ncard : ℝ)
  let N : PosEdge L k (i + 1) → PosEdge L k i → ℝ := fun c e₀ =>
    (K * Real.exp E) * n c e₀
  have hKrow : K * (L : ℝ) ^ (5 * 1) = 1 := by
    rw [hK, zpow_neg]
    have : (L : ℝ) ^ (4 : ℤ) = (L : ℝ) ^ 4 := by norm_cast
    rw [this]
    field_simp
  have hKcol : K * (L : ℝ) ^ 1 = (L : ℝ) ^ (-4 : ℤ) := by
    rw [hK]
    field_simp
  have hrows : ∀ c, Summable (N c) ∧ ∑' e₀, N c e₀ ≤ Real.exp E := by
    intro c
    have hs : HasSum (n c) ((L : ℝ) ^ (5 * 1)) :=
      hasSum_of_finite_support_finsum _ (hrow c).1 (hrow c).2
    have hs' := hs.mul_left (K * Real.exp E)
    refine ⟨hs'.summable, le_of_eq ?_⟩
    rw [hs'.tsum_eq]
    calc K * Real.exp E * (L : ℝ) ^ (5 * 1) = (K * (L : ℝ) ^ (5 * 1)) * Real.exp E := by ring
      _ = Real.exp E := by rw [hKrow, one_mul]
  have hcols : ∀ e₀, Summable (fun c => N c e₀) ∧
      ∑' c, N c e₀ ≤ (L : ℝ) ^ (-4 : ℤ) * Real.exp E := by
    intro e₀
    have hs : HasSum (fun c => n c e₀) ((L : ℝ) ^ 1) :=
      hasSum_of_finite_support_finsum _ (hcol e₀).1 (hcol e₀).2
    have hs' := hs.mul_left (K * Real.exp E)
    refine ⟨hs'.summable, le_of_eq ?_⟩
    rw [hs'.tsum_eq]
    calc K * Real.exp E * (L : ℝ) ^ 1 = (K * (L : ℝ) ^ 1) * Real.exp E := by ring
      _ = (L : ℝ) ^ (-4 : ℤ) * Real.exp E := by rw [hKcol]
  have hoff : ∀ (a a' : Fin 3) (y : PosEdge L k (i + 1)) (x : PosEdge L k i),
      a' ≠ a → conjKernel L k i θ (a', y) (a, x) = 0 := by
    intro a a' y x h
    rw [conjKernel_apply θ y (hform' y) a' a x (hT y x), if_neg h, mul_zero]
  have hdiag : ∀ (a : Fin 3) (y : PosEdge L k (i + 1)) (x : PosEdge L k i),
      ‖conjKernel L k i θ (a, y) (a, x)‖ ≤ N y x := by
    intro a y x
    rw [conjKernel_apply θ y (hform' y) a a x (hT y x), if_pos rfl, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    by_cases hne : (FullSpace.crossingSites L k i (i + 1) y.1 x.1).Nonempty
    · have hexp : ‖Complex.exp (bilinDot (toComplexVec θ)
          (toComplexVec ((y.1.initial : AmbientSpace) - (x.1.initial : AmbientSpace))))‖ ≤
            Real.exp E := by
        rw [hE]
        refine norm_exp_bilinDot_le θ _ fun μ => ?_
        have h := hnear y x hne μ
        rw [Pi.sub_apply, abs_sub_comm]
        exact h
      have h0 : 0 ≤ K * n y x := by positivity
      calc _ ≤ Real.exp E * (K * n y x) := mul_le_mul_of_nonneg_right hexp h0
        _ = N y x := by
          show _ = K * Real.exp E * n y x
          ring
    · have hz : (FullSpace.crossingSites L k i (i + 1) y.1 x.1).ncard = 0 := by
        rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.ncard_empty]
      have hz' : n y x = 0 := by
        show (((FullSpace.crossingSites L k i (i + 1) y.1 x.1).ncard : ℕ) : ℝ) = 0
        rw [hz]
        simp
      show _ ≤ K * Real.exp E * n y x
      rw [hz', hz]
      simp
  have hLW : (L : ℝ) ^ 4 * (L : ℝ) ^ (-4 : ℤ) = 1 := by
    rw [show (-4 : ℤ) = -((4 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
    exact mul_inv_cancel₀ (pow_ne_zero _ hLr.ne')
  obtain ⟨C, hC⟩ : ∃ C, C = 2 * TorusMetric.l1NormVec θ * meshAt L k (i + 1) := ⟨_, rfl⟩
  have hθ : 0 ≤ TorusMetric.l1NormVec θ :=
    Finset.sum_nonneg fun μ _ => abs_nonneg _
  have hEC : E ≤ C := by
    rw [hE, hC]
    have := mul_nonneg hθ (hspos (i + 1)).le
    nlinarith
  have hprod : meshAt L k (i + 1) ^ 4 *
      (Real.exp E * ((L : ℝ) ^ (-4 : ℤ) * Real.exp E)) ≤
        Real.exp C ^ 2 * meshAt L k i ^ 4 := by
    have hexp : Real.exp E ^ 2 ≤ Real.exp C ^ 2 :=
      pow_le_pow_left₀ hExp.le (Real.exp_le_exp.2 hEC) 2
    rw [hscale]
    calc ((L : ℝ) * meshAt L k i) ^ 4 *
          (Real.exp E * ((L : ℝ) ^ (-4 : ℤ) * Real.exp E))
        = ((L : ℝ) ^ 4 * (L : ℝ) ^ (-4 : ℤ)) * (Real.exp E ^ 2 * meshAt L k i ^ 4) := by ring
      _ = Real.exp E ^ 2 * meshAt L k i ^ 4 := by rw [hLW, one_mul]
      _ ≤ Real.exp C ^ 2 * meshAt L k i ^ 4 :=
        mul_le_mul_of_nonneg_right hexp (pow_pos (hspos i) 4).le
  have key := hSchur.2 (PosEdge L k i) (PosEdge L k (i + 1)) (conjKernel L k i θ) N
    (colourEdges L k i).weightOf (colourEdges L k (i + 1)).weightOf
    (meshAt L k i ^ 4) (meshAt L k (i + 1) ^ 4) (Real.exp E)
    ((L : ℝ) ^ (-4 : ℤ) * Real.exp E) (Real.exp C)
    (pow_pos (hspos i) 4) (pow_pos (hspos (i + 1)) 4) (Real.exp_pos _).le
    (fun _ => rfl) (fun _ => rfl) hoff hdiag hrows hcols hprod
  refine ⟨fun f hf => key.1 f hf, (key.2 _).1, ?_⟩
  have h := (key.2 (finiteNormSpace (colourEdges L k i))).2
  rw [hC] at h
  exact h
end YangMills.Construction.Tower.CrossingSmoothingBound
end
