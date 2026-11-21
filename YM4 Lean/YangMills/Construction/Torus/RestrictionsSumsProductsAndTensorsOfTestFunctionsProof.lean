import YangMills.Construction.Torus.CoveringMapOpenAndCompactSetsAndDerivativesOfTuplesProof
import YangMills.Construction.Continuum.TensorProductsAcrossTheTimeZeroPlaneProof
import YangMills.Construction.Torus.CoveringMapOpenAndCompactSetsAndDerivativesOfTuples
import YangMills.Construction.Torus.PeriodBoxModesCoefficientsAndPartialSums
import YangMills.Construction.Torus.RestrictionsSumsProductsAndTensorsOfTestFunctions
import Mathlib
set_option autoImplicit false
open Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.AmbientPoints
namespace SmoothCalculus
section EuclideanCoordinates
variable {D : ℕ}
abbrev CnOnSpace (n : ℕ) (G : (Fin D → ℝ) → ℂ) : Prop :=
  ContinuousPartialsUpTo (Set.univ : Set (Fin D → ℝ)) n G
def SmoothOnSpace (G : (Fin D → ℝ) → ℂ) : Prop := ∀ n, CnOnSpace n G
theorem continuous_of_cnOnSpace {n : ℕ} {G : (Fin D → ℝ) → ℂ} (hG : CnOnSpace n G) :
    Continuous G :=
  continuousOn_univ.mp hG.continuousOn
theorem hasLineDerivAt_of_cnOnSpace {n : ℕ} {G : (Fin D → ℝ) → ℂ} (hG : CnOnSpace (n + 1) G)
    (j : Fin D) (x : Fin D → ℝ) :
    HasLineDerivAt ℝ G (partialDeriv j G x) x (Pi.single j 1) :=
  ((hG.2 j).1 x (Set.mem_univ x)).hasLineDerivAt
theorem cnOnSpace_succ_of_hasLineDerivAt {n : ℕ} {G : (Fin D → ℝ) → ℂ}
    {G' : Fin D → (Fin D → ℝ) → ℂ}
    (hc : Continuous G) (hd : ∀ j x, HasLineDerivAt ℝ G (G' j x) x (Pi.single j 1))
    (hn : ∀ j, CnOnSpace n (G' j)) : CnOnSpace (n + 1) G := by
  refine ⟨hc.continuousOn, fun j => ⟨fun x _ => (hd j x).lineDifferentiableAt, ?_⟩⟩
  have hEq : partialDeriv j G = G' j := funext fun x => (hd j x).lineDeriv
  rw [hEq]
  exact hn j
theorem cnOnSpace_const (n : ℕ) (c : ℂ) : CnOnSpace n (fun _ : Fin D → ℝ => c) := by
  induction n generalizing c with
  | zero => exact continuousOn_const
  | succ n ih =>
    refine cnOnSpace_succ_of_hasLineDerivAt (G' := fun _ _ => 0) continuous_const
      (fun j x => hasDerivAt_const _ _) (fun _ => ih 0)
theorem cnOnSpace_add {n : ℕ} : ∀ {G H : (Fin D → ℝ) → ℂ}, CnOnSpace n G →
    CnOnSpace n H → CnOnSpace n (G + H) := by
  induction n with
  | zero => exact fun hG hH => ContinuousOn.add hG hH
  | succ n ih =>
    intro G H hG hH
    refine cnOnSpace_succ_of_hasLineDerivAt
      (G' := fun j => partialDeriv j G + partialDeriv j H)
      ((continuous_of_cnOnSpace hG).add (continuous_of_cnOnSpace hH))
      (fun j x => ?_) (fun j => ih (hG.2 j).2 (hH.2 j).2)
    exact HasDerivAt.add (hasLineDerivAt_of_cnOnSpace hG j x) (hasLineDerivAt_of_cnOnSpace hH j x)
theorem cnOnSpace_comp_clm (L : ℂ →L[ℝ] ℂ) {n : ℕ} : ∀ {G : (Fin D → ℝ) → ℂ}, CnOnSpace n G →
    CnOnSpace n (L ∘ G) := by
  induction n with
  | zero => exact fun hG => L.continuous.comp_continuousOn hG
  | succ n ih =>
    intro G hG
    refine cnOnSpace_succ_of_hasLineDerivAt (G' := fun j => L ∘ partialDeriv j G)
      (L.continuous.comp (continuous_of_cnOnSpace hG))
      (fun j x => ?_) (fun j => ih (hG.2 j).2)
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasLineDerivAt_of_cnOnSpace hG j x)
theorem hasLineDerivAt_mul_fn {G H : (Fin D → ℝ) → ℂ} {a b : ℂ} {x v : Fin D → ℝ}
    (hG : HasLineDerivAt ℝ G a x v) (hH : HasLineDerivAt ℝ H b x v) :
    HasLineDerivAt ℝ (G * H) (a * H x + G x * b) x v := by
  have hprod := HasDerivAt.mul hG hH
  have hx : x + (0 : ℝ) • v = x := by simp
  simp only [hx] at hprod
  exact hprod
theorem cnOnSpace_mul {n : ℕ} : ∀ {G H : (Fin D → ℝ) → ℂ}, CnOnSpace n G →
    CnOnSpace n H → CnOnSpace n (G * H) := by
  induction n with
  | zero => exact fun hG hH => ContinuousOn.mul hG hH
  | succ n ih =>
    intro G H hG hH
    refine cnOnSpace_succ_of_hasLineDerivAt
      (G' := fun j => partialDeriv j G * H + G * partialDeriv j H)
      ((continuous_of_cnOnSpace hG).mul (continuous_of_cnOnSpace hH))
      (fun j x => hasLineDerivAt_mul_fn (hasLineDerivAt_of_cnOnSpace hG j x)
        (hasLineDerivAt_of_cnOnSpace hH j x))
      (fun j => cnOnSpace_add (ih (hG.2 j).2 (ContinuousPartialsUpTo.of_succ hH))
        (ih (ContinuousPartialsUpTo.of_succ hG) (hH.2 j).2))
theorem SmoothOnSpace.deriv_coord {G : (Fin D → ℝ) → ℂ} (hG : SmoothOnSpace G) (j : Fin D) :
    SmoothOnSpace (partialDeriv j G) := by apply _root_.YangMills.Construction.AmbientPoints.TupleTopology.AllContinuousPartials.partialDeriv <;> assumption
theorem SmoothOnSpace.lineDiffAt {G : (Fin D → ℝ) → ℂ} (hG : SmoothOnSpace G) (j : Fin D)
    (x : Fin D → ℝ) : LineDifferentiableAt ℝ G x (Pi.single j 1) :=
  ((hG 1).2 j).1 x (Set.mem_univ x)
theorem SmoothOnSpace.iterate_coord {G : (Fin D → ℝ) → ℂ} (hG : SmoothOnSpace G) (j : Fin D)
    (k : ℕ) : SmoothOnSpace ((partialDeriv j)^[k] G) := by apply _root_.YangMills.Construction.AmbientPoints.TupleTopology.allContinuousPartials_iterate <;> assumption
theorem SmoothOnSpace.foldr_coords {G : (Fin D → ℝ) → ℂ} (hG : SmoothOnSpace G)
    (γ : PowerSeries.MultiIndex D) (l : List (Fin D)) :
    SmoothOnSpace (l.foldr (fun j H => (partialDeriv j)^[γ j] H) G) := by apply _root_.YangMills.Construction.AmbientPoints.TupleTopology.allContinuousPartials_foldr <;> assumption
end EuclideanCoordinates
section CoordinateBlocks
variable {D₁ D₂ : ℕ}
def headCoords (x : Fin (D₁ + D₂) → ℝ) : Fin D₁ → ℝ := fun i => x (Fin.castAdd D₂ i)
def tailCoords (x : Fin (D₁ + D₂) → ℝ) : Fin D₂ → ℝ := fun i => x (Fin.natAdd D₁ i)
def blockProduct (f : (Fin D₁ → ℝ) → ℂ) (h : (Fin D₂ → ℝ) → ℂ) : (Fin (D₁ + D₂) → ℝ) → ℂ :=
  fun x => f (headCoords x) * h (tailCoords x)
theorem natAdd_neq_castAdd (i : Fin D₂) (j : Fin D₁) : Fin.natAdd D₁ i ≠ Fin.castAdd D₂ j := by
  intro hij
  have hval := congrArg Fin.val hij
  simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
  have := j.isLt
  omega
theorem headCoords_shift_head (x : Fin (D₁ + D₂) → ℝ) (t : ℝ) (j : Fin D₁) :
    headCoords (x + t • Pi.single (Fin.castAdd D₂ j) (1 : ℝ)) =
      headCoords x + t • Pi.single j (1 : ℝ) := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp [headCoords]
  · have hne : Fin.castAdd D₂ i ≠ Fin.castAdd D₂ j :=
      fun e => hij (Fin.castAdd_injective _ _ e)
    simp [headCoords, hij, hne]
theorem tailCoords_shift_head (x : Fin (D₁ + D₂) → ℝ) (t : ℝ) (j : Fin D₁) :
    tailCoords (x + t • Pi.single (Fin.castAdd D₂ j) (1 : ℝ)) = tailCoords x := by
  funext i
  simp [tailCoords, natAdd_neq_castAdd i j]
theorem headCoords_shift_tail (x : Fin (D₁ + D₂) → ℝ) (t : ℝ) (j : Fin D₂) :
    headCoords (x + t • Pi.single (Fin.natAdd D₁ j) (1 : ℝ)) = headCoords x := by
  funext i
  simp [headCoords, (natAdd_neq_castAdd j i).symm]
theorem tailCoords_shift_tail (x : Fin (D₁ + D₂) → ℝ) (t : ℝ) (j : Fin D₂) :
    tailCoords (x + t • Pi.single (Fin.natAdd D₁ j) (1 : ℝ)) =
      tailCoords x + t • Pi.single j (1 : ℝ) := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp [tailCoords]
  · have hne : Fin.natAdd D₁ i ≠ Fin.natAdd D₁ j :=
      fun e => hij (Fin.natAdd_injective _ _ e)
    simp [tailCoords, hij, hne]
theorem hasLineDerivAt_blockProduct_head {f : (Fin D₁ → ℝ) → ℂ} (h : (Fin D₂ → ℝ) → ℂ) {a : ℂ}
    {x : Fin (D₁ + D₂) → ℝ} {j : Fin D₁}
    (hf : HasLineDerivAt ℝ f a (headCoords x) (Pi.single j 1)) :
    HasLineDerivAt ℝ (blockProduct f h) (a * h (tailCoords x)) x
      (Pi.single (Fin.castAdd D₂ j) 1) := by
  have hline : HasDerivAt
      (fun t : ℝ => f (headCoords x + t • Pi.single j (1 : ℝ)) * h (tailCoords x))
      (a * h (tailCoords x)) 0 := HasDerivAt.mul_const hf (h (tailCoords x))
  refine hline.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [blockProduct, headCoords_shift_head, tailCoords_shift_head]
theorem hasLineDerivAt_blockProduct_tail (f : (Fin D₁ → ℝ) → ℂ) {h : (Fin D₂ → ℝ) → ℂ} {a : ℂ}
    {x : Fin (D₁ + D₂) → ℝ} {j : Fin D₂}
    (hh : HasLineDerivAt ℝ h a (tailCoords x) (Pi.single j 1)) :
    HasLineDerivAt ℝ (blockProduct f h) (f (headCoords x) * a) x
      (Pi.single (Fin.natAdd D₁ j) 1) := by
  have hline : HasDerivAt
      (fun t : ℝ => f (headCoords x) * h (tailCoords x + t • Pi.single j (1 : ℝ)))
      (f (headCoords x) * a) 0 := HasDerivAt.const_mul (f (headCoords x)) hh
  refine hline.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [blockProduct, headCoords_shift_tail, tailCoords_shift_tail]
theorem partialDeriv_blockProduct_head {f : (Fin D₁ → ℝ) → ℂ} (h : (Fin D₂ → ℝ) → ℂ) {j : Fin D₁}
    (hf : ∀ y, LineDifferentiableAt ℝ f y (Pi.single j 1)) :
    partialDeriv (Fin.castAdd D₂ j) (blockProduct f h) =
      blockProduct (partialDeriv j f) h :=
  funext fun x => (hasLineDerivAt_blockProduct_head h (hf (headCoords x)).hasLineDerivAt).lineDeriv
theorem partialDeriv_blockProduct_tail (f : (Fin D₁ → ℝ) → ℂ) {h : (Fin D₂ → ℝ) → ℂ} {j : Fin D₂}
    (hh : ∀ y, LineDifferentiableAt ℝ h y (Pi.single j 1)) :
    partialDeriv (Fin.natAdd D₁ j) (blockProduct f h) =
      blockProduct f (partialDeriv j h) :=
  funext fun x => (hasLineDerivAt_blockProduct_tail f (hh (tailCoords x)).hasLineDerivAt).lineDeriv
theorem continuous_headCoords : Continuous (headCoords : (Fin (D₁ + D₂) → ℝ) → Fin D₁ → ℝ) :=
  continuous_pi fun i => continuous_apply _
theorem continuous_tailCoords : Continuous (tailCoords : (Fin (D₁ + D₂) → ℝ) → Fin D₂ → ℝ) :=
  continuous_pi fun i => continuous_apply _
theorem cnOnSpace_blockProduct {n : ℕ} : ∀ {f : (Fin D₁ → ℝ) → ℂ} {h : (Fin D₂ → ℝ) → ℂ},
    CnOnSpace n f → CnOnSpace n h → CnOnSpace n (blockProduct f h) := by
  induction n with
  | zero =>
    intro f h hf hh
    exact (((continuous_of_cnOnSpace hf).comp continuous_headCoords).mul
      ((continuous_of_cnOnSpace hh).comp continuous_tailCoords)).continuousOn
  | succ n ih =>
    intro f h hf hh
    have hc : Continuous (blockProduct f h) :=
      ((continuous_of_cnOnSpace hf).comp continuous_headCoords).mul
        ((continuous_of_cnOnSpace hh).comp continuous_tailCoords)
    refine ⟨hc.continuousOn, fun j => ?_⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · have hd : ∀ y, LineDifferentiableAt ℝ f y (Pi.single j 1) :=
        fun y => (hf.2 j).1 y (Set.mem_univ y)
      refine ⟨fun x _ =>
        (hasLineDerivAt_blockProduct_head h (hd _).hasLineDerivAt).lineDifferentiableAt, ?_⟩
      rw [partialDeriv_blockProduct_head h hd]
      exact ih (hf.2 j).2 (ContinuousPartialsUpTo.of_succ hh)
    · have hd : ∀ y, LineDifferentiableAt ℝ h y (Pi.single j 1) :=
        fun y => (hh.2 j).1 y (Set.mem_univ y)
      refine ⟨fun x _ =>
        (hasLineDerivAt_blockProduct_tail f (hd _).hasLineDerivAt).lineDifferentiableAt, ?_⟩
      rw [partialDeriv_blockProduct_tail f hd]
      exact ih (ContinuousPartialsUpTo.of_succ hf) (hh.2 j).2
theorem iterate_partialDeriv_blockProduct_head {f : (Fin D₁ → ℝ) → ℂ} (h : (Fin D₂ → ℝ) → ℂ)
    (j : Fin D₁) (k : ℕ) (hf : SmoothOnSpace f) :
    (partialDeriv (Fin.castAdd D₂ j))^[k] (blockProduct f h) =
      blockProduct ((partialDeriv j)^[k] f) h := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      partialDeriv_blockProduct_head h (hf.lineDiffAt j), ih (hf.deriv_coord j)]
theorem iterate_partialDeriv_blockProduct_tail (f : (Fin D₁ → ℝ) → ℂ) {h : (Fin D₂ → ℝ) → ℂ}
    (j : Fin D₂) (k : ℕ) (hh : SmoothOnSpace h) :
    (partialDeriv (Fin.natAdd D₁ j))^[k] (blockProduct f h) =
      blockProduct f ((partialDeriv j)^[k] h) := by
  induction k generalizing h with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      partialDeriv_blockProduct_tail f (hh.lineDiffAt j), ih (hh.deriv_coord j)]
theorem foldr_partialDeriv_blockProduct_head {f : (Fin D₁ → ℝ) → ℂ} (h : (Fin D₂ → ℝ) → ℂ)
    (γ : PowerSeries.MultiIndex D₁) (hf : SmoothOnSpace f) (l : List (Fin D₁)) :
    l.foldr (fun j H => (partialDeriv (Fin.castAdd D₂ j))^[γ j] H) (blockProduct f h) =
      blockProduct (l.foldr (fun j H => (partialDeriv j)^[γ j] H) f) h := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons]
    rw [ih, iterate_partialDeriv_blockProduct_head h j (γ j) (hf.foldr_coords γ l)]
theorem foldr_partialDeriv_blockProduct_tail (f : (Fin D₁ → ℝ) → ℂ) {h : (Fin D₂ → ℝ) → ℂ}
    (γ : PowerSeries.MultiIndex D₂) (hh : SmoothOnSpace h) (l : List (Fin D₂)) :
    l.foldr (fun j H => (partialDeriv (Fin.natAdd D₁ j))^[γ j] H) (blockProduct f h) =
      blockProduct f (l.foldr (fun j H => (partialDeriv j)^[γ j] H) h) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons]
    rw [ih, iterate_partialDeriv_blockProduct_tail f j (γ j) (hh.foldr_coords γ l)]
theorem finRange_sum_split : List.finRange (D₁ + D₂) =
    (List.finRange D₁).map (Fin.castAdd D₂) ++ (List.finRange D₂).map (Fin.natAdd D₁) := by apply _root_.YangMills.Construction.ConfigSpace.TensorSplit.finRange_add_eq_append <;> assumption
theorem iteratedPartial_blockProduct {f : (Fin D₁ → ℝ) → ℂ} {h : (Fin D₂ → ℝ) → ℂ}
    (α : PowerSeries.MultiIndex D₁) (α' : PowerSeries.MultiIndex D₂)
    (hf : SmoothOnSpace f) (hh : SmoothOnSpace h) :
    iteratedPartial (Fin.append α α' : PowerSeries.MultiIndex (D₁ + D₂)) (blockProduct f h) =
      blockProduct (iteratedPartial α f) (iteratedPartial α' h) := by
  unfold iteratedPartial
  rw [finRange_sum_split, List.foldr_append, List.foldr_map, List.foldr_map]
  simp only [Fin.append_left, Fin.append_right]
  rw [foldr_partialDeriv_blockProduct_tail f α' hh, foldr_partialDeriv_blockProduct_head _ α hf]
end CoordinateBlocks
section TuplesOfPoints
variable {s : Conventions.StandingParameters} {E : ReflectionPositivity.AxisMirror.Ambient}
  {p p' : ℕ}
theorem isSmoothFn_iff (F : Tuple s E p → ℂ) :
    IsSmoothFn F ↔ SmoothOnSpace (F ∘ tupleProj s E p) :=
  ⟨fun hF n => hF.2 n le_top, fun hF => ⟨isOpen_univ, fun n _ => hF n⟩⟩
theorem isCn_of_isSmoothFn {F : Tuple s E p → ℂ} (hF : IsSmoothFn F) (ν : ℕ) :
    IsCn (ν : ℕ∞) F :=
  ⟨isOpen_univ, fun n _ => hF.2 n le_top⟩
theorem isSmoothFn_add {F G : Tuple s E p → ℂ} (hF : IsSmoothFn F) (hG : IsSmoothFn G) :
    IsSmoothFn (F + G) :=
  (isSmoothFn_iff _).2 fun n =>
    cnOnSpace_add ((isSmoothFn_iff F).1 hF n) ((isSmoothFn_iff G).1 hG n)
theorem isSmoothFn_mul {F G : Tuple s E p → ℂ} (hF : IsSmoothFn F) (hG : IsSmoothFn G) :
    IsSmoothFn (F * G) :=
  (isSmoothFn_iff _).2 fun n =>
    cnOnSpace_mul ((isSmoothFn_iff F).1 hF n) ((isSmoothFn_iff G).1 hG n)
theorem isSmoothFn_comp_clm (L : ℂ →L[ℝ] ℂ) {F : Tuple s E p → ℂ} (hF : IsSmoothFn F) :
    IsSmoothFn (L ∘ F) :=
  (isSmoothFn_iff _).2 fun n => cnOnSpace_comp_clm L ((isSmoothFn_iff F).1 hF n)
theorem isSmoothFn_smul (b : ℂ) {F : Tuple s E p → ℂ} (hF : IsSmoothFn F) :
    IsSmoothFn (b • F) := by
  have hL := isSmoothFn_comp_clm (ContinuousLinearMap.mul ℝ ℂ b) hF
  have hEq : (ContinuousLinearMap.mul ℝ ℂ b) ∘ F = b • F := by
    funext y
    simp
  rwa [hEq] at hL
theorem isSmoothFn_const (c : ℂ) : IsSmoothFn (fun _ : Tuple s E p => c) :=
  (isSmoothFn_iff _).2 fun n => cnOnSpace_const n c
theorem mem_testFns_of_closedSupport_subset {Ω K : Set (Tuple s E p)} {G : Tuple s E p → ℂ}
    (hG : IsSmoothFn G) (hs : closedSupport G ⊆ K) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    G ∈ testFns Ω :=
  ⟨hG, hK.of_isClosed_subset isClosed_closure hs, hs.trans hKΩ⟩
theorem mem_closedSupport_of_ne_zero {F : Tuple s E p → ℂ} {y : Tuple s E p} (hy : F y ≠ 0) :
    y ∈ closedSupport F :=
  subset_closure hy
theorem closedSupport_linearComb_subset (F F' : Tuple s E p → ℂ) (b b' : ℂ) :
    closedSupport (b • F + b' • F') ⊆ closedSupport F ∪ closedSupport F' := by
  refine closure_minimal (fun y hy => ?_) (isClosed_closure.union isClosed_closure)
  by_contra hn
  have hF : F y = 0 := by
    by_contra hne
    exact hn (Or.inl (mem_closedSupport_of_ne_zero hne))
  have hF' : F' y = 0 := by
    by_contra hne
    exact hn (Or.inr (mem_closedSupport_of_ne_zero hne))
  exact hy (by simp [hF, hF'])
theorem closedSupport_mul_subset (φ F : Tuple s E p → ℂ) :
    closedSupport (φ * F) ⊆ closedSupport φ ∩ closedSupport F := by
  refine closure_minimal (fun y hy => ?_) (isClosed_closure.inter isClosed_closure)
  have hy' : φ y * F y ≠ 0 := hy
  exact ⟨mem_closedSupport_of_ne_zero (left_ne_zero_of_mul hy'),
    mem_closedSupport_of_ne_zero (right_ne_zero_of_mul hy')⟩
theorem linearCombFacts (Ω : Set (Tuple s E p)) : LinearCombFacts Ω := by
  intro F hF F' hF' b b'
  have hs := closedSupport_linearComb_subset F F' b b'
  exact ⟨mem_testFns_of_closedSupport_subset
    (isSmoothFn_add (isSmoothFn_smul b hF.1) (isSmoothFn_smul b' hF'.1))
    hs (hF.2.1.union hF'.2.1) (Set.union_subset hF.2.2 hF'.2.2), hs⟩
theorem restrictionFacts {Ω' Ω : Set (Tuple s E p)} (hΩ : Ω' ⊆ Ω) :
    RestrictionFacts hΩ := by
  have bound : ∀ (T : testFns Ω → ℂ) (K : Set (Tuple s E p)) (ν : ℕ),
      OrderBoundsOn T K ν → OrderBoundsOn (restrictDistrib hΩ T) K ν := by
    rintro T K ν ⟨C, hC⟩
    exact ⟨C, fun F hF => hC ⟨F.1, testFns_mono hΩ F.2⟩ hF⟩
  have distrib : ∀ T : testFns Ω → ℂ, IsDistrib T → IsDistrib (restrictDistrib hΩ T) := by
    intro T hT
    refine ⟨⟨fun F G H e => hT.1.1 _ _ _ e, fun c F H e => hT.1.2 c _ _ e⟩, fun K hK hKΩ => ?_⟩
    obtain ⟨ν, hν⟩ := hT.2 K hK (hKΩ.trans hΩ)
    exact ⟨ν, bound T K ν hν⟩
  refine ⟨testFns_mono hΩ, ?_, fun T hT => ⟨distrib T hT, fun ν₀ hν => ⟨distrib T hT, ?_⟩⟩⟩
  · rintro Fs F ⟨h1, h2, ⟨K, hK, hKΩ, h3, h4⟩, h5⟩
    exact ⟨fun t => testFns_mono hΩ (h1 t), testFns_mono hΩ h2,
      ⟨K, hK, hKΩ.trans hΩ, h3, h4⟩, h5⟩
  · exact fun K hK hKΩ => bound T K ν₀ (hν.2 K hK (hKΩ.trans hΩ))
theorem distribSeqContinuous (Ω : Set (Tuple s E p)) :
    DistribSeqContinuous Ω := by
  intro T hT Fs F hlim
  obtain ⟨K, hK, hKΩ, hFK, hFsK⟩ := hlim.2.2.1
  obtain ⟨ν, C, hC⟩ := hT.2 K hK hKΩ
  have hmem : ∀ t, Fs t - F ∈ testFns Ω ∧ closedSupport (Fs t - F) ⊆ K := by
    intro t
    have hEq : Fs t - F = (1 : ℂ) • Fs t + (-1 : ℂ) • F := by
      funext y
      simp [sub_eq_add_neg]
    rw [hEq]
    obtain ⟨h1, h2⟩ := linearCombFacts Ω (Fs t) (hlim.1 t) F hlim.2.1 1 (-1)
    exact ⟨h1, h2.trans (Set.union_subset (hFsK t) hFK)⟩
  have hsplit : ∀ t, T ⟨Fs t, hlim.1 t⟩ - T ⟨F, hlim.2.1⟩ = T ⟨Fs t - F, (hmem t).1⟩ := by
    intro t
    have := hT.1.1 ⟨Fs t - F, (hmem t).1⟩ ⟨F, hlim.2.1⟩ ⟨Fs t, hlim.1 t⟩ (by simp)
    rw [this]
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [hsplit]
  have hzero : Tendsto (fun t => (C : ℝ≥0∞) * cnNorm ν (Fs t - F)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) (hlim.2.2.2 ν)
      (Or.inr ENNReal.coe_ne_top)
    simpa using this
  have hle : Tendsto (fun t => ENNReal.ofReal ‖T ⟨Fs t - F, (hmem t).1⟩‖) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero (fun _ => zero_le)
      (fun t => hC ⟨Fs t - F, (hmem t).1⟩ (hmem t).2)
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hle
  simpa [Function.comp_def, ENNReal.toReal_ofReal] using this
theorem partsDerivNormFacts (hD : TupleDerivProps s E p) (Ω : Set (Tuple s E p)) :
    PartsDerivNormFacts Ω := by
  intro F hF
  have hre : IsSmoothFn (realPartFn F) :=
    isSmoothFn_comp_clm (Complex.ofRealCLM.comp Complex.reCLM) hF.1
  have him : IsSmoothFn (imPartFn F) :=
    isSmoothFn_comp_clm (Complex.ofRealCLM.comp Complex.imCLM) hF.1
  have hres : closedSupport (realPartFn F) ⊆ closedSupport F :=
    closure_mono fun y hy h0 => hy (by simp [realPartFn, show F y = 0 from h0])
  have hims : closedSupport (imPartFn F) ⊆ closedSupport F :=
    closure_mono fun y hy h0 => hy (by simp [imPartFn, show F y = 0 from h0])
  refine ⟨⟨mem_testFns_of_closedSupport_subset hre hres hF.2.1 hF.2.2, hres⟩,
    ⟨mem_testFns_of_closedSupport_subset him hims hF.2.1 hF.2.2, hims⟩, fun α => ?_, fun ν => ?_⟩
  · have hα := (hD ⊤ F hF.1).1 α le_top
    exact ⟨mem_testFns_of_closedSupport_subset (hα.2.2.2 rfl).1 hα.2.2.1 hF.2.1 hF.2.2,
      hα.2.2.1⟩
  · exact (hD ν F (isCn_of_isSmoothFn hF.1 ν)).2 ν rfl hF.2.1
theorem smoothMulFacts (Ω : Set (Tuple s E p)) : SmoothMulFacts Ω := by
  intro φ F hφ hF
  have hs := isSmoothFn_mul hφ hF
  have hsup := closedSupport_mul_subset φ F
  refine ⟨hs, hsup, ?_, ?_⟩
  · rintro (hm | hm)
    · exact mem_testFns_of_closedSupport_subset hs (hsup.trans Set.inter_subset_left)
        hm.2.1 hm.2.2
    · exact mem_testFns_of_closedSupport_subset hs (hsup.trans Set.inter_subset_right)
        hm.2.1 hm.2.2
  · intro Ω'' _ hFm hφm
    exact ⟨hs, hFm.2.1.of_isClosed_subset isClosed_closure (hsup.trans Set.inter_subset_right),
      fun y hy => ⟨hFm.2.2 (hsup hy).2, hφm.2.2 (hsup hy).1⟩⟩
theorem four_mul_add_eq (p p' : ℕ) : 4 * p + 4 * p' = 4 * (p + p') := (Nat.mul_add 4 p p').symm
def castBlockProduct {D₁ D₂ D : ℕ} (e : D₁ + D₂ = D) (f : (Fin D₁ → ℝ) → ℂ)
    (h : (Fin D₂ → ℝ) → ℂ) : (Fin D → ℝ) → ℂ :=
  fun x => f (fun i => x (Fin.cast e (Fin.castAdd D₂ i))) *
    h (fun i => x (Fin.cast e (Fin.natAdd D₁ i)))
theorem smoothOnSpace_castBlockProduct {D₁ D₂ D : ℕ} (e : D₁ + D₂ = D)
    {f : (Fin D₁ → ℝ) → ℂ} {h : (Fin D₂ → ℝ) → ℂ} (hf : SmoothOnSpace f) (hh : SmoothOnSpace h) :
    SmoothOnSpace (castBlockProduct e f h) := by
  subst e
  exact fun n => cnOnSpace_blockProduct (hf n) (hh n)
theorem iteratedPartial_castBlockProduct {D₁ D₂ D : ℕ} (e : D₁ + D₂ = D)
    {f : (Fin D₁ → ℝ) → ℂ} {h : (Fin D₂ → ℝ) → ℂ}
    (α : PowerSeries.MultiIndex D₁) (α' : PowerSeries.MultiIndex D₂)
    (hf : SmoothOnSpace f) (hh : SmoothOnSpace h) :
    iteratedPartial (fun j => Fin.append α α' (Fin.cast e.symm j) : PowerSeries.MultiIndex D)
        (castBlockProduct e f h) =
      castBlockProduct e (iteratedPartial α f) (iteratedPartial α' h) := by
  subst e
  exact iteratedPartial_blockProduct α α' hf hh
theorem order_split {D₁ D₂ D : ℕ} (e : D₁ + D₂ = D) (β : PowerSeries.MultiIndex D) :
    β.order = PowerSeries.MultiIndex.order (fun i => β (Fin.cast e (Fin.castAdd D₂ i))) +
      PowerSeries.MultiIndex.order (fun i => β (Fin.cast e (Fin.natAdd D₁ i))) := by
  subst e
  simp [PowerSeries.MultiIndex.order, Fin.sum_univ_add]
theorem append_split_eq {D₁ D₂ D : ℕ} (e : D₁ + D₂ = D) (β : PowerSeries.MultiIndex D) :
    (fun j => Fin.append (fun i => β (Fin.cast e (Fin.castAdd D₂ i)))
      (fun i => β (Fin.cast e (Fin.natAdd D₁ i))) (Fin.cast e.symm j) :
        PowerSeries.MultiIndex D) = β := by
  subst e
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
theorem flattenCoords_symm_apply (q : ℕ) (x : Fin (4 * q) → ℝ) (i : Fin q) (μ : Fin 4)
    (hlt : 4 * (i : ℕ) + μ < 4 * q) : (flattenCoords q).symm x i μ = x ⟨4 * i + μ, hlt⟩ := by apply _root_.YangMills.Construction.Torus.FourierBox.flattenCoords_symm_apply <;> assumption
theorem tupleProj_castAdd_components (x : Fin (4 * (p + p')) → ℝ) :
    (fun i : Fin p => tupleProj s E (p + p') x (Fin.castAdd p' i)) =
      tupleProj s E p
        (fun j => x (Fin.cast (four_mul_add_eq p p') (Fin.castAdd (4 * p') j))) := by
  funext i
  simp only [tupleProj]
  congr 1
theorem tupleProj_natAdd_components (x : Fin (4 * (p + p')) → ℝ) :
    (fun i : Fin p' => tupleProj s E (p + p') x (Fin.natAdd p i)) =
      tupleProj s E p'
        (fun j => x (Fin.cast (four_mul_add_eq p p') (Fin.natAdd (4 * p) j))) := by
  funext i
  simp only [tupleProj]
  congr 1
  funext μ
  have hi := i.isLt
  have hμ := μ.isLt
  rw [flattenCoords_symm_apply _ _ _ _ (by simp only [Fin.val_natAdd]; omega),
    flattenCoords_symm_apply _ _ _ _ (by omega)]
  congr 1
  ext
  simp only [Fin.val_natAdd, Fin.val_cast]
  omega
theorem tensorPair_comp_tupleProj (F : Tuple s E p → ℂ) (H : Tuple s E p' → ℂ) :
    tensorPair F H ∘ tupleProj s E (p + p') =
      castBlockProduct (four_mul_add_eq p p') (F ∘ tupleProj s E p)
        (H ∘ tupleProj s E p') := by
  funext x
  simp only [Function.comp, tensorPair, castBlockProduct]
  rw [tupleProj_castAdd_components, tupleProj_natAdd_components]
theorem isSmoothFn_tensorPair {F : Tuple s E p → ℂ} {H : Tuple s E p' → ℂ} (hF : IsSmoothFn F)
    (hH : IsSmoothFn H) : IsSmoothFn (tensorPair F H) := by
  rw [isSmoothFn_iff, tensorPair_comp_tupleProj]
  exact smoothOnSpace_castBlockProduct _ ((isSmoothFn_iff F).1 hF) ((isSmoothFn_iff H).1 hH)
theorem multiDeriv_comp_tupleProj_of_smooth {q : ℕ} (hD : TupleDerivProps s E q)
    {F : Tuple s E q → ℂ} (hF : IsSmoothFn F) (α : PowerSeries.MultiIndex (4 * q)) :
    multiDeriv α F ∘ tupleProj s E q = iteratedPartial α (F ∘ tupleProj s E q) :=
  multiDeriv_comp_tupleProj ((hD ⊤ F hF).1 α le_top).1.exists
theorem multiDeriv_tensorPair (hD : TupleDerivProps s E p)
    (hD' : TupleDerivProps s E p') (hD'' : TupleDerivProps s E (p + p'))
    {F : Tuple s E p → ℂ} {H : Tuple s E p' → ℂ} (hF : IsSmoothFn F) (hH : IsSmoothFn H)
    (α : PowerSeries.MultiIndex (4 * p)) (α' : PowerSeries.MultiIndex (4 * p')) :
    multiDeriv (appendMultiIndex α α') (tensorPair F H) =
      tensorPair (multiDeriv α F) (multiDeriv α' H) := by
  apply (tupleProj_surjective s E (p + p')).injective_comp_right
  change multiDeriv (appendMultiIndex α α') (tensorPair F H) ∘ tupleProj s E (p + p') =
    tensorPair (multiDeriv α F) (multiDeriv α' H) ∘ tupleProj s E (p + p')
  rw [multiDeriv_comp_tupleProj_of_smooth hD'' (isSmoothFn_tensorPair hF hH),
    tensorPair_comp_tupleProj, tensorPair_comp_tupleProj,
    multiDeriv_comp_tupleProj_of_smooth hD hF, multiDeriv_comp_tupleProj_of_smooth hD' hH]
  exact iteratedPartial_castBlockProduct (four_mul_add_eq p p') α α'
    ((isSmoothFn_iff F).1 hF) ((isSmoothFn_iff H).1 hH)
theorem cnNorm_tensorPair_le (hD : TupleDerivProps s E p)
    (hD' : TupleDerivProps s E p') (hD'' : TupleDerivProps s E (p + p'))
    {F : Tuple s E p → ℂ} {H : Tuple s E p' → ℂ} (hF : IsSmoothFn F) (hH : IsSmoothFn H) (ν : ℕ) :
    cnNorm ν (tensorPair F H) ≤ cnNorm ν F * cnNorm ν H := by
  refine iSup_le fun β => iSup_le fun hβ => iSup_le fun z => ?_
  obtain ⟨α, α', rfl, hα, hα'⟩ :
      ∃ (α : PowerSeries.MultiIndex (4 * p)) (α' : PowerSeries.MultiIndex (4 * p')),
        appendMultiIndex α α' = β ∧ α.order ≤ ν ∧ α'.order ≤ ν := by
    have hs := order_split (four_mul_add_eq p p') β
    exact ⟨_, _, append_split_eq (four_mul_add_eq p p') β, by omega, by omega⟩
  rw [multiDeriv_tensorPair hD hD' hD'' hF hH]
  simp only [tensorPair]
  rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
  exact mul_le_mul' (le_iSup_of_le α (le_iSup_of_le hα (le_iSup
      (fun y => ENNReal.ofReal ‖multiDeriv α F y‖) _)))
    (le_iSup_of_le α' (le_iSup_of_le hα' (le_iSup
      (fun y => ENNReal.ofReal ‖multiDeriv α' H y‖) _)))
theorem closedSupport_tensorPair_subset (F : Tuple s E p → ℂ) (H : Tuple s E p' → ℂ) :
    closedSupport (tensorPair F H) ⊆ prodTupleSets (closedSupport F) (closedSupport H) := by
  have hc : IsClosed (prodTupleSets (closedSupport F) (closedSupport H)) := by
    have hEq : prodTupleSets (closedSupport F) (closedSupport H) =
        (fun z : Tuple s E (p + p') => fun i : Fin p => z (Fin.castAdd p' i)) ⁻¹'
            closedSupport F ∩
          (fun z : Tuple s E (p + p') => fun i : Fin p' => z (Fin.natAdd p i)) ⁻¹'
            closedSupport H := rfl
    rw [hEq]
    exact (isClosed_closure.preimage (continuous_pi fun i => continuous_apply _)).inter
      (isClosed_closure.preimage (continuous_pi fun i => continuous_apply _))
  refine closure_minimal (fun z hz => ?_) hc
  have hz' : F (fun i => z (Fin.castAdd p' i)) * H (fun i => z (Fin.natAdd p i)) ≠ 0 := hz
  exact ⟨mem_closedSupport_of_ne_zero (left_ne_zero_of_mul hz'),
    mem_closedSupport_of_ne_zero (right_ne_zero_of_mul hz')⟩
theorem tensorPairFacts (hD : TupleDerivProps s E p)
    (hD' : TupleDerivProps s E p') (hD'' : TupleDerivProps s E (p + p'))
    {F : Tuple s E p → ℂ} {H : Tuple s E p' → ℂ} (hF : IsSmoothFn F) (hH : IsSmoothFn H) :
    TensorPairFacts F H :=
  ⟨isSmoothFn_tensorPair hF hH, multiDeriv_tensorPair hD hD' hD'' hF hH,
    closedSupport_tensorPair_subset F H,
    fun ν _ _ => cnNorm_tensorPair_le hD hD' hD'' hF hH ν⟩
theorem isSmoothFn_tensorProd {q : ℕ} (φ : Fin q → Pt s E → ℂ)
    (hφ : ∀ i, IsSmoothFn (ofSinglePoint (φ i))) : IsSmoothFn (tensorProd φ) := by
  induction q with
  | zero =>
    have hEq : tensorProd φ = fun _ => 1 := by
      funext y
      simp [tensorProd]
    rw [hEq]
    exact isSmoothFn_const 1
  | succ q ih =>
    have hEq : tensorProd φ = tensorPair (tensorProd fun i => φ (Fin.castSucc i))
        (ofSinglePoint (φ (Fin.last q))) := by
      funext z
      simp only [tensorProd, tensorPair, ofSinglePoint]
      rw [Fin.prod_univ_castSucc]
      rfl
    rw [hEq]
    exact isSmoothFn_tensorPair (ih _ fun i => hφ _) (hφ _)
theorem tsupport_of_ofSinglePoint_mem {g : Pt s E → ℂ} {O : Set (Pt s E)}
    (hg : ofSinglePoint g ∈ testFns (singletonTupleSet O)) :
    IsCompact (tsupport g) ∧ tsupport g ⊆ O := by
  have hK : IsCompact ((fun y : Tuple s E 1 => y 0) '' closedSupport (ofSinglePoint g)) :=
    hg.2.1.image (continuous_apply 0)
  have hsub : tsupport g ⊆ (fun y : Tuple s E 1 => y 0) '' closedSupport (ofSinglePoint g) :=
    closure_minimal (fun x hx => ⟨fun _ => x, mem_closedSupport_of_ne_zero hx, rfl⟩) hK.isClosed
  refine ⟨hK.of_isClosed_subset (isClosed_tsupport g) hsub, hsub.trans ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hg.2.2 hy
theorem tensorProdFacts (O : Fin p → Set (Pt s E)) (φ : Fin p → Pt s E → ℂ)
    (hφ : ∀ i, ofSinglePoint (φ i) ∈ testFns (singletonTupleSet (O i))) :
    TensorProdFacts O φ := by
  have hs : closedSupport (tensorProd φ) ⊆ Set.pi Set.univ fun i => tsupport (φ i) := by
    refine closure_minimal (fun y hy i _ => ?_)
      (isClosed_set_pi fun i _ => isClosed_tsupport _)
    have hy' : ∏ i, φ i (y i) ≠ 0 := hy
    exact subset_tsupport _ (Finset.prod_ne_zero_iff.mp hy' i (Finset.mem_univ i))
  exact ⟨mem_testFns_of_closedSupport_subset (isSmoothFn_tensorProd φ fun i => (hφ i).1) hs
    (isCompact_univ_pi fun i => (tsupport_of_ofSinglePoint_mem (hφ i)).1)
    (Set.pi_mono fun i _ => (tsupport_of_ofSinglePoint_mem (hφ i)).2), hs⟩
end TuplesOfPoints
end SmoothCalculus
open SmoothCalculus in
theorem testFnOperations_of_tupleTopology
    (hT : TupleTopology.Holds) : TestFnOperations := by
  intro s E p hp
  have hD : TupleDerivProps s E p := ((hT s E).1 p hp).2.2.2.2
  refine ⟨fun Ω' Ω hΩ _ _ => restrictionFacts hΩ, fun Ω _ => ⟨distribSeqContinuous Ω,
    linearCombFacts Ω, partsDerivNormFacts hD Ω, smoothMulFacts Ω⟩,
    fun p' hp' F H hF hH => ?_, fun O φ _ hφ => tensorProdFacts O φ hφ⟩
  exact tensorPairFacts hD ((hT s E).1 p' hp').2.2.2.2
    ((hT s E).1 (p + p') (by omega)).2.2.2.2 hF hH
end YangMills.Construction.AmbientPoints
