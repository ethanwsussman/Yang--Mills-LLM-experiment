import YangMills.Construction.Chessboard.CyclicProductDoublingBoundProof
import YangMills.Construction.Lattice.ChessboardEstimateAtEveryGridDatum
import YangMills.Construction.Lattice.CopyRuleOfAGridDatum
import YangMills.Construction.Lattice.ReflectionPositivityAcrossAPairOfLinkMirrors
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.CheckerboardEstimate
open Chessboard (cyclicHalf planeReflection reflectFamily)
section Arcs
variable {n : ℕ} [NeZero n]
def InArc (n : ℕ) (s x : ZMod n) : Prop := ∃ j : ℕ, j < n / 2 ∧ x = s + (j : ZMod n)
theorem inArc_iff (s x : ZMod n) : InArc n s x ↔ (x - s).val < n / 2 := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [add_sub_cancel_left, ZMod.val_natCast_of_lt (lt_of_lt_of_le hj (Nat.div_le_self _ _))]
    exact hj
  · intro h
    exact ⟨(x - s).val, h, by rw [ZMod.natCast_zmod_val]; ring⟩
theorem zmod_val_neg_one_sub (t : ZMod n) : (-1 - t).val = n - 1 - t.val := by
  have ht := ZMod.val_lt t
  have hw : (n - 1 - t.val) + t.val + 1 = n := by omega
  have h1 : (((n - 1 - t.val) + t.val + 1 : ℕ) : ZMod n) = 0 := by
    rw [hw]
    exact ZMod.natCast_self n
  rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one] at h1
  have h2 : -1 - t = ((n - 1 - t.val : ℕ) : ZMod n) := by
    linear_combination (-1 : ZMod n) * h1
  rw [h2, ZMod.val_natCast_of_lt (by omega)]
theorem inArc_iff_not_inArc_reflect (hn : Even n) (s x : ZMod n) :
    InArc n s x ↔ ¬ InArc n s (2 * s - 1 - x) := by
  rw [inArc_iff, inArc_iff]
  have e : 2 * s - 1 - x - s = -1 - (x - s) := by ring
  rw [e, zmod_val_neg_one_sub]
  obtain ⟨m, hm⟩ := hn
  have := ZMod.val_lt (x - s)
  have := NeZero.pos n
  omega
theorem not_inArc_iff_inArc_shift (hn : Even n) (s x : ZMod n) :
    ¬ InArc n s x ↔ InArc n (s + ((n / 2 : ℕ) : ZMod n)) x := by
  rw [inArc_iff, inArc_iff]
  obtain ⟨m, hm⟩ := hn
  have hdiv : n / 2 = m := by omega
  rw [hdiv]
  have h2 : (m : ZMod n) + m = 0 := by
    rw [← Nat.cast_add, ← hm]
    exact ZMod.natCast_self n
  have ht := ZMod.val_lt (x - s)
  have e : x - (s + (m : ZMod n)) = (x - s) - m := by ring
  rw [e]
  by_cases h : (x - s).val < m
  · have e2 : (x - s) - m = (((x - s).val + m : ℕ) : ZMod n) := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val]
      linear_combination (-1 : ZMod n) * h2
    rw [e2, ZMod.val_natCast_of_lt (by omega)]
    omega
  · have e2 : (x - s) - m = (((x - s).val - m : ℕ) : ZMod n) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_zmod_val]
    rw [e2, ZMod.val_natCast_of_lt (by omega)]
    omega
omit [NeZero n] in
theorem two_mul_halfPeriod_eq_zero (hn : Even n) : 2 * ((n / 2 : ℕ) : ZMod n) = 0 := by
  obtain ⟨m, hm⟩ := hn
  have hdiv : n / 2 = m := by omega
  rw [hdiv, two_mul, ← Nat.cast_add, ← hm]
  exact ZMod.natCast_self n
end Arcs
section CyclicIndices
variable {D : ℕ} (n : Fin D → ℕ) [∀ μ, NeZero (n μ)]
omit [∀ μ, NeZero (n μ)] in
theorem planeReflection_planeReflection (μ : Fin D) (s : ZMod (n μ))
    (k : Chessboard.CyclicIndex n) :
    planeReflection n μ s (planeReflection n μ s k) = k := by apply _root_.YangMills.Construction.Chessboard.planeReflection_planeReflection <;> assumption
variable {n}
theorem mem_cyclicHalf_iff_planeReflection_not_mem (hn : ∀ μ, Even (n μ)) (μ : Fin D)
    (s : ZMod (n μ)) (k : Chessboard.CyclicIndex n) :
    k ∈ cyclicHalf n μ s ↔ planeReflection n μ s k ∉ cyclicHalf n μ s := by
  have h := inArc_iff_not_inArc_reflect (hn μ) s (k μ)
  have e : (planeReflection n μ s k) μ = 2 * s - 1 - k μ := by simp [planeReflection]
  show InArc (n μ) s (k μ) ↔ ¬ InArc (n μ) s ((planeReflection n μ s k) μ)
  rw [e]
  exact h
theorem not_mem_cyclicHalf_iff (hn : ∀ μ, Even (n μ)) (μ : Fin D) (s : ZMod (n μ))
    (k : Chessboard.CyclicIndex n) :
    k ∉ cyclicHalf n μ s ↔ k ∈ cyclicHalf n μ (s + ((n μ / 2 : ℕ) : ZMod (n μ))) :=
  not_inArc_iff_inArc_shift (hn μ) s (k μ)
omit [∀ μ, NeZero (n μ)] in
theorem planeReflection_add_halfPeriod (hn : ∀ μ, Even (n μ)) (μ : Fin D) (s : ZMod (n μ)) :
    planeReflection n μ (s + ((n μ / 2 : ℕ) : ZMod (n μ))) = planeReflection n μ s := by
  funext k
  have h := two_mul_halfPeriod_eq_zero (hn μ)
  have e : 2 * (s + ((n μ / 2 : ℕ) : ZMod (n μ))) - 1 - k μ = 2 * s - 1 - k μ := by
    linear_combination h
  simp only [planeReflection]
  rw [e]
end CyclicIndices
theorem prod_involution_swap {I M : Type*} [CommMonoid M] (r : I → I) (hr : ∀ k, r (r k) = k)
    (S T : Finset I) (hST : ∀ k ∈ S, r k ∈ T) (hTS : ∀ k ∈ T, r k ∈ S) (w : I → I → M) :
    ∏ k ∈ T, w (r k) k = ∏ k ∈ S, w k (r k) :=
  Finset.prod_nbij' r r hTS hST (fun k _ => hr k) (fun k _ => hr k)
    (fun k _ => by rw [hr k])
section Edges
open BoxTorus
variable {L : ℕ} {κ : ℤ} {ℓ : Fin 4 → ℝ}
theorem isBoundedBorelOfEdges_mono {E E' : Set (DirectedEdge L κ ℓ)} (h : E ⊆ E')
    {F : GaugeConfig L κ ℓ → ℂ} (hF : IsBoundedBorelOfEdges E F) :
    IsBoundedBorelOfEdges E' F := by
  obtain ⟨f, hf, ⟨C, hC⟩, hFf⟩ := hF
  have hs : forwardPart E ⊆ forwardPart E' := fun b hb => hb.imp (fun x => h x) (fun x => h x)
  exact ⟨fun u => f fun b => u ⟨b.1, hs b.2⟩,
    hf.comp (measurable_pi_lambda _ fun b => measurable_pi_apply _), ⟨C, fun u => hC _⟩,
    fun U => hFf U⟩
theorem isBoundedBorelOfEdges_mul {E : Set (DirectedEdge L κ ℓ)}
    {F F' : GaugeConfig L κ ℓ → ℂ} (hF : IsBoundedBorelOfEdges E F)
    (hF' : IsBoundedBorelOfEdges E F') :
    IsBoundedBorelOfEdges E fun U => F U * F' U := by
  obtain ⟨f, hf, ⟨C, hC⟩, hFf⟩ := hF
  obtain ⟨f', hf', ⟨C', hC'⟩, hFf'⟩ := hF'
  refine ⟨fun u => f u * f' u, hf.mul hf', ⟨C * C', fun u => ?_⟩, fun U => ?_⟩
  · rw [norm_mul]
    exact mul_le_mul (hC u) (hC' u) (norm_nonneg _) ((norm_nonneg _).trans (hC u))
  · simp only [hFf U, hFf' U]
theorem isBoundedBorelOfEdges_prod {E : Set (DirectedEdge L κ ℓ)} {ι : Type*}
    (S : Finset ι) (F : ι → GaugeConfig L κ ℓ → ℂ)
    (h : ∀ i ∈ S, IsBoundedBorelOfEdges E (F i)) :
    IsBoundedBorelOfEdges E fun U => ∏ i ∈ S, F i U := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨fun _ => 1, measurable_const, ⟨1, fun _ => by simp⟩, fun U => by simp⟩
  | insert i S hi ih =>
    have h' := isBoundedBorelOfEdges_mul (h i (Finset.mem_insert_self i S))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.prod_insert hi] using h'
end Edges
variable {L : ℕ} {κ : ℤ}
theorem cellObservables_mem_localAlgebra (d : CellGrid L κ) (c : d.spaceCells)
    (O : TopologicalSpace.Opens d.Space) (h : interior c.1 ⊆ O) {F : d.GaugeConfig → ℂ}
    (hF : F ∈ d.cellObservables c) : F ∈ d.localAlgebra O :=
  isBoundedBorelOfEdges_mono
    (E := d.edgesWithin (TopologicalSpace.Opens.interior c.1))
    (fun _ hb => by
      obtain ⟨h₁, h₂⟩ := hb
      exact And.intro (h h₁) (h h₂)) hF
instance counts_neZero (d : CellGrid L κ) (μ : Fin 4) : NeZero (d.counts μ) :=
  ⟨(d.counts_pos μ).ne'⟩
def indexedCell (d : CellGrid L κ) (k : d.CellIndex) : d.spaceCells := ⟨d.cellAt k, _, rfl⟩
theorem indexedCell_bijective (d : CellGrid L κ)
    (h : GroupAndCells.SpaceCellsIndexed d) : Function.Bijective (indexedCell d) := by
  have hcl : ∀ k : d.CellIndex, d.indexClass (fun μ => ((k μ).cast : ℤ)) = k := fun k => by
    funext μ
    exact ZMod.intCast_zmod_cast _
  constructor
  · intro k k' e
    have e' : d.cellAt k = d.cellAt k' := congrArg Subtype.val e
    have := (h.1 (fun μ => ((k μ).cast : ℤ)) (fun μ => ((k' μ).cast : ℤ))).1 e'
    rwa [hcl, hcl] at this
  · rintro ⟨c, hc⟩
    have hc' : c ∈ Set.range d.cellAt := h.2.2.1 ▸ hc
    obtain ⟨k, rfl⟩ := hc'
    exact ⟨k, rfl⟩
def copiesMean (d : CellGrid L κ) (β : ℝ)
    (f : d.CellIndex → d.cellObservables (indexedCell d 0)) : ℂ :=
  d.gibbsMean β fun U => ∏ k, d.checkerboardCopy (indexedCell d 0) (indexedCell d k) (f k) U
theorem doubling_hypotheses_hold (hG : GroupAndCells.AllHold)
    (hC : GridCopyRule.CopyRuleHolds)
    (hR : MirrorPositivity.ReflectionPositivityAcrossMirrors) (d : CellGrid L κ) {β : ℝ}
    (hβ : 0 < β) (f : d.CellIndex → d.cellObservables (indexedCell d 0)) (μ : Fin 4)
    (s : ZMod (d.counts μ)) :
    (copiesMean d β (reflectFamily d.counts μ s f)).im = 0 ∧
    0 ≤ (copiesMean d β (reflectFamily d.counts μ s f)).re ∧
    ‖copiesMean d β f‖ ^ 2 ≤ (copiesMean d β (reflectFamily d.counts μ s f)).re *
      (copiesMean d β
        (reflectFamily d.counts μ (s + ((d.counts μ / 2 : ℕ) : ZMod (d.counts μ))) f)).re := by
  classical
  obtain ⟨-, hInd, -, -, -, hRefl, -⟩ := hG L κ d
  obtain ⟨a, rfl⟩ : ∃ a : ℤ, (a : ZMod (d.counts μ)) = s := ⟨_, ZMod.intCast_zmod_cast s⟩
  obtain ⟨θ, hθ, -, -⟩ := hInd.1 (d.faceReflectEquiv μ a)
    (Subgroup.subset_closure ⟨(μ, a), rfl⟩)
  have hθ' : d.IsInducedMap θ (d.faceReflect μ a) := hθ
  obtain ⟨hMir, hCell⟩ := hRefl μ a θ hθ'
  have hrefl : InfiniteLattice.coordinateReflection μ (d.faceLevel μ a) = d.faceReflect μ a := by
    funext x
    have e : x μ - d.faceLevel μ a = x μ - d.centre μ - a * d.cellLength := by
      simp only [CellGrid.faceLevel]
      ring
    simp only [InfiniteLattice.coordinateReflection, CellGrid.faceReflect, e]
    rfl
  have hUp := ((hR L κ d β hβ).1 μ _ hMir.1).2 θ (hrefl ▸ hθ')
  obtain ⟨-, -, ⟨-, hH, -, hCS⟩, -⟩ := hUp
  set r := planeReflection d.counts μ (a : ZMod (d.counts μ)) with hr
  have hrr : ∀ k, r (r k) = k := planeReflection_planeReflection d.counts μ _
  set hf := cyclicHalf d.counts μ (a : ZMod (d.counts μ)) with hhf
  have hin : ∀ k, k ∈ hf ↔ r k ∉ hf :=
    mem_cyclicHalf_iff_planeReflection_not_mem d.counts_even μ _
  have hout : ∀ k, k ∉ hf → r k ∈ hf := fun k hk => by
    by_contra h
    exact hk ((hin k).2 h)
  have hin' : ∀ k, k ∈ hf → r k ∉ hf := fun k hk => (hin k).1 hk
  let w : d.CellIndex → d.CellIndex → d.GaugeConfig → ℂ := fun k k' =>
    d.checkerboardCopy (indexedCell d 0) (indexedCell d k') (f k)
  let A : Finset d.CellIndex := Finset.univ.filter (· ∈ hf)
  let B : Finset d.CellIndex := Finset.univ.filter (· ∉ hf)
  have memA : ∀ k, k ∈ A ↔ k ∈ hf := fun k => by simp [A]
  have memB : ∀ k, k ∈ B ↔ k ∉ hf := fun k => by simp [B]
  have hAB : ∀ k ∈ A, r k ∈ B := fun k hk => (memB _).2 (hin' k ((memA k).1 hk))
  have hBA : ∀ k ∈ B, r k ∈ A := fun k hk => (memA _).2 (hout k ((memB k).1 hk))
  let P : d.GaugeConfig → ℂ := fun U => ∏ k ∈ A, w k k U
  let Q : d.GaugeConfig → ℂ := fun U => ∏ k ∈ B, w k (r k) U
  have hw_mem : ∀ k k', w k k' ∈ d.cellObservables (indexedCell d k') := fun k k' => by
    obtain ⟨h, -⟩ := hC L κ d (indexedCell d 0) (indexedCell d k') (f k)
    exact h
  have hsub : ∀ k k', k' ∈ hf → w k k' ∈ d.localAlgebra ⟨_, hH⟩ := fun k k' hk' =>
    cellObservables_mem_localAlgebra d (indexedCell d k') ⟨_, hH⟩ ((hCell.2.2.2 k').1 hk')
      (hw_mem k k')
  have hP : P ∈ d.localAlgebra ⟨_, hH⟩ :=
    isBoundedBorelOfEdges_prod A (fun k => w k k) fun k hk =>
      hsub k k ((memA k).1 hk)
  have hQ : Q ∈ d.localAlgebra ⟨_, hH⟩ :=
    isBoundedBorelOfEdges_prod B (fun k => w k (r k)) fun k hk =>
      hsub k (r k) (hout k ((memB k).1 hk))
  let g := d.symmetryOfMap θ
  have hconj : ∀ k k' U, starRingEnd ℂ (g.actOnObservables (w k k') U) = w k (r k') U :=
    fun k k' U => by
      obtain ⟨-, -, -, -, hrc⟩ := hC L κ d (indexedCell d 0) (indexedCell d k') (f k)
      exact congrFun (hrc θ ⟨μ, a, hθ'⟩ (indexedCell d (r k')) (hCell.1 k').symm) U
  have hconjP : ∀ U, starRingEnd ℂ (g.actOnObservables P U) = ∏ k ∈ A, w k (r k) U := fun U => by
    have e := map_prod (starRingEnd ℂ) (fun k => w k k (g.pullback U)) A
    exact e.trans (Finset.prod_congr rfl fun k _ => hconj k k U)
  have hconjQ : ∀ U, starRingEnd ℂ (g.actOnObservables Q U) = ∏ k ∈ B, w k k U := fun U => by
    have e := map_prod (starRingEnd ℂ) (fun k => w k (r k) (g.pullback U)) B
    refine e.trans (Finset.prod_congr rfl fun k _ => ?_)
    have h := hconj k (r k) U
    rw [hrr k] at h
    exact h
  have hsplit : ∀ v : d.CellIndex → ℂ, ∏ k, v k = (∏ k ∈ A, v k) * ∏ k ∈ B, v k := fun v =>
    (Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ hf) v).symm
  have e1 : copiesMean d β f = MirrorPositivity.reflectedPairing d β θ Q P := by
    show d.gibbsMean β _ = d.gibbsMean β _
    congr 1
    funext U
    rw [hconjQ U, hsplit, mul_comm]
  have e2 : copiesMean d β (reflectFamily d.counts μ (a : ZMod (d.counts μ)) f) =
      MirrorPositivity.reflectedPairing d β θ P P := by
    show d.gibbsMean β _ = d.gibbsMean β _
    congr 1
    funext U
    rw [hconjP U, hsplit, mul_comm]
    have h1 : ∀ k ∈ A, d.checkerboardCopy (indexedCell d 0) (indexedCell d k)
        (reflectFamily d.counts μ (a : ZMod (d.counts μ)) f k) U = w k k U := fun k hk => by
      have e : reflectFamily d.counts μ (a : ZMod (d.counts μ)) f k = f k :=
        if_pos ((memA k).1 hk)
      simp only [w, e]
    have h2 : ∀ k ∈ B, d.checkerboardCopy (indexedCell d 0) (indexedCell d k)
        (reflectFamily d.counts μ (a : ZMod (d.counts μ)) f k) U = w (r k) k U := fun k hk => by
      have e : reflectFamily d.counts μ (a : ZMod (d.counts μ)) f k = f (r k) :=
        if_neg ((memB k).1 hk)
      simp only [w, e]
    rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2,
      prod_involution_swap r hrr A B hAB hBA fun k k' => w k k' U]
  have e3 : copiesMean d β
      (reflectFamily d.counts μ
        ((a : ZMod (d.counts μ)) + ((d.counts μ / 2 : ℕ) : ZMod (d.counts μ))) f) =
      MirrorPositivity.reflectedPairing d β θ Q Q := by
    show d.gibbsMean β _ = d.gibbsMean β _
    congr 1
    funext U
    rw [hconjQ U, hsplit]
    have hcompl := not_mem_cyclicHalf_iff d.counts_even μ (a : ZMod (d.counts μ))
    have hshift := planeReflection_add_halfPeriod d.counts_even μ (a : ZMod (d.counts μ))
    have h1 : ∀ k ∈ A, d.checkerboardCopy (indexedCell d 0) (indexedCell d k)
        (reflectFamily d.counts μ
          ((a : ZMod (d.counts μ)) + ((d.counts μ / 2 : ℕ) : ZMod (d.counts μ))) f k) U =
        w (r k) k U := fun k hk => by
      have hn : k ∉ cyclicHalf d.counts μ
          ((a : ZMod (d.counts μ)) + ((d.counts μ / 2 : ℕ) : ZMod (d.counts μ))) := fun h =>
        (hcompl k).2 h ((memA k).1 hk)
      have e : reflectFamily d.counts μ
          ((a : ZMod (d.counts μ)) + ((d.counts μ / 2 : ℕ) : ZMod (d.counts μ))) f k
          = f (r k) := by
        rw [hr, ← hshift]
        exact if_neg hn
      simp only [w, e]
    have h2 : ∀ k ∈ B, d.checkerboardCopy (indexedCell d 0) (indexedCell d k)
        (reflectFamily d.counts μ
          ((a : ZMod (d.counts μ)) + ((d.counts μ / 2 : ℕ) : ZMod (d.counts μ))) f k) U =
        w k k U := fun k hk => by
      have e : reflectFamily d.counts μ
          ((a : ZMod (d.counts μ)) + ((d.counts μ / 2 : ℕ) : ZMod (d.counts μ))) f k = f k :=
        if_pos ((hcompl k).1 ((memB k).1 hk))
      simp only [w, e]
    rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2,
      prod_involution_swap r hrr B A hBA hAB fun k k' => w k k' U, mul_comm]
  obtain ⟨h0, hcs⟩ := hCS P hP Q hQ
  rw [e1, e2, e3]
  have h0' := Complex.le_def.1 h0
  exact ⟨h0'.2.symm, h0'.1, by rw [mul_comm]; exact hcs⟩
theorem checkerboardBound_holds (hD : Chessboard.DoublingBound) (hG : GroupAndCells.AllHold)
    (hC : GridCopyRule.CopyRuleHolds)
    (hR : MirrorPositivity.ReflectionPositivityAcrossMirrors) :
    CellGrid.CheckerboardBoundAtAllGrids := by
  intro L κ d β hβ
  obtain ⟨-, -, hCells, -⟩ := hG L κ d
  have hbij := indexedCell_bijective d hCells
  obtain ⟨hpos, hbound⟩ := hD 4 (by norm_num) d.counts d.counts_even
    (d.cellObservables (indexedCell d 0))
    (copiesMean d β) (fun f μ s => doubling_hypotheses_hold hG hC hR d hβ f μ s)
  have hmem : ∀ (c : d.spaceCells) (F : d.cellObservables c),
      d.checkerboardCopy c (indexedCell d 0) F ∈ d.cellObservables (indexedCell d 0) :=
    fun c F => by
      obtain ⟨h, -⟩ := hC L κ d c (indexedCell d 0) F
      exact h
  let toBase : (c : d.spaceCells) → d.cellObservables c → d.cellObservables (indexedCell d 0) :=
    fun c F => ⟨_, hmem c F⟩
  have hcopy : ∀ (c : d.spaceCells) (F : d.cellObservables c) (c' : d.spaceCells),
      d.checkerboardCopy (indexedCell d 0) c' (toBase c F) = d.checkerboardCopy c c' F :=
    fun c F c' => by
      obtain ⟨_, -, -, h, -⟩ := hC L κ d c (indexedCell d 0) F
      exact h c'
  have hself : ∀ (c : d.spaceCells) (F : d.cellObservables c), d.checkerboardCopy c c F = F.1 :=
    fun c F => by
      obtain ⟨-, -, h, -⟩ := hC L κ d c c F
      exact h
  have hconst : ∀ (c : d.spaceCells) (F : d.cellObservables c),
      copiesMean d β (fun _ => toBase c F) = d.copiesProductMean β c F := fun c F => by
    show d.gibbsMean β _ = d.gibbsMean β _
    congr 1
    funext U
    rw [← finprod_comp (g := fun c' => d.checkerboardCopy c c' F U) (indexedCell d) hbij,
      finprod_eq_prod_of_fintype]
    exact Finset.prod_congr rfl fun k _ => congrFun (hcopy c F _) U
  refine ⟨fun c F => ?_, fun F => ?_⟩
  · rw [← hconst]
    have h := hpos (toBase c F)
    exact Complex.le_def.2 ⟨h.2, h.1.symm⟩
  · let f : d.CellIndex → d.cellObservables (indexedCell d 0) := fun k =>
      toBase (indexedCell d k) (F (indexedCell d k))
    have hΦ : copiesMean d β f =
        d.gibbsMean β fun U => ∏ᶠ c : d.spaceCells, (F c).1 U := by
      show d.gibbsMean β _ = d.gibbsMean β _
      congr 1
      funext U
      rw [← finprod_comp (g := fun c => (F c).1 U) (indexedCell d) hbij,
        finprod_eq_prod_of_fintype]
      refine Finset.prod_congr rfl fun k _ => ?_
      show d.checkerboardCopy (indexedCell d 0) (indexedCell d k) (toBase _ _) U = _
      rw [hcopy, hself]
    have hV : ∏ᶠ c : d.spaceCells, d.checkerboardNorm β c (F c) =
        ∏ k : d.CellIndex, (copiesMean d β fun _ => f k).re ^
          (1 / ((∏ μ, d.counts μ : ℕ) : ℝ)) := by
      rw [← finprod_comp (g := fun c => d.checkerboardNorm β c (F c)) (indexedCell d) hbij,
        finprod_eq_prod_of_fintype]
      refine Finset.prod_congr rfl fun k _ => ?_
      show _ = (copiesMean d β fun _ => toBase _ _).re ^ _
      rw [hconst]
      rfl
    rw [← hΦ, hV]
    exact hbound f
end YangMills.Construction.CheckerboardEstimate
end
