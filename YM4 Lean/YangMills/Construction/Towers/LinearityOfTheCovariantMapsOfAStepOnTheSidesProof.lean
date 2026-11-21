import YangMills.Construction.Towers.CovariantDifferenceRelationsOfAStepOfASideProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.StepMapsComplexLinear
open YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct
open YangMills.Construction.Coordinates
open MeanStableFields (IsHolomorphicOnFields)
def coordsToMatrix : ComplexCoordinates 4 →L[ℂ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := ComplexCoordinates.matrixEquiv.symm
      map_add' := fun u v => by ext i j; simp [ComplexCoordinates.matrixEquiv]
      map_smul' := fun c u => by ext i j; simp [ComplexCoordinates.matrixEquiv] }
theorem coordsToMatrix_matrixEquiv (X : ComplexMatrix2) :
    coordsToMatrix (ComplexCoordinates.matrixEquiv X) = X :=
  ComplexCoordinates.matrixEquiv.symm_apply_apply X
def traceCLM : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
theorem basis_sum_repr_coe (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (y : ComplexMatrix2.traceless) :
    ∑ c, β.repr y c • (β c : ComplexMatrix2) = (y : ComplexMatrix2) := by
  conv_rhs => rw [← β.sum_repr y]
  simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul]
variable {ι : Type} [Fintype ι]
theorem asGroupFactors_smul_add (A A' : ι → ComplexMatrix2) (c : ℂ) (s : ι ⊕ Empty) :
    asGroupFactors (c • A + A') s = c • asGroupFactors A s + asGroupFactors A' s := by
  rcases s with i | e
  · rfl
  · exact e.elim
theorem asGroupFactors_zero (s : ι ⊕ Empty) : asGroupFactors (0 : ι → ComplexMatrix2) s = 0 := by
  rcases s with i | e
  · rfl
  · exact e.elim
theorem exists_linear_deriv_log_expChart (hel : ComplexMatrix2.ExpLogEstimates)
    (hps : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    {Ψ : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2} (h : IsHolomorphicToUnimodular β W Ψ)
    {p : ι ⊕ Empty → ComplexMatrix2} (hp : p ∈ W) :
    ∃ Λ : (ι → ComplexMatrix2) → ComplexMatrix2,
      (∀ A : ι → ComplexMatrix2, (∀ i, A i ∈ ComplexMatrix2.traceless) →
        HasDerivAt (fun t : ℂ =>
          ComplexMatrix2.logSeries (Ψ (expChartAt p (asGroupFactors (t • A))) * (Ψ p)⁻¹)) (Λ A) 0 ∧
        Λ A ∈ ComplexMatrix2.traceless) ∧
      ∀ (A A' : ι → ComplexMatrix2) (c : ℂ), Λ (c • A + A') = c • Λ A + Λ A' := by
  obtain ⟨-, hmaps, -, hloc⟩ := h
  obtain ⟨O, h0, hO, -, hcoord⟩ := hloc p hp
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective ComplexMatrix2.traceless.subtype
    (Submodule.ker_subtype _)
  have hPx : ∀ (x : ComplexMatrix2) (hx : x ∈ ComplexMatrix2.traceless), P x = ⟨x, hx⟩ :=
    fun x hx => LinearMap.congr_fun hP ⟨x, hx⟩
  let ν := Fintype.equivFin (ι ⊕ Empty)
  have hν := hcoord ν
  let w : (ι → ComplexMatrix2) → ComplexCoordinates (Fintype.card (ι ⊕ Empty) * 3) := fun A k =>
    β.repr (P (asGroupFactors A (ν.symm (finProdFinEquiv.symm k).1))) (finProdFinEquiv.symm k).2
  have hw_lin : ∀ (A A' : ι → ComplexMatrix2) (c : ℂ), w (c • A + A') = c • w A + w A' := by
    intro A A' c
    funext k
    simp only [w, asGroupFactors_smul_add, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
      Finsupp.coe_add, Finsupp.coe_smul, smul_eq_mul]
  have hw_zero : w 0 = 0 := by
    funext k
    simp only [w, asGroupFactors_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have hw_smul : ∀ (A : ι → ComplexMatrix2) (t : ℂ), w (t • A) = t • w A := by
    intro A t
    have h1 := hw_lin A 0 t
    rw [add_zero, hw_zero, add_zero] at h1
    exact h1
  have hτ : ∀ A : ι → ComplexMatrix2, (∀ i, A i ∈ ComplexMatrix2.traceless) →
      tupleOfCoords β ν (w A) = asGroupFactors A := by
    intro A hA
    funext s
    have hs : asGroupFactors A s ∈ ComplexMatrix2.traceless := by
      rcases s with i | e
      · exact hA i
      · exact e.elim
    show ∑ c : Fin 3, w A (finProdFinEquiv (ν s, c)) • (β c : ComplexMatrix2) = asGroupFactors A s
    have hterm : ∀ c : Fin 3, w A (finProdFinEquiv (ν s, c)) =
        β.repr ⟨asGroupFactors A s, hs⟩ c := by
      intro c
      simp only [w, Equiv.symm_apply_apply, hPx _ hs]
    simp only [hterm]
    exact basis_sum_repr_coe β ⟨asGroupFactors A s, hs⟩
  have hτ0 : tupleOfCoords β ν 0 = 0 := by
    have h1 := hτ 0 (fun _ => ComplexMatrix2.traceless.zero_mem)
    rw [hw_zero] at h1
    rw [h1]
    funext s
    exact asGroupFactors_zero s
  have hzero : (0 : ComplexCoordinates (Fintype.card (ι ⊕ Empty) * 3)) ∈
      tupleOfCoords β ν ⁻¹' O := by
    show tupleOfCoords β ν 0 ∈ O
    rw [hτ0]
    exact h0
  obtain ⟨Lf, hLf⟩ := ((hps.1 _ _ hν.1).1 4 _ hν).2.2.1 0 hzero
  have hLc := hasFDerivAt_of_restrictScalars ℝ hLf rfl
  refine ⟨fun A => coordsToMatrix (Lf (w A)), fun A hA => ?_, fun A A' c => ?_⟩
  · have hline : HasDerivAt (fun t : ℂ => t • w A) (w A) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const (w A)
    have hf := hLc.comp_hasDerivAt_of_eq (0 : ℂ) hline (zero_smul ℂ (w A)).symm
    have hG := coordsToMatrix.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hf
    have hval : ∀ t : ℂ, tupleOfCoords β ν (t • w A) = asGroupFactors (t • A) := by
      intro t
      rw [← hw_smul]
      exact hτ _ fun i => ComplexMatrix2.traceless.smul_mem t (hA i)
    have hD : HasDerivAt (fun t : ℂ =>
        ComplexMatrix2.logSeries (Ψ (expChartAt p (asGroupFactors (t • A))) * (Ψ p)⁻¹))
        (coordsToMatrix (Lf (w A))) 0 := by
      refine hG.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, hval, coordsToMatrix_matrixEquiv]
    refine ⟨hD, ?_⟩
    have hnear : ∀ᶠ t : ℂ in 𝓝 0, t • w A ∈ tupleOfCoords β ν ⁻¹' O := by
      have hc : Tendsto (fun t : ℂ => t • w A) (𝓝 0) (𝓝 0) := by
        have := hline.continuousAt.tendsto
        simpa using this
      exact hc.eventually (hν.1.mem_nhds hzero)
    have hone : (fun t : ℂ => Complex.exp (traceCLM
        (ComplexMatrix2.logSeries (Ψ (expChartAt p (asGroupFactors (t • A))) * (Ψ p)⁻¹)))) =ᶠ[𝓝 0]
        fun _ => 1 := by
      filter_upwards [hnear] with t ht
      have ht' : asGroupFactors (t • A) ∈ O := by
        have h1 : tupleOfCoords β ν (t • w A) ∈ O := ht
        rwa [hval] at h1
      obtain ⟨hc, hlog⟩ := hO _ ht'
      have hd1 : (Ψ (expChartAt p (asGroupFactors (t • A)))).det = 1 := hmaps hc
      have hd2 : (Ψ p).det = 1 := hmaps hp
      have hdet : (Ψ (expChartAt p (asGroupFactors (t • A))) * (Ψ p)⁻¹).det = 1 := by
        rw [Matrix.det_mul, hd1, Matrix.det_nonsing_inv, hd2]
        simp
      have hexp := (hel.2.2.2.1 _ hlog).2.2.2.2
      rw [add_sub_cancel] at hexp
      have hde := hel.2.2.2.2.2.1
        (ComplexMatrix2.logSeries (Ψ (expChartAt p (asGroupFactors (t • A))) * (Ψ p)⁻¹))
      rw [hexp, hdet] at hde
      exact hde.symm
    have htr := traceCLM.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hD
    have hce := htr.cexp
    have hun := hce.unique ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).congr_of_eventuallyEq hone)
    have hz := (mul_eq_zero.1 hun).resolve_left (Complex.exp_ne_zero _)
    exact hz
  · show coordsToMatrix (Lf (w (c • A + A'))) = _
    rw [hw_lin, map_add, map_smul, map_add, map_smul]
section Step
variable {L n k j : ℕ}
theorem opposite_isPositivelyOriented_of_not {b : Edge L n k j} (hb : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IteratedMeans.opposite_isPositivelyOriented_of_not <;> assumption
theorem forwardFrom_isPositivelyOriented (y : Vertex L n k j) (μ : Fin 4) :
    (PeriodicLattice.Bond.forwardFrom y μ : Edge L n k j).IsPositivelyOriented :=
  ⟨μ, by show y + PeriodicLattice.unitStep L n _ μ - y = _; abel⟩
theorem fieldOfPositiveValues_restrict
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.Construction.Tower.CovDiffStep.fieldOfPositiveValues_restrict <;> assumption
theorem fieldOfPositiveValues_expChart (V B : Edge L n k j → ComplexMatrix2) (t : ℂ) :
    fieldOfPositiveValues (fun b : PositiveEdge L n k j =>
        expChartAt (asGroupFactors (restrictToPositiveEdges V))
          (asGroupFactors (t • fun b : PositiveEdge L n k j => Complex.I • B b.1)) (.inl b)) =
      PeriodicLattice.expTwist (t • B) V := by
  funext b
  unfold fieldOfPositiveValues PeriodicLattice.expTwist
  by_cases hb : b.IsPositivelyOriented
  · rw [dif_pos hb, if_pos hb]
    show ComplexMatrix2.matExp (t • Complex.I • B b) * V b =
      ComplexMatrix2.matExp (Complex.I • t • B b) * V b
    rw [smul_comm]
  · rw [dif_neg hb, dif_pos (opposite_isPositivelyOriented_of_not hb), if_neg hb]
    show (ComplexMatrix2.matExp (t • Complex.I • B b.opposite) * V b.opposite)⁻¹ =
      (ComplexMatrix2.matExp (Complex.I • t • B b.opposite) * V b.opposite)⁻¹
    rw [smul_comm]
theorem logDirectionalDeriv_traceless_linear (hel : ComplexMatrix2.ExpLogEstimates)
    (hps : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {𝔇 : Set (Edge L n k j → ComplexMatrix2)}
    {Φ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2} (h : IsHolomorphicOnFields β 𝔇 Φ)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ 𝔇)
    (hVc : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    (∀ B ∈ complexEdgeForms L n k j, logDirectionalDeriv ℂ
      (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B ∈ ComplexMatrix2.traceless) ∧
    ∀ B ∈ complexEdgeForms L n k j, ∀ B' ∈ complexEdgeForms L n k j, ∀ c : ℂ,
      logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) (c • B + B') =
        c • logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B +
          logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B' := by
  obtain ⟨-, inst, hG⟩ := h
  have hp : asGroupFactors (restrictToPositiveEdges V) ∈
      asGroupFactors '' (restrictToPositiveEdges '' 𝔇) :=
    ⟨_, ⟨V, hV, rfl⟩, rfl⟩
  obtain ⟨Λ, hΛ, hlin⟩ := exists_linear_deriv_log_expChart hel hps β hG hp
  have hΨp : Φ (fieldOfPositiveValues fun b =>
      asGroupFactors (restrictToPositiveEdges V) (.inl b)) = Φ V := by
    have h1 : (fun b : PositiveEdge L n k j =>
        asGroupFactors (restrictToPositiveEdges V) (.inl b)) = restrictToPositiveEdges V := rfl
    rw [h1, fieldOfPositiveValues_restrict hVc]
  have key : ∀ B ∈ complexEdgeForms L n k j,
      logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B =
        Complex.I⁻¹ • Λ (fun b => Complex.I • B b.1) ∧
      Λ (fun b => Complex.I • B b.1) ∈ ComplexMatrix2.traceless := by
    intro B hB
    obtain ⟨hd, hm⟩ := hΛ (fun b => Complex.I • B b.1)
      fun b => ComplexMatrix2.traceless.smul_mem _ (hB.1 b.1 b.2)
    refine ⟨?_, hm⟩
    rw [hΨp] at hd
    unfold logDirectionalDeriv
    rw [← hd.deriv]
    congr 2
    funext t
    rw [fieldOfPositiveValues_expChart]
    rfl
  refine ⟨fun B hB => ?_, fun B hB B' hB' c => ?_⟩
  · rw [(key B hB).1]
    exact ComplexMatrix2.traceless.smul_mem _ (key B hB).2
  · have hmem : c • B + B' ∈ complexEdgeForms L n k j :=
      (complexEdgeForms L n k j).add_mem ((complexEdgeForms L n k j).smul_mem c hB) hB'
    rw [(key _ hmem).1, (key B hB).1, (key B' hB').1]
    have hsum : (fun b : PositiveEdge L n k j => Complex.I • (c • B + B') b.1) =
        c • (fun b : PositiveEdge L n k j => Complex.I • B b.1) +
          fun b : PositiveEdge L n k j => Complex.I • B' b.1 := by
      funext b
      simp only [Pi.add_apply, Pi.smul_apply, smul_add]
      rw [smul_comm]
    rw [hsum, hlin, smul_add, smul_comm]
theorem extendOddly_mem
    (ho : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {f : Edge L n k j → ComplexMatrix2}
    (hf : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.traceless) :
    extendOddly f ∈ complexEdgeForms L n k j := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · have h1 : extendOddly f b = f b := if_pos hb
    show extendOddly f b ∈ ComplexMatrix2.traceless
    rw [h1]
    exact hf b hb
  · unfold extendOddly
    by_cases hb : b.IsPositivelyOriented
    · have hr : ¬ b.opposite.IsPositivelyOriented := by
        rcases ho b with h | h
        · exact h.2
        · exact absurd hb h.2
      rw [if_pos hb, if_neg hr]
      rfl
    · rw [if_neg hb, if_pos (opposite_isPositivelyOriented_of_not hb), neg_neg]
theorem extendOddly_smul_add {f g h : Edge L n k j → ComplexMatrix2} (c : ℂ)
    (H : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b = c • g b + h b) :
    extendOddly f = c • extendOddly g + extendOddly h := by
  funext b
  simp only [Pi.add_apply, Pi.smul_apply]
  unfold extendOddly
  by_cases hb : b.IsPositivelyOriented
  · simp only [if_pos hb]
    exact H b hb
  · simp only [if_neg hb]
    rw [H _ (opposite_isPositivelyOriented_of_not hb), neg_add, smul_neg]
theorem smul_finsum_mem_traceless {α : Type} {S : Set α} (hS : S.Finite) (w : ℂ)
    {f : α → ComplexMatrix2} (hf : ∀ x ∈ S, f x ∈ ComplexMatrix2.traceless) :
    w • ∑ᶠ x ∈ S, f x ∈ ComplexMatrix2.traceless := by
  rw [finsum_mem_eq_finite_toFinset_sum f hS]
  exact ComplexMatrix2.traceless.smul_mem w
    (ComplexMatrix2.traceless.sum_mem fun x hx => hf x (hS.mem_toFinset.1 hx))
theorem smul_finsum_smul_add {α : Type} {S : Set α} (hS : S.Finite) (w c : ℂ)
    {f g h : α → ComplexMatrix2} (H : ∀ x ∈ S, f x = c • g x + h x) :
    w • ∑ᶠ x ∈ S, f x = c • (w • ∑ᶠ x ∈ S, g x) + w • ∑ᶠ x ∈ S, h x := by
  rw [finsum_mem_eq_finite_toFinset_sum f hS, finsum_mem_eq_finite_toFinset_sum g hS,
    finsum_mem_eq_finite_toFinset_sum h hS, smul_comm c w, ← smul_add]
  congr 1
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x hx => H x (hS.mem_toFinset.1 hx)
theorem conj_mem_traceless (W : ComplexMatrix2) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy W X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.PeriodicLattice.conjugateBy_mem_traceless <;> assumption
theorem conjugateBy_smul_add (W X Y : ComplexMatrix2) (c : ℂ) :
    ComplexMatrix2.conjugateBy W (c • X + Y) =
      c • ComplexMatrix2.conjugateBy W X + ComplexMatrix2.conjugateBy W Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul]
end Step
theorem claim_holds (hW : MeanStableFields.MeanStableFieldsHold)
    (hA : PolydiscContours.ContourHolomorphyHolds)
    (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hF : BondSetFields.ProductStructureHolds)
    (hel : ComplexMatrix2.ExpLogEstimates)
    (hps : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    Claim := by
  intro L hL n k j hn hjk V hV
  have hk : 1 ≤ k := by omega
  have hVc : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := hV.1
  have ho : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => ((hE ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hjk.le).2.2.2 b).2.2.2.2.2
  have ho' : ∀ b : Edge L n k (j + 1),
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => ((hE ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ (j + 1) hjk).2.2.2 b).2.2.2.2.2
  have hbonds : Finite (Edge L n k j) :=
    Set.finite_univ_iff.1 ((hF L hL k j hjk.le).1 n hn).2.1
  have hsites : Finite (Vertex L n k j) :=
    Finite.of_injective
      (fun x : Vertex L n k j => (PeriodicLattice.Bond.forwardFrom x 0 : Edge L n k j))
      fun x x' h => congrArg PeriodicLattice.Bond.source h
  have hblock : ∀ y : Vertex L n k (j + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
        Set (Vertex L n k j)).Finite :=
    fun y => Set.toFinite _
  let β := OneLoop.pauliBasis
  have hav : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented → _ := fun c hc =>
    logDirectionalDeriv_traceless_linear hel hps β
      (((hW L hL k hk).1 n hn).holomorphic_smoothing j hjk c hc β) hV hVc
  have hco : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y → _ := fun y x hx =>
    logDirectionalDeriv_traceless_linear hel hps β
      ((((hA L hL k j hjk).1 n hn (PeriodicLattice.Bond.forwardFrom y 0)
        (forwardFrom_isPositivelyOriented y 0)).holomorphicOn_fieldsNearOne y (Or.inl rfl) x
          hx).isHolomorphicOnFields β) hV hVc
  refine ⟨fun B hB => ⟨?_, fun y => ?_⟩, fun B hB B' hB' c => ⟨?_, ?_⟩, fun l hl => ⟨?_, fun y => ?_⟩,
    fun l l' hl hl' c => ⟨?_, ?_⟩⟩
  · exact extendOddly_mem (fun b => ho' b) fun c hc => (hav c hc).1 B hB
  · exact smul_finsum_mem_traceless (hblock y) _ fun x hx => (hco y x hx).1 B hB
  · exact extendOddly_smul_add c fun b hb => (hav b hb).2 B hB B' hB' c
  · funext y
    exact smul_finsum_smul_add (hblock y) _ c fun x hx => (hco y x hx).2 B hB B' hB' c
  · exact extendOddly_mem ho fun b _ =>
      ComplexMatrix2.traceless.sub_mem (conj_mem_traceless _ (hl _)) (hl _)
  · exact smul_finsum_mem_traceless (hblock y) _ fun x _ => conj_mem_traceless _ (hl x)
  · refine extendOddly_smul_add c fun b _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, conjugateBy_smul_add]
    module
  · funext y
    exact smul_finsum_smul_add (hblock y) _ c fun x _ => conjugateBy_smul_add _ _ _ c
end YangMills.Construction.Tower.StepMapsComplexLinear
end
