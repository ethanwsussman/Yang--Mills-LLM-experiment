import YangMills.Construction.TorusOrFourSpace.ContinuousPartialsUnderTranslationsSumsAndProducts
import YangMills.Construction.TorusOrFourSpace.DerivativesOfFunctionsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.DistanceAndLiftsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.IteratedPartialsOfFunctionsWithContinuousPartials
import YangMills.Construction.TorusOrFourSpace.OpenSetsAndBallsOfSeveralPoints
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicSpace.TupleDerivatives
open Kind
theorem continuous_of_contPartialsUpTo {p : ℕ+} (n : ℕ) (g : Coords p → ℂ)
    (hg : Coords.ContPartialsUpTo n g) : Continuous g := by
  cases n with
  | zero => exact hg
  | succ n => exact hg.1
theorem finite_setOf_degree_le (p : ℕ+) (ν : ℕ) :
    {α : CoordIndex p | α.degree ≤ ν}.Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin (4 * (p : ℕ)) => Set.Iic ν)
    fun _ => Set.finite_Iic ν).subset ?_
  intro α hα j _
  exact le_trans (Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)) hα
theorem statement_holds
    (hLift : TupleMetric.QuotientDistanceAndLifts)
    (hOpen : TupleTopology.QuotientOpenAndBalls)
    (hIter : PartialDerivatives.IteratedPartialsCompose)
    (hTrans : PartialsAlgebra.Statement) :
    Statement := by
  intro D E p
  obtain ⟨⟨hsurj, hfib⟩, -, ⟨-, hzero, hsymm, -⟩, -, -⟩ := hLift D E p
  obtain ⟨-, -, hopens, hcont, hballs⟩ := hOpen D E p
  obtain ⟨hshift, hvanish, -⟩ := hTrans p
  have fibreConst : ∀ (α : CoordIndex p) (g : Coords p → ℂ),
      (∀ x, ∀ k ∈ Tuple.periodSet D E p, g (x + k) = g x) →
      ∀ x x' : Coords p, Tuple.proj D E x = Tuple.proj D E x' →
        Coords.iterPartial α g x = Coords.iterPartial α g x' := by
    intro α g hg x x' hxx
    have hk := (hfib x x').1 hxx
    have e : (fun z => g (z + (x - x'))) = g := funext fun z => hg z _ hk
    have s := congrFun (hshift α g (x - x')) x'
    rw [e] at s
    have e2 : x' + (x - x') = x := by abel
    rw [e2] at s
    exact s.symm
  have periodic : ∀ (f : E.Tuple D p → ℂ) (x : Coords p),
      ∀ k ∈ Tuple.periodSet D E p,
        (f ∘ Tuple.proj D E) (x + k) = (f ∘ Tuple.proj D E) x := by
    intro f x k hk
    have h : Tuple.proj D E (x + k) = Tuple.proj D E x :=
      (hfib _ _).2 (by simpa using hk)
    simp only [Function.comp_apply, h]
  have exists_desc : ∀ (f : E.Tuple D p → ℂ) (α : CoordIndex p),
      ∃ h : E.Tuple D p → ℂ, h ∘ Tuple.proj D E =
        Coords.iterPartial α (f ∘ Tuple.proj D E) := by
    intro f α
    refine ⟨fun y => Coords.iterPartial α (f ∘ Tuple.proj D E)
      (Function.surjInv hsurj y), funext fun x => ?_⟩
    exact fibreConst α _ (periodic f) _ _ (Function.surjInv_eq hsurj _)
  have desc_unique : ∀ h h' : E.Tuple D p → ℂ,
      h ∘ Tuple.proj D E = h' ∘ Tuple.proj D E → h = h' := by
    intro h h' hh
    funext y
    obtain ⟨x, rfl⟩ := hsurj y
    exact congrFun hh x
  have deriv_spec : ∀ (f : E.Tuple D p → ℂ) (α : CoordIndex p),
      Tuple.partialDeriv D E α f ∘ Tuple.proj D E =
        Coords.iterPartial α (f ∘ Tuple.proj D E) :=
    fun f α => Classical.epsilon_spec (exists_desc f α)
  have classC : ∀ (ν : ℕ) (f : E.Tuple D p → ℂ), Tuple.IsClassC D E ν f →
      ∀ α : CoordIndex p, α.degree ≤ ν →
        Tuple.IsClassC D E (ν - α.degree) (Tuple.partialDeriv D E α f) := by
    intro ν f hf α hα
    have h := (hIter p ν _ hf α hα).1
    rw [← deriv_spec f α] at h
    exact h
  have contDeriv : ∀ (ν : ℕ) (f : E.Tuple D p → ℂ), Tuple.IsClassC D E ν f →
      ∀ α : CoordIndex p, α.degree ≤ ν →
        Tuple.IsContinuousT D E (Tuple.partialDeriv D E α f) :=
    fun ν f hf α hα => (hcont _).2
      (continuous_of_contPartialsUpTo _ _ (classC ν f hf α hα))
  have supp_subset : ∀ (f : E.Tuple D p → ℂ) (α : CoordIndex p),
      Tuple.supportT D E (Tuple.partialDeriv D E α f) ⊆
        Tuple.supportT D E f := by
    intro f α y hy r hr
    by_contra hno
    push Not at hno
    have hUopen := (hopens _).1 (hballs y r hr).1
    have hzeroOn : ∀ x ∈ Tuple.proj D E ⁻¹'
        {y' | Tuple.tupleDist D E y' y < r},
        (f ∘ Tuple.proj D E) x = 0 := by
      intro x hx
      by_contra h
      have hlt : Tuple.tupleDist D E y (Tuple.proj D E x) < r := by
        rw [hsymm]
        exact hx
      exact not_lt.2 (hno _ h) hlt
    obtain ⟨z, hz, hdz⟩ := hy r hr
    obtain ⟨x, rfl⟩ := hsurj z
    apply hz
    have hx : x ∈ Tuple.proj D E ⁻¹'
        {y' | Tuple.tupleDist D E y' y < r} := by
      show Tuple.tupleDist D E (Tuple.proj D E x) y < r
      rw [hsymm]
      exact hdz
    have h0 := hvanish α _ _ hUopen hzeroOn x hx
    rw [← deriv_spec f α] at h0
    exact h0
  have bdd : ∀ h : E.Tuple D p → ℂ, Tuple.IsContinuousT D E h →
      ∀ K : Set (E.Tuple D p), Tuple.IsCompactT D E K →
        (∀ y, h y ≠ 0 → y ∈ K) → ∃ C : ℝ, ∀ y, ‖h y‖ ≤ C := by
    intro h hh K hK hoff
    obtain ⟨U', hsub, hfin, hcov⟩ := hK
      {U | Tuple.IsOpenT D E U ∧ ∃ C : ℝ, ∀ y ∈ U, ‖h y‖ ≤ C}
      (fun U hU => hU.1) (by
        intro x _
        obtain ⟨δ, hδ, hx'⟩ := hh x 1 one_pos
        refine ⟨{y' | Tuple.tupleDist D E y' x < δ},
          ⟨(hballs x δ hδ).1, ‖h x‖ + 1, ?_⟩, ?_⟩
        · intro y hy
          have h1 : dist (h x) (h y) < 1 := hx' y (by
            rw [hsymm]
            exact hy)
          have h2 : ‖h y‖ ≤ ‖h x‖ + ‖h y - h x‖ := norm_le_norm_add_norm_sub' _ _
          rw [← dist_eq_norm, dist_comm] at h2
          linarith
        · show Tuple.tupleDist D E x x < δ
          rw [(hzero x x).2 rfl]
          exact hδ)
    have hc : ∀ U ∈ U', ∃ C : ℝ, ∀ y ∈ U, ‖h y‖ ≤ C := fun U hU => (hsub hU).2
    choose! c hc using hc
    obtain ⟨M, hM⟩ := (hfin.image c).bddAbove
    refine ⟨max M 0, fun y => ?_⟩
    by_cases hy : h y = 0
    · rw [hy, norm_zero]
      exact le_max_right _ _
    · obtain ⟨U, hU, hyU⟩ := hcov (hoff y hy)
      exact ((hc U hU y hyU).trans (hM ⟨U, hU, rfl⟩)).trans (le_max_left _ _)
  refine ⟨?_, ?_⟩
  · intro ν f hf α hα
    refine ⟨⟨_, deriv_spec f α, fun h hh => desc_unique _ _ (hh.trans (deriv_spec f α).symm)⟩,
      deriv_spec f α, contDeriv ν f hf α hα, classC ν f hf α hα, ?_, supp_subset f α⟩
    intro β hβ
    apply desc_unique
    rw [deriv_spec, deriv_spec, deriv_spec f (α + β)]
    exact (hIter p ν _ hf α hα).2 β hβ
  · intro ν f hf hK
    have eachIndex : ∀ α : CoordIndex p, ∃ C : ℝ, α.degree ≤ ν →
        ∀ y, ‖Tuple.partialDeriv D E α f y‖ ≤ C := by
      intro α
      by_cases hα : α.degree ≤ ν
      · obtain ⟨C, hC⟩ := bdd _ (contDeriv ν f hf α hα) _ hK (fun y hy => by
          refine supp_subset f α (fun r hr => ⟨y, hy, ?_⟩)
          rw [(hzero y y).2 rfl]
          exact hr)
        exact ⟨C, fun _ => hC⟩
      · exact ⟨0, fun h => absurd h hα⟩
    choose c hc using eachIndex
    obtain ⟨M, hM⟩ := ((finite_setOf_degree_le p ν).image c).bddAbove
    have hle : Tuple.cNorm D E ν f ≤ ENNReal.ofReal M := by
      refine iSup_le fun α => iSup_le fun hα => iSup_le fun y => ?_
      exact ENNReal.ofReal_le_ofReal ((hc α hα y).trans (hM ⟨α, hα, rfl⟩))
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
end YangMills.Construction.PeriodicSpace.TupleDerivatives
