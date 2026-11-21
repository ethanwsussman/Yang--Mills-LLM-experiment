import YangMills.Construction.BoundsOnEverySide.MovingTuplesOfALimitAlongStatesProof
import YangMills.Construction.SystemsWithFiveBounds.MovingTuplesAtNumbers
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds.TranslatedTuplesProof
theorem supportQ_euclidean_eq_tsupport (D : PeriodicSpace.Params) (f : (Fin 4 → ℝ) → ℝ) :
    (PeriodicSpace.Kind.supportQ D .euclidean f : Set (Fin 4 → ℝ)) = tsupport f := by apply _root_.YangMills.Construction.BoundsOnEverySide.TranslatedTuples.supportQ_eq_tsupport <;> assumption
theorem euclidSupp_eq_tsupport (f : (Fin 4 → ℝ) → ℝ) :
    ReflectionPositivity.CutoffMirrors.euclidSupp f = tsupport f :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
theorem bounds_of_isLipAt {s : Conventions.StandingParameters} {M : ℝ} {hM : 1 ≤ M} {n : ℕ}
    {d R : ℝ} (hd : 0 < d) {f : Fin n → (Fin 4 → ℝ) → ℝ}
    (h : BoundsOnEverySide.TranslatedTuples.IsLipAt s M hM d R f) :
    (∀ i, TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 (f i)) ∧
      (∀ i, ∃ x, tsupport (f i) ⊆ TestFunctions.closedBallR4 x R) ∧
      TestFunctions.HasSeparatedSupportsR4 f d := by
  set Y := LipschitzClasses.params s M hM with hY
  have h' : f ∈ PeriodicSpace.Kind.lipTuplesSpacedInBalls Y .euclidean n d R := h
  obtain ⟨hlip, hball, hsep⟩ := h'
  refine ⟨fun i => ?_, fun i => ?_, hd, fun i k hik => ?_⟩
  · obtain ⟨C, hC, hh⟩ := hlip i
    refine ⟨C, hC, fun x y => ?_⟩
    have e' : PeriodicSpace.Kind.quotDist Y .euclidean x y = TestFunctions.euclidDistR4 x y :=
      PeriodicSpace.EuclideanCase.quotDist_euclidean_eq Y x y
    have := hh x y
    rwa [e'] at this
  · obtain ⟨S, ⟨-, x, rfl⟩, hS⟩ := hball i
    refine ⟨x, ?_⟩
    rw [← supportQ_euclidean_eq_tsupport Y]
    intro (y : Fin 4 → ℝ) hy
    have h₁ : PeriodicSpace.Kind.quotDist Y .euclidean y x ≤ R := hS hy
    exact (PeriodicSpace.EuclideanCase.quotDist_euclidean_eq Y y x).ge.trans h₁
  · refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    have hx' : x ∈ PeriodicSpace.Kind.supportQ Y .euclidean (f i) := by
      rw [supportQ_euclidean_eq_tsupport Y]
      exact hx
    have hy' : y ∈ PeriodicSpace.Kind.supportQ Y .euclidean (f k) := by
      rw [supportQ_euclidean_eq_tsupport Y]
      exact hy
    have h₂ : PeriodicSpace.Kind.setInfDist Y .euclidean
        (PeriodicSpace.Kind.supportQ Y .euclidean (f i))
        (PeriodicSpace.Kind.supportQ Y .euclidean (f k)) ≤
        ENNReal.ofReal (PeriodicSpace.Kind.quotDist Y .euclidean x y) :=
      iInf₂_le_of_le x hx' (iInf₂_le y hy')
    have h₃ := (hsep i k hik).trans h₂
    rwa [PeriodicSpace.EuclideanCase.quotDist_euclidean_eq Y x y] at h₃
theorem cumulantBound_nonneg {N : BoundConstants} (hN : N.Admissible) (n : ℕ)
    (d : ℝ) {R : ℝ} (hR : 0 < R) : 0 ≤ N.cumulantBound n d R := by
  have h₁ := hN.aStar_pos
  have h₂ := hN.ballConst_pos R hR
  unfold BoundConstants.cumulantBound
  positivity
theorem translatedTuplesWithConstants_of_bounds (h : BoundsOnEverySide.TranslatedTuples.Statement)
    (hO : OnePointDifferenceAllRadii) : TranslatedTuplesWithConstants := by
  rintro F N B ⟨L, hLs, K₀, m⟩ K β ρ ν σ hs hlimit hdatum hρs hνs
  simp only at hs ρ ν hρs hνs
  subst hs
  have hKpos := hlimit.cutoff_pos
  have hD := fun j => hdatum j (hKpos j)
  refine h _ (freeMomentConstantsOf F N) K β ρ ν σ hlimit (fun j => F.pos_of_isFirstPassage _ _ (hD j)) ?_
  refine ⟨fun _ _ _ _ _ _ => ENNReal.ofReal_ne_top, ?_, ?_⟩
  · intro j n hn d R hd hR f hf
    obtain ⟨hlip, hball, hsep⟩ := bounds_of_isLipAt hd hf
    have key := B.cumulant_le ⟨K j, hKpos j⟩ (β j) (hD j) (ρ j) (hρs j (hKpos j)) n hn R d
      hR hd f hlip hball hsep
    change ENNReal.ofReal ‖InfiniteLattice.smearedEnergyCumulant (ρ j) f‖ ≤
      ENNReal.ofReal (N.cumulantBound n d R) *
        ENNReal.ofReal (∏ i, TestFunctions.sharpNormR4 F.M (f i))
    rw [← ENNReal.ofReal_mul (cumulantBound_nonneg B.admissible_constants n d hR)]
    exact ENNReal.ofReal_le_ofReal key
  · intro j R hR f x hf hsub
    exact hO F N B ⟨K j, hKpos j⟩ (β j) (hD j) (ρ j) (hρs j (hKpos j)) (ν j)
      (hνs j (hKpos j)) R hR f hf ⟨x, by rwa [← euclidSupp_eq_tsupport]⟩
end YangMills.Construction.SystemsWithFiveBounds.TranslatedTuplesProof
end
