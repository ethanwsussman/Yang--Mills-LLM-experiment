import YangMills.Construction.ResponseInTheExpansion.ColdConditionsHaveOneConstantProof
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesHaveOneCentring
import YangMills.Construction.SixteenPointsOnASmallTorus.LevelsOfARadius
import YangMills.Construction.SixteenPointsOnASmallTorus.ResponsesAreCarriedByAnIsometry
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
open TorusFields TorusLumps RenormalizationStepParameters WeightedResponses ResponseInTheExpansion TestFunctions
private def cellReflection (c : ℕ) (k : Fin 4 → ℕ) (hk : ∀ i, k i = 0 ∨ k i = 1) : TorusIsometry where
  axisPerm := 1
  axisSign := fun i => (-1) ^ k i
  offset := fun i => (k i : ℤ) * (c : ℤ)
  axisSign_unit := fun i => by
    rcases hk i with h | h <;> simp [h]
private theorem iteratedLift_axisPerm (L t : ℕ) (g : TorusIsometry) : (iteratedLift L t g).axisPerm = g.axisPerm := by
  induction t generalizing g with
  | zero => rfl
  | succ t ih => rw [iteratedLift, ih]; rfl
private theorem iteratedLift_axisSign (L t : ℕ) (g : TorusIsometry) : (iteratedLift L t g).axisSign = g.axisSign := by
  induction t generalizing g with
  | zero => rfl
  | succ t ih => rw [iteratedLift, ih]; rfl
private theorem iteratedLift_offset (L t : ℕ) (g : TorusIsometry) (i : Fin 4) :
    (iteratedLift L t g).offset i = (L : ℤ) ^ t * g.offset i := by
  induction t generalizing g with
  | zero => simp [iteratedLift]
  | succ t ih =>
    rw [iteratedLift, ih]
    simp only [TorusIsometry.scaledLift]
    ring
private theorem transports_trivialField (g : TorusIsometry) (n : ℕ) : g.Transports (trivialField n) (trivialField n) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.CoeffUniqueness.trivialField_transports <;> assumption
private theorem cellReflection_involutive (c : ℕ) (k : Fin 4 → ℕ) (hk : ∀ i, k i = 0 ∨ k i = 1) (n : ℕ) :
    Function.Involutive ((cellReflection c k hk).mapSite : TorusSite n → TorusSite n) := by
  intro y
  funext i
  simp only [TorusIsometry.mapSite, cellReflection, Equiv.Perm.one_apply]
  rcases hk i with h | h <;> simp [h]
private theorem reflectedPoint_of_image (a₀ : ℝ) (L s c M m : ℕ) (hM : L ^ s * c = M) (k : Fin 4 → ℕ) (hk : ∀ i, k i = 0 ∨ k i = 1)
    (p p' : TorusPlaquette m)
    (hp : doubledBarycentre p' = doubledSiteImage (iteratedLift L s (cellReflection c k hk)) (doubledBarycentre p)) :
    reflectedPoint a₀ M k p' = reflectedPoint a₀ M 0 p := by
  unfold reflectedPoint
  congr 1
  funext μ
  have e : doubledBarycentre p' μ = ((-1) ^ k μ : ZMod (2 * m)) * doubledBarycentre p μ + 2 * ((k μ : ZMod (2 * m)) * (M : ZMod (2 * m))) := by
    rw [hp]
    simp only [doubledSiteImage, iteratedLift_axisPerm, iteratedLift_axisSign, iteratedLift_offset, cellReflection, Equiv.Perm.one_apply]
    subst hM
    push_cast
    ring
  have e2 : ((-1 : ZMod (2 * m)) ^ k μ * (doubledBarycentre p' μ - 2 * (M : ZMod (2 * m)) * (k μ : ZMod (2 * m)))) =
      (-1 : ZMod (2 * m)) ^ (0 : Fin 4 → ℕ) μ * (doubledBarycentre p μ - 2 * (M : ZMod (2 * m)) * (((0 : Fin 4 → ℕ) μ : ℕ) : ZMod (2 * m))) := by
    rw [e]
    rcases hk μ with h | h <;> simp [h]
  rw [e2]
private theorem reflectedWeight_transported (a₀ : ℝ) (L s c M m : ℕ) (hM : L ^ s * c = M) (k : Fin 4 → ℕ) (hk : ∀ i, k i = 0 ∨ k i = 1)
    (h : EuclideanFourSpace → ℝ) :
    WeightTransported (iteratedLift L s (cellReflection c k hk)) (reflectedWeight (m := m) a₀ M 0 h) (reflectedWeight a₀ M k h) := by
  intro p p' hp
  simp only [reflectedWeight]
  rw [reflectedPoint_of_image a₀ L s c M m hM k hk p.1 p'.1 hp]
theorem reflectedCentringConst (hR : responseIsometryInvariantStatement) (hV : levelsBelowRadiusStatement) :
    reflectedCentringConstStatement := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hV a ha
  refine ⟨L₁, r₁, C₁, hr₁, ?_⟩
  intro L hL hLge T hTa hTL hD hCS hCH hrt hC
  obtain ⟨y₁, Y₁⟩ := H₁ L hL hLge T hTa hTL hD hCS hCH hrt hC
  refine ⟨max y₁ T.floorMin, ?_⟩
  intro y hy hRR hW
  have hadm : (T.stepParameters y).Admissible := hD.fits y (le_trans (le_max_right _ _) hy)
  have hLev := Y₁ y (le_trans (le_max_left _ _) hy) hRR hW
  intro Ξ β K κ al ρ H Λ h hdat hκ hρ hρl _ k
  unfold centring reflectedCentring
  rcases hs : radiusLevel (T.stepParameters y) β K ρ with _ | s
  · rfl
  · obtain ⟨-, hlev⟩ := hLev Ξ β K κ ρ hdat hκ hρ hρl s hs
    obtain ⟨-, hsκ, -, hblock⟩ := hlev s le_rfl
    have hk : ∀ i, ((k i : ℕ)) = 0 ∨ ((k i : ℕ)) = 1 := fun i => by
      have := (k i).isLt
      omega
    have hL0 : 0 < (T.stepParameters y).side := Nat.pos_of_ne_zero (NeZero.ne _)
    have hn : (T.stepParameters y).n₀ ≤ twoCellSide (T.stepParameters y).side κ s :=
      le_trans (Nat.le_mul_of_pos_left _ hL0) hblock.2
    have hM : (T.stepParameters y).side ^ s * (T.stepParameters y).side ^ (κ - s) = (T.stepParameters y).side ^ κ := by
      rw [← pow_add]
      congr 1
      omega
    simp only [meanAtTrivial]
    rw [← Equiv.sum_comp (Function.Involutive.toPerm _ (cellReflection_involutive ((T.stepParameters y).side ^ (κ - s)) (fun μ => (k μ : ℕ)) hk
      (twoCellSide (T.stepParameters y).side κ s)))]
    refine Finset.sum_congr rfl fun z _ => ?_
    exact hR (T.stepParameters y) hadm β (flowCouplings (T.stepParameters y) β) al s (twoCellSide (T.stepParameters y).side κ s) hn
      (cellReflection ((T.stepParameters y).side ^ (κ - s)) (fun μ => (k μ : ℕ)) hk) (trivialField _) (trivialField _) _ _ z
      (transports_trivialField _ _) (reflectedWeight_transported _ _ _ _ _ _ hM _ hk h)
end YangMills.Construction.SmallTorusCopies
end
