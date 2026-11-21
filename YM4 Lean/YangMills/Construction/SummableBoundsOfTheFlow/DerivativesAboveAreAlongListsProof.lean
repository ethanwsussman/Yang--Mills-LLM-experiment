import YangMills.Construction.SummableBoundsOfTheFlow.ByPartsAtABondProof
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveAreAlongLists
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
set_option linter.unusedSectionVars false
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace IteratedDerivative
namespace MixedDerivAlong
variable {F : BlockFrame}
open Classical in
def paramEmbed {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3)) :
    (Fin (l + k) → ℝ) →L[ℝ] StepVariable (finiteCells F) × (Fin k → ℝ) :=
  ContinuousLinearMap.prod
    (∑ i, (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => EuclideanSpace ℝ (Fin 3)) (b i)).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (l + k) => ℝ) (Fin.castAdd k i)).smulRight (u i)))
    (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (l + k) => ℝ) (Fin.natAdd l i))
theorem paramEmbed_fst {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (τ : Fin (l + k) → ℝ) : open Classical in
    (paramEmbed b u τ).1 = ∑ i, τ (Fin.castAdd k i) • Pi.single (b i) (u i) := by
  simp [paramEmbed]
theorem jointDisplacement_eq_comp {l k : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F))
    (V : F.GaugeField F.top) (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    jointDisplacement G η V b u c X = fun τ => rotatedEval G V c X ((η, 0) + paramEmbed b u τ) := by
  funext τ
  simp only [jointDisplacement, rotatedEval, displacedPoint, Prod.fst_add, Prod.snd_add, zero_add, paramEmbed_fst]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun i _ => Pi.single_smul _ _ _
theorem paramEmbed_single_castAdd {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (i : Fin l) : (paramEmbed b u (Pi.single (Fin.castAdd k i) 1) : StepVariable (finiteCells F) × (Fin k → ℝ)) =
      variableDirection (Fin k → ℝ) (open Classical in Pi.single (b i) (u i)) := by
  classical
  refine Prod.ext ?_ ?_
  · simp only [paramEmbed_fst, variableDirection]
    rw [Finset.sum_eq_single i]
    · simp
    · intro i' _ hi
      have : Fin.castAdd k i' ≠ Fin.castAdd k i := fun h => hi (Fin.castAdd_injective _ _ h)
      simp [Pi.single_eq_of_ne this]
    · simp
  · funext j
    have : Fin.natAdd l j ≠ Fin.castAdd k i := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [paramEmbed, variableDirection, Pi.single_eq_of_ne this]
theorem paramEmbed_single_natAdd {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (i : Fin k) : (paramEmbed b u (Pi.single (Fin.natAdd l i) 1) : StepVariable (finiteCells F) × (Fin k → ℝ)) =
      (0, Pi.single i 1) := by
  classical
  refine Prod.ext ?_ ?_
  · simp only [paramEmbed_fst]
    refine Finset.sum_eq_zero fun i' _ => ?_
    have : Fin.castAdd k i' ≠ Fin.natAdd l i := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [Pi.single_eq_of_ne this]
  · funext j
    by_cases hj : j = i
    · subst hj
      simp [paramEmbed]
    · have : Fin.natAdd l j ≠ Fin.natAdd l i := fun h => hj (Fin.natAdd_injective _ _ h)
      simp [paramEmbed, Pi.single_eq_of_ne this, Pi.single_eq_of_ne hj]
theorem jointMixedDeriv_eq_derivAlong (h : DerivAlongRulesHold) (V : F.GaugeField F.top)
    (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (η : StepVariable (finiteCells F)) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (l : ℕ)
    (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (hq : ContDiffAt ℝ ((l + k : ℕ) : WithTop ℕ∞) (rotatedEval G V c X) (η, 0)) :
    jointMixedDeriv G η V b u c X = derivAlong (rotatedEval G V c X)
      (pointDirections b u ++ parameterDirections _ _ (parameterBasis k)) (η, 0) := by
  have e0 : ((η, 0) : StepVariable (finiteCells F) × (Fin k → ℝ)) + paramEmbed b u 0 = (η, 0) := by simp
  have hq0 : ContDiffAt ℝ ((l + k : ℕ) : WithTop ℕ∞) (rotatedEval G V c X)
      ((η, 0) + paramEmbed b u (0 : Fin (l + k) → ℝ)) := by rw [e0]; exact hq
  have hm : ContDiffAt ℝ ((l + k : ℕ) : WithTop ℕ∞) (jointDisplacement G η V b u c X) 0 := by
    rw [jointDisplacement_eq_comp]
    exact ContDiffAt.comp (0 : Fin (l + k) → ℝ) hq0
      (contDiff_const.add (paramEmbed b u).contDiff).contDiffAt
  unfold jointMixedDeriv
  rw [((h.1 _ ℝ).iteratedFDeriv_eq _ _ _ _ hm), jointDisplacement_eq_comp,
    h.2 _ _ ℝ (rotatedEval G V c X) (paramEmbed b u) (η, 0) 0 _ (by simpa using hq0), e0]
  congr 1
  rw [List.map_ofFn, List.ofFn_add]
  congr 1
  · refine List.ofFn_inj.2 ?_
    funext i
    exact paramEmbed_single_castAdd b u i
  · simp only [parameterDirections, parameterBasis, List.map_ofFn]
    refine List.ofFn_inj.2 ?_
    funext i
    exact paramEmbed_single_natAdd b u i
section Smooth
variable (n : ℕ)
abbrev CoordSlot (F : BlockFrame) (n : ℕ) : Type := Fin (n + 2) × ↥(chordBonds (finiteCells F)) × Fin 3
def coordReadout (k : ℕ) (e : CoordSlot F n ≃ Fin (Fintype.card (CoordSlot F n))) :
    StepVariable (finiteCells F) × (Fin k → ℝ) →L[ℝ] (Fin (Fintype.card (CoordSlot F n) + k) → ℝ) :=
  ContinuousLinearMap.pi fun j => Fin.addCases (motive := fun _ =>
      StepVariable (finiteCells F) × (Fin k → ℝ) →L[ℝ] ℝ)
    (fun i => if (e.symm i).1 = 0 then
        (((EuclideanSpace.proj (e.symm i).2.2 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(chordBonds (finiteCells F)) =>
            EuclideanSpace ℝ (Fin 3)) (e.symm i).2.1)).comp
          (ContinuousLinearMap.fst ℝ _ _)
      else 0)
    (fun i => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).comp
      (ContinuousLinearMap.snd ℝ _ _)) j
theorem coordReadout_castAdd (k : ℕ) (e : CoordSlot F n ≃ Fin (Fintype.card (CoordSlot F n)))
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (i : Fin (Fintype.card (CoordSlot F n))) :
    coordReadout n k e p (Fin.castAdd k i) =
      if (e.symm i).1 = 0 then p.1 (e.symm i).2.1 (e.symm i).2.2 else 0 := by
  unfold coordReadout
  simp only [ContinuousLinearMap.coe_pi', Fin.addCases_left]
  split_ifs <;> simp
theorem coordReadout_natAdd (k : ℕ) (e : CoordSlot F n ≃ Fin (Fintype.card (CoordSlot F n)))
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (i : Fin k) :
    coordReadout n k e p (Fin.natAdd _ i) = p.2 i := by
  unfold coordReadout
  simp only [ContinuousLinearMap.coe_pi', Fin.addCases_right]
  simp
theorem euclidean_sum_single (x : EuclideanSpace ℝ (Fin 3)) :
    ∑ q, x q • EuclideanSpace.single q (1 : ℝ) = x := by apply _root_.YangMills.Construction.BondIntegration.sum_smul_bondBasis <;> assumption
open Classical in
theorem paramEmbed_coordReadout (k : ℕ) (e : CoordSlot F n ≃ Fin (Fintype.card (CoordSlot F n)))
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) :
    paramEmbed (fun i => (e.symm i).2.1) (fun i => EuclideanSpace.single (e.symm i).2.2 (1 : ℝ))
      (coordReadout n k e p) = p := by
  refine Prod.ext ?_ ?_
  · rw [paramEmbed_fst]
    simp only [coordReadout_castAdd]
    rw [Equiv.sum_comp e.symm (fun s : CoordSlot F n => (if s.1 = 0 then p.1 s.2.1 s.2.2 else 0) •
      (Pi.single s.2.1 (EuclideanSpace.single s.2.2 (1 : ℝ)) : StepVariable (finiteCells F)))]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (0 : Fin (n + 2))]
    · simp only [if_true]
      rw [Fintype.sum_prod_type]
      have hb : ∀ β : ↥(chordBonds (finiteCells F)), ∑ q : Fin 3, p.1 β q •
          (Pi.single β (EuclideanSpace.single q (1 : ℝ)) : StepVariable (finiteCells F)) = Pi.single β (p.1 β) := by
        intro β
        conv_rhs => rw [← euclidean_sum_single (p.1 β)]
        rw [show (Pi.single β (∑ q : Fin 3, p.1 β q • EuclideanSpace.single q (1 : ℝ)) : StepVariable (finiteCells F)) =
          ∑ q : Fin 3, Pi.single β (p.1 β q • EuclideanSpace.single q (1 : ℝ)) from
          map_sum (AddMonoidHom.single (fun _ : ↥(chordBonds (finiteCells F)) => EuclideanSpace ℝ (Fin 3)) β) _ _]
        exact Finset.sum_congr rfl fun q _ => (Pi.single_smul _ _ _).symm
      simp only [hb]
      exact Finset.univ_sum_single p.1
    · intro r _ hr
      simp [hr]
    · simp
  · funext j
    have := coordReadout_natAdd n k e p j
    simpa [paramEmbed] using this
theorem contDiffAt_rotatedEval {k : ℕ} (V : F.GaugeField F.top)
    (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hne : Nonempty ↥(chordBonds (finiteCells F)))
    (hk : ∀ (l : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3)),
      2 ≤ l → (∀ i, ‖u i‖ = 1) → ContDiffAt ℝ ((l + k : ℕ) : WithTop ℕ∞) (jointDisplacement G η V b u c X) 0) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (rotatedEval G V c X) (η, 0) := by
  classical
  let e := Fintype.equivFin (CoordSlot F n)
  have hcard : n + 2 ≤ Fintype.card (CoordSlot F n) := by
    have h1 : 0 < Fintype.card ↥(chordBonds (finiteCells F)) := Fintype.card_pos
    simp only [Fintype.card_prod, Fintype.card_fin]
    nlinarith [Nat.mul_le_mul_left (n + 2) (show 1 ≤ Fintype.card ↥(chordBonds (finiteCells F)) * 3 by omega)]
  have h1 := hk _ (fun i => (e.symm i).2.1) (fun i => EuclideanSpace.single (e.symm i).2.2 (1 : ℝ))
    (by omega) (fun i => by simp)
  have hread : rotatedEval G V c X = fun q => jointDisplacement G η V (fun i => (e.symm i).2.1)
      (fun i => EuclideanSpace.single (e.symm i).2.2 (1 : ℝ)) c X (coordReadout n k e (q - (η, 0))) := by
    funext q
    rw [jointDisplacement_eq_comp]
    beta_reduce
    rw [paramEmbed_coordReadout]
    simp
  rw [hread]
  have h0 : coordReadout n k e (((η, 0) : StepVariable (finiteCells F) × (Fin k → ℝ)) - (η, 0)) = 0 := by simp
  have h2 : ContDiffAt ℝ ((Fintype.card (CoordSlot F n) + k : ℕ) : WithTop ℕ∞)
      (jointDisplacement G η V (fun i => (e.symm i).2.1)
        (fun i => EuclideanSpace.single (e.symm i).2.2 (1 : ℝ)) c X)
      (coordReadout n k e (((η, 0) : StepVariable (finiteCells F) × (Fin k → ℝ)) - (η, 0))) := by
    rw [h0]; exact h1
  have h3 := ContDiffAt.comp (η, 0) h2
    (((coordReadout n k e).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt)
  exact h3.of_le (by exact_mod_cast (show n ≤ Fintype.card (CoordSlot F n) + k by omega))
end Smooth
end MixedDerivAlong
open MixedDerivAlong in
theorem jointMixedDerivEqDerivAlong_of_derivAlongRulesHold (h : DerivAlongRulesHold) :
    JointMixedDerivEqDerivAlong := by
  intro F V G η k c X
  exact ⟨fun hne hk n => contDiffAt_rotatedEval n V G η c X hne hk,
    fun l b u hq => jointMixedDeriv_eq_derivAlong h V G η k c X l b u hq⟩
end IteratedDerivative
end YangMills.Construction
end
