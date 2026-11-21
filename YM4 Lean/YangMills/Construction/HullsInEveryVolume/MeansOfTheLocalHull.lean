import YangMills.Construction.HullsInEveryVolume.LocalHullOfAChain
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsAGaussianChainProof
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadiusProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace HullMeans
open TorusLumps StepSettings TorusFields WeightedResponses HullTrees
  RenormalizationStepParameters StepReturn
section Fibres
variable {X : Type} [MeasurableSpace X]
theorem measurableSet_comp_of_fibres {A : Type} [Countable A] {f : X → A} (h : ∀ a, MeasurableSet {x | f x = a})
    (P : A → Prop) : MeasurableSet {x | P (f x)} := by apply _root_.YangMills.SharedProofs.p67002 <;> assumption
theorem measurableSet_comp₃_of_fibres {A B C : Type} [Countable A] [Countable B] [Countable C] {f₁ : X → A}
    {f₂ : X → B} {f₃ : X → C} (h₁ : ∀ a, MeasurableSet {x | f₁ x = a}) (h₂ : ∀ a, MeasurableSet {x | f₂ x = a})
    (h₃ : ∀ a, MeasurableSet {x | f₃ x = a}) (G : A → B → C → Prop) :
    MeasurableSet {x | G (f₁ x) (f₂ x) (f₃ x)} := by
  have e : {x | G (f₁ x) (f₂ x) (f₃ x)} = ⋃ a : A, ⋃ b : B, ⋃ c : C, ⋃ (_ : G a b c),
      ({x | f₁ x = a} ∩ {x | f₂ x = b}) ∩ {x | f₃ x = c} := by
    ext x
    simp
  rw [e]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun c =>
    MeasurableSet.iUnion fun _ => ((h₁ a).inter (h₂ b)).inter (h₃ c)
theorem measurableSet_sigma_fst_eq {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
end Fibres
section LocalHull
variable {ℓ : StepParameters} (T : StageTower ℓ) (s₁ : ℝ)
open Classical in
theorem measurableSet_localHullData_fst_eq (hC : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (hq : ∀ (n : ℕ) [NeZero n], Measurable (stageState T 0 n)) (j : ℕ) :
    ∀ (n : ℕ) [NeZero n] (Q a : Finset (TorusSite n)),
      MeasurableSet {w : MarkedSample ℓ j n | (localHullData T s₁ j n w Q).1 = a} := by
  induction j with
  | zero =>
    intro n _ Q a
    have h0 : ∀ b : Finset (TorusSite n), MeasurableSet {w : MarkedSample ℓ 0 n | hullSet T 0 n w = b} := by
      intro b
      have h : MeasurableSet {z : StageState T 0 n | z.2.1 = b} := measurable_snd (measurableSet_sigma_fst_eq b)
      exact hq n h
    exact measurableSet_comp_of_fibres h0 (fun Y => Y ∩ Q = a)
  | succ j ih =>
    intro n _ Q a
    have h₁ : ∀ a : Finset (TorusSite n), MeasurableSet
        {u : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n | hotCoreSites (T.stage j).toStepSetup u.2.2.1 = a} := fun a =>
      (measurable_fst.comp (measurable_snd.comp measurable_snd)) (hC (T.stage j).toStepSetup n a)
    have h₂ : ∀ a : Finset (TorusBond (n * ℓ.side)), MeasurableSet
        {u : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n | (u.2.2.2 : Finset (TorusBond (n * ℓ.side))) = a} := by
      intro a
      have hm : Measurable fun u : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n => u.2.2.2 :=
        measurable_snd.comp (measurable_snd.comp measurable_snd)
      have hs : MeasurableSet ({a} : Set (BondSet (n * ℓ.side))) := MeasurableSpace.measurableSet_top
      exact hm hs
    have h₃ : ∀ a : Finset (TorusSite (n * ℓ.side)), MeasurableSet
        {u : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n |
          (localHullData T s₁ j (n * ℓ.side) u.1 (sitesInBlocks ℓ.side Q)).1 = a} := fun a =>
      measurable_fst (ih (n * ℓ.side) (sitesInBlocks ℓ.side Q) a)
    exact measurableSet_comp₃_of_fibres h₁ h₂ h₃ (fun C (b : Finset (TorusBond (n * ℓ.side))) Y =>
      thickening ((T.stage j).toStepSetup.nextRange / 2) ((C ∩ Q) ∪ (coreBlocks ℓ.side (T.stage j).toStepSetup.range
        (attachedSites ℓ.side (T.stage j).toStepSetup.range (b.filter fun e => e.1 ∈ sitesInBlocks ℓ.side Q) Y (C ∩ Q)) ∩ Q)) ∩ Q = a)
open Classical in
theorem measurable_localHullData_snd (hC : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (hq : ∀ (n : ℕ) [NeZero n], Measurable (stageState T 0 n)) (j : ℕ) :
    ∀ (n : ℕ) [NeZero n] (Q : Finset (TorusSite n)) (y : TorusSite n),
      Measurable fun w : MarkedSample ℓ j n => (localHullData T s₁ j n w Q).2 y := by
  induction j with
  | zero =>
    intro n _ Q y
    exact measurable_const
  | succ j ih =>
    intro n _ Q y
    have h₁ : ∀ a : Finset (TorusSite n), MeasurableSet
        {u : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n | hotCoreSites (T.stage j).toStepSetup u.2.2.1 = a} := fun a =>
      (measurable_fst.comp (measurable_snd.comp measurable_snd)) (hC (T.stage j).toStepSetup n a)
    have h₂ : ∀ a : Finset (TorusBond (n * ℓ.side)), MeasurableSet
        {u : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n | (u.2.2.2 : Finset (TorusBond (n * ℓ.side))) = a} := by
      intro a
      have hm : Measurable fun u : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n => u.2.2.2 :=
        measurable_snd.comp (measurable_snd.comp measurable_snd)
      have hs : MeasurableSet ({a} : Set (BondSet (n * ℓ.side))) := MeasurableSpace.measurableSet_top
      exact hm hs
    have h₃ : ∀ a : Finset (TorusSite (n * ℓ.side)), MeasurableSet
        {u : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n |
          (localHullData T s₁ j (n * ℓ.side) u.1 (sitesInBlocks ℓ.side Q)).1 = a} := fun a =>
      measurable_fst (measurableSet_localHullData_fst_eq T s₁ hC hq j (n * ℓ.side) (sitesInBlocks ℓ.side Q) a)
    have hZ : MeasurableSet {u : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n |
        y ∈ (hotCoreSites (T.stage j).toStepSetup u.2.2.1 ∩ Q) ∪ (coreBlocks ℓ.side (T.stage j).toStepSetup.range
          (attachedSites ℓ.side (T.stage j).toStepSetup.range
            ((show Finset (TorusBond (n * ℓ.side)) from u.2.2.2).filter fun e => e.1 ∈ sitesInBlocks ℓ.side Q)
            (localHullData T s₁ j (n * ℓ.side) u.1 (sitesInBlocks ℓ.side Q)).1
            (hotCoreSites (T.stage j).toStepSetup u.2.2.1 ∩ Q)) ∩ Q)} :=
      measurableSet_comp₃_of_fibres h₁ h₂ h₃ (fun C (b : Finset (TorusBond (n * ℓ.side))) Y =>
        y ∈ (C ∩ Q) ∪ (coreBlocks ℓ.side (T.stage j).toStepSetup.range
          (attachedSites ℓ.side (T.stage j).toStepSetup.range (b.filter fun e => e.1 ∈ sitesInBlocks ℓ.side Q) Y (C ∩ Q)) ∩ Q))
    have hY : MeasurableSet {u : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n |
        y ∈ thickening ((T.stage j).toStepSetup.nextRange / 2) ((hotCoreSites (T.stage j).toStepSetup u.2.2.1 ∩ Q) ∪
          (coreBlocks ℓ.side (T.stage j).toStepSetup.range
          (attachedSites ℓ.side (T.stage j).toStepSetup.range
            ((show Finset (TorusBond (n * ℓ.side)) from u.2.2.2).filter fun e => e.1 ∈ sitesInBlocks ℓ.side Q)
            (localHullData T s₁ j (n * ℓ.side) u.1 (sitesInBlocks ℓ.side Q)).1
            (hotCoreSites (T.stage j).toStepSetup u.2.2.1 ∩ Q)) ∩ Q)) ∩ Q} :=
      measurableSet_comp₃_of_fibres h₁ h₂ h₃ (fun C (b : Finset (TorusBond (n * ℓ.side))) Y =>
        y ∈ thickening ((T.stage j).toStepSetup.nextRange / 2) ((C ∩ Q) ∪ (coreBlocks ℓ.side (T.stage j).toStepSetup.range
          (attachedSites ℓ.side (T.stage j).toStepSetup.range (b.filter fun e => e.1 ∈ sitesInBlocks ℓ.side Q) Y (C ∩ Q)) ∩ Q)) ∩ Q)
    have hsum : Measurable fun u : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n =>
        ∑ z ∈ sitesInBlocks ℓ.side {y} ∩ (localHullData T s₁ j (n * ℓ.side) u.1 (sitesInBlocks ℓ.side Q)).1,
          (localHullData T s₁ j (n * ℓ.side) u.1 (sitesInBlocks ℓ.side Q)).2 z := by
      have e : (fun u : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n =>
          ∑ z ∈ sitesInBlocks ℓ.side {y} ∩ (localHullData T s₁ j (n * ℓ.side) u.1 (sitesInBlocks ℓ.side Q)).1,
            (localHullData T s₁ j (n * ℓ.side) u.1 (sitesInBlocks ℓ.side Q)).2 z) = fun u =>
          ∑ z ∈ sitesInBlocks ℓ.side {y}, if z ∈ (localHullData T s₁ j (n * ℓ.side) u.1 (sitesInBlocks ℓ.side Q)).1 then
            (localHullData T s₁ j (n * ℓ.side) u.1 (sitesInBlocks ℓ.side Q)).2 z else 0 := by
        funext u
        rw [Finset.sum_ite_mem]
      rw [e]
      refine Finset.measurable_sum _ fun z _ => ?_
      have hm : MeasurableSet {u : MarkedSample ℓ j (n * ℓ.side) × StepOutcome ℓ n |
          z ∈ (localHullData T s₁ j (n * ℓ.side) u.1 (sitesInBlocks ℓ.side Q)).1} :=
        measurableSet_comp_of_fibres h₃ (fun Y => z ∈ Y)
      exact Measurable.ite hm ((ih (n * ℓ.side) (sitesInBlocks ℓ.side Q) z).comp measurable_fst) measurable_const
    exact Measurable.ite hZ (measurable_const.add hsum) (Measurable.ite hY measurable_const measurable_const)
end LocalHull
end HullMeans
theorem HullTrees.EventuallyInParameters.mono_of_imp {P Q : RenormalizationStepParameters.ParameterAssignment →
      WeightedResponses.ResponseParameters → ℝ → Prop}
    (h : ∀ Tb Kr y, Odd Tb.side → Tb.Admissible → Tb.floorMin ≤ y →
      (∀ y' : ℝ, Kr.Admissible (Tb.stepParameters y')) → StepReturn.ExpansionReturnsAt (Tb.stepParameters y) →
      (∀ β : ℝ, y ≤ β → TorusLumps.HasExpansion (Tb.stepParameters y) 0 β (TorusLumps.wilsonWeight β)) →
      P Tb Kr y → Q Tb Kr y)
    (hP : HullTrees.EventuallyInParameters P) : HullTrees.EventuallyInParameters Q := by
  intro a ha
  obtain ⟨L₁, r₁, c₁, p₁, h₁⟩ := hP a ha
  refine ⟨L₁, r₁, c₁, p₁, fun L hL hLL Tb e1 e2 hD hC hH hrt hc => ?_⟩
  obtain ⟨M₁, k₁⟩ := h₁ L hL hLL Tb e1 e2 hD hC hH hrt hc
  refine ⟨M₁, fun Kr hK e3 e4 hF hR => ?_⟩
  obtain ⟨y₁, l₁⟩ := k₁ Kr hK e3 e4 hF hR
  exact ⟨max y₁ Tb.floorMin, fun y hy hr hw => h _ _ _ (e2 ▸ hL) hD ((le_max_right _ _).trans hy) hF hr hw
    (l₁ y ((le_max_left _ _).trans hy) hr hw)⟩
namespace HullMeans
open TorusLumps StepSettings TorusFields WeightedResponses HullTrees
  RenormalizationStepParameters StepReturn
variable {ℓ : StepParameters}
theorem hasExpansion_expansionCoupling {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ}
    {D : TorusFunctional} (hx : ℓ.y₁ ≤ x) (hD : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
theorem y₁_le_couplingFlow_of_le_crossing {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ)
    (hW : ∀ β : ℝ, ℓ.y₁ ≤ β → HasExpansion ℓ 0 β (wilsonWeight β)) (hB : 0 ≤ ℓ.B) {g β : ℝ} {K : ℕ}
    (hy : ℓ.y₁ ≤ (g ^ 2)⁻¹) (hβ : windowUpper ℓ g ≤ β) (hK : IsFirstCrossing ℓ (windowUpper ℓ g) β K) :
    ∀ j ≤ K, ℓ.y₁ ≤ (couplingFlow ℓ β j).1 := by
  have hΞ : ℓ.y₁ ≤ windowUpper ℓ g := by
    unfold windowUpper
    linarith
  have hβy : ℓ.y₁ ≤ β := hΞ.trans hβ
  have hlt : ∀ j < K, ℓ.y₁ ≤ (couplingFlow ℓ β j).1 := fun j hj => hΞ.trans (hK.2 j hj).le
  have hrow : ∀ t : ℕ, (∀ j < t, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) →
      HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2 := by
    intro t
    induction t with
    | zero => exact fun _ => hW β hβy
    | succ t ih =>
      intro hj
      exact (hasExpansion_expansionCoupling hR (hj t (Nat.lt_succ_self t))
        (ih fun j hjt => hj j (Nat.lt_succ_of_lt hjt))).1
  intro j hj
  rcases Nat.lt_or_ge j K with h | h
  · exact hlt j h
  · have hjK : j = K := le_antisymm hj h
    subst hjK
    cases j with
    | zero => exact hβy
    | succ j =>
      have h1 := abs_le.mp (hasExpansion_expansionCoupling hR (hlt j (Nat.lt_succ_self j))
        (hrow j fun i hi => hlt i (hi.trans (Nat.lt_succ_self j)))).2
      have h2 := hK.2 j (Nat.lt_succ_self j)
      have e : (couplingFlow ℓ β (j + 1)).1 =
          expansionCoupling ℓ j (couplingFlow ℓ β j).1 (couplingFlow ℓ β j).2 := rfl
      unfold windowUpper at h2
      rw [e]
      linarith [h1.1]
end HullMeans
end YangMills.Construction
end
