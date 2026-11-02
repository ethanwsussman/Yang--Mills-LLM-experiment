module

public import NoContact.Gradient
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology ContDiff

namespace NoContact

/-- Bounded complex multilinear forms on `L²(ℝ³; ℂ³)` indexed by `ι`. -/
abbrev Form (ι : Type*) := ContinuousMultilinearMap ℂ (fun _ : ι => L2) ℂ

/-- Vanishing on fields with pairwise disjoint compact essential supports in `U`. -/
def Local {ι : Type*} (U : Set X) (D : Form ι) : Prop :=
  ∀ K : ι → Set X, (∀ i, IsCompact (K i)) → (∀ i, K i ⊆ U) →
    Pairwise (fun i j => Disjoint (K i) (K j)) →
    ∀ f : ι → L2, (∀ i, Supported (K i) (f i)) → D f = 0

/-- The gradient hypothesis, with all other slots in the same `L²_U`. -/
def GradientZero {ι : Type*} (U : Set X) (D : Form ι) : Prop :=
  ∀ (i : ι) (u : Potential U) (f : ι → L2), (∀ j, Supported U (f j)) →
    f i = u.gradientLp → D f = 0

/-- Assemble free and frozen slots without changing their index labels. -/
def assemble {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (f : ι → L2) (g : {i // P i} → L2) : ι → L2 :=
  fun i => if h : P i then g ⟨i, h⟩ else f i

/-- Freeze the slots outside `P`, preserving continuous multilinearity. -/
def freeze {ι : Type*} (D : Form ι) (P : ι → Prop) [DecidablePred P]
    (f : ι → L2) : Form {i // P i} where
  toMultilinearMap := D.toMultilinearMap.domDomRestrict P (fun i => f i)
  cont := by
    apply D.cont.comp
    apply continuous_pi
    intro i
    by_cases hi : P i
    · simpa [hi] using (continuous_apply (⟨i, hi⟩ : {i // P i}))
    · simpa [hi] using (continuous_const : Continuous (fun _ : ({i // P i} → L2) => f i))

/-- Evaluation of the partially frozen multilinear form. -/
@[simp] theorem freeze_apply {ι : Type*} (D : Form ι) (P : ι → Prop) [DecidablePred P]
    (f : ι → L2) (g : {i // P i} → L2) : freeze D P f g = D (assemble P f g) := rfl

/-- Restoring the original free entries recovers the original tuple. -/
@[simp] theorem assemble_self {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (f : ι → L2) : assemble P f (fun i => f i) = f := by
  funext i
  simp [assemble]

/-- Assembling free and frozen entries preserves their common support bound. -/
theorem assemble_supported {ι : Type*} (P : ι → Prop) [DecidablePred P]
    {f : ι → L2} {g : {i // P i} → L2} {U : Set X}
    (hf : ∀ i, ¬ P i → Supported U (f i)) (hg : ∀ i, Supported U (g i)) :
    ∀ i, Supported U (assemble P f g i) := by
  intro i
  by_cases hi : P i
  · simpa [assemble, hi] using hg ⟨i, hi⟩
  · simpa [assemble, hi] using hf i hi

/-- The gradient hypothesis is inherited under freezing and restriction to a subset. -/
theorem gradientZero_freeze {ι : Type*} {D : Form ι} {U V : Set X}
    (hD : GradientZero U D) (hVU : V ⊆ U) (P : ι → Prop) [DecidablePred P]
    (f : ι → L2) (hf : ∀ i, ¬ P i → Supported U (f i)) :
    GradientZero V (freeze D P f) := by
  intro i u g hg hi
  apply hD i.val (u.mono hVU) (assemble P f g)
  · exact assemble_supported P hf (fun j => (hg j).mono hVU)
  · simpa [assemble, i.property] using hi

/-- Vanishing for a genuinely separated, nontrivial split of the slots. -/
def SplitZero {ι : Type*} (U : Set X) (D : Form ι) : Prop :=
  ∀ s : Set X, MeasurableSet s → ∀ P : ι → Prop, ∀ f : ι → L2,
    (∃ i, P i) → (∃ j, ¬ P j) →
    (∀ i, Supported U (f i)) →
    (∀ i, P i → Supported s (f i)) →
    (∀ i, ¬ P i → Supported sᶜ (f i)) → D f = 0

end NoContact
