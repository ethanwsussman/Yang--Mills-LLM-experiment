module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Tactic

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NoContact

/-- Euclidean space `ℝ³` with Lebesgue measure. -/
abbrev X := EuclideanSpace ℝ (Fin 3)
/-- The coefficient space `ℂ³` of the vector fields. -/
abbrev E := EuclideanSpace ℂ (Fin 3)
/-- The ambient space `L²(ℝ³; ℂ³)`. -/
abbrev L2 := Lp E 2 (volume : Measure X)

/-- An `L²` field vanishes almost everywhere outside `s`. -/
def Supported (s : Set X) (f : L2) : Prop :=
  ∀ᵐ x ∂volume, x ∉ s → f x = 0

/-- Enlarge an essential support set. -/
theorem Supported.mono {s t : Set X} {f : L2} (hf : Supported s f)
    (hst : s ⊆ t) : Supported t f :=
  Filter.Eventually.mono hf fun _ hx ht => hx (fun hs => ht (hst hs))

/-- The zero field is supported in every set. -/
theorem supported_zero (s : Set X) : Supported s (0 : L2) := by
  filter_upwards [Lp.coeFn_zero E 2 (volume : Measure X)] with x hx
  intro _
  exact hx

/-- Addition preserves essential support. -/
theorem Supported.add {s : Set X} {f g : L2} (hf : Supported s f)
    (hg : Supported s g) : Supported s (f + g) := by
  filter_upwards [hf, hg, Lp.coeFn_add f g] with x hx hy hxy
  intro hs
  simpa [hx hs, hy hs] using hxy

/-- Scalar multiplication preserves essential support. -/
theorem Supported.smul {s : Set X} {f : L2} (hf : Supported s f) (c : ℂ) :
    Supported s (c • f) := by
  filter_upwards [hf, Lp.coeFn_smul c f] with x hx hcx
  intro hs
  simpa [hx hs] using hcx

/-- Subtraction preserves essential support. -/
theorem Supported.sub {s : Set X} {f g : L2} (hf : Supported s f)
    (hg : Supported s g) : Supported s (f - g) := by
  simpa [sub_eq_add_neg] using hf.add (hg.smul (-1))

/-- The submodule of fields vanishing almost everywhere outside `U`. -/
def l2Submodule (U : Set X) : Submodule ℂ L2 where
  carrier := {f | Supported U f}
  zero_mem' := supported_zero U
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c _ hf => hf.smul c

/-- `L²(U; ℂ³)`, extended by zero to `ℝ³`. -/
abbrev L2U (U : Set X) := l2Submodule U

/-- Multiplication by the indicator of a measurable set. -/
def cut (s : Set X) (hs : MeasurableSet s) (f : L2) : L2 :=
  ((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator f)

/-- A cut agrees almost everywhere with the pointwise indicator product. -/
theorem cut_ae (s : Set X) (hs : MeasurableSet s) (f : L2) :
    cut s hs f =ᵐ[volume] s.indicator f := MemLp.coeFn_toLp _

/-- A field cut to `s` is essentially supported in `s`. -/
theorem cut_supported (s : Set X) (hs : MeasurableSet s) (f : L2) :
    Supported s (cut s hs f) := by
  filter_upwards [cut_ae s hs f] with x hx
  intro hxs
  simpa [Set.indicator_of_notMem hxs] using hx

/-- Cutting a field to its essential support preserves its `L²` class. -/
theorem cut_eq_self {s : Set X} (hs : MeasurableSet s) {f : L2}
    (hf : Supported s f) : cut s hs f = f := by
  apply Lp.ext
  filter_upwards [cut_ae s hs f, hf] with x hx hf
  by_cases hxs : x ∈ s
  · simpa [Set.indicator_of_mem hxs] using hx
  · simpa [Set.indicator_of_notMem hxs, hf hxs] using hx

/-- Fields supported in `s` are exactly the fixed points of cutting to `s`. -/
theorem cut_eq_self_iff {s : Set X} (hs : MeasurableSet s) (f : L2) :
    cut s hs f = f ↔ Supported s f := by
  constructor
  · intro h
    exact h ▸ cut_supported s hs f
  · exact cut_eq_self hs

/-- Indicator multiplication preserves addition. -/
theorem cut_add (s : Set X) (hs : MeasurableSet s) (f g : L2) :
    cut s hs (f + g) = cut s hs f + cut s hs g := by
  apply Lp.ext
  filter_upwards [cut_ae s hs (f + g), cut_ae s hs f, cut_ae s hs g,
    Lp.coeFn_add f g, Lp.coeFn_add (cut s hs f) (cut s hs g)] with x h₁ h₂ h₃ h₄ h₅
  by_cases hx : x ∈ s <;> simp_all

/-- Indicator multiplication preserves complex scalar multiplication. -/
theorem cut_smul (s : Set X) (hs : MeasurableSet s) (c : ℂ) (f : L2) :
    cut s hs (c • f) = c • cut s hs f := by
  apply Lp.ext
  filter_upwards [cut_ae s hs (c • f), cut_ae s hs f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (cut s hs f)] with x h₁ h₂ h₃ h₄
  by_cases hx : x ∈ s <;> simp_all

/-- Indicator multiplication does not increase the `L²` norm. -/
theorem norm_cut_le (s : Set X) (hs : MeasurableSet s) (f : L2) :
    ‖cut s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cut_ae s hs f] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- Indicator multiplication as a continuous linear map. -/
def cutCLM (s : Set X) (hs : MeasurableSet s) : L2 →L[ℂ] L2 :=
  LinearMap.mkContinuous
    { toFun := cut s hs
      map_add' := cut_add s hs
      map_smul' := cut_smul s hs }
    1 (by intro f; simpa using norm_cut_le s hs f)

/-- Evaluation of the indicator projection. -/
@[simp] theorem cutCLM_apply (s : Set X) (hs : MeasurableSet s) (f : L2) :
    cutCLM s hs f = cut s hs f := rfl

/-- Fields supported in a fixed measurable set form a closed subspace. -/
theorem isClosed_supported (s : Set X) (hs : MeasurableSet s) :
    IsClosed {f : L2 | Supported s f} := by
  have : {f : L2 | Supported s f} = {f | cutCLM s hs f = f} := by
    ext f
    exact (cut_eq_self_iff hs f).symm
  rw [this]
  exact isClosed_eq (cutCLM s hs).continuous continuous_id

/-- Split a field between a measurable set and its complement. -/
theorem cut_add_compl (s : Set X) (hs : MeasurableSet s) (f : L2) :
    cut s hs f + cut sᶜ hs.compl f = f := by
  apply Lp.ext
  filter_upwards [cut_ae s hs f, cut_ae sᶜ hs.compl f,
    Lp.coeFn_add (cut s hs f) (cut sᶜ hs.compl f)] with x h₁ h₂ h₃
  by_cases hx : x ∈ s <;> simp_all

/-- Cutting intersects essential support sets. -/
theorem cut_supported_inter {s t : Set X} (hs : MeasurableSet s) {f : L2}
    (hf : Supported t f) : Supported (s ∩ t) (cut s hs f) := by
  filter_upwards [cut_ae s hs f, hf] with x hx ht
  intro hst
  by_cases hxs : x ∈ s
  · have hxt : x ∉ t := fun hxt => hst ⟨hxs, hxt⟩
    simpa [hxs, ht hxt] using hx
  · simpa [hxs] using hx

/-- Cutting to a disjoint set gives zero. -/
theorem cut_zero_of_disjoint {s t : Set X} (hs : MeasurableSet s)
    (hst : Disjoint s t) {f : L2} (hf : Supported t f) : cut s hs f = 0 := by
  apply Lp.ext
  filter_upwards [cut_ae s hs f, hf, Lp.coeFn_zero E 2 (volume : Measure X)]
    with x hx ht hz
  rw [hz, hx]
  by_cases hxs : x ∈ s
  · have hxt : x ∉ t := fun hxt => Set.disjoint_left.mp hst hxs hxt
    simp [hxs, ht hxt]
  · simp [hxs]

/-- Only the zero field is supported in the empty set. -/
theorem supported_empty_iff (f : L2) : Supported ∅ f ↔ f = 0 := by
  constructor
  · intro hf
    apply Lp.ext
    filter_upwards [hf, Lp.coeFn_zero E 2 (volume : Measure X)] with x hx hz
    simpa using (hx (by simp)).trans hz.symm
  · rintro rfl
    exact supported_zero _

end NoContact
