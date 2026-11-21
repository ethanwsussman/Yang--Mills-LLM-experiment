import YangMills.Construction.ComplexAnalysis.PartialDerivativesAndLogarithm
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TorusBoundNotation
section Objects
variable {n : ℕ}
def coordDeriv (i : Fin n) (F : Coordinates.ComplexCoordinates n → ℂ) :
    Coordinates.ComplexCoordinates n → ℂ :=
  fun z => deriv (fun ζ : ℂ => F (z + ζ • Coordinates.ComplexCoordinates.stdBasisVector i)) 0
theorem eventually_differentiableAt_line {O : Set (Coordinates.ComplexCoordinates n)}
    {F : Coordinates.ComplexCoordinates n → ℂ} (hF : ComplexVariables.IsHolomorphicScalar O F)
    {z : Coordinates.ComplexCoordinates n} (hz : z ∈ O) (i : Fin n) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ),
      DifferentiableAt ℂ
        (fun ζ : ℂ => F (z + ζ • Coordinates.ComplexCoordinates.stdBasisVector i)) ζ := by
  obtain ⟨-, -, h⟩ := hF
  filter_upwards [h z hz i] with ζ hζ
  simpa using differentiableAt_pi.mp hζ 0
theorem partialDeriv_eq_coordDeriv {O : Set (Coordinates.ComplexCoordinates n)}
    {F : Coordinates.ComplexCoordinates n → ℂ} (hF : ComplexVariables.IsHolomorphicScalar O F)
    {z : Coordinates.ComplexCoordinates n} (hz : z ∈ O) (i : Fin n) :
    ComplexVariables.partialDeriv i F z = coordDeriv i F z := by
  have hd := (eventually_differentiableAt_line hF hz i).self_of_nhds
  have ht := hasDerivAt_iff_tendsto_slope_zero.mp hd.hasDerivAt
  refine Tendsto.limUnder_eq ?_
  change Tendsto (fun ζ : ℂ =>
    ζ⁻¹ * (F (z + ζ • Coordinates.ComplexCoordinates.stdBasisVector i) - F z)) _ _
  simpa [coordDeriv] using ht
theorem isHolomorphicScalar_fin_one_iff {O : Set (Coordinates.ComplexCoordinates 1)}
    (hO : IsOpen O) (F : Coordinates.ComplexCoordinates 1 → ℂ) :
    ComplexVariables.IsHolomorphicScalar O F ↔
      ∀ a ∈ O, DifferentiableAt ℂ (fun w : ℂ => F fun _ => w) (a 0) := by
  have hF : ∀ z : Coordinates.ComplexCoordinates 1, F z = (fun w : ℂ => F fun _ => w) (z 0) :=
    fun z => by
      refine congrArg F (funext fun i => ?_)
      rw [Subsingleton.elim i 0]
  have hstep : ∀ (a : Coordinates.ComplexCoordinates 1) (j : Fin 1) (ζ : ℂ),
      (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) 0 = a 0 + ζ := fun a j ζ => by
    rw [Subsingleton.elim j 0]
    simp [Coordinates.ComplexCoordinates.stdBasisVector]
  constructor
  · intro h a ha
    have hd := (eventually_differentiableAt_line h ha 0).self_of_nhds
    have he : (fun ζ : ℂ => F (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector 0)) =
        fun ζ : ℂ => (fun w : ℂ => F fun _ => w) (a 0 + ζ) := by
      funext ζ
      rw [hF, hstep]
    rw [he] at hd
    simpa using (differentiableAt_comp_add_left (𝕜 := ℂ) (f := fun w : ℂ => F fun _ => w)
      (x := (0 : ℂ)) (a 0)).mp hd
  · intro h
    refine ⟨hO, fun a ha => ?_, fun a ha j => ?_⟩
    · refine ContinuousAt.continuousWithinAt ?_
      refine continuousAt_pi.mpr fun i => ?_
      have hc : ContinuousAt
          (fun z : Coordinates.ComplexCoordinates 1 => (fun w : ℂ => F fun _ => w) (z 0)) a :=
        ContinuousAt.comp (f := fun z : Coordinates.ComplexCoordinates 1 => z 0)
          (h a ha).continuousAt (continuous_apply 0).continuousAt
      have he : (fun z => ((Equiv.funUnique (Fin 1) ℂ).symm ∘ F) z i) =
          fun z : Coordinates.ComplexCoordinates 1 => (fun w : ℂ => F fun _ => w) (z 0) := by
        funext z
        rw [← hF]
        simp
      rw [he]
      exact hc
    · have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ),
          a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j ∈ O := by
        have hcont : Continuous fun ζ : ℂ =>
            a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j := by
          fun_prop
        exact hcont.continuousAt.eventually_mem (by simpa using hO.mem_nhds ha)
      filter_upwards [hnear] with ζ hζ
      refine differentiableAt_pi.mpr fun i => ?_
      have he : (fun ζ : ℂ => ((Equiv.funUnique (Fin 1) ℂ).symm ∘ F)
            (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) i) =
          fun ζ : ℂ => (fun w : ℂ => F fun _ => w) (a 0 + ζ) := by
        funext ζ
        rw [← hstep a j ζ, ← hF]
        simp
      rw [he]
      refine (differentiableAt_comp_add_left (𝕜 := ℂ) (f := fun w : ℂ => F fun _ => w)
        (a 0)).mpr ?_
      have := h _ hζ
      rwa [hstep] at this
def FormedSuccessively (O : Set (Coordinates.ComplexCoordinates n))
    (F : Coordinates.ComplexCoordinates n → ℂ) : List (Fin n) → Prop
  | [] => True
  | _ :: l =>
    FormedSuccessively O F l ∧ ComplexVariables.IsHolomorphicScalar O (l.foldr coordDeriv F)
def MixedDerivFormed (O : Set (Coordinates.ComplexCoordinates n))
    (F : Coordinates.ComplexCoordinates n → ℂ) : Prop :=
  FormedSuccessively O F (List.finRange n)
def mixedDeriv (F : Coordinates.ComplexCoordinates n → ℂ) : Coordinates.ComplexCoordinates n → ℂ :=
  (List.finRange n).foldr coordDeriv F
end Objects
def discAtOne : Set ℂ := {u | ‖u - 1‖ < 1}
def principalLog (u : ℂ) : ℂ :=
  ∑' k : ℕ+, (-1 : ℂ) ^ ((k : ℕ) - 1) / ((k : ℕ) : ℂ) * (u - 1) ^ (k : ℕ)
end YangMills.Construction.TorusBoundNotation
end
