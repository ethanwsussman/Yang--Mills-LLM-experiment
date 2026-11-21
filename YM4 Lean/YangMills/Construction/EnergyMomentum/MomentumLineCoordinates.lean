import YangMills.Construction.EnergyMomentum.ContractionSemigroupUnitaryGroup
import YangMills.Construction.SpectralTheory.EuclideanBorelProjectionValuedMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction
namespace EuclideanSpectral.SpectralMeasure
variable {X K : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
open Classical in
def dirac (hX : IsEuclideanBorel X) (x₀ : X) : SpectralMeasure X K where
  borelSubset := hX
  toFun A := if x₀ ∈ A.1 then 1 else 0
  selfAdjoint A := by
    intro u v
    split_ifs <;> simp
  map_univ := by simp
  map_inter A B := by
    by_cases hA : x₀ ∈ A.1 <;> by_cases hB : x₀ ∈ B.1 <;> simp [hA, hB]
  countablyAdditive v A hdisj := by
    by_cases hex : ∃ n, x₀ ∈ (A n).1
    · obtain ⟨n, hn⟩ := hex
      have hmem : x₀ ∈ ⋃ n, (A n).1 := mem_iUnion.2 ⟨n, hn⟩
      have hout : ∀ m, m ≠ n → x₀ ∉ (A m).1 :=
        fun m hm hxm => Set.disjoint_left.1 (hdisj hm) hxm hn
      have heq : ⟪v, (if x₀ ∈ ⋃ n, (A n).1 then (1 : K →L[ℂ] K) else 0) v⟫_ℂ =
          ⟪v, (if x₀ ∈ (A n).1 then (1 : K →L[ℂ] K) else 0) v⟫_ℂ := by
        rw [if_pos hmem, if_pos hn]
      simp only [heq]
      refine hasSum_single n fun m hm => ?_
      simp [hout m hm]
    · have hmem : x₀ ∉ ⋃ n, (A n).1 := fun hxm => hex (mem_iUnion.1 hxm)
      have hout : ∀ m, x₀ ∉ (A m).1 := fun m hxm => hex ⟨m, hxm⟩
      simp only [if_neg hmem, hout, if_false]
      simp
theorem nonempty_of_isEuclideanBorel (hX : IsEuclideanBorel X) [Nonempty X] :
    Nonempty (SpectralMeasure X K) :=
  ⟨dirac hX (Classical.arbitrary X)⟩
end EuclideanSpectral.SpectralMeasure
namespace EnergyMomentum
open EuclideanSpectral
abbrev EnergyMomentumLine : Type := ℝ≥0 × ℝ
def projMomentum (i : Fin 3) (p : EnergyMomentumSpace) : EnergyMomentumLine := (p.1, p.2 i)
theorem measurable_projMomentum (i : Fin 3) : Measurable (projMomentum i) :=
  (continuous_fst.prodMk ((EuclideanSpace.proj i).continuous.comp continuous_snd)).measurable
def laplaceFourierExpLine (t : ℝ≥0) (s : ℝ) (p : EnergyMomentumLine) : ℂ :=
  Complex.exp (((-(t : ℝ) * (p.1 : ℝ) : ℝ) : ℂ) + Complex.I * ((s * p.2 : ℝ) : ℂ))
def coordEnergy (p : EnergyMomentumSpace) : ℂ := ((p.1 : ℝ) : ℂ)
def coordMomentum (i : Fin 3) (p : EnergyMomentumSpace) : ℂ := ((p.2 i : ℝ) : ℂ)
def lineEnergyCoord (p : EnergyMomentumLine) : ℂ := ((p.1 : ℝ) : ℂ)
def lineMomentumCoord (p : EnergyMomentumLine) : ℂ := ((p.2 : ℝ) : ℂ)
theorem isEuclideanBorel_energyMomentumSpace : IsEuclideanBorel EnergyMomentumSpace := by
  let e : EnergyMomentumSpace → EuclideanSpace ℝ (Fin 4) := fun p => !₂[(p.1 : ℝ), p.2 0, p.2 1, p.2 2]
  let r : EuclideanSpace ℝ (Fin 4) → EnergyMomentumSpace := fun x => (Real.toNNReal (x 0), !₂[x 1, x 2, x 3])
  have he : Continuous e := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    fin_cases j <;> simp <;> fun_prop
  have hr : Continuous r := by
    refine (continuous_real_toNNReal.comp (by fun_prop)).prodMk
      ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_))
    fin_cases j <;> simp <;> fun_prop
  have hinv : Function.LeftInverse r e := by
    rintro ⟨E, q⟩
    refine Prod.ext (by simp [r, e]) ?_
    ext j
    fin_cases j <;> simp [r, e]
  have hrange : range e = {x | 0 ≤ x 0} := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      simp [e]
    · intro hx
      refine ⟨r x, ?_⟩
      ext j
      fin_cases j
      · simpa [r, e] using hx
      all_goals simp [r, e]
  refine ⟨4, e, hinv.isEmbedding hr he, ?_⟩
  rw [hrange]
  exact (isClosed_le continuous_const (by fun_prop)).measurableSet
theorem isEuclideanBorel_energyMomentumLine : IsEuclideanBorel EnergyMomentumLine := by
  let e : EnergyMomentumLine → EuclideanSpace ℝ (Fin 2) := fun p => !₂[(p.1 : ℝ), p.2]
  let r : EuclideanSpace ℝ (Fin 2) → EnergyMomentumLine := fun x => (Real.toNNReal (x 0), x 1)
  have he : Continuous e := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    fin_cases j <;> simp <;> fun_prop
  have hr : Continuous r :=
    (continuous_real_toNNReal.comp (by fun_prop)).prodMk (by fun_prop)
  have hinv : Function.LeftInverse r e := by
    rintro ⟨E, q⟩
    exact Prod.ext (by simp [r, e]) (by simp [r, e])
  have hrange : range e = {x | 0 ≤ x 0} := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      simp [e]
    · intro hx
      refine ⟨r x, ?_⟩
      ext j
      fin_cases j
      · simpa [r, e] using hx
      all_goals simp [r, e]
  refine ⟨2, e, hinv.isEmbedding hr he, ?_⟩
  rw [hrange]
  exact (isClosed_le continuous_const (by fun_prop)).measurableSet
end EnergyMomentum
end YangMills.Construction
