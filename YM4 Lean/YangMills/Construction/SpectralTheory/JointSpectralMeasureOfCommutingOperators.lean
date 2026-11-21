import YangMills.Construction.SpectralTheory.BorelProjectionValuedMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace JointSpectral
open BorelSpectral
variable {n : ℕ} {Y : Set (Fin n → ℝ)} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
def closedBox (a b : Fin n → ℝ) : Set (Fin n → ℝ) := pi univ fun i => Icc (a i) (b i)
theorem measurableSet_closedBox (a b : Fin n → ℝ) : MeasurableSet (closedBox a b) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc
structure IsCommutingInBox (T : Fin n → H →L[ℂ] H) (a b : Fin n → ℝ) : Prop where
  selfAdjoint : ∀ i, IsSelfAdjoint (T i)
  commute : ∀ i j, Commute (T i) (T j)
  lt : ∀ i, a i < b i
  lower_le : ∀ i, ((a i : ℝ) : ℂ) • (1 : H →L[ℂ] H) ≤ T i
  le_upper : ∀ i, T i ≤ ((b i : ℝ) : ℂ) • (1 : H →L[ℂ] H)
def coordFn (i : Fin n) (y : Y) : ℂ := ((y.1 i : ℝ) : ℂ)
def IsJointRepresentation (F : SpectralMeasure Y H) (T : Fin n → H →L[ℂ] H) : Prop :=
  ∀ i, T i = F.integralOp (coordFn i)
open scoped Classical in
def dirac (hn : 1 ≤ n) (hY : MeasurableSet Y) (y₀ : Y) : SpectralMeasure Y H where
  one_le_dimension := hn
  measurableSet_carrier := hY
  toFun S := if y₀ ∈ S.1 then 1 else 0
  isStarProjection S := by
    split_ifs
    · exact IsStarProjection.one _
    · exact IsStarProjection.zero _
  map_univ := by simp
  map_inter S S' := by
    by_cases h : y₀ ∈ S.1 <;> by_cases h' : y₀ ∈ S'.1 <;> simp [h, h']
  countablyAdditive v S hd := by
    by_cases h : ∃ k, y₀ ∈ (S k).1
    · obtain ⟨k, hk⟩ := h
      have hu : y₀ ∈ ⋃ k, (S k).1 := mem_iUnion.mpr ⟨k, hk⟩
      have hs := hasSum_single (f := fun l => inner ℂ v
        ((if y₀ ∈ (S l).1 then (1 : H →L[ℂ] H) else 0) v)) k (fun l hl => by
          have : y₀ ∉ (S l).1 := fun hl' =>
            (Set.disjoint_left.mp (hd hl) hl' hk)
          simp [this])
      simpa [hk, hu] using hs
    · have hu : y₀ ∉ ⋃ k, (S k).1 := fun hu => h (mem_iUnion.mp hu)
      have h' : ∀ k, y₀ ∉ (S k).1 := fun k hk => h ⟨k, hk⟩
      simp [h', hu, hasSum_zero]
def jointMeasure (hn : 1 ≤ n) (T : Fin n → H →L[ℂ] H) (a b : Fin n → ℝ)
    (hab : ∀ i, a i < b i) : SpectralMeasure (closedBox a b) H :=
  haveI : Nonempty (SpectralMeasure (closedBox a b) H) :=
    ⟨dirac hn (measurableSet_closedBox a b) ⟨a, fun i _ => ⟨le_rfl, (hab i).le⟩⟩⟩
  Classical.epsilon fun F => IsJointRepresentation F T
def JointSpectralTheorem : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ)
    (hn : 1 ≤ n),
    (∀ (T : Fin n → H →L[ℂ] H) (a b : Fin n → ℝ) (h : IsCommutingInBox T a b),
      (∃! F : SpectralMeasure (closedBox a b) H, IsJointRepresentation F T) ∧
      IsJointRepresentation (jointMeasure hn T a b h.lt) T ∧
      (∀ (a₂ b₂ : Fin n → ℝ), IsCommutingInBox T a₂ b₂ →
        ∀ (F : SpectralMeasure (closedBox a b) H)
          (F₂ : SpectralMeasure (closedBox a₂ b₂) H),
          IsJointRepresentation F T → IsJointRepresentation F₂ T →
            F.extendCarrier (subset_univ _) MeasurableSet.univ =
              F₂.extendCarrier (subset_univ _) MeasurableSet.univ) ∧
      (∀ F : SpectralMeasure (closedBox a b) H, IsJointRepresentation F T →
        ∀ B : H →L[ℂ] H, (∀ i, Commute B (T i)) → ∀ S, Commute B (F S))) ∧
    ∀ (m : ℕ) (Y : Set (Fin m → ℝ)) (E E' : SpectralMeasure Y H)
      (φ : Y → Fin n → ℝ) (ρ : (Fin n → ℝ) → Y),
      Measurable φ → (∃ c : ℝ, ∀ y, ‖φ y‖ ≤ c) → Measurable ρ → (∀ y, ρ (φ y) = y) →
      (∀ i, E.integralOp (fun y => ((φ y i : ℝ) : ℂ)) =
        E'.integralOp fun y => ((φ y i : ℝ) : ℂ)) →
      E = E'
end JointSpectral
end YangMills.Construction
