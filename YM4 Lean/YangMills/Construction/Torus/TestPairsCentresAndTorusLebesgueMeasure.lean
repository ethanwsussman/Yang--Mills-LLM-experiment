import YangMills.Construction.TestFunctions.SeparatedBumpPairs
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace TestFunctions
open TorusMetric PeriodicLattice
def IsSepShapePair (d θ : ℝ) : Prop := 0 < d ∧ θ ∈ Ioc (0 : ℝ) 1
def IsAdmissibleSide (L : ℕ) (ℓ d : ℝ) : Prop := ℓ ∈ torusSides L ∧ 40 * d ≤ ℓ
section CentrePairs
variable {X : Type*} [TopologicalSpace X]
def IsCentrePair (dst : X → X → ℝ) (bl : X → ℝ → Set X) (sdst : Set X → Set X → ℝ≥0∞)
    (intg : (X → ℝ) → ℝ) (d θ : ℝ) (a b : X) (q : (X → ℝ) × (X → ℝ)) : Prop :=
  (tsupport q.1 ⊆ bl a d ∧ θ * uniformNorm q.1 * d ^ 4 ≤ intg q.1 ∧
      bestLipschitzConstant dst q.1 ≤ uniformNorm q.1 / (θ * d)) ∧
    (tsupport q.2 ⊆ bl b d ∧ θ * uniformNorm q.2 * d ^ 4 ≤ intg q.2 ∧
      bestLipschitzConstant dst q.2 ≤ uniformNorm q.2 / (θ * d)) ∧
    ENNReal.ofReal d ≤ sdst (tsupport q.1) (tsupport q.2) ∧
    sdst (tsupport q.1) (tsupport q.2) ≤ ENNReal.ofReal (6 * d)
theorem mem_separatedPairs_iff (dst : X → X → ℝ) (bl : X → ℝ → Set X)
    (sdst : Set X → Set X → ℝ≥0∞) (intg : (X → ℝ) → ℝ) (d θ : ℝ)
    (q : (X → ℝ) × (X → ℝ)) :
    q ∈ separatedPairs dst bl sdst intg d θ ↔
      (IsLipschitzFor dst q.1 ∧ (∀ y, 0 ≤ q.1 y) ∧ ∃ y, q.1 y ≠ 0) ∧
      (IsLipschitzFor dst q.2 ∧ (∀ y, 0 ≤ q.2 y) ∧ ∃ y, q.2 y ≠ 0) ∧
      ∃ a b, IsCentrePair dst bl sdst intg d θ a b q := by
  constructor
  · rintro ⟨a, b, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩, ⟨k₁, k₂, k₃, k₄, k₅, k₆⟩, s₁, s₂⟩
    exact ⟨⟨h₁, h₂, h₃⟩, ⟨k₁, k₂, k₃⟩, a, b, ⟨h₄, h₅, h₆⟩, ⟨k₄, k₅, k₆⟩, s₁, s₂⟩
  · rintro ⟨⟨h₁, h₂, h₃⟩, ⟨k₁, k₂, k₃⟩, a, b, ⟨h₄, h₅, h₆⟩, ⟨k₄, k₅, k₆⟩, s₁, s₂⟩
    exact ⟨a, b, ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩, ⟨k₁, k₂, k₃, k₄, k₅, k₆⟩, s₁, s₂⟩
end CentrePairs
def IsCentrePairR4 (d θ : ℝ) (a b : Fin 4 → ℝ)
    (q : ((Fin 4 → ℝ) → ℝ) × ((Fin 4 → ℝ) → ℝ)) : Prop :=
  IsCentrePair euclidDistR4 closedBallR4 setDistR4 (fun f => ∫ x, f x) d θ a b q
def IsCentrePairTorus (ℓ d θ : ℝ) (a b : Torus4 ℓ)
    (q : (Torus4 ℓ → ℝ) × (Torus4 ℓ → ℝ)) : Prop :=
  IsCentrePair euclidDistTorus closedBallTorus setEuclidDist (torusVolumeIntegral ℓ) d θ a b q
def LiftsToBall {𝕜 : Type*} [Zero 𝕜] (ℓ : ℝ) (c : Fin 4 → ℝ) (r : ℝ)
    (g : Torus4 ℓ → 𝕜) : Prop :=
  0 < r ∧ r ≤ ℓ / 4 ∧ ∀ x, x ∉ torusProj ℓ '' closedBallR4 c r → g x = 0
def centredIcoCube (ℓ : ℝ) (C : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  Set.pi univ fun i => Ico (C i - ℓ / 2) (C i + ℓ / 2)
def cubePushforward (ℓ : ℝ) (C : Fin 4 → ℝ) : Measure (Torus4 ℓ) :=
  (volume.restrict (centredIcoCube ℓ C)).map (torusProj ℓ)
def torusLebesgue (ℓ : ℝ) : Measure (Torus4 ℓ) := cubePushforward ℓ 0
def integralTorusLebesgue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ℓ : ℝ)
    (f : Torus4 ℓ → E) : E :=
  ∫ x, f x ∂torusLebesgue ℓ
theorem measurable_addCircle_coe (ℓ : ℝ) : Measurable ((↑) : ℝ → AddCircle ℓ) := by
  have h : Continuous ((↑) : ℝ → AddCircle ℓ) := continuous_quotient_mk'
  exact h.measurable
theorem measurable_torusProj (ℓ : ℝ) : Measurable (torusProj ℓ) :=
  measurable_pi_lambda _ fun i => (measurable_addCircle_coe ℓ).comp (measurable_pi_apply i)
theorem cubePushforward_eq_pi {ℓ : ℝ} [Fact (0 < ℓ)] (C : Fin 4 → ℝ) :
    cubePushforward ℓ C = Measure.pi fun _ : Fin 4 => (volume : Measure (AddCircle ℓ)) := by
  have hcirc : ∀ i : Fin 4, (volume.restrict (Ico (C i - ℓ / 2) (C i + ℓ / 2))).map
      (QuotientAddGroup.mk : ℝ → AddCircle ℓ) = (volume : Measure (AddCircle ℓ)) := by
    intro i
    have h := (AddCircle.measurePreserving_mk ℓ (C i - ℓ / 2)).map_eq
    have e : C i - ℓ / 2 + ℓ = C i + ℓ / 2 := by ring
    rw [e, ← Measure.restrict_congr_set Ico_ae_eq_Ioc] at h
    exact h
  have hmap := Measure.pi_map_pi
    (μ := fun i : Fin 4 => (volume : Measure ℝ).restrict (Ico (C i - ℓ / 2) (C i + ℓ / 2)))
    (f := fun _ => (QuotientAddGroup.mk : ℝ → AddCircle ℓ))
    (fun _ => (measurable_addCircle_coe ℓ).aemeasurable)
  rw [cubePushforward, centredIcoCube, volume_pi, Measure.restrict_pi_pi]
  simp only [hcirc] at hmap
  exact hmap
theorem cubePushforward_indep {ℓ : ℝ} (hℓ : 0 < ℓ) (C C' : Fin 4 → ℝ) :
    cubePushforward ℓ C = cubePushforward ℓ C' := by
  have : Fact (0 < ℓ) := ⟨hℓ⟩
  rw [cubePushforward_eq_pi, cubePushforward_eq_pi]
theorem bijOn_torusProj_centredIcoCube {ℓ : ℝ} (hℓ : 0 < ℓ) (C : Fin 4 → ℝ) :
    BijOn (torusProj ℓ) (centredIcoCube ℓ C) univ := by
  have : Fact (0 < ℓ) := ⟨hℓ⟩
  have hI : ∀ i : Fin 4, C i + ℓ / 2 = C i - ℓ / 2 + ℓ := fun i => by ring
  refine ⟨fun _ _ => mem_univ _, ?_, ?_⟩
  · intro v hv w hw h
    funext i
    have hvi : v i ∈ Ico (C i - ℓ / 2) (C i + ℓ / 2) := hv i (mem_univ i)
    have hwi : w i ∈ Ico (C i - ℓ / 2) (C i + ℓ / 2) := hw i (mem_univ i)
    rw [hI] at hvi hwi
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hvi hwi).mp (congrFun h i)
  · intro x _
    have hs : ∀ i : Fin 4, ∃ t ∈ Ico (C i - ℓ / 2) (C i + ℓ / 2), (t : AddCircle ℓ) = x i := by
      intro i
      have hx : x i ∈ ((↑) : ℝ → AddCircle ℓ) '' Ico (C i - ℓ / 2) (C i - ℓ / 2 + ℓ) := by
        rw [AddCircle.coe_image_Ico_eq]
        exact mem_univ _
      rw [hI]
      exact hx
    choose v hv hvx using hs
    exact ⟨v, fun i _ => hv i, funext hvx⟩
theorem torusVolumeIntegral_eq_integralTorusLebesgue {ℓ : ℝ} (hℓ : 0 < ℓ) (f : Torus4 ℓ → ℝ)
    (hf : AEStronglyMeasurable f (torusLebesgue ℓ)) :
    torusVolumeIntegral ℓ f = integralTorusLebesgue ℓ f := by
  have hC : torusLebesgue ℓ = cubePushforward ℓ fun _ => ℓ / 2 :=
    cubePushforward_indep hℓ _ _
  have hcube : centredIcoCube ℓ (fun _ => ℓ / 2) = Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) ℓ := by
    simp [centredIcoCube]
  rw [hC] at hf
  rw [integralTorusLebesgue, hC, cubePushforward,
    integral_map (measurable_torusProj ℓ).aemeasurable hf, hcube, torusVolumeIntegral]
end TestFunctions
end YangMills.Construction
