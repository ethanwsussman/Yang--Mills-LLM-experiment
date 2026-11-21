import YangMills.Construction.ParameterData.TheShapesAreAPair
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPair
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.TotalDensitiesGiveASystem.TheShapesAreATuple
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
private theorem tentProfile_nonneg (r : ℝ) : 0 ≤ TrajectoryData.tentProfile r := le_max_right _ _
private theorem tentProfile_le_one (r : ℝ) : TrajectoryData.tentProfile r ≤ 1 := max_le (min_le_left _ _) zero_le_one
private theorem tentProfile_zero : TrajectoryData.tentProfile 0 = 1 := by
  unfold TrajectoryData.tentProfile
  norm_num
private theorem uniformNorm_eq_one_of_attains {X : Type*} {F : X → ℝ} (hnonneg : ∀ p, 0 ≤ F p)
    (hle : ∀ p, F p ≤ 1) (q : X) (hq : F q = 1) :
    TestFunctions.uniformNorm F = 1 := by
  have : Nonempty X := ⟨q⟩
  have hb : BddAbove (Set.range fun x => ‖F x‖) := ⟨1, by
    rintro _ ⟨x, rfl⟩
    simpa [Real.norm_of_nonneg (hnonneg x)] using hle x⟩
  refine le_antisymm (ciSup_le fun x => ?_) ?_
  · rw [Real.norm_of_nonneg (hnonneg x)]
    exact hle x
  · have h := le_ciSup hb q
    have e : ‖F q‖ = 1 := by rw [hq]; simp
    rw [e] at h
    exact h
private theorem uniformNorm_firstBump (L m : ℕ) (n : ℝ) :
    TestFunctions.uniformNorm (TrajectoryData.firstBump L m n 0) = 1 := by
  refine uniformNorm_eq_one_of_attains (fun p => tentProfile_nonneg _) (fun p => tentProfile_le_one _)
    (TrajectoryData.torusPointOf L m fun i => (((0 : Fin 4 → ℤ) i : ℤ) : ℝ)) ?_
  show TrajectoryData.tentProfile (TestFunctions.euclidDistTorus _ _ / (0.99 * n)) = 1
  have : TestFunctions.euclidDistTorus (TrajectoryData.torusPointOf L m fun i => (((0 : Fin 4 → ℤ) i : ℤ) : ℝ))
      (TrajectoryData.torusPointOf L m fun i => (((0 : Fin 4 → ℤ) i : ℤ) : ℝ)) = 0 :=
    AmbientPoints.torusEuclidNorm_sub_self _
  rw [this, zero_div, tentProfile_zero]
private theorem uniformNorm_translatedBump (L m : ℕ) (n : ℝ) :
    TestFunctions.uniformNorm (TrajectoryData.translatedBump L m n 0) = 1 := by
  refine uniformNorm_eq_one_of_attains (fun p => tentProfile_nonneg _) (fun p => tentProfile_le_one _)
    ((TrajectoryData.torusPointOf L m fun i => (((0 : Fin 4 → ℤ) i : ℤ) : ℝ)) +
      TrajectoryData.torusPointOf L m (Pi.single 0 (3.5 * n))) ?_
  show TrajectoryData.firstBump L m n 0 _ = 1
  rw [add_sub_cancel_right]
  show TrajectoryData.tentProfile (TestFunctions.euclidDistTorus _ _ / (0.99 * n)) = 1
  have : TestFunctions.euclidDistTorus (TrajectoryData.torusPointOf L m fun i => (((0 : Fin 4 → ℤ) i : ℤ) : ℝ))
      (TrajectoryData.torusPointOf L m fun i => (((0 : Fin 4 → ℤ) i : ℤ) : ℝ)) = 0 :=
    AmbientPoints.torusEuclidNorm_sub_self _
  rw [this, zero_div, tentProfile_zero]
theorem bumpPairIsSeparatedTuple_of_geometry (hpair : TrajectoryData.bumpsFormSeparatedPairStatement)
    (hgeom : TestPairs.GeometryAndKernelBounds) :
    BumpPairIsSeparatedTuple := by
  intro ℓ m n hL hm hn hside
  set f := TrajectoryData.firstBump ℓ.side m n 0 with hf
  set h := TrajectoryData.translatedBump ℓ.side m n 0 with hh
  have hcl : (f, h) ∈ TestFunctions.separatedPairsFourTorus ℓ.side m n (1 / 4) := hpair ℓ.side m n 0 hL hn hside
  obtain ⟨x₁, x₂, b₁, b₂, e₁, e₂⟩ := id hcl
  obtain ⟨l₁, -, -, s₁, i₁, c₁⟩ := b₁
  obtain ⟨l₂, -, -, s₂, i₂, c₂⟩ := b₂
  have hsf : TestFunctions.uniformNorm f = 1 := uniformNorm_firstBump ℓ.side m n
  have hsh : TestFunctions.uniformNorm h = 1 := uniformNorm_translatedBump ℓ.side m n
  have hcent : TestFunctions.IsCentrePairTorus (PeriodicLattice.torusSide ℓ.side m) n (1 / 4) x₁ x₂ (f, h) :=
    ⟨⟨s₁, i₁, c₁⟩, ⟨s₂, i₂, c₂⟩, e₁, e₂⟩
  have hmem : PeriodicLattice.torusSide ℓ.side m ∈ PeriodicLattice.torusSides ℓ.side := ⟨m, by omega, rfl⟩
  obtain ⟨hb, -⟩ := hgeom.2 ℓ.side (PeriodicLattice.torusSide ℓ.side m) n (1 / 4) ⟨hn, by norm_num, by norm_num⟩
    ⟨hmem, hside⟩ x₁ x₂ f h hcl hcent
  obtain ⟨-, -, happ, -, hc₁, hc₂, -⟩ := hb
  have hdist : ∀ {x₀ u v : TorusMetric.Torus4 (PeriodicLattice.torusSide ℓ.side m)},
      u ∈ TestFunctions.closedBallTorus x₀ n → v ∈ TestFunctions.closedBallTorus x₀ n →
      TestFunctions.euclidDistTorus u v ≤ 10 * n := fun {x₀ u v} hu hv => by
    have ht := AmbientPoints.torusEuclidNorm_sub_le u x₀ v
    have hv' : TorusMetric.torusEuclidNorm (x₀ - v) ≤ n := by
      rw [AmbientPoints.torusEuclidNorm_sub_comm]; exact hv
    have hu' : TorusMetric.torusEuclidNorm (u - x₀) ≤ n := hu
    show TorusMetric.torusEuclidNorm (u - v) ≤ 10 * n
    linarith
  have h01 : ENNReal.ofReal n ≤ TorusMetric.setEuclidDist (tsupport f) (tsupport h) :=
    le_iInf₂ fun a ha => le_iInf₂ fun b hb' => ENNReal.ofReal_le_ofReal (happ a ha b hb').1
  have h10 : ENNReal.ofReal n ≤ TorusMetric.setEuclidDist (tsupport h) (tsupport f) :=
    le_iInf₂ fun a ha => le_iInf₂ fun b hb' => ENNReal.ofReal_le_ofReal (by
      have := (happ b hb' a ha).1
      rw [AmbientPoints.torusEuclidNorm_sub_comm]
      exact this)
  have hs₁ : TestFunctions.lipConstTorus f ≤ 1 / (1 / 4 * n) := by
    have := c₁
    rw [show TestFunctions.uniformNorm (f, h).1 = 1 from hsf] at this
    exact this
  have hs₂ : TestFunctions.lipConstTorus h ≤ 1 / (1 / 4 * n) := by
    have := c₂
    rw [show TestFunctions.uniformNorm (f, h).2 = 1 from hsh] at this
    exact this
  refine ⟨⟨?_, ?_, ?_, ⟨hn, ?_⟩, ?_⟩, ⟨hcl, hsf, hsh⟩, ?_⟩
  · intro i
    fin_cases i
    · exact hsf
    · exact hsh
  · intro i
    fin_cases i
    · exact l₁
    · exact l₂
  · intro i
    fin_cases i
    · exact hs₁
    · exact hs₂
  · intro i k hik
    fin_cases i <;> fin_cases k
    · exact absurd rfl hik
    · exact h01
    · exact h10
    · exact absurd rfl hik
  · intro i k u hu v hv
    fin_cases i <;> fin_cases k
    · exact hdist (s₁ hu) (s₁ hv)
    · exact (happ u hu v hv).2
    · have := (happ v hv u hu).2
      show TorusMetric.torusEuclidNorm (u - v) ≤ 10 * n
      rw [AmbientPoints.torusEuclidNorm_sub_comm]
      exact this
    · exact hdist (s₂ hu) (s₂ hv)
  · have h1 := hc₁.trans hc₂
    rw [show TestFunctions.uniformNorm f = 1 from hsf, show TestFunctions.uniformNorm h = 1 from hsh] at h1
    simpa [TestPairs.kernelLowerConst] using h1
end YangMills.Construction.TotalDensitiesGiveASystem
end
