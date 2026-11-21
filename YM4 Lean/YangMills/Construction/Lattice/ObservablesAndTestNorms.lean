import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice
variable {L m : ℕ} {j : ℤ} {E : Type*} [AddCommMonoid E] [Module ℝ E]
def smearedObservable (f : FourTorus L m → E) (U : Bond L m j → ComplexMatrix2) : E :=
  ∑ᶠ p : Plaquette L m j, plaquetteCost U p • f p.barycenter
def observableExpanded (f : FourTorus L m → E) (U : Bond L m j → ComplexMatrix2) : E :=
  ∑ᶠ p : Plaquette L m j,
    (1 - (1 / 2) * (ComplexMatrix2.fullTrace (plaquetteHolonomy U p)).re) • f p.barycenter
end PeriodicLattice
namespace TestFunctions
open TorusMetric PeriodicLattice
section Norms
variable {X E : Type*}
open TorusMetric PeriodicLattice
def IsBoundedFun [Norm E] (f : X → E) : Prop := ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
def uniformNorm [Norm E] (f : X → E) : ℝ := ⨆ x, ‖f x‖
def euclidDistR4 (x y : Fin 4 → ℝ) : ℝ := euclidNormVec (x - y)
def euclidDistTorus {ℓ : ℝ} (x y : Torus4 ℓ) : ℝ := torusEuclidNorm (x - y)
variable [NormedAddCommGroup E]
def IsLipschitzFor (d : X → X → ℝ) (f : X → E) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * d x y
def bestLipschitzConstant (d : X → X → ℝ) (f : X → E) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * d x y}
def lipConstR4 (f : (Fin 4 → ℝ) → E) : ℝ := bestLipschitzConstant euclidDistR4 f
def lipConstTorus {ℓ : ℝ} (f : Torus4 ℓ → E) : ℝ := bestLipschitzConstant euclidDistTorus f
def sharpNormR4 (M : ℝ) (f : (Fin 4 → ℝ) → E) : ℝ := max (uniformNorm f) (40 * M * lipConstR4 f)
def sharpNormTorus {ℓ : ℝ} (M : ℝ) (f : Torus4 ℓ → E) : ℝ :=
  max (uniformNorm f) (40 * M * lipConstTorus f)
variable [NormedSpace ℝ E]
def IsC1R4 (f : (Fin 4 → ℝ) → E) : Prop := ContDiff ℝ 1 f
def IsC1Torus {ℓ : ℝ} (f : Torus4 ℓ → E) : Prop := ContDiff ℝ 1 (f ∘ torusProj ℓ)
def partialDerivR4 (μ : Fin 4) (f : (Fin 4 → ℝ) → E) (x : Fin 4 → ℝ) : E :=
  deriv (fun t : ℝ => f (x + t • Pi.single μ (1 : ℝ))) 0
def partialDerivTorus {ℓ : ℝ} (μ : Fin 4) (f : Torus4 ℓ → E) (x : Torus4 ℓ) : E :=
  deriv (fun t : ℝ => f (x + torusProj ℓ (t • Pi.single μ (1 : ℝ)))) 0
def c1NormR4 (f : (Fin 4 → ℝ) → E) : ℝ :=
  max (uniformNorm f) (⨆ μ : Fin 4, uniformNorm (partialDerivR4 μ f))
def c1NormTorus {ℓ : ℝ} (f : Torus4 ℓ → E) : ℝ :=
  max (uniformNorm f) (⨆ μ : Fin 4, uniformNorm (partialDerivTorus μ f))
end Norms
def closedBallTorus {ℓ : ℝ} (x : Torus4 ℓ) (r : ℝ) : Set (Torus4 ℓ) :=
  {y | torusEuclidNorm (y - x) ≤ r}
def closedBallR4 (x : Fin 4 → ℝ) (r : ℝ) : Set (Fin 4 → ℝ) := {y | euclidNormVec (y - x) ≤ r}
def setDistR4 (A B : Set (Fin 4 → ℝ)) : ℝ≥0∞ :=
  ⨅ a ∈ A, ⨅ b ∈ B, ENNReal.ofReal (euclidNormVec (a - b))
section Separation
variable {E : Type*} [Zero E] {n : ℕ}
def HasSeparatedSupportsTorus {ℓ : ℝ} (f : Fin n → Torus4 ℓ → E) (d : ℝ) : Prop :=
  0 < d ∧ ∀ i k, i ≠ k → ENNReal.ofReal d ≤ setEuclidDist (tsupport (f i)) (tsupport (f k))
def HasSeparatedSupportsR4 (f : Fin n → (Fin 4 → ℝ) → E) (d : ℝ) : Prop :=
  0 < d ∧ ∀ i k, i ≠ k → ENNReal.ofReal d ≤ setDistR4 (tsupport (f i)) (tsupport (f k))
end Separation
def injectiveTuples (Y : Type*) (n : ℕ) : Set (Fin n → Y) := {y | Function.Injective y}
theorem torusProj_surjective (ℓ : ℝ) : Function.Surjective (torusProj ℓ) := by
  intro x
  choose v hv using fun μ => QuotientAddGroup.mk_surjective (x μ)
  exact ⟨v, funext hv⟩
def liftPoint {ℓ : ℝ} (x : Torus4 ℓ) : Fin 4 → ℝ :=
  Function.surjInv (torusProj_surjective ℓ) x
theorem torusProj_liftPoint {ℓ : ℝ} (x : Torus4 ℓ) : torusProj ℓ (liftPoint x) = x :=
  Function.surjInv_eq _ x
def latticeTranslate (ℓ : ℝ) (k : Fin 4 → ℤ) : Fin 4 → ℝ := fun μ => ℓ * (k μ : ℝ)
theorem latticeTranslate_add (ℓ : ℝ) (k k' : Fin 4 → ℤ) :
    latticeTranslate ℓ (k + k') = latticeTranslate ℓ k + latticeTranslate ℓ k' := by
  funext μ
  simp [latticeTranslate, mul_add]
theorem torusProj_add_latticeTranslate (ℓ : ℝ) (v : Fin 4 → ℝ) (k : Fin 4 → ℤ) :
    torusProj ℓ (v + latticeTranslate ℓ k) = torusProj ℓ v := by
  funext μ
  have hz : ((ℓ * (k μ : ℝ) : ℝ) : AddCircle ℓ) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k μ, by simp [mul_comm]⟩
  simp [torusProj, latticeTranslate, hz]
theorem exists_latticeTranslate_of_torusProj_eq {ℓ : ℝ} {v w : Fin 4 → ℝ}
    (h : torusProj ℓ v = torusProj ℓ w) : ∃ k, v = w + latticeTranslate ℓ k := by
  have hμ : ∀ μ, ∃ k : ℤ, v μ = w μ + ℓ * (k : ℝ) := by
    intro μ
    have hc : (v μ : AddCircle ℓ) = (w μ : AddCircle ℓ) := congrFun h μ
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq_iff_sub_mem.mp hc)
    refine ⟨k, ?_⟩
    have hk' : (k : ℝ) * ℓ = v μ - w μ := by simpa using hk
    linarith
  choose k hk using hμ
  exact ⟨k, funext hk⟩
def HasDiameterLE (A : Set (Fin 4 → ℝ)) (D : ℝ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, euclidNormVec (x - y) ≤ D
section Periodization
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
def periodicSum (ℓ : ℝ) (f : (Fin 4 → ℝ) → E) (v : Fin 4 → ℝ) : E :=
  ∑' k : Fin 4 → ℤ, f (v + latticeTranslate ℓ k)
theorem periodicSum_add_latticeTranslate (ℓ : ℝ) (f : (Fin 4 → ℝ) → E) (v : Fin 4 → ℝ)
    (k : Fin 4 → ℤ) : periodicSum ℓ f (v + latticeTranslate ℓ k) = periodicSum ℓ f v := by
  unfold periodicSum
  rw [← (Equiv.addRight k).tsum_eq (fun c => f (v + latticeTranslate ℓ c))]
  refine tsum_congr fun c => ?_
  simp only [Equiv.coe_addRight, latticeTranslate_add]
  congr 1
  abel
def periodize (ℓ : ℝ) (f : (Fin 4 → ℝ) → E) : Torus4 ℓ → E :=
  fun x => periodicSum ℓ f (liftPoint x)
theorem periodize_torusProj (ℓ : ℝ) (f : (Fin 4 → ℝ) → E) (v : Fin 4 → ℝ) :
    periodize ℓ f (torusProj ℓ v) = periodicSum ℓ f v := by
  obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq (torusProj_liftPoint (torusProj ℓ v))
  rw [periodize, hk, periodicSum_add_latticeTranslate]
end Periodization
def IsPeriodizable {E : Type*} [Zero E] (ℓ : ℝ) (A : Set (Fin 4 → ℝ))
    (f : (Fin 4 → ℝ) → E) : Prop :=
  HasDiameterLE A (ℓ / 2) ∧ Function.support f ⊆ A
section Kernel
variable {𝕜 : Type*} [RCLike 𝕜]
def IsKernelPairR4 (f h : (Fin 4 → ℝ) → 𝕜) : Prop :=
  IsBoundedFun f ∧ IsBoundedFun h ∧ Measurable f ∧ Measurable h ∧ HasCompactSupport f ∧
    HasCompactSupport h ∧ 0 < setDistR4 (tsupport f) (tsupport h)
def inverseEighthKernel (f h : (Fin 4 → ℝ) → 𝕜) : 𝕜 :=
  ∫ z : (Fin 4 → ℝ) × (Fin 4 → ℝ),
    f z.1 * h z.2 * ((euclidNormVec (z.1 - z.2) ^ (-8 : ℤ) : ℝ) : 𝕜)
def liftToBall (ℓ : ℝ) (c : Fin 4 → ℝ) (r : ℝ) (f : Torus4 ℓ → 𝕜) : (Fin 4 → ℝ) → 𝕜 :=
  (closedBallR4 c r).indicator (f ∘ torusProj ℓ)
def IsKernelBallTorus {ℓ : ℝ} (f h : Torus4 ℓ → 𝕜) (c : Fin 4 → ℝ) (r : ℝ) : Prop :=
  0 < setEuclidDist (tsupport f) (tsupport h) ∧ 0 < r ∧ r ≤ ℓ / 4 ∧
    tsupport f ⊆ closedBallTorus (torusProj ℓ c) r ∧ tsupport h ⊆ closedBallTorus (torusProj ℓ c) r
def inverseEighthKernelTorus {ℓ : ℝ} (f h : Torus4 ℓ → 𝕜) : 𝕜 :=
  open Classical in
  if H : ∃ q : (Fin 4 → ℝ) × ℝ, IsKernelBallTorus f h q.1 q.2 then
    inverseEighthKernel (liftToBall ℓ H.choose.1 H.choose.2 f) (liftToBall ℓ H.choose.1 H.choose.2 h)
  else 0
end Kernel
def contractTorus (L m b : ℕ) (x : FourTorus L (m + b)) : FourTorus L m :=
  torusProj (torusSide L m) (meshSize L (b : ℤ) • liftPoint x)
theorem contractTorus_torusProj {L : ℕ} (hL : 0 < L) (m b : ℕ) (v : Fin 4 → ℝ) :
    contractTorus L m b (torusProj (torusSide L (m + b)) v) =
      torusProj (torusSide L m) (meshSize L (b : ℤ) • v) := by
  obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq
    (torusProj_liftPoint (torusProj (torusSide L (m + b)) v))
  have hs : meshSize L (b : ℤ) * torusSide L (m + b) = torusSide L m := by
    simp only [meshSize, torusSide, zpow_neg, zpow_natCast, pow_add]
    field_simp
  have hv : meshSize L (b : ℤ) • (v + latticeTranslate (torusSide L (m + b)) k) =
      meshSize L (b : ℤ) • v + latticeTranslate (torusSide L m) k := by
    funext μ
    simp only [Pi.smul_apply, Pi.add_apply, latticeTranslate, smul_eq_mul, ← hs]
    ring
  rw [contractTorus, hk, hv, torusProj_add_latticeTranslate]
variable {E : Type*}
def dilateR4 (L b : ℕ) (f : (Fin 4 → ℝ) → E) : (Fin 4 → ℝ) → E :=
  fun x => f (meshSize L (b : ℤ) • x)
def dilateTorus (L m b : ℕ) (f : FourTorus L m → E) : FourTorus L (m + b) → E :=
  fun x => f (contractTorus L m b x)
end TestFunctions
end YangMills.Construction
