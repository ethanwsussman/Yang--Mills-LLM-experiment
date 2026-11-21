import YangMills.Construction.ColdChainAtEveryLevel.DecayOnATorusForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def siteSupDist {j : ℕ} (y z : F.Site j) : ℕ := Finset.univ.sup fun i => ((y i - z i).valMinAbs).natAbs
def bondSpan {j k : ℕ} (y : F.Site j) (c : Fin k → F.Site j × Fin 4) : ℕ :=
  max (Finset.univ.sup fun l : Fin k => siteSupDist y (c l).1)
    (Finset.univ.sup fun l : Fin k => Finset.univ.sup fun l' : Fin k => siteSupDist (c l).1 (c l').1)
def bondSpread {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) :
    F.Site j → Fin 4 → imaginaryQuaternions :=
  fun y i => ∑ l, if c l = (y, i) then τ l • X l else 0
def leftTranslate {j : ℕ} (v : F.Site j → Fin 4 → imaginaryQuaternions) (W : F.GaugeField j) :
    F.GaugeField j :=
  fun y i => expUnit (v y i) * W y i
def bondDeriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j k : ℕ} (G : F.GaugeField j → E)
    (W : F.GaugeField j) (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) : E :=
  iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0
    (fun l => Pi.single l 1)
def ContDiffThreeAlongBonds {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ}
    (G : F.GaugeField j → E) (W : F.GaugeField j) : Prop :=
  ∀ (k : ℕ) (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions),
    ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0
def uniformField (F : BlockFrame) (j : ℕ) : F.GaugeField j := fun _ _ => 1
def IsSmallCurvature {j : ℕ} (s : ℝ) (X : F.GaugeField j) : Prop :=
  ∀ p : F.Site j × Fin 4 × Fin 4, p.2.1 < p.2.2 → plaquetteDefect X p < s
def translateField {j : ℕ} (h : F.Site j) (X : F.GaugeField j) : F.GaugeField j := fun y i => X (y - h) i
def bondsAt {j k : ℕ} (y : F.Site j) (h : Fin k → (Fin 4 → ℤ) × Fin 4) :
    Fin k → F.Site j × Fin 4 :=
  fun l => (y + siteOfCoords j (h l).1, (h l).2)
def cubicTorusFrame (L t n : ℕ) : BlockFrame := ⟨L, t, fun _ => n⟩
def IsCubicTorusAbove (L t n₀ : ℕ) (F : BlockFrame) : Prop :=
  F.blockSide = L ∧ F.depth = t ∧ ∃ n : ℕ, (∀ i, F.extent i = n) ∧ n₀ ≤ n * L
def AgreeOnBox {F' : BlockFrame} (W : F.GaugeField F.depth) (W' : F'.GaugeField F'.depth)
    (y : F.Site F.depth) (y' : F'.Site F'.depth) (r : ℕ) : Prop :=
  (∀ i, 2 * r + 2 < F.period F.depth i) ∧ (∀ i, 2 * r + 2 < F'.period F'.depth i) ∧
    ∀ b, BondWithinRadius r b →
      W (y + siteOfCoords F.depth b.1) b.2 = W' (y' + siteOfCoords F'.depth b.1) b.2
abbrev LocalFamily : Type := (F : BlockFrame) → F.Site F.depth → F.GaugeField F.depth → ℝ
def subtractTrivial (f : LocalFamily) : LocalFamily :=
  fun F y W => f F y W - f F y (uniformField F F.depth)
def hessianAtTrivial (f : LocalFamily) (L t n : ℕ) (b b' : (Fin 4 → ℤ) × Fin 4)
    (X X' : imaginaryQuaternions) : ℝ :=
  bondDeriv (f (cubicTorusFrame L t n) 0) (uniformField _ _) (bondsAt 0 ![b, b']) ![X, X']
abbrev BondBilinearForm : Type :=
  (Fin 4 → ℤ) × Fin 4 → (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions → imaginaryQuaternions → ℝ
def IsLinearPotential (Fm : Fin 4 → Fin 4 → imaginaryQuaternions)
    (B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions) : Prop :=
  ∃ (A : Fin 4 → Fin 4 → imaginaryQuaternions) (e : Fin 4 → imaginaryQuaternions),
    (∀ x μ, B (x, μ) = (∑ ν, (x ν : ℝ) • A μ ν) + e μ) ∧ ∀ μ ν, A ν μ - A μ ν = Fm μ ν
def IsAntisymmetricCurvature (Fm : Fin 4 → Fin 4 → imaginaryQuaternions) : Prop :=
  ∀ μ ν, Fm μ ν = - Fm ν μ
structure IsRegularFamily (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) : Prop where
  smooth : ∀ F, IsCubicTorusAbove L t n₀ F → ∀ (y : F.Site F.depth) (W : F.GaugeField F.depth),
    IsSmallCurvature σ W → ContDiffThreeAlongBonds (f F y) W
  gauge_invariant : ∀ F, IsCubicTorusAbove L t n₀ F → ∀ (y : F.Site F.depth) (W : F.GaugeField F.depth)
    (γ : F.Site F.depth → UnitQuaternion), IsSmallCurvature σ W → f F y (gaugeTransform γ W) = f F y W
  translation_invariant : ∀ F, IsCubicTorusAbove L t n₀ F → ∀ (y h : F.Site F.depth)
    (W : F.GaugeField F.depth), IsSmallCurvature σ W → f F (y + h) (translateField h W) = f F y W
  decay : ∀ F, IsCubicTorusAbove L t n₀ F → ∀ (y : F.Site F.depth) (W : F.GaugeField F.depth) (k : ℕ)
    (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions), IsSmallCurvature σ W →
    1 ≤ k → k ≤ 3 → AreUnitVectors X →
    |bondDeriv (f F y) W c X| ≤ (if k = 3 then E₃ else E) / torusDecayFactor L δ (bondSpan y c)
  locality : ∀ F F', IsCubicTorusAbove L t n₀ F → IsCubicTorusAbove L t n₀ F' →
    ∀ (y : F.Site F.depth) (y' : F'.Site F'.depth) (W : F.GaugeField F.depth)
      (W' : F'.GaugeField F'.depth) (r k : ℕ)
      (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
    IsSmallCurvature σ W → IsSmallCurvature σ W' → AgreeOnBox W W' y y' r → k ≤ 2 →
    (∀ l, BondWithinRadius r (h l)) → AreUnitVectors X →
    |bondDeriv (subtractTrivial f F y) W (bondsAt y h) X -
        bondDeriv (subtractTrivial f F' y') W' (bondsAt y' h) X| ≤
      E / torusDecayFactor L δ r
  flat_limit : ∃ q : BondBilinearForm,
    (∀ b b' X X', Filter.Tendsto (fun n => hessianAtTrivial f L t n b b' X X') Filter.atTop
      (𝓝 (q b b' X X'))) ∧
    ∀ Fm Fm' B B', IsAntisymmetricCurvature Fm → IsAntisymmetricCurvature Fm' →
      IsLinearPotential Fm B → IsLinearPotential Fm' B' →
      HasSum (fun p : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        q p.1 p.2 (B p.1) (B' p.2)) 0
end YangMills.Construction.ColdStepAtMirrorFrames
end
