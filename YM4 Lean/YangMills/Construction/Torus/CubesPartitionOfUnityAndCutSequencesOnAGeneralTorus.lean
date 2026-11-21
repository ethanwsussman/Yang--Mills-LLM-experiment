import YangMills.Construction.Torus.FormsAveragesAndOperatorsOnAGeneralTorus
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.GeneralTorus
def IsCubeCorner {S : ℝ} (s : ℝ) (q : Set (Torus4 S)) (z : Torus4 S) : Prop :=
  ∃ y : Torus4 S, q = supCube s y ∧ ∃ ε : Fin 4 → ℝ, (∀ μ, ε μ = 1 ∨ ε μ = -1) ∧
    z = y + torusProj S fun μ => s / 2 * ε μ
namespace ScaleData
abbrev CubeIndex (D : ScaleData) : Type := ℕ × D.Space
variable {D : ScaleData}
def cubeScale (Q : D.CubeIndex) : ℝ := D.blockLength Q.1
def scaledCube (Q : D.CubeIndex) (r : ℝ) : Set D.Space :=
  {x | torusSupNorm (x - Q.2) ≤ r * cubeScale Q}
def cubeSet (Q : D.CubeIndex) : Set D.Space := scaledCube Q 1
def bump (Q : D.CubeIndex) (x : D.Space) : ℝ :=
  min 1 (max 0 (4 - 6 * torusSupNorm (x - Q.2) / cubeScale Q))
def cutoffFn (Q : D.CubeIndex) (x : D.Space) : ℝ :=
  min 1 (max 0 (5 - 3 * torusSupNorm (x - Q.2) / cubeScale Q))
def cutoffOnSites (Q : D.CubeIndex) : D.SiteField := fun x => cutoffFn Q x
variable (D)
def bondMul (θ : D.SiteField) (A : D.BondField) : D.BondField := fun b => θ b.1.src * A b
def plaquetteMul (θ : D.SiteField) (F : D.PlaquetteField) : D.PlaquetteField :=
  fun p => θ p.basePoint * F p
def leibnizTerm (θ : D.SiteField) (A : D.BondField) : D.PlaquetteField := fun p =>
  D.forwardDiff p.dir₁ θ p.basePoint *
      D.formComponent p.dir₂ A (p.basePoint + unitStep D.torusSide (D.levelSpacing 0) p.dir₁) -
    D.forwardDiff p.dir₂ θ p.basePoint *
      D.formComponent p.dir₁ A (p.basePoint + unitStep D.torusSide (D.levelSpacing 0) p.dir₂)
end ScaleData
namespace SeparatedChain
variable {D : ScaleData} (B : SeparatedChain D)
def cubesAt (n : ℕ) : Set D.CubeIndex :=
  {Q | n ≤ D.lastLevel ∧ Q.1 = n ∧
    ∃ q ∈ D.blockPartition n, q ⊆ B.shell n ∧ IsCubeCorner (D.blockLength n) q Q.2}
def allCubes : Set D.CubeIndex := ⋃ n, B.cubesAt n
def cutLevel (Q : D.CubeIndex) : ℕ := min (Q.1 + 1) B.lastNonempty
def envelopeAux (Q : D.CubeIndex) : ℕ → Set D.Space
  | 0 => ⋃₀ {q ∈ D.blockPartition (B.cutLevel Q) | (q ∩ ScaleData.scaledCube Q 2).Nonempty}
  | k + 1 => {x | setSupDist ({x} : Set D.Space) (envelopeAux Q k) ≤
      ENNReal.ofReal (((D.gapCount : ℝ) + 1) * D.blockLength (B.cutLevel Q - (k + 1)))}
def envelope (Q : D.CubeIndex) (m : ℕ) : Set D.Space := B.envelopeAux Q (B.cutLevel Q - m)
open Classical in
def localSet (Q : D.CubeIndex) (m : ℕ) : Set D.Space :=
  if m ≤ B.cutLevel Q then ⋃₀ {q ∈ D.blockPartition m | q ⊆ B.set m ∧ q ⊆ B.envelope Q m} else ∅
def IsLocalization (Q : D.CubeIndex) (B' : SeparatedChain D) : Prop :=
  ∀ m, B'.set m = B.localSet Q m
def localization (Q : D.CubeIndex) : SeparatedChain D :=
  haveI : Nonempty (SeparatedChain D) := ⟨B⟩
  Classical.epsilon (B.IsLocalization Q)
end SeparatedChain
structure CubeGaugeSetting extends GaugeSetting where
  twelve_mul_L_le_blockCount : 12 * data.L ≤ data.blockCount
namespace CubeGaugeSetting
variable (C : CubeGaugeSetting)
def bondsIn (Q : C.data.CubeIndex) : Set C.CoarseBond :=
  {c | GaugeSetting.coarseAnchor c ∈ ScaleData.cubeSet Q}
def cubeIndicator (Q : C.data.CubeIndex) : Module.End ℝ C.CoarseField :=
  C.indicatorMul (C.bondsIn Q)
def coarseBump (Q : C.data.CubeIndex) (c : C.CoarseBond) : ℝ :=
  ScaleData.bump Q (GaugeSetting.coarseAnchor c)
def unityWeight (Q : C.data.CubeIndex) (c : C.CoarseBond) : ℝ :=
  C.coarseBump Q c * (∑ᶠ Q' ∈ C.chain.allCubes, C.coarseBump Q' c ^ 2) ^ (-(1 / 2) : ℝ)
def unityMul (Q : C.data.CubeIndex) : Module.End ℝ C.CoarseField where
  toFun f c := C.unityWeight Q c * f c
  map_add' f g := by
    funext c
    simp only [Pi.add_apply]
    ring
  map_smul' r f := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def localSetting (Q : C.data.CubeIndex) : CubeGaugeSetting where
  data := C.data
  chain := C.chain.localization Q
  L_le_gapCount := C.L_le_gapCount
  choice := C.choice
  mass := C.mass
  mass_pos := C.mass_pos
  twelve_mul_L_le_blockCount := C.twelve_mul_L_le_blockCount
end CubeGaugeSetting
end YangMills.Construction.GeneralTorus
