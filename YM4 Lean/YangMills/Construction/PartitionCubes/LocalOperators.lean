import YangMills.Construction.PartitionCubes.CubesAndCutoffs
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.RegionSequence
open YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction
namespace PartitionCubes
variable {𝒮 : NestedRegions} {M : ℕ}
def closedCube (c : Fin 4 → ℝ) (σ : ℝ) : Set (Fin 4 → ℝ) := {p | ∀ μ, |p μ - c μ| ≤ σ / 2}
def LevelCube.torusSide (Q : LevelCube 𝒮 M) : ℝ := 8 * cubeSide 𝒮 M Q.level
def LevelCube.liftedCentre (Q : LevelCube 𝒮 M) : Fin 4 → ℝ := fun μ => circleCentredRep (Q.centre μ)
def LevelCube.nextCentres (Q : LevelCube 𝒮 M) : Set (Fin 4 → ℝ) :=
  {c | closedCube c (cubeSide 𝒮 M Q.level) ⊆ closedCube Q.liftedCentre (6 * cubeSide 𝒮 M Q.level) ∧
    torusProj 4 𝒮.side '' closedCube c (cubeSide 𝒮 M Q.level) ∈
      cubePartition 4 𝒮.side (cubeSide 𝒮 M Q.level) ∧
    torusProj 4 𝒮.side '' closedCube c (cubeSide 𝒮 M Q.level) ⊆ 𝒮.Ω (Q.level + 1)}
def LevelCube.nextRegion (Q : LevelCube 𝒮 M) : Set (PeriodicTorus 4 Q.torusSide) :=
  torusProj 4 Q.torusSide '' ⋃ c ∈ Q.nextCentres, closedCube c (cubeSide 𝒮 M Q.level)
def LevelCube.torusRegions (Q : LevelCube 𝒮 M) (j : ℕ) : Set (PeriodicTorus 4 Q.torusSide) :=
  if j ≤ Q.level then univ else if j = Q.level + 1 then Q.nextRegion else ∅
structure LevelCube.IsAdmissible (Q : LevelCube 𝒮 M) : Prop where
  side_pos : 0 < Q.torusSide
  side_mem_zmultiples : ∃ k : ℤ,
    Q.torusSide = (k : ℝ) * (2 * scaleSpacing 𝒮.L 𝒮.ξ ((Q.level + 1 : ℕ) : ℤ))
  isCubeUnion : ∀ j ≤ Q.level + 1, IsCubeUnion (scaleSpacing 𝒮.L 𝒮.ξ (j : ℤ)) (Q.torusRegions j)
def LevelCube.torusSetting (Q : LevelCube 𝒮 M) (h : Q.IsAdmissible) : NestedRegions where
  L := 𝒮.L
  odd_L := 𝒮.odd_L
  thirteen_le_L := 𝒮.thirteen_le_L
  ξ := 𝒮.ξ
  ξ_pos := 𝒮.ξ_pos
  side := Q.torusSide
  side_pos := h.side_pos
  s := Q.level + 1
  side_mem_zmultiples := h.side_mem_zmultiples
  Ω := Q.torusRegions
  Ω_succ_subset := by
    intro j hj
    have hj' : j ≤ Q.level := Nat.lt_succ_iff.mp hj
    intro x _
    simp [LevelCube.torusRegions, hj']
  isCubeUnion_Ω := h.isCubeUnion
  Ω_eq_empty := by
    intro j hj
    have h₁ : ¬ j ≤ Q.level := by omega
    have h₂ : j ≠ Q.level + 1 := by omega
    simp [LevelCube.torusRegions, h₁, h₂]
  bonds := univ
  mem_bonds_of_mem := fun _ _ _ => mem_univ _
  mem_of_mem_bonds := fun _ _ => Or.inl (by simp [LevelCube.torusRegions])
open Classical in
def LevelCube.firstTypeSetting (Q : LevelCube 𝒮 M) : NestedRegions :=
  if h : Q.IsAdmissible then Q.torusSetting h else 𝒮
def LevelCube.chart (Q : LevelCube 𝒮 M) (x : 𝒮.Point) : Fin 4 → ℝ :=
  Classical.epsilon fun p =>
    (∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level) ∧ torusProj 4 𝒮.side p = x
structure CubeSystem (𝒮 : NestedRegions) where
  setting : NestedRegions
  embed : 𝒮.Point → setting.Point
  forms : Submodule ℝ (setting.FineBond → ℝ)
  op : (setting.FineBond → ℝ) → setting.FineBond → ℝ
def LevelCube.firstTypeSystem (Q : LevelCube 𝒮 M) : CubeSystem 𝒮 where
  setting := Q.firstTypeSetting
  embed := fun x => torusProj 4 Q.firstTypeSetting.side (Q.chart x)
  forms := Q.firstTypeSetting.oneForms
  op := baseOp
def LevelCube.coreBonds (Q : LevelCube 𝒮 M) : Set 𝒮.FineBond :=
  {b | b ∈ 𝒮.bonds ∧ (b.source : 𝒮.Point) ∈ Q.enlarge 3 ∧ (b.target : 𝒮.Point) ∈ Q.enlarge 3}
def LevelCube.coreForms (Q : LevelCube 𝒮 M) : Submodule ℝ (𝒮.FineBond → ℝ) where
  carrier := {A | A ∈ 𝒮.oneForms ∧ ∀ b : 𝒮.FineBond,
    ¬((b.source : 𝒮.Point) ∈ Q.enlarge 3 ∧ (b.target : 𝒮.Point) ∈ Q.enlarge 3) → A b = 0}
  add_mem' := fun hA hB => ⟨𝒮.oneForms.add_mem hA.1 hB.1, fun b hb => by
    simp [hA.2 b hb, hB.2 b hb]⟩
  zero_mem' := ⟨𝒮.oneForms.zero_mem, fun _ _ => rfl⟩
  smul_mem' := fun c _ hA => ⟨𝒮.oneForms.smul_mem c hA.1, fun b hb => by simp [hA.2 b hb]⟩
def LevelCube.coreProj (Q : LevelCube 𝒮 M) (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  indicator Q.coreBonds A
def LevelCube.coreOp (Q : LevelCube 𝒮 M) (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  Q.coreProj (curlTorusAdj (curlTorus (Q.coreProj A))) +
    (gaugeParam * (𝒮.ξ ^ 2)⁻¹) • A
def LevelCube.secondTypeSystem (Q : LevelCube 𝒮 M) : CubeSystem 𝒮 where
  setting := 𝒮
  embed := id
  forms := Q.coreForms
  op := Q.coreOp
open Classical in
def LevelCube.system (Q : LevelCube 𝒮 M) : CubeSystem 𝒮 :=
  if Q.IsSecondType then Q.secondTypeSystem else Q.firstTypeSystem
namespace CubeSystem
variable (𝔏 : CubeSystem 𝒮)
def inv (v : 𝔏.setting.FineBond → ℝ) : 𝔏.setting.FineBond → ℝ :=
  inverseValue (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) 𝔏.op v
def mapSite (x : 𝒮.FineSite) : 𝔏.setting.FineSite :=
  Classical.epsilon fun y => (y : 𝔏.setting.Point) = 𝔏.embed x
def mapBond (b : 𝒮.FineBond) : 𝔏.setting.FineBond := ⟨𝔏.mapSite b.source, b.dir⟩
def pushBonds (φ : 𝒮.Point → ℝ) (v : 𝔏.setting.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  fun b => φ (b.source : 𝒮.Point) * v (𝔏.mapBond b)
def pullBonds (φ : 𝒮.Point → ℝ) (A : 𝒮.FineBond → ℝ) : 𝔏.setting.FineBond → ℝ :=
  fun c => ∑ᶠ b ∈ {b : 𝒮.FineBond | (b.source : 𝒮.Point) ∈ tsupport φ ∧ 𝔏.mapBond b = c},
    φ (b.source : 𝒮.Point) * A b
def pushSites (φ : 𝒮.Point → ℝ) (f : 𝔏.setting.FineSite → ℝ) : 𝒮.FineSite → ℝ :=
  fun x => φ (x : 𝒮.Point) * f (𝔏.mapSite x)
def pullSites (φ : 𝒮.Point → ℝ) (f : 𝒮.FineSite → ℝ) : 𝔏.setting.FineSite → ℝ :=
  fun y => ∑ᶠ x ∈ {x : 𝒮.FineSite | (x : 𝒮.Point) ∈ tsupport φ ∧ 𝔏.mapSite x = y},
    φ (x : 𝒮.Point) * f x
def pushTensor {r : ℕ} (φ : 𝒮.Point → ℝ) (J : 𝔏.setting.Tensor r) : 𝒮.Tensor r :=
  fun ν => 𝔏.pushBonds φ (J ν)
def pullTensor {r : ℕ} (φ : 𝒮.Point → ℝ) (J : 𝒮.Tensor r) : 𝔏.setting.Tensor r :=
  fun ν => 𝔏.pullBonds φ (J ν)
def transferFn (φ : 𝒮.Point → ℝ) (y : 𝔏.setting.Point) : ℝ :=
  ∑ᶠ x ∈ {x : 𝒮.Point | x ∈ tsupport φ ∧ 𝔏.embed x = y}, φ x
def mulTransfer (φ : 𝒮.Point → ℝ) (v : 𝔏.setting.FineBond → ℝ) : 𝔏.setting.FineBond → ℝ :=
  fun c => 𝔏.transferFn φ (c.source : 𝔏.setting.Point) * v c
def lapComm (φ : 𝒮.Point → ℝ) (v : 𝔏.setting.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  𝔏.pushBonds φ (bondLap v) - bondLap (𝔏.pushBonds φ v)
def curlComm (φ : 𝒮.Point → ℝ) (v : 𝔏.setting.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  𝔏.pushBonds φ (curlTorusAdj (curlTorus v)) - curlTorusAdj (curlTorus (𝔏.pushBonds φ v))
def avgComm (φ : 𝒮.Point → ℝ) (v : 𝔏.setting.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  𝔏.pushBonds φ (avgOp v) - avgOp (𝔏.pushBonds φ v)
end CubeSystem
def mulBonds (φ : 𝒮.Point → ℝ) (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  fun b => φ (b.source : 𝒮.Point) * A b
def lapBracket (φ : 𝒮.Point → ℝ) (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  mulBonds φ (bondLap A) - bondLap (mulBonds φ A)
def avgBracket (φ : 𝒮.Point → ℝ) (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  mulBonds φ (avgOp A) - avgOp (mulBonds φ A)
def LevelCube.torusDist (Q : LevelCube 𝒮 M) (o o' : Q.system.setting.Point) : ℝ :=
  (𝒮.scale Q.level)⁻¹ * lOneNorm (o - o')
def LevelCube.defectOp (Q : LevelCube 𝒮 M) (v : Q.system.setting.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  Q.system.pushBonds Q.partitionFn (Q.system.op v) -
    baseOp (Q.system.pushBonds Q.partitionFn v)
def LevelCube.invTerm (Q : LevelCube 𝒮 M) (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  Q.system.pushBonds Q.partitionFn (Q.system.inv (Q.system.pullBonds Q.partitionFn A))
def LevelCube.remTerm (Q : LevelCube 𝒮 M) (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  Q.defectOp (Q.system.inv (Q.system.pullBonds Q.partitionFn A))
variable (𝒮 M) in
def approxInverse (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  fun b => ∑ᶠ Q ∈ active 𝒮 M, Q.invTerm A b
variable (𝒮 M) in
def remainderOp (A : 𝒮.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  fun b => ∑ᶠ Q ∈ active 𝒮 M, Q.remTerm A b
def LevelCube.torusLongOp (Q : LevelCube 𝒮 M) (v : Q.system.setting.FineBond → ℝ) :
    Q.system.setting.FineBond → ℝ :=
  longOp v
open Classical in
def LevelCube.diagKernel (Q : LevelCube 𝒮 M) (v : Q.system.setting.FineBond → ℝ) :
    𝒮.FineBond → ℝ :=
  if Q.IsSecondType then projBonds (Q.system.curlComm Q.partitionFn v)
  else
    Q.system.lapComm Q.partitionFn v + Q.system.avgComm Q.partitionFn v +
      (mulBonds Q.smallCutoff (longOp (Q.system.pushBonds Q.partitionFn v)) -
        Q.system.pushBonds Q.smallCutoff
          (Q.torusLongOp (Q.system.mulTransfer Q.partitionFn v))) +
      Q.system.pushBonds Q.smallCutoff
        (Q.torusLongOp (Q.system.mulTransfer Q.partitionFn v) -
          Q.system.mulTransfer Q.partitionFn (Q.torusLongOp v))
open Classical in
def LevelCube.offDiagKernel (Q' Q : LevelCube 𝒮 M) (v : Q.system.setting.FineBond → ℝ) :
    𝒮.FineBond → ℝ :=
  if Q.IsSecondType then 0
  else
    mulBonds (fun x => Q'.partitionFn x ^ 2)
      (mulBonds (fun x => 1 - Q.smallCutoff x)
        (longOp (Q.system.pushBonds Q.partitionFn v)))
open Classical in
def LevelCube.kernel (Q' Q : LevelCube 𝒮 M) (v : Q.system.setting.FineBond → ℝ) :
    𝒮.FineBond → ℝ :=
  if Q' = Q then Q.diagKernel v else Q'.offDiagKernel Q v
end PartitionCubes
end YangMills.Construction
