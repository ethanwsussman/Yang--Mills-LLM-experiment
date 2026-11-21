import YangMills.Construction.Lattice.FivePropertiesFloorAndRepresentationsInTheSettingOfTheTorusBound
import YangMills.Construction.Lattice.KernelsLocalLogarithmAndConnectedFunctions
import YangMills.Construction.Lattice.LevelsPresentOnTheTorus
import YangMills.Construction.ToriAtArbitraryCouplings.BoundFunctionsAndTheFamiliesThatObeyThem
import YangMills.Construction.ToriAtArbitraryCouplings.ChoicesOfCountableDenseSets
import YangMills.Construction.ToriAtArbitraryCouplings.ConnectedFunctionsOfAFunctionalOnSeparatedTuples
import YangMills.Construction.ToriAtArbitraryCouplings.TheCountableFamilyAdaptedToSupports
import YangMills.Construction.ToriAtArbitraryCouplings.TheSeparationAtEveryLength
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace TorusSide
variable (s : TorusSide)
def cumulantAt (K : ℕ+) (β : ℝ) (X : s.FnTuple .torus) : ℂ :=
  PeriodicLattice.connectedFunction s.L s.m K (β : ℂ) X.get
def mirrorDataOf (K : ℕ+) (β : ℝ) (hβ : 0 < β) : ReflectionPositivity.AxisMirror.MirrorData :=
  ⟨⟨s.L, s.admissible, K, s.m⟩, β, hβ⟩
def centeredMomentAt (K : ℕ+) (β : ℝ) (hβ : 0 < β) (X : s.FnTuple .torus) : ℝ :=
  (s.mirrorDataOf K β hβ).latticeMoment X
def torusBoundSetup (m' : ℕ) (K : ℕ+) (β : ℝ) (hβ : 0 < β) : TorusBound.Setup where
  toStandingParameters := ⟨s.L, s.admissible, K, s.m⟩
  cubeExp := m'
  β := β
  β_pos := hβ
structure IsClusterConstant (C : ℕ → ℝ → ℝ) : Prop where
  nonneg : ∀ n : ℕ, 2 ≤ n → ∀ d : ℝ, 0 < d → 0 ≤ C n d
  antitoneOn : ∀ n : ℕ, 2 ≤ n → AntitoneOn (C n) (Ioi 0)
def IsClusterConstant.toClusterBound {C : ℕ → ℝ → ℝ} (hC : IsClusterConstant C) :
    Schwinger.ClusterBound where
  value n d _ := C n d
  value_nonneg n hn d _ hd _ := hC.nonneg n hn d hd
  value_anti n hn _ _ _ hd hdd' _ :=
    hC.antitoneOn n hn (mem_Ioi.2 hd) (mem_Ioi.2 (hd.trans_le hdd')) hdd'
structure IsUniformlyBoundedSeq (m' : ℕ) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (C : ℕ → ℝ → ℝ) : Prop where
  tendsto_cutoff : Tendsto K atTop atTop
  β_pos : ∀ j, 0 < β j
  isClusterConstant : IsClusterConstant C
  bound : ∀ (j : ℕ+) (n : ℕ), 2 ≤ n → ∀ d : ℝ, 0 < d →
    ∀ X ∈ s.lipDisjointOfLength .torus n, ENNReal.ofReal d ≤ s.gapAllLengths .torus X →
      ‖s.cumulantAt (K j) (β j) X‖ ≤ C n d * s.sharpNormProduct m' .torus X
abbrev ComplexTupleFns : Type :=
  (n : ℕ) → 2 ≤ n → s.sepOfLength .torus n → ℂ
def cumulantFnsAt (K : ℕ+) (β : ℝ) : s.ComplexTupleFns :=
  fun _ _ X => s.cumulantAt K β X.1
def TendstoAlong (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (J : Set ℕ+) (S : s.ComplexTupleFns) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (X : s.sepOfLength .torus n),
    Tendsto (fun j => s.cumulantFnsAt (K j) (β j) n hn X) (atTop ⊓ 𝓟 J) (𝓝 (S n hn X))
def HasConvergentSubseq (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) : Prop :=
  ∀ J₀ : Set ℕ+, J₀.Infinite →
    ∀ (I : Type) (_ : Countable I) (j₀ : I → ℕ+) (v : I → ℕ+ → ℂ),
      (∀ ι, ∃ B : ℝ, ∀ j, j₀ ι ≤ j → ‖v ι j‖ ≤ B) →
      ∃ J ⊆ J₀, J.Infinite ∧ (∃ S, s.TendstoAlong K β J S) ∧
        ∀ ι, ∃ a : ℂ, Tendsto (v ι) (atTop ⊓ 𝓟 J) (𝓝 a)
def toComplexTupleFns (F : Ambient.ConnectedFamily s.asMirrorData .torus) :
    s.ComplexTupleFns :=
  fun n hn X => (F.fn n hn X : ℂ)
def ObeysClusterEstimate (m' : ℕ) (C : ℕ → ℝ → ℝ) (Ψ : s.ComplexTupleFns) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (d : ℝ), 0 < d → ∀ X : s.sepOfLength .torus n,
    ENNReal.ofReal d ≤ s.gapAllLengths .torus X.1 →
      ‖Ψ n hn X‖ ≤ C n d * s.sharpNormProduct m' .torus X.1
def IsEquicontinuousBound (m' : ℕ) (C : ℕ → ℝ → ℝ) (Ψ : s.ComplexTupleFns) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (d : ℝ), 0 < d → ∀ A : Fin n → Set (s.Point .torus),
    (∀ i k, i ≠ k → ENNReal.ofReal d ≤ s.setDist .torus (A i) (A k)) →
    ∀ (f h : Fin n → s.Point .torus → ℝ) (hf : List.ofFn f ∈ s.sepOfLength .torus n)
      (hh : List.ofFn h ∈ s.sepOfLength .torus n),
      (∀ l, s.closedSupport .torus (f l) ⊆ A l) → (∀ l, s.closedSupport .torus (h l) ⊆ A l) →
      ‖Ψ n hn ⟨_, hf⟩ - Ψ n hn ⟨_, hh⟩‖ ≤
        C n d * ∑ l, s.sharpNormAt m' .torus (f l - h l) *
          ∏ l' ∈ Finset.univ.erase l,
            (s.sharpNormAt m' .torus (f l') + s.sharpNormAt m' .torus (h l'))
structure CenteredMomentsTendsto (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (hβ : ∀ j, 0 < β j) (J : Set ℕ+)
    (F : Ambient.ConnectedFamily s.asMirrorData .torus) : Prop where
  tendsto : ∀ X : s.sepTuples .torus,
    Tendsto (fun j => s.centeredMomentAt (K j) (β j) (hβ j) X.1) (atTop ⊓ 𝓟 J)
      (𝓝 (F.centeredFunctional X))
  isSeparated : Ambient.IsSeparatedFunctional s.asMirrorData .torus F.centeredFunctional
  isPermInvariant : ∀ n : ℕ, s.IsPermInvariant .torus (n := n)
    (Ambient.restrictN s.asMirrorData .torus F.centeredFunctional n)
  connected_one : ∀ X : s.sepOfLength .torus 1,
    Ambient.connectedOfSeparated F.centeredFunctional 1 X = 0
  connected_eq : ∀ (n : ℕ) (hn : 2 ≤ n) (X : s.sepOfLength .torus n),
    Ambient.connectedOfSeparated F.centeredFunctional n X = F.fn n hn X
structure IsUniquelyDetermined (m' : ℕ) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) {C : ℕ → ℝ → ℝ}
    (hC : IsClusterConstant C) (J : Set ℕ+)
    (F : Ambient.ConnectedFamily s.asMirrorData .torus) : Prop where
  countable : ∀ D : s.supportFamily .torus → Set (s.Point .torus → ℝ),
    s.IsCountableC1DenseChoice .torus D →
    (s.adaptedTupleSetLengthGeTwo .torus D).Countable
  eq_of_agree : ∀ D : s.supportFamily .torus → Set (s.Point .torus → ℝ),
    s.IsCountableC1DenseChoice .torus D →
    ∀ S' ∈ s.clusterBoundedFamilies m' hC.toClusterBound .torus,
    ∀ S'' ∈ s.clusterBoundedFamilies m' hC.toClusterBound .torus,
      (∀ X : s.adaptedTupleSetLengthGeTwo .torus D,
        s.evalOnAdaptedTuples S' X = s.evalOnAdaptedTuples S'' X) → S' = S''
  mem_clusterBoundedFamilies : F ∈ s.clusterBoundedFamilies m' hC.toClusterBound .torus
  tendstoAlong_subset : ∀ J' ⊆ J, J'.Infinite → s.TendstoAlong K β J' (s.toComplexTupleFns F)
def expVolumeFactor (Eplus Clow : ℝ) : ℝ := Real.exp ((Eplus + Clow) * s.length ^ 4)
def clusterBoundOfFamilies (CUV : ℝ → ℝ) (Eplus Clow ϱ' : ℝ) (n : ℕ) (d : ℝ) : ℝ :=
  (s.length ^ 4 * CUV d + Real.log 2 * (2 * s.expVolumeFactor Eplus Clow + 2) ^ n) *
    ((n : ℝ) / ϱ') ^ n
end TorusSide
namespace LimitExtraction
open TorusSide
def statement : Prop :=
  ∀ (s : TorusSide), 8 * 105 ^ 4 ≤ s.L → ∀ (m' : ℕ) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (C : ℕ → ℝ → ℝ)
    (h : s.IsUniformlyBoundedSeq m' K β C),
    s.HasConvergentSubseq K β ∧
    (∀ j, s.IsEquicontinuousBound m' C (s.cumulantFnsAt (K j) (β j))) ∧
    ∀ J : Set ℕ+, J.Infinite → ∀ S : s.ComplexTupleFns, s.TendstoAlong K β J S →
      ∃ F : Ambient.ConnectedFamily s.asMirrorData .torus,
        s.toComplexTupleFns F = S ∧
        s.IsPermInvariantFamily .torus F ∧
        s.ObeysClusterEstimate m' C (s.toComplexTupleFns F) ∧
        s.IsEquicontinuousBound m' C (s.toComplexTupleFns F) ∧
        s.CenteredMomentsTendsto K β h.β_pos J F ∧
        s.IsUniquelyDetermined m' K β h.isClusterConstant J F
def boundFromFamilies : Prop :=
  ∃ CUV : ℕ → ℕ → ℝ → ℝ → ℝ → ℝ,
    ∀ (s : TorusSide), 8 * 105 ^ 4 ≤ s.L → ∀ (m' : ℕ) (Ce κe : ℝ), 0 ≤ Ce →
      PolymerActivities.DomainCounting.countingRate < κe →
      (∀ d : ℝ, 0 < d → 0 < CUV s.L (cubeEdge s.L m') Ce κe d) ∧
      AntitoneOn (CUV s.L (cubeEdge s.L m') Ce κe) (Ioi 0) ∧
      ∀ (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (hβ : ∀ j, 0 < β j), Tendsto K atTop atTop →
        (∀ (j : ℕ+) (i : ℕ), i ≤ (K j : ℕ) → (s.torusBoundSetup m' (K j) (β j) (hβ j)).LevelFits i) →
        ∀ (Eplus Clow ϱ' : ℝ) (hϱ' : 0 < ϱ'),
          (∀ j, ∃ e : (s.torusBoundSetup m' (K j) (β j) (hβ j)).RadiusFamily ϱ' hϱ',
            e.SatisfiesFiveBounds Ce κe Eplus Clow) →
          s.IsUniformlyBoundedSeq m' K β
            (s.clusterBoundOfFamilies (CUV s.L (cubeEdge s.L m') Ce κe) Eplus Clow ϱ')
end LimitExtraction
end YangMills.Construction.ToriAtArbitraryCouplings
end
