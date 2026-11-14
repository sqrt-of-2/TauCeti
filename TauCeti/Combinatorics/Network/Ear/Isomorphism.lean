/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Ear.Basic
public import TauCeti.Combinatorics.Network.Isomorphism.Subnetwork

/-!
# Directed ear decompositions under network isomorphisms

Relabelling a bounded network transports open and closed directed ears and entire ear
decompositions. Every prefix is the image subnetwork, and each ear retains its kind and its
ordered walk, including individual parallel arrows and loops. The transport is an equivalence,
so a chosen decomposition can be reused after relabelling without making new existence choices.

No finiteness or algebraic structure on the bounds is required.
-/

public section

namespace TauCeti.Network

universe u u' w

variable {K : Type w} [LE K] {V : Type u} {W : Type u'}
  {N : Network K V} {N' : Network K W} {S T : N.Subnetwork}

namespace OpenEar

/-- Relabel an open directed ear, retaining its path and all arrow identities. -/
def map (P : OpenEar S) (e : N ≃ₙ N') : OpenEar (e.subnetworkOrderIso S) where
  source := e.vertexEquiv P.source
  target := e.vertexEquiv P.target
  walk := e.mapPath P.walk
  isPath := (e.isPath_mapPath P.walk).mpr P.isPath
  source_mem := by
    rw [Iso.subnetworkOrderIso_vertexSet]
    exact ⟨_, P.source_mem, rfl⟩
  target_mem := by
    rw [Iso.subnetworkOrderIso_vertexSet]
    exact ⟨_, P.target_mem, rfl⟩
  source_ne_target := e.vertexEquiv.injective.ne P.source_ne_target
  internal_notMem := by
    rintro _ hx hsource htarget hS
    rw [Iso.vertices_mapPath, List.mem_map] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    exact P.internal_notMem x hx (fun h ↦ hsource (congrArg e.vertexEquiv h))
      (fun h ↦ htarget (congrArg e.vertexEquiv h)) (by simpa using hS)
  arrows_notMem := by
    rintro _ ha hS
    rw [Iso.arrows_mapPath, List.mem_map] at ha
    obtain ⟨a, ha, rfl⟩ := ha
    exact P.arrows_notMem a ha (by
      simpa only [Iso.subnetworkOrderIso_arrowSet,
        e.totalHomEquiv.injective.mem_set_image] using hS)

@[simp]
theorem map_source (P : OpenEar S) (e : N ≃ₙ N') :
    (P.map e).source = e.vertexEquiv P.source := (rfl)

@[simp]
theorem map_target (P : OpenEar S) (e : N ≃ₙ N') :
    (P.map e).target = e.vertexEquiv P.target := (rfl)

/-- The endpoint-indexed walk of the relabelled ear is its transported walk. -/
@[simp]
theorem toWalk_map (P : OpenEar S) (e : N ≃ₙ N') :
    (P.map e).toWalk = e.totalPathEquiv P.toWalk := by
  cases P
  simp only [map, toWalk_mk, Iso.totalPathEquiv_apply]

end OpenEar

namespace ClosedEar

/-- Relabel a closed directed ear, including a one-arrow loop ear. -/
def map (P : ClosedEar S) (e : N ≃ₙ N') : ClosedEar (e.subnetworkOrderIso S) where
  base := e.vertexEquiv P.base
  walk := e.mapPath P.walk
  isCycle := (e.isCycle_mapPath P.walk).mpr P.isCycle
  base_mem := by
    rw [Iso.subnetworkOrderIso_vertexSet]
    exact ⟨_, P.base_mem, rfl⟩
  eq_base_of_mem := by
    rintro _ hx hS
    rw [Iso.vertices_mapPath, List.mem_map] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    exact congrArg e.vertexEquiv (P.eq_base_of_mem x hx (by simpa using hS))
  arrows_notMem := by
    rintro _ ha hS
    rw [Iso.arrows_mapPath, List.mem_map] at ha
    obtain ⟨a, ha, rfl⟩ := ha
    exact P.arrows_notMem a ha (by
      simpa only [Iso.subnetworkOrderIso_arrowSet,
        e.totalHomEquiv.injective.mem_set_image] using hS)

@[simp]
theorem map_base (P : ClosedEar S) (e : N ≃ₙ N') :
    (P.map e).base = e.vertexEquiv P.base := (rfl)

/-- The endpoint-indexed cycle of the relabelled ear is its transported cycle. -/
@[simp]
theorem toWalk_map (P : ClosedEar S) (e : N ≃ₙ N') :
    (P.map e).toWalk = e.totalPathEquiv P.toWalk := by
  cases P
  simp only [map, toWalk_mk, Iso.totalPathEquiv_apply]

end ClosedEar

namespace Ear

/-- Transport a directed ear to the image subnetwork. -/
def map (P : Ear S) (e : N ≃ₙ N') : Ear (e.subnetworkOrderIso S) :=
  match P with
  | .open P => .open (P.map e)
  | .closed P => .closed (P.map e)

@[simp]
theorem map_open (P : OpenEar S) (e : N ≃ₙ N') :
    (Ear.open P).map e = .open (P.map e) := (rfl)

@[simp]
theorem map_closed (P : ClosedEar S) (e : N ≃ₙ N') :
    (Ear.closed P).map e = .closed (P.map e) := (rfl)

/-- Relabelling preserves whether an ear is open or closed. -/
@[simp]
theorem kind_map (P : Ear S) (e : N ≃ₙ N') : (P.map e).kind = P.kind := by
  cases P <;> simp

/-- Relabelling transports the entire endpoint-indexed walk of an ear. -/
@[simp]
theorem toWalk_map (P : Ear S) (e : N ≃ₙ N') :
    (P.map e).toWalk = e.totalPathEquiv P.toWalk := by
  cases P <;> simp

/-- The subnetwork traced by an ear commutes with relabelling. -/
@[simp]
theorem toSubnetwork_map (P : Ear S) (e : N ≃ₙ N') :
    (P.map e).toSubnetwork = e.subnetworkOrderIso P.toSubnetwork := by
  cases P <;> simp [OpenEar.map, ClosedEar.map]

/-- Adjoining a directed ear commutes with relabelling. -/
@[simp]
theorem adjoin_map (P : Ear S) (e : N ≃ₙ N') :
    (P.map e).adjoin = e.subnetworkOrderIso P.adjoin := by
  simp [adjoin_def]

/-- Transport along an isomorphism and then its inverse recovers the ear. -/
@[simp]
theorem map_symm_map (P : Ear S) (e : N ≃ₙ N') :
    ((P.map e).map e.symm).copy (by simp) = P := by
  apply Ear.ext
  simp only [toWalk_copy, toWalk_map, Iso.totalPathEquiv_symm, Equiv.symm_apply_apply]

end Ear

namespace Iso

/-- A network isomorphism gives a bijection of the directed ears at corresponding subnetworks. -/
def earEquiv (e : N ≃ₙ N') (S : N.Subnetwork) : Ear S ≃ Ear (e.subnetworkOrderIso S) where
  toFun P := P.map e
  invFun P := (P.map e.symm).copy (by simp)
  left_inv P := P.map_symm_map e
  right_inv P := by
    apply Ear.ext
    simp

@[simp]
theorem earEquiv_apply (e : N ≃ₙ N') (S : N.Subnetwork) (P : Ear S) :
    e.earEquiv S P = P.map e := (rfl)

@[simp]
theorem earEquiv_symm_apply (e : N ≃ₙ N') (S : N.Subnetwork)
    (P : Ear (e.subnetworkOrderIso S)) :
    (e.earEquiv S).symm P = (P.map e.symm).copy (by simp) := (rfl)

end Iso

namespace EarDecomposition

/-- Transport all stages and ears of a directed ear decomposition.

Reducibility lets the dependent `Fin` indices of stages and ears be used unchanged in a client:
transport preserves the length definitionally, not just up to an index cast. -/
@[expose, reducible]
def map (D : EarDecomposition T) (e : N ≃ₙ N') :
    EarDecomposition (e.subnetworkOrderIso T) where
  length := D.length
  initialVertex := e.vertexEquiv D.initialVertex
  stage i := e.subnetworkOrderIso (D.stage i)
  ear i := (D.ear i).map e
  stage_zero := by simp
  stage_succ i := by rw [D.stage_succ, Ear.adjoin_map]
  stage_last := by rw [D.stage_last]

@[simp]
theorem map_length (D : EarDecomposition T) (e : N ≃ₙ N') :
    (D.map e).length = D.length := (rfl)

@[simp]
theorem map_initialVertex (D : EarDecomposition T) (e : N ≃ₙ N') :
    (D.map e).initialVertex = e.vertexEquiv D.initialVertex := (rfl)

/-- Every prefix subnetwork is relabelled by the subnetwork order isomorphism. -/
@[simp]
theorem map_stage (D : EarDecomposition T) (e : N ≃ₙ N') (i : Fin (D.length + 1)) :
    (D.map e).stage i = e.subnetworkOrderIso (D.stage i) := (rfl)

/-- Each displayed ear is the relabelled original ear. -/
@[simp]
theorem map_ear (D : EarDecomposition T) (e : N ≃ₙ N') (i : Fin D.length) :
    (D.map e).ear i = (D.ear i).map e := (rfl)

/-- Every ear keeps its kind under relabelling. -/
@[simp]
theorem kindAt_map (D : EarDecomposition T) (e : N ≃ₙ N') (i : Fin D.length) :
    (D.map e).kindAt i = D.kindAt i := by simp [kindAt_def]

/-- Every ear keeps its full walk with vertices and arrow identities relabelled. -/
@[simp]
theorem walkAt_map (D : EarDecomposition T) (e : N ≃ₙ N') (i : Fin D.length) :
    (D.map e).walkAt i = e.totalPathEquiv (D.walkAt i) := by simp [walkAt_def]

/-- Transport followed by inverse transport recovers every stage and every ear. -/
@[simp]
theorem map_symm_map (D : EarDecomposition T) (e : N ≃ₙ N') :
    ((D.map e).map e.symm).copy (by simp) = D := by
  refine ext_walkAt (D := ((D.map e).map e.symm).copy (by simp)) (E := D)
    (by rfl) ?_
  intro i
  rw [copy_walkAt ((D.map e).map e.symm) _ i, walkAt_map (D.map e) e.symm i,
    walkAt_map D e i]
  simp only [Iso.totalPathEquiv_symm, Equiv.symm_apply_apply]
  rfl

/-- Transport commutes with taking a prefix decomposition. -/
@[simp]
theorem prefixDecomposition_map (D : EarDecomposition T) (e : N ≃ₙ N')
    (k : Fin (D.length + 1)) :
    (D.map e).prefixDecomposition k = (D.prefixDecomposition k).map e := (rfl)

end EarDecomposition

namespace Iso

/-- Relabelling is an equivalence of directed ear decomposition data, not merely of existence
propositions. The inverse transports back and identifies the recovered final subnetwork. -/
def earDecompositionEquiv (e : N ≃ₙ N') (T : N.Subnetwork) :
    EarDecomposition T ≃ EarDecomposition (e.subnetworkOrderIso T) where
  toFun D := D.map e
  invFun D := (D.map e.symm).copy (by simp)
  left_inv D := D.map_symm_map e
  right_inv D := by
    refine EarDecomposition.ext_walkAt
      (D := ((D.map e.symm).copy (by simp)).map e) (E := D) (by rfl) ?_
    intro i
    rw [EarDecomposition.walkAt_map ((D.map e.symm).copy _) e i,
      EarDecomposition.copy_walkAt (D.map e.symm) _ i,
      EarDecomposition.walkAt_map D e.symm i]
    simp only [totalPathEquiv_symm, Equiv.apply_symm_apply]
    rfl

@[simp]
theorem earDecompositionEquiv_apply (e : N ≃ₙ N') (T : N.Subnetwork)
    (D : EarDecomposition T) : e.earDecompositionEquiv T D = D.map e := (rfl)

@[simp]
theorem earDecompositionEquiv_symm_apply (e : N ≃ₙ N') (T : N.Subnetwork)
    (D : EarDecomposition (e.subnetworkOrderIso T)) :
    (e.earDecompositionEquiv T).symm D = (D.map e.symm).copy (by simp) := (rfl)

end Iso

end TauCeti.Network
