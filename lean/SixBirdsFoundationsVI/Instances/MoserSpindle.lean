import SixBirdsFoundationsVI.Laws.G12FiniteWitnessRadiation
import Std

namespace SixBirdsFoundationsVI.Instances.MoserSpindle
open SixBirdsFoundationsVI.Laws.G12FiniteWitnessRadiation

abbrev Vertex := Fin 7

/-- 0=A, 1=B, 2=C, 3=D, 4=B', 5=C', 6=D'. -/
def edges : List (Vertex × Vertex) :=
  [(0,1), (0,2), (1,2), (1,3), (2,3),
   (0,4), (0,5), (4,5), (4,6), (5,6), (3,6)]

def Edge (x y : Vertex) : Prop := (x,y) ∈ edges ∨ (y,x) ∈ edges

def vertices : List Vertex := List.ofFn id

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem finite_check (a b c d e f g : Fin 3)
    (h01 : a ≠ b) (h02 : a ≠ c) (h12 : b ≠ c)
    (h13 : b ≠ d) (h23 : c ≠ d)
    (h04 : a ≠ e) (h05 : a ≠ f) (h45 : e ≠ f)
    (h46 : e ≠ g) (h56 : f ≠ g) (h36 : d ≠ g) : False := by
  have n01 := Fin.val_ne_of_ne h01
  have n02 := Fin.val_ne_of_ne h02
  have n12 := Fin.val_ne_of_ne h12
  have n13 := Fin.val_ne_of_ne h13
  have n23 := Fin.val_ne_of_ne h23
  have n04 := Fin.val_ne_of_ne h04
  have n05 := Fin.val_ne_of_ne h05
  have n45 := Fin.val_ne_of_ne h45
  have n46 := Fin.val_ne_of_ne h46
  have n56 := Fin.val_ne_of_ne h56
  have n36 := Fin.val_ne_of_ne h36
  have ba := a.isLt; have bb := b.isLt; have bc := c.isLt
  have bd := d.isLt; have be := e.isLt; have bf := f.isLt; have bg := g.isLt
  omega

theorem no_fin3_coloring :
    ¬ ∃ c : Vertex → Fin 3, ∀ x y, Edge x y → c x ≠ c y := by
  intro ⟨c, h⟩
  apply finite_check (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6)
  all_goals apply h <;> simp [Edge, edges]

theorem spindle_witness : FiniteWitnessObstruction Edge 3 vertices := by
  intro h
  obtain ⟨c, hb, he⟩ := h
  apply no_fin3_coloring
  let d : Vertex → Fin 3 := fun i => ⟨c i, hb i (List.mem_ofFn.mpr ⟨i, rfl⟩)⟩
  refine ⟨d, ?_⟩
  intro x y hxy
  exact Fin.ne_of_val_ne (he x y (List.mem_ofFn.mpr ⟨x, rfl⟩)
    (List.mem_ofFn.mpr ⟨y, rfl⟩) hxy)

/-- G12 transfers the obstruction through any edge-preserving image. -/
theorem no_coloring_of_edge_image {X : Type} (E : X → X → Prop)
    (f : Vertex → X) (hf : ∀ x y, Edge x y → E (f x) (f y)) :
    ¬ ∃ c : X → Nat, ProperKColoring E 3 c := by
  have hw : FiniteWitnessObstruction E 3 (vertices.map f) := by
    intro hc
    obtain ⟨c, hb, he⟩ := hc
    apply spindle_witness
    refine ⟨fun x => c (f x), ?_, ?_⟩
    · intro x hx
      apply hb (f x)
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
    · intro x y hx hy hxy
      apply he (f x) (f y)
      · exact List.mem_map.mpr ⟨x, hx, rfl⟩
      · exact List.mem_map.mpr ⟨y, hy, rfl⟩
      · exact hf x y hxy
  exact no_global_k_coloring E 3 (vertices.map f) hw

#print axioms finite_check
#print axioms no_fin3_coloring
#print axioms spindle_witness
#print axioms no_coloring_of_edge_image
end SixBirdsFoundationsVI.Instances.MoserSpindle
