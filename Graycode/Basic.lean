--import Mathlib
import Mathlib.Analysis.Normed.Lp.lpSpace

#synth AddCommGroup (Fin 2)

def next_to (x y : ℕ) : Prop :=
  ∃ j, x.testBit j != y.testBit j ∧
    ∀k ≠ j, x.testBit k = y.testBit k

def Computable.next_to (x y : ℕ) : Bool :=
  let diff := x ^^^ y
  if diff = 0 then
    false
  else diff &&& (diff - 1) == 0

#check Nat.testBit

/--
info: true
-/
#guard_msgs in
#eval Computable.next_to 1 3

/--
info: true
-/
#guard_msgs in
#eval Computable.next_to 3 2

/--
info: true
-/
#guard_msgs in
#eval Computable.next_to 4 5

def IsGrayCode (f : ℕ → ℕ) : Prop :=
  ∀ i, ∃ j, (f i).testBit j != (f (i+1)).testBit j ∧
    ∀k ≠ j, (f i).testBit k = (f i).testBit k

instance : NormedAddCommGroup (Fin 2) where
  norm n := (n : ℝ)
  dist_self := by simp
  dist_comm := by
    intros x y
    fin_cases x, y <;> simp
  dist_triangle := by
    intros x y z
    fin_cases x, y, z <;> simp
  eq_of_dist_eq_zero := by
    intros x y
    fin_cases x, y <;> simp



variable {α : Type*}
variable [Fintype α] {E : α → Type*} {p q : ENNReal} [∀ i, NormedAddCommGroup (E i)]

def l1norm [Fintype α] (f : ∀ i, E i) : ℝ := ∑ i, ‖f i‖

def x : Fin 5 → Fin 2 := 1

#check NNNorm

#eval l1norm x

lemma finmem (f : ∀ i, E i) : Memℓp f 1 := memℓp_gen (Summable.of_finite)

def test : lp (fun (_ : Fin 3) => Fin 2) 1 := ⟨fun _ ↦ 1, finmem _⟩

#check lp.instNormSubtypePreLpMemAddSubgroup

--#eval norm test

local instance : Norm (lp E 1) where
  norm f := ∑  i, ‖f i‖

def hello := "world"
