import Mathlib
--import Mathlib.Analysis.Normed.Lp.lpSpace

--#eval Nat.testBit 1 0

def next_to (x y : ℕ) : Prop :=
  ∃ j, x.testBit j != y.testBit j ∧
    ∀k ≠ j, x.testBit k = y.testBit k

example : next_to 4 5 := by
  unfold next_to
  use 0
  refine ⟨by simp, ?_⟩
  intro k knot0
  rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth]
  rw [show Nat.bits 4 = [false, false, true] by simp [Nat.bits, Nat.binaryRec]]
  rw [show Nat.bits 5 = [true, false, true] by simp [Nat.bits, Nat.binaryRec]]
  -- There still has to be  abetter way to do this kind of casework
  if k = 0 then
    contradiction
  else if h : k = 1 then
    simp [h]
  else if h' : k = 2 then
    simp [h']
  else
    have : 3 ≤ k := by grind
    rw [List.getI_eq_default [false, false, true] (by simp [this])]
    rw [List.getI_eq_default [true, false, true] (by simp [this])]


#check geom_sum_two

lemma geom_sum_pow_two (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i = 2^n - 1 := by
  have := Nat.geomSum_eq (m := 2) Nat.AtLeastTwo.prop n
  simp [this]

#check Nat.testBit_two_pow_sub_one


/--
Note that $2^k - 1 = 1 + \cdots + 2^{k-1}$. Thus $(2^k - 1)_i = 1$ for
all $i \le {k-1}$.

When $x = 2^k$, since $(x)_k = 1$ and all others are $0$, while
$(x - 1)_k = 1$ for all $i \le k-1$ and $0$ otherwise. Thus $x \& (x - 1) = 0$
and we return true.

If $x = 0$, then we return false correctly.

Suppose that $2^i < x < 2^{i+1}$, then $(x)_i = 1$ and $2^i \le (x - 1) < 2^{i-1}$,
so thus $(x-1)_i = 1$. Thus $x \& (x - 1) \neq 0$.

    $x$ is next to $y$ iff there is some $i$ alone where they are different.
    This occurs iff $(x \oplus y) = (x)_i \oplus (y)_i = 1$ only for $i$.
    $(x \oplus y)_i$ for only $i$ iff $(x \oplus y) = 2^i$.
-/
lemma next_to_xor_two_pow (x y : ℕ) :
  next_to x y ↔ (x ^^^ y).isPowerOfTwo := by
  rw [show next_to x y ↔ ∃ j, (x ^^^ y).testBit j ∧ ∀k ≠ j, ¬(x ^^^ y).testBit k by
    simp [next_to]]
  apply exists_congr
  intro i
  set z := x ^^^ y
  refine ⟨?_, by grind⟩
  intro h
  apply Nat.eq_of_testBit_eq
  intro j
  if h' : j = i then
    rw [<-h'] at h ⊢
    simp only [Nat.testBit_two_pow_self, h.1]
  else
    rw [show z.testBit j = false by simp [h.2 j h']]
    rw [Nat.testBit_two_pow_of_ne (by grind)]

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
