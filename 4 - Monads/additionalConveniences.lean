/- ======================= -/
/- Additional Conveniences -/
/- ======================= -/

/- --------------------- -/
/- Shared Argument Types -/
/- --------------------- -/
def equal? [BEq α] (x : α) (y : α) : Option α :=
  if x == y then
    some x
  else
    none

def equal?' [BEq α] (x y : α) : Option α :=
  if x == y then
    some x
  else
    none

/- -------------------- -/
/- Leading Dot Notation -/
/- -------------------- -/

inductive BinTree (α : Type) where
  | leaf   : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def BinTree.mirror : BinTree α → BinTree α
  | BinTree.leaf         => BinTree.leaf
  | BinTree.branch l x r => BinTree.branch (mirror r) x (mirror l)

def BinTree.mirror' : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)

def BinTree.empty : BinTree α := .leaf

#check (.empty : BinTree Nat)

/- ----------- -/
/- Or-Patterns -/
/- ----------- -/

inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
deriving Repr

def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | Weekday.saturday => true
  | Weekday.sunday   => true
  | _                => false

-- using constructor dot notation
def Weekday.isWeekend' (day : Weekday) : Bool :=
  match day with
  | .saturday => true
  | .sunday   => true
  | _         => false

-- using or-pattern
def Weekday.isWeekend'' (day : Weekday) : Bool :=
  match day with
  | .saturday | .sunday => true
  | _                   => false

-- unnamed arguments
def Weekday.isWeekend''' : Weekday → Bool
  | .saturday | .sunday => true
  | _                   => false

def condense : α ⊕ α → α
  | .inl x | .inr x => x

def stringy : Nat ⊕ Weekday → String
  | .inl x | .inr x => s!"It is {repr x}"

-- TODO
-- #eval stringy ((0 : Nat), Weekday.monday)

def getTheNat : (Nat × α) ⊕ (Nat × β) → Nat
  | .inl (n, _x) | .inr (n, _y) => n

-- there is no x available in the second pattern
def getTheAlpha : (Nat × α) ⊕ (Nat × α) → α
  | .inl (n, x) | .inr (n, y) => x

-- The fact that the result expression is essentially copy-pasted to each branch of the pattern match can lead to some surprising behavior.
def str := "Some string"

def getTheString : (Nat × String) ⊕ (Nat × β) → String
  | .inl (_n, str) | .inr (_n, _y) => str

-- type annotation for β necessary
#eval getTheString (.inl (20, "twenty") : (Nat × String) ⊕ (Nat × String))

-- global str is used
#eval getTheString (.inr (20, "twenty"))
