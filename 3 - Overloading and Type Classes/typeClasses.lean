/- ----------------------------- -/
/- Type Classes and Polymorphism -/
/- ----------------------------- -/

-- from previous chapters

inductive Pos : Type where
  | one  : Pos
  | succ : Pos → Pos

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k    => Pos.succ k
  | Pos.succ n, k => Pos.succ $ n.plus k

instance : Add Pos where
  add := Pos.plus
  
def Pos.toNat : Pos → Nat
  | Pos.one    => 1
  | Pos.succ n => n.toNat + 1
  
instance : ToString Pos where
  toString x := toString $ x.toNat

def Pos.mul : Pos → Pos → Pos
  | Pos.one, k    => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul

instance : One Pos where
  one := Pos.one

instance : OfNat Pos (n + 1) where
  ofNat := let rec natPlusOne : Nat → Pos       
             | 0     => Pos.one                 
             | k + 1 => Pos.succ $ natPlusOne k 
           natPlusOne n                         

/- ----------------------------------- -/
/- Checking Polymorphic Function Types -/
/- ----------------------------------- -/

-- couldn't figure out type of implicit arguments
-- prints types with metavariables
#check (IO.println)

-- signature without metavariables
-- α must have a ToString instance
#check @IO.println 

/- ------------------------------------------------------ -/
/- Defining Polymorphic Functions with Instance Implicits -/
/- ------------------------------------------------------ -/

-- α must have an Add and OfNat instance
def List.sumOfContents1 [Add α] [OfNat α 0] : List α → α
  | []      => 0
  | x :: xs => x + xs.sumOfContents1

-- alternative with a Zero instance for α
def List.sumOfContents2 [Add α] [Zero α] : List α → α
  | []      => 0
  | x :: xs => x + xs.sumOfContents2

def fourNats : List Nat := [1, 2, 3, 4]

#eval fourNats.sumOfContents1
#eval fourNats.sumOfContents2

def fourPos : List Pos := [1, 2, 3, 4]

-- Pos doesn't have zeros
#eval fourPos.sumOfContents1
#eval fourPos.sumOfContents2

-- in the standard library this function is called List.sum
#check List.sum

-- Specifications of required instances in square brackets are called INSTANCE IMPLICITS.

-- The most important difference between ordinary IMPLICIT ARGUMENTS and INSTANCE IMPLICITS is the strategy that Lean uses to find an argument value.
-- In the case of ordinary IMPLICIT ARGUMENTS, Lean uses a technique called UNIFICATION to find a single unique argument value that would allow the program to pass the type checker.
-- This process relies only on the specific types involved in the function's definition and the call site.
-- For INSTANCE IMPLICITS, Lean instead consults a built-in table of instance values.

structure PPoint (α : Type) where
  x : α
  y : α

#check (PPoint)
#check @PPoint 

--     α is required to be addable
--           ^^^^^^^
instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

-- An instance of Add (PPoint Nat) contains a reference to the instance of Add Nat.

/- ------------------------------ -/
/- Methods and Implicit Arguments -/
/- ------------------------------ -/

-- NOTE: didn't understand the point

-- The type parameter α can be implicit because the arguments to Add.add provide information about which type the user intended. 
#check Add.add 

-- In the case of OfNat.ofNat, the particular Nat literal to be decoded does not appear as part of any other parameter's type.
-- This means that Lean would have no information to use when attempting to figure out the implicit parameter n.
-- In this case, Lean uses an explicit parameter for the class's method.
--                                                    ^^^^^^^^^^
#check OfNat.ofNat

/- --------- -/
/- Exercises -/
/- --------- -/

-- see solution for inductive type
-- https://proofassistants.stackexchange.com/questions/2435/recursive-type-class-for-ofnat-even
-- https://github.com/James-Oswald/Functional-Programming-In-Lean/blob/lean-3.51.1/src/4.2.lean

-- --------------------
-- Even Number Literals
-- --------------------

structure Even where
  even : Nat

def Even.plus : Even → Even → Even 
| Even.mk n, Even.mk m => Even.mk (((2 * n) + (2 * m)) / 2)

instance : Add Even where
  add := Even.plus

instance : OfNat Even n where
  ofNat := Even.mk (n / 2)

instance : ToString Even where
  toString e := toString (2 * e.even)
