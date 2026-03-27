/- ----------------------------- -/
/- Type Classes and Polymorphism -/
/- ----------------------------- -/

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

-- couldn't figure out type of implicit arguments -> prints metavariables
#check (IO.println)

-- signature without metavariables
#check @IO.println

/- ------------------------------------------------------ -/
/- Defining Polymorphic Functions with Instance Implicits -/
/- ------------------------------------------------------ -/

def List.sumOfContents1 [Add α] [OfNat α 0] : List α → α
  | []      => 0
  | x :: xs => x + xs.sumOfContents1

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

-- this function is in the standard library
#check List.sum

-- Specifications of required instances in square brackets are called INSTANCE IMPLICITS.

-- The most important difference between ordinary IMPLICIT ARGUMENTS and INSTANCE IMPLICITS is the strategy that Lean uses to find an argument value.
-- In the case of ordinary IMPLICIT ARGUMENTS, Lean uses a technique called UNIFICATION to find a single unique argument value that would allow the program to pass the type checker.
-- This process relies only on the specific types involved in the function's definition and the call site.
-- For INSTANCE IMPLICITS, Lean instead consults a built-in table of instance values.

structure PPoint (α : Type) where
  x : α
  y : α

--     α must also be addable
--           ^^^^^^^
instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

/- ------------------------------  -/
/- Methods and Implicit Arguments  -/
/- ------------------------------  -/

-- The type parameter α can be implicit because the arguments to Add.add provide information about which type the user intended. 
#check Add.add 

-- In the case of OfNat.ofNat, the particular Nat literal to be decoded does not appear as part of any other parameter's type.
-- This means that Lean would have no information to use when attempting to figure out the implicit parameter n.
-- In this case, Lean uses an explicit parameter for the class's method.
--                                                     ^^^^^^^^^^
#check OfNat.ofNat

/- --------- -/
/- Exercises -/
/- --------- -/

-- see solution for inductive type
-- https://proofassistants.stackexchange.com/questions/2435/recursive-type-class-for-ofnat-even
-- https://github.com/James-Oswald/Functional-Programming-In-Lean/blob/lean-3.51.1/src/4.2.lean

-- Even Number Literals

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

/- --------------------------- -/
/- Controlling Instance Search -/
/- --------------------------- -/

def addNatPos : Nat → Pos → Pos
  | 0, p     => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0     => p
  | p, n + 1 => Pos.succ (addPosNat p n)

#eval addNatPos 5 4
#eval addPosNat 5 4

/- -------------------------- -/
/- Heterogeneous Overloadings -/
/- -------------------------- -/

instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

#eval (3 : Nat) + (5 : Nat)
#eval (3 : Pos) + (5 : Nat)
#eval (3 : Nat) + (5 : Pos)
#eval (3 : Pos) + (5 : Pos)

class HPlus1 (α : Type) (β : Type) (γ : Type) where
  hPlus : α → β → γ
  
instance : HPlus1 Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus1 Pos Nat Pos where
  hPlus := addPosNat

-- Note: metavariables represent unknown parts of a program that could not be inferred
-- see error message from language server
#eval HPlus1.hPlus (3 : Pos) (5 : Nat)

-- with (unconvenient) type annotations
#eval (HPlus1.hPlus (3 : Pos) (5 : Nat) : Pos)

/- ----------------- -/
/- Output Parameters -/
/- ----------------- -/

-- Most type class parameters are inputs to the search algorithm: they are used to select an instance.

-- In some cases, it can be convenient to start the search process even when some of the type parameters
-- are not yet known, and use the instances that are discovered in the search to determine values for metavariables.

-- The parameters that aren't needed to start instance search are outputs of the process, which is declared with
-- the outParam modifier.

class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

-- With this output parameter, type class instance search is able to select an instance without knowing γ in advance.
#eval HPlus.hPlus (3 : Pos) (5 : Nat)

/- ----------------- -/
/- Default Instances -/
/- ----------------- -/

-- Default instances are instances that are available for instance search even when not all their inputs are known. 

-- When one of these instances can be used, it will be used.

instance [Add α] : HPlus α α α where
  hPlus := Add.add

-- With this instance, hPlus can be used for any addable type, like Nat:
#eval HPlus.hPlus (3 : Nat) (5 : Nat)

#check HPlus.hPlus (5 : Nat) (3 : Nat)
#check HPlus.hPlus (5 : Nat)

--In the vast majority of cases, when someone supplies one argument to addition, the other argument will have the same type.
-- To make this instance into a default instance, apply the `default_instance` attribute.

@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add

#check HPlus.hPlus (5 : Nat)

-- Default instances can also be assigned priorities that affect which will be chosen in situations where more than one might apply.
-- For more information on default instance priorities, please consult the Lean manual.

/- --------- -/
/- Exercises -/
/- --------- -/

-- TBD
