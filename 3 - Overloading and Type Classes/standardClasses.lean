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
  
instance : OfNat Pos (n + 1) where
  ofNat := let rec natPlusOne : Nat → Pos       
             | 0     => Pos.one                 
             | k + 1 => Pos.succ $ natPlusOne k 
           natPlusOne n                         

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0     => xs.head
  | n + 1 => xs.tail[n]

instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [ "Long-legged Sac Spider",
            "Wolf Spider",
            "Hobo Spider",
            "Cat-faced Spider" ]
}

structure PPoint (α : Type) where
  x : α
  y : α

/- ================ -/
/- Standard Classes -/
/- ================ -/
-- Unlike C++, infix operators in Lean are defined as abbreviations for named functions.
-- This means that overloading them for new types is not done using the operator itself, but rather using the underlying name (e.g. HAdd.hAdd).

/- ---------- -/
/- Arithmetic -/
/- ---------- -/

-- For each heterogeneous operator, there is a corresponding homogeneous version that can found by removing the letter h, so that HAdd.hAdd becomes Add.add.

-- -----------|---------------|------------
-- Expression | Desugaring    | Class Name
-- -----------|---------------|------------
-- x + y      | HAdd.hAdd x y | HAdd
-- x - y      | HSub.hSub x y | HSub
-- x * y      | HMul.hMul x y | HMul
-- x / y      | HDiv.hDiv x y | HDiv
-- x % y      | HMod.hMod x y | HMod
-- x ^ y      | HPow.hPow x y | HPow
--  -x        | Neg.neg x     | Neg
-- -----------|---------------|------------

/- ----------------- -/
/- Bitwise Operators -/
/- ----------------- -/

-- There are instances for fixed-width types such as UInt8, UInt16, UInt32, UInt64, and USize.
-- The latter is the size of words on the current platform, typically 32 or 64 bits.

-- The homogeneous versions of HAnd and HOr are called AndOp and OrOp rather than And and Or.

-- -----------|----------------------------|--------------
-- Expression | Desugaring                 | Class Name
-- -----------|----------------------------|--------------
-- x &&& y    | HAnd.hAnd x y              | HAnd
-- x ||| y    | HOr.hOr x y                | HOr
-- x ^^^ y    | HXor.hXor x y              | HXor
-- ~~~x       | Complement.complement x    | Complement
-- x >>> y    | HShiftRight.hShiftRight x y| HShiftRight
-- x <<< y    | HShiftLeft.hShiftLeft x y  | HShiftLeft
-- -----------|----------------------------|--------------

/- --------------------- -/
/- Equality and Ordering -/
/- --------------------- -/

-- Testing equality of two values typically uses the BEq type class.

-- BEq = Boolean Equality,               uses '=='
-- Propositional Equality needs a proof, uses '='

-- Boolean Equality yields a boolean value (true/false)
#eval "Octopus"   ==  "Cuttlefish"            
#eval "Octopodes" ==  "Octo".append "podes   "

-- Functions cannot be checked for boolean equality.
-- `==` is overloaded using a type class (see error message).
-- The expression `x == y` is shorthand for `BEq.beq x y`.
#eval (fun (x : Nat) => 1 + x) == (Nat.succ ·)

-- We have to provide a proof that they are the same functions.
#eval (fun (x : Nat) => 1 + x) = (Nat.succ ·) 

-- From the perspective of mathematics, two functions are equal if they map equal inputs to equal outputs.
-- So this statement is even true, though it requires a one-line proof to convince Lean of this fact.

-- a proposition
#check 2 < 4                                  

-- but perfectly acceptable in an `if` expression, because it's decidable
#eval if 2 < 4 then 1 else 2                  

-- Decidable propositions have an instance of the Decidable type class, which contains the decision procedure. 

-- not decidable
#eval if (fun (x : Nat) => 1 + x) = (Nat.succ ·) then "yes" else "no"

-- The following propositions, that are usually decidable, are overloaded with type classes.

-- -----------|------------|------------
-- Expression | Desugaring | Class Name
-- -----------|------------|------------
-- x < y      | LT.lt x y  | LT
-- x ≤ y      | LE.le x y  | LE
-- x > y      | LT.lt y x  | LT
-- x ≥ y      | LE.le y x  | LE
-- -----------|------------|------------

instance : LT Pos where
  lt x y := LT.lt x.toNat y.toNat

instance : LE Pos where
  le x y := LE.le x.toNat y.toNat

-- These propositions are not decidable by default because Lean doesn't unfold the definitions of propositions while synthesizing an instance.
#eval (1 : Pos) < (2 : Pos)                        

-- Can be bridged using the inferInstanceAs operator, which finds an instance for a given class if it exists.
instance {x : Pos} {y : Pos} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.toNat < y.toNat))

instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.toNat ≤ y.toNat))

#eval (2 : Pos) < (1 : Pos)                        
#eval (1 : Pos) < (2 : Pos)                        

-- The type checker confirms that the definitions of the propositions match. Confusing them results in an error.
instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.toNat < y.toNat))  

inductive MyOrdering where
  | lt
  | eq
  | gt

-- Ord type class has a compare function outputting an Ordering.
#check Ord

def Pos.comp : Pos → Pos → Ordering
  | Pos.one,    Pos.one    => Ordering.eq
  | Pos.one,    Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one    => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k

instance : Ord Pos where
  compare := Pos.comp

/- ------- -/
/- Hashing -/
/- ------- -/

-- if x == y then hash x == hash y
class MyHashable (α : Type) where
  hash : α → UInt64

#check Hashable

-- The standard library contains a function mixHash with type UInt64 → UInt64 → UInt64 that can be used to combine hashes for different fields for a constructor.
-- `mixHash` is an opaque hash mixing operation, used to implement hashing for products. 
def hashPos : Pos → UInt64
  | Pos.one    => 0
  | Pos.succ n => mixHash 1 $ hashPos n

instance : Hashable Pos where
  hash := hashPos

#eval hash  0       
#eval hash  1       
#eval hash  2       
#eval hash  3       
#eval hash  4       
#eval hash  5       
#eval hash (1 : Pos)
#eval hash (2 : Pos)
#eval hash (3 : Pos)
#eval hash (4 : Pos)
#eval hash (5 : Pos)
#eval hash (6 : Pos)
#eval hash (7 : Pos)
#eval hash (8 : Pos)
#eval hash (9 : Pos)

-- Hashable instances for polymorphic types can use recursive instance search.
-- Hashing a NonEmptyList α is only possible when α can be hashed
instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)

-- Binary Trees --

-- Binary trees use both recursion and recursive instance search in the implementations of BEq and Hashable
inductive BinTree (α : Type) where
  | leaf   : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf                       => true
  | BinTree.branch l1 x1 r1, BinTree.branch l2 x2 r2 => x1 == x2 && eqBinTree l1 l2 && eqBinTree r1 r2
  | _, _                                             => false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf                => 0
  | BinTree.branch left x right => mixHash 1
                                    (mixHash (hashBinTree left)
                                      (mixHash (hash x) (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree

open BinTree
#eval hash (leaf : BinTree Pos)                                        
#eval hash (branch leaf (5 : Pos) leaf )                               
#eval hash (branch (branch leaf 6 leaf) (5 : Pos) leaf)                
#eval hash (branch (branch leaf 6 leaf) (5 : Pos) (branch leaf 7 leaf))

/- ------------------------- -/
/- Deriving Standard Classes -/
/- ------------------------- -/

deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable for NonEmptyList

-- same as above, btw
#eval hash (1 : Pos)
#eval hash (2 : Pos)
#eval hash (3 : Pos)
#eval hash (4 : Pos)
#eval hash (5 : Pos)
#eval hash (6 : Pos)
#eval hash (7 : Pos)
#eval hash (8 : Pos)
#eval hash (9 : Pos)

-- Instances can be derived for at least the following classes:
--  · BEq
--  · Ord
--  · Hashable
--  · Repr
--  · Inhabited

-- The collection of classes for which instances can be derived can be extended by advanced users of Lean.

/- --------- -/
/- Appending -/
/- --------- -/

class MyHAppend (α : Type) (β : Type) (γ : outParam Type) where
  hAppend : α → β → γ

#check Append  
#check HAppend 

-- `xs ++ ys` desugars to HAppend.hAppend xs ys
-- For homogeneous cases, it's enough to implement an instance of Append.

instance : Append (NonEmptyList α) where
  append xs ys := { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

#eval idahoSpiders ++ idahoSpiders

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys := { head := xs.head, tail := xs.tail ++ ys }

#eval idahoSpiders ++ ["Trapdoor Spider", "Zombie Spider", "Dog Spider"]

/- -------- -/
/- Functors -/
/- -------- -/

-- a functor has a map function, infix operator <$>
#check Functor

#eval Functor.map (· + 5) [1, 2, 3]                     
#eval Functor.map (· + 5) (some 5)                      
#eval Functor.map (· + 5)  none                         
#eval Functor.map toString $ some $ List.cons 5 List.nil
#eval Functor.map List.reverse [[1, 2, 3], [4, 5, 6]]   

-- with infix operator <$>
#eval (· + 5) <$> [1, 2, 3]                             
#eval (· + 5) <$> some 5                                
#eval (· + 5) <$> none                                  
#eval toString <$> some <$> List.cons 5 List.nil        
#eval List.reverse <$> [[1, 2, 3], [4, 5, 6]]           

instance : Functor NonEmptyList where
  map f xs := { head := f xs.head, tail := f <$> xs.tail }

instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }

#eval (· * 2) <$> { head := 1, tail := [2, 3, 4, 5] : NonEmptyList Nat} 

-- default method definitions

-- concatenate any non-empty list whose entries are appendable
def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | []        => start
    | (z :: zs) => catList (start ++ z) zs
  catList xs.head xs.tail

class MyFunctor (f : Type → Type) where
  map : {α β : Type} → (α → β) → f α → f β

  -- default method definition
  mapConst {α β : Type} (x : α) (coll : f β) : f α :=
    map (fun _ => x) coll

instance : MyFunctor NonEmptyList where
  map f xs := f <$> xs

open MyFunctor
#eval mapConst "spider" idahoSpiders

/- --------------------- -/
/- Messages You May Meet -/
/- --------------------- -/

-- ToString cannot be derived automatically (Repr works though.)
deriving instance ToString for NonEmptyList
deriving instance Repr     for NonEmptyList

/- --------- -/
/- Exercises -/
/- --------- -/

-- TBD :)
