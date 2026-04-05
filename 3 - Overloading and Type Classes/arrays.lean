-- from previous chapters

inductive Pos : Type where
  | one  : Pos
  | succ : Pos → Pos

instance : OfNat Pos (n + 1) where
  ofNat := let rec natPlusOne : Nat → Pos       
             | 0     => Pos.one                 
             | k + 1 => Pos.succ $ natPlusOne k 
           natPlusOne n                         

def Pos.toNat : Pos → Nat
  | Pos.one    => 1
  | Pos.succ n => n.toNat + 1
  
/- =================== -/
/- Arrays and Indexing -/
/- =================== -/

/- ------ -/
/- Arrays -/
/- ------ -/

-- Arrays are written similarly to lists, but with a leading `#`
def northernTrees : Array String := #["sloe", "birch", "elm", "oak"]

#eval northernTrees.size 

#eval northernTrees[0]   
#eval northernTrees[1]   
#eval northernTrees[2]   
#eval northernTrees[3]   

/- --------------- -/
/- Non-Empty Lists -/
/- --------------- -/

-- Goal: we would love to use indexing for Non-Empty Lists!

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String := {
  head :=   "Banded Garden Spider",
  tail := [ "Long-legged Sac Spider",
            "Wolf Spider",
            "Hobo Spider",
            "Cat-faced Spider" ]
}

def NonEmptyList.get1? : NonEmptyList α → Nat → Option α
  | xs, 0                              => some xs.head
  | {head := _, tail := []}, _ + 1     => none
  | {head := _, tail := h :: t}, n + 1 => get1? {head := h, tail := t} n

def NonEmptyList.get2? : NonEmptyList α → Nat → Option α
  | xs, 0     => some xs.head
  | xs, n + 1 => xs.tail[n]?

-- written as an abbrev so it can be found easily by tactics
abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

theorem atLeastThreeSpiders :  idahoSpiders.inBounds 2 := by decide
theorem notSixSpiders       : ¬idahoSpiders.inBounds 5 := by decide

-- check at compile-time - Option not required
def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0     => xs.head
  | n + 1 => xs.tail[n]

-- works, but not very convenient
#eval idahoSpiders.get 0 (by decide)
#eval idahoSpiders.get 1 (by decide)
#eval idahoSpiders.get 2 (by decide)
#eval idahoSpiders.get 3 (by decide)
#eval idahoSpiders.get 4 (by decide)

/- -------------------- -/
/- Overloading Indexing -/
/- -------------------- -/

-- indexing notation in order to look up entries in a list by their position is governed by the type class GetElem.
class MyGetElem
    (coll     : Type)
    (idx      : Type)
    (item     : outParam Type)
    (inBounds : outParam (coll → idx → Prop)) where
  getElem : (c : coll) → (i : idx) → inBounds c i → item

instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

#eval idahoSpiders.head
#eval idahoSpiders.tail

-- now we can use indexing
-- NonEmptyList becomes just as convenient to use as List 
#eval idahoSpiders[0]  
#eval idahoSpiders[1]  
#eval idahoSpiders[2]  
#eval idahoSpiders[3]  
#eval idahoSpiders[4]  

-- -------------------------- --
-- Indexing a List with a Pos --
-- -------------------------- --

instance : GetElem (List α) Pos α (fun list n => list.length > n.toNat - 1) where
  getElem (xs : List α) (i : Pos) ok := xs[i.toNat - 1]

def carBrands := ["BMW", "Mercedes", "VW"]

-- indexing with Nat's
#eval carBrands[0]                            
#eval carBrands[1]                            
#eval carBrands[2]                            

-- indexing with Pos's
#eval carBrands[Pos.one]                      
#eval carBrands[Pos.succ $ Pos.one]           
#eval carBrands[Pos.succ $ Pos.succ $ Pos.one]

-- -------------------------------- --
-- Indexing a PPoint with a Boolean --
-- -------------------------------- --

structure PPoint (α : Type) where
  x : α
  y : α

-- using Bool as an index type
instance : GetElem (PPoint α) Bool α (fun _ppoint _idx => True) where
  getElem (p : PPoint α) (i : Bool) _ := if i then p.y else p.x
  
def p1 := { x := 1, y := 2 : PPoint Nat}

#eval p1[false]
#eval p1[true] 
