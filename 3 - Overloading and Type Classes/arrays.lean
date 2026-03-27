/- =================== -/
/- Arrays and Indexing -/
/- =================== -/

/- ------ -/
/- Arrays -/
/- ------ -/

def northernTrees : Array String := #["sloe", "birch", "elm", "oak"]

#eval northernTrees.size 

#eval northernTrees[0]   
#eval northernTrees[1]   
#eval northernTrees[2]   
#eval northernTrees[3]   
#eval northernTrees[4]   

/- --------------- -/
/- Non-Empty Lists -/
/- --------------- -/

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String := {
  head :=  "Banded Garden Spider",
  tail := [ "Long-legged Sac Spider",
            "Wolf Spider",
            "Hobo Spider",
            "Cat-faced Spider"
          ]
}

def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0                              => some xs.head
  | {head := _, tail := []}, _ + 1     => none
  | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n

def NonEmptyList.get1? : NonEmptyList α → Nat → Option α
  | xs, 0     => some xs.head
  | xs, n + 1 => xs.tail[n]?

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

theorem atLeastThreeSpiders :  idahoSpiders.inBounds 2 := by decide
theorem notSixSpiders       : ¬idahoSpiders.inBounds 5 := by decide

-- check at compile-time - Option not required
def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0     => xs.head
  | n + 1 => xs.tail[n]

/- -------------------- -/
/- Overloading Indexing -/
/- -------------------- -/

class MyGetElem
    (coll     : Type)
    (idx      : Type)
    (item     : outParam Type)
    (inBounds : outParam (coll → idx → Prop)) where
  getElem : (c : coll) → (i : idx) → inBounds c i → item

instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

-- NonEmptyList becomes just as convenient to use as List 
#eval idahoSpiders.head
#eval idahoSpiders[0]  
#eval idahoSpiders[1]  
#eval idahoSpiders[2]  
#eval idahoSpiders[3]  
#eval idahoSpiders[4]  
#eval idahoSpiders[5]  

instance : GetElem (List α) Pos α (fun list n => list.length > n.toNat) where
  getElem (xs : List α) (i : Pos) ok := xs[i.toNat]

def carBrands := ["BMW", "Mercedes", "VW"]

#eval carBrands[one]
#eval carBrands[two]

#eval carBrands[three]

-- using Bool as an index type
instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p : PPoint α) (i : Bool) _ := if not i then p.x else p.y
  
def p1 := { x := 1, y := 2 : PPoint Nat}

#eval p1[false]
#eval p1[true] 
