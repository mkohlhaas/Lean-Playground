/- ================ -/
/- Standard Classes -/
/- ================ -/

/- ---------- -/
/- Arithmetic -/
/- ---------- -/

-- -----------|---------------|------------
-- Expression | Desugaring    | Class Name
-- -----------|---------------|------------
-- x + y      | HAdd.hAdd x y | HAdd
-- x - y      | HSub.hSub x y | HSub
-- x * y      | HMul.hMul x y | HMul
-- x / y      | HDiv.hDiv x y | HDiv
-- x % y      | HMod.hMod x y | HMod
-- x ^ y      | HPow.hPow x y | HPow
-- - x        | Neg.neg x     | Neg
-- -----------|---------------|------------

/- ----------------- -/
/- Bitwise Operators -/
/- ----------------- -/

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

-- The homogeneous versions of HAnd and HOr are called AndOp and OrOp rather than And and Or.

/- --------------------- -/
/- Equality and Ordering -/
/- --------------------- -/

-- BEq = Boolean Equality '=='
-- Propositional Equality needs a proof '='

-- Boolean Equality yields a boolean value (true/false)
#eval "Octopus"   ==  "Cuttlefish"         
#eval "Octopodes" ==  "Octo".append "podes"

-- functions cannot be checked for equality
#eval (fun (x : Nat) => 1 + x) == (Nat.succ ·)

-- The expression x == y is shorthand for BEq.beq x y.

-- we have to provide a proof that they are the same functions
#eval (fun (x : Nat) => 1 + x) = (Nat.succ ·)

-- a proposition
#check 2 < 4

-- but perfectly acceptable
#eval if 2 < 4 then 1 else 2

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

-- These propositions are not decidable by default because Lean doesn't unfold the definitions
-- of propositions while synthesizing an instance.
#eval (1 : Pos) < (2 : Pos)

-- can be bridged using the inferInstanceAs operator, which finds an instance for a given class if it exists
instance {x : Pos} {y : Pos} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.toNat < y.toNat))

instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.toNat ≤ y.toNat))

#eval (1 : Pos) < (2 : Pos)

-- The type checker confirms that the definitions of the propositions match. Confusing them results in an error.
instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.toNat < y.toNat))

inductive MyOrdering where
  | lt
  | eq
  | gt

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

class MyHashable (α : Type) where
  hash : α → UInt64

-- The standard library contains a function mixHash with type UInt64 → UInt64 → UInt64 that can be used to combine hashes for different fields for a constructor.
def hashPos : Pos → UInt64
  | Pos.one    => 0
  | Pos.succ n => mixHash 1 (hashPos n)

instance : Hashable Pos where
  hash := hashPos

-- using recursive instance search
instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)

-- Binary trees use both recursion and recursive instance search in the implementations of BEq and Hashable
inductive BinTree (α : Type) where
  | leaf   : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf                    => true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 => x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ => false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf                => 0
  | BinTree.branch left x right =>
    mixHash 1
      (mixHash (hashBinTree left)
        (mixHash (hash x)
          (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree

/- ------------------------- -/
/- Deriving Standard Classes -/
/- ------------------------- -/

deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable for NonEmptyList

-- Instances can be derived for at least the following classes:
--  · Inhabited
--  · BEq
--  · Repr
--  · Hashable
--  · Ord

/- --------- -/
/- Appending -/
/- --------- -/

class MyHAppend (α : Type) (β : Type) (γ : outParam Type) where
  hAppend : α → β → γ

-- The syntax xs ++ ys desugars to HAppend.hAppend xs ys.
-- For homogeneous cases, it's enough to implement an instance of Append.

instance : Append (NonEmptyList α) where
  append xs ys := { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

#eval idahoSpiders ++ idahoSpiders

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys := { head := xs.head, tail := xs.tail ++ ys }

#eval idahoSpiders ++ ["Trapdoor Spider"]

/- -------- -/
/- Functors -/
/- -------- -/

#eval Functor.map (· + 5) [1, 2, 3]                     
#eval Functor.map toString (some (List.cons 5 List.nil))
#eval Functor.map List.reverse [[1, 2, 3], [4, 5, 6]]   

-- with infix operator <$>
#eval (· + 5) <$> [1, 2, 3]                     
#eval toString <$> (some (List.cons 5 List.nil))
#eval List.reverse <$> [[1, 2, 3], [4, 5, 6]]   


instance : Functor NonEmptyList where
  map f xs := { head := f xs.head, tail := f <$> xs.tail }

instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }

-- default method definitions

def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | []        => start
    | (z :: zs) => catList (start ++ z) zs
  catList xs.head xs.tail

-- Default method definitions contain := in a class definition.

class MyFunctor (f : Type → Type) where
  map : {α β : Type} → (α → β) → f α → f β

  -- default method definition
  mapConst {α β : Type} (x : α) (coll : f β) : f α :=
    map (fun _ => x) coll

/- --------------------- -/
/- Messages You May Meet -/
/- --------------------- -/

deriving instance ToString for NonEmptyList

/- --------- -/
/- Exercises -/
/- --------- -/

-- TBD :)
